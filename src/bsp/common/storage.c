/*
 * storage.c - Storage Stack Implementation for ARM Bootloader
 *
 * Provides storage device abstraction and FAT filesystem support.
 */

#include "storage.h"
#include "shell.h"
#include "env.h"
#include "boot_common.h"

/* Storage state */
static struct {
    int initialized;
    int current_device;
    storage_info_t devices[STORAGE_MAX_DEVICES];
} storage_state;

/* Filesystem state per device */
static struct {
    int mounted;
    int type;                       /* 1=FAT16, 2=FAT32 */
    uint32_t partition_lba;         /* Partition start sector */
    uint32_t fat_begin_sector;
    uint32_t cluster_begin_sector;
    uint32_t sectors_per_cluster;
    uint32_t root_dir_cluster;      /* FAT32 only */
    uint32_t root_dir_sector;       /* FAT16 only */
    uint32_t root_dir_sectors;      /* FAT16 only */
    uint32_t sectors_per_fat;
    uint32_t total_clusters;
    uint8_t  num_fats;
    char     volume_label[12];
} fs_state[STORAGE_MAX_DEVICES];

/* Sector buffer */
static uint8_t sector_buf[STORAGE_BLOCK_SIZE] __attribute__((aligned(16)));

/*
 * Storage Stack API
 */

int storage_init(void) {
    int i;

    /* Clear state */
    storage_state.initialized = 0;
    storage_state.current_device = 0;

    for (i = 0; i < STORAGE_MAX_DEVICES; i++) {
        storage_state.devices[i].type = STORAGE_TYPE_NONE;
        storage_state.devices[i].initialized = 0;
        fs_state[i].mounted = 0;
    }

    /* Try to initialize device 0 (primary SD/eMMC) */
    if (bsp_storage_init(0) == 0) {
        bsp_storage_info(0, &storage_state.devices[0]);
        storage_state.devices[0].initialized = 1;
        storage_state.initialized = 1;

        shell_printf("Storage: Device 0 initialized\n");
        shell_printf("  Type: ");
        switch (storage_state.devices[0].type) {
            case STORAGE_TYPE_SD:   shell_printf("SD\n"); break;
            case STORAGE_TYPE_SDHC: shell_printf("SDHC\n"); break;
            case STORAGE_TYPE_SDXC: shell_printf("SDXC\n"); break;
            case STORAGE_TYPE_EMMC: shell_printf("eMMC\n"); break;
            case STORAGE_TYPE_MMC:  shell_printf("MMC\n"); break;
            default: shell_printf("Unknown\n"); break;
        }
        shell_printf("  Capacity: %u MB\n", (uint32_t)storage_state.devices[0].capacity_mb);

        return 0;
    }

    shell_printf("Storage: No device found\n");
    return -1;
}

int storage_get_info(int device, storage_info_t *info) {
    if (device < 0 || device >= STORAGE_MAX_DEVICES) {
        return -1;
    }

    if (!storage_state.devices[device].initialized) {
        return -1;
    }

    /* Use explicit copy to avoid implicit memcpy call */
    shell_memcpy(info, &storage_state.devices[device], sizeof(storage_info_t));
    return 0;
}

int storage_read_blocks(int device, uint64_t start, uint32_t count, uint8_t *buffer) {
    if (device < 0 || device >= STORAGE_MAX_DEVICES) {
        return -1;
    }

    if (!storage_state.devices[device].initialized) {
        return -1;
    }

    return bsp_storage_read(device, start, count, buffer);
}

int storage_write_blocks(int device, uint64_t start, uint32_t count, const uint8_t *buffer) {
    if (device < 0 || device >= STORAGE_MAX_DEVICES) {
        return -1;
    }

    if (!storage_state.devices[device].initialized) {
        return -1;
    }

    return bsp_storage_write(device, start, count, buffer);
}

/*
 * FAT Filesystem Implementation
 */

static uint32_t fat_cluster_to_sector(int device, uint32_t cluster) {
    return fs_state[device].cluster_begin_sector +
           ((cluster - 2) * fs_state[device].sectors_per_cluster);
}

static uint32_t fat_get_next_cluster(int device, uint32_t cluster) {
    uint32_t fat_offset;
    uint32_t fat_sector;
    uint32_t ent_offset;
    uint32_t next_cluster;

    if (fs_state[device].type == 2) {
        /* FAT32 */
        fat_offset = cluster * 4;
        fat_sector = fs_state[device].fat_begin_sector + (fat_offset / STORAGE_BLOCK_SIZE);
        ent_offset = fat_offset % STORAGE_BLOCK_SIZE;

        if (storage_read_blocks(device, fat_sector, 1, sector_buf) != 0) {
            return 0x0FFFFFFF;
        }

        next_cluster = *(uint32_t *)(sector_buf + ent_offset);
        return next_cluster & 0x0FFFFFFF;
    } else {
        /* FAT16 */
        fat_offset = cluster * 2;
        fat_sector = fs_state[device].fat_begin_sector + (fat_offset / STORAGE_BLOCK_SIZE);
        ent_offset = fat_offset % STORAGE_BLOCK_SIZE;

        if (storage_read_blocks(device, fat_sector, 1, sector_buf) != 0) {
            return 0xFFFF;
        }

        next_cluster = *(uint16_t *)(sector_buf + ent_offset);
        return (next_cluster >= 0xFFF8) ? 0x0FFFFFFF : next_cluster;
    }
}

int fs_mount(int device) {
    fat_boot_sector_t *bpb;
    uint32_t partition_lba = 0;
    uint32_t root_dir_sectors;
    uint32_t first_data_sector;
    uint32_t total_sectors;
    uint32_t data_sectors;

    if (device < 0 || device >= STORAGE_MAX_DEVICES) {
        return -1;
    }

    if (!storage_state.devices[device].initialized) {
        shell_printf("Storage device %d not initialized\n", device);
        return -1;
    }

    /* Read sector 0 (MBR or VBR) */
    if (storage_read_blocks(device, 0, 1, sector_buf) != 0) {
        shell_printf("Failed to read boot sector\n");
        return -1;
    }

    /* Check boot signature */
    if (sector_buf[510] != 0x55 || sector_buf[511] != 0xAA) {
        shell_printf("Invalid boot signature\n");
        return -1;
    }

    /* Check if MBR (partition table) or VBR (volume boot record) */
    if (sector_buf[0] != 0xEB && sector_buf[0] != 0xE9) {
        /* Likely MBR - check partition table */
        uint8_t part_type = sector_buf[446 + 4];

        if (part_type == 0x0B || part_type == 0x0C) {
            /* FAT32 */
            partition_lba = *(uint32_t *)(sector_buf + 446 + 8);
        } else if (part_type == 0x06 || part_type == 0x04 || part_type == 0x0E) {
            /* FAT16 */
            partition_lba = *(uint32_t *)(sector_buf + 446 + 8);
        } else if (part_type != 0) {
            shell_printf("Unknown partition type: 0x%x\n", part_type);
            return -1;
        }

        if (partition_lba != 0) {
            if (storage_read_blocks(device, partition_lba, 1, sector_buf) != 0) {
                shell_printf("Failed to read VBR\n");
                return -1;
            }
        }
    }

    fs_state[device].partition_lba = partition_lba;

    /* Parse BPB */
    bpb = (fat_boot_sector_t *)sector_buf;

    if (bpb->bytes_per_sector != 512) {
        shell_printf("Unsupported sector size: %d\n", bpb->bytes_per_sector);
        return -1;
    }

    /* Calculate filesystem parameters */
    root_dir_sectors = ((bpb->root_entry_count * 32) + 511) / 512;

    if (bpb->sectors_per_fat_16 != 0) {
        fs_state[device].sectors_per_fat = bpb->sectors_per_fat_16;
    } else {
        fs_state[device].sectors_per_fat = bpb->sectors_per_fat_32;
    }

    fs_state[device].sectors_per_cluster = bpb->sectors_per_cluster;
    fs_state[device].num_fats = bpb->num_fats;
    fs_state[device].fat_begin_sector = partition_lba + bpb->reserved_sectors;

    first_data_sector = bpb->reserved_sectors +
                        (bpb->num_fats * fs_state[device].sectors_per_fat) +
                        root_dir_sectors;

    fs_state[device].cluster_begin_sector = partition_lba + first_data_sector;

    if (bpb->total_sectors_16 != 0) {
        total_sectors = bpb->total_sectors_16;
    } else {
        total_sectors = bpb->total_sectors_32;
    }

    data_sectors = total_sectors - first_data_sector;
    fs_state[device].total_clusters = data_sectors / bpb->sectors_per_cluster;

    /* Determine FAT type */
    if (fs_state[device].total_clusters < 4085) {
        shell_printf("FAT12 not supported\n");
        return -1;
    } else if (fs_state[device].total_clusters < 65525) {
        fs_state[device].type = 1;  /* FAT16 */
        fs_state[device].root_dir_sector = fs_state[device].fat_begin_sector +
                                           (bpb->num_fats * bpb->sectors_per_fat_16);
        fs_state[device].root_dir_sectors = root_dir_sectors;
        fs_state[device].root_dir_cluster = 0;  /* Not used for FAT16 */
    } else {
        fs_state[device].type = 2;  /* FAT32 */
        fs_state[device].root_dir_cluster = bpb->root_cluster;
        fs_state[device].root_dir_sector = 0;   /* Not used for FAT32 */
        fs_state[device].root_dir_sectors = 0;
    }

    /* Copy volume label */
    int i;
    for (i = 0; i < 11; i++) {
        fs_state[device].volume_label[i] = bpb->volume_label[i];
    }
    fs_state[device].volume_label[11] = '\0';

    /* Trim trailing spaces */
    for (i = 10; i >= 0 && fs_state[device].volume_label[i] == ' '; i--) {
        fs_state[device].volume_label[i] = '\0';
    }

    fs_state[device].mounted = 1;

    shell_printf("Mounted FAT%d filesystem\n", fs_state[device].type == 1 ? 16 : 32);
    shell_printf("  Volume: %s\n", fs_state[device].volume_label[0] ?
                 fs_state[device].volume_label : "(none)");
    shell_printf("  Clusters: %u\n", fs_state[device].total_clusters);
    shell_printf("  Cluster size: %u bytes\n",
                 fs_state[device].sectors_per_cluster * STORAGE_BLOCK_SIZE);

    return 0;
}

int fs_unmount(int device) {
    if (device < 0 || device >= STORAGE_MAX_DEVICES) {
        return -1;
    }

    fs_state[device].mounted = 0;
    return 0;
}

int fs_info(int device, fs_info_t *info) {
    if (device < 0 || device >= STORAGE_MAX_DEVICES) {
        return -1;
    }

    if (!fs_state[device].mounted) {
        return -1;
    }

    info->type = fs_state[device].type;
    info->initialized = fs_state[device].mounted;
    info->total_clusters = fs_state[device].total_clusters;
    info->free_clusters = 0;  /* Would need to scan FAT */
    info->cluster_size = fs_state[device].sectors_per_cluster * STORAGE_BLOCK_SIZE;

    int i;
    for (i = 0; i < 12; i++) {
        info->volume_label[i] = fs_state[device].volume_label[i];
    }

    return 0;
}

/* Convert 8.3 name to readable format */
static void fat_name_to_string(const char *name83, char *output) {
    int i, j = 0;

    /* Copy name (8 chars, trim spaces) */
    for (i = 0; i < 8 && name83[i] != ' '; i++) {
        output[j++] = name83[i];
    }

    /* Add extension if present */
    if (name83[8] != ' ') {
        output[j++] = '.';
        for (i = 8; i < 11 && name83[i] != ' '; i++) {
            output[j++] = name83[i];
        }
    }

    output[j] = '\0';
}

/* Convert string to 8.3 name format */
static void string_to_fat_name(const char *str, char *name83) {
    int i, j;

    /* Fill with spaces */
    for (i = 0; i < 11; i++) {
        name83[i] = ' ';
    }

    /* Copy name */
    for (i = 0; i < 8 && str[i] && str[i] != '.'; i++) {
        char c = str[i];
        if (c >= 'a' && c <= 'z') c -= 32;
        name83[i] = c;
    }

    /* Find extension */
    const char *ext = str;
    while (*ext && *ext != '.') ext++;

    if (*ext == '.') {
        ext++;
        for (j = 0; j < 3 && ext[j]; j++) {
            char c = ext[j];
            if (c >= 'a' && c <= 'z') c -= 32;
            name83[8 + j] = c;
        }
    }
}

static int fat_name_match(const char *a, const char *b) {
    int i;
    for (i = 0; i < 11; i++) {
        if (a[i] != b[i]) return 0;
    }
    return 1;
}

/* List directory at given cluster (0 for root on FAT16) */
static int fs_ls_cluster(int device, uint32_t cluster, dir_entry_t *entries,
                         int max_entries, int *count) {
    fat_dir_entry_t *dir_entries;
    uint32_t sector;
    uint32_t sectors_to_read;
    int entry_count = 0;
    int done = 0;
    uint32_t s;
    int i;

    if (fs_state[device].type == 1 && cluster == 0) {
        /* FAT16 root directory */
        sector = fs_state[device].root_dir_sector;
        sectors_to_read = fs_state[device].root_dir_sectors;

        for (s = 0; s < sectors_to_read && !done; s++) {
            if (storage_read_blocks(device, sector + s, 1, sector_buf) != 0) {
                return -1;
            }

            dir_entries = (fat_dir_entry_t *)sector_buf;

            for (i = 0; i < 16 && !done; i++) {
                if (dir_entries[i].name[0] == 0x00) {
                    done = 1;
                    break;
                }

                if ((uint8_t)dir_entries[i].name[0] == 0xE5) continue;
                if (dir_entries[i].attributes == FAT_ATTR_LFN) continue;
                if (dir_entries[i].attributes & FAT_ATTR_VOLUME_ID) continue;

                if (entry_count < max_entries) {
                    fat_name_to_string(dir_entries[i].name, entries[entry_count].name);
                    entries[entry_count].attributes = dir_entries[i].attributes;
                    entries[entry_count].size = dir_entries[i].file_size;
                    entries[entry_count].cluster = ((uint32_t)dir_entries[i].first_cluster_high << 16) |
                                                   dir_entries[i].first_cluster_low;
                    entries[entry_count].date = dir_entries[i].modification_date;
                    entries[entry_count].time = dir_entries[i].modification_time;
                    entry_count++;
                }
            }
        }
    } else {
        /* FAT16 subdirectory or FAT32 directory */
        while (cluster >= 2 && cluster < 0x0FFFFFF8 && !done) {
            sector = fat_cluster_to_sector(device, cluster);

            for (s = 0; s < fs_state[device].sectors_per_cluster && !done; s++) {
                if (storage_read_blocks(device, sector + s, 1, sector_buf) != 0) {
                    return -1;
                }

                dir_entries = (fat_dir_entry_t *)sector_buf;

                for (i = 0; i < 16 && !done; i++) {
                    if (dir_entries[i].name[0] == 0x00) {
                        done = 1;
                        break;
                    }

                    if ((uint8_t)dir_entries[i].name[0] == 0xE5) continue;
                    if (dir_entries[i].attributes == FAT_ATTR_LFN) continue;
                    if (dir_entries[i].attributes & FAT_ATTR_VOLUME_ID) continue;

                    if (entry_count < max_entries) {
                        fat_name_to_string(dir_entries[i].name, entries[entry_count].name);
                        entries[entry_count].attributes = dir_entries[i].attributes;
                        entries[entry_count].size = dir_entries[i].file_size;
                        entries[entry_count].cluster = ((uint32_t)dir_entries[i].first_cluster_high << 16) |
                                                       dir_entries[i].first_cluster_low;
                        entries[entry_count].date = dir_entries[i].modification_date;
                        entries[entry_count].time = dir_entries[i].modification_time;
                        entry_count++;
                    }
                }
            }

            cluster = fat_get_next_cluster(device, cluster);
        }
    }

    *count = entry_count;
    return 0;
}

int fs_ls(int device, const char *path, dir_entry_t *entries, int max_entries, int *count) {
    uint32_t cluster;

    if (device < 0 || device >= STORAGE_MAX_DEVICES) {
        return -1;
    }

    if (!fs_state[device].mounted) {
        shell_printf("Filesystem not mounted\n");
        return -1;
    }

    /* For now, only support root directory */
    if (path == NULL || path[0] == '\0' || (path[0] == '/' && path[1] == '\0')) {
        if (fs_state[device].type == 2) {
            cluster = fs_state[device].root_dir_cluster;
        } else {
            cluster = 0;  /* FAT16 root */
        }

        return fs_ls_cluster(device, cluster, entries, max_entries, count);
    }

    shell_printf("Subdirectory listing not implemented\n");
    return -1;
}

/* Find file in directory */
static int fs_find_file(int device, const char *filename, uint32_t *cluster, uint32_t *size) {
    fat_dir_entry_t *dir_entries;
    char name83[11];
    uint32_t dir_cluster;
    uint32_t sector;
    int found = 0;
    uint32_t s;
    int i;

    string_to_fat_name(filename, name83);

    if (fs_state[device].type == 2) {
        dir_cluster = fs_state[device].root_dir_cluster;
    } else {
        dir_cluster = 0;
    }

    if (fs_state[device].type == 1 && dir_cluster == 0) {
        /* FAT16 root directory */
        for (s = 0; s < fs_state[device].root_dir_sectors && !found; s++) {
            sector = fs_state[device].root_dir_sector + s;

            if (storage_read_blocks(device, sector, 1, sector_buf) != 0) {
                return -1;
            }

            dir_entries = (fat_dir_entry_t *)sector_buf;

            for (i = 0; i < 16; i++) {
                if (dir_entries[i].name[0] == 0x00) {
                    return -1;  /* End of directory */
                }

                if ((uint8_t)dir_entries[i].name[0] == 0xE5) continue;
                if (dir_entries[i].attributes == FAT_ATTR_LFN) continue;
                if (dir_entries[i].attributes & FAT_ATTR_VOLUME_ID) continue;
                if (dir_entries[i].attributes & FAT_ATTR_DIRECTORY) continue;

                if (fat_name_match(dir_entries[i].name, name83)) {
                    *cluster = ((uint32_t)dir_entries[i].first_cluster_high << 16) |
                               dir_entries[i].first_cluster_low;
                    *size = dir_entries[i].file_size;
                    return 0;
                }
            }
        }
    } else {
        /* FAT16 subdirectory or FAT32 */
        while (dir_cluster >= 2 && dir_cluster < 0x0FFFFFF8 && !found) {
            sector = fat_cluster_to_sector(device, dir_cluster);

            for (s = 0; s < fs_state[device].sectors_per_cluster && !found; s++) {
                if (storage_read_blocks(device, sector + s, 1, sector_buf) != 0) {
                    return -1;
                }

                dir_entries = (fat_dir_entry_t *)sector_buf;

                for (i = 0; i < 16; i++) {
                    if (dir_entries[i].name[0] == 0x00) {
                        return -1;
                    }

                    if ((uint8_t)dir_entries[i].name[0] == 0xE5) continue;
                    if (dir_entries[i].attributes == FAT_ATTR_LFN) continue;
                    if (dir_entries[i].attributes & FAT_ATTR_VOLUME_ID) continue;
                    if (dir_entries[i].attributes & FAT_ATTR_DIRECTORY) continue;

                    if (fat_name_match(dir_entries[i].name, name83)) {
                        *cluster = ((uint32_t)dir_entries[i].first_cluster_high << 16) |
                                   dir_entries[i].first_cluster_low;
                        *size = dir_entries[i].file_size;
                        return 0;
                    }
                }
            }

            dir_cluster = fat_get_next_cluster(device, dir_cluster);
        }
    }

    return -1;
}

int fs_load(int device, const char *path, uint32_t load_addr, uint32_t max_size, uint32_t *actual_size) {
    uint32_t cluster;
    uint32_t file_size;
    uint32_t remaining;
    uint32_t sector;
    uint8_t *dest;
    uint32_t to_copy;
    uint32_t s;

    if (device < 0 || device >= STORAGE_MAX_DEVICES) {
        return -1;
    }

    if (!fs_state[device].mounted) {
        shell_printf("Filesystem not mounted\n");
        return -1;
    }

    /* Skip leading slash */
    if (path[0] == '/') path++;

    /* Find the file */
    if (fs_find_file(device, path, &cluster, &file_size) != 0) {
        shell_printf("File not found: %s\n", path);
        return -1;
    }

    if (file_size > max_size) {
        shell_printf("File too large: %u > %u\n", file_size, max_size);
        return -1;
    }

    shell_printf("Loading %s (%u bytes)...\n", path, file_size);

    dest = (uint8_t *)(uintptr_t)load_addr;
    remaining = file_size;

    while (remaining > 0 && cluster >= 2 && cluster < 0x0FFFFFF8) {
        sector = fat_cluster_to_sector(device, cluster);

        for (s = 0; s < fs_state[device].sectors_per_cluster && remaining > 0; s++) {
            if (storage_read_blocks(device, sector + s, 1, sector_buf) != 0) {
                shell_printf("Read error at sector %u\n", sector + s);
                return -1;
            }

            to_copy = (remaining > STORAGE_BLOCK_SIZE) ? STORAGE_BLOCK_SIZE : remaining;

            for (uint32_t b = 0; b < to_copy; b++) {
                dest[b] = sector_buf[b];
            }

            dest += to_copy;
            remaining -= to_copy;
        }

        cluster = fat_get_next_cluster(device, cluster);

        /* Progress indicator */
        if (((file_size - remaining) & 0x7FFF) == 0) {
            shell_printf(".");
        }
    }

    shell_printf("\n");

    *actual_size = file_size;

    /* Update environment */
    char size_str[16];
    shell_snprintf(size_str, sizeof(size_str), "%u", file_size);
    env_set("filesize", size_str);

    char addr_str[20];
    shell_snprintf(addr_str, sizeof(addr_str), "0x%x", load_addr);
    env_set("fileaddr", addr_str);

    return 0;
}

int fs_exists(int device, const char *path) {
    uint32_t cluster, size;

    if (!fs_state[device].mounted) {
        return 0;
    }

    if (path[0] == '/') path++;

    return (fs_find_file(device, path, &cluster, &size) == 0);
}

int fs_size(int device, const char *path, uint32_t *size) {
    uint32_t cluster;

    if (!fs_state[device].mounted) {
        return -1;
    }

    if (path[0] == '/') path++;

    return fs_find_file(device, path, &cluster, size);
}

/*
 * Shell Commands
 */

int cmd_mmc(int argc, char *argv[]) {
    if (argc > 1) {
        if (shell_strncmp(argv[1], "init", 4) == 0) {
            return storage_init();
        } else if (shell_strncmp(argv[1], "info", 4) == 0) {
            return cmd_mmcinfo(argc - 1, argv + 1);
        }
    }

    shell_printf("Usage: mmc init|info\n");
    shell_printf("  mmc init - Initialize storage\n");
    shell_printf("  mmc info - Show device info\n");
    return 0;
}

int cmd_mmcinfo(int argc, char *argv[]) {
    int device = 0;
    storage_info_t info;

    (void)argc;
    (void)argv;

    if (!storage_state.initialized) {
        shell_printf("No storage device initialized\n");
        return -1;
    }

    if (storage_get_info(device, &info) != 0) {
        shell_printf("Failed to get device info\n");
        return -1;
    }

    shell_printf("\nMMC Device %d:\n", device);
    shell_printf("  Type:     ");
    switch (info.type) {
        case STORAGE_TYPE_SD:   shell_printf("SD\n"); break;
        case STORAGE_TYPE_SDHC: shell_printf("SDHC\n"); break;
        case STORAGE_TYPE_SDXC: shell_printf("SDXC\n"); break;
        case STORAGE_TYPE_EMMC: shell_printf("eMMC\n"); break;
        case STORAGE_TYPE_MMC:  shell_printf("MMC\n"); break;
        default: shell_printf("Unknown\n"); break;
    }
    shell_printf("  Capacity: %u MB\n", (uint32_t)info.capacity_mb);
    shell_printf("  Blocks:   %u\n", (uint32_t)info.total_blocks);
    shell_printf("  Block sz: %u bytes\n", info.block_size);

    if (info.vendor[0]) {
        shell_printf("  Vendor:   %s\n", info.vendor);
    }
    if (info.product[0]) {
        shell_printf("  Product:  %s\n", info.product);
    }

    return 0;
}

int cmd_fatload(int argc, char *argv[]) {
    int device = 0;
    uint32_t load_addr;
    const char *filename;
    uint32_t size = 0;

    if (argc < 3) {
        shell_printf("Usage: fatload <device> <addr> <filename> [maxsize]\n");
        shell_printf("  device: mmc 0 (or just 0)\n");
        return -1;
    }

    /* Parse device - support "mmc 0" or just "0" */
    int arg_offset = 0;
    if (shell_strncmp(argv[1], "mmc", 3) == 0) {
        if (argc < 4) {
            shell_printf("Usage: fatload mmc <dev> <addr> <filename>\n");
            return -1;
        }
        device = shell_parse_u32(argv[2]);
        arg_offset = 1;
    } else {
        device = shell_parse_u32(argv[1]);
    }

    load_addr = shell_parse_addr(argv[2 + arg_offset]);
    filename = argv[3 + arg_offset];

    uint32_t max_size = 0x1000000;  /* 16MB default */
    if (argc > 4 + arg_offset) {
        max_size = shell_parse_u32(argv[4 + arg_offset]);
    }

    /* Mount filesystem if needed */
    if (!fs_state[device].mounted) {
        if (fs_mount(device) != 0) {
            return -1;
        }
    }

    /* Load file */
    if (fs_load(device, filename, load_addr, max_size, &size) != 0) {
        return -1;
    }

    shell_printf("Loaded %u bytes to 0x%X\n", size, load_addr);
    return 0;
}

int cmd_fatls(int argc, char *argv[]) {
    int device = 0;
    const char *path = "/";
    dir_entry_t entries[32];
    int count = 0;
    int i;

    if (argc > 1) {
        if (shell_strncmp(argv[1], "mmc", 3) == 0 && argc > 2) {
            device = shell_parse_u32(argv[2]);
            if (argc > 3) path = argv[3];
        } else {
            device = shell_parse_u32(argv[1]);
            if (argc > 2) path = argv[2];
        }
    }

    /* Mount filesystem if needed */
    if (!fs_state[device].mounted) {
        if (fs_mount(device) != 0) {
            return -1;
        }
    }

    if (fs_ls(device, path, entries, 32, &count) != 0) {
        return -1;
    }

    shell_printf("\n");
    for (i = 0; i < count; i++) {
        if (entries[i].attributes & FAT_ATTR_DIRECTORY) {
            shell_printf("  <DIR>     ");
        } else {
            shell_printf("  %8u  ", entries[i].size);
        }
        shell_printf("%s\n", entries[i].name);
    }
    shell_printf("\n%d file(s)\n", count);

    return 0;
}

int cmd_fatinfo(int argc, char *argv[]) {
    int device = 0;
    fs_info_t info;

    if (argc > 1) {
        if (shell_strncmp(argv[1], "mmc", 3) == 0 && argc > 2) {
            device = shell_parse_u32(argv[2]);
        } else {
            device = shell_parse_u32(argv[1]);
        }
    }

    /* Mount filesystem if needed */
    if (!fs_state[device].mounted) {
        if (fs_mount(device) != 0) {
            return -1;
        }
    }

    if (fs_info(device, &info) != 0) {
        shell_printf("Failed to get filesystem info\n");
        return -1;
    }

    shell_printf("\nFilesystem Info:\n");
    shell_printf("  Type:         FAT%d\n", info.type == 1 ? 16 : 32);
    shell_printf("  Volume:       %s\n", info.volume_label[0] ? info.volume_label : "(none)");
    shell_printf("  Clusters:     %u\n", info.total_clusters);
    shell_printf("  Cluster size: %u bytes\n", info.cluster_size);
    shell_printf("\n");

    return 0;
}

int cmd_fatsize(int argc, char *argv[]) {
    int device = 0;
    const char *filename;
    uint32_t size;
    int arg_offset = 0;

    if (argc < 2) {
        shell_printf("Usage: fatsize <device> <filename>\n");
        return -1;
    }

    if (shell_strncmp(argv[1], "mmc", 3) == 0 && argc > 2) {
        device = shell_parse_u32(argv[2]);
        arg_offset = 2;
    } else {
        arg_offset = 1;
    }

    if (argc <= arg_offset) {
        shell_printf("Usage: fatsize [mmc] <device> <filename>\n");
        return -1;
    }

    filename = argv[arg_offset + 1];

    /* Mount filesystem if needed */
    if (!fs_state[device].mounted) {
        if (fs_mount(device) != 0) {
            return -1;
        }
    }

    if (fs_size(device, filename, &size) != 0) {
        shell_printf("File not found: %s\n", filename);
        return -1;
    }

    shell_printf("%s: %u bytes\n", filename, size);

    /* Set environment variable */
    char size_str[16];
    shell_snprintf(size_str, sizeof(size_str), "%u", size);
    env_set("filesize", size_str);

    return 0;
}

int cmd_load(int argc, char *argv[]) {
    /* Alias for fatload */
    return cmd_fatload(argc, argv);
}
