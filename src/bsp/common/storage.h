/*
 * storage.h - Storage Abstraction Layer for ARM Bootloader
 *
 * Provides a unified interface for storage devices:
 * - SD/SDHC/SDXC cards
 * - eMMC devices
 * - FAT filesystem support
 */

#ifndef STORAGE_H
#define STORAGE_H

#include <stdint.h>
#include <stddef.h>

/* Storage device types */
#define STORAGE_TYPE_NONE       0
#define STORAGE_TYPE_SD         1
#define STORAGE_TYPE_SDHC       2
#define STORAGE_TYPE_SDXC       3
#define STORAGE_TYPE_EMMC       4
#define STORAGE_TYPE_MMC        5

/* Storage block size */
#define STORAGE_BLOCK_SIZE      512

/* Maximum number of storage devices */
#define STORAGE_MAX_DEVICES     4

/* Maximum filename length */
#define STORAGE_MAX_FILENAME    256

/* FAT directory entry attributes */
#define FAT_ATTR_READ_ONLY      0x01
#define FAT_ATTR_HIDDEN         0x02
#define FAT_ATTR_SYSTEM         0x04
#define FAT_ATTR_VOLUME_ID      0x08
#define FAT_ATTR_DIRECTORY      0x10
#define FAT_ATTR_ARCHIVE        0x20
#define FAT_ATTR_LFN            0x0F

/* Storage device information */
typedef struct {
    int         type;               /* Device type */
    int         initialized;        /* Is device ready */
    uint32_t    block_size;         /* Block size (usually 512) */
    uint64_t    total_blocks;       /* Total blocks on device */
    uint64_t    capacity_mb;        /* Capacity in MB */
    char        vendor[16];         /* Vendor string */
    char        product[32];        /* Product string */
    char        serial[32];         /* Serial number */
} storage_info_t;

/* Filesystem information */
typedef struct {
    int         type;               /* 0=none, 1=FAT16, 2=FAT32 */
    int         initialized;        /* Is filesystem mounted */
    uint32_t    total_clusters;     /* Total clusters */
    uint32_t    free_clusters;      /* Free clusters */
    uint32_t    cluster_size;       /* Bytes per cluster */
    char        volume_label[12];   /* Volume label */
} fs_info_t;

/* Directory entry for listing */
typedef struct {
    char        name[STORAGE_MAX_FILENAME];
    uint8_t     attributes;
    uint32_t    size;
    uint32_t    cluster;
    uint16_t    date;
    uint16_t    time;
} dir_entry_t;

/* FAT32 Boot Sector / BPB */
typedef struct {
    uint8_t     jump[3];
    char        oem_name[8];
    uint16_t    bytes_per_sector;
    uint8_t     sectors_per_cluster;
    uint16_t    reserved_sectors;
    uint8_t     num_fats;
    uint16_t    root_entry_count;
    uint16_t    total_sectors_16;
    uint8_t     media_type;
    uint16_t    sectors_per_fat_16;
    uint16_t    sectors_per_track;
    uint16_t    num_heads;
    uint32_t    hidden_sectors;
    uint32_t    total_sectors_32;
    /* FAT32 extended fields */
    uint32_t    sectors_per_fat_32;
    uint16_t    ext_flags;
    uint16_t    fs_version;
    uint32_t    root_cluster;
    uint16_t    fs_info_sector;
    uint16_t    backup_boot_sector;
    uint8_t     reserved[12];
    uint8_t     drive_number;
    uint8_t     reserved1;
    uint8_t     boot_signature;
    uint32_t    volume_id;
    char        volume_label[11];
    char        fs_type[8];
} __attribute__((packed)) fat_boot_sector_t;

/* FAT32 Directory Entry */
typedef struct {
    char        name[11];
    uint8_t     attributes;
    uint8_t     nt_reserved;
    uint8_t     creation_time_tenth;
    uint16_t    creation_time;
    uint16_t    creation_date;
    uint16_t    access_date;
    uint16_t    first_cluster_high;
    uint16_t    modification_time;
    uint16_t    modification_date;
    uint16_t    first_cluster_low;
    uint32_t    file_size;
} __attribute__((packed)) fat_dir_entry_t;

/*
 * BSP Storage Driver Interface
 * Each BSP must implement these functions
 */

/* Initialize storage hardware */
int bsp_storage_init(int device);

/* Check if device is present */
int bsp_storage_present(int device);

/* Get device information */
int bsp_storage_info(int device, storage_info_t *info);

/* Read blocks from device */
int bsp_storage_read(int device, uint64_t block, uint32_t count, uint8_t *buffer);

/* Write blocks to device */
int bsp_storage_write(int device, uint64_t block, uint32_t count, const uint8_t *buffer);

/*
 * Storage Stack API
 */

/* Initialize storage subsystem */
int storage_init(void);

/* Get device info */
int storage_get_info(int device, storage_info_t *info);

/* Read raw blocks */
int storage_read_blocks(int device, uint64_t start, uint32_t count, uint8_t *buffer);

/* Write raw blocks */
int storage_write_blocks(int device, uint64_t start, uint32_t count, const uint8_t *buffer);

/*
 * Filesystem API
 */

/* Mount filesystem on device */
int fs_mount(int device);

/* Unmount filesystem */
int fs_unmount(int device);

/* Get filesystem info */
int fs_info(int device, fs_info_t *info);

/* List directory contents */
int fs_ls(int device, const char *path, dir_entry_t *entries, int max_entries, int *count);

/* Read file to memory */
int fs_load(int device, const char *path, uint32_t load_addr, uint32_t max_size, uint32_t *actual_size);

/* Check if path exists */
int fs_exists(int device, const char *path);

/* Get file size */
int fs_size(int device, const char *path, uint32_t *size);

/*
 * Shell Commands for Storage
 */

/* MMC/SD commands */
int cmd_mmc(int argc, char *argv[]);       /* MMC device info/control */
int cmd_mmcinfo(int argc, char *argv[]);   /* Show MMC device info */

/* FAT filesystem commands */
int cmd_fatload(int argc, char *argv[]);   /* Load file from FAT fs */
int cmd_fatls(int argc, char *argv[]);     /* List directory on FAT fs */
int cmd_fatinfo(int argc, char *argv[]);   /* Show FAT fs info */
int cmd_fatsize(int argc, char *argv[]);   /* Get file size */

/* Load commands */
int cmd_load(int argc, char *argv[]);      /* Generic file load */

#endif /* STORAGE_H */
