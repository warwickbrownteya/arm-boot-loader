/*
 * SD Card and FAT32 Filesystem Header
 * For Raspberry Pi 3/4 BCM2837/BCM2711
 */

#ifndef SD_H
#define SD_H

#include <stdint.h>

/* ============================================================
 * SD Card Interface
 * ============================================================ */

/*
 * Initialize the SD card
 * Returns: 0 on success, -1 on failure
 */
int sd_init(void);

/*
 * Read a single 512-byte sector from the SD card
 * sector: sector number (LBA)
 * buffer: pointer to 512-byte buffer
 * Returns: 0 on success, -1 on failure
 */
int sd_read_sector(uint32_t sector, uint8_t *buffer);

/*
 * Read multiple consecutive sectors
 * start_sector: first sector number (LBA)
 * count: number of sectors to read
 * buffer: pointer to buffer (must be count * 512 bytes)
 * Returns: 0 on success, -1 on failure
 */
int sd_read_sectors(uint32_t start_sector, uint32_t count, uint8_t *buffer);

/*
 * Check if SD card is initialized
 * Returns: 1 if initialized, 0 if not
 */
int sd_is_initialized(void);

/* ============================================================
 * FAT32 Filesystem Interface
 * ============================================================ */

/* FAT32 Boot Sector / BPB structure */
typedef struct {
    uint8_t  jump[3];              /* 0x00: Jump instruction */
    char     oem_name[8];          /* 0x03: OEM name */
    uint16_t bytes_per_sector;     /* 0x0B: Bytes per sector (512) */
    uint8_t  sectors_per_cluster;  /* 0x0D: Sectors per cluster */
    uint16_t reserved_sectors;     /* 0x0E: Reserved sectors before FAT */
    uint8_t  num_fats;             /* 0x10: Number of FATs (usually 2) */
    uint16_t root_entries;         /* 0x11: Root entries (0 for FAT32) */
    uint16_t total_sectors_16;     /* 0x13: Total sectors (0 for FAT32) */
    uint8_t  media_descriptor;     /* 0x15: Media descriptor */
    uint16_t sectors_per_fat_16;   /* 0x16: Sectors per FAT (0 for FAT32) */
    uint16_t sectors_per_track;    /* 0x18: Sectors per track */
    uint16_t num_heads;            /* 0x1A: Number of heads */
    uint32_t hidden_sectors;       /* 0x1C: Hidden sectors */
    uint32_t total_sectors_32;     /* 0x20: Total sectors (32-bit) */
    /* FAT32 specific fields */
    uint32_t sectors_per_fat_32;   /* 0x24: Sectors per FAT */
    uint16_t flags;                /* 0x28: FAT flags */
    uint16_t version;              /* 0x2A: FAT32 version */
    uint32_t root_cluster;         /* 0x2C: Root directory cluster */
    uint16_t fs_info_sector;       /* 0x30: FSInfo sector */
    uint16_t backup_boot_sector;   /* 0x32: Backup boot sector */
    uint8_t  reserved[12];         /* 0x34: Reserved */
    uint8_t  drive_number;         /* 0x40: Drive number */
    uint8_t  reserved1;            /* 0x41: Reserved */
    uint8_t  boot_signature;       /* 0x42: Extended boot signature */
    uint32_t volume_id;            /* 0x43: Volume ID */
    char     volume_label[11];     /* 0x47: Volume label */
    char     fs_type[8];           /* 0x52: File system type */
} __attribute__((packed)) fat_boot_sector_t;

/* FAT32 Directory Entry structure */
typedef struct {
    char     name[11];             /* 0x00: 8.3 filename */
    uint8_t  attributes;           /* 0x0B: File attributes */
    uint8_t  reserved;             /* 0x0C: Reserved (NT) */
    uint8_t  creation_time_tenths; /* 0x0D: Creation time (tenths of second) */
    uint16_t creation_time;        /* 0x0E: Creation time */
    uint16_t creation_date;        /* 0x10: Creation date */
    uint16_t last_access_date;     /* 0x12: Last access date */
    uint16_t first_cluster_high;   /* 0x14: High 16 bits of cluster */
    uint16_t last_mod_time;        /* 0x16: Last modification time */
    uint16_t last_mod_date;        /* 0x18: Last modification date */
    uint16_t first_cluster_low;    /* 0x1A: Low 16 bits of cluster */
    uint32_t file_size;            /* 0x1C: File size in bytes */
} __attribute__((packed)) fat_dir_entry_t;

/* File attribute flags */
#define FAT_ATTR_READ_ONLY  0x01
#define FAT_ATTR_HIDDEN     0x02
#define FAT_ATTR_SYSTEM     0x04
#define FAT_ATTR_VOLUME_ID  0x08
#define FAT_ATTR_DIRECTORY  0x10
#define FAT_ATTR_ARCHIVE    0x20
#define FAT_ATTR_LONG_NAME  0x0F

/*
 * Initialize FAT32 filesystem
 * Must be called after sd_init()
 * Returns: 0 on success, -1 on failure
 */
int fat_init(void);

/*
 * Read a file from the filesystem
 * filename: name of file (e.g., "kernel8.img")
 * load_addr: memory address to load file to
 * size: pointer to receive file size
 * Returns: 0 on success, -1 on failure
 */
int fat_read_file(const char *filename, uint32_t load_addr, uint32_t *size);

#endif /* SD_H */
