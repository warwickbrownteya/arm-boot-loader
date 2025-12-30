/*
 * ARM Bootloader - ELF Format Definitions
 * Supports both 32-bit and 64-bit ELF files
 */

#ifndef ELF_H
#define ELF_H

#include <stdint.h>

/* ============================================================
 * ELF Magic Number
 * ============================================================ */

#define ELF_MAGIC       0x464C457F  /* "\x7FELF" */

/* ELF identification indices */
#define EI_MAG0         0   /* File identification */
#define EI_MAG1         1
#define EI_MAG2         2
#define EI_MAG3         3
#define EI_CLASS        4   /* File class */
#define EI_DATA         5   /* Data encoding */
#define EI_VERSION      6   /* File version */
#define EI_OSABI        7   /* OS/ABI identification */
#define EI_ABIVERSION   8   /* ABI version */
#define EI_NIDENT       16  /* Size of e_ident */

/* ELF class */
#define ELFCLASS32      1   /* 32-bit objects */
#define ELFCLASS64      2   /* 64-bit objects */

/* ELF data encoding */
#define ELFDATA2LSB     1   /* Little endian */
#define ELFDATA2MSB     2   /* Big endian */

/* ELF type */
#define ET_NONE         0   /* No file type */
#define ET_REL          1   /* Relocatable file */
#define ET_EXEC         2   /* Executable file */
#define ET_DYN          3   /* Shared object file */

/* ELF machine types */
#define EM_ARM          40  /* ARM 32-bit */
#define EM_AARCH64      183 /* ARM 64-bit */

/* Program header types */
#define PT_NULL         0   /* Unused entry */
#define PT_LOAD         1   /* Loadable segment */
#define PT_DYNAMIC      2   /* Dynamic linking info */
#define PT_INTERP       3   /* Program interpreter */
#define PT_NOTE         4   /* Auxiliary information */

/* Program header flags */
#define PF_X            0x1 /* Execute */
#define PF_W            0x2 /* Write */
#define PF_R            0x4 /* Read */

/* ============================================================
 * 32-bit ELF Structures
 * ============================================================ */

typedef uint32_t Elf32_Addr;
typedef uint32_t Elf32_Off;
typedef uint16_t Elf32_Half;
typedef uint32_t Elf32_Word;
typedef int32_t  Elf32_Sword;

/* ELF32 Header */
typedef struct {
    uint8_t     e_ident[EI_NIDENT]; /* ELF identification */
    Elf32_Half  e_type;             /* Object file type */
    Elf32_Half  e_machine;          /* Machine type */
    Elf32_Word  e_version;          /* Object file version */
    Elf32_Addr  e_entry;            /* Entry point address */
    Elf32_Off   e_phoff;            /* Program header offset */
    Elf32_Off   e_shoff;            /* Section header offset */
    Elf32_Word  e_flags;            /* Processor-specific flags */
    Elf32_Half  e_ehsize;           /* ELF header size */
    Elf32_Half  e_phentsize;        /* Program header entry size */
    Elf32_Half  e_phnum;            /* Number of program headers */
    Elf32_Half  e_shentsize;        /* Section header entry size */
    Elf32_Half  e_shnum;            /* Number of section headers */
    Elf32_Half  e_shstrndx;         /* Section name string table index */
} Elf32_Ehdr;

/* ELF32 Program Header */
typedef struct {
    Elf32_Word  p_type;     /* Segment type */
    Elf32_Off   p_offset;   /* Offset in file */
    Elf32_Addr  p_vaddr;    /* Virtual address */
    Elf32_Addr  p_paddr;    /* Physical address */
    Elf32_Word  p_filesz;   /* Size in file */
    Elf32_Word  p_memsz;    /* Size in memory */
    Elf32_Word  p_flags;    /* Segment flags */
    Elf32_Word  p_align;    /* Alignment */
} Elf32_Phdr;

/* ============================================================
 * 64-bit ELF Structures
 * ============================================================ */

typedef uint64_t Elf64_Addr;
typedef uint64_t Elf64_Off;
typedef uint16_t Elf64_Half;
typedef uint32_t Elf64_Word;
typedef int32_t  Elf64_Sword;
typedef uint64_t Elf64_Xword;
typedef int64_t  Elf64_Sxword;

/* ELF64 Header */
typedef struct {
    uint8_t     e_ident[EI_NIDENT]; /* ELF identification */
    Elf64_Half  e_type;             /* Object file type */
    Elf64_Half  e_machine;          /* Machine type */
    Elf64_Word  e_version;          /* Object file version */
    Elf64_Addr  e_entry;            /* Entry point address */
    Elf64_Off   e_phoff;            /* Program header offset */
    Elf64_Off   e_shoff;            /* Section header offset */
    Elf64_Word  e_flags;            /* Processor-specific flags */
    Elf64_Half  e_ehsize;           /* ELF header size */
    Elf64_Half  e_phentsize;        /* Program header entry size */
    Elf64_Half  e_phnum;            /* Number of program headers */
    Elf64_Half  e_shentsize;        /* Section header entry size */
    Elf64_Half  e_shnum;            /* Number of section headers */
    Elf64_Half  e_shstrndx;         /* Section name string table index */
} Elf64_Ehdr;

/* ELF64 Program Header */
typedef struct {
    Elf64_Word  p_type;     /* Segment type */
    Elf64_Word  p_flags;    /* Segment flags */
    Elf64_Off   p_offset;   /* Offset in file */
    Elf64_Addr  p_vaddr;    /* Virtual address */
    Elf64_Addr  p_paddr;    /* Physical address */
    Elf64_Xword p_filesz;   /* Size in file */
    Elf64_Xword p_memsz;    /* Size in memory */
    Elf64_Xword p_align;    /* Alignment */
} Elf64_Phdr;

/* ============================================================
 * ELF Loader Functions
 * ============================================================ */

/* Check if address points to valid ELF file */
int elf_check(bsp_addr_t addr);

/* Get ELF class (32 or 64 bit) */
int elf_get_class(bsp_addr_t addr);

/* Get ELF entry point */
bsp_addr_t elf_get_entry(bsp_addr_t addr);

/* Load ELF segments to memory, returns entry point or 0 on error */
bsp_addr_t elf_load(bsp_addr_t addr);

/* Get ELF file info (for display) */
typedef struct {
    int         is_valid;
    int         class;          /* 32 or 64 */
    int         machine;        /* EM_ARM or EM_AARCH64 */
    bsp_addr_t  entry;          /* Entry point */
    int         phnum;          /* Number of program headers */
    bsp_addr_t  load_addr;      /* Lowest load address */
    bsp_addr_t  load_end;       /* Highest load address + size */
} elf_info_t;

int elf_get_info(bsp_addr_t addr, elf_info_t *info);

#endif /* ELF_H */
