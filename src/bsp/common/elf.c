/*
 * ARM Bootloader - ELF Loader Implementation
 * Loads 32-bit and 64-bit ELF executables
 */

#include "bsp.h"
#include "elf.h"
#include "shell.h"

/* ============================================================
 * Memory Copy Helper
 * ============================================================ */

static void elf_memcpy(void *dst, const void *src, uint32_t n) {
    uint8_t *d = dst;
    const uint8_t *s = src;
    while (n--) *d++ = *s++;
}

static void elf_memset(void *dst, int c, uint32_t n) {
    uint8_t *d = dst;
    while (n--) *d++ = c;
}

/* ============================================================
 * ELF Validation
 * ============================================================ */

int elf_check(bsp_addr_t addr) {
    const uint8_t *magic = (const uint8_t *)(uintptr_t)addr;

    /* Check ELF magic number */
    if (magic[0] != 0x7F || magic[1] != 'E' ||
        magic[2] != 'L' || magic[3] != 'F') {
        return -1;
    }

    /* Check class */
    if (magic[EI_CLASS] != ELFCLASS32 && magic[EI_CLASS] != ELFCLASS64) {
        return -1;
    }

    /* Check data encoding (we only support little endian) */
    if (magic[EI_DATA] != ELFDATA2LSB) {
        return -1;
    }

    return 0;
}

int elf_get_class(bsp_addr_t addr) {
    const uint8_t *magic = (const uint8_t *)(uintptr_t)addr;

    if (elf_check(addr) != 0) return 0;

    return magic[EI_CLASS] == ELFCLASS64 ? 64 : 32;
}

/* ============================================================
 * ELF64 Loader
 * ============================================================ */

#ifdef BSP_ARCH_64BIT
static bsp_addr_t elf64_load(bsp_addr_t addr) {
    const Elf64_Ehdr *ehdr = (const Elf64_Ehdr *)(uintptr_t)addr;
    const Elf64_Phdr *phdr;
    int i;

    /* Validate machine type */
    if (ehdr->e_machine != EM_AARCH64) {
        shell_printf("ELF: Wrong machine type (expected AARCH64)\n");
        return 0;
    }

    /* Validate executable type */
    if (ehdr->e_type != ET_EXEC && ehdr->e_type != ET_DYN) {
        shell_printf("ELF: Not an executable\n");
        return 0;
    }

    /* Load program segments */
    phdr = (const Elf64_Phdr *)(uintptr_t)(addr + ehdr->e_phoff);

    for (i = 0; i < ehdr->e_phnum; i++) {
        if (phdr[i].p_type != PT_LOAD) continue;

        /* Source in file */
        const void *src = (const void *)(uintptr_t)(addr + phdr[i].p_offset);

        /* Destination in memory */
        void *dst = (void *)(uintptr_t)phdr[i].p_paddr;

        /* Copy file data */
        if (phdr[i].p_filesz > 0) {
            elf_memcpy(dst, src, phdr[i].p_filesz);
        }

        /* Zero BSS (difference between memory size and file size) */
        if (phdr[i].p_memsz > phdr[i].p_filesz) {
            elf_memset((uint8_t *)dst + phdr[i].p_filesz, 0,
                       phdr[i].p_memsz - phdr[i].p_filesz);
        }
    }

    /* Flush caches */
    bsp_dsb();
    bsp_isb();

    return ehdr->e_entry;
}
#endif

/* ============================================================
 * ELF32 Loader
 * ============================================================ */

static bsp_addr_t elf32_load(bsp_addr_t addr) {
    const Elf32_Ehdr *ehdr = (const Elf32_Ehdr *)(uintptr_t)addr;
    const Elf32_Phdr *phdr;
    int i;

    /* Validate machine type */
#ifdef BSP_ARCH_64BIT
    /* Allow loading 32-bit ELF on 64-bit, but warn */
    if (ehdr->e_machine != EM_ARM) {
        shell_printf("ELF: Wrong machine type (expected ARM)\n");
        return 0;
    }
    shell_printf("ELF: Warning - loading 32-bit ELF on 64-bit platform\n");
#else
    if (ehdr->e_machine != EM_ARM) {
        shell_printf("ELF: Wrong machine type (expected ARM)\n");
        return 0;
    }
#endif

    /* Validate executable type */
    if (ehdr->e_type != ET_EXEC && ehdr->e_type != ET_DYN) {
        shell_printf("ELF: Not an executable\n");
        return 0;
    }

    /* Load program segments */
    phdr = (const Elf32_Phdr *)(uintptr_t)(addr + ehdr->e_phoff);

    for (i = 0; i < ehdr->e_phnum; i++) {
        if (phdr[i].p_type != PT_LOAD) continue;

        /* Source in file */
        const void *src = (const void *)(uintptr_t)(addr + phdr[i].p_offset);

        /* Destination in memory */
        void *dst = (void *)(uintptr_t)phdr[i].p_paddr;

        /* Copy file data */
        if (phdr[i].p_filesz > 0) {
            elf_memcpy(dst, src, phdr[i].p_filesz);
        }

        /* Zero BSS */
        if (phdr[i].p_memsz > phdr[i].p_filesz) {
            elf_memset((uint8_t *)dst + phdr[i].p_filesz, 0,
                       phdr[i].p_memsz - phdr[i].p_filesz);
        }
    }

    /* Flush caches */
    bsp_dsb();
    bsp_isb();

    return ehdr->e_entry;
}

/* ============================================================
 * Public ELF Loader API
 * ============================================================ */

bsp_addr_t elf_get_entry(bsp_addr_t addr) {
    if (elf_check(addr) != 0) return 0;

    int class = elf_get_class(addr);
    if (class == 64) {
#ifdef BSP_ARCH_64BIT
        const Elf64_Ehdr *ehdr = (const Elf64_Ehdr *)(uintptr_t)addr;
        return ehdr->e_entry;
#else
        return 0;  /* Cannot load 64-bit ELF on 32-bit platform */
#endif
    } else {
        const Elf32_Ehdr *ehdr = (const Elf32_Ehdr *)(uintptr_t)addr;
        return ehdr->e_entry;
    }
}

bsp_addr_t elf_load(bsp_addr_t addr) {
    if (elf_check(addr) != 0) {
        shell_printf("ELF: Invalid ELF file\n");
        return 0;
    }

    int class = elf_get_class(addr);
    if (class == 64) {
#ifdef BSP_ARCH_64BIT
        return elf64_load(addr);
#else
        shell_printf("ELF: Cannot load 64-bit ELF on 32-bit platform\n");
        return 0;
#endif
    } else {
        return elf32_load(addr);
    }
}

int elf_get_info(bsp_addr_t addr, elf_info_t *info) {
    if (!info) return -1;

    info->is_valid = 0;
    info->class = 0;
    info->machine = 0;
    info->entry = 0;
    info->phnum = 0;
    info->load_addr = 0;
    info->load_end = 0;

    if (elf_check(addr) != 0) return -1;

    info->is_valid = 1;
    info->class = elf_get_class(addr);

    if (info->class == 64) {
#ifdef BSP_ARCH_64BIT
        const Elf64_Ehdr *ehdr = (const Elf64_Ehdr *)(uintptr_t)addr;
        const Elf64_Phdr *phdr = (const Elf64_Phdr *)(uintptr_t)(addr + ehdr->e_phoff);
        int i;

        info->machine = ehdr->e_machine;
        info->entry = ehdr->e_entry;
        info->phnum = ehdr->e_phnum;

        /* Find load range */
        for (i = 0; i < ehdr->e_phnum; i++) {
            if (phdr[i].p_type != PT_LOAD) continue;

            if (info->load_addr == 0 || phdr[i].p_paddr < info->load_addr) {
                info->load_addr = phdr[i].p_paddr;
            }

            bsp_addr_t end = phdr[i].p_paddr + phdr[i].p_memsz;
            if (end > info->load_end) {
                info->load_end = end;
            }
        }
#else
        return -1;
#endif
    } else {
        const Elf32_Ehdr *ehdr = (const Elf32_Ehdr *)(uintptr_t)addr;
        const Elf32_Phdr *phdr = (const Elf32_Phdr *)(uintptr_t)(addr + ehdr->e_phoff);
        int i;

        info->machine = ehdr->e_machine;
        info->entry = ehdr->e_entry;
        info->phnum = ehdr->e_phnum;

        /* Find load range */
        for (i = 0; i < ehdr->e_phnum; i++) {
            if (phdr[i].p_type != PT_LOAD) continue;

            if (info->load_addr == 0 || phdr[i].p_paddr < info->load_addr) {
                info->load_addr = phdr[i].p_paddr;
            }

            bsp_addr_t end = phdr[i].p_paddr + phdr[i].p_memsz;
            if (end > info->load_end) {
                info->load_end = end;
            }
        }
    }

    return 0;
}
