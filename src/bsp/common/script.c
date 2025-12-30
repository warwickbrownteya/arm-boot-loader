/*
 * ARM Bootloader - Boot Script Implementation
 * U-Boot compatible script execution
 */

#include "script.h"
#include "shell.h"
#include "env.h"

/* ============================================================
 * U-Boot Image Support
 * ============================================================ */

/* Convert big-endian to host (assuming little endian ARM) */
static uint32_t be32_to_cpu(uint32_t val) {
    return ((val & 0xff) << 24) |
           ((val & 0xff00) << 8) |
           ((val & 0xff0000) >> 8) |
           ((val & 0xff000000) >> 24);
}

int script_is_uboot_image(bsp_addr_t addr) {
    const uboot_image_header_t *hdr = (const uboot_image_header_t *)(uintptr_t)addr;

    /* Check magic number */
    if (be32_to_cpu(hdr->ih_magic) != IH_MAGIC) {
        return 0;
    }

    /* Check if it's a script */
    if (hdr->ih_type != IH_TYPE_SCRIPT) {
        return 0;
    }

    return 1;
}

const char *script_get_uboot_data(bsp_addr_t addr, uint32_t *len) {
    const uboot_image_header_t *hdr = (const uboot_image_header_t *)(uintptr_t)addr;

    if (!script_is_uboot_image(addr)) {
        return NULL;
    }

    if (len) {
        *len = be32_to_cpu(hdr->ih_size);
    }

    /* Data starts after header */
    return (const char *)(uintptr_t)(addr + sizeof(uboot_image_header_t));
}

/* ============================================================
 * Script Execution
 * ============================================================ */

/* Execute a single line */
static int script_exec_line(const char *line, int len) {
    char buf[256];
    int i;

    /* Copy line to buffer (can't modify original) */
    if (len >= (int)sizeof(buf)) {
        len = sizeof(buf) - 1;
    }

    for (i = 0; i < len; i++) {
        buf[i] = line[i];
    }
    buf[len] = '\0';

    /* Skip leading whitespace */
    char *cmd = buf;
    while (*cmd == ' ' || *cmd == '\t') cmd++;

    /* Skip empty lines and comments */
    if (*cmd == '\0' || *cmd == '#') {
        return 0;
    }

    /* Execute command */
    return shell_exec(cmd);
}

int script_run(bsp_addr_t addr, uint32_t len) {
    const char *script;
    const char *line_start;
    uint32_t pos = 0;
    int line_len;
    int ret = 0;

    /* Check for U-Boot image format */
    if (script_is_uboot_image(addr)) {
        script = script_get_uboot_data(addr, &len);
        if (!script) {
            shell_printf("Script: Invalid U-Boot image\n");
            return -1;
        }
        shell_printf("Running U-Boot script...\n");
    } else {
        script = (const char *)(uintptr_t)addr;
        /* If len is 0, treat as null-terminated */
        if (len == 0) {
            len = 0xFFFFFFFF;  /* Will stop at null terminator */
        }
    }

    /* Process script line by line */
    line_start = script;
    while (pos < len && *line_start) {
        /* Find end of line */
        line_len = 0;
        while (pos + line_len < len &&
               line_start[line_len] != '\n' &&
               line_start[line_len] != '\r' &&
               line_start[line_len] != '\0') {
            line_len++;
        }

        /* Execute line */
        if (line_len > 0) {
            ret = script_exec_line(line_start, line_len);
            if (ret != 0) {
                /* Command failed - continue or abort based on first char */
                /* If line starts with '-', errors are ignored */
                if (line_start[0] != '-') {
                    shell_printf("Script: Command failed (error %d)\n", ret);
                    /* Continue anyway for now */
                }
            }
        }

        /* Move to next line */
        pos += line_len;
        line_start += line_len;

        /* Skip line ending */
        while (pos < len && (*line_start == '\n' || *line_start == '\r')) {
            pos++;
            line_start++;
        }
    }

    return 0;
}

int script_run_env(const char *name) {
    const char *cmd;

    if (!name) {
        return -1;
    }

    cmd = env_get(name);
    if (!cmd) {
        shell_printf("Script: Variable '%s' not set\n", name);
        return -1;
    }

    /* Execute as a simple command (environment vars are typically single commands) */
    return shell_exec(cmd);
}

int script_run_bootcmd(void) {
    return script_run_env("bootcmd");
}
