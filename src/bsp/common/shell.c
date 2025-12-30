/*
 * ARM Bootloader - Command Shell Implementation
 * U-Boot compatible command line interface
 */

#include "shell.h"
#include "boot_common.h"
#include "env.h"
#include "elf.h"
#include "script.h"
#include "net.h"
#include "storage.h"
#include <stdarg.h>

/* ============================================================
 * String Utilities
 * ============================================================ */

int shell_strlen(const char *s) {
    int len = 0;
    while (*s++) len++;
    return len;
}

char *shell_strcpy(char *dst, const char *src) {
    char *d = dst;
    while ((*d++ = *src++));
    return dst;
}

int shell_strncmp(const char *s1, const char *s2, int n) {
    while (n-- && *s1 && *s2) {
        if (*s1 != *s2) return *s1 - *s2;
        s1++; s2++;
    }
    if (n < 0) return 0;
    return *s1 - *s2;
}

static int shell_strcmp(const char *s1, const char *s2) {
    while (*s1 && *s2) {
        if (*s1 != *s2) return *s1 - *s2;
        s1++; s2++;
    }
    return *s1 - *s2;
}

void *shell_memcpy(void *dst, const void *src, int n) {
    char *d = dst;
    const char *s = src;
    while (n--) *d++ = *s++;
    return dst;
}

void *shell_memset(void *dst, int c, int n) {
    char *d = dst;
    while (n--) *d++ = c;
    return dst;
}

/* ============================================================
 * Number Parsing
 * ============================================================ */

static int is_hex_digit(char c) {
    return (c >= '0' && c <= '9') ||
           (c >= 'a' && c <= 'f') ||
           (c >= 'A' && c <= 'F');
}

static int hex_value(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return 0;
}

bsp_addr_t shell_parse_addr(const char *str) {
    bsp_addr_t val = 0;
    int is_hex = 0;

    /* Skip whitespace */
    while (*str == ' ' || *str == '\t') str++;

    /* Check for hex prefix */
    if (str[0] == '0' && (str[1] == 'x' || str[1] == 'X')) {
        is_hex = 1;
        str += 2;
    }

    if (is_hex) {
        while (is_hex_digit(*str)) {
            val = (val << 4) | hex_value(*str++);
        }
    } else {
        while (*str >= '0' && *str <= '9') {
            val = val * 10 + (*str++ - '0');
        }
    }

    return val;
}

uint32_t shell_parse_u32(const char *str) {
    return (uint32_t)shell_parse_addr(str);
}

/* ============================================================
 * Output Functions
 * ============================================================ */

/* Print a single character */
static void shell_putc(char c) {
    bsp_uart_putc(c);
}

/* Print a string */
static void shell_puts(const char *s) {
    while (*s) shell_putc(*s++);
}

/* Print hex value (various sizes) */
static void shell_print_hex8(uint8_t val) {
    static const char hex[] = "0123456789abcdef";
    shell_putc(hex[(val >> 4) & 0xf]);
    shell_putc(hex[val & 0xf]);
}

static void shell_print_hex32(uint32_t val) {
    shell_print_hex8((val >> 24) & 0xff);
    shell_print_hex8((val >> 16) & 0xff);
    shell_print_hex8((val >> 8) & 0xff);
    shell_print_hex8(val & 0xff);
}

#ifdef BSP_ARCH_64BIT
static void shell_print_hex64(uint64_t val) {
    shell_print_hex32((val >> 32) & 0xffffffff);
    shell_print_hex32(val & 0xffffffff);
}
#endif

static void shell_print_addr(bsp_addr_t val) {
#ifdef BSP_ARCH_64BIT
    shell_print_hex64(val);
#else
    shell_print_hex32(val);
#endif
}

static void shell_print_dec(int32_t val) {
    char buf[12];
    int i = 10;
    int neg = 0;

    if (val < 0) {
        neg = 1;
        val = -val;
    }

    buf[11] = '\0';
    if (val == 0) {
        buf[i--] = '0';
    } else {
        while (val > 0 && i >= 0) {
            buf[i--] = '0' + (val % 10);
            val /= 10;
        }
    }
    if (neg) buf[i--] = '-';
    shell_puts(&buf[i + 1]);
}

static void shell_print_udec(uint32_t val) {
    char buf[12];
    int i = 10;

    buf[11] = '\0';
    if (val == 0) {
        buf[i--] = '0';
    } else {
        while (val > 0 && i >= 0) {
            buf[i--] = '0' + (val % 10);
            val /= 10;
        }
    }
    shell_puts(&buf[i + 1]);
}

/* Simple printf implementation with width support */
void shell_printf(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);

    while (*fmt) {
        if (*fmt == '%') {
            fmt++;
            int left_justify = 0;
            int width = 0;

            /* Check for left justify */
            if (*fmt == '-') {
                left_justify = 1;
                fmt++;
            }

            /* Parse width */
            while (*fmt >= '0' && *fmt <= '9') {
                width = width * 10 + (*fmt - '0');
                fmt++;
            }

            switch (*fmt) {
                case 's': {
                    const char *s = va_arg(ap, char*);
                    int len = shell_strlen(s);
                    if (left_justify) {
                        shell_puts(s);
                        while (len < width) { shell_putc(' '); len++; }
                    } else {
                        while (len < width) { shell_putc(' '); len++; }
                        shell_puts(s);
                    }
                    break;
                }
                case 'd':
                case 'i':
                    shell_print_dec(va_arg(ap, int32_t));
                    break;
                case 'u':
                    shell_print_udec(va_arg(ap, uint32_t));
                    break;
                case 'x':
                    shell_print_hex32(va_arg(ap, uint32_t));
                    break;
                case 'p':
                case 'X':
                    shell_print_addr(va_arg(ap, bsp_addr_t));
                    break;
                case 'c':
                    shell_putc((char)va_arg(ap, int));
                    break;
                case '%':
                    shell_putc('%');
                    break;
                default:
                    shell_putc('%');
                    shell_putc(*fmt);
            }
        } else if (*fmt == '\n') {
            shell_putc('\r');
            shell_putc('\n');
        } else {
            shell_putc(*fmt);
        }
        fmt++;
    }

    va_end(ap);
}

/* Simple snprintf implementation */
int shell_snprintf(char *buf, int size, const char *fmt, ...) {
    va_list ap;
    int pos = 0;

    va_start(ap, fmt);

    while (*fmt && pos < size - 1) {
        if (*fmt == '%') {
            fmt++;

            switch (*fmt) {
                case 's': {
                    const char *s = va_arg(ap, char*);
                    while (*s && pos < size - 1) {
                        buf[pos++] = *s++;
                    }
                    break;
                }
                case 'd':
                case 'i': {
                    int32_t val = va_arg(ap, int32_t);
                    char tmp[12];
                    int i = 10;
                    int neg = 0;
                    if (val < 0) { neg = 1; val = -val; }
                    tmp[11] = '\0';
                    if (val == 0) tmp[i--] = '0';
                    while (val > 0 && i >= 0) {
                        tmp[i--] = '0' + (val % 10);
                        val /= 10;
                    }
                    if (neg) tmp[i--] = '-';
                    const char *p = &tmp[i + 1];
                    while (*p && pos < size - 1) buf[pos++] = *p++;
                    break;
                }
                case 'u': {
                    uint32_t val = va_arg(ap, uint32_t);
                    char tmp[12];
                    int i = 10;
                    tmp[11] = '\0';
                    if (val == 0) tmp[i--] = '0';
                    while (val > 0 && i >= 0) {
                        tmp[i--] = '0' + (val % 10);
                        val /= 10;
                    }
                    const char *p = &tmp[i + 1];
                    while (*p && pos < size - 1) buf[pos++] = *p++;
                    break;
                }
                case 'x': {
                    uint32_t val = va_arg(ap, uint32_t);
                    static const char hex[] = "0123456789abcdef";
                    char tmp[9];
                    int i = 7;
                    tmp[8] = '\0';
                    if (val == 0) tmp[i--] = '0';
                    while (val > 0 && i >= 0) {
                        tmp[i--] = hex[val & 0xf];
                        val >>= 4;
                    }
                    const char *p = &tmp[i + 1];
                    while (*p && pos < size - 1) buf[pos++] = *p++;
                    break;
                }
                case 'c':
                    buf[pos++] = (char)va_arg(ap, int);
                    break;
                case '%':
                    buf[pos++] = '%';
                    break;
                default:
                    buf[pos++] = '%';
                    if (pos < size - 1) buf[pos++] = *fmt;
            }
        } else {
            buf[pos++] = *fmt;
        }
        fmt++;
    }

    buf[pos] = '\0';
    va_end(ap);
    return pos;
}

/* ============================================================
 * Command Table
 * ============================================================ */

/* Built-in commands */
static const shell_cmd_t builtin_cmds[] = {
    /* Core commands */
    {"help",     cmd_help,     "help [cmd]",     "Print help"},
    {"?",        cmd_help,     "? [cmd]",        "Alias for help"},
    {"info",     cmd_info,     "info",           "System information"},
    {"version",  cmd_version,  "version",        "Bootloader version"},
    {"reset",    cmd_reset,    "reset",          "Reset the system"},

    /* Memory commands */
    {"md",       cmd_md,       "md[.b/.w/.l] addr [count]", "Memory display"},
    {"mw",       cmd_mw,       "mw[.b/.w/.l] addr val [count]", "Memory write"},
    {"mm",       cmd_mm,       "mm[.b/.w/.l] addr", "Memory modify (interactive)"},
    {"cp",       cmd_cp,       "cp[.b/.w/.l] src dst count", "Copy memory"},
    {"cmp",      cmd_cmp,      "cmp[.b/.w/.l] addr1 addr2 count", "Compare memory"},
    {"mtest",    cmd_mtest,    "mtest [start [end [pattern]]]", "Memory test"},

    /* Boot commands */
    {"boot",     cmd_boot,     "boot",           "Boot default kernel"},
    {"bootm",    cmd_bootm,    "bootm [addr [initrd [fdt]]]", "Boot from memory"},
    {"go",       cmd_go,       "go addr [args]", "Jump to address"},

    /* Environment commands */
    {"env",      cmd_env,      "env",            "Environment commands"},
    {"setenv",   cmd_setenv,   "setenv name [value]", "Set environment variable"},
    {"printenv", cmd_printenv, "printenv [name]", "Print environment"},
    {"saveenv",  cmd_saveenv,  "saveenv",        "Save environment (not implemented)"},

    /* Test commands */
    {"test",     cmd_test,     "test [uart|timer|gpio|mem|all]", "Run tests"},
    {"timer",    cmd_timer,    "timer [delay_ms]", "Timer test"},
    {"gpio",     cmd_gpio,     "gpio [pin] [0|1]", "GPIO control"},

    /* ELF commands */
    {"elfinfo",  cmd_elfinfo,  "elfinfo addr", "Display ELF file info"},
    {"loadelf",  cmd_loadelf,  "loadelf addr", "Load and run ELF file"},

    /* Script commands */
    {"source",   cmd_source,   "source addr [len]", "Run script from memory"},
    {"run",      cmd_run,      "run var [var...]", "Run env variable as command"},

    /* Network commands */
    {"net",      cmd_net,      "net [init|info]", "Network status/config"},
    {"dhcp",     cmd_dhcp,     "dhcp",            "Get IP via DHCP"},
    {"ping",     cmd_ping,     "ping ip [count]", "Ping host"},
    {"tftp",     cmd_tftp,     "tftp addr filename [ip]", "Download via TFTP"},
    {"tftpboot", cmd_tftp,     "tftpboot addr filename", "Alias for tftp"},

    /* Storage commands */
    {"mmc",      cmd_mmc,      "mmc init|info",   "MMC/SD device control"},
    {"mmcinfo",  cmd_mmcinfo,  "mmcinfo",         "Show MMC device info"},
    {"fatload",  cmd_fatload,  "fatload dev addr file", "Load file from FAT"},
    {"fatls",    cmd_fatls,    "fatls [dev] [path]", "List FAT directory"},
    {"fatinfo",  cmd_fatinfo,  "fatinfo [dev]",   "Show FAT filesystem info"},
    {"fatsize",  cmd_fatsize,  "fatsize dev file", "Get file size"},
    {"load",     cmd_load,     "load dev addr file", "Load file (alias fatload)"},

    {NULL, NULL, NULL, NULL}  /* Terminator */
};

/* Find a command by name */
static const shell_cmd_t *find_cmd(const char *name) {
    const shell_cmd_t *cmd = builtin_cmds;

    while (cmd->name) {
        if (shell_strcmp(cmd->name, name) == 0) {
            return cmd;
        }
        cmd++;
    }
    return NULL;
}

/* ============================================================
 * Line Reading with Editing
 * ============================================================ */

/* Command history */
static char history[SHELL_HISTORY_SIZE][SHELL_MAX_LINE];
static int history_count = 0;
static int history_index = 0;

/* Add to history */
static void history_add(const char *line) {
    if (shell_strlen(line) == 0) return;

    shell_strcpy(history[history_count % SHELL_HISTORY_SIZE], line);
    history_count++;
    history_index = history_count;
}

/* Get from history */
static const char *history_get(int index) {
    if (index < 0 || index >= history_count) return NULL;
    if (history_count > SHELL_HISTORY_SIZE &&
        index < history_count - SHELL_HISTORY_SIZE) return NULL;
    return history[index % SHELL_HISTORY_SIZE];
}

/* Read a line with basic editing */
int shell_readline(char *buf, int maxlen) {
    int pos = 0;
    int len = 0;
    int c;
    int hist_pos = history_count;

    shell_memset(buf, 0, maxlen);

    while (1) {
        c = bsp_uart_getc();

        if (c == '\r' || c == '\n') {
            /* Enter - finish line */
            shell_puts("\r\n");
            buf[len] = '\0';
            if (len > 0) history_add(buf);
            return len;
        }
        else if (c == '\b' || c == 0x7F) {
            /* Backspace */
            if (pos > 0) {
                /* Move characters left */
                for (int i = pos - 1; i < len - 1; i++) {
                    buf[i] = buf[i + 1];
                }
                pos--;
                len--;
                buf[len] = '\0';

                /* Redraw line */
                shell_putc('\b');
                for (int i = pos; i < len; i++) {
                    shell_putc(buf[i]);
                }
                shell_putc(' ');
                for (int i = pos; i <= len; i++) {
                    shell_putc('\b');
                }
            }
        }
        else if (c == 0x03) {
            /* Ctrl+C - cancel */
            shell_puts("^C\r\n");
            return -1;
        }
        else if (c == 0x15) {
            /* Ctrl+U - clear line */
            while (pos > 0) {
                shell_putc('\b');
                pos--;
            }
            for (int i = 0; i < len; i++) {
                shell_putc(' ');
            }
            for (int i = 0; i < len; i++) {
                shell_putc('\b');
            }
            len = 0;
            pos = 0;
            buf[0] = '\0';
        }
        else if (c == 0x1B) {
            /* Escape sequence */
            c = bsp_uart_getc();
            if (c == '[') {
                c = bsp_uart_getc();
                if (c == 'A') {
                    /* Up arrow - history back */
                    if (hist_pos > 0 && hist_pos > history_count - SHELL_HISTORY_SIZE) {
                        hist_pos--;
                        const char *h = history_get(hist_pos);
                        if (h) {
                            /* Clear current line */
                            while (pos > 0) { shell_putc('\b'); pos--; }
                            for (int i = 0; i < len; i++) shell_putc(' ');
                            for (int i = 0; i < len; i++) shell_putc('\b');

                            /* Copy history */
                            shell_strcpy(buf, h);
                            len = shell_strlen(buf);
                            pos = len;
                            shell_puts(buf);
                        }
                    }
                }
                else if (c == 'B') {
                    /* Down arrow - history forward */
                    if (hist_pos < history_count - 1) {
                        hist_pos++;
                        const char *h = history_get(hist_pos);
                        if (h) {
                            while (pos > 0) { shell_putc('\b'); pos--; }
                            for (int i = 0; i < len; i++) shell_putc(' ');
                            for (int i = 0; i < len; i++) shell_putc('\b');

                            shell_strcpy(buf, h);
                            len = shell_strlen(buf);
                            pos = len;
                            shell_puts(buf);
                        }
                    } else {
                        /* At end - clear line */
                        hist_pos = history_count;
                        while (pos > 0) { shell_putc('\b'); pos--; }
                        for (int i = 0; i < len; i++) shell_putc(' ');
                        for (int i = 0; i < len; i++) shell_putc('\b');
                        len = 0;
                        pos = 0;
                        buf[0] = '\0';
                    }
                }
                else if (c == 'C') {
                    /* Right arrow */
                    if (pos < len) {
                        shell_putc(buf[pos]);
                        pos++;
                    }
                }
                else if (c == 'D') {
                    /* Left arrow */
                    if (pos > 0) {
                        shell_putc('\b');
                        pos--;
                    }
                }
            }
        }
        else if (c >= 0x20 && c < 0x7F) {
            /* Printable character */
            if (len < maxlen - 1) {
                /* Insert at position */
                for (int i = len; i > pos; i--) {
                    buf[i] = buf[i - 1];
                }
                buf[pos] = c;
                len++;
                buf[len] = '\0';

                /* Redraw from position */
                for (int i = pos; i < len; i++) {
                    shell_putc(buf[i]);
                }
                pos++;
                /* Move cursor back if inserted */
                for (int i = pos; i < len; i++) {
                    shell_putc('\b');
                }
            }
        }
    }
}

/* ============================================================
 * Command Parsing and Execution
 * ============================================================ */

/* Parse command line into arguments */
static int parse_line(char *line, char *argv[], int max_args) {
    int argc = 0;
    int in_arg = 0;
    int in_quote = 0;

    while (*line && argc < max_args) {
        if (*line == '"') {
            in_quote = !in_quote;
            if (!in_quote && in_arg) {
                *line = '\0';
            }
        }
        else if (*line == ' ' && !in_quote) {
            if (in_arg) {
                *line = '\0';
                in_arg = 0;
            }
        }
        else if (!in_arg) {
            argv[argc++] = line;
            in_arg = 1;
        }
        line++;
    }

    return argc;
}

/* Execute a command with arguments */
int shell_exec_cmd(int argc, char *argv[]) {
    const shell_cmd_t *cmd;

    if (argc == 0) return 0;

    cmd = find_cmd(argv[0]);
    if (cmd) {
        return cmd->func(argc, argv);
    }

    /* Check for variable assignment */
    char *eq = NULL;
    for (char *p = argv[0]; *p; p++) {
        if (*p == '=') {
            eq = p;
            break;
        }
    }
    if (eq) {
        *eq = '\0';
        env_set(argv[0], eq + 1);
        return 0;
    }

    shell_printf("Unknown command: %s\n", argv[0]);
    shell_printf("Type 'help' for available commands\n");
    return -1;
}

/* Execute a command line */
int shell_exec(const char *line) {
    static char buf[SHELL_MAX_LINE];
    char *argv[SHELL_MAX_ARGS];
    int argc;

    /* Copy line to mutable buffer */
    shell_strcpy(buf, line);

    /* Parse into arguments */
    argc = parse_line(buf, argv, SHELL_MAX_ARGS);

    return shell_exec_cmd(argc, argv);
}

/* ============================================================
 * Shell Initialization and Main Loop
 * ============================================================ */

void shell_init(void) {
    history_count = 0;
    history_index = 0;
    env_init();
}

void shell_run(void) {
    static char line[SHELL_MAX_LINE];
    int ret;

    shell_printf("\n");
    shell_printf("ARM Bootloader Shell\n");
    shell_printf("Type 'help' for available commands\n");
    shell_printf("\n");

    while (1) {
        shell_puts(SHELL_PROMPT);

        ret = shell_readline(line, SHELL_MAX_LINE);
        if (ret < 0) {
            continue;  /* Ctrl+C pressed */
        }
        if (ret == 0) {
            continue;  /* Empty line */
        }

        shell_exec(line);
    }
}

/* ============================================================
 * Built-in Command Implementations
 * ============================================================ */

int cmd_help(int argc, char *argv[]) {
    const shell_cmd_t *cmd;

    if (argc > 1) {
        /* Help for specific command */
        cmd = find_cmd(argv[1]);
        if (cmd) {
            shell_printf("%s - %s\n", cmd->name, cmd->help);
            shell_printf("Usage: %s\n", cmd->usage);
            return 0;
        }
        shell_printf("Unknown command: %s\n", argv[1]);
        return -1;
    }

    /* List all commands */
    shell_printf("Available commands:\n\n");

    cmd = builtin_cmds;
    while (cmd->name) {
        shell_printf("  %-10s - %s\n", cmd->name, cmd->help);
        cmd++;
    }
    shell_printf("\n");
    shell_printf("Type 'help <cmd>' for detailed usage\n");
    return 0;
}

int cmd_info(int argc, char *argv[]) {
    const bsp_info_t *info = bsp_get_info();
    (void)argc; (void)argv;

    shell_printf("\nSystem Information:\n");
    shell_printf("  Platform:   %s\n", info->name);
    shell_printf("  Description: %s\n", info->description);
    shell_printf("  RAM Base:   0x%X\n", info->ram_base);
    shell_printf("  RAM Size:   0x%X (%u MB)\n", info->ram_size,
                 (uint32_t)(info->ram_size / (1024 * 1024)));
    shell_printf("  UART Base:  0x%X\n", info->uart_base);
    if (info->timer_base) {
        shell_printf("  Timer Base: 0x%X\n", info->timer_base);
    }
    if (info->gpio_base) {
        shell_printf("  GPIO Base:  0x%X\n", info->gpio_base);
    }
    shell_printf("\n");
    return 0;
}

int cmd_version(int argc, char *argv[]) {
    (void)argc; (void)argv;
    shell_printf("ARM Bootloader v2.0 (Unified)\n");
    shell_printf("Build: %s %s\n", __DATE__, __TIME__);
#ifdef BSP_ARCH_64BIT
    shell_printf("Architecture: AArch64\n");
#else
    shell_printf("Architecture: AArch32\n");
#endif
    return 0;
}

int cmd_reset(int argc, char *argv[]) {
    (void)argc; (void)argv;
    shell_printf("Resetting system...\n");
    bsp_timer_delay_ms(100);

    /* Platform-specific reset - for now, just loop */
    shell_printf("Reset not implemented - halting\n");
    while (1) {
#ifdef BSP_ARCH_64BIT
        __asm__ volatile ("wfe");
#else
        __asm__ volatile ("wfe");
#endif
    }
}

/* ============================================================
 * Memory Commands
 * ============================================================ */

int cmd_md(int argc, char *argv[]) {
    bsp_addr_t addr;
    uint32_t count = 64;
    int size = 4;  /* Default: 32-bit words */
    uint32_t i;
    char *cmd = argv[0];

    /* Check for size suffix */
    int len = shell_strlen(cmd);
    if (len > 2 && cmd[len-2] == '.') {
        if (cmd[len-1] == 'b') size = 1;
        else if (cmd[len-1] == 'w') size = 2;
        else if (cmd[len-1] == 'l') size = 4;
    }

    if (argc < 2) {
        shell_printf("Usage: %s\n", "md[.b/.w/.l] addr [count]");
        return -1;
    }

    addr = shell_parse_addr(argv[1]);
    if (argc > 2) {
        count = shell_parse_u32(argv[2]);
    }

    /* Display memory */
    for (i = 0; i < count; i++) {
        if ((i % (16 / size)) == 0) {
            shell_printf("%X: ", addr + i * size);
        }

        if (size == 1) {
            shell_print_hex8(*(volatile uint8_t *)(uintptr_t)(addr + i));
        } else if (size == 2) {
            shell_print_hex8((*(volatile uint16_t *)(uintptr_t)(addr + i * 2) >> 8) & 0xff);
            shell_print_hex8(*(volatile uint16_t *)(uintptr_t)(addr + i * 2) & 0xff);
        } else {
            shell_print_hex32(*(volatile uint32_t *)(uintptr_t)(addr + i * 4));
        }
        shell_putc(' ');

        if (((i + 1) % (16 / size)) == 0 || i == count - 1) {
            shell_printf("\n");
        }
    }

    return 0;
}

int cmd_mw(int argc, char *argv[]) {
    bsp_addr_t addr;
    uint32_t value;
    uint32_t count = 1;
    int size = 4;
    char *cmd = argv[0];
    uint32_t i;

    int len = shell_strlen(cmd);
    if (len > 2 && cmd[len-2] == '.') {
        if (cmd[len-1] == 'b') size = 1;
        else if (cmd[len-1] == 'w') size = 2;
        else if (cmd[len-1] == 'l') size = 4;
    }

    if (argc < 3) {
        shell_printf("Usage: %s\n", "mw[.b/.w/.l] addr value [count]");
        return -1;
    }

    addr = shell_parse_addr(argv[1]);
    value = shell_parse_u32(argv[2]);
    if (argc > 3) {
        count = shell_parse_u32(argv[3]);
    }

    for (i = 0; i < count; i++) {
        if (size == 1) {
            *(volatile uint8_t *)(uintptr_t)(addr + i) = value;
        } else if (size == 2) {
            *(volatile uint16_t *)(uintptr_t)(addr + i * 2) = value;
        } else {
            *(volatile uint32_t *)(uintptr_t)(addr + i * 4) = value;
        }
    }

    return 0;
}

int cmd_mm(int argc, char *argv[]) {
    bsp_addr_t addr;
    int size = 4;
    char *cmd = argv[0];
    char line[32];
    uint32_t val;

    int len = shell_strlen(cmd);
    if (len > 2 && cmd[len-2] == '.') {
        if (cmd[len-1] == 'b') size = 1;
        else if (cmd[len-1] == 'w') size = 2;
        else if (cmd[len-1] == 'l') size = 4;
    }

    if (argc < 2) {
        shell_printf("Usage: %s\n", "mm[.b/.w/.l] addr");
        return -1;
    }

    addr = shell_parse_addr(argv[1]);

    shell_printf("Memory modify at 0x%X (enter empty line to quit)\n", addr);

    while (1) {
        shell_printf("%X: ", addr);

        if (size == 1) {
            shell_print_hex8(*(volatile uint8_t *)(uintptr_t)addr);
        } else if (size == 2) {
            uint16_t v = *(volatile uint16_t *)(uintptr_t)addr;
            shell_print_hex8((v >> 8) & 0xff);
            shell_print_hex8(v & 0xff);
        } else {
            shell_print_hex32(*(volatile uint32_t *)(uintptr_t)addr);
        }

        shell_printf(" ? ");

        if (shell_readline(line, sizeof(line)) <= 0) {
            break;
        }

        val = shell_parse_u32(line);
        if (size == 1) {
            *(volatile uint8_t *)(uintptr_t)addr = val;
        } else if (size == 2) {
            *(volatile uint16_t *)(uintptr_t)addr = val;
        } else {
            *(volatile uint32_t *)(uintptr_t)addr = val;
        }

        addr += size;
    }

    return 0;
}

int cmd_cp(int argc, char *argv[]) {
    bsp_addr_t src, dst;
    uint32_t count;
    int size = 4;
    char *cmd = argv[0];
    uint32_t i;

    int len = shell_strlen(cmd);
    if (len > 2 && cmd[len-2] == '.') {
        if (cmd[len-1] == 'b') size = 1;
        else if (cmd[len-1] == 'w') size = 2;
        else if (cmd[len-1] == 'l') size = 4;
    }

    if (argc < 4) {
        shell_printf("Usage: %s\n", "cp[.b/.w/.l] src dst count");
        return -1;
    }

    src = shell_parse_addr(argv[1]);
    dst = shell_parse_addr(argv[2]);
    count = shell_parse_u32(argv[3]);

    for (i = 0; i < count; i++) {
        if (size == 1) {
            *(volatile uint8_t *)(uintptr_t)(dst + i) =
                *(volatile uint8_t *)(uintptr_t)(src + i);
        } else if (size == 2) {
            *(volatile uint16_t *)(uintptr_t)(dst + i * 2) =
                *(volatile uint16_t *)(uintptr_t)(src + i * 2);
        } else {
            *(volatile uint32_t *)(uintptr_t)(dst + i * 4) =
                *(volatile uint32_t *)(uintptr_t)(src + i * 4);
        }
    }

    shell_printf("Copied %u bytes\n", count * size);
    return 0;
}

int cmd_cmp(int argc, char *argv[]) {
    bsp_addr_t addr1, addr2;
    uint32_t count;
    int size = 4;
    char *cmd = argv[0];
    uint32_t i;

    int len = shell_strlen(cmd);
    if (len > 2 && cmd[len-2] == '.') {
        if (cmd[len-1] == 'b') size = 1;
        else if (cmd[len-1] == 'w') size = 2;
        else if (cmd[len-1] == 'l') size = 4;
    }

    if (argc < 4) {
        shell_printf("Usage: %s\n", "cmp[.b/.w/.l] addr1 addr2 count");
        return -1;
    }

    addr1 = shell_parse_addr(argv[1]);
    addr2 = shell_parse_addr(argv[2]);
    count = shell_parse_u32(argv[3]);

    for (i = 0; i < count; i++) {
        uint32_t v1, v2;
        if (size == 1) {
            v1 = *(volatile uint8_t *)(uintptr_t)(addr1 + i);
            v2 = *(volatile uint8_t *)(uintptr_t)(addr2 + i);
        } else if (size == 2) {
            v1 = *(volatile uint16_t *)(uintptr_t)(addr1 + i * 2);
            v2 = *(volatile uint16_t *)(uintptr_t)(addr2 + i * 2);
        } else {
            v1 = *(volatile uint32_t *)(uintptr_t)(addr1 + i * 4);
            v2 = *(volatile uint32_t *)(uintptr_t)(addr2 + i * 4);
        }

        if (v1 != v2) {
            shell_printf("Mismatch at offset 0x%x: 0x%x != 0x%x\n",
                         i * size, v1, v2);
            return 1;
        }
    }

    shell_printf("Compared %u bytes - match\n", count * size);
    return 0;
}

int cmd_mtest(int argc, char *argv[]) {
    bsp_addr_t start, end;
    uint32_t pattern = 0xAA55AA55;
    volatile uint32_t *p;
    uint32_t val;
    uint32_t errors = 0;
    const bsp_info_t *info = bsp_get_info();

    if (argc < 2) {
        /* Test a small region by default */
        start = info->ram_base + 0x100000;  /* 1MB offset */
        end = start + 0x10000;              /* 64KB */
    } else {
        start = shell_parse_addr(argv[1]);
        if (argc > 2) {
            end = shell_parse_addr(argv[2]);
        } else {
            end = start + 0x10000;
        }
    }

    if (argc > 3) {
        pattern = shell_parse_u32(argv[3]);
    }

    shell_printf("Memory test: 0x%X - 0x%X (pattern: 0x%x)\n",
                 start, end, pattern);

    /* Write pattern */
    shell_printf("Writing...\n");
    for (p = (volatile uint32_t *)(uintptr_t)start;
         (uintptr_t)p < end; p++) {
        *p = pattern;
    }

    /* Verify pattern */
    shell_printf("Verifying...\n");
    for (p = (volatile uint32_t *)(uintptr_t)start;
         (uintptr_t)p < end; p++) {
        val = *p;
        if (val != pattern) {
            shell_printf("Error at 0x%X: expected 0x%x, got 0x%x\n",
                         (bsp_addr_t)(uintptr_t)p, pattern, val);
            errors++;
            if (errors > 10) {
                shell_printf("Too many errors, stopping\n");
                return -1;
            }
        }
    }

    /* Test with inverted pattern */
    pattern = ~pattern;
    shell_printf("Testing inverted pattern: 0x%x\n", pattern);
    for (p = (volatile uint32_t *)(uintptr_t)start;
         (uintptr_t)p < end; p++) {
        *p = pattern;
    }

    for (p = (volatile uint32_t *)(uintptr_t)start;
         (uintptr_t)p < end; p++) {
        val = *p;
        if (val != pattern) {
            shell_printf("Error at 0x%X: expected 0x%x, got 0x%x\n",
                         (bsp_addr_t)(uintptr_t)p, pattern, val);
            errors++;
            if (errors > 10) {
                shell_printf("Too many errors, stopping\n");
                return -1;
            }
        }
    }

    if (errors == 0) {
        shell_printf("Memory test passed!\n");
    } else {
        shell_printf("Memory test failed with %u errors\n", errors);
    }
    return errors ? -1 : 0;
}

/* ============================================================
 * Boot Commands
 * ============================================================ */

int cmd_boot(int argc, char *argv[]) {
    (void)argc; (void)argv;
    shell_printf("Attempting to boot kernel...\n");
    boot_try_kernel();
    shell_printf("No bootable kernel found\n");
    return -1;
}

int cmd_bootm(int argc, char *argv[]) {
    bsp_addr_t kaddr = KERNEL_LOAD_ADDR;
    bsp_addr_t daddr = DTB_LOAD_ADDR;

    if (argc > 1) {
        kaddr = shell_parse_addr(argv[1]);
    }
    if (argc > 3) {
        daddr = shell_parse_addr(argv[3]);
    } else if (argc > 2) {
        daddr = shell_parse_addr(argv[2]);
    }

    shell_printf("Booting from 0x%X (DTB: 0x%X)\n", kaddr, daddr);

    if (kernel_validate(kaddr) != 0) {
        shell_printf("No valid kernel at 0x%X\n", kaddr);
        return -1;
    }

    if (daddr && dtb_validate(daddr) != 0) {
        shell_printf("No valid DTB at 0x%X\n", daddr);
        daddr = 0;
    }

    shell_printf("Jumping to kernel...\n");
    bsp_timer_delay_ms(100);
    kernel_boot(kaddr, daddr);

    return 0;  /* Never reached */
}

int cmd_go(int argc, char *argv[]) {
    bsp_addr_t addr;
    void (*fn)(void);

    if (argc < 2) {
        shell_printf("Usage: go addr\n");
        return -1;
    }

    addr = shell_parse_addr(argv[1]);
    shell_printf("Jumping to 0x%X\n", addr);
    bsp_timer_delay_ms(100);

    fn = (void (*)(void))(uintptr_t)addr;
    fn();

    return 0;  /* Never reached */
}

/* ============================================================
 * Environment Commands
 * ============================================================ */

int cmd_env(int argc, char *argv[]) {
    (void)argc; (void)argv;
    shell_printf("Environment commands:\n");
    shell_printf("  printenv [name] - Show environment variables\n");
    shell_printf("  setenv name val - Set variable\n");
    shell_printf("  setenv name     - Delete variable\n");
    shell_printf("  name=value      - Also sets variable\n");
    return 0;
}

int cmd_setenv(int argc, char *argv[]) {
    if (argc < 2) {
        shell_printf("Usage: setenv name [value]\n");
        return -1;
    }

    if (argc == 2) {
        /* Delete variable */
        env_set(argv[1], NULL);
    } else {
        /* Set variable */
        env_set(argv[1], argv[2]);
    }
    return 0;
}

int cmd_printenv(int argc, char *argv[]) {
    if (argc > 1) {
        const char *val = env_get(argv[1]);
        if (val) {
            shell_printf("%s=%s\n", argv[1], val);
        } else {
            shell_printf("Variable '%s' not set\n", argv[1]);
            return -1;
        }
    } else {
        env_print_all();
    }
    return 0;
}

int cmd_saveenv(int argc, char *argv[]) {
    (void)argc; (void)argv;
    shell_printf("saveenv not implemented (no persistent storage)\n");
    return -1;
}

/* ============================================================
 * Test Commands
 * ============================================================ */

int cmd_test(int argc, char *argv[]) {
    const bsp_info_t *info = bsp_get_info();

    if (argc > 1) {
        if (shell_strcmp(argv[1], "uart") == 0) {
            shell_printf("UART test: OK\n");
        } else if (shell_strcmp(argv[1], "timer") == 0) {
            shell_printf("Timer test:\n");
            shell_printf("  Frequency: %u Hz\n", bsp_timer_get_freq());
            shell_printf("  Current ticks: ");
            boot_print_hex(bsp_timer_get_ticks());
            shell_printf("\n");
        } else if (shell_strcmp(argv[1], "gpio") == 0) {
            shell_printf("GPIO test: toggling pin 0\n");
            bsp_gpio_set(0);
            bsp_timer_delay_ms(100);
            bsp_gpio_clear(0);
        } else if (shell_strcmp(argv[1], "mem") == 0) {
            char *args[] = {"mtest", NULL};
            cmd_mtest(1, args);
        } else if (shell_strcmp(argv[1], "all") == 0) {
            boot_run_tests(info);
        }
    } else {
        boot_run_tests(info);
    }
    return 0;
}

int cmd_timer(int argc, char *argv[]) {
    uint32_t delay = 1000;
    uint64_t start, end;

    if (argc > 1) {
        delay = shell_parse_u32(argv[1]);
    }

    shell_printf("Timer test: delaying %u ms...\n", delay);
    start = bsp_timer_get_ticks();
    bsp_timer_delay_ms(delay);
    end = bsp_timer_get_ticks();

    shell_printf("Elapsed ticks: ");
    boot_print_hex(end - start);
    shell_printf("\n");
    shell_printf("Expected: %u\n", (bsp_timer_get_freq() / 1000) * delay);
    return 0;
}

int cmd_gpio(int argc, char *argv[]) {
    uint8_t pin;
    int val;

    if (argc < 2) {
        shell_printf("Usage: gpio pin [0|1]\n");
        return -1;
    }

    pin = shell_parse_u32(argv[1]);

    if (argc > 2) {
        val = shell_parse_u32(argv[2]);
        if (val) {
            bsp_gpio_set(pin);
            shell_printf("GPIO %d set high\n", pin);
        } else {
            bsp_gpio_clear(pin);
            shell_printf("GPIO %d set low\n", pin);
        }
    } else {
        shell_printf("GPIO %d: control only, no read support\n", pin);
    }
    return 0;
}

/* ============================================================
 * ELF Commands
 * ============================================================ */

int cmd_elfinfo(int argc, char *argv[]) {
    bsp_addr_t addr;
    elf_info_t info;

    if (argc < 2) {
        shell_printf("Usage: elfinfo addr\n");
        return -1;
    }

    addr = shell_parse_addr(argv[1]);

    if (elf_get_info(addr, &info) != 0) {
        shell_printf("Not a valid ELF file at 0x%X\n", addr);
        return -1;
    }

    shell_printf("\nELF File Information:\n");
    shell_printf("  Class:      %d-bit\n", info.class);
    shell_printf("  Machine:    %s\n",
                 info.machine == 183 ? "AArch64" :
                 info.machine == 40  ? "ARM" : "Unknown");
    shell_printf("  Entry:      0x%X\n", info.entry);
    shell_printf("  Segments:   %d\n", info.phnum);
    shell_printf("  Load range: 0x%X - 0x%X\n", info.load_addr, info.load_end);
    shell_printf("  Size:       %u bytes\n", (uint32_t)(info.load_end - info.load_addr));
    shell_printf("\n");

    return 0;
}

int cmd_loadelf(int argc, char *argv[]) {
    bsp_addr_t addr;
    bsp_addr_t entry;
    void (*fn)(void);

    if (argc < 2) {
        shell_printf("Usage: loadelf addr\n");
        return -1;
    }

    addr = shell_parse_addr(argv[1]);

    shell_printf("Loading ELF from 0x%X...\n", addr);

    entry = elf_load(addr);
    if (entry == 0) {
        shell_printf("Failed to load ELF file\n");
        return -1;
    }

    shell_printf("Entry point: 0x%X\n", entry);
    shell_printf("Jumping to entry...\n");

    bsp_timer_delay_ms(100);

    fn = (void (*)(void))(uintptr_t)entry;
    fn();

    return 0;  /* Never reached */
}

/* ============================================================
 * Script Commands
 * ============================================================ */

int cmd_source(int argc, char *argv[]) {
    bsp_addr_t addr;
    uint32_t len = 0;

    if (argc < 2) {
        shell_printf("Usage: source addr [len]\n");
        return -1;
    }

    addr = shell_parse_addr(argv[1]);
    if (argc > 2) {
        len = shell_parse_u32(argv[2]);
    }

    return script_run(addr, len);
}

int cmd_run(int argc, char *argv[]) {
    int i;
    int ret = 0;

    if (argc < 2) {
        shell_printf("Usage: run var [var...]\n");
        shell_printf("Runs commands from environment variables\n");
        return -1;
    }

    /* Run each variable in sequence */
    for (i = 1; i < argc; i++) {
        ret = script_run_env(argv[i]);
        if (ret != 0) {
            shell_printf("Failed to run '%s'\n", argv[i]);
            return ret;
        }
    }

    return 0;
}

/* ============================================================
 * Network Commands
 * ============================================================ */

static int net_initialized = 0;

int cmd_net(int argc, char *argv[]) {
    if (argc > 1 && shell_strcmp(argv[1], "init") == 0) {
        if (net_init() == 0) {
            net_initialized = 1;
            shell_printf("Network initialized\n");
            return 0;
        }
        return -1;
    }

    if (!net_initialized) {
        shell_printf("Network not initialized. Run 'net init' first.\n");
        return -1;
    }

    /* Show network info */
    net_state_t *state = net_get_state();

    shell_printf("\nNetwork Status:\n");
    shell_printf("  MAC Address: ");
    net_print_mac(&state->our_mac);
    shell_printf("\n");
    shell_printf("  Link:        %s\n", state->link_up ? "UP" : "DOWN");
    shell_printf("  IP Address:  ");
    net_print_ip(&state->our_ip);
    shell_printf("\n");
    shell_printf("  Netmask:     ");
    net_print_ip(&state->netmask);
    shell_printf("\n");
    shell_printf("  Gateway:     ");
    net_print_ip(&state->gateway);
    shell_printf("\n");

    if (state->dhcp_done) {
        shell_printf("  DHCP:        Configured\n");
        shell_printf("  Server:      ");
        net_print_ip(&state->server_ip);
        shell_printf("\n");
    }

    shell_printf("\n  RX Packets:  %u\n", state->rx_packets);
    shell_printf("  TX Packets:  %u\n", state->tx_packets);
    shell_printf("\n");

    return 0;
}

int cmd_dhcp(int argc, char *argv[]) {
    (void)argc; (void)argv;

    if (!net_initialized) {
        shell_printf("Initializing network...\n");
        if (net_init() == 0) {
            net_initialized = 1;
        } else {
            return -1;
        }
    }

    return net_dhcp();
}

int cmd_ping(int argc, char *argv[]) {
    ip_addr_t ip;
    int count = 3;

    if (!net_initialized) {
        shell_printf("Network not initialized. Run 'net init' or 'dhcp' first.\n");
        return -1;
    }

    if (argc < 2) {
        shell_printf("Usage: ping ip [count]\n");
        return -1;
    }

    if (net_parse_ip(argv[1], &ip) != 0) {
        shell_printf("Invalid IP address: %s\n", argv[1]);
        return -1;
    }

    if (argc > 2) {
        count = shell_parse_u32(argv[2]);
    }

    return net_ping(&ip, count);
}

int cmd_tftp(int argc, char *argv[]) {
    bsp_addr_t addr;
    const char *filename;
    ip_addr_t server;
    size_t received = 0;
    net_state_t *state;

    if (!net_initialized) {
        shell_printf("Initializing network...\n");
        if (net_init() == 0) {
            net_initialized = 1;
        } else {
            return -1;
        }
    }

    state = net_get_state();

    /* Check if we have an IP */
    if (net_ip_equal(&state->our_ip, &IP_ZERO)) {
        shell_printf("No IP configured. Running DHCP...\n");
        if (net_dhcp() != 0) {
            return -1;
        }
    }

    if (argc < 3) {
        shell_printf("Usage: tftp addr filename [server_ip]\n");
        return -1;
    }

    addr = shell_parse_addr(argv[1]);
    filename = argv[2];

    if (argc > 3) {
        if (net_parse_ip(argv[3], &server) != 0) {
            shell_printf("Invalid server IP: %s\n", argv[3]);
            return -1;
        }
    } else {
        /* Use server from DHCP or environment */
        const char *server_ip = env_get("serverip");
        if (server_ip && net_parse_ip(server_ip, &server) == 0) {
            /* Got from environment */
        } else if (state->dhcp_done) {
            net_ip_copy(&server, &state->server_ip);
        } else {
            shell_printf("No server IP specified. Set 'serverip' or provide IP.\n");
            return -1;
        }
    }

    /* Download file */
    if (net_tftp_get(&server, filename, (uint8_t *)(uintptr_t)addr,
                     0x1000000, &received) != 0) {  /* 16MB max */
        return -1;
    }

    /* Update environment */
    char size_str[16];
    shell_snprintf(size_str, sizeof(size_str), "%u", (unsigned)received);
    env_set("filesize", size_str);

    char addr_str[20];
    shell_snprintf(addr_str, sizeof(addr_str), "0x%x", (unsigned)addr);
    env_set("fileaddr", addr_str);

    shell_printf("Loaded %u bytes to 0x%X\n", (unsigned)received, addr);

    return 0;
}
