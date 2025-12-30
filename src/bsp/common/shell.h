/*
 * ARM Bootloader - Command Shell Interface
 * U-Boot compatible command line interface
 */

#ifndef SHELL_H
#define SHELL_H

#include "bsp.h"

/* ============================================================
 * Shell Configuration
 * ============================================================ */

#define SHELL_MAX_LINE      256     /* Maximum command line length */
#define SHELL_MAX_ARGS      16      /* Maximum command arguments */
#define SHELL_HISTORY_SIZE  8       /* Command history entries */
#define SHELL_PROMPT        "=> "   /* Command prompt */

/* ============================================================
 * Command Structure
 * ============================================================ */

/* Command handler function type */
typedef int (*cmd_func_t)(int argc, char *argv[]);

/* Command descriptor */
typedef struct {
    const char  *name;          /* Command name */
    cmd_func_t   func;          /* Handler function */
    const char  *usage;         /* Usage string */
    const char  *help;          /* Short help string */
} shell_cmd_t;

/* ============================================================
 * Shell Functions
 * ============================================================ */

/* Initialize the shell */
void shell_init(void);

/* Run the shell main loop */
void shell_run(void) __attribute__((noreturn));

/* Execute a single command line */
int shell_exec(const char *line);

/* Execute a command with arguments */
int shell_exec_cmd(int argc, char *argv[]);

/* Register a command (for extensibility) */
int shell_register_cmd(const shell_cmd_t *cmd);

/* Print formatted output (printf-like, but simpler) */
void shell_printf(const char *fmt, ...);

/* Format to buffer (snprintf-like) */
int shell_snprintf(char *buf, int size, const char *fmt, ...);

/* ============================================================
 * Line Editing Support
 * ============================================================ */

/* Read a line with editing support */
int shell_readline(char *buf, int maxlen);

/* ============================================================
 * Utility Functions
 * ============================================================ */

/* Parse a number from string (hex or decimal) */
bsp_addr_t shell_parse_addr(const char *str);

/* Parse a 32-bit number */
uint32_t shell_parse_u32(const char *str);

/* Check if string starts with prefix */
int shell_strncmp(const char *s1, const char *s2, int n);

/* String length */
int shell_strlen(const char *s);

/* String copy */
char *shell_strcpy(char *dst, const char *src);

/* Memory copy */
void *shell_memcpy(void *dst, const void *src, int n);

/* Memory set */
void *shell_memset(void *dst, int c, int n);

/* ============================================================
 * Built-in Commands
 * ============================================================ */

/* Core commands */
int cmd_help(int argc, char *argv[]);
int cmd_info(int argc, char *argv[]);
int cmd_reset(int argc, char *argv[]);
int cmd_version(int argc, char *argv[]);

/* Memory commands */
int cmd_md(int argc, char *argv[]);      /* Memory display */
int cmd_mw(int argc, char *argv[]);      /* Memory write */
int cmd_mm(int argc, char *argv[]);      /* Memory modify (interactive) */
int cmd_cp(int argc, char *argv[]);      /* Copy memory */
int cmd_cmp(int argc, char *argv[]);     /* Compare memory */
int cmd_mtest(int argc, char *argv[]);   /* Memory test */

/* Boot commands */
int cmd_boot(int argc, char *argv[]);    /* Boot default kernel */
int cmd_bootm(int argc, char *argv[]);   /* Boot memory (U-Boot compatible) */
int cmd_go(int argc, char *argv[]);      /* Jump to address */

/* Environment commands */
int cmd_env(int argc, char *argv[]);     /* Environment variables */
int cmd_setenv(int argc, char *argv[]);  /* Set environment variable */
int cmd_printenv(int argc, char *argv[]);/* Print environment */
int cmd_saveenv(int argc, char *argv[]); /* Save environment */

/* Testing commands */
int cmd_test(int argc, char *argv[]);    /* Run hardware tests */
int cmd_timer(int argc, char *argv[]);   /* Timer test */
int cmd_gpio(int argc, char *argv[]);    /* GPIO control */

/* ELF commands */
int cmd_elfinfo(int argc, char *argv[]); /* Display ELF info */
int cmd_loadelf(int argc, char *argv[]); /* Load ELF file */

/* Script commands */
int cmd_source(int argc, char *argv[]);  /* Run script from memory */
int cmd_run(int argc, char *argv[]);     /* Run env variable as command */

/* Network commands */
int cmd_net(int argc, char *argv[]);     /* Network status/config */
int cmd_dhcp(int argc, char *argv[]);    /* DHCP client */
int cmd_ping(int argc, char *argv[]);    /* Ping host */
int cmd_tftp(int argc, char *argv[]);    /* TFTP download */

/* Storage commands (declared in storage.h, referenced here) */
int cmd_mmc(int argc, char *argv[]);     /* MMC device control */
int cmd_mmcinfo(int argc, char *argv[]); /* MMC device info */
int cmd_fatload(int argc, char *argv[]); /* Load file from FAT */
int cmd_fatls(int argc, char *argv[]);   /* List FAT directory */
int cmd_fatinfo(int argc, char *argv[]); /* FAT filesystem info */
int cmd_fatsize(int argc, char *argv[]); /* Get file size */
int cmd_load(int argc, char *argv[]);    /* Generic load command */

#endif /* SHELL_H */
