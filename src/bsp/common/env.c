/*
 * ARM Bootloader - Environment Variable Implementation
 * U-Boot compatible environment variable storage
 */

#include "env.h"
#include "shell.h"

/* ============================================================
 * Environment Storage
 * ============================================================ */

typedef struct {
    char name[ENV_NAME_SIZE];
    char value[ENV_VALUE_SIZE];
    int  used;
} env_entry_t;

static env_entry_t env_table[ENV_MAX_ENTRIES];
static int env_initialized = 0;

/* ============================================================
 * String Helpers (avoid dependency on shell.c)
 * ============================================================ */

static int env_strcmp(const char *s1, const char *s2) {
    while (*s1 && *s2) {
        if (*s1 != *s2) return *s1 - *s2;
        s1++; s2++;
    }
    return *s1 - *s2;
}

static int env_strlen(const char *s) {
    int len = 0;
    while (*s++) len++;
    return len;
}

static void env_strcpy(char *dst, const char *src, int maxlen) {
    int i;
    for (i = 0; i < maxlen - 1 && *src; i++) {
        *dst++ = *src++;
    }
    *dst = '\0';
}

/* ============================================================
 * Environment Functions
 * ============================================================ */

void env_init(void) {
    int i;

    if (env_initialized) return;

    /* Clear all entries */
    for (i = 0; i < ENV_MAX_ENTRIES; i++) {
        env_table[i].used = 0;
        env_table[i].name[0] = '\0';
        env_table[i].value[0] = '\0';
    }

    /* Set default environment */
    env_set("bootdelay", "3");
    env_set("baudrate", "115200");
    env_set("stdin", "serial");
    env_set("stdout", "serial");
    env_set("stderr", "serial");

    /* Platform-specific defaults are set based on defines */
#ifdef KERNEL_LOAD_ADDR
    {
        char buf[20];
        bsp_addr_t addr = KERNEL_LOAD_ADDR;
        /* Convert to hex string */
        static const char hex[] = "0123456789abcdef";
        int i, pos = 0;
        buf[pos++] = '0';
        buf[pos++] = 'x';
#ifdef BSP_ARCH_64BIT
        for (i = 60; i >= 0; i -= 4) {
            char c = hex[(addr >> i) & 0xf];
            if (c != '0' || pos > 2 || i == 0) {
                buf[pos++] = c;
            }
        }
#else
        for (i = 28; i >= 0; i -= 4) {
            char c = hex[(addr >> i) & 0xf];
            if (c != '0' || pos > 2 || i == 0) {
                buf[pos++] = c;
            }
        }
#endif
        buf[pos] = '\0';
        env_set("kernel_addr", buf);
    }
#endif

    env_set("bootcmd", "boot");
    env_set("bootargs", "console=ttyAMA0 earlycon");

    env_initialized = 1;
}

const char *env_get(const char *name) {
    int i;

    if (!name) return NULL;

    for (i = 0; i < ENV_MAX_ENTRIES; i++) {
        if (env_table[i].used && env_strcmp(env_table[i].name, name) == 0) {
            return env_table[i].value;
        }
    }
    return NULL;
}

int env_set(const char *name, const char *value) {
    int i;
    int free_slot = -1;

    if (!name || env_strlen(name) == 0) return -1;

    /* Look for existing entry or free slot */
    for (i = 0; i < ENV_MAX_ENTRIES; i++) {
        if (env_table[i].used) {
            if (env_strcmp(env_table[i].name, name) == 0) {
                /* Found existing - update or delete */
                if (value) {
                    env_strcpy(env_table[i].value, value, ENV_VALUE_SIZE);
                } else {
                    env_table[i].used = 0;
                    env_table[i].name[0] = '\0';
                    env_table[i].value[0] = '\0';
                }
                return 0;
            }
        } else if (free_slot < 0) {
            free_slot = i;
        }
    }

    /* Not found - add new entry if value provided */
    if (!value) return 0;  /* Delete non-existent = success */

    if (free_slot < 0) {
        /* No free slots */
        return -1;
    }

    env_strcpy(env_table[free_slot].name, name, ENV_NAME_SIZE);
    env_strcpy(env_table[free_slot].value, value, ENV_VALUE_SIZE);
    env_table[free_slot].used = 1;
    return 0;
}

int env_delete(const char *name) {
    return env_set(name, NULL);
}

void env_print_all(void) {
    int i;
    int count = 0;

    for (i = 0; i < ENV_MAX_ENTRIES; i++) {
        if (env_table[i].used) {
            shell_printf("%s=%s\n", env_table[i].name, env_table[i].value);
            count++;
        }
    }

    if (count == 0) {
        shell_printf("No environment variables set\n");
    } else {
        shell_printf("\n%d variables defined\n", count);
    }
}

int env_count(void) {
    int i;
    int count = 0;

    for (i = 0; i < ENV_MAX_ENTRIES; i++) {
        if (env_table[i].used) count++;
    }
    return count;
}
