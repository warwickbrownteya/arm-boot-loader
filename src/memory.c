/* Minimal Memory Management for Bootloader */

#include <stdint.h>
#include <stddef.h>
#include "memory.h"

// Linker-defined heap boundaries (from linker.ld)
extern uint8_t __heap_start;
extern uint8_t __heap_end;

typedef struct mem_block {
    size_t size;
    uint8_t free;
    struct mem_block *next;
} mem_block_t;

static mem_block_t *heap_base = NULL;
static int heap_initialized = 0;

void memory_init(void) {
    // Use linker-defined heap region
    heap_base = (mem_block_t*)&__heap_start;
    size_t heap_size = (size_t)(&__heap_end - &__heap_start);

    // Initialize the first block
    heap_base->size = heap_size - sizeof(mem_block_t);
    heap_base->free = 1;
    heap_base->next = NULL;
    heap_initialized = 1;
}

void* malloc(size_t size) {
    if (!heap_initialized || !heap_base || size == 0) return NULL;

    // Align to 8-byte boundary
    size = (size + 7) & ~7;

    mem_block_t *current = heap_base;

    while (current) {
        if (current->free && current->size >= size) {
            // Split block if large enough
            if (current->size > size + sizeof(mem_block_t) + 8) {
                mem_block_t *new_block = (mem_block_t*)((uint8_t*)current + sizeof(mem_block_t) + size);
                new_block->size = current->size - size - sizeof(mem_block_t);
                new_block->free = 1;
                new_block->next = current->next;

                current->size = size;
                current->next = new_block;
            }

            current->free = 0;
            return (void*)((uint8_t*)current + sizeof(mem_block_t));
        }
        current = current->next;
    }

    return NULL;
}

void free(void *ptr) {
    if (!ptr || !heap_base) return;

    mem_block_t *block = (mem_block_t*)((uint8_t*)ptr - sizeof(mem_block_t));
    block->free = 1;

    // Coalesce with next block if free
    if (block->next && block->next->free) {
        block->size += sizeof(mem_block_t) + block->next->size;
        block->next = block->next->next;
    }
}
