#ifndef RUNTIME_H
#define RUNTIME_H

#include <stdint.h>

void initialize(uint64_t rootstack_size, uint64_t heap_size);
void collect(int64_t **rootstack_ptr, uint64_t bytes_requested);
int64_t *free_ptr;
int64_t *fromspace_begin;
int64_t *fromspace_end;
int64_t **rootstack_begin;
int64_t **rootstack_end;

#endif