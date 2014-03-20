/* Copyright (C) Adrien Guatto <adrien.guatto@laposte.net> 2013-2014
 *
 * This file is part of Acid Synchrone.
 *
 * nsched is free software: you can redistribute it and/or modify it under the
 * terms of the GNU General Public License as published by the Free Software
 * Foundation, either version 3 of the License, or (at your option) any later
 * version.
 *
 * nsched is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE.  See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * nsched. If not, see <http://www.gnu.org/licenses/>.
 */
#ifndef NIR_H
#define NIR_H

#include <stddef.h>
#include <stdbool.h>
#include <string.h>
#include <strings.h>
#include <stdlib.h>
#include <assert.h>

static inline void *Rt_alloc(size_t size) {
    void *ret = malloc(size);
    assert(ret != NULL && "NIR RUNTIME: malloc() failed");
    return ret;
}

static inline void *Rt_free(void *p) {
    free(p);
}

struct Rt_buffer_mem {
    size_t front;               /* consumer position  */
    size_t back;                /* producer position */
    char *data;                 /* internal data */
};

static inline struct Rt_buffer_mem *Rt_buffer_create() {
    struct Rt_buffer_mem *res = Rt_alloc(sizeof(*res));
    bzero(res, sizeof(*res));   /* data should always to be set to zero */
    return res;
}

static inline void Rt_buffer_destroy(struct Rt_buffer_mem *mem) {
    Rt_free(mem->data);
    Rt_free(mem);
}

static inline void Rt_buffer_reset(struct Rt_buffer_mem *mem,
                                   size_t elem_size,
                                   size_t capacity) {
    mem->front = 0;
    mem->back = 0;
    mem->data = malloc(elem_size * capacity);
}

static inline void Rt_buffer_push(struct Rt_buffer_mem *mem,
                                  size_t elem_size,
                                  size_t capacity,
                                  size_t amount,
                                  void *data) {
    memcpy(mem->data + mem->back * elem_size,
           data,
           elem_size * amount);
    mem->back += amount;
    if (mem->back >= capacity)
        mem->back = 0;
}

static inline void Rt_buffer_pop(struct Rt_buffer_mem *mem,
                                 size_t elem_size,
                                 size_t capacity,
                                 size_t amount,
                                 void *data) {
    memcpy(data,
           mem->data + mem->front * elem_size,
           elem_size * amount);
    mem->front += amount;
    if (mem->front >= capacity)
        mem->front = 0;
}

struct Rt_pword_mem {
    unsigned int wpos;          /* position in the word */
    unsigned int dpos;          /* position in a datum */
};

static inline struct Rt_pword_mem *Rt_pword_create() {
    return Rt_alloc(sizeof(struct Rt_pword_mem));
}

static inline void Rt_pword_destroy(struct Rt_pword_mem *mem) {
    Rt_free(mem);
}

static inline void Rt_pword_reset(struct Rt_pword_mem *mem,
                                  unsigned int size_pref,
                                  unsigned int size_word,
                                  const int *word_data,
                                  const int *word_exps) {
    mem->wpos = 0;
    mem->dpos = 0;
}

static inline void Rt_pword_step(struct Rt_pword_mem *mem,
                                 unsigned int size_pref,
                                 unsigned int size_word,
                                 const int *word_data,
                                 const int *word_exps,

                          int *step) {
    *step = word_data[mem->wpos];
    mem->dpos++;
    if (mem->dpos >= word_exps[mem->wpos]) {
        mem->dpos = 0;
        mem->wpos++;
        if (mem->wpos >= size_word)
            mem->wpos = size_pref;
    }
}

static inline void Rt_builtin_copy(size_t elem_size,
                                   size_t elem_count,
                                   const void *src,
                                   void *dest) {
    memcpy(dest, src, elem_size * elem_count);
}

static inline void Rt_builtin_ceq(size_t n,
                                  int cst,
                                  const int *x,
                                  int *res)
{
    for (size_t i = 0; i < n; i++)
        res[i] = x[i] == cst;
}

static inline void Rt_builtin_on(size_t n,
                                 const int *x,
                                 int *res) {
    *res = 0;
    for (size_t i = 0; i < n; i++)
        *res += x[i];
}

static inline void Rt_builtin_add(int x, int y, int *r) {
  *r = x + y;
}

#define Rt_builtin_max(a, b) ((a) < (b) ? (a) : (b))

#endif // NIR_H
