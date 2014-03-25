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

/******************************************************************************/
/* Memory management functions                                                */
/******************************************************************************/

static inline void *Rt_alloc(size_t size) {
    void *ret = malloc(size);
    assert(ret != NULL && "NIR RUNTIME: malloc() failed");
    return ret;
}

static inline void Rt_free(void *p) {
    free(p);
}

static inline void Rt_builtin_copy(size_t elem_size,
                                   size_t elem_count,
                                   const void *src,
                                   void *dest) {
    memcpy(dest, src, elem_size * elem_count);
}

/******************************************************************************/
/* Language primitives: buffers and ultimately periodic words                 */
/******************************************************************************/

struct Rt_buffer_mem {
    size_t front;               /* producer position  */
    size_t back;                /* consumer position */
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
    if (mem->data == NULL)
        mem->data = malloc(elem_size * capacity);
}

static inline void Rt_buffer_push(struct Rt_buffer_mem *mem,
                                  size_t elem_size,
                                  size_t capacity,
                                  size_t amount,
                                  void *data) {
    assert(amount <= capacity);

    if (amount == 0)
        return;

    if (mem->front + amount <= capacity) {
        memcpy(mem->data + mem->front * elem_size,
               data,
               amount * elem_size);
    } else {
        size_t initial_amount = capacity - mem->front;
        memcpy(mem->data + mem->front * elem_size,
               data,
               initial_amount * elem_size);
        memcpy(mem->data,
               data + initial_amount * elem_size,
               (amount - initial_amount) * elem_size);
    }

    /* for (int i = 0; i < amount; i++) */
    /*     mem->data[(mem->back + i) % capacity] = data[i]; */

    mem->front = (mem->front + amount) % capacity;
}

static inline void Rt_buffer_pop(struct Rt_buffer_mem *mem,
                                 size_t elem_size,
                                 size_t capacity,
                                 size_t amount,
                                 void *data) {
    assert(amount <= capacity);

    if (amount == 0)
        return;

    if (mem->back + amount <= capacity) {
        memcpy(data,
               mem->data + mem->back * elem_size,
               amount * elem_size);
    } else {
        size_t initial_amount = capacity - mem->back;
        memcpy(data,
               mem->data + mem->back * elem_size,
               initial_amount * elem_size);
        memcpy(data + initial_amount * elem_size,
               mem->data,
               (amount - initial_amount) * elem_size);
    }

    /* for (int i = 0; i < amount; i++) */
    /*     data[i] = mem->data[(mem->front + i) % capacity]; */

    mem->back = (mem->back + amount) % capacity;
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

/******************************************************************************/
/* Language operators                                                         */
/******************************************************************************/

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

/******************************************************************************/
/* Functions from the standard library                                        */
/******************************************************************************/

#define Rt_builtin_max(a, b) ((a) < (b) ? (a) : (b))

static inline void Rt_builtin_add(int x, int y, int *r) {
  *r = x + y;
}

static inline void Rt_builtin_sub(int x, int y, int *r) {
  *r = x - y;
}

static inline void Rt_builtin_mult(int x, int y, int *r) {
  *r = x * y;
}

static inline void Rt_builtin_div(int x, int y, int *r) {
  *r = x / y;
}

static inline void Rt_builtin_fadd(float x, float y, float *r) {
  *r = x + y;
}

static inline void Rt_builtin_fsub(float x, float y, float *r) {
  *r = x - y;
}

static inline void Rt_builtin_fmult(float x, float y, float *r) {
  *r = x * y;
}

static inline void Rt_builtin_fdiv(float x, float y, float *r) {
  *r = x / y;
}

#define Rt_builtin_eq(a, b, res) (*(res) = (a) == (b))

/******************************************************************************/
/* Reflection stuff                                                           */
/******************************************************************************/

enum NIR_TYPE {
    NIR_TYPE_BOOL = 0,
    NIR_TYPE_INT,
    NIR_TYPE_FLOAT,
    NIR_TYPE_ARRAY
};

struct NIR_VALUE {
    enum NIR_TYPE nir_type;
    union {
        int nir_bool;
        int nir_int;
        float nir_float;
        struct NIR_VALUE *nir_array;
    } nir_val;
};

#endif // NIR_H
