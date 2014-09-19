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
               (char *)data + initial_amount * elem_size,
               (amount - initial_amount) * elem_size);
    }

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
        memcpy((char *)data + initial_amount * elem_size,
               mem->data,
               (amount - initial_amount) * elem_size);
    }

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
                                 int n,
                                 int *step) {
    for (int i = 0; i < n; i++) {
        step[i] = word_data[mem->wpos];
        mem->dpos++;
        if (mem->dpos >= word_exps[mem->wpos]) {
            mem->dpos = 0;
            mem->wpos++;
            if (mem->wpos >= size_word)
                mem->wpos = size_pref;
        }
    }
}

/******************************************************************************/
/* Boxes                                                                      */
/******************************************************************************/

struct Rt_box {
    size_t size;
    char *mem;
    int live;
    struct Rt_box *next;
};

static struct Rt_box *global_box = NULL;

static inline struct Rt_box *Rt_box_alloc(size_t size, const char *p) {
    struct Rt_box *r;
    r = Rt_alloc(sizeof(*r));

    r->size = size;
    memcpy(r->mem, p, size);
    r->mem = Rt_alloc(size);
    r->live = 0;
    r->next = global_box;

    global_box = r;
    return r;
}

static inline void Rt_box_destroy(struct Rt_box *box) {
    Rt_free(box->mem);
    Rt_free(box);
}

static inline struct Rt_box *Rt_box_copy(const struct Rt_box *b) {
    struct Rt_box *c = Rt_box_alloc(b->size, b->mem);
    return c;
}

static inline void Rt_box_collect() {
    struct Rt_box *old, **b = &global_box;

    while (*b != NULL) {
        if ((*b)->live)
            b = &(*b)->next;
        else {
            old = *b;
            *b = (*b)->next;
            Rt_box_destroy(old);
        }
    }
}

static inline void Rt_box_register(struct Rt_box *box) {
    box->live = 1;
}

static inline void Rt_box_unregister(struct Rt_box *box) {
    box->live = 0;
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

static inline void Rt_builtin_const(size_t n,
                                    int c,
                                    int *res) {
    for (size_t i = 0; i < n; i++)
        res[i] = c;
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

static inline void Rt_builtin_eq_int(int n, int *x, int *y, int *r) {
    for (int i = 0; i < n; i++) {
        r[i] = x[i] == y[i];
    }
}

static inline void Rt_builtin_eq_float(int n, float *x, float *y, int *r) {
    for (int i = 0; i < n; i++) {
        r[i] = x[i] == y[i];
    }
}

static inline void Rt_builtin_and(int x, int y, int *r) {
    *r = x && y;
}

static inline void Rt_builtin_or(int x, int y, int *r) {
    *r = x || y;
}

static inline void Rt_builtin_xor(int x, int y, int *r) {
    *r = x ^ y;
}

/******************************************************************************/
/* Reflection stuff                                                           */
/******************************************************************************/

/* Tags */

enum NIR_TYPE_TAG {
    NIR_TYPE_TAG_BOOL = 0,
    NIR_TYPE_TAG_INT,
    NIR_TYPE_TAG_FLOAT,
    NIR_TYPE_TAG_BOX,
    NIR_TYPE_TAG_ARRAY
};

/* Types */

struct NIR_TYPE {
    enum NIR_TYPE_TAG nir_tag;
    struct {
        size_t size;
        struct NIR_TYPE **types;
    } nir_arr;
};

static inline struct NIR_TYPE *Rt_type_create() {
    struct NIR_TYPE *t = Rt_alloc(sizeof(*t));
    bzero(t, sizeof(*t));
    return t;
}

static inline void Rt_type_destroy(struct NIR_TYPE *t) {
    switch (t->nir_tag) {
    case NIR_TYPE_TAG_BOOL:
    case NIR_TYPE_TAG_INT:
    case NIR_TYPE_TAG_FLOAT:
    case NIR_TYPE_TAG_BOX: // TODO
        break;
    case NIR_TYPE_TAG_ARRAY:
        for (size_t i = 0; i < t->nir_arr.size; i++)
            Rt_type_destroy(t->nir_arr.types[i]);
        Rt_free(t->nir_arr.types);
        break;
    }
    Rt_free(t);
}

static inline struct NIR_TYPE *Rt_type_bool() {
    struct NIR_TYPE *t = Rt_type_create();
    t->nir_tag = NIR_TYPE_TAG_BOOL;
    return t;
}

static inline struct NIR_TYPE *Rt_type_int() {
    struct NIR_TYPE *t = Rt_type_create();
    t->nir_tag = NIR_TYPE_TAG_INT;
    return t;
}

static inline struct NIR_TYPE *Rt_type_float() {
    struct NIR_TYPE *t = Rt_type_create();
    t->nir_tag = NIR_TYPE_TAG_FLOAT;
    return t;
}

static inline struct NIR_TYPE *Rt_type_box() {
    struct NIR_TYPE *t = Rt_type_create();
    t->nir_tag = NIR_TYPE_TAG_BOX;
    return t;
}

static inline struct NIR_TYPE *Rt_type_array(size_t n, struct NIR_TYPE **a) {
    struct NIR_TYPE *t = Rt_type_create();
    t->nir_tag = NIR_TYPE_TAG_ARRAY;
    t->nir_arr.types = a;
    return t;
}

static inline struct NIR_TYPE *Rt_type_copy(const struct NIR_TYPE *t) {
    switch (t->nir_tag) {
    case NIR_TYPE_TAG_BOOL:
        return Rt_type_bool();
    case NIR_TYPE_TAG_INT:
        return Rt_type_int();
    case NIR_TYPE_TAG_FLOAT:
        return Rt_type_float();
    case NIR_TYPE_TAG_BOX:
        return Rt_type_box();
    case NIR_TYPE_TAG_ARRAY:;
        struct NIR_TYPE **types = Rt_alloc(sizeof(*types) * t->nir_arr.size);
        for (size_t i = 0; i < t->nir_arr.size; i++)
            types[i] = Rt_type_copy(t->nir_arr.types[i]);
        return Rt_type_array(t->nir_arr.size, types);
    }
}

/* Values */

struct NIR_VALUE {
    enum NIR_TYPE_TAG nir_tag;
    union {
        int nir_bool;
        int nir_int;
        float nir_float;
        struct Rt_box *nir_box;
        struct {
            size_t size;
            struct NIR_VALUE **values;
        } nir_arr;
    } nir_val;
};

static inline struct NIR_VALUE *Rt_value_create() {
    struct NIR_VALUE *v = Rt_alloc(sizeof(*v));
    bzero(v, sizeof(*v));
    return v;
}

static inline void Rt_value_destroy(struct NIR_VALUE *v) {
    switch (v->nir_tag) {
    case NIR_TYPE_TAG_BOOL:
    case NIR_TYPE_TAG_INT:
    case NIR_TYPE_TAG_FLOAT:
    case NIR_TYPE_TAG_BOX: // TODO
        break;
    case NIR_TYPE_TAG_ARRAY:
        for (size_t i = 0; i < v->nir_val.nir_arr.size; i++)
            Rt_value_destroy(v->nir_val.nir_arr.values[i]);
        Rt_free(v->nir_val.nir_arr.values);
        break;
    }
    Rt_free(v);
}

static inline struct NIR_VALUE *Rt_value_bool(int b) {
    struct NIR_VALUE *v = Rt_value_create();
    v->nir_tag = NIR_TYPE_TAG_BOOL;
    v->nir_val.nir_bool = b;
    return v;
}

static inline struct NIR_VALUE *Rt_value_int(int i) {
    struct NIR_VALUE *v = Rt_value_create();
    v->nir_tag = NIR_TYPE_TAG_INT;
    v->nir_val.nir_int = i;
    return v;
}

static inline struct NIR_VALUE *Rt_value_float(float f) {
    struct NIR_VALUE *v = Rt_value_create();
    v->nir_tag = NIR_TYPE_TAG_FLOAT;
    v->nir_val.nir_float = f;
    return v;
}

static inline struct NIR_VALUE *Rt_value_box(struct Rt_box *b) {
    struct NIR_VALUE *v = Rt_value_create();
    v->nir_tag = NIR_TYPE_TAG_BOX;
    v->nir_val.nir_box = b;
    return v;
}

static inline struct NIR_VALUE *Rt_value_array(size_t n, struct NIR_VALUE **a) {
    struct NIR_VALUE *v = Rt_value_create();
    v->nir_tag = NIR_TYPE_TAG_ARRAY;
    v->nir_val.nir_arr.size = n;
    v->nir_val.nir_arr.values = a;
    return v;
}

static inline struct NIR_VALUE *Rt_value_copy(const struct NIR_VALUE *v) {
    switch(v->nir_tag) {
    case NIR_TYPE_TAG_BOOL:
        return Rt_value_bool(v->nir_val.nir_bool);
    case NIR_TYPE_TAG_INT:
        return Rt_value_int(v->nir_val.nir_int);
    case NIR_TYPE_TAG_FLOAT:
        return Rt_value_float(v->nir_val.nir_float);
    case NIR_TYPE_TAG_BOX: {
        struct Rt_box *b = Rt_box_copy(v->nir_val.nir_box);
        return Rt_value_box(b);
    }
    case NIR_TYPE_TAG_ARRAY:;
        struct NIR_VALUE **values =
            Rt_alloc(sizeof(*values) * v->nir_val.nir_arr.size);
        for (size_t i = 0; i < v->nir_val.nir_arr.size; i++)
            values[i] = Rt_value_copy(v->nir_val.nir_arr.values[i]);
        return Rt_value_array(v->nir_val.nir_arr.size, values);
    }
}

#endif // NIR_H
