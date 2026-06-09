# P086 Anti shuffle

## Problem (HumanEval 86)

Write a function that takes a string && returns an ordered version of it.
Ordered version of string, is a string where all words (separated by space)
are replaced by a new word where all the characters arranged in
ascending order based on ascii value.
Note: You should keep the order of words && blank spaces in the sentence.

For example:
p086_anti_shuffle("Hi") returns "Hi"
p086_anti_shuffle("hello") returns "ehllo"
p086_anti_shuffle("Hello World!!!") returns "Hello !!!Wdlor"

## Stub Function Specifications

Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.

### `malloc_char_array`

Allocates a fresh writable character array with unspecified contents.

Contract shape:

```c
char *malloc_char_array(int n)
/*@ Require n > 0 && n < INT_MAX
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/;
```

### `strlen`

Coq model: represent strings as a list `l : list Z` of nonzero byte values followed by a zero terminator in memory.

Contract shape:

```c
int strlen(char *s)
/*@ With l n
    Require 0 <= n && n < INT_MAX &&
            Zlength(l) == n &&
            (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
            CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/;
```

### `free_char_array`

Consumes ownership of a previously allocated character array.

Contract shape:

```c
void free_char_array(char *p, int init_size, int size)
/*@ With l
    Require size >= 0 && init_size >= size && Zlength(l) == size &&
            CharArray::full(p, size, l)
    Ensure emp
*/;
```

### `sort_char_array`

Coq model: define a relation stating that the output character list is sorted and is a permutation of the input character list.

Contract shape:

```c
void sort_char_array(char *p, int n)
/*@ With l
    Require 0 <= n && Zlength(l) == n &&
            CharArray::full(p, n, l)
    Ensure exists out_l,
           sort_char_array_spec(l, out_l) &&
           CharArray::full(p, n, out_l)
*/;
```

### `copy_char_array`

Coq model: define a relation describing the destination list after copying `len` bytes from `src` into `dst + off`, preserving all other destination positions.

Contract shape:

```c
void copy_char_array(char *dst, int off, char *src, int len, int cap)
/*@ With dst_l src_l
    Require 0 <= off && 0 <= len && off + len <= cap &&
            Zlength(dst_l) == cap && Zlength(src_l) == len &&
            CharArray::full(dst, cap, dst_l) *
            CharArray::full(src, len, src_l)
    Ensure exists out_l,
           copy_char_array_spec(dst_l, src_l, off, out_l) &&
           CharArray::full(dst, cap, out_l) *
           CharArray::full(src, len, src_l)
*/;
```

## Reference Implementation

```c
/*
Write a function that takes a string && returns an ordered version of it.
Ordered version of string, is a string where all words (separated by space)
are replaced by a new word where all the characters arranged in
ascending order based on ascii value.
Note: You should keep the order of words && blank spaces in the sentence.

For example:
p086_anti_shuffle("Hi") returns "Hi"
p086_anti_shuffle("hello") returns "ehllo"
p086_anti_shuffle("Hello World!!!") returns "Hello !!!Wdlor"
*/

int strlen(char *s)

;

char *malloc_char_array(int n)

;

void free_char_array(char *p, int init_size, int size)

;

void sort_char_array(char *p, int n)

;

void copy_char_array(char *dst, int off, char *src, int len, int cap)

;

char* p086_anti_shuffle(char *s)

{
    int n = strlen(s);
    int cap = n + 1;
    char *out = malloc_char_array(cap);
    char *cur = malloc_char_array(cap);
    int out_len = 0;
    int cur_len = 0;
    int i;

    for (i = 0; i < n; i++) {
        if (s[i] != 32) {
            cur[cur_len] = s[i];
            cur_len = cur_len + 1;
        } else {
            sort_char_array(cur, cur_len);
            copy_char_array(out, out_len, cur, cur_len, cap);
            out_len = out_len + cur_len;
            cur_len = 0;
            out[out_len] = 32;
            out_len = out_len + 1;
        }
    }

    sort_char_array(cur, cur_len);
    copy_char_array(out, out_len, cur, cur_len, cap);
    out_len = out_len + cur_len;
    free_char_array(cur, cur_len, cap);
    cur_len = 0;

    out[out_len] = 0;

    return out;
}
```
