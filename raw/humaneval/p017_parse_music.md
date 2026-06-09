# P017 Parse music

## Problem (HumanEval 17)

Input to this function is a string representing musical notes in a special ASCII format.
Your task is to parse this string && return vector of integers corresponding to how many beats does each
! last.

Here is a legend:
"o" - whole note, lasts four beats
"o|" - half note, lasts two beats
".|" - quater note, lasts one beat

>>> p017_parse_music("o o| .| o| o| .| .| .| .| o o")
{4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4}

## Stub Function Specifications

Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.

### `malloc_int_array_struct`

Allocates a fresh `IntArray` header object.

Contract shape:

```c
IntArray *malloc_int_array_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> data)) *
           undef_data_at(&(__return -> size))
*/;
```

### `malloc_int_array`

Allocates a fresh writable integer array with unspecified contents.

Contract shape:

```c
int *malloc_int_array(int size)
/*@ Require size >= 0 && size < INT_MAX
    Ensure __return != 0 && IntArray::undef_full(__return, size)
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

## Reference Implementation

```c
/*
Input to this function is a string representing musical notes in a special ASCII format.
Your task is to parse this string && return vector of integers corresponding to how many beats does each
! last.

Here is a legend:
"o" - whole note, lasts four beats
"o|" - half note, lasts two beats
".|" - quater note, lasts one beat

>>> p017_parse_music("o o| .| o| o| .| .| .| .| o o")
{4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4}
*/

typedef struct {
    int *data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

int strlen(char *s)

;

IntArray *p017_parse_music(char *music_string)

{
    IntArray *out = malloc_int_array_struct();
    int n = strlen(music_string);
    out->size = 0;
    out->data = malloc_int_array(n + 1);
    int *data = out->data;
    int state = 0;
    int i;

    for (i = 0; i < n; i++) {
        if (music_string[i] == 32) {
            if (state == 1) {
                data[out->size] = 4;
                out->size = out->size + 1;
            } else if (state == 2) {
                data[out->size] = 2;
                out->size = out->size + 1;
            } else if (state == 4) {
                data[out->size] = 1;
                out->size = out->size + 1;
            }
            state = 0;
        } else {
            if (state == 0 && music_string[i] == 111) {
                state = 1;
            } else if (state == 0 && music_string[i] == 46) {
                state = 3;
            } else if (state == 1 && music_string[i] == 124) {
                state = 2;
            } else if (state == 3 && music_string[i] == 124) {
                state = 4;
            } else {
                state = 5;
            }
        }

    }

    if (state == 1) {
        data[out->size] = 4;
        out->size = out->size + 1;
    } else if (state == 2) {
        data[out->size] = 2;
        out->size = out->size + 1;
    } else if (state == 4) {
        data[out->size] = 1;
        out->size = out->size + 1;
    }

    return out;
}
```
