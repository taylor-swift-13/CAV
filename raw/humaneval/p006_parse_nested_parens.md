# P006 Parse nested parens

## Problem (HumanEval 6)

Input to this function is a string represented multiple groups for nested parentheses separated by spaces.
For each of the group, output the deepest level of nesting of parentheses.
E.g. (()()) has maximum two levels of nesting while ((())) has three.

>>> p006_parse_nested_parens("(()()) ((())) () ((())()())")
{2, 3, 1, 3}

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
Input to this function is a string represented multiple groups for nested parentheses separated by spaces.
For each of the group, output the deepest level of nesting of parentheses.
E.g. (()()) has maximum two levels of nesting while ((())) has three.

>>> p006_parse_nested_parens("(()()) ((())) () ((())()())")
{2, 3, 1, 3}
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

IntArray *p006_parse_nested_parens(char *paren_string)

{
    IntArray *out = malloc_int_array_struct();
    int n = strlen(paren_string);
    out->size = 0;
    out->data = malloc_int_array(n);
    int *data = out->data;
    int level = 0;
    int max_level = 0;
    int in_group = 0;
    int i;

    for (i = 0; i < n; i++) {
        if (paren_string[i] == 32) {
            if (in_group) {
                data[out->size] = max_level;
                out->size = out->size + 1;
                level = 0;
                max_level = 0;
                in_group = 0;
            }
        } else {
            in_group = 1;
            if (paren_string[i] == 40) {
                level = level + 1;
                if (level > max_level) {
                    max_level = level;
                }
            } else {
                if (level > 0) {
                    level = level - 1;
                }
            }
        }

    }

    if (in_group) {
        data[out->size] = max_level;
        out->size = out->size + 1;
    }

    return out;
}
```
