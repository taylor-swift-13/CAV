# P027 Filp case

## Problem (HumanEval 27)

For a given string, flip lowercase characters to uppercase && uppercase to lowercase.
>>> flip_case("Hello")
"hELLO"

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

## Reference Implementation

```c
/*
For a given string, flip lowercase characters to uppercase && uppercase to lowercase.
>>> flip_case("Hello")
"hELLO"
*/

char *malloc_char_array(int n)

;

int strlen(char *s)

;

char *p027_filp_case(char *str)

{
    int i;
    int n = strlen(str);
    char *out = malloc_char_array(n + 1);

    for (i = 0; i < n; i++) {
        int w = str[i];
        if (w >= 97 && w <= 122) {
            w = w - 32;
        } else if (w >= 65 && w <= 90) {
            w = w + 32;
        }
        out[i] = w;
    }
    out[n] = 0;
    return out;
}
```
