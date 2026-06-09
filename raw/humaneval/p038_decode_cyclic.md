# P038 Decode cyclic

## Problem (HumanEval 38)

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
p038_decode_cyclic takes as input a string encoded with encode_cyclic and returns
the decoded string. Only p038_decode_cyclic is verified for problem 38.
*/

char *malloc_char_array(int n)

;

int strlen(char *s)

;

char *p038_decode_cyclic(char *s)

{
    int n = strlen(s);
    char *out = malloc_char_array(n + 1);
    int full = (n / 3) * 3;
    int i;

    for (i = 0; i < n; i++) {
        if (i < full) {
            if ((i + 1) % 3 == 1) {

                out[i] = s[i + 2];
            } else {

                out[i] = s[i - 1];
            }
        } else {

            out[i] = s[i];
        }
    }
    out[n] = 0;
    return out;
}
```
