# P050 Decode shift

## Problem (HumanEval 50)

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
char *malloc_char_array(int n)

;

int strlen(char *s)

;

char *encode_shift(char *s)

{
    int i;
    int n = strlen(s);
    char *out = malloc_char_array(n + 1);

    for (i = 0; i < n; i++) {
        int w = (s[i] + 5 - 97) % 26 + 97;
        out[i] = w;
    }
    out[n] = 0;
    return out;
}

char *p050_decode_shift(char *s)

{
    int i;
    int n = strlen(s);
    char *out = malloc_char_array(n + 1);

    for (i = 0; i < n; i++) {
        int w = (s[i] + 21 - 97) % 26 + 97;
        out[i] = w;
    }
    out[n] = 0;
    return out;
}
```
