# P011 String xor

## Problem (HumanEval 11)

Input are two strings a && b consisting only of 1s && 0s.
Perform binary XOR on these inputs && return result also as a string.
>>> p011_string_xor("010", "110")
"100"

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

char *p011_string_xor(char *a, char *b)

{
    int i;
    int n1 = strlen(a);
    int n2 = strlen(b);
    int n;
    if (n1 < n2) {
        n = n1;
    } else {
        n = n2;
    }



    char *output = malloc_char_array(n + 1);

    for (i = 0; i < n; i++) {
        if (a[i] == b[i]) {
            output[i] = 48;
        } else {
            output[i] = 49;
        }
    }
    output[n] = 0;
    return output;
}
```
