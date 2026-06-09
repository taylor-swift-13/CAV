# P140 Fix spaces

## Problem (HumanEval 140)

Given a string text, replace all spaces in it with underscores,
&& if a string has more than 2 consecutive spaces,
then replace all consecutive spaces with -

p140_fix_spaces("Example") == "Example"
p140_fix_spaces("Example 1") == "Example_1"
p140_fix_spaces(" Example 2") == "_Example_2"
p140_fix_spaces(" Example   3") == "_Example-3"

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
Given a string text, replace all spaces in it with underscores,
&& if a string has more than 2 consecutive spaces,
then replace all consecutive spaces with -

p140_fix_spaces("Example") == "Example"
p140_fix_spaces("Example 1") == "Example_1"
p140_fix_spaces(" Example 2") == "_Example_2"
p140_fix_spaces(" Example   3") == "_Example-3"
*/

char *malloc_char_array(int n)

;

int strlen(char *s)

;

char *p140_fix_spaces(char *text)

{
    int n = strlen(text);
    char *out = malloc_char_array(n + 1);
    int k = 0;
    int spacelen = 0;
    int i;

    for (i = 0; i < n; i++) {
        int c = text[i];
        if (c == 32) {
            spacelen = spacelen + 1;
        } else {
            if (spacelen == 1) {
                out[k] = 95;
                k = k + 1;
            } else if (spacelen == 2) {
                out[k] = 95;
                k = k + 1;
                out[k] = 95;
                k = k + 1;
            } else if (spacelen > 2) {
                out[k] = 45;
                k = k + 1;
            }
            spacelen = 0;
            out[k] = c;
            k = k + 1;
        }
    }

    if (spacelen == 1) {
        out[k] = 95;
        k = k + 1;
    } else if (spacelen == 2) {
        out[k] = 95;
        k = k + 1;
        out[k] = 95;
        k = k + 1;
    } else if (spacelen > 2) {
        out[k] = 45;
        k = k + 1;
    }

    out[k] = 0;
    return out;
}
```
