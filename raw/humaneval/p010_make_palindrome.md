# P010 Make palindrome

## Problem (HumanEval 10)

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
Find the shortest palindrome that begins with a supplied string.
Algorithm idea is simple:
- Find the longest postfix of supplied string that is a palindrome.
- Append to the end of the string reverse of a string prefix that comes before the palindromic suffix.
>>> p010_make_palindrome("")
""
>>> p010_make_palindrome("cat")
"catac"
>>> p010_make_palindrome("cata")
"catac"
*/

int strlen(char *s)

;

char *malloc_char_array(int n)

;

int is_pal_suffix(char *s, int start, int n)

{
    int i = start;
    int j = n - 1;

    if (start == n) {
        return 1;
    }

    while (i < j) {
        if (s[i] != s[j]) {
            return 0;
        }
        i = i + 1;
        j = j - 1;
    }
    return 1;
}

char *p010_make_palindrome(char *str)

{
    int n = strlen(str);
    int best = n;
    int i;

    for (i = 0; i < n; i++) {
        if (best == n) {
            int ok = is_pal_suffix(str, i, n);
            if (ok == 1) {
                best = i;
            }
        }
    }

    if (best == n) {
        best = 0;
    }

    int out_len = n + best;
    char *out = malloc_char_array(out_len + 1);

    for (i = 0; i < n; i++) {
        out[i] = str[i];
    }

    int k;

    for (k = 0; k < best; k++) {
        out[n + k] = str[best - 1 - k];
    }

    out[out_len] = 0;

    return out;
}
```
