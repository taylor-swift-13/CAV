# P154 Cycpattern check

## Problem (HumanEval 154)

You are given 2 words. You need to return true if the second word || any of its rotations is a substring in the first word
p154_cycpattern_check("abcd","abd") => false
p154_cycpattern_check("hello","ell") => true
p154_cycpattern_check("whassup","psus") => false
p154_cycpattern_check("abab","baa") => true
p154_cycpattern_check("efef","eeff") => false
p154_cycpattern_check("himenss",'simen") => true

## Stub Function Specifications

Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.

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
You are given 2 words. You need to return true if the second word or any of its rotations is a substring in the first word
p154_cycpattern_check("abcd","abd") => false
p154_cycpattern_check("hello","ell") => true
p154_cycpattern_check("whassup","psus") => false
p154_cycpattern_check("abab","baa") => true
p154_cycpattern_check("efef","eeff") => false
p154_cycpattern_check("himenss","simen") => true

*/

int strlen(char *s)

;

int rotation_match_at(char *a, char *b, int pos, int shift, int n, int m)

{
    int ok = 1;
    int j;

    for (j = 0; j < m; j++) {
        int idx = shift + j;
        if (idx >= m) {
            idx = idx - m;
        }

        if (a[pos + j] != b[idx]) {
            ok = 0;
        }
    }
    return ok;
}

int rotation_occurs_at_shift(char *a, char *b, int shift, int n, int m)

{
    int found = 0;
    int pos;

    for (pos = 0; pos <= n - m; pos++) {
        int ok = rotation_match_at(a, b, pos, shift, n, m);
        if (ok == 1) {
            found = 1;
        }
    }
    return found;
}

int p154_cycpattern_check(char *a, char *b)

{
    int n0 = strlen(a);
    int m0 = strlen(b);

    if (m0 == 0) {
        return 1;
    }
    if (m0 > n0) {
        return 0;
    }

    int found = 0;
    int shift;

    for (shift = 0; shift < m0; shift++) {
        int ok = rotation_occurs_at_shift(a, b, shift, n0, m0);
        if (ok == 1) {
            found = 1;
        }
    }
    return found;
}
```
