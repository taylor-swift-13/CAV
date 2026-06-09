# P018 How many times

## Problem (HumanEval 18)

Find how many times a given substring can be found in the original string. Count overlaping cases.
>>> p018_how_many_times("", "a")
0
>>> p018_how_many_times("aaa", "a")
3
>>> p018_how_many_times("aaaa", "aa")
3

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
Find how many times a given substring can be found in the original string. Count overlaping cases.
>>> p018_how_many_times("", "a")
0
>>> p018_how_many_times("aaa", "a")
3
>>> p018_how_many_times("aaaa", "aa")
3
*/

int strlen(char *s)

;

int p018_how_many_times(char *str, char *substring)

{
    int out = 0;
    int i = 0;
    int j = 0;
    int ok = 0;
    int n0 = strlen(str);
    int m0 = strlen(substring);

    if (n0 == 0) {
        return 0;
    }
    if (m0 == 0) {
        return 0;
    }
    if (m0 > n0) {
        return 0;
    }

    for (i = 0; i <= n0 - m0; i++) {
        ok = 1;

        for (j = 0; j < m0; j++) {
            if (str[i + j] != substring[j]) {
                ok = 0;
            }
        }

        if (ok == 1) {
            out += 1;
        }
    }
    return out;
}
```
