# P016 Count distinct characters

## Problem (HumanEval 16)

Given a string, find out how many distinct characters (regardless of case) does it consist of
>>> p016_count_distinct_characters("xyzXYZ")
3
>>> p016_count_distinct_characters("Jerry")
4

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
Given a string, find out how many distinct characters (regardless of case) does it consist of
>>> p016_count_distinct_characters("xyzXYZ")
3
>>> p016_count_distinct_characters("Jerry")
4
*/

int strlen(char *s)

;

int p016_count_distinct_characters(char *str)

{
    int n = strlen(str);
    int count = 0;
    int i;

    for (i = 0; i < n; i++) {
        int c = str[i];
        int seen = 0;
        int j;

        if (c >= 65 && c <= 90) {
            c = c + 32;
        }

        for (j = 0; j < i; j++) {
            int d = str[j];
            if (d >= 65 && d <= 90) {
                d = d + 32;
            }
            if (d == c) {
                seen = 1;
            }
        }

        if (seen == 0) {
            count = count + 1;
        }
    }
    return count;
}
```
