# P098 Count upper

## Problem (HumanEval 98)

Given a string s, count the number of uppercase vowels in even indices.

For example:
p098_count_upper("aBCdEf") returns 1
p098_count_upper("abcdefg") returns 0
p098_count_upper("dBBE") returns 0

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
Given a string s, count the number of uppercase vowels in even indices.

For example:
p098_count_upper("aBCdEf") returns 1
p098_count_upper("abcdefg") returns 0
p098_count_upper("dBBE") returns 0
*/

int strlen(char *s)

;

int p098_count_upper(char *s)

{
    int n = strlen(s);
    int count = 0;
    int i;

    for (i = 0; i < n; i++) {
        if (i % 2 == 0) {
            if (s[i] == 65 || s[i] == 69 || s[i] == 73 ||
                s[i] == 79 || s[i] == 85) {
                count = count + 1;
            }
        }
    }
    return count;
}
```
