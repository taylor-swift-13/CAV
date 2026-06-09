# P066 DigitSum

## Problem (HumanEval 66)

Task
Write a function that takes a string as input && returns the sum of the upper characters only's
ASCII codes.

Examples:
    p066_digitSum("") => 0
    p066_digitSum("abAB") => 131
    p066_digitSum("abcCd") => 67
    p066_digitSum("helloE") => 69
    p066_digitSum("woArBld") => 131
    p066_digitSum("aAaaaXa") => 153

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
Task
Write a function that takes a string as input && returns the sum of the upper characters only's
ASCII codes.

Examples:
    p066_digitSum("") => 0
    p066_digitSum("abAB") => 131
    p066_digitSum("abcCd") => 67
    p066_digitSum("helloE") => 69
    p066_digitSum("woArBld") => 131
    p066_digitSum("aAaaaXa") => 153
*/

int strlen(char *s)

;

int p066_digitSum(char *s)

{
    int sum = 0;
    int n = strlen(s);
    int i;

    for (i = 0; i < n; i++) {
        if (s[i] >= 65 && s[i] <= 90) {
            sum = sum + s[i];
        }
    }
    return sum;
}
```
