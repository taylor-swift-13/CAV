# P080 Is happy

## Problem (HumanEval 80)

You are given a string s.
Your task is to check if the string is happy || !.
A string is happy if its length is at least 3 && every 3 consecutive letters are distinct
For example:
p080_is_happy("a") => false
p080_is_happy("aa") => false
p080_is_happy("abcd") => true
p080_is_happy("aabb") => false
p080_is_happy("adb") => true
p080_is_happy("xyy") => false

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
You are given a string s.
Your task is to check if the string is happy || !.
A string is happy if its length is at least 3 && every 3 consecutive letters are distinct
For example:
p080_is_happy("a") => false
p080_is_happy("aa") => false
p080_is_happy("abcd") => true
p080_is_happy("aabb") => false
p080_is_happy("adb") => true
p080_is_happy("xyy") => false
*/

int strlen(char *s)

;

int p080_is_happy(char *s)

{
    int n = strlen(s);
    int i;
    if (n < 3) {
        return 0;
    }
    if (s[0] == s[1]) {
        return 0;
    }

    for (i = 2; i < n; i++) {
        if (s[i] == s[i - 1]) {
            return 0;
        }
        if (s[i] == s[i - 2]) {
            return 0;
        }
    }
    return 1;
}
```
