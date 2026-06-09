# P056 Correct bracketing

## Problem (HumanEval 56)

brackets is a string of '<' && '>'.
return true if every opening bracket has a corresponding closing bracket.

>>> p056_correct_bracketing("<")
false
>>> p056_correct_bracketing("<>")
true
>>> p056_correct_bracketing("<<><>>")
true
>>> p056_correct_bracketing("><<>")
false

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
brackets is a string of '<' && '>'.
return true if every opening bracket has a corresponding closing bracket.

>>> p056_correct_bracketing("<")
false
>>> p056_correct_bracketing("<>")
true
>>> p056_correct_bracketing("<<><>>")
true
>>> p056_correct_bracketing("><<>")
false
*/

int strlen(char *s)

;

int p056_correct_bracketing(char *brackets)

{
    int level = 0;
    int n = strlen(brackets);
    int i;

    for (i = 0; i < n; i++) {
        if (brackets[i] == 60) {
            level = level + 1;
        } else if (brackets[i] == 62) {
            level = level - 1;
        }
        if (level < 0) {
            return 0;
        }
    }
    if (level != 0) {
        return 0;
    }
    return 1;
}
```
