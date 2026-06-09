# P132 Is nested

## Problem (HumanEval 132)

Create a function that takes a string as input which contains only square brackets.
The function should return true if && only if there is a valid subsequence of brackets
where at least one bracket in the subsequence is nested.

p132_is_nested("[[]]") ➞ true
p132_is_nested("[]]]]]]][[[[[]") ➞ false
p132_is_nested("[][]") ➞ false
p132_is_nested("[]") ➞ false
p132_is_nested("[[][]]") ➞ true
p132_is_nested("[[]][[") ➞ true

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
Create a function that takes a string as input which contains only square brackets.
The function should return true if && only if there is a valid subsequence of brackets
where at least one bracket in the subsequence is nested.

p132_is_nested("[[]]") -> true
p132_is_nested("[]]]]]]][[[[[]") -> false
p132_is_nested("[][]") -> false
p132_is_nested("[]") -> false
p132_is_nested("[[][]]") -> true
p132_is_nested("[[]][[") -> true
*/

int strlen(char *s)

;

int p132_is_nested(char *str)

{
    int state = 0;
    int i;
    int n = strlen(str);

    for (i = 0; i < n; i++) {
        int chr = str[i];
        if (state == 0) {
            if (chr == 91) {
                state = 1;
            }
        } else if (state == 1) {
            if (chr == 91) {
                state = 2;
            }
        } else if (state == 2) {
            if (chr == 93) {
                state = 3;
            }
        } else if (state == 3) {
            if (chr == 93) {
                state = 4;
            }
        }
    }
    if (state == 4) {
        return 1;
    }
    return 0;
}
```
