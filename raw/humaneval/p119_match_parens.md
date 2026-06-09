# P119 Match parens

## Problem (HumanEval 119)

You are given a vector of two strings, both strings consist of open
parentheses '(' || close parentheses ')' only.
Your job is to check if it is possible to concatenate the two strings in
some order, that the resulting string will be good.
A string S is considered to be good if && only if all parentheses in S
are balanced. For example: the string "(())()" is good, while the string
"())" is !.
Return "Yes" if there's a way to make a good string, && return "No" otherwise.

Examples:
p119_match_parens({"()(", ")"}) == "Yes"
p119_match_parens({")", ")"}) == "No"

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
You are given a vector of two strings, both strings consist of open
parentheses '(' || close parentheses ')' only.
Your job is to check if it is possible to concatenate the two strings in
some order, that the resulting string will be good.
A string S is considered to be good if && only if all parentheses in S
are balanced. For example: the string "(())()" is good, while the string
"())" is !.
Return "Yes" if there's a way to make a good string, && return "No" otherwise.

Examples:
p119_match_parens({"()(", ")"}) == "Yes"
p119_match_parens({")", ")"}) == "No"
*/

int strlen(char *s)

;

int p119_match_parens(char *s1, char *s2)

{
    int i;
    int count = 0;
    int can = 1;
    int n1 = strlen(s1);
    int n2 = strlen(s2);

    for (i = 0; i < n1; i++) {
        if (s1[i] == 40) {
            count += 1;
        } else if (s1[i] == 41) {
            count -= 1;
        }
        if (count < 0) can = 0;
    }

    for (i = 0; i < n2; i++) {
        if (s2[i] == 40) {
            count += 1;
        } else if (s2[i] == 41) {
            count -= 1;
        }
        if (count < 0) can = 0;
    }

    if (count != 0) return 0;
    if (can == 1) return 1;

    count = 0;
    can = 1;

    for (i = 0; i < n2; i++) {
        if (s2[i] == 40) {
            count += 1;
        } else if (s2[i] == 41) {
            count -= 1;
        }
        if (count < 0) can = 0;
    }

    for (i = 0; i < n1; i++) {
        if (s1[i] == 40) {
            count += 1;
        } else if (s1[i] == 41) {
            count -= 1;
        }
        if (count < 0) can = 0;
    }

    if (can == 1) return 1;
    return 0;
}
```
