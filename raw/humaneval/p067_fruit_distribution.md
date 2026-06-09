# P067 Fruit distribution

## Problem (HumanEval 67)

In this task, you will be given a string that represents a number of apples && oranges
that are distributed in a basket of fruit this basket contains
apples, oranges, && mango fruits. Given the string that represents the total number of
the oranges && apples && an integer that represent the total number of the fruits
in the basket return the number of the mango fruits in the basket.
for example:
p067_fruit_distribution("5 apples && 6 oranges", 19) ->19 - 5 - 6 = 8
p067_fruit_distribution("0 apples && 1 oranges",3) -> 3 - 0 - 1 = 2
p067_fruit_distribution("2 apples && 3 oranges", 100) -> 100 - 2 - 3 = 95
p067_fruit_distribution("100 apples && 1 oranges",120) -> 120 - 100 - 1 = 19

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
In this task, you will be given a string that represents a number of apples && oranges
that are distributed in a basket of fruit this basket contains
apples, oranges, && mango fruits. Given the string that represents the total number of
the oranges && apples && an integer that represent the total number of the fruits
in the basket return the number of the mango fruits in the basket.
for example:
p067_fruit_distribution("5 apples && 6 oranges", 19) ->19 - 5 - 6 = 8
p067_fruit_distribution("0 apples && 1 oranges",3) -> 3 - 0 - 1 = 2
p067_fruit_distribution("2 apples && 3 oranges", 100) -> 100 - 2 - 3 = 95
p067_fruit_distribution("100 apples && 1 oranges",120) -> 120 - 100 - 1 = 19
*/

int strlen(char *s)

;

int p067_fruit_distribution(char *s, int total)

{
    int num1 = -1;
    int num2 = -1;
    int cur = -1;
    int i;
    int slen = strlen(s);

    for (i = 0; i < slen; i++) {
        int chr = s[i];
        if (chr >= 48 && chr <= 57) {
            if (cur < 0) {
                cur = 0;
            }
            cur = cur * 10 + (chr - 48);
        } else if (cur >= 0) {
            if (num1 < 0) {
                num1 = cur;
            } else if (num2 < 0) {
                num2 = cur;
            }
            cur = -1;
        }
    }

    if (cur >= 0) {
        if (num1 < 0) {
            num1 = cur;
        } else if (num2 < 0) {
            num2 = cur;
        }
    }

    if (num1 < 0) {
        num1 = 0;
    }
    if (num2 < 0) {
        num2 = 0;
    }
    return total - num1 - num2;
}
```
