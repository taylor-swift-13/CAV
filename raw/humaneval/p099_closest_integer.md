# P099 Closest integer

## Problem (HumanEval 99)

Create a function that takes a value (string) representing a number
&& returns the closest integer to it. If the number is equidistant
from two integers, round it away from zero.

Examples
>>> p099_closest_integer("10")
10
>>> p099_closest_integer("15.3")
15

Note:
Rounding away from zero means that if the given number is equidistant
from two integers, the one you should return is the one that is the
farthest from zero. For example p099_closest_integer("14.5") should
return 15 && p099_closest_integer("-14.5") should return -15.

## Stub Function Specifications

Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.

### `he_external_round`

Coq model: define nearest-integer rounding with ties away from zero, matching the HumanEval statement when used for closest-integer tasks.

Contract shape:

```c
int he_external_round(double x)
/*@ Require emp
    Ensure he_round_spec(x, __return)
*/;
```

### `he_external_strtod`

Coq model: define decimal-string parsing for the accepted input grammar in the task statement.

Contract shape:

```c
double he_external_strtod(const char *s)
/*@ With l n
    Require 0 <= n && n < INT_MAX &&
            Zlength(l) == n &&
            CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure CharArray::full(s, n + 1, app(l, cons(0, nil))) &&
           he_strtod_spec(l, __return)
*/;
```

## Reference Implementation

```c
int he_external_round(double x);
double he_external_strtod(const char *s);
int p099_closest_integer(const char* value){
    double w;
    w = he_external_strtod(value);
    return he_external_round(w);
}
```
