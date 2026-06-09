# MBPP 781 Count Divisors

## Problem

Write a python function to check whether the count of divisors is even. https://www.w3resource.com/python-exercises/basic/python-basic-1-exercise-24.php

## Signature

- Python: `count_divisors(n: int) -> bool`
- C entrypoint: `mbpp_781_count_divisors`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert count_divisors(10)`
- `assert not count_divisors(100)`
- `assert count_divisors(125)`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 781.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Stub Function Specifications

The C reference intentionally uses external stubs instead of libc/math.h:

- `int mbpp_external_isqrt(int x);`

Contract-stage requirements:

- Keep these as explicit C stub declarations or stub functions; do not replace them with libc calls.
- Give every stub a function contract in `mid/<dataset>/<name>.c` before verifying the caller.
- Implement the mathematical meaning in the companion `mid/<dataset>/<name>.v` with definition-only Coq definitions/relations, then expose them with `Extern Coq` / `Import Coq` annotations from the C file.
- Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for the external semantics.

### `mbpp_external_isqrt`

Coq model:

```coq
Definition mbpp_isqrt_spec (x r : Z) : Prop :=
  0 <= x /\ 0 <= r /\ r * r <= x /\ x < (r + 1) * (r + 1).
```

Function contract shape:

```c
int mbpp_external_isqrt(int x)
/*@ Require 0 <= x && x < INT_MAX
    Ensure mbpp_isqrt_spec(x, __return)
*/;
```

## Original Python Implementation

```python
import math 
def count_divisors(n) : 
    count = 0
    for i in range(1, (int)(math.sqrt(n)) + 2) : 
        if (n % i == 0) : 
            if( n // i == i) : 
                count = count + 1
            else : 
                count = count + 2
    return count % 2 == 0
```

## Reference Implementation

```c
int mbpp_external_isqrt(int x);

int mbpp_781_count_divisors(int n) {
    int count = 0;
    int i;
    for (i = 1; i < (mbpp_external_isqrt(n) + 2); i++) {
        if (((n % i) == 0)) {
            if (((n / i) == i)) {
                count = (count + 1);
            } else {
                count = (count + 2);
            }
        }
    }
    return ((count % 2) == 0);
}
```
