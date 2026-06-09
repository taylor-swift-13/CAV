# MBPP 3 Is Not Prime

## Problem

Write a python function to identify non-prime numbers.

## Signature

- Python: `is_not_prime(n: int) -> bool`
- C entrypoint: `mbpp_3_is_not_prime`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert is_not_prime(2) == False`
- `assert is_not_prime(10) == True`
- `assert is_not_prime(35) == True`
- `assert is_not_prime(37) == False`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 3.
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
def is_not_prime(n):
    result = False
    for i in range(2,int(math.sqrt(n)) + 1):
        if n % i == 0:
            result = True
    return result
```

## Reference Implementation

```c
int mbpp_external_isqrt(int x);

int mbpp_3_is_not_prime(int n) {
    int result = 0;
    int i;
    for (i = 2; i < (mbpp_external_isqrt(n) + 1); i++) {
        if (((n % i) == 0)) {
            result = 1;
        }
    }
    return result;
}
```
