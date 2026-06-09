# MBPP 164 Are Equivalent

## Problem

Write a function to determine if the sum of the divisors of two integers are the same.

## Signature

- Python: `are_equivalent(num1: int, num2: int) -> bool`
- C entrypoint: `mbpp_164_are_equivalent`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert are_equivalent(36, 57) == False`
- `assert are_equivalent(2, 4) == False`
- `assert are_equivalent(23, 47) == True`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 164.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Stub Function Specifications

The C reference intentionally uses external stubs instead of libc/math.h:

- `int mbpp_external_floor(double x);`

Contract-stage requirements:

- Keep these as explicit C stub declarations or stub functions; do not replace them with libc calls.
- Give every stub a function contract in `mid/<dataset>/<name>.c` before verifying the caller.
- Implement the mathematical meaning in the companion `mid/<dataset>/<name>.v` with definition-only Coq definitions/relations, then expose them with `Extern Coq` / `Import Coq` annotations from the C file.
- Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for the external semantics.

### Rounding stubs

Coq model: define the corresponding integer rounding relation for every rounding stub used here. For floor, the returned integer `r` should satisfy `r <= x < r + 1` in the chosen numeric model; define analogous relations for ceil/round if they appear.

Function contract shape:

```c
int mbpp_external_floor(double x)
/*@ Require emp
    Ensure mbpp_floor_spec(x, __return)
*/;
```

## Original Python Implementation

```python
import math 
def div_sum(n): 
  total = 1
  i = 2

  while i * i <= n:
    if (n % i == 0):
      total = (total + i + math.floor(n / i))
    i += 1

  return total

def are_equivalent(num1, num2): 
    return div_sum(num1) == div_sum(num2);
```

## Reference Implementation

```c
int mbpp_external_floor(double x);

int div_sum(int n) {
    int total = 1;
    int i = 2;
    while (((i * i) <= n)) {
        if (((n % i) == 0)) {
            total = ((total + i) + mbpp_external_floor((n / i)));
        }
        i += 1;
    }
    return total;
}

int mbpp_164_are_equivalent(int num1, int num2) {
    return (div_sum(num1) == div_sum(num2));
}
```
