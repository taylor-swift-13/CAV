# MBPP 453 Sumoffactors

## Problem

Write a python function to find the sum of even factors of a number.

## Signature

- Python: `sumofFactors(n: int) -> int`
- C entrypoint: `mbpp_453_sumofFactors`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert sumofFactors(18) == 26`
- `assert sumofFactors(30) == 48`
- `assert sumofFactors(6) == 8`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 453.
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
def sumofFactors(n) : 
    if (n % 2 != 0) : 
        return 0
    res = 1
    for i in range(2, (int)(math.sqrt(n)) + 1) :    
        count = 0
        curr_sum = 1
        curr_term = 1
        while (n % i == 0) : 
            count= count + 1
            n = n // i 
            if (i == 2 and count == 1) : 
                curr_sum = 0
            curr_term = curr_term * i 
            curr_sum = curr_sum + curr_term 
        res = res * curr_sum  
    if (n >= 2) : 
        res = res * (1 + n) 
    return res
```

## Reference Implementation

```c
int mbpp_external_isqrt(int x);

int mbpp_453_sumofFactors(int n) {
    if (((n % 2) != 0)) {
        return 0;
    }
    int res = 1;
    int i;
    for (i = 2; i < (mbpp_external_isqrt(n) + 1); i++) {
        int count = 0;
        int curr_sum = 1;
        int curr_term = 1;
        while (((n % i) == 0)) {
            count = (count + 1);
            n = (n / i);
            if (((i == 2) && (count == 1))) {
                curr_sum = 0;
            }
            curr_term = (curr_term * i);
            curr_sum = (curr_sum + curr_term);
        }
        res = (res * curr_sum);
    }
    if ((n >= 2)) {
        res = (res * (1 + n));
    }
    return res;
}
```
