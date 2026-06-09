# MBPP 244 Next Perfect Square

## Problem

Write a python function to find the next perfect square greater than a given number.

## Signature

- Python: `next_Perfect_Square(N: int) -> int`
- C entrypoint: `mbpp_244_next_Perfect_Square`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert next_Perfect_Square(35) == 36`
- `assert next_Perfect_Square(6) == 9`
- `assert next_Perfect_Square(9) == 16`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 244.
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
def next_Perfect_Square(N): 
    nextN = math.floor(math.sqrt(N)) + 1
    return nextN * nextN
```

## Reference Implementation

```c
int mbpp_external_isqrt(int x);

int mbpp_244_next_Perfect_Square(int N) {
    int nextN = (mbpp_external_isqrt(N) + 1);
    return (nextN * nextN);
}
```
