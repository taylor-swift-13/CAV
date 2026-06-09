# MBPP 293 Otherside Rightangle

## Problem

Write a function to find the third side of a right angled triangle.

## Signature

- Python: `otherside_rightangle(w: int, h: int) -> float`
- C entrypoint: `mbpp_293_otherside_rightangle`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert otherside_rightangle(7,8)==10.63014581273465`
- `assert otherside_rightangle(3,4)==5`
- `assert otherside_rightangle(7,15)==16.55294535724685`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 293.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Stub Function Specifications

The C reference intentionally uses external stubs instead of libc/math.h:

- `double mbpp_external_sqrt(double x);`

Contract-stage requirements:

- Keep these as explicit C stub declarations or stub functions; do not replace them with libc calls.
- Give every stub a function contract in `mid/<dataset>/<name>.c` before verifying the caller.
- Implement the mathematical meaning in the companion `mid/<dataset>/<name>.v` with definition-only Coq definitions/relations, then expose them with `Extern Coq` / `Import Coq` annotations from the C file.
- Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for the external semantics.

### `mbpp_external_sqrt`

Coq model: define a pure relation/function for the mathematical square root required by this task. The relation must at least state that the result is nonnegative and its square equals the input in the chosen numeric model.

Function contract shape:

```c
double mbpp_external_sqrt(double x)
/*@ Require x >= 0
    Ensure mbpp_sqrt_spec(x, __return)
*/;
```

## Original Python Implementation

```python
import math
def otherside_rightangle(w,h):
  s=math.sqrt((w*w)+(h*h))
  return s
```

## Reference Implementation

```c
double mbpp_external_sqrt(double x);

double mbpp_293_otherside_rightangle(int w, int h) {
    double s = mbpp_external_sqrt(((w * w) + (h * h)));
    return s;
}
```
