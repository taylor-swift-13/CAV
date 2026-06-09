# MBPP 742 Area Tetrahedron

## Problem

Write a function to caluclate the area of a tetrahedron.

## Signature

- Python: `area_tetrahedron(side: int) -> float`
- C entrypoint: `mbpp_742_area_tetrahedron`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert area_tetrahedron(3)==15.588457268119894`
- `assert area_tetrahedron(20)==692.8203230275509`
- `assert area_tetrahedron(10)==173.20508075688772`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 742.
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
def area_tetrahedron(side):
  area = math.sqrt(3)*(side*side)
  return area
```

## Reference Implementation

```c
double mbpp_external_sqrt(double x);

double mbpp_742_area_tetrahedron(int side) {
    double area = (mbpp_external_sqrt(3) * (side * side));
    return area;
}
```
