# MBPP 127 Multiply Int

## Problem

Write a function to multiply two integers.

## Signature

- Python: `multiply_int(x: int, y: int) -> int`
- C entrypoint: `mbpp_127_multiply_int`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert multiply_int(10,20)==200`
- `assert multiply_int(5,10)==50`
- `assert multiply_int(4,8)==32`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 127.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def multiply_int(x, y):
    if y < 0:
        return -multiply_int(x, -y)
    elif y == 0:
        return 0
    elif y == 1:
        return x
    else:
        return x + multiply_int(x, y - 1)
```

## Reference Implementation

```c
int mbpp_127_multiply_int(int x, int y) {
    if ((y < 0)) {
        return (-mbpp_127_multiply_int(x, (-y)));
    } else {
        if ((y == 0)) {
            return 0;
        } else {
            if ((y == 1)) {
                return x;
            } else {
                return (x + mbpp_127_multiply_int(x, (y - 1)));
            }
        }
    }
}
```
