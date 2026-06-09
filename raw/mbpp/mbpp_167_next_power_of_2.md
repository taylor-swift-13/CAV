# MBPP 167 Next Power Of 2

## Problem

Write a python function to find the smallest power of 2 greater than or equal to n.

## Signature

- Python: `next_power_of_2(n: int) -> int`
- C entrypoint: `mbpp_167_next_power_of_2`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert next_power_of_2(0) == 1`
- `assert next_power_of_2(5) == 8`
- `assert next_power_of_2(17) == 32`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 167.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def next_power_of_2(n): 
  if n and not n & (n - 1):
    return n

  count = 0
  while n != 0: 
    n >>= 1
    count += 1

  return 1 << count;
```

## Reference Implementation

```c
int mbpp_167_next_power_of_2(int n) {
    if ((n && (!(n & (n - 1))))) {
        return n;
    }
    int count = 0;
    while ((n != 0)) {
        n >>= 1;
        count += 1;
    }
    return (1 << count);
}
```
