# MBPP 808 Check K

## Problem

Write a function to check if the given tuples contain the k or not.

## Signature

- Python: `check_K(test_tup: List[int], K: int) -> bool`
- C entrypoint: `mbpp_808_check_K`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert check_K((10, 4, 5, 6, 8), 6) == True`
- `assert check_K((1, 2, 3, 4, 5, 6), 7) == False`
- `assert check_K((7, 8, 9, 44, 11, 12), 11) == True`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 808.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def check_K(test_tup, K):
  res = False
  for ele in test_tup:
    if ele == K:
      res = True
      break
  return res
```

## Reference Implementation

```c
int mbpp_808_check_K(int *test_tup, int test_tup_size, int K) {
    int res = 0;
    int ele;
    for (int __mbpp_i0 = 0; __mbpp_i0 < test_tup_size; __mbpp_i0++) {
        ele = test_tup[__mbpp_i0];
        if ((ele == K)) {
            res = 1;
            break;
        }
    }
    return res;
}
```
