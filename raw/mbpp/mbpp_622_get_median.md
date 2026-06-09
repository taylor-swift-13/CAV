# MBPP 622 Get Median

## Problem

Write a function to find the median of two sorted lists of same size.

## Signature

- Python: `get_median(arr1: List[int], arr2: List[int], n: int) -> float`
- C entrypoint: `mbpp_622_get_median`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert get_median([1, 12, 15, 26, 38], [2, 13, 17, 30, 45], 5) == 16.0`
- `assert get_median([2, 4, 8, 9], [7, 13, 19, 28], 4) == 8.5`
- `assert get_median([3, 6, 14, 23, 36, 42], [2, 18, 27, 39, 49, 55], 6) == 25.0`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 622.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def get_median(arr1, arr2, n):
  i = 0
  j = 0
  m1 = -1
  m2 = -1
  count = 0
  while count < n + 1:
    count += 1
    if i == n:
      m1 = m2
      m2 = arr2[0]
      break
    elif j == n:
      m1 = m2
      m2 = arr1[0]
      break
    if arr1[i] <= arr2[j]:
      m1 = m2
      m2 = arr1[i]
      i += 1
    else:
      m1 = m2
      m2 = arr2[j]
      j += 1
  return (m1 + m2)/2
```

## Reference Implementation

```c
double mbpp_622_get_median(int *arr1, int arr1_size, int *arr2, int arr2_size, int n) {
    int i = 0;
    int j = 0;
    int m1 = (-1);
    int m2 = (-1);
    int count = 0;
    while ((count < (n + 1))) {
        count += 1;
        if ((i == n)) {
            m1 = m2;
            m2 = arr2[0];
            break;
        } else {
            if ((j == n)) {
                m1 = m2;
                m2 = arr1[0];
                break;
            }
        }
        if ((arr1[i] <= arr2[j])) {
            m1 = m2;
            m2 = arr1[i];
            i += 1;
        } else {
            m1 = m2;
            m2 = arr2[j];
            j += 1;
        }
    }
    return ((m1 + m2) / 2);
}
```
