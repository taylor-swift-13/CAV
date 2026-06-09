# MBPP 564 Count Pairs

## Problem

Write a python function which takes a list of integers and counts the number of possible unordered pairs where both elements are unequal.

## Signature

- Python: `count_Pairs(arr: List[int], n: int) -> int`
- C entrypoint: `mbpp_564_count_Pairs`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert count_Pairs([1,2,1],3) == 2`
- `assert count_Pairs([1,1,1,1],4) == 0`
- `assert count_Pairs([1,2,3,4,5],5) == 10`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 564.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def count_Pairs(arr,n): 
    cnt = 0; 
    for i in range(n): 
        for j in range(i + 1,n): 
            if (arr[i] != arr[j]): 
                cnt += 1; 
    return cnt;
```

## Reference Implementation

```c
int mbpp_564_count_Pairs(int *arr, int arr_size, int n) {
    int cnt = 0;
    int i;
    for (i = 0; i < n; i++) {
        int j;
        for (j = (i + 1); j < n; j++) {
            if ((arr[i] != arr[j])) {
                cnt += 1;
            }
        }
    }
    return cnt;
}
```
