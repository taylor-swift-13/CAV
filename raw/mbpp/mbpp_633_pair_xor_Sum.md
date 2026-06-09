# MBPP 633 Pair Xor Sum

## Problem

Write a python function to find the sum of xor of all pairs of numbers in the given list.

## Signature

- Python: `pair_xor_Sum(arr: List[int], n: int) -> int`
- C entrypoint: `mbpp_633_pair_xor_Sum`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert pair_xor_Sum([5,9,7,6],4) == 47`
- `assert pair_xor_Sum([7,3,5],3) == 12`
- `assert pair_xor_Sum([7,3],2) == 4`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 633.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def pair_xor_Sum(arr,n) : 
    ans = 0 
    for i in range(0,n) :    
        for j in range(i + 1,n) :   
            ans = ans + (arr[i] ^ arr[j])          
    return ans
```

## Reference Implementation

```c
int mbpp_633_pair_xor_Sum(int *arr, int arr_size, int n) {
    int ans = 0;
    int i;
    for (i = 0; i < n; i++) {
        int j;
        for (j = (i + 1); j < n; j++) {
            ans = (ans + (arr[i] ^ arr[j]));
        }
    }
    return ans;
}
```
