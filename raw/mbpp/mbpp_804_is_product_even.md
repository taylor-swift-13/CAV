# MBPP 804 Is Product Even

## Problem

Write a function to check whether the product of numbers in a list is even or not.

## Signature

- Python: `is_product_even(arr: List[int]) -> bool`
- C entrypoint: `mbpp_804_is_product_even`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert is_product_even([1,2,3])`
- `assert is_product_even([1,2,1,4])`
- `assert not is_product_even([1,1])`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 804.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def is_product_even(arr): 
    for i in range(len(arr)): 
        if (arr[i] & 1) == 0: 
            return True
    return False
```

## Reference Implementation

```c
int mbpp_804_is_product_even(int *arr, int arr_size) {
    int i;
    for (i = 0; i < arr_size; i++) {
        if (((arr[i] & 1) == 0)) {
            return 1;
        }
    }
    return 0;
}
```
