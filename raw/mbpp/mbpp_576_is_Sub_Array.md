# MBPP 576 Is Sub Array

## Problem

Write a python function to check whether a list is sublist of another or not.

## Signature

- Python: `is_Sub_Array(A: List[int], B: List[int]) -> bool`
- C entrypoint: `mbpp_576_is_Sub_Array`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert is_Sub_Array([1,4,3,5],[1,2]) == False`
- `assert is_Sub_Array([1,2,1],[1,2,1]) == True`
- `assert is_Sub_Array([1,0,2,2],[2,2,0]) ==False`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 576.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def is_Sub_Array(A,B): 
    n = len(A)
    m = len(B)
    i = 0; j = 0; 
    while (i < n and j < m):  
        if (A[i] == B[j]): 
            i += 1; 
            j += 1; 
            if (j == m): 
                return True;  
        else: 
            i = i - j + 1; 
            j = 0;       
    return False;
```

## Reference Implementation

```c
int mbpp_576_is_Sub_Array(int *A, int A_size, int *B, int B_size) {
    int n = A_size;
    int m = B_size;
    int i = 0;
    int j = 0;
    while (((i < n) && (j < m))) {
        if ((A[i] == B[j])) {
            i += 1;
            j += 1;
            if ((j == m)) {
                return 1;
            }
        } else {
            i = ((i - j) + 1);
            j = 0;
        }
    }
    return 0;
}
```
