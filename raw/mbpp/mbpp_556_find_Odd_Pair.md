# MBPP 556 Find Odd Pair

## Problem

Write a python function to count the number of pairs whose xor value is odd.

## Signature

- Python: `find_Odd_Pair(A: List[int], N: int) -> int`
- C entrypoint: `mbpp_556_find_Odd_Pair`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert find_Odd_Pair([5,4,7,2,1],5) == 6`
- `assert find_Odd_Pair([7,2,8,1,0,5,11],7) == 12`
- `assert find_Odd_Pair([1,2,3],3) == 2`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 556.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def find_Odd_Pair(A,N) : 
    oddPair = 0
    for i in range(0,N) :  
        for j in range(i+1,N) :  
            if ((A[i] ^ A[j]) % 2 != 0):  
                oddPair+=1  
    return oddPair
```

## Reference Implementation

```c
int mbpp_556_find_Odd_Pair(int *A, int A_size, int N) {
    int oddPair = 0;
    int i;
    for (i = 0; i < N; i++) {
        int j;
        for (j = (i + 1); j < N; j++) {
            if ((((A[i] ^ A[j]) % 2) != 0)) {
                oddPair += 1;
            }
        }
    }
    return oddPair;
}
```
