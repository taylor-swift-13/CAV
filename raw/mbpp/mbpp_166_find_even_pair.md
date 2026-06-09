# MBPP 166 Find Even Pair

## Problem

Write a function that counts the number of pairs of integers in a list that xor to an even number.

## Signature

- Python: `find_even_pair(A: List[int]) -> int`
- C entrypoint: `mbpp_166_find_even_pair`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert find_even_pair([5, 4, 7, 2, 1]) == 4`
- `assert find_even_pair([7, 2, 8, 1, 0, 5, 11]) == 9`
- `assert find_even_pair([1, 2, 3]) == 1`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 166.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def find_even_pair(A): 
  count = 0
  for i in range(0, len(A)): 
    for j in range(i+1, len(A)): 
        if ((A[i] ^ A[j]) % 2 == 0): 
          count += 1

  return count
```

## Reference Implementation

```c
int mbpp_166_find_even_pair(int *A, int A_size) {
    int count = 0;
    int i;
    for (i = 0; i < A_size; i++) {
        int j;
        for (j = (i + 1); j < A_size; j++) {
            if ((((A[i] ^ A[j]) % 2) == 0)) {
                count += 1;
            }
        }
    }
    return count;
}
```
