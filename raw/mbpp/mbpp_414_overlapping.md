# MBPP 414 Overlapping

## Problem

Write a python function to check whether any value in a sequence exists in a sequence or not.

## Signature

- Python: `overlapping(list1: List[int], list2: List[int]) -> bool`
- C entrypoint: `mbpp_414_overlapping`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert overlapping([1,2,3,4,5],[6,7,8,9]) == False`
- `assert overlapping([1,2,3],[4,5,6]) == False`
- `assert overlapping([1,4,5],[1,4,5]) == True`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 414.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def overlapping(list1,list2):  
    for i in range(len(list1)): 
        for j in range(len(list2)): 
            if(list1[i]==list2[j]): 
                return True
    return False
```

## Reference Implementation

```c
int mbpp_414_overlapping(int *list1, int list1_size, int *list2, int list2_size) {
    int i;
    for (i = 0; i < list1_size; i++) {
        int j;
        for (j = 0; j < list2_size; j++) {
            if ((list1[i] == list2[j])) {
                return 1;
            }
        }
    }
    return 0;
}
```
