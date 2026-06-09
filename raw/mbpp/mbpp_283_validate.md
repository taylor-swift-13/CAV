# MBPP 283 Validate

## Problem

Write a python function takes in an integer and check whether the frequency of each digit in the integer is less than or equal to the digit itself.

## Signature

- Python: `validate(n: int) -> bool`
- C entrypoint: `mbpp_283_validate`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert validate(1234) == True`
- `assert validate(51241) == False`
- `assert validate(321) == True`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 283.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def validate(n): 
    for i in range(10): 
        temp = n;  
        count = 0; 
        while (temp): 
            if (temp % 10 == i): 
                count+=1;  
            if (count > i): 
                return False
            temp //= 10; 
    return True
```

## Reference Implementation

```c
int mbpp_283_validate(int n) {
    int i;
    for (i = 0; i < 10; i++) {
        int temp = n;
        int count = 0;
        while (temp) {
            if (((temp % 10) == i)) {
                count += 1;
            }
            if ((count > i)) {
                return 0;
            }
            temp /= 10;
        }
    }
    return 1;
}
```
