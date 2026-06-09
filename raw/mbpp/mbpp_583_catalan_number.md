# MBPP 583 Catalan Number

## Problem

Write a function which returns nth catalan number.

## Signature

- Python: `catalan_number(num: int) -> int`
- C entrypoint: `mbpp_583_catalan_number`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert catalan_number(10)==16796`
- `assert catalan_number(9)==4862`
- `assert catalan_number(7)==429`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 583.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def catalan_number(num):
    if num <=1:
         return 1   
    res_num = 0
    for i in range(num):
        res_num += catalan_number(i) * catalan_number(num-i-1)
    return res_num
```

## Reference Implementation

```c
int mbpp_583_catalan_number(int num) {
    if ((num <= 1)) {
        return 1;
    }
    int res_num = 0;
    int i;
    for (i = 0; i < num; i++) {
        res_num += (mbpp_583_catalan_number(i) * mbpp_583_catalan_number(((num - i) - 1)));
    }
    return res_num;
}
```
