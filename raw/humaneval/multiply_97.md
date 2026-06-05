# Multiply 97

## Problem (HumanEval 97)

Complete the function that takes two integers && returns 
the product of their unit digits.
Assume the input is always valid.
Examples:
multiply_97(148, 412) should return 16.
multiply_97(19, 28) should return 72.
multiply_97(2020, 1851) should return 0.
multiply_97(14,-15) should return 20.

## Reference Implementation

```c
int multiply_97(int a, int b){
    return (abs(a)%10)*(abs(b)%10);
}
```
