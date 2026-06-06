# P097 Multiply

## Problem (HumanEval 97)

Complete the function that takes two integers && returns
the product of their unit digits.
Assume the input is always valid.
Examples:
p097_multiply(148, 412) should return 16.
p097_multiply(19, 28) should return 72.
p097_multiply(2020, 1851) should return 0.
p097_multiply(14,-15) should return 20.

## Reference Implementation

```c
int p097_multiply(int a, int b){
    return (abs(a)%10)*(abs(b)%10);
}
```
