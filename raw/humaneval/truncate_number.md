# Truncate Number

## Problem (HumanEval 2)

Given a positive floating point number, it can be decomposed into
&& integer part (largest integer smaller than given number) && decimals
(leftover part always smaller than 1).

Return the decimal part of the number.
>>> truncate_number(3.5)
0.5

## Reference Implementation

```c
float truncate_number(float number){
    return number - floorf(number);
}
```
