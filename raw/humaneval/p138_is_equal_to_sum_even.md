# P138 Is equal to sum even

## Problem (HumanEval 138)

Evaluate whether the given number n can be written as the sum of exactly 4 positive even numbers
Example
p138_is_equal_to_sum_even(4) == false
p138_is_equal_to_sum_even(6) == false
p138_is_equal_to_sum_even(8) == true

## Reference Implementation

```c
/*
Evaluate whether the given number n can be written as the sum of exactly 4 positive even numbers
Example
p138_is_equal_to_sum_even(4) == false
p138_is_equal_to_sum_even(6) == false
p138_is_equal_to_sum_even(8) == true
*/

int p138_is_equal_to_sum_even(int n)

{
    if (n%2==0 && n>=8) return 1;
    return 0;
}
```
