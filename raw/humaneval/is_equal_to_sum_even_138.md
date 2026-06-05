# Is Equal To Sum Even 138

## Problem (HumanEval 138)

Evaluate whether the given number n can be written as the sum of exactly 4 positive even numbers
Example
is_equal_to_sum_even_138(4) == false
is_equal_to_sum_even_138(6) == false
is_equal_to_sum_even_138(8) == true

## Reference Implementation

```c
bool is_equal_to_sum_even_138(int n){
    if (n%2==0 && n>=8) return true;
    return false;
}
```
