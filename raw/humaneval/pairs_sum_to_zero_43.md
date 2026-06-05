# Pairs Sum To Zero 43

## Problem (HumanEval 43)

pairs_sum_to_zero_43 takes a vector of integers as an input.
it returns true if there are two distinct elements in the vector that
sum to zero, && false otherwise.
>>> pairs_sum_to_zero_43({1, 3, 5, 0})
false
>>> pairs_sum_to_zero_43({1, 3, -2, 1})
false
>>> pairs_sum_to_zero_43({1, 2, 3, 7})
false
>>> pairs_sum_to_zero_43({2, 4, -5, 3, 5, 7})
true
>>> pairs_sum_to_zero_43({1})
false

## Reference Implementation

```c
bool pairs_sum_to_zero_43(int* l, int l_size){
    for (int i=0;i<l_size;i++)
    for (int j=i+1;j<l_size;j++)
    if (l[i]+l[j]==0) return true;
    return false;
}
```
