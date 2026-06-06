# P060 Sum to n

## Problem (HumanEval 60)

p060_sum_to_n is a function that sums numbers from 1 to n.
>>> p060_sum_to_n(30)
465
>>> p060_sum_to_n(100)
5050
>>> p060_sum_to_n(5)
15
>>> p060_sum_to_n(10)
55
>>> p060_sum_to_n(1)
1

## Reference Implementation

```c
int p060_sum_to_n(int n){
    return n*(n+1)/2;
}
```
