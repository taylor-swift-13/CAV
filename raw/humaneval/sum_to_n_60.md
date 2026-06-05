# Sum To N 60

## Problem (HumanEval 60)

sum_to_n_60 is a function that sums numbers from 1 to n.
>>> sum_to_n_60(30)
465
>>> sum_to_n_60(100)
5050
>>> sum_to_n_60(5)
15
>>> sum_to_n_60(10)
55
>>> sum_to_n_60(1)
1

## Reference Implementation

```c
int sum_to_n_60(int n){
    return n*(n+1)/2;
}
```
