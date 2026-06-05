# Is Simple Power 76

## Problem (HumanEval 76)

Your task is to write a function that returns true if a number x is a simple
power of n && false in other cases.
x is a simple power of n if n**int=x
For example:
is_simple_power_76(1, 4) => true
is_simple_power_76(2, 2) => true
is_simple_power_76(8, 2) => true
is_simple_power_76(3, 2) => false
is_simple_power_76(3, 1) => false
is_simple_power_76(5, 3) => false

## Reference Implementation

```c
bool is_simple_power_76(int x, int n){
    int p=1,count=0;
    while (p<=x && count<100)
    {
        if (p==x) return true;
        p=p*n;count+=1;
    }
    return false;
}
```
