# P076 Is simple power

## Problem (HumanEval 76)

Your task is to write a function that returns true if a number x is a simple
power of n && false in other cases.
x is a simple power of n if n**int=x
For example:
p076_is_simple_power(1, 4) => true
p076_is_simple_power(2, 2) => true
p076_is_simple_power(8, 2) => true
p076_is_simple_power(3, 2) => false
p076_is_simple_power(3, 1) => false
p076_is_simple_power(5, 3) => false

## Reference Implementation

```c
/*
Your task is to write a function that returns true if a number x is a simple
power of n && false in other cases.
x is a simple power of n if n**int=x
For example:
p076_is_simple_power(1, 4) => true
p076_is_simple_power(2, 2) => true
p076_is_simple_power(8, 2) => true
p076_is_simple_power(3, 2) => false
p076_is_simple_power(3, 1) => false
p076_is_simple_power(5, 3) => false
*/

int p076_is_simple_power(int x, int n)

{
    int p=1,count=0;

    while (p<=x && count<100)
    {
        if (p==x) return 1;
        p=p*n;count+=1;
    }
    return 0;
}
```
