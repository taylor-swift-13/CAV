# Greatest Common Divisor 13

## Problem (HumanEval 13)

Return a greatest common divisor of two integers a && b
>>> greatest_common_divisor_13(3, 5)
1
>>> greatest_common_divisor_13(25, 15)
5

## Reference Implementation

```c
int greatest_common_divisor_13(int a, int b){
    int out,m;
    while (1){
        if (a<b) 
        {
            m=a;a=b;b=m;
        }
        a=a%b;
        if (a==0) return b;
    }
}
```
