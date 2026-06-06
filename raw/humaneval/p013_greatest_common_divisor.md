# P013 Greatest common divisor

## Problem (HumanEval 13)

Return a greatest common divisor of two integers a && b
>>> p013_greatest_common_divisor(3, 5)
1
>>> p013_greatest_common_divisor(25, 15)
5

## Reference Implementation

```c
int p013_greatest_common_divisor(int a, int b){
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
