# P049 Modp

## Problem (HumanEval 49)

Return 2^n modulo p (be aware of numerics).
>>> p049_modp(3, 5)
3
>>> p049_modp(1101, 101)
2
>>> p049_modp(0, 101)
1
>>> p049_modp(3, 11)
8
>>> p049_modp(100, 101)
1

## Reference Implementation

```c
int p049_modp(int n, int p){
    int out=1;
    for (int i=0;i<n;i++)
        out=(out*2)%p;
    return out;
}
```
