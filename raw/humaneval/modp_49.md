# Modp 49

## Problem (HumanEval 49)

Return 2^n modulo p (be aware of numerics).
>>> modp_49(3, 5)
3
>>> modp_49(1101, 101)
2
>>> modp_49(0, 101)
1
>>> modp_49(3, 11)
8
>>> modp_49(100, 101)
1

## Reference Implementation

```c
int modp_49(int n, int p){
    int out=1;
    for (int i=0;i<n;i++)
        out=(out*2)%p;
    return out;
}
```
