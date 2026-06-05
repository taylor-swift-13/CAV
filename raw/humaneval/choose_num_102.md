# Choose Num 102

## Problem (HumanEval 102)

This function takes two positive numbers x && y && returns the
biggest even integer number that is in the range [x, y] inclusive. If 
there's no such number, then the function should return -1.

For example:
choose_num_102(12, 15) = 14
choose_num_102(13, 12) = -1

## Reference Implementation

```c
int choose_num_102(int x, int y){
    if (y<x) return -1;
    if (y==x && y%2==1) return -1;
    if (y%2==1) return y-1;
    return y;
}
```
