# Below Threshold 52

## Problem (HumanEval 52)

Return true if all numbers in the vector l are below threshold t.
>>> below_threshold_52({1, 2, 4, 10}, 100)
true
>>> below_threshold_52({1, 20, 4, 10}, 5)
false

## Reference Implementation

```c
bool below_threshold_52(int* l, int l_size, int t){
    for (int i=0;i<l_size;i++)
        if (l[i]>=t) return false;
    return true;
}
```
