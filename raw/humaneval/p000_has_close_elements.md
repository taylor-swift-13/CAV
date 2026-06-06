# P000 Has close elements

## Problem (HumanEval 0)

Check if in given vector of numbers, are any two numbers closer to each other than
given threshold.
>>> p000_has_close_elements({1.0, 2.0, 3.0}, 0.5)
false
>>> p000_has_close_elements({1.0, 2.8, 3.0, 4.0, 5.0, 2.0}, 0.3)
true

## Reference Implementation

```c
bool p000_has_close_elements(float* numbers, int numbers_size, float threshold){
    int i,j;

    for (i=0;i<numbers_size;i++)
    for (j=i+1;j<numbers_size;j++)
    if (abs(numbers[i]-numbers[j])<threshold)
    return true;

    return false;
}
```
