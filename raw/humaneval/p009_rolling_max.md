# P009 Rolling max

## Problem (HumanEval 9)

From a given vector of integers, generate a vector of rolling maximum element found until given moment
in the sequence.
>>> p009_rolling_max({1, 2, 3, 2, 3, 4, 2})
{1, 2, 3, 3, 3, 4, 4}

## Reference Implementation

```c
/*
From a given vector of integers, generate a vector of rolling maximum element found until given moment
in the sequence. Output is written into pre-allocated array `out` of the same size.
>>> p009_rolling_max({1, 2, 3, 2, 3, 4, 2}, out)
out = {1, 2, 3, 3, 3, 4, 4}
*/

int *p009_rolling_max(int *numbers, int numbers_size, int *out, int out_size)

{
    int i;
    int max = -2147483648;

    for (i = 0; i < numbers_size; ++i) {
        if (numbers[i] > max) max = numbers[i];
        out[i] = max;
    }

    return out;
}
```
