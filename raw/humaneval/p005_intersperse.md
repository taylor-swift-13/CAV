# P005 Intersperse

## Problem (HumanEval 5)

Insert a number "delimeter" between every two consecutive elements of input vector `numbers"
>>> p005_intersperse({}, 4)
{}
>>> p005_intersperse({1, 2, 3}, 4)
{1, 4, 2, 4, 3}

## Reference Implementation

```c
void p005_intersperse(const int *numbers, int numbers_size, int delimeter,
         int *out)

{
    int k = 0;
    if (numbers_size == 0) {
        return;
    }

    out[k] = numbers[0];
    k = k + 1;

    int i;

    for (i = 1; i < numbers_size; i++) {
        out[k] = delimeter;
        k = k + 1;
        out[k] = numbers[i];
        k = k + 1;
    }

}
```
