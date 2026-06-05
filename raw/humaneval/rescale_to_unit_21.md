# Rescale To Unit 21

## Problem (HumanEval 21)

Given vector of numbers (of at least two elements), apply a linear transform to that vector,
such that the smallest number will become 0 && the largest will become 1
>>> rescale_to_unit_21({1.0, 2.0, 3.0, 4.0, 5.0})
{0.0, 0.25, 0.5, 0.75, 1.0}

## Reference Implementation

```c
typedef struct {
    float* data;
    int size;
} FloatArray;

FloatArray rescale_to_unit_21(const float* numbers, int numbers_size){ 
    float min=100000,max=-100000;
    FloatArray out;
    out.data = (float*)malloc((size_t)numbers_size * sizeof(float));
    out.size = numbers_size;
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }

    for (int i=0;i<numbers_size;i++)
        {
            if (numbers[i]<min) min=numbers[i];
            if (numbers[i]>max) max=numbers[i];
        }
    if (max == min) {
        for (int i = 0; i < numbers_size; i++) {
            out.data[i] = 0.0f;
        }
        return out;
    }

    for (int i=0;i<numbers_size;i++)
        out.data[i]=(numbers[i]-min)/(max-min);
    return out;
}
```
