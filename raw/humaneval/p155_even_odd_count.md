# P155 Even odd count

## Problem (HumanEval 155)

Given an integer. return a vector that has the number of even && odd digits respectively.

 Example:
    p155_even_odd_count(-12) ==> {1, 1}
    p155_even_odd_count(123) ==> {1, 2}

## Reference Implementation

```c
/*
Given an integer. return a vector that has the number of even && odd digits respectively.

 Example:
    p155_even_odd_count(-12) ==> {1, 1}
    p155_even_odd_count(123) ==> {1, 2}
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

int abs(int x)

{
    if (x < 0) return -x;
    else return x;
}

IntArray *p155_even_odd_count(int num)

{
    int w = abs(num);
    int n1=0,n2=0;
    int d=0;
    if (w == 0) n2 = 1;

    while (w > 0) {
        d = w % 10;
        if (d % 2 == 1) {
            n1 += 1;

        } else {
            n2 += 1;

        }
        w /= 10;
    }
    IntArray *out = malloc_int_array_struct();
    out->data = malloc_int_array(2);
    out->size = 2;
    int *data = out->data;
    data[0] = n2;
    data[1] = n1;
    return out;
}
```
