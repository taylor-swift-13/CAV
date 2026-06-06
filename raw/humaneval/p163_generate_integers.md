# P163 Generate integers

## Problem (HumanEval 163)

Given two positive integers a && b, return the even digits between a
&& b, in ascending order.

For example:
p163_generate_integers(2, 8) => {2, 4, 6, 8}
p163_generate_integers(8, 2) => {2, 4, 6, 8}
p163_generate_integers(10, 14) => {}

## Reference Implementation

```c
/*
Given two positive integers a && b, return the even digits between a
&& b, in ascending order.

For example:
p163_generate_integers(2, 8) => {2, 4, 6, 8}
p163_generate_integers(8, 2) => {2, 4, 6, 8}
p163_generate_integers(10, 14) => {}
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

IntArray *p163_generate_integers(int a,int b)

{
    int m = 0;
    IntArray *out = malloc_int_array_struct();
    out->data = (void *)0;
    out->size = 0;
    if (b<a)
    {
        m=a;a=b;b=m;
    }

    int capacity = 10;
    out->data = malloc_int_array(capacity);
    int *data = out->data;
    if (data == 0) {
        return out;
    }
    int output_size = out->size;
    int i;

    for (i=a;i<=b;i++) {
        if (i<10 && i%2==0) {

            data[output_size] = i;
            output_size++;

        }

    }
    out->size = output_size;

    return out;
}
```
