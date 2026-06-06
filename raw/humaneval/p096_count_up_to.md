# P096 Count up to

## Problem (HumanEval 96)

Implement a function that takes an non-negative integer && returns a vector of the first n
integers that are prime numbers && less than n.
for example:
p096_count_up_to(5) => {2,3}
p096_count_up_to(11) => {2,3,5,7}
p096_count_up_to(0) => {}
p096_count_up_to(20) => {2,3,5,7,11,13,17,19}
p096_count_up_to(1) => {}
p096_count_up_to(18) => {2,3,5,7,11,13,17}

## Reference Implementation

```c
/*
Implement a function that takes an non-negative integer && returns a vector of the first n
integers that are prime numbers && less than n.
for example:
p096_count_up_to(5) => {2,3}
p096_count_up_to(11) => {2,3,5,7}
p096_count_up_to(0) => {}
p096_count_up_to(20) => {2,3,5,7,11,13,17,19}
p096_count_up_to(1) => {}
p096_count_up_to(18) => {2,3,5,7,11,13,17}
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

IntArray *p096_count_up_to(int n)

{
    IntArray *out = malloc_int_array_struct();
    out->data = malloc_int_array(n);
    int *data = out->data;
    int output_size = 0;
    out->size = 0;
    int i;
    int d;

    if (n > 2) {

        for (i=2;i<n;i++)
        {
            if (output_size == 0) {

                data[output_size] = i;
                output_size = output_size + 1;
            } else {
                int j;
                int isp=1;

                j = 0;
                while (j < output_size) {
                    d = data[j];
                    if (d <= 0) break;
                    if (d > i / d) break;
                    if (i % d == 0) isp=0;
                    j = j + 1;
                }
                if (isp) {data[output_size] = i; output_size = output_size + 1;}
            }
        }
    }
    out->size = output_size;
    return out;
}
```
