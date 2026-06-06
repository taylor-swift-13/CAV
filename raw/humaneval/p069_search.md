# P069 Search

## Problem (HumanEval 69)

You are given a non-empty vector of positive integers. Return the greatest integer that is greater than
zero, && has a frequency greater than || equal to the value of the integer itself.
The frequency of an integer is the number of times it appears in the vector.
If no such a value exist, return -1.
Examples:
    p069_search({4, 1, 2, 2, 3, 1}) == 2
    p069_search({1, 2, 2, 3, 3, 3, 4, 4, 4}) == 3
    p069_search({5, 5, 4, 4, 4}) == -1

## Reference Implementation

```c
/*
You are given a non-empty vector of positive integers. Return the greatest integer that is greater than
zero, && has a frequency greater than || equal to the value of the integer itself.
The frequency of an integer is the number of times it appears in the vector.
If no such a value exist, return -1.
Examples:
    p069_search({4, 1, 2, 2, 3, 1}) == 2
    p069_search({1, 2, 2, 3, 3, 3, 4, 4, 4}) == 3
    p069_search({5, 5, 4, 4, 4}) == -1
*/

int *malloc_int_array(int size)
;

void free_int_array(int *array, int init_size, int size)
;

int p069_search(int* lst, int lst_size)

{
    int* vals;
    int* cnts;
    int freq_size = 0;
    int max = -1;

    vals = malloc_int_array(lst_size);
    cnts = malloc_int_array(lst_size);
    if (vals == 0 || cnts == 0) {
        return -1;
    }

    int i;
    int current = 0;
    int has = 0;
    int j = 0;

    for (i=0; i<lst_size; i++)
    {
        current = lst[i];
        has = 0;

        for (j=0; j<freq_size; j++)
            if (current==vals[j])
            {
                cnts[j]+=1;
                has=1;
                if (cnts[j]>=vals[j] && vals[j]>max) max=vals[j];
                break;
            }

        if (has == 0)
        {

            vals[freq_size]=current;

            cnts[freq_size]=1;
            freq_size += 1;
            if (max==-1 && current==1) max=1;

        }

    }
    free_int_array(vals, freq_size, lst_size);
    free_int_array(cnts, freq_size, lst_size);
    return max;
}
```
