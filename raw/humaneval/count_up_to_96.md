# Count Up To 96

## Problem (HumanEval 96)

Implement a function that takes an non-negative integer && returns a vector of the first n
integers that are prime numbers && less than n.
for example:
count_up_to_96(5) => {2,3}
count_up_to_96(11) => {2,3,5,7}
count_up_to_96(0) => {}
count_up_to_96(20) => {2,3,5,7,11,13,17,19}
count_up_to_96(1) => {}
count_up_to_96(18) => {2,3,5,7,11,13,17}

## Reference Implementation

```c
typedef struct {
    int* data;
    int size;
} IntArray;

IntArray count_up_to_96(int n){
    IntArray out;
    out.size = 0;
    out.data = (int*)malloc((size_t)n * sizeof(int));
    if (out.data == NULL) return out;
    int i,j;
    for (i=2;i<n;i++)
        if (out.size==0) {out.data[out.size++] = i;}
        else
        {
            bool isp=true;
            for (j=0;j<out.size && out.data[j]*out.data[j]<=i;j++)
                if (i%out.data[j]==0) isp=false;
            if (isp) out.data[out.size++] = i;
        }
    return out;
}
```
