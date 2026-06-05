# Add 85

## Problem (HumanEval 85)

Given a non-empty vector of integers lst. add_85 the even elements that are at odd indices..


Examples:
    add_85({4, 2, 6, 7}) ==> 2

## Reference Implementation

```c
int add_85(int* lst, int lst_size){
    int sum=0;
    for (int i=0;i*2+1<lst_size;i++)
        if (lst[i*2+1]%2==0) sum+=lst[i*2+1];
    return sum;
}
```
