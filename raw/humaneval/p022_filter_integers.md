# P022 Filter integers

## Problem (HumanEval 22)

Filter given vector of any python values only for integers
>>> p022_filter_integers({"a", 3.14, 5})
{5}
>>> p022_filter_integers({1, 2, 3, "abc", {}, {}})
{1, 2, 3}

## Reference Implementation

```c
typedef enum {
    PY_INT,
    PY_DOUBLE,
    PY_STRING
} PyType;

typedef struct {
    PyType type;
    int i;
    double d;
    const char* s;
} PyValue;

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray p022_filter_integers(const PyValue* values, int values_size){
    IntArray out;
    out.size = 0;
    out.data = (int*)malloc((size_t)values_size * sizeof(int));
    if (out.data == NULL) return out;
    for (int i=0;i<values_size;i++)
    {
        if (values[i].type == PY_INT)
            out.data[out.size++] = values[i].i;
    }
    return out;
}
```
