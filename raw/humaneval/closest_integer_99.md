# Closest Integer 99

## Problem (HumanEval 99)

Create a function that takes a value (string) representing a number
&& returns the closest integer to it. If the number is equidistant
from two integers, round it away from zero.

Examples
>>> closest_integer_99("10")
10
>>> closest_integer_99("15.3")
15

Note:
Rounding away from zero means that if the given number is equidistant
from two integers, the one you should return is the one that is the
farthest from zero. For example closest_integer_99("14.5") should
return 15 && closest_integer_99("-14.5") should return -15.

## Reference Implementation

```c
int closest_integer_99(const char* value){
    double w;
    w = strtod(value, NULL);
    return round(w);
}
```
