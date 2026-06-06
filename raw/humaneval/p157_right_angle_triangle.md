# P157 Right angle triangle

## Problem (HumanEval 157)

Given the lengths of the three sides of a triangle. Return true if the three
sides form a right-angled triangle, false otherwise.
A right-angled triangle is a triangle in which one angle is right angle ||
90 degree.
Example:
p157_right_angle_triangle(3, 4, 5) == true
p157_right_angle_triangle(1, 2, 3) == false

## Reference Implementation

```c
bool p157_right_angle_triangle(float a, float b, float c){
    if (abs(a*a+b*b-c*c)<1e-4 || abs(a*a+c*c-b*b)<1e-4 || abs(b*b+c*c-a*a)<1e-4) return true;
    return false;
}
```
