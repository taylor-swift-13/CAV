# Right Angle Triangle 157

## Problem (HumanEval 157)

Given the lengths of the three sides of a triangle. Return true if the three
sides form a right-angled triangle, false otherwise.
A right-angled triangle is a triangle in which one angle is right angle || 
90 degree.
Example:
right_angle_triangle_157(3, 4, 5) == true
right_angle_triangle_157(1, 2, 3) == false

## Reference Implementation

```c
bool right_angle_triangle_157(float a, float b, float c){
    if (abs(a*a+b*b-c*c)<1e-4 || abs(a*a+c*c-b*b)<1e-4 || abs(b*b+c*c-a*a)<1e-4) return true;
    return false;
}
```
