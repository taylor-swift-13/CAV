# P071 Triangle area

## Problem (HumanEval 71)

Given the lengths of the three sides of a triangle. Return the area of
the triangle rounded to 2 decimal points if the three sides form a valid triangle.
Otherwise return -1
Three sides make a valid triangle when the sum of any two sides is greater
than the third side.
Example:
p071_triangle_area(3, 4, 5) == 6.00
p071_triangle_area(1, 2, 10) == -1

## Stub Function Specifications

Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.

### `he_external_pow`

Coq model: define the mathematical power needed by the task. For integer exponents use repeated multiplication; for exponent `0.5`, use the square-root relation.

Contract shape:

```c
double he_external_pow(double x, double y)
/*@ Require emp
    Ensure he_pow_spec(x, y, __return)
*/;
```

## Reference Implementation

```c
double he_external_pow(double x, double y);
float p071_triangle_area(float a, float b, float c){
    if (a+b<=c || a+c<=b || b+c<=a) return -1;
    float h=(a+b+c)/2;
    float area;
    area=he_external_pow(h*(h-a)*(h-b)*(h-c),0.5);
    return area;
}
```
