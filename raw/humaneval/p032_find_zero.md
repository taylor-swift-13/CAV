# P032 Find zero

## Problem (HumanEval 32)

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

### `he_external_fabs`

Coq model: define nonnegative absolute value over the chosen real-number model.

Contract shape:

```c
double he_external_fabs(double x)
/*@ Require emp
    Ensure he_fabs_spec(x, __return)
*/;
```

## Reference Implementation

```c
double he_external_pow(double x, double y);
double he_external_fabs(double x);
double poly(double* xs, int xs_size, double x){
    /*
    Evaluates polynomial with coefficients xs at point x. return xs[0] + xs[1] * x + xs[1] * x^2 + .... xs[n] * x^n
    */
    double sum=0;
    int i;
    for (i=0;i<xs_size;i++)
    {
        sum+=xs[i]*he_external_pow(x,i);
    }
    return sum;
}

double p032_find_zero(double* xs, int xs_size){
    /*
    xs are coefficients of a polynomial. p032_find_zero find x such that poly(x) = 0. p032_find_zero returns only only zero point, even if there are many.
    Moreover, p032_find_zero only takes list xs having even number of coefficients && largest non zero coefficient as it guarantees a solution.
    >>> round(p032_find_zero([1, 2]), 2) #f(x) = 1 + 2x
    -0.5
    >>> round(p032_find_zero([-6, 11, -6, 1]), 2) # (x - 1) * (x - 2) * (x - 3) = -6 + 11x - 6x^2 + x^3
    1.0
    */
    double ans=0;
    double value;
    value=poly(xs,xs_size,ans);
    while (he_external_fabs(value)>1e-6)
    {
        double driv=0;
        for (int i=1;i<xs_size;i++)
        {
            driv+=xs[i]*he_external_pow(ans,i-1)*i;
        }
        ans=ans-value/driv;
        value=poly(xs,xs_size,ans);
    }
    return ans;

}
```
