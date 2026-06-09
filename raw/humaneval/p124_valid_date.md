# P124 Valid date

## Problem (HumanEval 124)

You have to write a function which validates a given date string &&
returns true if the date is valid otherwise false.
The date is valid if all of the following rules are satisfied:
1. The date string is ! empty.
2. The number of days is ! less than 1 || higher than 31 days for months 1,3,5,7,8,10,12. And the number of days is ! less than 1 || higher than 30 days for months 4,6,9,11. And, the number of days is ! less than 1 || higher than 29 for the month 2.
3. The months should ! be less than 1 || higher than 12.
4. The date should be in the format: mm-dd-yyyy

for example:
p124_valid_date("03-11-2000") => true

p124_valid_date("15-01-2012") => false

p124_valid_date("04-0-2040") => false

p124_valid_date("06-04-2020") => true

p124_valid_date("06/04/2020") => false

## Stub Function Specifications

Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.

### `strlen`

Coq model: represent strings as a list `l : list Z` of nonzero byte values followed by a zero terminator in memory.

Contract shape:

```c
int strlen(char *s)
/*@ With l n
    Require 0 <= n && n < INT_MAX &&
            Zlength(l) == n &&
            (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
            CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/;
```

## Reference Implementation

```c
/*
You have to write a function which validates a given date string &&
returns true if the date is valid otherwise false.
The date is valid if all of the following rules are satisfied:
1. The date string is ! empty.
2. The number of days is ! less than 1 || higher than 31 days for months 1,3,5,7,8,10,12. And the number of days is ! less than 1 || higher than 30 days for months 4,6,9,11. And, the number of days is ! less than 1 || higher than 29 for the month 2.
3. The months should ! be less than 1 || higher than 12.
4. The date should be in the format: mm-dd-yyyy

for example:
p124_valid_date("03-11-2000") => true

p124_valid_date("15-01-2012") => false

p124_valid_date("04-0-2040") => false

p124_valid_date("06-04-2020") => true

p124_valid_date("06/04/2020") => false
*/

int strlen(char *s)

;

int p124_valid_date(char *date)

{
    int i;
    int n = strlen(date);
    if (n != 10) {
        return 0;
    }

    for (i = 0; i < 10; i++) {
        if (i == 2 || i == 5) {
            if (date[i] != 45) {
                return 0;
            }
        } else {
            if (date[i] < 48 || date[i] > 57) {
                return 0;
            }
        }
    }

    int mm = (date[0] - 48) * 10 + (date[1] - 48);
    int dd = (date[3] - 48) * 10 + (date[4] - 48);
    if (mm < 1 || mm > 12) {
        return 0;
    }
    if (dd < 1 || dd > 31) {
        return 0;
    }
    if (dd == 31 && (mm == 4 || mm == 6 || mm == 9 || mm == 11 || mm == 2)) {
        return 0;
    }
    if (dd == 30 && mm == 2) {
        return 0;
    }
    return 1;
}
```
