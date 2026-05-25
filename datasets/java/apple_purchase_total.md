# apple_purchase_total

## Problem

Return the total cost for buying `count` apples when each apple costs `price`.

## Requirements

- `count >= 0` and `price >= 0`.
- The mathematical product is guaranteed to fit in a signed 32-bit integer.
- Zero count or zero price must return zero.
- No input parsing is part of the function; both values are already provided as integers.

## Source

- Source: Luogu problem `P5703`.
- URL: https://www.luogu.com.cn/problem/P5703
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ApplePurchaseTotal {
    public static int apple_purchase_total(int count, int price) {
        return count * price;
    }
}
```
