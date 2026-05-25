# Array Count Distinct Sorted

## 问题描述

实现一个函数，统计有序数组中不同整数值的个数。

约定：
- `n` 表示数组长度，`n >= 0`。
- `a` 指向长度至少为 `n` 的整数数组。
- 输入数组按非降序排列。
- 如果 `n == 0`，返回 `0`。

## 参考实现

```rust
pub fn array_count_distinct_sorted(mut n: i32, a: &[i32]) -> i32 {
    if n == 0 {
        return 0;
    }
    let mut count: i32 = 1;
    let mut i: i32 = 1;
    while i < n {
        if a[(i) as usize] != a[(i - 1) as usize] {
            count += 1;
        }
        i += 1;
    }
    return count;
}
```

## 说明

有序数组中相同元素一定连续出现。因此只需要统计当前位置是否与前一个位置不同，就能得到不同值的个数。
