# Array Intersection Count Sorted

## 问题描述

实现一个函数，统计两个有序数组的多重集合交集大小。

约定：
- `n >= 0`，`m >= 0`。
- `a` 指向长度至少为 `n` 的整数数组，`b` 指向长度至少为 `m` 的整数数组。
- 两个数组都按非降序排列。
- 如果一个值在两个数组中都出现多次，则按可以配对的次数计数。

## 参考实现

```rust
pub fn array_intersection_count_sorted(n: i32, a: &[i32], m: i32, b: &[i32]) -> i32 {
    let mut i: i32 = 0;
    let mut j: i32 = 0;
    let mut count: i32 = 0;
    while i < n && j < m {
        if a[(i) as usize] == b[(j) as usize] {
            count += 1;
            i += 1;
            j += 1;
        } else if a[(i) as usize] < b[(j) as usize] {
            i += 1;
        } else {
            j += 1;
        }
    }
    return count;
}
```

## 说明

这段代码使用两个指针扫描两个有序数组。元素相等时形成一次配对；较小的一侧不可能再和当前较大元素配对，因此向前移动。
