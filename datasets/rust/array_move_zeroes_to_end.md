# Array Move Zeroes To End

## 问题描述

实现一个函数，把数组中的所有非零元素保持相对顺序移动到前面，并把剩余位置填成 `0`。

约定：
- `n` 表示数组长度，`n >= 0`。
- `a` 指向长度至少为 `n` 的整数数组。
- 非零元素的相对顺序必须保持不变。
- 返回后，数组前缀是原数组中按原顺序出现的所有非零元素，后缀全是 `0`。

## 参考实现

```rust
pub fn array_move_zeroes_to_end(n: i32, a: &mut [i32]) {
    let mut write: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[(i) as usize] != 0 {
            a[(write) as usize] = a[(i) as usize];
            write += 1;
        }
        i += 1;
    }
    while write < n {
        a[(write) as usize] = 0;
        write += 1;
    }
}
```

## 说明

第一轮循环把所有非零元素依次写入数组前缀。第二轮循环把剩余位置全部补成 `0`。
