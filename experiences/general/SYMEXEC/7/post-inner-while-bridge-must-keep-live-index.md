# Post-inner-`while` bridge must summarize the still-live loop index (2026-06-05)

Symptom:

- a function uses a nested `while` loop, and the inner loop introduces a block-local index such as `i`;
- `symexec` succeeds on the inner-loop invariant itself, but fails immediately at the bridge `Assert` after the inner loop with an error like:

```text
Error: Fail to Remove Memory Permission of i:...
```

- the bridge already carries the semantic fact you wanted, for example `p == Zpower(d, digits)`, so the failure looks unrelated to arithmetic.

Cause:

- for a `while` loop, the inner index variable is still live at the post-loop control point;
- a bridge `Assert` is a cutpoint, so if it does not summarize that live local, QCP loses the store/cleanup path for the variable and then fails while removing local permissions;
- this differs from borrowed patterns taken from `for`-loop proofs, where the loop index may already be out of scope by the time the bridge is placed.

Rule:

- after an inner `while`, if the first failure is `Fail to Remove Memory Permission of <idx>`, treat it as a control-point summary bug, not a proof bug;
- keep the semantic bridge, but also include the live index in the post-loop summary, usually as its exit fact such as `0 <= i && i == digits`;
- rerun `symexec` before changing proof scripts, because the problem is in the annotation cutpoint shape.

Minimal pattern:

```c
int i = 0;
while (i < digits) {
    p *= d;
    i++;
}

/* wrong: forgets the live inner-loop index */
/*@ Assert
      ...
      p == Zpower(d, digits)
*/
sum += p;
```

Repair:

```c
/*@ Assert
      ...
      0 <= i &&
      i == digits &&
      p == Zpower(d, digits)
*/
```

Scope:

- `problem_kind = math`
- `data = scalar`
- `pattern = nested_loop`
- especially decimal-scan / digit-power loops where an inner bounded `while` computes an accumulator and the outer loop immediately consumes it
