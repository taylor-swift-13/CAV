# Parser Buffer Phase Boundary Should Export `IntArray::full`

Symptom: a parser loop fills a local buffer with an `IntArray::seg(values, 0, n, vals) * IntArray::undef_seg(values, n, CAP)` invariant, then a later consumer loop reads only the initialized prefix. `symexec` keeps failing at function teardown or a late return bridge with errors like `Fail to Remove Memory Permission of values`, `... of stop`, or `... of n`.

Cause: the parse phase leaves the stack array in a partially-initialized split form all the way to return, so verify is forced to add a fragile epilogue `Assert` just to abstract local ownership before cleanup. That late bridge tends to interact badly with surviving locals and frontend cleanup.

Rule: after the parsing loop finishes and you already know `vals == parse_csv(...)` and `n == Zlength(vals)`, convert the local buffer once at the phase boundary to a full-array view:

```c
/*@ Assert
      exists vals tail,
      vals == parse_csv(l) &&
      n == Zlength(vals) &&
      0 <= n && n <= CAP &&
      IntArray::full(values, CAP, app(vals, tail)) *
      ...
*/
```

Then carry that `IntArray::full(values, CAP, app(vals, tail))` shape through the consumer-loop invariant, and let the return use the consumer-loop exit facts directly.

Minimal command shape:

```text
parser loop with seg/undef_seg
  -> phase-boundary Assert to IntArray::full(values, CAP, app(vals, tail))
  -> consumer-loop invariant keeps the same full-array footprint
  -> no return-side bridge just for stack-array cleanup
```

Scope: string/array parsers that first materialize parsed tokens into a fixed local array and then run a second pass over the initialized prefix. This is especially useful when the second pass only needs reads and the late return bridge is the only reason local array ownership is still being reshaped at epilogue time.
