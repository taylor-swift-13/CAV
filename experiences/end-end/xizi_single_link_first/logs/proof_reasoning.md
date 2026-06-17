# Proof Reasoning

Generated obligations:

- `return_wit_1`: the field cell and `xizi_sll(first,l)` are unchanged, and the return value is exactly the loaded `first`.

Proof:

```coq
Proof.
  pre_process.
Qed.
```

The final audit re-ran `symexec`, restored checked proof files, compiled deps/goal/proofs/goal_check, and found no proof obligation markers.
