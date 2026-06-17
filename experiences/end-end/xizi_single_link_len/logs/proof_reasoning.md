# Proof Reasoning

Generated obligations:

- `safety_wit_1`, `safety_wit_2`: pure zero-literal range goals, closed by `pre_process`.
- `partial_solve_wit_1`: unfold non-null `xizi_sll(tmp_list,l2)` with `xizi_sll_not_zero`.
- `entail_wit_1`: initialize the invariant with `l1 = nil`, `l2 = l`.
- `entail_wit_2`: move one node from suffix to prefix using `xizi_sllseg_len1` and `xizi_sllseg_sllseg`.
- `return_wit_1`: use `xizi_sll_zero` to learn the suffix is nil at `tmp_list == 0`, then fold `xizi_sllseg(first,0,l1)` to `xizi_sll(first,l1)`.

One XiZi-specific helper was added to `xizi_single_link_lib.v`:

```coq
Lemma xizi_sllseg_0_sll: forall x l,
  xizi_sllseg x 0 l |-- xizi_sll x l.
```

This mirrors QCP's ordinary `sllseg_0_sll` pattern and is needed because `xizi_sll_zero` consumes the empty suffix when deriving `l2 = nil`.

For `unsigned_last_nbits(length + 1, 32)`, the proof uses `unsigned_last_nbits_eq`; the bound follows from:

- `length = Zlength(l1)`
- `l = l1 ++ d :: l0`
- `Zlength(l) <= UINT_MAX`
- `Zlength_nonneg`

The final audit re-ran `symexec`, restored checked proof files, compiled deps/goal/proofs/goal_check, and found no proof obligation markers.
