## 2026-06-02 Verification record

Phenomenon: the proof-only workspace had one remaining manual witness in `/home/yangfp/CAV/OS/CAV/output/verify_20260602_185301v_xizi_circular_area_write_advance/coq/generated/xizi_circular_area_write_advance_proof_manual.v`, theorem `proof_of_xizi_circular_area_write_advance_return_wit_2`.

Location: generated VC at `/home/yangfp/CAV/OS/CAV/output/verify_20260602_185301v_xizi_circular_area_write_advance/coq/generated/xizi_circular_area_write_advance_goal.v`, definition `xizi_circular_area_write_advance_return_wit_2`.

Fix actions:

```coq
Proof.
  pre_process.
  entailer!.
  - intros Heq.
    rewrite Heq.
    apply Z.rem_same.
    lia.
  - intros Hlt.
    apply Z.rem_small.
    lia.
Qed.
```

Key debugging evidence:

```text
1. Initial failure after `entailer!`: first subgoal order was equality case before strict-less-than case.
2. Equality branch normalized to `area_length_pre % area_length_pre = 0`.
3. `%` in this environment is `Z.rem`, not `Z.mod`; `Z.mod_same` and `Z.mod_small` did not unify, while `Z.rem_same` and `Z.rem_small` matched the generated goal head.
```

Why this worked: the branch condition `writeidx_pre + data_length_pre <= area_length_pre` makes the `>` implication vacuous, so only the equality and strict-less-than arithmetic cases remain. The final proof discharges those two `Z.rem` facts directly under `0 < area_length_pre`.

Machine-gate status:

```text
- coqc ... xizi_circular_area_write_advance_goal.v        : pass
- coqc ... xizi_circular_area_write_advance_proof_auto.v  : pass
- coqc ... xizi_circular_area_write_advance_proof_manual.v: pass
- coqc ... xizi_circular_area_write_advance_goal_check.v  : pass
- input/original integrity                                : pass
- input/annotated equality in proof-only mode             : pass
- cleanup of non-.v files under coq/ and input/           : pass
```

Final Result: Success
