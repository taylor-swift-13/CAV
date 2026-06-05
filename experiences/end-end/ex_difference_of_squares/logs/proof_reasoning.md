2026-06-05 08:11 CST

Phenomenon: `coq/generated/ex_difference_of_squares_proof_manual.v` contains exactly four remaining placeholders: `proof_of_ex_difference_of_squares_safety_wit_2`, `_7`, `_10`, and `_17`.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_080354v_ex_difference_of_squares/coq/generated/ex_difference_of_squares_proof_manual.v`, theorem names above. The generated VC file shows each target is a pure arithmetic safety entailment over the existing precondition facts from `ex_difference_of_squares_goal.v`.

Repair action: Replace each `Admitted` with the proof skeleton from `experiences/general/PROOF/README.md §3` for straight-line scalar safety VCs: `pre_process; entailer!; try lia`. This is the first try-first pass before deeper inspection with `coqtop`.

Key code/log fragment:

```coq
Definition ex_difference_of_squares_safety_wit_2 :=
  ...
|--
  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre * (n_pre + 1 ) )) ”.
```

Why this change: these witnesses only need facts already present in the precondition or immediate arithmetic consequences such as `0 <= n_pre * (n_pre + 1)`, so the standard `pre_process` + `entailer!` + `lia` path is the lowest-risk first attempt.

2026-06-05 08:12 CST

Phenomenon: the first compile attempt failed at `proof_manual.v:25` with `Error: No such goal.`

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_080354v_ex_difference_of_squares/coq/generated/ex_difference_of_squares_proof_manual.v:22-27`, theorem `proof_of_ex_difference_of_squares_safety_wit_2`.

Repair action: remove the trailing `lia` from all four manual lemmas and keep only `pre_process.` followed by `entailer!.`

Key code/log fragment:

```text
File ".../ex_difference_of_squares_proof_manual.v", line 25, characters 2-12:
Error: No such goal.
```

Why this change: for these generated safety witnesses, `entailer!` already consumes the available pure hypotheses and finishes the proof. The extra arithmetic tactic is not strengthening the proof; it is running after the goal is closed.

2026-06-05 08:13 CST

Phenomenon: recompilation still fails at `proof_manual.v:25`, now exactly on `entailer!`, with the same `No such goal` message.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_080354v_ex_difference_of_squares/coq/generated/ex_difference_of_squares_proof_manual.v:22-26`, again at `proof_of_ex_difference_of_squares_safety_wit_2`.

Repair action: shrink all four proofs one step further to `Proof. pre_process. Qed.` and retry the compile chain.

Key code/log fragment:

```text
22 Lemma proof_of_ex_difference_of_squares_safety_wit_2 : ...
23 Proof.
24   pre_process.
25   entailer!.
26 Qed.
```

Why this change: these safety witnesses are generated in a form where `pre_process` itself normalizes and solves the entailment. The stable signal is that every additional tactic after `pre_process` hits an already-closed proof state.
