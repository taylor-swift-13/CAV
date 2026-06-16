## 2026-06-06 manual proof compile blocker

- Gate: `coqc ../coq/generated/p046_fib4_proof_manual.v`
- Current files:
  - `/home/yangfp/CAV/C/CAV/annotated/verify_20260606_201036_p046_fib4.c`
  - `/home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/coq/generated/p046_fib4_goal.v`
  - `/home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/coq/generated/p046_fib4_proof_manual.v`
- Status:
  - Symexec succeeded after restoring the loop invariant.
  - Manual proofs were rewritten to remove all `Admitted`.
  - The remaining blocker is compile cost / non-return of `coqc` on `p046_fib4_proof_manual.v` after multiple proof repairs, rather than a new theorem error being reported.
- Concrete repair history:
  - Added the rolling-state invariant `a == fib4(i-4)`, `b == fib4(i-3)`, `c == fib4(i-2)`, `d == fib4(i-1)` to the active annotated C so symexec could generate VCs.
  - Replaced manual `Admitted` obligations with proofs for range witnesses, entailments, and returns.
  - Tried three loop-step proof strategies inside `p046_fib4_proof_manual.v`:
    1. symbolic `fib4_fuel` recurrence helper;
    2. bounded proof by destructing `Z.to_nat i`;
    3. bounded case split over `i = 4 .. 99` with precomputed arithmetic equalities.
  - The third strategy avoids the earlier semantic mismatch, but `coqc` still does not return in a practical time window.
- Next concrete step:
  - Refactor `proof_of_p046_fib4_entail_wit_2` / `fib4_unfold` to use a smaller reusable helper or a different arithmetic normalization strategy so `coqc` can finish and expose the next real failing theorem, if any.

## 2026-06-06 retry attempt 2 blocker after timeout repair

- Gates exercised:
  - `coqc -R ... -Q /home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/coq/generated SimpleC.EE.CAV.verify_20260606_201036_p046_fib4 ../coq/generated/p046_fib4_proof_manual.v`
  - `python3 scripts/symexec_keep_proofs.py --name p046_fib4 --stamp 20260606_201036`
- Current files:
  - `/home/yangfp/CAV/C/CAV/annotated/verify_20260606_201036_p046_fib4.c`
  - `/home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/coq/generated/p046_fib4_goal.v`
  - `/home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/coq/generated/p046_fib4_proof_manual.v`
- Concrete progress:
  - Replaced the giant top-level `fib4_unfold` case split with a direct structural proof of the loop-step recurrence in `proof_of_p046_fib4_entail_wit_2`; this removed the previous 120s compile timeout.
  - After that repair, `coqc` exposed real proof errors instead of timing out:
    - `proof_of_p046_fib4_safety_wit_14/15/16` specialized `fib4_step_int_range` with `H : i <= n_pre` instead of the required pair bound `4 <= i <= n_pre`.
    - `proof_of_p046_fib4_entail_wit_1` then exposed the real semantic blocker around `next`.
- Root blocker now:
  - The loop invariant in `/home/yangfp/CAV/C/CAV/annotated/verify_20260606_201036_p046_fib4.c` uses `exists next_v, next == next_v && ...`.
  - This generates `p046_fib4_entail_wit_1`, whose remaining goal is to derive
    `&( "next") # Int |->_ |-- EX (next_v: Z), &( "next") # Int |-> next_v`.
  - That obligation is too strong for an uninitialized local: the left side only gives `undef_store_int`, while the right side requires a concrete `store_int`.
- Repair attempt and outcome:
  - I removed `exists next_v, next == next_v` from the invariant and reran symexec.
  - Symexec then failed immediately with:
    `fatal error: cannot find the program variable next(338) in assertion, please check the @pre or related which implies in /home/yangfp/CAV/C/CAV/annotated/verify_20260606_201036_p046_fib4.c:66:8`
  - So within the current executable code, QCP requires `next` to appear in the invariant, but the current value-level way of mentioning it produces an unprovable VC from `next |->_`.
- Why this is blocked inside the write boundary:
  - A proof-only fix is not enough: the generated VC is wrong for the intended abstraction level of an uninitialized local.
  - An annotation-only removal is not enough: symexec rejects the invariant because `next` disappears from the assertion.
  - The obvious operational fix would be to initialize `next` before the loop, but that changes the executable implementation, which is outside the allowed verify-side edit contract for this task.
- Next concrete step for a future round:
  - Either allow an implementation-preserving-but-text-changing source edit such as initializing `next`, or provide a QCP-supported annotation pattern for live uninitialized locals that mentions the program variable without forcing `EX next_v, next |-> next_v`.

## 2026-06-06 retry attempt 3 proof/manual blocker confirmed unrepairable inside boundary

- Gate: `coqc` on `/home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/coq/generated/p046_fib4_proof_manual.v`
- Current files:
  - `/home/yangfp/CAV/C/CAV/annotated/verify_20260606_201036_p046_fib4.c`
  - `/home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/coq/generated/p046_fib4_goal.v`
  - `/home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/coq/generated/p046_fib4_proof_manual.v`
- Concrete proof repair:
  - Replaced the failing `eexists; entailer!` in `proof_of_p046_fib4_entail_wit_1` with an explicit existential witness attempt to address the `next` heap cell.
  - Recompiled in the correct workspace-relative mode:
    `coqc -R SeparationLogic/SeparationLogic SimpleC.SL -R SeparationLogic/unifysl Logic -R SeparationLogic/sets SetsClass -R SeparationLogic/compcert_lib compcert.lib -R SeparationLogic/auxlibs AUXLib -R SeparationLogic/examples SimpleC.EE -R SeparationLogic/StrategyLib SimpleC.StrategyLib -R SeparationLogic/Common SimpleC.Common -R SeparationLogic/fixedpoints FP -R SeparationLogic/MonadLib MonadLib -R SeparationLogic/listlib ListLib -Q /home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/original \"\" -Q /home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/coq/generated SimpleC.EE.CAV.verify_20260606_201036_p046_fib4 coq/generated/p046_fib4_proof_manual.v`
- Failing theorem / error:
  - `proof_of_p046_fib4_entail_wit_1`
  - `File "./coq/generated/p046_fib4_proof_manual.v", line 58, characters 2-37`
  - `Unable to unify "?_x # Int |-> ?_x0" with "&( s) # Int |->_".`
- Why this is a real blocker:
  - The generated goal in `p046_fib4_goal.v` requires
    `(&( "next")) # Int |->_ |-- EX next_v, (&( "next")) # Int |-> next_v`.
  - The local library only provides the one-way lemma
    `store_int_undef_store_int : (x # Int |-> v) |-- (x # Int |->_)`
    in `/home/yangfp/CAV/C/CAV/QualifiedCProgramming/SeparationLogic/SeparationLogic/StoreAux.v:509`.
  - `undef_store_int` is defined as `isvalidptr_int x && store_4byte_noninit x` in `/home/yangfp/CAV/C/CAV/QualifiedCProgramming/SeparationLogic/SeparationLogic/CommonAssertion.v:321`, and there is no converse lemma from noninitialized storage to a concrete `store_int`.
  - Therefore the current VC asks for information that is not derivable from the modeled heap state of an uninitialized local.
- Boundary conclusion:
  - This cannot be repaired by further proof edits inside `proof_manual.v`.
  - Removing `next` from the invariant is also not viable in this workspace because symexec rejects the invariant when the live program variable disappears.
  - The remaining repair would require either a different QCP-supported invariant pattern for live uninitialized locals or an executable-source change such as initializing `next`, which is outside the allowed verify-side edit contract here.

## 2026-06-06 retry attempt 4 annotation experiment rejected by symexec

- Gates exercised:
  - `coqc` in workspace-relative mode from `/home/yangfp/CAV/C/CAV/QualifiedCProgramming`
  - `python3 scripts/symexec_keep_proofs.py --name p046_fib4 --stamp 20260606_201036`
- Files touched:
  - `/home/yangfp/CAV/C/CAV/annotated/verify_20260606_201036_p046_fib4.c`
  - `/home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/coq/generated/p046_fib4_proof_manual.v`
- Concrete findings:
  - After compiling with the correct QCP-root load path, `original/p046_fib4.v`, `coq/generated/p046_fib4_goal.v`, and `coq/generated/p046_fib4_proof_auto.v` all compile successfully.
  - `proof_manual.v` still fails at `proof_of_p046_fib4_entail_wit_1`; trying to witness the postcondition directly exposed that the environment contains no concrete `next_v`, only the heap fact for `&( "next") # Int |->_`.
  - Library search confirmed the only relevant lemma is one-way:
    `store_int_undef_store_int : (x # Int |-> v) |-- (x # Int |->_)`
    from `/home/yangfp/CAV/C/CAV/QualifiedCProgramming/SeparationLogic/SeparationLogic/StoreAux.v:509`.
  - I then changed the invariant temporarily to
    `(i == 4 || next == next_v) && ...`
    so `next` would only need a concrete value after the first iteration.
  - Symexec rejected that annotation immediately with:
    `fatal error: cannot find the program variable next(338) in assertion, please check the @pre or related which implies in /home/yangfp/CAV/C/CAV/annotated/verify_20260606_201036_p046_fib4.c:68:8`
    and `symexec_keep_proofs.py` restored the previous generated files.
- Failure gate / current blocker:
  - Valid generated VC path still requires the invariant form `exists next_v, next == next_v && ...`, which regenerates the unprovable initial obligation from `next |->_` to `EX next_v, next |-> next_v`.
  - The only annotation-side weakening that preserves the original executable code was rejected by symexec before VC generation.
- Why this is the stop point:
  - Proof-only repair is blocked by the missing converse from `undef_store_int` to `store_int`.
  - Annotation-only repair is blocked because QCP refuses the conditional/non-direct mention of the live local `next`.
- The remaining semantic repair is to initialize `next` in the C code before the loop, which changes the executable implementation and violates the verify-side edit boundary for this task.

## 2026-06-06 retry attempt 5 storage-predicate invariant accepted, proof repair still incomplete

- Gates exercised:
  - `python3 scripts/symexec_keep_proofs.py --name p046_fib4 --stamp 20260606_201036`
  - `coqc -R /home/yangfp/CAV/C/CAV/QualifiedCProgramming/SeparationLogic/SeparationLogic SimpleC.SL ... -R /home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/coq/generated SimpleC.EE.CAV.verify_20260606_201036_p046_fib4 /home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/coq/generated/p046_fib4_proof_manual.v`
- Files changed in this round:
  - `/home/yangfp/CAV/C/CAV/annotated/verify_20260606_201036_p046_fib4.c`
  - `/home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/coq/generated/p046_fib4_proof_manual.v`
- Concrete repair that succeeded:
  - Replaced the loop invariant's pure `exists next_v, next == next_v` with a storage-predicate disjunction:
    - entry branch at `i == 4` uses `undef_data_at(&next, int)`
    - later branch uses `exists next_v, store(&next, next_v)`
  - Symexec accepted this invariant and regenerated a healthier VC:
    - `p046_fib4_entail_wit_1` is now a disjunction whose right branch keeps `next |->_` instead of forcing `EX next_v, next |-> next_v` at loop entry.
    - loop preservation split into `p046_fib4_entail_wit_2_1` for the `i = 4` branch and `p046_fib4_entail_wit_2_2` for the `i >= 5` branch.
- Current failing gate:
  - `coqc` on `/home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/coq/generated/p046_fib4_proof_manual.v`
- Precise current blocker:
  - latest error after multiple proof rewrites:
    `File "/home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/coq/generated/p046_fib4_proof_manual.v", line 95, characters 53-56: Error: Tactic failure: Cannot find witness.`
  - localization:
    `proof_of_p046_fib4_entail_wit_1`
  - the annotation-side VC is no longer the old impossible strengthening; the remaining problem is that the proof script still does not correctly normalize quoted pure assertions such as `“ 0 = fib4 0 ”` inside the right disjunct after `right; unfold andp; simpl`.
- Key proof-state findings from direct Coq inspection:
  - after `right; unfold andp; simpl`, the target becomes a nested conjunction of quoted pure facts and the final spatial fact `(&( "next")) # Int |->_`.
  - if one destructs the quoted `fib4_step_int_range` conjunct too aggressively, Coq expands it into 6 numeric subgoals plus the `next` validity/noninit components.
  - a better next step is to keep the quoted pure conjuncts abstract and use either:
    - a proof pattern that rewrites `“ P ” m` to `P` without expanding unrelated definitions, or
    - a library tactic/lemma for quoted pure assertions that avoids manual `andp` destruction.
- Why this is a timeout stop rather than a semantic impossibility claim:
  - symexec now accepts the annotation and the generated theorem shapes are semantically plausible.
  - the current blocker is a tactical Coq proof-engineering issue in `proof_manual.v`, not an annotation or contract contradiction that has been shown unrepairable.

## External Codex Failure

- Stage: `external-agent-run`
- Exit code: `124`
- Stderr log: `/home/yangfp/CAV/C/CAV/output/verify_20260606_201036_p046_fib4/logs/agent_stderr_20260606_215048.log`
- Detail: `external agent run exceeded remaining timeout budget of 1187 seconds`
