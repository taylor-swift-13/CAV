## 2026-06-05 20:18:54 +0800 - Initial proof plan and required retrieval record

Query command:

```bash
python3 scripts/search_fingerprint.py --fingerprint /home/yangfp/CAV/C/CAV/output/verify_20260605_200638v_ex_perfect_number_code/logs/workspace_fingerprint.json --scope all --min-keyword-matches 1 --prefer-stage PROOF --top 5 --format markdown
```

Top 1-3 candidate paths:

```text
/home/yangfp/CAV/C/CAV/experiences/general/PROOF/19/c-parity-branches-use-z-rem-not-z-mod.md
/home/yangfp/CAV/C/CAV/experiences/general/PROOF/1/div-by-2-truncation.md
/home/yangfp/CAV/C/CAV/experiences/end-end/lcm_simple
```

Expanded files:

```text
/home/yangfp/CAV/C/CAV/experiences/general/PROOF/19/c-parity-branches-use-z-rem-not-z-mod.md
/home/yangfp/CAV/C/CAV/experiences/general/PROOF/1/div-by-2-truncation.md
/home/yangfp/CAV/C/CAV/experiences/end-end/lcm_simple/logs/proof_reasoning.md
/home/yangfp/CAV/C/CAV/experiences/end-end/lcm_simple/coq/generated/lcm_simple_proof_manual.v
```

Adopted proof patterns:

- Write step lemmas against the generated C remainder shape `n % (d)` / `Z.rem`, not against `Z.mod`, because the loop branch facts in `goal.v` already use `%` notation and helper mismatch would block rewriting.
- Keep scalar arithmetic witnesses short: for the addition safety witness, prove an intermediate bound from the semantic step lemma and then finish the actual `INT_MAX` target with `lia`.
- Treat the loop-preservation obligations as pure helper-lemma applications over the invariant equation, not as annotation problems, because `symexec` already generated the intended semantic state with `sum + aliquot_sum_tail_z(...) == aliquot_sum_z(n_pre)`.

Rejected patterns:

- The `div-by-2-truncation` helper is not directly applicable here because this VC does not use `Z.quot`/`÷`; the loop arithmetic is based on remainder and a fuelled recursive tail helper.
- The full `lcm_simple` divisibility machinery is stronger than needed. The reusable part is only the proof structure: establish a math helper first, then use it to discharge both safety and loop-preservation witnesses with small `lia` tails.

Current obligations in `/home/yangfp/CAV/C/CAV/output/verify_20260605_200638v_ex_perfect_number_code/coq/generated/ex_perfect_number_code_proof_manual.v`:

- `proof_of_ex_perfect_number_code_safety_wit_5`
- `proof_of_ex_perfect_number_code_entail_wit_1`
- `proof_of_ex_perfect_number_code_entail_wit_2_1`
- `proof_of_ex_perfect_number_code_entail_wit_2_2`
- `proof_of_ex_perfect_number_code_entail_wit_3`
- `proof_of_ex_perfect_number_code_return_wit_1`
- `proof_of_ex_perfect_number_code_return_wit_2`
- `proof_of_ex_perfect_number_code_return_wit_3`

The generated goals are all scalar/pure. The main proof work should therefore be:

1. Add local helper lemmas for the tail helper:
   - initialization `aliquot_sum_tail_z n 1 = aliquot_sum_z n`
   - step when `n % d = 0`
   - step when `n % d <> 0`
   - exit `aliquot_sum_tail_z n n = 0`
2. Use those helpers to prove:
   - initialization and loop preservation by rewriting the invariant equation
   - the addition safety witness by deriving `sum + d <= aliquot_sum_z n_pre <= INT_MAX`
   - the exit witness by rewriting the tail to `0`
3. Prove return witnesses by unfolding `ex_perfect_number_code_spec` and rewriting branch equalities from `sum = aliquot_sum_z n_pre`.

First replay infrastructure check:

```text
coqc ... coq/deps/ex_perfect_number_code_helper.v
Error: Cannot find a physical path bound to logical path ex_perfect_number_code.
```

This is a compile-path issue, not a proof-state issue. The helper depends on `original/ex_perfect_number_code.v`, so helper replay must compile with both `-Q "$ORIG" ""` and `-Q "$DEPS" ""`. Once the helper compiles, `goal.v` should be able to resolve `Require Import ex_perfect_number_code_helper`.

## 2026-06-05 20:24:44 +0800 - First `coqc` failure is notation shape, not tactic failure

Replay after inserting helper lemmas reached `proof_manual.v` and failed at:

```text
File ".../ex_perfect_number_code_proof_manual.v", line 33, characters 23-28:
Error: Unknown scope delimiting key d.
```

The failure is on bare remainder notation in the helper:

```coq
destruct (Z.eqb (n % d) 0) ...
```

This matches the retrieved `%`-shape warning: generated VCs in this environment print the C remainder branch as `n_pre % ( d )`, and the parser is stricter than ordinary Coq notation. The repair is purely syntactic: normalize all helper statements and local remainder expressions to the same parenthesized shape `n % ( d )`. No invariant or theorem structure change is needed.

## 2026-06-05 20:26:04 +0800 - Stop helper should avoid unavailable `Z.geb_lt`

The next replay reached the local stop helper and failed with:

```text
File ".../ex_perfect_number_code_proof_manual.v", line 75, characters 10-18:
Error: The reference Z.geb_lt was not found in the current environment.
```

This is only a library-name mismatch in the impossible branch of:

```coq
destruct (Z.geb n n) eqn:Hdgeb.
```

The proof does not need any strict-order helper there. Since the discriminant is syntactically `Z.geb n n`, the false branch can be closed by changing it to `true` and contradicting `Hdgeb`:

```coq
change (Z.geb n n) with true in Hdgeb.
discriminate.
```

That `change` form turned out not to be convertible in this printing environment, so the stable version is:

```coq
assert (Z.geb n n = true) as Hrefl by (apply Z.geb_le; lia).
rewrite Hrefl in Hdgeb.
discriminate.
```

This still avoids the absent `Z.geb_lt` name, but relies only on the already working `Z.geb_le` bridge.

## 2026-06-05 20:28:41 +0800 - `safety_wit_5` remains an entailment after the pure arithmetic setup

The first real witness failure was not missing arithmetic at all. A `coqtop` replay of `proof_of_ex_perfect_number_code_safety_wit_5` showed that after:

```coq
pre_process.
assert (Hstep : ...).
assert (Hnonneg_next : ...).
rewrite Hstep in H6.
```

the goal is still:

```coq
&( "n") # Int |-> n_pre ** (&( "d") # Int |-> d ** &( "sum") # Int |-> sum)
|-- “ sum + d <= 2147483647 ” && “ -2147483648 <= sum + d ”
```

So the previous `lia` failed because the proof was still at the entailment layer with live spatial context. The adopted fix is to keep the helper-lemma arithmetic preparation, then close the remaining entailment with:

```coq
entailer!
```

This is safe here because the arithmetic side has already been normalized to the generated pure target and `entailer!` can discharge the residual spatial frame plus the final pure bounds.

## 2026-06-05 20:29:40 +0800 - Retrieval rerun after the second `Cannot find witness`

Query command (rerun required by the repeated error class):

```bash
python3 scripts/search_fingerprint.py --fingerprint /home/yangfp/CAV/C/CAV/output/verify_20260605_200638v_ex_perfect_number_code/logs/workspace_fingerprint.json --scope all --min-keyword-matches 1 --prefer-stage PROOF --top 5 --format markdown
```

Top 1-3 candidate paths:

```text
/home/yangfp/CAV/C/CAV/experiences/general/PROOF/19/c-parity-branches-use-z-rem-not-z-mod.md
/home/yangfp/CAV/C/CAV/experiences/general/PROOF/1/div-by-2-truncation.md
/home/yangfp/CAV/C/CAV/experiences/end-end/lcm_simple
```

Expanded files actually reused:

```text
/home/yangfp/CAV/C/CAV/experiences/general/PROOF/19/c-parity-branches-use-z-rem-not-z-mod.md
/home/yangfp/CAV/C/CAV/experiences/end-end/lcm_simple/logs/proof_reasoning.md
```

Adopted/rejected patterns after rerun:

- Adopted again: when a scalar witness still has an entailment layer after the arithmetic setup, replace the final `lia` with an entailment-closing tactic and keep the local helper equalities for normalization.
- Rejected again: there is still no need for new division/truncation helper lemmas; the blocker is witness closure shape, not quotient algebra.

`coqtop` inspection of `proof_of_ex_perfect_number_code_entail_wit_1` showed the same underlying pattern as `safety_wit_5`: after `pre_process`, helper assertions, and `rewrite Hstart`, the goal is still an entailment

```coq
emp |-- ...
```

not a standalone arithmetic proposition. The additional missing pure fact is that the rewritten target asks for `0 <= aliquot_sum_z n_pre`, while the context still contains:

```coq
Hnonneg : 0 <= aliquot_sum_tail_z n_pre 1
Hstart  : aliquot_sum_tail_z n_pre 1 = aliquot_sum_z n_pre
```

So the correct closure pattern is:

```coq
rewrite Hstart in Hnonneg.
rewrite Hstart.
entailer!
```

The same reasoning should apply to the loop-preservation and loop-exit entailment witnesses: prepare the semantic equation with helper rewrites, preserve the needed nonnegativity fact in the same normalized shape, then close the remaining entailment with `entailer!`.

## 2026-06-05 20:31:11 +0800 - Exit witness used the wrong post-`subst` hypothesis name

The next replay failure was:

```text
Error: Found no subterm matching "aliquot_sum_tail_z n_pre n_pre" in H6.
```

`coqtop` inspection of `proof_of_ex_perfect_number_code_entail_wit_3` showed the actual post-`subst d` context is:

```coq
H5 : sum + aliquot_sum_tail_z n_pre n_pre = aliquot_sum_z n_pre
```

while `H6` is only the duplicated positivity fact `0 < n_pre`. This is exactly the witness-numbering instability warned about in the proof guidance. The repair is to rewrite the stop lemma into `H5`, not `H6`, and then let `entailer!` close the remaining `emp |-- ...` goal.

## 2026-06-05 20:32:24 +0800 - Return witnesses need entailment closure, not `reflexivity`

The next compile failure was:

```text
File ".../ex_perfect_number_code_proof_manual.v", line 188, characters 6-17:
Error: Proof is not complete.
```

## 2026-06-05 20:48:02 +0800 - Post-resymexec proof delta after restoring the original `for` form

Current generated state after rerunning

```bash
python3 scripts/symexec_keep_proofs.py --name ex_perfect_number_code --stamp 20260605_200638v
```

is:

```text
[keep-proofs] preserved=4 helpers=6 still_admitted=4 dropped_vc_changed=4
```

The open obligations are now only:

```text
proof_of_ex_perfect_number_code_entail_wit_3
proof_of_ex_perfect_number_code_return_wit_1
proof_of_ex_perfect_number_code_return_wit_2
proof_of_ex_perfect_number_code_return_wit_3
```

Precise current goal shapes from `/home/yangfp/CAV/C/CAV/output/verify_20260605_200638v_ex_perfect_number_code/coq/generated/ex_perfect_number_code_goal.v`:

- `entail_wit_3` now concludes only `sum = aliquot_sum_z(n_pre)` from
  `d >= n_pre`, `d <= n_pre`, and the invariant equation. The previous round's rewrite-through-`d = n_pre` pattern still applies, but the result no longer needs a post-loop `d = n_pre` fact in later return witnesses.
- `return_wit_1/2/3` now quantify only `(n_pre, sum)` and ask directly for
  `ex_perfect_number_code_spec n_pre {3,2,1}` from `sum = aliquot_sum_z n_pre`
  plus the corresponding branch inequality/equality.

Adopted proof pattern:

- Keep `entail_wit_3` as a one-step semantic rewrite: derive `d = n_pre` by `lia`, rewrite `aliquot_sum_tail_z_stop` into the invariant equality, and close the remaining entailment with `entailer!`.
- For the three return witnesses, unfold `ex_perfect_number_code_spec`, rewrite `sum = aliquot_sum_z n_pre`, case-split on the generated `Z.eqb` / `Z.gtb`, and finish contradictions or the successful branch with `entailer!`.

Separate audit-path repair required in parallel:

- `goal.v` still contains `Require Import ex_perfect_number_code_helper.`
- the helper currently lives only at `/home/yangfp/CAV/C/CAV/output/verify_20260605_200638v_ex_perfect_number_code/coq/deps/ex_perfect_number_code_helper.v`
- runner audit previously bare-compiled `goal.v`, so the helper also needs a sibling source under `coq/generated/` to satisfy that replay path; this is a load-path placement fix, not a semantic proof change.

## 2026-06-05 20:51:14 +0800 - Generated helper made self-contained for replay stability

After moving `ex_perfect_number_code_helper.v` under `coq/generated/`, a direct local check of that helper showed:

```text
Error: Cannot find a physical path bound to logical path ex_perfect_number_code.
```

The problem was inside the helper source itself:

```coq
Require Import ex_perfect_number_code.
Definition aliquot_sum_tail_z ... := aliquot_sum_from_fuel ...
```

That dependency is unnecessary for generated-file replay. The adopted fix was:

- change the generated helper to define a local copy `aliquot_sum_from_fuel_tail`;
- define `aliquot_sum_tail_z` from that local fixpoint;
- add a manual-proof bridge lemma
  `aliquot_sum_from_fuel_tail_eq : ... = aliquot_sum_from_fuel ...`
  so `aliquot_sum_tail_z_start` can still rewrite to the original `aliquot_sum_z`.

Why this is the right repair:

- it removes the helper's dependence on the original-path import during generated replay;
- it leaves the VC semantics unchanged because the new local fixpoint is definitionally identical to the original recurrence;
- only one proof lemma (`aliquot_sum_tail_z_start`) needed adjustment, by inserting the equality bridge before `reflexivity`.

`coqtop` inspection of `proof_of_ex_perfect_number_code_return_wit_1` showed that the supposedly solved success branch is still:

```coq
emp |-- “ 3 = 3 ” && emp
```

after the `Z.eqb` / `Z.gtb` case analysis. So the issue is not the branch logic; it is that the proof is still at the entailment layer. The stable pattern for all three return witnesses is:

- use `lia` only on impossible branches (`3 = 1`, `3 = 2`, or the contradictory equality cases);
- use `entailer!` on the surviving branch that already reduced the pure proposition to `1 = 1`, `2 = 2`, or `3 = 3`.

## 2026-06-05 20:33:16 +0800 - `return_wit_2` false `Z.gtb` branch should be contradicted by rewriting to `true`

The next replay failure was:

```text
Error: The reference Z.gtb_ge was not found in the current environment.
```

This happened in the impossible false branch of `proof_of_ex_perfect_number_code_return_wit_2`. After `subst sum`, the context still states that `aliquot_sum_z n_pre > n_pre`, so the executable comparison must satisfy `aliquot_sum_z n_pre >? n_pre = true`. The stable proof is to build that equality with `Z.gtb_lt`, then rewrite it against the false branch equation:

```coq
assert ((aliquot_sum_z n_pre >? n_pre) = true) as Hgt_true.
{ apply Z.gtb_lt. lia. }
rewrite Hgt_true in Hgt.
discriminate.
```

This avoids the unavailable `Z.gtb_ge` lemma name and keeps the contradiction tied directly to the branch equation generated by `destruct`.

## 2026-06-05 20:52:40 +0800 - Retry retrieval before any new manual proof edits

Query command:

```bash
python3 scripts/search_fingerprint.py --fingerprint /home/yangfp/CAV/C/CAV/output/verify_20260605_200638v_ex_perfect_number_code/logs/workspace_fingerprint.json --scope all --min-keyword-matches 1 --prefer-stage PROOF --top 5 --format markdown
```

Top 1-3 candidate paths:

```text
/home/yangfp/CAV/C/CAV/experiences/general/PROOF/19/c-parity-branches-use-z-rem-not-z-mod.md
/home/yangfp/CAV/C/CAV/experiences/general/PROOF/1/div-by-2-truncation.md
/home/yangfp/CAV/C/CAV/experiences/end-end/lcm_simple
```

Expanded files in this retry round:

```text
/home/yangfp/CAV/C/CAV/experiences/general/PROOF/19/c-parity-branches-use-z-rem-not-z-mod.md
/home/yangfp/CAV/C/CAV/experiences/end-end/lcm_simple/logs/proof_reasoning.md
```

Adopted proof patterns for the upcoming regenerated VC:

- Keep branch lemmas aligned with the generated C `%` shape rather than introducing a separate helper import; the working pattern is to match the exact recursive definition already present in `original/ex_perfect_number_code.v`.
- Use local arithmetic helper lemmas plus a final `entailer!` when the witness remains an entailment after semantic rewriting.

Rejected patterns in this retry round:

- Do not keep `Require Import ex_perfect_number_code_helper` in the annotated file or regenerate VCs that depend on a workspace-local helper module, because bare audit replay compiles `generated/*.v` without that extra load-path and fails before proof checking.
- Do not apply the `div-by-2-truncation` pattern, because the present blocker is stale import / VC regeneration, not quotient-bridge arithmetic.
