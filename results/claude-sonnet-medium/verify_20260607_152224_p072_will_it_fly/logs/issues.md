# Issues Log — p072_will_it_fly

## Resolved Issues

### 1. `match goal` variable-name capture
- **Symptom**: `No matching clauses for match` when matching `forall k, ...` hypothesis after `intros k Hk`.
- **Cause**: The pattern variable `k` in `match goal with | H : forall k, ...` clashed with the free variable `k` already introduced in scope.
- **Fix**: Replaced all `match goal` hypothesis lookups with `assert ... by eassumption`, which finds hypotheses by type regardless of name.

### 2. Multi-goal `split_pures` with asserts ordered incorrectly
- **Symptom**: `safety_wit_7` — "Attempt to save an incomplete proof (there are remaining open goals)".
- **Cause**: `split_pures; dump_pre_spatial.` (with period) created 2 goals; subsequent `assert` + `lia` closed only the first.
- **Fix**: Moved all `assert`/`pose proof` before `split_pures.`, then used explicit `-` bullets.

### 3. `entail_wit_2` — unknown number of conjuncts after simplification
- **Symptom**: 7th bullet `eassumption` failure (`No applicable tactic`) for what appeared to be `will_it_fly_int_range lv`.
- **Cause**: `TT_simpl` inside `split_pures` eliminates `"(problem_72_pre lv w_pre)"` = `"True"` from the conjunction, reducing 9 goals to 8.
- **Fix**: Used `all: dump_pre_spatial.` then `all: try lia.`, `all: try eassumption.`, `all: try exact I.`, and explicit `try (...)` for the forall and sum goals — order-agnostic.

### 4. `intro _` syntax error
- **Symptom**: Syntax error at `intro _.` — `[ltac_use_default] expected after [tactic]`.
- **Cause**: `intro _` is not valid Coq 8.20 syntax; `intros _` must be used.
- **Fix**: Changed all `intro _.` to `intros _.`.

### 5. Hypothesis name collision (`H is already used`)
- **Symptom**: `H is already used` when writing `intro H.` in `return_wit_2`/`3`.
- **Cause**: `pre_process` auto-names hypotheses `H`, `H0`, … in the context.
- **Fix**: Renamed to `intro Heq0. discriminate Heq0.`

### 6. Goal structure mismatch in `return_wit_3` (need `exfalso`)
- **Symptom**: `Unable to unify '...' with '(0 =? 1) = true'` when calling `apply Hneq.`
- **Cause**: After `intro Hconj; destruct Hconj as [Hrev _]`, the goal is `false = true` (not `False`). `Hneq` has conclusion `False`.
- **Fix**: Added `exfalso.` before `apply Hneq.`

## Helper Lemmas Written

- `fold_left_Z_add_acc`: `fold_left (fun a x => a+x) l acc = acc + sum l`
- `sum_sublist_step`: `sum (sublist 0 (i+1) lv) = sum (sublist 0 i lv) + Znth i lv 0`
- `Znth_rev_lem`: `Znth k (rev l) 0 = Znth (Zlength l - 1 - k) l 0`
- `mirror_to_rev`: pointwise palindrome predicate implies `lv = rev lv`
