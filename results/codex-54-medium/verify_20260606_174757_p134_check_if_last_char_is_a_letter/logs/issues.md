## 2026-06-06

- Gate: `symexec`
  File: `/home/yangfp/CAV/C/CAV/annotated/verify_20260606_174757_p134_check_if_last_char_is_a_letter.c`
  Location: call to `strlen` at line 50
  Symptom: `Cannot derive the precondition of function strlen`
  Cause: the generated caller state did not instantiate `strlen`'s `With l n` variables automatically.
  Fix: added the call-site annotation `/*@ where l = l, n = len */` on `strlen(txt)` and reran `python3 scripts/symexec_keep_proofs.py --name p134_check_if_last_char_is_a_letter --stamp 20260606_174757`.

- Gate: `coqc proof_manual`
  Files:
  `/home/yangfp/CAV/C/CAV/output/verify_20260606_174757_p134_check_if_last_char_is_a_letter/coq/generated/p134_check_if_last_char_is_a_letter_proof_manual.v`
  `/home/yangfp/CAV/C/CAV/output/verify_20260606_174757_p134_check_if_last_char_is_a_letter/coq/generated/p134_check_if_last_char_is_a_letter_goal.v`
  Theorems: `proof_of_p134_check_if_last_char_is_a_letter_return_wit_{1..10}`
  Symptom: manual return witnesses initially failed due to mismatched facts on `l ++ [0]` versus `l`, plus impossible branches of `problem_134_spec l 0`.
  Fix: replaced all `Admitted` return witnesses with explicit proofs, using `app_Znth1` to transport last/previous-character facts from `l ++ 0 :: nil` back to `l`, and used explicit `exfalso` in the `problem_134_spec l 0` branches.
