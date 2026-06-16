## 2026-06-06

- `coqc input/humaneval/p055_fib.v` initially failed because the load-paths from the generic compilation template did not match this repository layout. Resolution: switched all `-R` roots to `QualifiedCProgramming/SeparationLogic/...`, which made the spec and generated files compile.

- `coq/generated/p055_fib_proof_manual.v` needed a nontrivial local bridge from `fib_seq` to the `nat`-based `fib` in [input/humaneval/p055_fib.v](/home/yangfp/CAV/C/CAV/input/humaneval/p055_fib.v:1). The direct proof of `fib_seq_step` against `fib_seq_fuel` kept failing on fuel-shape mismatches. Resolution: added local lemmas `nat_ind2`, `fib_seq_fuel_enough`, and `fib_seq_as_nat` in [p055_fib_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260606_221239_p055_fib/coq/generated/p055_fib_proof_manual.v:21), then derived `fib_seq_step` from the `nat` Fibonacci recurrence.

- `proof_of_p055_fib_entail_wit_1` left hidden obligations after a naive `repeat split`. The remaining blockers were the quoted `fib_step_int_range` bounds and `isvalidptr_int` address facts. Resolution: unfolded `fib_step_int_range`, `isvalidptr_int`, and the final `coq_prop` obligation explicitly, then discharged the lower/upper range goals from the specialized hypothesis.

- `proof_of_p055_fib_entail_wit_2_1` and `proof_of_p055_fib_entail_wit_2_2` similarly exposed hidden range obligations and brittle base-case rewrites. Resolution: normalized `coq_prop` and pointer-validity facts up front, proved the range subgoals via specialized `fib_step_int_range`, and handled the concrete `i = 2` case with direct normalization instead of fragile `fib_seq_0/fib_seq_1/fib_seq_2` rewrites alone.
