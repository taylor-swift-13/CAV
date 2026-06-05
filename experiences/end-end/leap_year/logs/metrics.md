## Verify metrics

- Function: `leap_year`
- Source raw: `raw/leap_year.md`
- Contract output: `input/leap_year.c`
- Annotated C: `annotated/verify_20260604_105149_leap_year.c`
- Workspace: `output/verify_20260604_105149_leap_year`
- Manual proof obligations: 1 (`proof_of_leap_year_return_wit_4`)
- Verification: `leap_year_goal.v`, `leap_year_proof_auto.v`, `leap_year_proof_manual.v`, and `leap_year_goal_check.v` compiled successfully.
- Notes: runner proof-only agent did not return after writing the proof, so the stuck runner was terminated after manual `goal_check` recompile succeeded.

Final Result: Success
