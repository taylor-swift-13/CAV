# Issues

## Baseline gate

- Stage: verify
- Command: `scripts/check_jml_cheating.py --baseline /home/yangfp/CAV-JAVA/output/verify_20260423_043442_abs/original/abs.java /home/yangfp/CAV-JAVA/output/verify_20260423_043442_abs/verified/abs.java`
- Failing file and line: none
- OpenJML message: none
- Diagnosis: anti-cheating scan passed; baseline contract clauses were preserved.
- Edit made: none
- Result after rerun: passed

## OpenJML gate

- Stage: verify
- Command: `scripts/run_openjml_verify.sh /home/yangfp/CAV-JAVA/output/verify_20260423_043442_abs/verified/abs.java`
- Failing file and line: none
- OpenJML message: none
- Diagnosis: OpenJML proved the scalar branch-split absolute-value implementation with the existing overflow guard.
- Edit made: none
- Result after rerun: passed
