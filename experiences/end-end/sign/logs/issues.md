# Issues

## Baseline anti-cheating scan

- Stage: verify
- Command: `scripts/check_jml_cheating.py --baseline /home/yangfp/CAV-JAVA/output/verify_20260423_044724_sign/original/sign.java /home/yangfp/CAV-JAVA/output/verify_20260423_044724_sign/verified/sign.java`
- Failing file and line: none
- OpenJML message: none
- Diagnosis: anti-cheating scan passed; baseline `requires`, `assignable`, and `ensures` clauses were preserved.
- Edit made: none
- Result after rerun: passed

## Baseline OpenJML ESC

- Stage: verify
- Command: `scripts/run_openjml_verify.sh /home/yangfp/CAV-JAVA/output/verify_20260423_044724_sign/verified/sign.java`
- Failing file and line: none
- OpenJML message: none
- Diagnosis: OpenJML proved the scalar branch postconditions without additional annotations.
- Edit made: none
- Result after rerun: passed
