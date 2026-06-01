# Combined Algorithm Dataset

- Problems: 518
- Languages: C, Java, Rust
- Layout: one Markdown file per problem per language in `c/`, `java/`, and `rust/`.
- Tests: shared JSON files in `tests/`.
- Difficulty: every problem has a `difficulty` field in `tests/*.json` and `manifest.json`.
- Difficulty counts: easy 305, medium 204, hard 9.
- Source counts: CAV-JAVA local dataset 175, LeetCode 140, Luogu 32, FormalBench 109, SpecGenBench 20, Exercism 42.
- Source attribution: every problem includes a `source` field in `tests/*.json` and `manifest.json`.
- Generation: `python3 scripts/expand_multisource_dataset.py`
