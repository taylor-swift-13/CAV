# Combined Algorithm Dataset

- Problems: 626
- Languages: C, Java, Rust
- Layout: one Markdown file per problem per language in `c/`, `java/`, and `rust/`.
- Tests: shared JSON files in `tests/`.
- Difficulty: every problem has a `difficulty` field in `tests/*.json` and `manifest.json`.
- Difficulty counts: easy 315, medium 287, hard 24.
- Source counts: CAV-JAVA local dataset 175, LeetCode 237, Luogu 43, FormalBench 109, SpecGenBench 20, Exercism 42.
- Source attribution: every problem includes a `source` field in `tests/*.json` and `manifest.json`.
- Generation: `python3 scripts/expand_multisource_dataset.py`
