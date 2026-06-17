# Issues

Resolved:

- The QCP workspace must be staged from `/home/yangfp/CAV/OS/CAV`; running the staging command from inside `QualifiedCProgramming` makes relative `input/xizi/...` paths fail.
- Because the shared XiZi header includes local strategy rules, the case-local `deps/` directory must include and compile `xizi_single_link_strategy_goal.v` and `xizi_single_link_strategy_proof.v`.

No unresolved issues.
