# Issues

## Invalid Non-XiZi Model Removed

An earlier non-XiZi model for `single_link.c` was discarded. The current verified case uses `SysSingleLinklistType` and the `SingleLinklistNode.node_next` pointer field.

Invalid prior output and experience for `xizi_single_link_empty` were removed before this successful QCP run.

## QCP Header Preprocessor Boundary

QCP symexec rejected include guards and `#define NONE (0)` in the case-local XiZi header. The successful staged header contains only the XiZi struct/typedef and Coq declarations; `NONE` is represented in the executable as `(void *)0`, matching XiZi's null-pointer semantics.

## Missing Custom Strategy Artifacts

Including `xizi_single_link.strategies` without providing `xizi_single_link_strategy_goal.v` and `xizi_single_link_strategy_proof.v` caused `goal.v` compilation to fail. For this straight-line function, the strategy include was removed and the contract kept the needed `node_next` field cell explicit.

Final audit completed successfully.
