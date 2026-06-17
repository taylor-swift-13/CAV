# Issues

Resolved:

- QCP header parsing cannot rely on C preprocessor directives, so `NONE` is staged as `(void *)0`.
- Multiple CAV cases using a short logical name `xizi_single_link_lib` can leave duplicate `.vo` files under different `deps/` directories. The case-local audit removes other compiled `xizi_single_link_lib.*` artifacts before compiling the current case.
- The generated `proof_auto.v` contains `Admitted` by default. The audit overwrites it with a checked empty import file and keeps all real proofs in `proof_manual.v`.

Boundary:

- `xizi_single_link.strategies` is present in the QCP C workspace but not included by `xizi_single_link_def.h`, so this case does not validate that strategies file.
