# Issues

No open issues.

Notes:

- `run_verify.py` was not run.
- `const SysSingleLinklistType *` is accepted by QCP for this case.
- Old compiled XiZi deps in sibling CAV workspaces can shadow the current local `xizi_single_link_lib`; the audit script deletes sibling `deps/xizi_single_link*.vo/vok/vos/glob` artifacts before compiling.
