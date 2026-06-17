# Issues

- A single top-level disjunctive present/absent contract caused brittle `@pre` and address-rewrite behavior in QCP strategy search.
- The final verification uses two closed contracts for the same XiZi program behavior: present deletion and absent no-op.
- A broad field-store equality rewrite strategy was tested and rejected because it made `symexec` search diverge.

Final status: target-absent/no-op branch audited successfully.
