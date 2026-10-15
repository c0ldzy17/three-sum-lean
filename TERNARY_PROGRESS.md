# Ternary executable and exact 1.921 theorem

The complete theorem is
[`ThreeSum.solvedInTime_1921_1000`](Submission/ThreeSum/TernaryFinalSolver.lean),
with `Race.bound` exporting the exact rational `1921/1000`. The frozen-source
full build and axiom audit passed on 15 October 2026; see
[VERIFICATION.md](VERIFICATION.md). Earlier numerical certificates or individual
component builds do not replace those checks.

The original 1.962 solver, trusted statement, model/compiler sources, and
pinned dependencies retain their baseline contents. The historical official
acceptance belongs to commit `2b639655e07421b9ac743de9090459bab473a7c0`.

## Concrete proof chain

- [`TernaryConcreteProfile`](Submission/ThreeSum/TernaryConcreteProfile.lean)
  chooses fixed parameters for each magnitude exponent κ. Its simultaneous
  bounds cover the minor condition, collision cleanup, carry cost, and
  runtime margins. Parameters do not depend on the input values.
- The actual extension-field backend finds an irreducible polynomial and
  computes the finite row menu. Signed digits, endpoint tags, all carry
  occurrences, and original source/requester indices are carried through
  the literal dictionary and query constructors.
- The prefix loop executes admissibility checks, append hashing, wanted-row
  enumeration, collision scores, weighted tensor counts, and the selector.
  Its integer upper budgets do not require evaluating the enormous initial
  moment potential. Actual replay and commit receipts establish the selected
  rows and retained physical memory.
- [`TernaryColoredTerminalReceipt`](Submission/ThreeSum/TernaryColoredTerminalReceipt.lean)
  converts the executed loop invariant into canonical final hashes, committed
  original key arrays, bank/wanted metadata, the live host header, and zero
  paired potential. It also proves the actual collision counts are at most
  `n^(7483/10000)`. These facts are derived from the original normalized inputs.
- Zero potential yields bounded physical support after singleton cleanup.
  The implementation handles deleted source values with exact two-sum scans
  and membership searches. The retained groups use actual weighted moments
  and a finite moment detector, without a rank or decision oracle.
- [`TernaryColoredRuntimeCertificate`](Submission/ThreeSum/TernaryColoredRuntimeCertificate.lean)
  discharges the concrete runtime model and prices the actual global query
  maximum. It bounds the full preprocessing, initialization, selected-prefix
  execution, cleanup, and final reporting cost by `P.colorTime`.
- [`TernaryProfileFastExecution`](Submission/ThreeSum/TernaryProfileFastExecution.lean)
  connects the actual colored solver to the outer coloring program on the
  original input segment. The hybrid executable handles finite exceptional
  input sizes and the magnitude guard with actual fallback code.
- [`TernaryFinalSolver`](Submission/ThreeSum/TernaryFinalSolver.lean)
  supplies the complete solver, polynomial resource bound, and eventual
  exact time inequality for every κ, then transfers them to the unchanged
  benchmark statement. The decision concerns distinct original positions,
  including inputs with repeated values.

## Exponent and verification scope

[`TernaryProfileRuntime`](Submission/ThreeSum/TernaryProfileRuntime.lean)
proves `PowerBound` for the size-only per-color and outer budgets at
`19209/10000 = 1.9209`. The strict margin absorbs subpolynomial factors and
produces the final eventual bound `n^(1921/1000)`. A `PowerBound` exponent is
not a measured runtime or an assertion of an exact practical crossover.
The earlier principal ledger near 1.92028 is not the exported theorem's bound.

The final package records successful checks of its frozen source bytes:

```bash
python3 scripts/build_serial.py --aggregate
python3 scripts/audit_axioms.py
```

Current build receipt: [successful build receipt](verification/receipts/lean-1.921-20261015/build-results.json).
Current full-source audit receipt: [successful audit receipt](verification/receipts/lean-1.921-20261015/audit-results.json).
Verified proof-source commit: 74516abc0b3ea820c21a3e07a30d0dfe3f93816f.

A new hosted Comparator receipt and independent Nanoda result have not been
established. Historical baseline checks do not certify this revision. No
new official record, priority claim, or practical-speed claim follows from
this local development.
