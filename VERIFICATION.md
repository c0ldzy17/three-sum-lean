# Verification record

## Exact 1.921 result

```lean
theorem Race.bound :
    EndStatement.ThreeSum.SolvedInTime ((1921 : Rat) / 1000) := by
  exact ThreeSum.solvedInTime_1921_1000
```

The exact rational target is **1921/1000 = 1.921**. The complete theorem is
[`ThreeSum.solvedInTime_1921_1000`](Submission/ThreeSum/TernaryFinalSolver.lean).
It supplies a concrete uniform program for every fixed original-input
magnitude exponent κ. The target remains the original distinct-position 3SUM
statement in [Submission/EndStatement.lean](Submission/EndStatement.lean).

**The final frozen-source build and full-source axiom audit passed.** The
receipts below cover the identical 1,198-module source snapshot, including the
exported `Race.bound` at `1921/1000`.

| Current 1.921 check | Exact result / evidence |
|---|---|
| Verified proof-source commit | 74516abc0b3ea820c21a3e07a30d0dfe3f93816f |
| Submitted source roster | 1,198 modules, 754 chains |
| Canonical proof-source digest | d80a4843eecc48b2942f6b312e4c0229a722c4d733f3f61afa5272dadc8555cc |
| Complete source build | [successful build receipt](verification/receipts/lean-1.921-20261015/build-results.json) |
| Build completion UTC | 2026-10-15T12:49:20.886263+00:00 |
| Build log SHA-256 | c5264c659592cc704d6f25a833f631347f4127e2aeeca315d14549c09464fa14 |
| Full-source axiom audit | [successful audit receipt](verification/receipts/lean-1.921-20261015/audit-results.json) |
| Audit completion UTC | 2026-10-15T12:50:00.888793+00:00 |
| Audited submitted declarations | 43,763 |
| Audit log SHA-256 | af0e87fd7220169e7cae52cd54aaf9d3a8cb129e0e526ee71fbcd08915cde7d2 |
| `Race.bound` transitive axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Hosted Comparator / official qualifying receipt | Not established for this revision |
| Independent Nanoda acceptance | Not established for this revision |

Run the commands in [REPRODUCTION.md](REPRODUCTION.md). The complete build
checks the pinned configuration, full source roster, actual Lean version,
and source stability. The full-source audit rejects submitted axioms and
permits only `propext`, `Classical.choice`, and `Quot.sound` in transitive
proof dependencies. Declaration counts describe this exact source closure
and Lean release; they are not counts of new mathematical discoveries.

The manifest records a completed local check only when its successful,
nonprovisional receipt matches all current submitted source hashes. Source
changes invalidate the applicability of earlier receipts. Local build/audit
receipts are distinct from hosted Comparator and independent-kernel results.

## Preserved statement and toolchain

| Input | Exact identity |
|---|---|
| Lean | `leanprover/lean4:v4.33.1` |
| Mathlib | `0df444a360eaa60ab8c11dca51a86af692955474` |
| Dependency manifest SHA-256 | `484af05025301c3920dfeb644f6dbb7f02b05f596bf48831c9324e383694db25` |
| Trusted statement SHA-256 | `4291e3f05781cea42f9d672ff73ceac1f6d1a0c3021038e94372fa8f7e1ad987` |
| Historical reviewed verifier commit | `025396033eede56e3af6e02ed2679ba828381bd5` |

The trusted benchmark, every original proof/model/compiler source, and pinned
dependency configuration retain the baseline bytes. The change to
`Submission.lean` selects the new complete solver and changes the exported
rational exponent. It does not change the task or machine semantics.

## Historical officially accepted 1.962 baseline

Commit `2b639655e07421b9ac743de9090459bab473a7c0` exported `981/500 = 1.962`
through `ThreeSum.solvedInTime_981_500`. Its
[official hosted receipt](https://github.com/bigospeedrun/verifier/actions/runs/38175066816)
applies to that baseline, not to the new 1.921 source revision.

The historical local records on 11 October 2026 included:

| Baseline check | Historical result |
|---|---|
| Complete source build | 223 chains, 667 modules; finished 19:23:19 UTC |
| Full-source axiom audit | 27,199 submitted declarations, including 20,534 theorem declarations; finished 19:26:30 UTC |
| Comparator and Lean kernel | Exit 0; 879.265 seconds; `preflight_lean_20261011T192943Z.json` |
| Separate target-axiom gate | Exit 0; 8.806 seconds; `preflight_audit_20261011T194431Z.json` |
| Comparator, Nanoda and Lean kernels | Exit 0; 1,298.12 seconds; `preflight_nanoda_20261011T194454Z.json` |

The historical full-audit log hash was
`e5a5ebfc637d21939b3de7fd5611946b49999f8a864e4a1e96beb5ae60d23b62`.
The Comparator, target-axiom and Nanoda log hashes respectively were:

```text
6c6c978fcb746ffe3eddf39f93ff115f15510a6bc5a900c9ce28d0616275bd82
4dc3bc531de140cd693871031402ca9cf178053f360aec3cc612d488639b09dd
ab2bc2c5c0f3492cb0e8d258786740b437b7a79e43508f36caa834c073fdf7d7
```

These identities preserve provenance and do not transfer verification to new
sources. No new official record, hosted acceptance, independent-kernel result,
or practical runtime claim is made by this document.
