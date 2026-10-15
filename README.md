# Deterministic 3SUM in O(n^1.921), formalized in Lean

The entry point exports the exact rational bound **1921/1000 = 1.921**:

```lean
theorem Race.bound :
    EndStatement.ThreeSum.SolvedInTime ((1921 : Rat) / 1000) := by
  exact ThreeSum.solvedInTime_1921_1000
```

The frozen-source full build and axiom audit both passed on 15 October 2026. See
[verification details](VERIFICATION.md).

The task asks whether three distinct input positions sum to zero. Equal values
at different positions are allowed. For every fixed polynomial bound on the
original integers, the theorem supplies a uniform finite program in the
unchanged benchmark word-RAM model, with correctness and the required eventual
running-time inequality.

The complete theorem is
[`ThreeSum.solvedInTime_1921_1000`](Submission/ThreeSum/TernaryFinalSolver.lean).
It instantiates the concrete parameter profile, executed colored solver,
outer coloring program, and hybrid fallback for every magnitude exponent κ.
The trusted [benchmark statement](Submission/EndStatement.lean), original
model/compiler sources, and pinned dependencies retain their baseline bytes.

The implementation charges preprocessing, finite-field construction, selected
rows, weighted counting, collision cleanup, moment reporting, and control flow.
Its size-only per-color and outer runtime bounds have `PowerBound` exponent
`19209/10000 = 1.9209`; the strict margin yields the final exact 1.921 bound.
This is an asymptotic result. No practical crossover or measured speedup is
claimed. See [the proof map](TERNARY_PROGRESS.md) and [attribution](NOTICE).

## Verification and historical provenance

| Current 1.921 source | Status |
|---|---|
| Verified proof-source commit | 74516abc0b3ea820c21a3e07a30d0dfe3f93816f |
| Complete submitted-source build | [successful build receipt](verification/receipts/lean-1.921-20261015/build-results.json) |
| Full-source axiom audit | [successful audit receipt](verification/receipts/lean-1.921-20261015/audit-results.json) |
| Hosted Comparator / qualifying official acceptance | Not established for this revision |
| Independent Nanoda acceptance | Not established for this revision |

The officially accepted **1.962** baseline is commit
`2b639655e07421b9ac743de9090459bab473a7c0`; its
[hosted verifier receipt](https://github.com/bigospeedrun/verifier/actions/runs/38175066816)
is historical evidence for that baseline. Its local and hosted checks do not
certify the new 1.921 sources. No new record or official verification status
is asserted here.

## Reproduction

Use Lean `leanprover/lean4:v4.33.1`, Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`, and the unchanged
`lake-manifest.json`. After restoring dependencies, run from the repository root:

```bash
python3 scripts/build_serial.py --aggregate
python3 scripts/audit_axioms.py
```

The build plan must cover every current submitted module exactly once. The
scripts record exact source hashes and reject source changes during checking.
The audit rejects submitted axioms and permits only `propext`,
`Classical.choice`, and `Quot.sound` as transitive axioms. See
[REPRODUCTION.md](REPRODUCTION.md) for the full procedure.

## Submission route and attribution

The intended submission bound is `1921/1000`, entry point `Race.bound`, problem
`3sum`. Publish and submit only the immutable source revision whose checks are
reported, and retain any resulting official receipt separately from local
checks. The repository-and-issue route and reviewed verifier policy are linked
in [REPRODUCTION.md](REPRODUCTION.md).

Existing credits and license notices are preserved. The construction builds on
work credited in [METHOD.md](METHOD.md) and [NOTICE](NOTICE), including Alman
and Vassilevska Williams; Björklund, Husfeldt, Kaski, and Koivisto; and Swapnil
Jain. The inherited word-RAM statement, program logic, and compiler originate
in Anthropic's formalization, obtained through Jihoon Hyun's
ImprovedExponents tree. Lean, Mathlib, and their dependencies supply the proof
infrastructure. Successful checking alone establishes no independent-priority
claim.
