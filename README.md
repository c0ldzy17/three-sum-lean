# Deterministic 3SUM in O(n^1.962), formalized in Lean

**This branch develops a ternary construction targeting 1.921. The complete
benchmark theorem still has exponent 1.962.** The new numerical certificates
and executable components do not yet constitute an integrated faster solver.
See [the exact progress and remaining obligations](TERNARY_PROGRESS.md).

This project proves the exact benchmark statement

```lean
theorem Race.bound :
    EndStatement.ThreeSum.SolvedInTime ((981 : Rat) / 500)
```

The decision problem asks whether **three distinct input positions** sum to
zero; equal values at different positions are allowed. For every fixed
polynomial bound on the input integers, the theorem supplies a uniform finite
program for the benchmark's fixed-width word-RAM model, with correctness and
the exact running-time inequality required by that model.

The entry point is [Submission.lean](Submission.lean). Its proof is
[ThreeSum.solvedInTime_981_500](Submission/ThreeSum/FinalSolver.lean), and the
[trusted statement](Submission/EndStatement.lean) is preserved byte-for-byte.

## Verification status

**The complete Lean 4.33.1 submission port has built successfully.** All 223
planned dependency chains completed, including the `Submission` entry point,
on 11 October 2026 at 19:23:19 UTC.

The subsequent full-closure axiom audit passed at 19:26:30 UTC. It examined
**20,534 theorem declarations across the exact 667 submitted modules**, covering
27,199 submitted declarations in total. There were no submitted axioms, and
the transitive proof dependencies used only `propext`, `Classical.choice`, and
`Quot.sound`. Both `Race.bound` and `ThreeSum.solvedInTime_981_500` were included.
The audit recorded unchanged source hashes throughout.

The pinned local Comparator accepted the theorem against the trusted statement,
and Lean's kernel accepted the exported proof. That gate passed in 879.265
seconds. The separate `Race.bound` axiom gate also passed, with exactly the
three permitted axioms. The Nanoda-enabled gate passed in 1,298.12 seconds,
with explicit Nanoda, Lean kernel, and final Comparator acceptance. All four
local gates passed for the same unchanged source snapshot. See
[verification details](VERIFICATION.md) for exact
receipt identities and local-environment limitations. The baseline release
at commit `2b639655e07421b9ac743de9090459bab473a7c0` subsequently received
[official verifier acceptance](https://github.com/bigospeedrun/verifier/actions/runs/38175066816).
That receipt applies to the baseline, not to the new ternary development.

## Method

Read [the method and proof map](METHOD.md) for the construction, exponent
accounting, source-module links, and detailed attribution.

The construction combines deterministic prime filtering, independently trimmed
subset representations, finite local covers, shared partial zeta transforms,
balanced output queries, and a fully charged reporting hierarchy. The proof
connects these components to actual finite programs, including preprocessing,
overflow bounds, memory addressing, control flow, and instruction costs.

The exact exponent certificate has a strict margin below 1.962, which absorbs
the separately proved subpolynomial overheads. This is an asymptotic theorem;
no practical runtime or crossover measurement is claimed.

## Submission route

The source closure contains **667 Lean files**. It is prepared for the public
repository plus structured-issue route in
[bigospeedrun/verifier](https://github.com/bigospeedrun/verifier). The issue's
bound is the reduced rational `981/500`, and the entry point is `Race.bound`.
The official verifier supplies its own configuration and dependencies and
stages only `Submission.lean` and the additional Lean sources under
`Submission/`.

To submit the locally verified package:

1. Publish this source tree in a public GitHub repository and retain the full
   40-character commit SHA of the submitted version.
2. Open the verifier's [submission issue form](https://github.com/bigospeedrun/verifier/issues/new/choose).
   Fill its four fields with Problem `3sum`, the public Repository URL, the
   complete Commit SHA, and Bound `981/500`. Use only the form's four one-line
   values in the issue body; put technical explanations in the repository
   documentation.
3. Retain the official issue and receipt links, and report the source commit
   alongside the result. Use the site's **Lean Verified** label only after its
   qualifying official receipt exists.

The verifier rechecks record eligibility before starting a proof job. See its
[issue submission guide](https://github.com/bigospeedrun/verifier/blob/025396033eede56e3af6e02ed2679ba828381bd5/docs/direct-submissions.md)
for the reviewed route and evidence policy.

The accompanying development configuration pins:

- Lean: `leanprover/lean4:v4.33.1`.
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- The full dependency manifest supplied by the reviewed verifier profile.

See [the reproduction instructions](REPRODUCTION.md) and
[the serial build helper](scripts/build_serial.py).

## Attribution

The mathematical construction uses and adapts work of Alman and Vassilevska
Williams; Björklund, Husfeldt, Kaski, and Koivisto; and Swapnil Jain, among
other credited predecessors. The inherited word-RAM specification, program
logic, compiler, and supporting proofs originate in Anthropic's formalization,
obtained through Jihoon Hyun's ImprovedExponents tree. Lean, Mathlib, and their
dependencies provide the foundational libraries and checking infrastructure.

Original source credits and license notices are retained. See [NOTICE](NOTICE)
for the scope of the inherited license and source provenance. No independent
priority or practical-speed claim follows merely from successful proof
checking.
