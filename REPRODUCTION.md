# Reproducing the 1.921 submission

The frozen-source full build and axiom audit passed on 15 October 2026.
The historical 1.962 acceptance is documented separately in
[VERIFICATION.md](VERIFICATION.md).

## Pinned inputs

Use the ordinary Lean release `leanprover/lean4:v4.33.1`. Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474`; `lake-manifest.json` fixes the
remaining dependencies. Keep the toolchain, project configuration, dependency
manifest, trusted statement, and model/compiler sources unchanged.

Start with the immutable published source revision:

```bash
git clone https://github.com/c0ldzy17/three-sum-lean.git three-sum-proof
cd three-sum-proof
git checkout 74516abc0b3ea820c21a3e07a30d0dfe3f93816f
elan toolchain install leanprover/lean4:v4.33.1
lake env lean --version
```

The last command must report Lean 4.33.1. No custom compiler or proof-checker
patch is required. Python 3 runs the repository's verification helpers.

Lake may report the known Mathlib manifest descriptor warnings: the generated
configuration uses a `.git` URL and commit, while the unchanged manifest records
the corresponding URL and `v4.33.1` tag. Keep the pinned manifest unchanged;
`lake update` is not a reproduction step.

## Restore dependency artifacts

The pinned cache tool accepts the roots in
`scripts/mathlib-cache-roots.txt`, including their transitive dependencies:

```bash
python3 - <<'PY'
from pathlib import Path
import subprocess
roots = Path('scripts/mathlib-cache-roots.txt').read_text().split()
subprocess.run(['lake', 'exe', 'cache', 'get', *roots], check=True)
PY
```

Preserve the command's exit status and output. Restoring a cache does not
verify the submitted proof. Building dependencies from source is also possible.

## Build every submitted source

Freeze the source tree before checking. The planned roster is
1,198 modules in 754 dependency chains;
`scripts/source-chains.json` must cover the current `Submission.lean` and
`Submission/**/*.lean` exactly once.

```bash
python3 scripts/build_serial.py --aggregate
```

This invokes ordinary Lake with every planned module explicitly selected.
It checks the exact configuration/plan hashes, actual compiler version, source
coverage, and unchanged source hashes through completion. Results and logs go
to `verification/builds/<timestamp>/`. The final build receipt is
[successful build receipt](verification/receipts/lean-1.921-20261015/build-results.json), finished 2026-10-15T12:49:20.886263+00:00.

Serial endpoint checking is available as `python3 scripts/build_serial.py`.
A diagnostic restart may use `--start-at INDEX`, but a resumed run records only
its attempted suffix. Record a complete successful invocation from index zero
for final whole-source verification. Do not edit submitted sources during a
build or audit; changed sources require new checks.

The entry module can also be selected explicitly with `lake build +Submission`.
That targeted check does not replace the complete source build. Its
export is:

```lean
theorem Race.bound :
    EndStatement.ThreeSum.SolvedInTime ((1921 : Rat) / 1000) := by
  exact ThreeSum.solvedInTime_1921_1000
```

## Audit the exact source closure

After the complete build succeeds on the frozen sources:

```bash
python3 scripts/audit_axioms.py
```

The audit imports every submitted module, rejects submitted axiom
declarations, and checks every submitted declaration's transitive dependencies.
Only these standard axioms are permitted:

```text
propext
Classical.choice
Quot.sound
```

The final audit receipt is [successful audit receipt](verification/receipts/lean-1.921-20261015/audit-results.json), finished
2026-10-15T12:50:00.888793+00:00, with 43,763 declarations.
Inspect the successful marker, exit code, `Race.bound` type, and axiom output.
A `sorryAx`, custom assumed theorem, or evaluation-backed proof axiom fails
this policy.

For an additional targeted diagnostic:

```bash
lake env lean -j1 -DautoImplicit=false VerifierAudit.lean
```

That printing-only diagnostic does not replace the enforcing full-source audit.
The final source manifest is `SOURCE_MANIFEST.json`; its source identities and
record references must agree with the exact build and audit receipts.

## Independent official checking

The intended issue fields are Problem `3sum`, Repository URL, immutable full
Commit SHA, and reduced rational Bound `1921/1000`, through the verifier's
[submission form](https://github.com/bigospeedrun/verifier/issues/new/choose).
See the previously reviewed
[submission guide](https://github.com/bigospeedrun/verifier/blob/025396033eede56e3af6e02ed2679ba828381bd5/docs/direct-submissions.md)
for that route.

No new official acceptance or independent Nanoda result is established by
local compilation and axiom auditing. Report any subsequent hosted receipt
with its own exact source commit and scope. The baseline's official 1.962
receipt does not certify the 1.921 revision.
