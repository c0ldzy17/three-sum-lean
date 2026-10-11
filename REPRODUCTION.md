# Reproducing the submission

*Publication draft. Replace the repository/commit placeholders with the actual public immutable source before publication.*

The Lean 4.33.1 port has completed all 223 planned build chains, including
`Submission`. Its full-closure audit passed for 20,534 theorem declarations
across 667 submitted modules, with no submitted axioms and only `propext`,
`Classical.choice`, and `Quot.sound` in transitive proof dependencies. The build
finished on 11 October 2026 at 19:23:19 UTC, and the audit finished at 19:26:30
UTC. See [verification details](VERIFICATION.md) for exact receipt identities,
source hashes, and local-environment limitations.

The pinned local Comparator and Lean kernel accepted the complete exported
proof, and the separate target-axiom gate passed. The Nanoda-enabled gate also
passed, with explicit acceptance from both kernels and Comparator. All four
local gates passed for the same unchanged source snapshot; official hosted
acceptance remains pending. The commands below describe independent
reproduction with ordinary tools.

## Pinned inputs

Use ordinary Lean/Lake with `leanprover/lean4:v4.33.1`. The submitted project pins
Mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`; the included
`lake-manifest.json` fixes all nine dependency revisions and is copied from the
verifier’s pinned profile. Keep that manifest unchanged. `lake update` is not a
necessary reproduction step and may change dependency resolution.

Use a Unix-like shell with Git, Elan/Lake, Python 3, and curl available on
`PATH`; curl 7.81 or newer is recommended by the pinned Mathlib cache tool.

Start with a clean checkout of the published commit:

```bash
git clone PUBLIC_REPOSITORY_URL three-sum-proof
cd three-sum-proof
git checkout FULL_COMMIT_SHA
elan toolchain install leanprover/lean4:v4.33.1
lake env lean --version
```

The last command must report **Lean 4.33.1**, not a release candidate or a newer
version. The checked-in configuration and dependency manifest select the
required build; no custom compiler, workspace launcher, or proof-checker patch
is required. Python 3 runs the cache-root command below and the small serial
build helper.

Lake can emit two expected “manifest out of date” warnings saying that the
Mathlib Git URL and revision changed. The verifier's generated configuration
uses a URL ending in `.git` and the exact commit, while its unchanged manifest
records the URL without that suffix and the input tag `v4.33.1`. Both select the
locked commit shown above. These descriptor warnings do not change the locked
revision. Keep the pinned files unchanged, despite the warnings' generic
suggestion to run `lake update mathlib`.

## Dependency cache

The pinned Mathlib cache tool accepts an explicit list of module names and
fetches their transitive imported artifacts. `scripts/mathlib-cache-roots.txt`
contains the 135 roots selected for this proof, including the required Aesop
root. From the repository root:

```bash
python3 - <<'PY'
from pathlib import Path
import subprocess
roots = Path('scripts/mathlib-cache-roots.txt').read_text().split()
subprocess.run(['lake', 'exe', 'cache', 'get', *roots], check=True)
PY
```

Check the cache command's exit status and output, and preserve them with your
build record. Cache restoration does not verify the proof. The ordinary
broader `lake exe cache get` is also supported by the pinned cache tool, but
downloads substantially more than this proof’s selected closure. A source
build remains possible when caches are unavailable, with additional time and
storage requirements.

## Build the exact entry point

The verifier’s source planner groups the local modules into ordered dependency
chains. The supplied `scripts/source-chains.json` contains that plan. Build one
chain endpoint at a time to avoid starting a large number of independent Lean
processes:

```bash
python3 scripts/build_serial.py
```

The helper checks the exact `lean-toolchain`, `lakefile.toml`,
`lake-manifest.json`, and supplied chain-plan hashes, verifies the actual Lean
version, and uses ordinary `lake build` with `LEAN_NUM_THREADS=4`. It records
the source hashes, command, elapsed time, exit code, and log hash for each
attempt in `verification/builds/<timestamp>/results.json`. It stops at the first
failed chain and preserves its log.

The last chain ends at module `Submission`, whose `Submission.lean` exports:

```lean
theorem Race.bound :
    EndStatement.ThreeSum.SolvedInTime ((981 : Rat) / 500) := by
  exact ThreeSum.solvedInTime_981_500
```

After resolving an interrupted or failed build, resume at its **zero-based**
chain index, for example:

```bash
python3 scripts/build_serial.py --start-at 17
```

Earlier successful logs remain in their original run directory. A restart
records only its own attempted chains; it does not claim to have rechecked the
skipped prefix. Do not edit source files while a build is running. Changed
source inputs require a fresh build from chain zero before recording a final
clean verification result. Once dependency artifacts exist, explicitly select
the entry-point module with `lake build +Submission`; the `+` prefix selects
the module rather than the identically named library target.

## Check the theorem’s axiom dependencies

The supplied `VerifierAudit.lean` imports `Submission` and runs
`#print axioms Race.bound`. Execute it with the same pinned environment:

```bash
lake env lean -j1 -DautoImplicit=false VerifierAudit.lean
```

Inspect the actual printed transitive dependency list. Every reported axiom
must belong to:

```text
propext
Quot.sound
Classical.choice
```

An empty list or a subset is acceptable. `sorryAx`, a custom assumed theorem,
or an evaluation-backed proof axiom is not. The printing command itself does
not enforce a whitelist: the official verifier reads and checks this output,
and a local reviewer must apply the same policy. Preserve both its exit code
and the complete output; successful compilation alone does not perform this
policy check.

## Independent acceptance

For hosted submission, publish the exact sources in a public GitHub repository,
retain its complete commit SHA, and use the four-field issue route described
in [the README](README.md#submission-route). The form takes Problem `3sum`,
Repository URL, Commit SHA, and the reduced rational Bound `981/500`.

The official verifier compares `Race.bound` and its underlying definitions
against the trusted statement, accepts the proof in Lean’s kernel, and checks
the axiom whitelist. Its qualifying receipt establishes the site's **Lean
Verified** status. Nanoda runs subsequently: a resource timeout does not
invalidate an otherwise qualifying Lean-and-axiom result, while a confirmed
Nanoda rejection blocks the row and an ambiguous failure requires review.
See the [reviewed verifier policy](https://github.com/bigospeedrun/verifier/blob/025396033eede56e3af6e02ed2679ba828381bd5/README.md#what-lean-verified-means).

Preserve the official receipt and exact public source commit when reporting
hosted acceptance. The completed local build and full-closure audit should be
reported with their own receipt scope while the official checks are pending.
