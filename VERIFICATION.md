# Verification record

## Exact result

The submission exports:

```lean
theorem Race.bound :
    EndStatement.ThreeSum.SolvedInTime ((981 : Rat) / 500) := by
  exact ThreeSum.solvedInTime_981_500
```

The exact reduced exponent is **981/500 = 1.962**. The trusted statement is
[Submission/EndStatement.lean](Submission/EndStatement.lean); the complete proof
is [Submission/ThreeSum/FinalSolver.lean](Submission/ThreeSum/FinalSolver.lean).
See [METHOD.md](METHOD.md) for the algorithm and the connection to the specified
word-RAM decision problem, and [REPRODUCTION.md](REPRODUCTION.md) for build commands.

## Completed local checks

All times in this record are UTC on **11 October 2026**.

| Check | Actual result | Evidence |
|---|---|---|
| Complete Lean 4.33.1 source build | Passed all 223 planned dependency chains, including `Submission`; final completion 19:23:19 | Final central `Submission` log and receipt; all 223 chains were also replayed successfully in both Comparator logs |
| Full submitted-module axiom audit | Passed at 19:26:30; 20,534 theorem declarations across 667 exact submitted modules; 27,199 submitted declarations in total | `full_axiom_audit_20261011T192354Z.json` and its complete log |
| Pinned Comparator, Lean kernel | Passed; explicit Lean kernel and final Comparator acceptance; exit 0 in 879.265 seconds | `preflight_lean_20261011T192943Z.json` and its complete log |
| Separate `Race.bound` axiom gate | Passed; exactly the three permitted axioms; exit 0 in 8.806 seconds | `preflight_audit_20261011T194431Z.json` and its complete log |
| Pinned Comparator, Nanoda and Lean kernels | Passed; explicit acceptance from Nanoda, Lean, and Comparator; exit 0 in 1,298.12 seconds | `preflight_nanoda_20261011T194454Z.json` and its complete log |
| Fresh source/package review | Passed all 17 checks; no source drift from the frozen controls | `source_checks_20261011T193426343965Z/source-checks.json` |
| Port and original-source review | 621 modules unchanged after import normalization, 45 compatibility-edited; the textual review flagged no changes to theorem headers, definition bodies, added/removed declarations, or notice lines | `port_delta_20261011T193426343398Z/port-delta.json` and per-file diffs |

The full audit rejects submitted axiom declarations and checks every submitted
theorem's transitive axiom dependencies, including private auxiliaries. It
found only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`.
Both `Race.bound` and `ThreeSum.solvedInTime_981_500` have exactly that list.
The audit exited with code 0 in 156.066 seconds, with no source changes during
the run. Its complete log has SHA-256
`e5a5ebfc637d21939b3de7fd5611946b49999f8a864e4a1e96beb5ae60d23b62`.

The completed Comparator run printed both `Lean default kernel accepts the
solution` and `Your solution is okay!`. Its complete log has SHA-256
`6c6c978fcb746ffe3eddf39f93ff115f15510a6bc5a900c9ce28d0616275bd82`.
The separate target-axiom gate log has SHA-256
`4dc3bc531de140cd693871031402ca9cf178053f360aec3cc612d488639b09dd`.
The Nanoda-enabled run printed `Nanoda kernel accepts the solution`, then
`Lean default kernel accepts the solution`, and finally `Your solution is okay!`.
Its complete log has SHA-256
`ab2bc2c5c0f3492cb0e8d258786740b437b7a79e43508f36caa834c073fdf7d7`.
All three preflight runs recorded unchanged source files, prepared controls,
trusted staged controls, and local adapter identities. Together with the
full submitted-module audit, **all four required local gates passed** for the
same frozen source snapshot. None timed out or reported a rejection.

The theorem count is a declaration count for this exact Lean version and
module closure; it is not a count of newly invented mathematical results.
The port's one source-context adjustment raises a local elaboration heartbeat
limit. It changes neither the theorem statement nor the kernel's proof rules.

## Source and checker identities

The frozen submission contains **667 admitted Lean source files**, totaling
**4,902,788 bytes**. These are `Submission.lean` and the additional sources under
`Submission/`. The original verified project's source bytes are preserved.
The source/evidence archive includes a per-file path, size, and SHA-256 manifest.

| Input | Exact identity |
|---|---|
| Verifier repository commit | `025396033eede56e3af6e02ed2679ba828381bd5` |
| Lean toolchain | `leanprover/lean4:v4.33.1` |
| Mathlib commit | `0df444a360eaa60ab8c11dca51a86af692955474` |
| Dependency manifest SHA-256 | `484af05025301c3920dfeb644f6dbb7f02b05f596bf48831c9324e383694db25` |
| Trusted statement SHA-256 | `4291e3f05781cea42f9d672ff73ceac1f6d1a0c3021038e94372fa8f7e1ad987` |
| Prepared source/control manifest SHA-256 | `2987de200763fd26bc39a891ee6364d8184b0017e824d75e72b171e20b582fbf` |
| Comparator commit | `3927ad383f208ae977c340a91c48ac9b497d2097` |
| lean4export commit | `15f6055e299ad5b89345e533cc2192f4cc00f659` |
| Nanoda commit | `3a2407216ee84a75f9e1aead6803d0578be06ae7` |
| landrun commit | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

Fresh public retrievals at 19:25 UTC confirmed the verifier commit and these
requirements. All nine actual dependency Git HEADs match the pinned manifest.
The unchanged submission controller's numeric gate returned `true` for
`981/500`, a strict improvement over the then-leading listed claim
`997891/500000 = 1.995782`. This is a dated eligibility observation, not a claim
about exhaustive off-board priority. The immutable board snapshot is
[site commit 41cf0881b439cbd583f03ca40cf45df05e5038a6](https://github.com/bigospeedrun/site/blob/41cf0881b439cbd583f03ca40cf45df05e5038a6/data/3sum.json).

## Local checking and official acceptance

The actual pinned checker binaries, target generator, and axiom/verdict policy
are used for local preflight. Local launchers preserve executable-path and
dependency-path environment settings required by this workspace. Their source
and build identities are retained as evidence. They do not modify Lean's
kernel, the proof terms, the comparison target, or the permitted-axiom policy.
The ordinary public reproduction procedure uses the standard Lean distribution.

This local environment does not reproduce the hosted runner's complete outer
filesystem, network, and cgroup isolation. Recorded child-process resource
figures are local Linux measurements, not measurements of the hosted runner.
The generated verifier-owned challenge is excluded from the public sources;
its pinned hash and generating source are retained in the evidence.

**Official Big O Speedrun acceptance remains pending.** No public repository
commit or official submission receipt is established by this package. The
verifier commit above identifies the checker; it is not the proof's eventual
public source commit. Publish the public source tree, submit its actual full
commit SHA through the repository-and-issue route, and retain the hosted
receipt before using the site's `Lean Verified` label.

The accompanying archive preserves source bytes and verification evidence.
It does not capture running processes or subagent state, and it does not bundle
all regenerable third-party runtime and dependency installations.
