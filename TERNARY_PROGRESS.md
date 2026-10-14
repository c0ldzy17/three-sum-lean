# Ternary construction targeting 1.921

The branch preserves the officially verified 1.962 submission at commit
`2b639655e07421b9ac743de9090459bab473a7c0` and adds Lean proofs and actual
Light-language procedures for a different, compressed ternary construction.
**It does not yet prove `EndStatement.ThreeSum.SolvedInTime (1921/1000)`.**
`Submission.lean` continues to export the complete `981/500` theorem. The
trusted `EndStatement.lean`, old solver, toolchain, and dependency revisions
retain their baseline contents.

## What is proved

- `TernaryParameters` proves all five principal real-valued ledger terms
  strictly below `1.9203`, using exact rational logarithm bounds.
- `TernaryShortLedger` proves the ledger plus explicit fixed-depth scoring
  overhead strictly below `1.9205 < 1.921`. It charges a representation
  factor at all `D+1` occurrences, with `D=100000`, exponent `10^-10`, a
  conservative fourth power of the prime window, and a `0.0001` reserve.
  These are numerical certificates, not an executable's time theorem.
- `TernaryJointType` proves the forced six-cell joint type of genuine
  coordinatewise ternary addition. The cover modules prove actual fixed-type
  projection-fiber caps, paired-rank counting, and the tagged raw high moment.
- `TernaryBankEnumeration` and `TernaryNearBankEnumeration` identify the
  deterministic pruned enumeration with the actual finite rank bank and
  query neighborhood, including their Gibbs cardinality bounds.
- `TernaryTransform` and `TernaryConvolution` connect coordinate passes to
  binomial transforms and ordinary additive convolution. `TernaryCodeSemantics`
  connects canonical two-bit address operations to trit coordinate updates.
- `TernaryPhysicalSources` preserves original record multiplicities:
  convolution of histograms is exactly the count of indexed record pairs.
- `LightTernaryEnumerationSetup` is a closed program that constructs its
  own power table and enumerates the compact bank. The near enumerator,
  lookup, metadata, forward/inverse passes, product, exact division, and
  Euler memo modules specify actual programs with execution-time and
  memory-preservation contracts. The numeric address width is `2N`; the
  enumerators visit only admitted ternary states.
- `LightFiniteTable` initializes any fixed finite dictionary from literal
  program instructions. It does not assume input-dependent advice.
- `TernaryResidueScore` and `TernaryResidueChain` retain positive represented
  false-triple scores and the representation loss during prime selection.
  `TernaryGlobalEncoding` supplies the signed radix bridge for arbitrary
  original records. `TernaryHybridCore` and `TernaryEndBridge` transfer a
  concrete fast solver, once supplied, to the unchanged benchmark statement.

## Remaining obligations

The final fast program has not been supplied to the hybrid/end bridge.
Its original-input source and wanted-output dictionary joins, selected-prime
scoring calls, complete bounded query/reporting engine, and complete global
resource/time contracts must be assembled and proved. Individual execution
contracts still state their physical layout, source support, metadata, and
arithmetic bounds; a final host must discharge those conditions from its
actual preceding procedures.

The finite cover, literal output-fiber bounds, and representation-overhead
parameter selection are proved. The principal running-time port still needs
the actual typed-output cardinality rate corresponding to `Hpi`, rather than
only a smaller combinatorial lower bound. The wanted-output constructor must
enumerate per-target radix fibers; enumerating the complete global output
dictionary would retain an `n^2` charge.

The restricted-coordinate Euler law is proved in `TernaryPartialEuler`.
Endpoint-prefix reporting still needs its pair-specific inverse-product stages
and cumulative cost proof; one unrestricted count does not pay for those
stages. The actual frozen query has proved leaves and recursive branch
contracts, but its complete execution induction remains open. No benchmark
theorem may be obtained by treating an unimplemented query or score as one
machine operation.

The accepted binary executable's parameters alone cannot yield 1.921: its
source-loading, box, and recursive-query charges prevent that substitution.
The ternary work therefore preserves the old theorem instead of changing its
rational exponent without a new executable proof.

## Reproduction

Use the pinned Lean 4.33.1 and unchanged dependency manifest. After restoring
the dependency cache, check every explicitly planned submitted module with:

```bash
python3 scripts/build_serial.py --aggregate
python3 scripts/audit_axioms.py
```

The aggregate mode checks the same exact pins, full source-plan coverage,
compiler version, and source freeze as serial mode, and selects every module
explicitly in one Lake invocation. The audit imports every submitted module,
rejects submitted axioms, and checks all transitive dependencies against
`propext`, `Classical.choice`, and `Quot.sound`.

Receipts record the exact checked source hashes. The original hosted receipt
does not certify these additions; local compilation and axiom-policy checks
are not a new hosted Comparator or Nanoda receipt.
