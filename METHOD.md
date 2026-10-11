# Deterministic 3SUM in O(n^1.962): method and proof

*Source and verification snapshot: 11 October 2026.*

## Result and verification status

The completed original formalization proves

```lean
ThreeSum.solvedInTime_981_500 :
  EndStatement.ThreeSum.SolvedInTime (981 / 500 : Rat)
```

This is deterministic decision 3SUM on three **distinct input positions**. Equal values at different positions are allowed. For every fixed natural number κ, the theorem supplies a finite word-RAM program for inputs with absolute values at most n^κ. Its correctness is uniform over the required input sizes and every sufficiently large word width. The benchmark’s exact runtime condition is `∃ K, ∀ n ≥ 2, T(n)^500 ≤ K * n^981`. See [the unchanged statement](Submission/EndStatement.lean) and [the final proof](Submission/ThreeSum/FinalSolver.lean).

The submission compiles on the verifier's pinned **Lean 4.33.1** and Mathlib. All 223 dependency chains, ending at `Submission`, completed successfully. The full local axiom audit checked **20,534 theorem declarations across all 667 submitted modules**, including private auxiliaries, permitting only `propext`, `Classical.choice`, and `Quot.sound`; no submitted axiom declarations were found among the 27,199 submitted declarations. The original proof sources are preserved, and the version port changes imports and proof compatibility without changing theorem statements. The pinned local Comparator and Lean kernel accepted the complete exported proof; the separate target-axiom gate and the Nanoda-enabled gate also passed. **All four local verification gates passed.** Big O Speedrun's hosted acceptance remains pending. See [the verification record](VERIFICATION.md) for the exact source snapshot and completed gate results.

## Algorithm

### 1. Preserve the original decision problem

A deterministic family of O(log² n) colorings separates every triple of distinct positions in at least one coloring. Each call asks whether `a + b = c`, taking the third color’s values with reversed signs. Sorting and normalization preserve the existence of witnesses. Consecutive bands let the algorithm retain only band triples whose value intervals could contain a solution. The proof preserves the relationship to the original positions throughout. See [ColorParameters](Submission/ThreeSum/ColorParameters.lean), [LightEncodedColorNormalize](Submission/ThreeSum/LightEncodedColorNormalize.lean), and [BandRawAColorOriginal](Submission/ThreeSum/BandRawAColorOriginal.lean).

### 2. Filter arithmetic candidates deterministically

For a current modulus, exact residue histograms and cyclic correlations count candidate equations. A weighted zero test assigns weight zero to genuine equations and positive weight to bounded nonzero differences. A prime chain chooses a minimizing prime at each step, contracting the false-candidate weight while retaining every true solution. Ordinary Karatsuba multiplication supplies the correlations; the construction needs no assumed matrix-multiplication exponent.

Two formalization repairs matter. The executable prime pool is **(y, 4y]**, where the proved Chebyshev bounds supply enough candidates; the preliminary write-up used [y, 2y]. Also, the same pool can serve the auxiliary zero tests even when factors repeat in the main modulus. For an auxiliary prime p, the joint divisibility test uses **q if p divides q, otherwise q·p**. Always using q·p would require an additional coprimality hypothesis. Both the identity and its executable branch are proved. See [PrimeDensity](Submission/ThreeSum/PrimeDensity.lean), [WeightedModuli](Submission/ThreeSum/WeightedModuli.lean), [LightWeightedScore](Submission/ThreeSum/LightWeightedScore.lean), and [LightBandPrimeConstruction](Submission/ThreeSum/LightBandPrimeConstruction.lean).

### 3. Represent residue pairs by disjoint subsets

Small blocks use two balanced subset endpoints whose disjoint union is an output key. One-hot linear hashes over a finite prime field connect those endpoints to residue pairs. Large hash buckets are trimmed **independently on the two sides**, so the surviving representation remains a product of two endpoint conditions.

A finite greedy search constructs a cover of every local residue pair. Small block size makes this exhaustive local construction subpolynomial in n. Positional composition combines the local covers; the carry argument proves global coverage and a bound on representation multiplicity. It never needs to enumerate all pairs of global residues. See [LocalHashMoments](Submission/ThreeSum/LocalHashMoments.lean), [LightLocalCoverBuild](Submission/ThreeSum/LightLocalCoverBuild.lean), [GlobalEncoding](Submission/ThreeSum/GlobalEncoding.lean), and [BlockEncoding](Submission/ThreeSum/BlockEncoding.lean).

### 4. Share transforms and query sparse subsets

The endpoint arrays contain original bucket populations, repeated at their allowed subset coordinates. Partial zeta transforms retain intermediate stages, making the same stored tables useful after different coordinate prefixes have been fixed.

Möbius cancellation turns products of these transforms into exact counts of disjoint endpoint pairs. Sparse suffix queries divide the sum into explicitly visited leaves and precomputed boxes, trading preprocessing against query time. The cost proof charges the tables for **all relevant prefix partitions**, including their construction and addressing. See [Subset](Submission/ThreeSum/Subset.lean), [LightZetaStages](Submission/ThreeSum/LightZetaStages.lean), [SparseBoxes](Submission/ThreeSum/SparseBoxes.lean), and [LightSparseQuery](Submission/ThreeSum/LightSparseQuery.lean).

### 5. Balance queries and control reporting

An exact cyclic correlation selects a common offset that bounds the number of wanted output records. Records retain their original input incidence and representation multiplicity, rather than collapsing distinct values or occurrences merely because their modular keys coincide.

The scan maintains accumulated represented mass. If it exceeds the proved upper bound on all false represented triples, the algorithm can soundly answer YES. Otherwise positive-prefix reporting refines surviving candidates block by block and eventually checks original values. Every genuine solution has a retained path; the mass bound controls work on YES inputs as well as NO inputs. See [LightOriginalOffset](Submission/ThreeSum/LightOriginalOffset.lean), [RawReporting](Submission/ThreeSum/RawReporting.lean), and [LightReportingWantedScanStored](Submission/ThreeSum/LightReportingWantedScanStored.lean).

## Where the exponent comes from

The parameter choice uses a block expansion factor of 256, representation scale D = n^(1/5+o(1)), band shift −1/20, and terminal reporting fraction 13/20. An integer-computable cubic switch balances box construction against suffix-query work. Exact inequalities establish a principal certificate exponent

```text
9809107 / 5000000 = 1.9618214 < 1.962.
```

The strict gap absorbs separately proved subpolynomial overheads. This includes local enumeration, prime selection, transforms, prefix catalogs, reporting, and the coloring family. It is not enough to check those numerical inequalities alone: the executable cost proofs connect actual operations to the budget. See [Parameters](Submission/ThreeSum/Parameters.lean), [SharedTraversalCostBounds](Submission/ThreeSum/SharedTraversalCostBounds.lean), and [ThreeSumHybridCosts](Submission/ThreeSum/ThreeSumHybridCosts.lean).

## From algorithm to the machine theorem

[LightEncodedColorReportingPipeline](Submission/ThreeSum/LightEncodedColorReportingPipeline.lean) constructs the stored data from the original input. [LightThreeSumColor](Submission/ThreeSum/LightThreeSumColor.lean) connects that prelude to the actual reporting scan. [LightThreeSumConcreteFast](Submission/ThreeSum/LightThreeSumConcreteFast.lean) runs the full coloring family. [LightThreeSumHybrid](Submission/ThreeSum/LightThreeSumHybrid.lean) adds the verified fallback for exceptional sizes and proves the complete task contract and polynomial resource requirements.

[ThreeSumHybridEndBridge](Submission/ThreeSum/ThreeSumHybridEndBridge.lean) then applies the inherited verified compiler and runtime conversion to the trusted word-RAM statement. Arithmetic bounds, memory addresses, call depth, and instruction costs are included. The final theorem assumes no unproved solver callback. Practical runtime, hidden constants, and crossover sizes have not been measured.

## Attribution and novelty

The research notes identify the proposed contribution as the **composition** of repeated histogram layouts, uniformly constructed trimmed covers, balanced output keys, and fully charged prefix reporting that yields this bound. Independent review should assess its novelty; the classical ingredients are not claimed as new.

Credits include Josh Alman and Virginia Vassilevska Williams for the underlying subquadratic-3SUM framework and sparse-query construction; Björklund, Husfeldt, Kaski, and Koivisto for classical fast subset convolution; Swapnil Jain’s `threesum-derand` work for prime-chain minimization and weighted zero testing; and Kassabov, Landsberg, Souza, and Speegle’s overlapping-input tensor work for an initial research motivation.

The formalization reuses Anthropic, PBC’s word-RAM specification, program logic, compiler, and supporting proofs, obtained through Jihoon Hyun’s **ImprovedExponents** source tree at commit `0725f2477587d67212936777b8a264c9793ac7bb`. It also depends on Lean, Mathlib, and their pinned dependencies. Original copyright and Apache-2.0 notices are preserved. Those earlier mathematical and formalization contributions should accompany every public presentation of this result.
