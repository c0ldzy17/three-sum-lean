import Submission.ThreeSum.TernaryHybridCosts

/-! The public-model boundary for the ternary solver. All statements consume
an actual executable contract, its polynomial needs, and its own time bound.
The original 3SUM task, compiler, and EndStatement are imported unchanged.
This file does not assert that the remaining fast executable is complete. -/
noncomputable section
namespace ThreeSum.TernarySolverEndBridge
open Light Filter StageBounds
open scoped Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000

def target : ℚ := 1921/1000
def targetExponent : ℝ := 1921/1000

theorem target_cast : (target:ℝ)=targetExponent := by norm_num [target,targetExponent]

theorem realized_of_solves {P : Program} {p : ℕ} {T : ℕ→ ℕ→ ℕ} {need : ℕ→ ℕ→ Need}
    (hs : Solves s3Task P p T need) (hp : PolyNeed need) :
    ThreeSumApsp.WordRam.Realized EndStatement.ThreeSum (timeUpTo T) :=
  TernaryEndBridge.realized_of_solves hs hp

theorem solvedAt_of_solves {κ : ℕ} {P : Program} {p : ℕ}
    {T : ℕ→ ℕ→ ℕ} {need : ℕ→ ℕ→ Need}
    (hs : Solves s3Task P p T need) (hp : PolyNeed need)
    (ht : ∀ᶠ n : ℕ in atTop,
      timeUpTo T n ((n:ℝ)^(κ:ℝ))≤ (n:ℝ)^targetExponent) :
    ThreeSumApsp.WordRam.SolvedInTimeAt EndStatement.ThreeSum κ (1921/1000:ℝ) 0 :=
  TernaryEndBridge.solvedAt_of_solves hs hp ht

theorem solvedAt_of_uniform {κ : ℕ} {P : Program} {p : ℕ}
    {T : ℕ→ ℕ→ ℕ} {need : ℕ→ ℕ→ Need}
    (hs : Solves s3Task P p T need) (hp : PolyNeed need)
    (ht : ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, U≤ n^κ→ (T n U:ℝ)≤ (n:ℝ)^targetExponent) :
    ThreeSumApsp.WordRam.SolvedInTimeAt EndStatement.ThreeSum κ (1921/1000:ℝ) 0 :=
  solvedAt_of_solves hs hp (TernaryEndBridge.timeUpTo_eventually_of_uniform ht)

/-- The final publication theorem needs one real solver and resource/time
proof for every fixed original-input magnitude exponent. -/
theorem endStatement_of_solvers
    (h : ∀ κ : ℕ, ∃ (P : Program) (p : ℕ) (T : ℕ→ ℕ→ ℕ) (need : ℕ→ ℕ→ Need),
      Solves s3Task P p T need ∧ PolyNeed need ∧
      ∀ᶠ n : ℕ in atTop, timeUpTo T n ((n:ℝ)^(κ:ℝ))≤ (n:ℝ)^targetExponent) :
    EndStatement.ThreeSum.SolvedInTime (1921/1000:Rat) := by
  apply TernaryEndBridge.endStatement_of_solvers (by norm_num : (0:ℚ)≤ 1921/1000)
  simpa only [Rat.cast_div,Rat.cast_ofNat,targetExponent] using h

theorem powerBound_of_eventually {T : ℕ→ ℕ} {a : ℝ}
    (ht : ∀ᶠ n : ℕ in atTop, (T n:ℝ)≤ (n:ℝ)^a) : PowerBound T a := by
  intro δ hδ
  filter_upwards [ht,eventually_ge_atTop (1:ℕ)] with n hn h1
  exact hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h1) (by linarith))

/-- This contract is the remaining operational obligation. Its inputs and
magnitude condition are the original task's, and its postcondition is the
original distinct-position decision. The cutoff is tested by actual code. -/
def FastExecution (P : Program) (p κ cutoff : ℕ) (T : ℕ→ ℕ) (need : ℕ→ ℕ→ Need) : Prop :=
  ∀ {lim : Limits} {src n free d : ℕ}, ∀ (x : Fin n→ ℤ) (μ : ℕ→ ℤ),
    cutoff≤ n→ 0<n→ src+n≤ free→ (need n (n^κ)).Ok lim free d→
    Seg μ src (List.ofFn x)→ (∀ i, |x i|≤ ((n^κ:ℕ):ℤ))→
    Meets lim P p d [src,n,free] μ (T n)
      (fun r ν=>(r=0∨r=1) ∧ (r=1↔Coloring.DistinctZeroSum x) ∧ Kept μ ν free)

theorem hybrid_solves {P : Program} {p κ cutoff : ℕ}
    {T : ℕ→ ℕ} {need : ℕ→ ℕ→ Need} (hexec : FastExecution P p κ cutoff T need) :
    Solves s3Task (TernaryHybridCore.program P p κ cutoff) (P.length+5)
      (TernaryHybridCore.time T κ cutoff) (TernaryHybridResources.need need κ cutoff) :=
  TernaryHybridCore.solves_of_fast need T hexec

theorem hybrid_polyNeed {need : ℕ→ ℕ→ Need} (hp : PolyNeed need) (κ cutoff : ℕ) :
    PolyNeed (TernaryHybridResources.need need κ cutoff) :=
  TernaryHybridResources.poly_need need hp κ cutoff

theorem hybrid_timeUpTo {T : ℕ→ ℕ} {a : ℝ}
    (ht : PowerBound T a) (ha : 0≤ a) (hmargin : a<targetExponent) (κ cutoff : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      timeUpTo (TernaryHybridCore.time T κ cutoff) n ((n:ℝ)^(κ:ℝ))≤ (n:ℝ)^targetExponent :=
  TernaryHybridCosts.timeUpTo_eventually ht ha hmargin κ cutoff

/-- Exact public-model conclusion from the fully instantiated fast program.
Both the finite exceptional inputs and excessive magnitude branch execute
the original four-procedure triple scan. -/
theorem hybrid_solvedAt {P : Program} {p κ cutoff : ℕ}
    {T : ℕ→ ℕ} {need : ℕ→ ℕ→ Need} {a : ℝ}
    (hexec : FastExecution P p κ cutoff T need) (hp : PolyNeed need)
    (ht : PowerBound T a) (ha : 0≤ a) (hmargin : a<targetExponent) :
    ThreeSumApsp.WordRam.SolvedInTimeAt EndStatement.ThreeSum κ (1921/1000:ℝ) 0 :=
  solvedAt_of_solves (hybrid_solves hexec) (hybrid_polyNeed hp κ cutoff)
    (hybrid_timeUpTo ht ha hmargin κ cutoff)

theorem endStatement_of_fast_solvers
    (h : ∀ κ : ℕ,
      ∃ (P : Program) (p cutoff : ℕ) (T : ℕ→ ℕ) (need : ℕ→ ℕ→ Need) (a : ℝ),
        FastExecution P p κ cutoff T need ∧ PolyNeed need ∧
        PowerBound T a ∧ 0≤ a ∧ a<targetExponent) :
    EndStatement.ThreeSum.SolvedInTime (1921/1000:Rat) := by
  apply endStatement_of_solvers
  intro κ
  obtain ⟨P,p,cutoff,T,need,a,hexec,hp,ht,ha,hmargin⟩:= h κ
  exact ⟨TernaryHybridCore.program P p κ cutoff,P.length+5,
    TernaryHybridCore.time T κ cutoff,TernaryHybridResources.need need κ cutoff,
    hybrid_solves hexec,hybrid_polyNeed hp κ cutoff,hybrid_timeUpTo ht ha hmargin κ cutoff⟩

end ThreeSum.TernarySolverEndBridge
