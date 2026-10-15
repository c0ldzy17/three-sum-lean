import Submission.ThreeSum.TernaryCoverHighMoment
import Submission.ThreeSum.TernaryLocalParameters

/-! # Actual fixed-type trinary tagged high moments

The graph, both tag columns, all projection caps, and the prime-size guard
are instantiated here.  The bound counts all raw ordered representations;
no trimmed-edge or independent-feature surrogate replaces that graph.
-/

noncomputable section
namespace ThreeSum.TernaryCoverActualMoment

open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryCoverHighMoment TernaryCoverRankFibers TernaryLocalParameters
open TernaryCoverOutputCap
open scoped BigOperators

def taggedLeft {L : ℕ} {α π : DigitType} (e : LocalEdge L α π) : Coordinate (Fin L) → Fin 3 :=
  Sum.elim (left e) (fun b => if b then 0 else 1)

def taggedRight {L : ℕ} {α π : DigitType} (e : LocalEdge L α π) : Coordinate (Fin L) → Fin 3 :=
  Sum.elim (right e) (fun b => if b then 1 else 0)

theorem cast_taggedLeft {L p : ℕ} [Fact p.Prime] {α π : DigitType} (e : LocalEdge L α π) :
    castWord (K := ZMod p) (taggedLeft e) = leftVector (fieldLeft (p := p) e) := by
  funext c
  cases c with
  | inl i => rfl
  | inr b => cases b <;> simp [castWord, taggedLeft, leftVector]

theorem cast_taggedRight {L p : ℕ} [Fact p.Prime] {α π : DigitType} (e : LocalEdge L α π) :
    castWord (K := ZMod p) (taggedRight e) = rightVector (fieldRight (p := p) e) := by
  funext c
  cases c with
  | inl i => rfl
  | inr b => cases b <;> simp [castWord, taggedRight, rightVector]

theorem tagged_endpoint_injective {L p : ℕ} [Fact p.Prime] (α π : DigitType) (hp : 2 < p) :
    Function.Injective (fun e : LocalEdge L α π =>
      (castWord (K := ZMod p) (taggedLeft e), castWord (K := ZMod p) (taggedRight e))) := by
  intro e f he
  apply field_endpoint_injective α π hp
  have hl := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  apply Prod.ext
  · funext i
    exact congrFun hl (.inl i)
  · funext i
    exact congrFun hr (.inl i)

theorem actual_rawEvents {L p : ℕ} [Fact p.Prime] (α π : DigitType) (a b : ZMod p) :
    rawEvents (fun e : LocalEdge L α π => taggedLeft e) taggedRight a b =
      (fun e => pairEvent (fieldLeft (p := p) e) (fieldRight e) a b) := by
  funext e
  unfold rawEvents pairEvent linearHash
  rw [cast_taggedLeft, cast_taggedRight]

theorem actual_high_moment (m p : ℕ) [Fact p.Prime] (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2)
    (k : ℕ) (a b : ZMod p) :
    (∑ w : Coordinate (Fin (fixedLength m)) → ZMod p,
      TernaryCoverFibers.rawPairCount
        (leftHash (α := fixedAlpha m) (π := fixedPi m) w) (rightHash w) a b ^ k) ≤
      3 ^ (4*k^2) * Fintype.card (Coordinate (Fin (fixedLength m)) → ZMod p) := by
  classical
  let E := LocalEdge (fixedLength m) (fixedAlpha m) (fixedPi m)
  have hE : Fintype.card E ≤ Fintype.card (ZMod p) ^ 2 := by
    simpa [E] using (edges_card_le (L := fixedLength m) (fixedAlpha m) (fixedPi m)).trans hP
  have hprojection (β γ : ZMod p) (hn : β ≠ 0 ∨ γ ≠ 0)
      (q : Coordinate (Fin (fixedLength m)) → ZMod p) :
      (projectionFiber (fun e : E => castWord (K := ZMod p) (taggedLeft e))
        (fun e => castWord (K := ZMod p) (taggedRight e)) β γ q).card ≤ Fintype.card (ZMod p) := by
    have hsub : projectionFiber (fun e : E => castWord (K := ZMod p) (taggedLeft e))
        (fun e => castWord (K := ZMod p) (taggedRight e)) β γ q ⊆
        TernaryCoverGenericProjection.mixedFiber (fixedAlpha m) (fixedPi m) β γ (fun i => q (.inl i)) := by
      intro e he
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      intro i
      exact (mem_filter.mp he).2 (.inl i)
    exact (card_le_card hsub).trans (by simpa using fixed_mixedFiber_cap m p hp hP hn (fun i => q (.inl i)))
  have h := raw_high_moment (fun e : E => taggedLeft e) taggedRight
    (tagged_endpoint_injective (fixedAlpha m) (fixedPi m) (by omega : 2 < p))
    hE hprojection k a b
  rw [actual_rawEvents] at h
  simpa [E, HashFamily.incidenceCount, TernaryCoverFibers.rawPairCount,
    pairEvent, leftHash, rightHash, linearHash] using h

end ThreeSum.TernaryCoverActualMoment
