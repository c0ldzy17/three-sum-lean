import Submission.ThreeSum.LightTernaryEulerMetadata
import Submission.ThreeSum.LightTernaryEulerMemo
import Submission.ThreeSum.TernaryPartialEuler

/-! Exact meaning of physical Euler predecessor rows. -/
noncomputable section
namespace ThreeSum.TernaryPhysicalEuler

open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics

set_option maxHeartbeats 3000000

/-- Logical ordinal of a word in a compact dictionary. Runtime code obtains this
ordinal by the proved binary search, rather than evaluating this definition. -/
def ordinal {N : ℕ} (words : ℕ → TritWord N) (n : ℕ) (w : TritWord N) : ℕ :=
  if h : ∃ j<n, words j=w then h.choose else 0

theorem ordinal_spec {N : ℕ} {words : ℕ → TritWord N} {n : ℕ} {w : TritWord N}
    (h : ∃ j<n, words j=w) : ordinal words n w<n ∧ words (ordinal words n w)=w := by
  unfold ordinal
  rw [dif_pos h]
  exact h.choose_spec

/-- The value function used by the actual indirect loads. Bank cells precede
near cells; the zero-weight dummy is the first initialized bank cell. -/
def physicalWord {N : ℕ} (bankWords nearWords : ℕ → TritWord N) (bv nv x : ℕ) : TritWord N :=
  if x<nv then bankWords (x-bv) else nearWords (x-nv)

def physicalValue {N : ℕ} (F : TritWord N → ℤ) (bankWords nearWords : ℕ → TritWord N)
    (bv nv x : ℕ) : ℤ := F (physicalWord bankWords nearWords bv nv x)

theorem physical_bank {N bv nv nb j : ℕ} (bankWords nearWords : ℕ → TritWord N)
    (hsep : bv+nb≤nv) (hj : j<nb) :
    physicalWord bankWords nearWords bv nv (bv+j)=bankWords j := by
  simp [physicalWord,show bv+j<nv by omega]

theorem physical_near {N bv nv j : ℕ} (bankWords nearWords : ℕ → TritWord N) :
    physicalWord bankWords nearWords bv nv (nv+j)=nearWords j := by
  simp [physicalWord]

theorem digit_canonical {N : ℕ} (R : TritWord N) (i : Fin N) :
    LightTernaryPredecessor.digit N (LightTernaryEulerMetadata.lowAt N i.val)
      (LightTernaryEulerMetadata.highAt N i.val) (address R)=(R i).val := by
  exact digit_eq R i

theorem predRank_canonical {N : ℕ} (R : TritWord N) (i : Fin N) (hi : 0<(R i).val) :
    LightTernaryPredecessor.predRank N (LightTernaryEulerMetadata.lowAt N i.val)
      (LightTernaryEulerMetadata.highAt N i.val) (address R)=rank (predecessor R i) := by
  unfold LightTernaryPredecessor.predRank
  change LightTernaryRank.partialRank N
    (LightTernaryPredecessor.code N (low i) (high i) (address R)) N=rank (predecessor R i)
  rw [LightTernaryPredecessor.code_canonical R i hi,LightTernaryRank.partialRank_address]

def rowWeight {N : ℕ} (R : TritWord N) (i : ℕ) : ℕ :=
  LightTernaryPredecessor.weight N (LightTernaryEulerMetadata.lowAt N i)
    (LightTernaryEulerMetadata.highAt N i) (address R) 1

def rowKey {N : ℕ} (R : TritWord N) (bankWords nearWords : ℕ → TritWord N)
    (nb nn T bv nv i : ℕ) : ℕ :=
  let low := LightTernaryEulerMetadata.lowAt N i
  let high := LightTernaryEulerMetadata.highAt N i
  let pred := if hi : i<N then predecessor R ⟨i,hi⟩ else R
  LightTernaryPredecessor.key N low high (address R) T 1 bv nv
    (ordinal bankWords nb pred) (ordinal nearWords nn pred)

theorem rowWeight_eq {N : ℕ} (R : TritWord N) (i : Fin N) : rowWeight R i.val=(R i).val := by
  simp [rowWeight,LightTernaryPredecessor.weight,digit_canonical]

theorem rowKey_zero {N nb nn T bv nv : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (i : Fin N) (hi : (R i).val=0) :
    rowKey R bankWords nearWords nb nn T bv nv i.val=bv := by
  simp [rowKey,LightTernaryPredecessor.key,digit_canonical,hi]

theorem rowKey_bank {N nb nn T bv nv : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (i : Fin N) (hi : 0<(R i).val)
    (hr : rank (predecessor R i)≤T) :
    rowKey R bankWords nearWords nb nn T bv nv i.val=
      bv+ordinal bankWords nb (predecessor R i) := by
  simp [rowKey,LightTernaryPredecessor.key,digit_canonical,predRank_canonical R i hi,
    show (R i).val≠0 by omega,hr]

theorem rowKey_near {N nb nn T bv nv : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (i : Fin N) (hi : 0<(R i).val)
    (hr : T<rank (predecessor R i)) :
    rowKey R bankWords nearWords nb nn T bv nv i.val=
      nv+ordinal nearWords nn (predecessor R i) := by
  simp [rowKey,LightTernaryPredecessor.key,digit_canonical,predRank_canonical R i hi,
    show (R i).val≠0 by omega,show ¬rank (predecessor R i)≤T by omega]

/-- Every positive read is exactly the canonical predecessor. -/
theorem positive_read {N nb nn T bv nv : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (hsep : bv+nb≤nv)
    (hbank : ∀ W, rank W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ i : Fin N, T<rank (predecessor R i) → ∃ j<nn, nearWords j=predecessor R i)
    (i : Fin N) (hi : 0<(R i).val) :
    physicalWord bankWords nearWords bv nv (rowKey R bankWords nearWords nb nn T bv nv i.val)=
      predecessor R i := by
  by_cases hr : rank (predecessor R i)≤T
  · rw [rowKey_bank R bankWords nearWords i hi hr]
    obtain ⟨hj,he⟩ := ordinal_spec (hbank _ hr)
    rw [physical_bank bankWords nearWords hsep hj,he]
  · rw [rowKey_near R bankWords nearWords i hi (by omega)]
    rw [physical_near]
    exact (ordinal_spec (hnear i (by omega))).2

/-- The physical signed numerator is the homogeneous Euler numerator, including
zero coordinates whose actual reads use the safe dummy bank cell. -/
theorem numerator {N nb nn T bv nv h : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (f : TritWord N → ℤ)
    (hf : ∀ A, f A≠0 → rank A=h) (hcut : h≤rank R)
    (hsep : bv+nb≤nv)
    (hbank : ∀ W, rank W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ i : Fin N, T<rank (predecessor R i) → ∃ j<nn, nearWords j=predecessor R i) :
    LightTernaryWeightedSum.sum (rowWeight R) (rowKey R bankWords nearWords nb nn T bv nv)
      (physicalValue (binomialZeta f) bankWords nearWords bv nv) N=
      (rank R-h : ℕ)*binomialZeta f R := by
  unfold LightTernaryWeightedSum.sum
  rw [←Fin.sum_univ_eq_sum_range]
  have he : (∑ i : Fin N, (rowWeight R i.val : ℤ)*
      physicalValue (binomialZeta f) bankWords nearWords bv nv
        (rowKey R bankWords nearWords nb nn T bv nv i.val))=
      ∑ i : Fin N, (R i).val*binomialZeta f (predecessor R i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [rowWeight_eq]
    by_cases hi : (R i).val=0
    · simp [hi]
    · have hh := positive_read R bankWords nearWords hsep hbank hnear i (by omega)
      simp only [physicalValue,hh]
  rw [he,binomialZeta_euler f h hf,Nat.cast_sub hcut]

/-- A predecessor reached outside the bank is present in the same near segment. -/
theorem near_predecessor_present {N nn T : ℕ} (Q R : TritWord N)
    (nearWords : ℕ → TritWord N)
    (hnear : ∀ W, Below W Q → T<rank W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : Fin N) (hr : T<rank (predecessor R i)) :
    ∃ j<nn, nearWords j=predecessor R i := by
  exact hnear _ (fun k => (predecessor_below R i k).trans (hRQ k)) hr

/-- Every metadata address is inside an initialized bank or a strictly earlier
near rank. In particular a zero-weight read is still a real initialized read. -/
theorem rowKey_precedes {N nb nn T bv nv : ℕ} (Q R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (hsep : bv+nb≤nv) (hnb : 0<nb)
    (hbank : ∀ W, rank W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ W, Below W Q → T<rank W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : Fin N) :
    rowKey R bankWords nearWords nb nn T bv nv i.val<nv ∨
      ∃ j<nn, rowKey R bankWords nearWords nb nn T bv nv i.val=nv+j ∧
        rank (nearWords j)<rank R := by
  by_cases hz : (R i).val=0
  · rw [rowKey_zero R bankWords nearWords i hz]
    exact Or.inl (by omega)
  · have hp : 0<(R i).val := by omega
    by_cases hr : rank (predecessor R i)≤T
    · rw [rowKey_bank R bankWords nearWords i hp hr]
      have hh := (ordinal_spec (hbank _ hr)).1
      exact Or.inl (by omega)
    · have hh := ordinal_spec (near_predecessor_present Q R nearWords hnear hRQ i (by omega))
      refine Or.inr ⟨_,hh.1,rowKey_near R bankWords nearWords i hp (by omega),?_⟩
      rw [hh.2]
      exact predecessor_rank_lt R i hp

theorem rowKey_lower_bound {N nb nn T bv nv : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (hsep : bv≤nv) (i : Fin N) :
    bv≤rowKey R bankWords nearWords nb nn T bv nv i.val := by
  unfold rowKey
  dsimp only
  unfold LightTernaryPredecessor.key
  split_ifs <;> omega

theorem rowKey_bound {N nb nn T bv nv : ℕ} (Q R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (hsep : bv+nb≤nv) (hnb : 0<nb)
    (hbank : ∀ W, rank W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ W, Below W Q → T<rank W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : Fin N) :
    rowKey R bankWords nearWords nb nn T bv nv i.val<nv+nn := by
  rcases rowKey_precedes Q R bankWords nearWords hsep hnb hbank hnear hRQ i with hb | ⟨j,hj,he,_⟩
  · omega
  · omega

/-- Exact original bank reads, including the dummy read, suffice for all
predecessor reads that lie before the near destination. -/
theorem rowKey_bank_read {N nb nn T bv nv : ℕ} (Q R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (F : TritWord N → ℤ) (μ : ℕ → ℤ)
    (hsep : bv+nb≤nv) (hnb : 0<nb)
    (hbank : ∀ W, rank W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ W, Below W Q → T<rank W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q)
    (hread : ∀ j<nb, μ (bv+j)=F (bankWords j)) (i : Fin N)
    (hk : rowKey R bankWords nearWords nb nn T bv nv i.val<nv) :
    ∃ j<nb, rowKey R bankWords nearWords nb nn T bv nv i.val=bv+j ∧
      μ (rowKey R bankWords nearWords nb nn T bv nv i.val)=
        physicalValue F bankWords nearWords bv nv (rowKey R bankWords nearWords nb nn T bv nv i.val) := by
  by_cases hz : (R i).val=0
  · rw [rowKey_zero R bankWords nearWords i hz]
    refine ⟨0,hnb,by omega,?_⟩
    simpa [physicalValue,physicalWord,show bv<nv by omega] using hread 0 hnb
  · have hp : 0<(R i).val := by omega
    by_cases hr : rank (predecessor R i)≤T
    · have hj := ordinal_spec (hbank _ hr)
      rw [rowKey_bank R bankWords nearWords i hp hr]
      refine ⟨_,hj.1,rfl,?_⟩
      unfold physicalValue
      rw [physical_bank bankWords nearWords hsep hj.1,hread _ hj.1]
    · rw [rowKey_near R bankWords nearWords i hp (by omega)] at hk
      omega

/-- Logical predecessor indices for each physical metadata column. -/
def predecessorOrdinal {N : ℕ} (words : ℕ → TritWord N) (n : ℕ)
    (R : TritWord N) (i : ℕ) : ℕ :=
  ordinal words n (if hi : i<N then predecessor R ⟨i,hi⟩ else R)

theorem bank_index_correct {N nb T : ℕ} (bankWords : ℕ → TritWord N)
    (hbank : ∀ W, rank W≤T → ∃ j<nb, bankWords j=W)
    (R : TritWord N) (i : ℕ) (hi : i<N)
    (hdigit : LightTernaryPredecessor.digit N (LightTernaryEulerMetadata.lowAt N i)
      (LightTernaryEulerMetadata.highAt N i) (address R)≠0)
    (hrank : LightTernaryPredecessor.predRank N (LightTernaryEulerMetadata.lowAt N i)
      (LightTernaryEulerMetadata.highAt N i) (address R)≤T) :
    predecessorOrdinal bankWords nb R i<nb ∧
      address (bankWords (predecessorOrdinal bankWords nb R i))=
        LightTernaryPredecessor.code N (LightTernaryEulerMetadata.lowAt N i)
          (LightTernaryEulerMetadata.highAt N i) (address R) := by
  let fi : Fin N := ⟨i,hi⟩
  have hd : 0<(R fi).val := by rw [digit_canonical R fi] at hdigit; omega
  have hr : rank (predecessor R fi)≤T := by
    rwa [predRank_canonical R fi hd] at hrank
  have ho := ordinal_spec (hbank _ hr)
  have he : predecessorOrdinal bankWords nb R i=ordinal bankWords nb (predecessor R fi) := by
    simp [predecessorOrdinal,hi,fi]
  rw [he]
  refine ⟨ho.1,?_⟩
  rw [ho.2]
  exact (LightTernaryPredecessor.code_canonical R fi hd).symm

theorem near_index_correct {N nn T : ℕ} (Q R : TritWord N)
    (nearWords : ℕ → TritWord N)
    (hnear : ∀ W, Below W Q → T<rank W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : ℕ) (hi : i<N)
    (hdigit : LightTernaryPredecessor.digit N (LightTernaryEulerMetadata.lowAt N i)
      (LightTernaryEulerMetadata.highAt N i) (address R)≠0)
    (hrank : T<LightTernaryPredecessor.predRank N (LightTernaryEulerMetadata.lowAt N i)
      (LightTernaryEulerMetadata.highAt N i) (address R)) :
    predecessorOrdinal nearWords nn R i<nn ∧
      address (nearWords (predecessorOrdinal nearWords nn R i))=
        LightTernaryPredecessor.code N (LightTernaryEulerMetadata.lowAt N i)
          (LightTernaryEulerMetadata.highAt N i) (address R) := by
  let fi : Fin N := ⟨i,hi⟩
  have hd : 0<(R fi).val := by rw [digit_canonical R fi] at hdigit; omega
  have hr : T<rank (predecessor R fi) := by
    rwa [predRank_canonical R fi hd] at hrank
  have ho := ordinal_spec (near_predecessor_present Q R nearWords hnear hRQ fi hr)
  have he : predecessorOrdinal nearWords nn R i=ordinal nearWords nn (predecessor R fi) := by
    simp [predecessorOrdinal,hi,fi]
  rw [he]
  refine ⟨ho.1,?_⟩
  rw [ho.2]
  exact (LightTernaryPredecessor.code_canonical R fi hd).symm

end ThreeSum.TernaryPhysicalEuler
