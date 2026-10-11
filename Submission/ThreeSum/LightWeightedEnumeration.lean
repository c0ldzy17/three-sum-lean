import Submission.ThreeSum.LightSubsetEnumeration

/-!
# Output-sensitive enumeration with arbitrary nonnegative coordinate weights

The existing recursive machine body is checked under a second contract.
Each output is the sum of the selected coordinate weights and the initial
prefix. The time and number of outputs remain binomial in the number of
available coordinates, independent of the size of the ambient mask.
-/

namespace ThreeSum.LightWeightedEnumeration

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open LightSubsetEnumeration (time work_pos)
open scoped BigOperators

variable {lim : Limits} {P : Program}

def total (weights : ℕ → ℕ) (L : ℕ) : ℕ := ∑ i ∈ Finset.range L, weights i

@[simp] theorem total_zero (weights : ℕ → ℕ) : total weights 0 = 0 := by
  simp [total]

@[simp] theorem total_succ (weights : ℕ → ℕ) (L : ℕ) :
    total weights (L+1) = total weights L+weights L := by
  simp [total,Finset.sum_range_succ]

def output (weights : ℕ → ℕ) : ℕ → ℕ → ℕ → List ℤ
  | _,0,pref => [pref]
  | 0,_+1,_ => []
  | L+1,k+1,pref =>
      if k+1 ≤ L+1 then
        output weights L (k+1) pref ++ output weights L k (pref+weights L)
      else []

@[simp] theorem output_length (weights : ℕ → ℕ) (L k pref : ℕ) :
    (output weights L k pref).length = L.choose k := by
  induction L generalizing k pref with
  | zero => cases k <;> simp [output]
  | succ L ih =>
    cases k with
    | zero => simp [output]
    | succ k =>
      by_cases h : k+1 ≤ L+1
      · simp [output,h,ih,Nat.choose_succ_succ,Nat.add_comm]
      · simp [output,h,Nat.choose_eq_zero_of_lt (by omega : L+1 < k+1)]

@[simp] theorem output_zero (weights : ℕ → ℕ) (L pref : ℕ) :
    output weights L 0 pref = [pref] := by
  cases L <;> rfl

theorem output_empty {weights : ℕ → ℕ} {L k : ℕ} (hk : L < k) (pref : ℕ) :
    output weights L k pref = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [output_length,Nat.choose_eq_zero_of_lt hk]

theorem output_succ {weights : ℕ → ℕ} {L k : ℕ} (hk : k+1 ≤ L+1) (pref : ℕ) :
    output weights (L+1) (k+1) pref =
      output weights L (k+1) pref ++ output weights L k (pref+weights L) := by
  simp [output,hk]

def Weights (μ : ℕ → ℤ) (base W : ℕ) (weights : ℕ → ℕ) : Prop :=
  ∀ i, i < W → μ (base+i) = (weights i : ℤ)

theorem meets {pEnum W powers U : ℕ} {weights : ℕ → ℕ}
    (hprog : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : (U : ℤ) ≤ lim.word) :
    ∀ L k pref dst : ℕ, ∀ μ : ℕ → ℤ,
      L ≤ W → k ≤ W+1 → pref+total weights L ≤ U →
      dst+L.choose k ≤ powers → Weights μ powers W weights →
      ∀ d, d+L ≤ lim.depth →
      Meets lim P pEnum d [L,k,pref,dst,powers] μ (time L k)
        (fun r μ' => r = (L.choose k : ℤ) ∧
          Seg μ' dst (output weights L k pref) ∧ SameOutside μ μ' dst (L.choose k)) := by
  intro L
  induction L with
  | zero =>
    intro k pref dst μ hL hk hprefix hdst hpowers d hd
    have htime : 150 ≤ 150*enumerationWork 0 k := Nat.mul_le_mul_left 150 (work_pos 0 k)
    have hprefNat : pref ≤ U := (Nat.le_add_right _ _).trans hprefix
    have hprefZ : (pref : ℤ) ≤ lim.word := by
      have hz : (pref : ℤ) ≤ (U : ℤ) := by exact_mod_cast hprefNat
      exact hz.trans hword
    cases k with
    | zero =>
      have hdspace : dst+1 ≤ lim.space := by simpa using hdst.trans (by omega)
      apply Meets.of_body hprog
      unfold LightSubsetEnumeration.body LightSubsetEnumeration.time
      refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simpa using h))
      light_store dst (pref : ℕ) using enumerationWork
      light_set (1 : ℕ) using enumerationWork
      refine ⟨rfl,?_,?_⟩
      · simp [output_zero,seg_cons]
      · intro a ha
        simp only [Nat.choose_zero_right] at ha
        change Function.update μ dst (pref : ℤ) a = _
        exact Function.update_of_ne (by omega) _ _
    | succ k =>
      apply Meets.of_body hprog
      unfold LightSubsetEnumeration.body LightSubsetEnumeration.time
      refine Ends.iteLast (fun h => False.elim (by simp at h <;> omega)) (fun _ => ?_)
      refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simpa using h))
      light_set (0 : ℕ) using enumerationWork
      refine ⟨by simp, ?_, SameOutside.refl⟩
      rw [output_empty (weights := weights) (L := 0) (k := k+1) (by omega) pref]
      exact Seg.nil
  | succ L ih =>
    intro k pref dst μ hL hk hprefix hdst hpowers d hd
    have htime : 150 ≤ 150*enumerationWork (L+1) k :=
      Nat.mul_le_mul_left 150 (work_pos (L+1) k)
    have hLW : L ≤ W := by omega
    have hprefNat : pref ≤ U := (Nat.le_add_right _ _).trans hprefix
    have hprefZ : (pref : ℤ) ≤ lim.word := by
      have hz : (pref : ℤ) ≤ (U : ℤ) := by exact_mod_cast hprefNat
      exact hz.trans hword
    cases k with
    | zero =>
      have hdspace : dst+1 ≤ lim.space := by simpa using hdst.trans (by omega)
      apply Meets.of_body hprog
      unfold LightSubsetEnumeration.body LightSubsetEnumeration.time
      refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simpa using h))
      light_store dst (pref : ℕ) using enumerationWork
      light_set (1 : ℕ) using enumerationWork
      refine ⟨by simp,?_,?_⟩
      · simp [output_zero,seg_cons]
      · intro a ha
        simp only [Nat.choose_zero_right] at ha
        change Function.update μ dst (pref : ℤ) a = _
        exact Function.update_of_ne (by omega) _ _
    | succ k =>
      apply Meets.of_body hprog
      unfold LightSubsetEnumeration.body LightSubsetEnumeration.time
      refine Ends.iteLast (fun h => False.elim (by simp at h <;> omega)) (fun _ => ?_)
      light_if hemptyZ hfullZ : ((L+1 : ℕ) : ℤ) < ((k+1 : ℕ) : ℤ)
      · have hempty : L+1 < k+1 := by exact_mod_cast hemptyZ
        have hnot : ¬ k+1 ≤ L+1 := by omega
        light_set (0 : ℕ) using enumerationWork,hnot
        refine ⟨by simp [Nat.choose_eq_zero_of_lt hempty], ?_, SameOutside.refl⟩
        rw [output_empty (weights := weights) hempty pref]
        exact Seg.nil
      · have hfull : k+1 ≤ L+1 := by exact_mod_cast (le_of_not_gt hfullZ)
        have hchoose : (L+1).choose (k+1) = L.choose (k+1)+L.choose k := by
          rw [Nat.choose_succ_succ,Nat.add_comm]
        have hdst₀ : dst+L.choose (k+1) ≤ powers := by omega
        have hdst₁ : dst+L.choose (k+1)+L.choose k ≤ powers := by omega
        have hprefix₀ : pref+total weights L ≤ U := by
          rw [total_succ] at hprefix
          omega
        have hprefix₁ : pref+weights L+total weights L ≤ U := by
          rw [total_succ] at hprefix
          omega
        light_set (L : ℕ) using enumerationWork,hfull
        have hchild₀ := ih (k+1) pref dst μ hLW hk hprefix₀ hdst₀ hpowers (d+1) (by omega)
        light_call hchild₀ using time,enumerationWork,hfull
          with n₀ μ₁ ⟨hn₀,hseg₀,hsame₀⟩
        have hpowers₁ : Weights μ₁ powers W weights := by
          intro i hi
          rw [hsame₀ (powers+i) (Or.inr (by omega))]
          exact hpowers i hi
        have hpowerRead := hpowers₁ L (by omega)
        have hargPrefix : (pref : ℤ)+μ₁ (powers+L) = ((pref+weights L : ℕ) : ℤ) := by
          rw [hpowerRead]
          push_cast
          rfl
        have hprefixArgBound : (pref : ℤ)+μ₁ (powers+L) ≤ lim.word := by
          rw [hargPrefix]
          have hb : pref+weights L ≤ U := by omega
          have hz : ((pref+weights L : ℕ) : ℤ) ≤ (U : ℤ) := by exact_mod_cast hb
          exact hz.trans hword
        have hreadNonneg : (0 : ℤ) ≤ μ₁ (powers+L) := by
          rw [hpowerRead]
          exact Int.natCast_nonneg _
        have hpowerEqInt : (weights L : ℤ) = μ₁ (powers+L) := by
          simpa using hpowerRead.symm
        have hpowerIntNonneg : (0 : ℤ) ≤ (weights L : ℤ) := Int.natCast_nonneg _
        have hprefixIntBound : (pref : ℤ)+(weights L : ℤ) ≤ lim.word := by
          rw [hpowerEqInt]
          exact hprefixArgBound
        have hchild₁ := ih k (pref+weights L) (dst+L.choose (k+1)) μ₁
          hLW (by omega) hprefix₁ hdst₁ hpowers₁ (d+1) (by omega)
        light_call hchild₁ using time,enumerationWork,hfull,hn₀,hargPrefix
          with n₁ μ₂ ⟨hn₁,hseg₁,hsame₁⟩
        have htotalBound : ((L.choose (k+1)+L.choose k : ℕ) : ℤ) ≤ lim.word := by
          have hn : L.choose (k+1)+L.choose k ≤ lim.space := by omega
          have hz : ((L.choose (k+1)+L.choose k : ℕ) : ℤ) ≤ (lim.space : ℤ) := by
            exact_mod_cast hn
          exact hz.trans hw
        have hseg₀' : Seg μ₂ dst (output weights L (k+1) pref) :=
          hseg₀.of_sameOutside hsame₁ (Or.inl (by simp))
        light_set (L.choose (k+1)+L.choose k : ℕ)
          using time,enumerationWork,hfull,hn₀,hn₁
        refine ⟨by simpa [hchoose],?_,?_⟩
        · rw [output_succ hfull,seg_append,output_length]
          exact ⟨hseg₀',hseg₁⟩
        · exact hsame₀.then hsame₁ (fun a ha => by
            rw [hchoose] at ha
            constructor <;> omega)

def program : Program := [LightSubsetEnumeration.body 0]

theorem program_meets {W powers U L k pref dst d : ℕ} {weights : ℕ → ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : (U : ℤ) ≤ lim.word)
    (hL : L ≤ W) (hk : k ≤ W+1) (hprefix : pref+total weights L ≤ U)
    (hdst : dst+L.choose k ≤ powers) (hpowers : Weights μ powers W weights)
    (hd : d+L ≤ lim.depth) :
    Meets lim program 0 d [L,k,pref,dst,powers] μ (time L k)
      (fun r μ' => r = (L.choose k : ℤ) ∧
        Seg μ' dst (output weights L k pref) ∧ SameOutside μ μ' dst (L.choose k)) :=
  meets rfl hw hspace hword L k pref dst μ hL hk hprefix hdst hpowers d hd

end ThreeSum.LightWeightedEnumeration
