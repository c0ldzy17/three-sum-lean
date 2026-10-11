import Submission.ThreeSum.LightSubsetAddress

/-!
# Output-sensitive subset-layer enumeration in the benchmark language

The recursive routine writes into consecutive output cells. Empty layers
return immediately; a zero-cardinality layer emits one mask. The two
recursive children share the output buffer and write adjacent, disjoint
segments. No ambient Boolean cube is scanned and no output list is copied.
-/

namespace ThreeSum.LightSubsetEnumeration

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def output (L k pref : ℕ) : List ℤ :=
  (enumerateLayer L k).map (fun m => ((pref+m : ℕ) : ℤ))

@[simp] theorem output_length (L k pref : ℕ) :
    (output L k pref).length = L.choose k := by
  simp [output,enumerateLayer_length]

@[simp] theorem output_zero (L pref : ℕ) : output L 0 pref = [pref] := by
  simp [output,enumerateLayer]

theorem output_empty {L k : ℕ} (hk : L < k) (pref : ℕ) : output L k pref = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [output_length,Nat.choose_eq_zero_of_lt hk]

theorem output_succ {L k : ℕ} (hk : k+1 ≤ L+1) (pref : ℕ) :
    output (L+1) (k+1) pref =
      output L (k+1) pref ++ output L k (pref+2^L) := by
  simp [output,enumerateLayer,hk,List.map_append,List.map_map,Function.comp_def,Nat.add_assoc]

/-- Arguments: remaining width, cardinality, pref, output base, powers base.
The pref contains the already selected high bits. -/
def body (pSelf : ℕ) : Stmt :=
  .ite (v 1 <' k 1)
    (.store (v 3) (v 2) ;; .set 0 (k 1))
    (.ite (v 0 <' v 1)
      (.set 0 (k 0))
      (.set 5 (v 0 -' k 1) ;;
        .call pSelf [v 5,v 1,v 2,v 3,v 4] 6 ;;
        .call pSelf [v 5,v 1 -' k 1,v 2 +' M (v 4 +' v 5),v 3 +' v 6,v 4] 7 ;;
        .set 0 (v 6 +' v 7)))

def time (L k : ℕ) : ℕ := 150*enumerationWork L k

theorem work_pos (L k : ℕ) : 1 ≤ enumerationWork L k := by
  cases L with
  | zero => cases k <;> simp [enumerationWork]
  | succ L =>
    cases k with
    | zero => simp [enumerationWork]
    | succ k =>
      simp only [enumerationWork]
      split <;> omega

theorem time_bound (L k : ℕ) :
    time L k ≤ 150*((4*L+1)*L.choose k+1) := by
  exact Nat.mul_le_mul_left 150 (enumerationWork_bound L k)

theorem meets {pEnum W powers : ℕ}
    (hprog : P[pEnum]? = some (body pEnum))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word) :
    ∀ L k pref dst : ℕ, ∀ μ : ℕ → ℤ,
      L ≤ W → k ≤ W+1 → pref+2^L ≤ 2^W →
      dst+L.choose k ≤ powers → Powers μ powers W →
      ∀ d, d+L ≤ lim.depth →
      Meets lim P pEnum d [L,k,pref,dst,powers] μ (time L k)
        (fun r μ' => r = (L.choose k : ℤ) ∧
          Seg μ' dst (output L k pref) ∧ SameOutside μ μ' dst (L.choose k)) := by
  have hpowWord : ((2^W : ℕ) : ℤ) ≤ lim.word := by
    have hn : (2^W : ℕ) ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hz : ((2^W : ℕ) : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ) := by exact_mod_cast hn
    exact hz.trans hword
  intro L
  induction L with
  | zero =>
    intro k pref dst μ hL hk hprefix hdst hpowers d hd
    have htime : 150 ≤ 150*enumerationWork 0 k := Nat.mul_le_mul_left 150 (work_pos 0 k)
    have hprefNat : pref ≤ 2^W := (Nat.le_add_right _ _).trans hprefix
    have hprefZ : (pref : ℤ) ≤ lim.word := by
      have hz : (pref : ℤ) ≤ ((2^W : ℕ) : ℤ) := by exact_mod_cast hprefNat
      exact hz.trans hpowWord
    cases k with
    | zero =>
      have hdspace : dst+1 ≤ lim.space := by simpa using hdst.trans (by omega)
      apply Meets.of_body hprog
      unfold body time
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
      unfold body time
      refine Ends.iteLast (fun h => False.elim (by simp at h <;> omega)) (fun _ => ?_)
      refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simpa using h))
      light_set (0 : ℕ) using enumerationWork
      refine ⟨by simp, ?_, SameOutside.refl⟩
      rw [output_empty (L := 0) (k := k+1) (by omega) pref]
      exact Seg.nil
  | succ L ih =>
    intro k pref dst μ hL hk hprefix hdst hpowers d hd
    have htime : 150 ≤ 150*enumerationWork (L+1) k :=
      Nat.mul_le_mul_left 150 (work_pos (L+1) k)
    have hLW : L ≤ W := by omega
    have hprefNat : pref ≤ 2^W := (Nat.le_add_right _ _).trans hprefix
    have hprefZ : (pref : ℤ) ≤ lim.word := by
      have hz : (pref : ℤ) ≤ ((2^W : ℕ) : ℤ) := by exact_mod_cast hprefNat
      exact hz.trans hpowWord
    cases k with
    | zero =>
      have hdspace : dst+1 ≤ lim.space := by simpa using hdst.trans (by omega)
      apply Meets.of_body hprog
      unfold body time
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
      unfold body time
      refine Ends.iteLast (fun h => False.elim (by simp at h <;> omega)) (fun _ => ?_)
      light_if hemptyZ hfullZ : ((L+1 : ℕ) : ℤ) < ((k+1 : ℕ) : ℤ)
      · have hempty : L+1 < k+1 := by exact_mod_cast hemptyZ
        have hnot : ¬ k+1 ≤ L+1 := by omega
        light_set (0 : ℕ) using enumerationWork,hnot
        refine ⟨by simp [Nat.choose_eq_zero_of_lt hempty], ?_, SameOutside.refl⟩
        rw [output_empty hempty pref]
        exact Seg.nil
      · have hfull : k+1 ≤ L+1 := by exact_mod_cast (le_of_not_gt hfullZ)
        have hchoose : (L+1).choose (k+1) = L.choose (k+1)+L.choose k := by
          rw [Nat.choose_succ_succ,Nat.add_comm]
        have hdst₀ : dst+L.choose (k+1) ≤ powers := by omega
        have hdst₁ : dst+L.choose (k+1)+L.choose k ≤ powers := by omega
        have hprefix₀ : pref+2^L ≤ 2^W := by
          have he : 2^(L+1)=2^L+2^L := by rw [pow_succ]; omega
          omega
        have hprefix₁ : pref+2^L+2^L ≤ 2^W := by
          have he : 2^(L+1)=2^L+2^L := by rw [pow_succ]; omega
          omega
        light_set (L : ℕ) using enumerationWork,hfull
        have hchild₀ := ih (k+1) pref dst μ hLW hk hprefix₀ hdst₀ hpowers (d+1) (by omega)
        light_call hchild₀ using time,enumerationWork,hfull
          with n₀ μ₁ ⟨hn₀,hseg₀,hsame₀⟩
        have hpowers₁ : Powers μ₁ powers W := by
          intro i hi
          rw [hsame₀ (powers+i) (Or.inr (by omega))]
          exact hpowers i hi
        have hpowerRead := hpowers₁ L hLW
        have hargPrefix : (pref : ℤ)+μ₁ (powers+L) = ((pref+2^L : ℕ) : ℤ) := by
          rw [hpowerRead]
          push_cast
          rfl
        have hprefixArgBound : (pref : ℤ)+μ₁ (powers+L) ≤ lim.word := by
          rw [hargPrefix]
          have hb : pref+2^L ≤ 2^W := by omega
          have hz : ((pref+2^L : ℕ) : ℤ) ≤ ((2^W : ℕ) : ℤ) := by exact_mod_cast hb
          exact hz.trans hpowWord
        have hreadNonneg : (0 : ℤ) ≤ μ₁ (powers+L) := by
          rw [hpowerRead]
          exact Int.natCast_nonneg _
        have hpowerEqInt : (2 : ℤ)^L = μ₁ (powers+L) := by
          simpa using hpowerRead.symm
        have hpowerIntNonneg : (0 : ℤ) ≤ (2 : ℤ)^L := by positivity
        have hprefixIntBound : (pref : ℤ)+(2 : ℤ)^L ≤ lim.word := by
          rw [hpowerEqInt]
          exact hprefixArgBound
        have hchild₁ := ih k (pref+2^L) (dst+L.choose (k+1)) μ₁
          hLW (by omega) hprefix₁ hdst₁ hpowers₁ (d+1) (by omega)
        light_call hchild₁ using time,enumerationWork,hfull,hn₀,hargPrefix
          with n₁ μ₂ ⟨hn₁,hseg₁,hsame₁⟩
        have htotalBound : ((L.choose (k+1)+L.choose k : ℕ) : ℤ) ≤ lim.word := by
          have hn : L.choose (k+1)+L.choose k ≤ lim.space := by omega
          have hz : ((L.choose (k+1)+L.choose k : ℕ) : ℤ) ≤ (lim.space : ℤ) := by
            exact_mod_cast hn
          exact hz.trans hw
        have hseg₀' : Seg μ₂ dst (output L (k+1) pref) :=
          hseg₀.of_sameOutside hsame₁ (Or.inl (by simp))
        light_set (L.choose (k+1)+L.choose k : ℕ)
          using time,enumerationWork,hfull,hn₀,hn₁
        refine ⟨by simpa [hchoose],?_,?_⟩
        · rw [output_succ hfull,seg_append,output_length]
          exact ⟨hseg₀',hseg₁⟩
        · exact hsame₀.then hsame₁ (fun a ha => by
            rw [hchoose] at ha
            constructor <;> omega)

def program : Program := [body 0]

theorem program_meets {W powers L k pref dst d : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hL : L ≤ W) (hk : k ≤ W+1) (hprefix : pref+2^L ≤ 2^W)
    (hdst : dst+L.choose k ≤ powers) (hpowers : Powers μ powers W)
    (hd : d+L ≤ lim.depth) :
    Meets lim program 0 d [L,k,pref,dst,powers] μ (time L k)
      (fun r μ' => r = (L.choose k : ℤ) ∧
        Seg μ' dst (output L k pref) ∧ SameOutside μ μ' dst (L.choose k)) :=
  meets rfl hw hspace hword L k pref dst μ hL hk hprefix hdst hpowers d hd

end ThreeSum.LightSubsetEnumeration
