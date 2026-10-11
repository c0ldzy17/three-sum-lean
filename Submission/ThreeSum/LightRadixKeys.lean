import Submission.ThreeSum.LightRadixRows

/-!
# Complete positional-key product construction

The three fixed procedures build every product stage. Each stage has a
computed length header followed by its literal key array. The recursive
caller reads the previous header and appends Cartesian rows. Its final
array contains every record sequence, retaining repeated keys.
-/

namespace ThreeSum.LightRadixKeys

open Light RadixKeyLists

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def offset (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => offset m j+1+m^j

theorem le_offset (m j : ℕ) : j ≤ offset m j := by
  induction j with
  | zero => simp [offset]
  | succ j ih => rw [offset]; omega

def space (dst m j : ℕ) : ℕ := dst+offset m j+1+m^j
def word (p U j : ℕ) : ℕ := LightRadixRows.word p U (U*(p+1)^j)

def time (m : ℕ) : ℕ → ℕ
  | 0 => 50
  | j+1 => time m j+LightRadixRows.time m (m^j)+200

theorem space_step (dst m j : ℕ) : space dst m j ≤ space dst m (j+1) := by
  unfold space
  rw [offset]
  omega

theorem word_mono {p U j k : ℕ} (hj : j ≤ k) : word p U j ≤ word p U k := by
  have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ p+1) hj
  have hv := Nat.mul_le_mul_left U hpow
  have hpv := Nat.mul_le_mul_left p hv
  unfold word LightRadixRows.word
  omega

theorem space_bound (dst m J : ℕ) (hm : 1 ≤ m) :
    space dst m J ≤ dst+(J+1)*(m^J+1) := by
  have haux : ∀ j, j ≤ J → offset m j ≤ j*(m^J+1) := by
    intro j
    induction j with
    | zero => simp [offset]
    | succ j ih =>
      intro hj
      have hh := ih (by omega)
      have hp := Nat.pow_le_pow_right hm (show j ≤ J by omega)
      rw [offset]
      nlinarith
  have hh := haux J le_rfl
  unfold space
  nlinarith

theorem time_bound (m J : ℕ) (hm : 1 ≤ m) :
    time m J ≤ 300*(J+1)*(m^J+1) := by
  have haux : ∀ j, j ≤ J → time m j ≤ 50+j*(130*m^J+220) := by
    intro j
    induction j with
    | zero => simp [time]
    | succ j ih =>
      intro hj
      have ht := ih (by omega)
      have hr := LightRadixRows.time_bound_product m (m^j) (Nat.pow_pos (by omega))
      have hp := Nat.pow_le_pow_right hm hj
      rw [pow_succ'] at hp
      have hp' := Nat.mul_le_mul_left 130 hp
      rw [time]
      nlinarith
  have hh := haux J le_rfl
  have he : 300*(J+1)*(m^J+1) =
      50+J*(130*m^J+220)+(170*J*m^J+80*J+300*m^J+250) := by ring
  rw [he]
  omega

/-- Source local keys and count, product length, radix, first output cell. -/
def body (pSelf pRows : ℕ) : Stmt :=
  .ite (k 0 <' v 2)
    (.call pSelf [v 0,v 1,v 2 -' k 1,v 3,v 4] 5 ;;
      .set 6 (M (v 5)) ;;
      .set 7 (v 5 +' k 1 +' v 6) ;;
      .store (v 7) (v 1 *' v 6) ;;
      .call pRows [v 0,v 5 +' k 1,v 7 +' k 1,v 1,v 6,v 3] 8 ;;
      .set 0 (v 7))
    (.store (v 4) (k 1) ;; .store (v 4 +' k 1) (k 0) ;; .set 0 (v 4))

variable {lim : Limits} {P : Program}

theorem meets {pMain pRows pAffine src dst p U : ℕ}
    (hmain : P[pMain]? = some (body pMain pRows))
    (hrows : P[pRows]? = some (LightRadixRows.body pAffine))
    (haffine : P[pAffine]? = some LightReportingAffine.body)
    (base : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+base.length ≤ dst) (hm : 0 < base.length)
    (hbound : ∀ x ∈ base, |x| ≤ (U : ℤ)) :
    ∀ J d : ℕ, ∀ μ : ℕ → ℤ,
      space dst base.length J ≤ lim.space → (word p U J : ℤ) ≤ lim.word →
      d+J+2 ≤ lim.depth → Seg μ src base →
      Meets lim P pMain d [src,base.length,J,p,dst] μ (time base.length J)
        (fun r ν => r = ((dst+offset base.length J : ℕ) : ℤ) ∧
          ν (dst+offset base.length J) = ((base.length^J : ℕ) : ℤ) ∧
          Seg ν (dst+offset base.length J+1) (values (p : ℤ) base J) ∧ Kept μ ν dst) := by
  intro J
  induction J with
  | zero =>
    intro d μ hspace hword hd hread
    have hs : dst+2 ≤ lim.space := by
      simp only [space,offset,pow_zero,Nat.add_zero] at hspace
      omega
    apply Meets.of_body hmain
    unfold body time
    refine Ends.iteLast (fun h => False.elim (by simpa using h)) (fun _ => ?_)
    light_store dst (1 : ℕ)
    light_store (dst+1) (0 : ℕ)
    light_set (dst : ℕ)
    refine ⟨by simp [offset],?_,?_,?_⟩
    · simp [offset,Function.update_of_ne (by omega : dst ≠ dst+1)]
    · simp [values,offset,seg_cons]
    · intro a ha
      simp only [State.mem]
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
  | succ J ih =>
    intro d μ hspace hword hd hread
    let old := dst+offset base.length J
    let next := old+1+base.length^J
    have hnext : next = dst+offset base.length (J+1) := by dsimp [next,old,offset]; omega
    have hs : next+1+base.length^(J+1) ≤ lim.space := by rw [hnext]; exact hspace
    have hJ : J+1 ≤ offset base.length (J+1) := le_offset _ _
    have hn : 0 < base.length^J := Nat.pow_pos hm
    have hrowWord : (LightRadixRows.word p U (U*(p+1)^J) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (word_mono (p := p) (U := U) (Nat.le_succ J))).trans hword
    have hpWord : (p : ℤ) ≤ lim.word := by
      exact (Int.ofNat_le.mpr (show p ≤ word p U (J+1) by
        unfold word LightRadixRows.word; omega)).trans hword
    have hprod : (base.length : ℤ)*((base.length^J : ℕ) : ℤ) ≤ lim.word := by
      have hh : base.length*base.length^J ≤ lim.space := by rw [← pow_succ']; omega
      exact (by exact_mod_cast hh : (base.length : ℤ)*((base.length^J : ℕ) : ℤ) ≤ lim.space).trans hw
    apply Meets.of_body hmain
    unfold body time
    refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simp at h))
    light_call (ih (d+1) μ ((space_step dst base.length J).trans hspace)
      hrowWord (by omega) hread) using LightRadixRows.time,LightReportingAffine.time
      with r ν₀ ⟨hresult,hheader,hprev,hkeep₀⟩
    have hr : r = (old : ℤ) := hresult
    have hh : ν₀ old = ((base.length^J : ℕ) : ℤ) := hheader
    have hpowerNonneg : (0 : ℤ) ≤ (base.length : ℤ)^J := by positivity
    have hprodInt : (base.length : ℤ)*(base.length : ℤ)^J ≤ lim.word := by
      simpa only [Nat.cast_pow] using hprod
    have hprodNonneg : (0 : ℤ) ≤ (base.length : ℤ)*(base.length : ℤ)^J := by positivity
    have hnextWord : (old : ℤ)+1+(base.length : ℤ)^J ≤ lim.word := by
      have hnat : next ≤ lim.space := by omega
      simpa only [next,Nat.cast_add,Nat.cast_one,Nat.cast_pow] using
        (Int.ofNat_le.mpr hnat).trans hw
    light_set (base.length^J : ℕ) using hr,hh,LightRadixRows.time,LightReportingAffine.time
    light_set (next : ℕ) using hr,hh,next,LightRadixRows.time,LightReportingAffine.time
    light_store next (base.length^(J+1) : ℕ) using pow_succ',LightRadixRows.time,LightReportingAffine.time
    let ν₁ := Function.update ν₀ next ((base.length^(J+1) : ℕ) : ℤ)
    have hprev₁ : Seg ν₁ (old+1) (values (p : ℤ) base J) := by
      apply hprev.update_out
      right
      rw [values_length]
    have hbase₁ : Seg ν₁ src base := by
      intro i hi
      change Function.update ν₀ next _ (src+i) = _
      rw [Function.update_of_ne (by dsimp [next,old]; omega),hkeep₀ _ (by omega)]
      exact hread i hi
    have hsRows : next+1+base.length*(values (p : ℤ) base J).length ≤ lim.space := by
      rw [values_length,← pow_succ']
      exact hs
    have hc := LightRadixRows.meets (d := d+1) (μ := ν₁) (srcBase := src)
      (srcPrev := old+1) (dst := next+1) (p := p) (U := U) (V := U*(p+1)^J)
      hrows haffine base (values (p : ℤ) base J) hw (by dsimp [next,old]; omega)
      (by rw [values_length]; dsimp [next]; omega) hsRows hrowWord (by omega)
      hbase₁ hprev₁ hbound (values_bounded p U base hbound J)
    simp only [values_length] at hc
    light_call hc using values_length,hr,LightRadixRows.time,LightReportingAffine.time
      with result ν₂ ⟨hvalues,hkeep₁⟩
    light_set (next : ℕ) using LightRadixRows.time,LightReportingAffine.time
    refine ⟨by simp [hnext],?_,?_,?_⟩
    · change ν₂ (dst+offset base.length (J+1)) = _
      rw [← hnext,hkeep₁ _ (Or.inl (by omega))]
      exact Function.update_self ..
    · change Seg ν₂ (dst+offset base.length (J+1)+1) _
      rw [← hnext]
      exact hvalues
    · intro a ha
      change ν₂ a = μ a
      rw [hkeep₁ _ (Or.inl (by dsimp [next,old]; omega))]
      change Function.update ν₀ next _ a = μ a
      rw [Function.update_of_ne (by dsimp [next,old]; omega)]
      exact hkeep₀ a ha

def program : Program := [body 0 1,LightRadixRows.body 2,LightReportingAffine.body]

theorem program_meets {src dst p U J d : ℕ} {μ : ℕ → ℤ}
    (base : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+base.length ≤ dst) (hm : 0 < base.length)
    (hbound : ∀ x ∈ base, |x| ≤ (U : ℤ))
    (hspace : space dst base.length J ≤ lim.space) (hword : (word p U J : ℤ) ≤ lim.word)
    (hd : d+J+2 ≤ lim.depth) (hread : Seg μ src base) :
    Meets lim program 0 d [src,base.length,J,p,dst] μ (time base.length J)
      (fun r ν => r = ((dst+offset base.length J : ℕ) : ℤ) ∧
        ν (dst+offset base.length J) = ((base.length^J : ℕ) : ℤ) ∧
        Seg ν (dst+offset base.length J+1) (values (p : ℤ) base J) ∧ Kept μ ν dst) :=
  meets rfl rfl rfl base hw hsrc hm hbound J d μ hspace hword hd hread

end ThreeSum.LightRadixKeys
