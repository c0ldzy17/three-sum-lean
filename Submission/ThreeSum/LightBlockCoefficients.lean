import Submission.ThreeSum.LightScaleArray
import Submission.ThreeSum.LightSubsetAddress
import Submission.ThreeSum.BlockIndex

/-!
# Constructing the positional one-hot coefficient arrays

The program reads one map occurrence per block. It copies both symbol rows
of that map and multiplies them by the block's radix power. The powers are
built internally. All original map and occurrence data are preserved.
-/

namespace ThreeSum.LightBlockCoefficients

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

variable {lim : Limits} {P : Program}

def Powers (μ : ℕ → ℤ) (work J p : ℕ) : Prop :=
  ∀ i ≤ J, μ (work+i) = ((p^i : ℕ) : ℤ)

def Rows (μ : ℕ → ℤ) (dst0 dst1 L p : ℕ) (sel : ℕ → ℕ)
    (w0 w1 : ℕ → ℕ → ℕ) (j : ℕ) : Prop :=
  ∀ a < j, ∀ i < L,
    μ (dst0+a*L+i) = ((p^a*w0 (sel a) i : ℕ) : ℤ) ∧
    μ (dst1+a*L+i) = ((p^a*w1 (sel a) i : ℕ) : ℤ)

def roundBody (pScale : ℕ) : Stmt :=
  .set 9 (v 4 +' k 2 *' v 1 *' M (v 3 +' v 8)) ;;
  .set 10 (v 5 +' v 8 *' v 1) ;;
  .set 11 (v 6 +' v 8 *' v 1) ;;
  .call pScale [v 9,v 10,v 1,M (v 7 +' v 8)] 12 ;;
  .call pScale [v 9 +' v 1,v 11,v 1,M (v 7 +' v 8)] 13

/-- Arguments: number of blocks, block width, radix, occurrence array,
map-coefficient array, output-zero row, output-one row, scratch. -/
def body (pPowers pScale : ℕ) : Stmt :=
  .call pPowers [v 7,v 0 +' k 1,v 2] 8 ;;
  .for 8 (v 0) (roundBody pScale)

def roundTime (L : ℕ) : ℕ := 2*LightScaleArray.time L+100
def time (J L : ℕ) : ℕ := powTableTime (J+1)+J*(roundTime L+20)+100
def word (J p U : ℕ) : ℕ := p^(J+1)*(U+1)

def Inv (μ : ℕ → ℤ) (J L p occ maps dst0 dst1 work : ℕ)
    (sel : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ (s a b r0 r1 : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [J,L,p,occ,maps,dst0,dst1,work,j,s,a,b,r0,r1],ν⟩ ∧
    Rows ν dst0 dst1 L p sel w0 w1 j ∧ Kept μ ν dst0 ∧ Powers ν work J p

theorem row_end_le {J L j : ℕ} (hj : j < J) : j*L+L ≤ J*L := by
  calc
    j*L+L = (j+1)*L := by ring
    _ ≤ J*L := Nat.mul_le_mul_right L (by omega)

theorem map_end_le {M L s : ℕ} (hs : s < M) : 2*L*s+L+L ≤ 2*L*M := by
  calc
    2*L*s+L+L = 2*L*(s+1) := by ring
    _ ≤ 2*L*M := Nat.mul_le_mul_left (2*L) (by omega)

theorem meets {pMain pPowers pScale : ℕ}
    (hmain : P[pMain]? = some (body pPowers pScale))
    (hpowers : P[pPowers]? = some powTableBody)
    (hscale : P[pScale]? = some LightScaleArray.body)
    {μ : ℕ → ℤ} {J L p occ maps dst0 dst1 work U M d : ℕ}
    (sel : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p)
    (hocc : occ+J ≤ dst0) (hmaps : maps+2*L*M ≤ dst0)
    (hdst0 : dst0+J*L ≤ dst1) (hdst1 : dst1+J*L ≤ work)
    (hspace : work+(J+1) ≤ lim.space)
    (hword : (word J p U : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsel : ∀ j < J, sel j < M)
    (hselRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hread0 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+i) = (w0 s i : ℤ))
    (hread1 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+L+i) = (w1 s i : ℤ))
    (hbound0 : ∀ s < M, ∀ i < L, w0 s i ≤ U)
    (hbound1 : ∀ s < M, ∀ i < L, w1 s i ≤ U) :
    Meets lim P pMain d [J,L,p,occ,maps,dst0,dst1,work] μ (time J L)
      (fun _ ν => Rows ν dst0 dst1 L p sel w0 w1 J ∧
        Kept μ ν dst0 ∧ Powers ν work J p) := by
  have hpw : ∀ i ≤ J+1, ((p^i : ℕ) : ℤ) ≤ lim.word := by
    intro i hi
    have hh : p^i ≤ word J p U :=
      (Nat.pow_le_pow_right hp hi).trans (Nat.le_mul_of_pos_right _ (by omega))
    exact (by exact_mod_cast hh : ((p^i : ℕ) : ℤ) ≤ (word J p U : ℤ)).trans hword
  have hpb : (p : ℤ) ≤ lim.word := by simpa using hpw 1 (by omega)
  apply Meets.of_body hmain
  unfold body time
  have hpCall := powTable_meets (d := d+1) (μ := μ) (dst := work)
    (L := J+1) (b := p) hpowers hw hspace hpw
  light_call hpCall using powTableTime,roundTime,LightScaleArray.time
    with rPow ν₀ ⟨hpow,hkeep₀⟩
  refine Ends.for (Inv μ J L p occ maps dst0 dst1 work sel w0 w1)
    J (roundTime L) ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,0,0,0,0,ν₀,?_,?_,?_,?_⟩
    · simp [update_frame_setLocal]
      change frame [(J : ℤ),L,p,occ,maps,dst0,dst1,work,0] =
        frame ([(J : ℤ),L,p,occ,maps,dst0,dst1,work,0] ++ [0,0,0,0,0])
      exact (frame_append_zeros _ 5).symm
    · intro a ha
      omega
    · intro a ha
      exact hkeep₀ a (Or.inl (by omega))
    · intro i hi
      have hh := hpow i (by simp; omega)
      simpa only [getElem_powList] using hh
  case round =>
    rintro j _ hj _ ⟨s,a,b,r0,r1,ν,rfl,hrows,hkept,hpows⟩
    have hs := hsel j hj
    have hme := map_end_le (L := L) hs
    have hre := row_end_le (L := L) hj
    have htwo : 2*L ≤ lim.space :=
      (Nat.le_mul_of_pos_right (2*L) (by omega : 0 < M)).trans (by omega)
    have hprod : 2*(L : ℤ)*(sel j : ℤ) ≤ lim.word := by
      have hh : 2*L*sel j ≤ lim.space := by omega
      exact (by exact_mod_cast hh : 2*(L : ℤ)*(sel j : ℤ) ≤ lim.space).trans hw
    have hprodNonneg : 0 ≤ 2*(L : ℤ)*(sel j : ℤ) := by positivity
    have haddrWord : (maps : ℤ)+2*(L : ℤ)*(sel j : ℤ) ≤ lim.word := by
      have hh : maps+2*L*sel j ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (maps : ℤ)+2*(L : ℤ)*(sel j : ℤ) ≤ lim.space).trans hw
    have haddrEndWord : (maps : ℤ)+2*(L : ℤ)*(sel j : ℤ)+(L : ℤ)+(L : ℤ) ≤ lim.word := by
      have hh : maps+2*L*sel j+L+L ≤ lim.space := by omega
      exact (by exact_mod_cast hh :
        (maps : ℤ)+2*(L : ℤ)*(sel j : ℤ)+(L : ℤ)+(L : ℤ) ≤ lim.space).trans hw
    have hrowProd : (j : ℤ)*(L : ℤ) ≤ lim.word := by
      have hh : j*L ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (j : ℤ)*(L : ℤ) ≤ lim.space).trans hw
    have hrowNonneg : 0 ≤ (j : ℤ)*(L : ℤ) := by positivity
    have hselection : ν (occ+j) = (sel j : ℤ) :=
      (hkept _ (by omega)).trans (hselRead j hj)
    have hpower := hpows j (by omega)
    have hread0' : ∀ i < L, ν (maps+2*L*sel j+i) = (w0 (sel j) i : ℤ) := by
      intro i hi
      exact (hkept _ (by omega)).trans (hread0 _ hs i hi)
    have hread1' : ∀ i < L, ν (maps+2*L*sel j+L+i) = (w1 (sel j) i : ℤ) := by
      intro i hi
      exact (hkept _ (by omega)).trans (hread1 _ hs i hi)
    have hv0 : ∀ i < L, |(p^j : ℕ)*ν (maps+2*L*sel j+i)| ≤ lim.word := by
      intro i hi
      rw [hread0' i hi]
      have hh : p^j*w0 (sel j) i ≤ word J p U :=
        Nat.mul_le_mul (Nat.pow_le_pow_right hp (by omega))
          ((hbound0 _ hs i hi).trans (Nat.le_succ U))
      have hz : (((p^j*w0 (sel j) i : ℕ) : ℤ)) ≤ lim.word :=
        (by exact_mod_cast hh : ((p^j*w0 (sel j) i : ℕ) : ℤ) ≤ (word J p U : ℤ)).trans hword
      simpa only [Nat.cast_mul,abs_mul,abs_of_nonneg (Int.natCast_nonneg _),Int.abs_natCast] using hz
    unfold roundBody roundTime
    light_set (maps+2*L*sel j : ℕ) using hselection,LightScaleArray.time
    light_set (dst0+j*L : ℕ) using LightScaleArray.time
    light_set (dst1+j*L : ℕ) using LightScaleArray.time
    have hcall0 := LightScaleArray.meets (d := d+1) (src := maps+2*L*sel j)
      (dst := dst0+j*L) (n := L) (c := (p^j : ℕ)) hscale hw (by omega) (by omega)
      (Or.inr (Or.inl (by omega))) hv0
    light_call hcall0 using hpower,LightScaleArray.time with q0 ν₁ ⟨hout0,hkeep0⟩
    have hpower₁ : ν₁ (work+j) = ((p^j : ℕ) : ℤ) :=
      (hkeep0 _ (Or.inr (by omega))).trans hpower
    have hread1'' : ∀ i < L, ν₁ (maps+2*L*sel j+L+i) = (w1 (sel j) i : ℤ) := by
      intro i hi
      exact (hkeep0 _ (Or.inl (by omega))).trans (hread1' i hi)
    have hv1 : ∀ i < L, |(p^j : ℕ)*ν₁ (maps+2*L*sel j+L+i)| ≤ lim.word := by
      intro i hi
      rw [hread1'' i hi]
      have hh : p^j*w1 (sel j) i ≤ word J p U :=
        Nat.mul_le_mul (Nat.pow_le_pow_right hp (by omega))
          ((hbound1 _ hs i hi).trans (Nat.le_succ U))
      have hz : (((p^j*w1 (sel j) i : ℕ) : ℤ)) ≤ lim.word :=
        (by exact_mod_cast hh : ((p^j*w1 (sel j) i : ℕ) : ℤ) ≤ (word J p U : ℤ)).trans hword
      simpa only [Nat.cast_mul,abs_mul,abs_of_nonneg (Int.natCast_nonneg _),Int.abs_natCast] using hz
    have hcall1 := LightScaleArray.meets (d := d+1) (src := maps+2*L*sel j+L)
      (dst := dst1+j*L) (n := L) (c := (p^j : ℕ)) hscale hw (by omega) (by omega)
      (Or.inr (Or.inl (by omega))) hv1
    light_call hcall1 using hpower₁,LightScaleArray.time with q1 ν₂ ⟨hout1,hkeep1⟩
    refine ⟨by simp,((maps+2*L*sel j : ℕ) : ℤ),((dst0+j*L : ℕ) : ℤ),
      ((dst1+j*L : ℕ) : ℤ),q0,q1,ν₂,?_,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro a ha i hi
      by_cases haj : a = j
      · subst a
        constructor
        · rw [hkeep1 _ (Or.inl (by omega)),hout0 i hi,hread0' i hi,Nat.cast_mul]
        · simpa only [Nat.cast_mul] using (hout1 i hi).trans (by rw [hread1'' i hi])
      · have hal : a < j := by omega
        have he : a*L+i < j*L := by
          have hh := row_end_le (L := L) hal
          omega
        constructor
        · exact (hkeep1 _ (Or.inl (by omega))).trans
            ((hkeep0 _ (Or.inl (by omega))).trans (hrows a hal i hi).1)
        · exact (hkeep1 _ (Or.inl (by omega))).trans
            ((hkeep0 _ (Or.inr (by omega))).trans (hrows a hal i hi).2)
    · intro a ha
      exact (hkeep1 _ (Or.inl (by omega))).trans
        ((hkeep0 _ (Or.inl (by omega))).trans (hkept a ha))
    · intro a ha
      exact (hkeep1 _ (Or.inr (by omega))).trans
        ((hkeep0 _ (Or.inr (by omega))).trans (hpows a ha))
  case done =>
    rintro _ _ ⟨s,a,b,r0,r1,ν,rfl,hrows,hkept,hpows⟩
    exact ⟨hrows,hkept,hpows⟩
  case bound =>
    rintro j _ hj _ ⟨s,a,b,r0,r1,ν,rfl,_,_,_⟩
    light_side

def program : Program := [body 1 2,powTableBody,LightScaleArray.body]

theorem program_meets {μ : ℕ → ℤ} {J L p occ maps dst0 dst1 work U M d : ℕ}
    (sel : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p)
    (hocc : occ+J ≤ dst0) (hmaps : maps+2*L*M ≤ dst0)
    (hdst0 : dst0+J*L ≤ dst1) (hdst1 : dst1+J*L ≤ work)
    (hspace : work+(J+1) ≤ lim.space)
    (hword : (word J p U : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsel : ∀ j < J, sel j < M)
    (hselRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hread0 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+i) = (w0 s i : ℤ))
    (hread1 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+L+i) = (w1 s i : ℤ))
    (hbound0 : ∀ s < M, ∀ i < L, w0 s i ≤ U)
    (hbound1 : ∀ s < M, ∀ i < L, w1 s i ≤ U) :
    Meets lim program 0 d [J,L,p,occ,maps,dst0,dst1,work] μ (time J L)
      (fun _ ν => Rows ν dst0 dst1 L p sel w0 w1 J ∧
        Kept μ ν dst0 ∧ Powers ν work J p) :=
  meets rfl rfl rfl sel w0 w1 hw hp hocc hmaps hdst0 hdst1 hspace hword hd
    hsel hselRead hread0 hread1 hbound0 hbound1

theorem time_bound (J L : ℕ) : time J L ≤ 300*(J+1)*(L+1) := by
  unfold time roundTime LightScaleArray.time powTableTime
  nlinarith

end ThreeSum.LightBlockCoefficients
