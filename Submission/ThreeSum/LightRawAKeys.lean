import Submission.ThreeSum.LightResidues
import Submission.ThreeSum.LightReportingAffine
import Submission.ThreeSum.RawAKeyLists

/-!
# Actual construction of the three lifted original A-key arrays

The middle row is computed by the checked signed remainder routine. Two
affine scans append the minus and plus lifts. Every original position is
retained in each row, and the resulting segment is the exact guarded-key
list whose balancing bound is proved in `RawAKeyLists`.
-/

namespace ThreeSum.LightRawAKeys

open Light LightResidues RawIncidences RawAKeyLists

set_option maxHeartbeats 1000000
set_option maxRecDepth 6000

/-- Original array, length, modulus, and first free address. -/
def body (pResidues pAffine : ℕ) : Stmt :=
  .set 4 (v 3 +' k 3 *' v 1) ;;
  .call pResidues [v 0,v 3 +' v 1,v 1,v 2,v 4,k 1] 5 ;;
  .call pAffine [v 3 +' v 1,v 3,v 1,k 0 -' v 2,k 1] 5 ;;
  .call pAffine [v 3 +' v 1,v 3 +' k 2 *' v 1,v 1,v 2,k 1] 5 ;;
  .set 0 (v 3)

def time (n U : ℕ) : ℕ := residuesTime n U+2*LightReportingAffine.time n+150
def space (free n U : ℕ) : ℕ := free+3*n+Nat.log 2 (U+1)+2
def word (p U : ℕ) : ℕ := 4*U+4*p+16

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pResidues pAffine pEmod src free p U : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some (body pResidues pAffine))
    (hres : P[pResidues]? = some (residuesBody pEmod))
    (haff : P[pAffine]? = some LightReportingAffine.body)
    (hem : P[pEmod]? = some emodBody) (xs : List ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p)
    (hsrc : src+xs.length ≤ free)
    (hspace : space free xs.length U ≤ lim.space)
    (hword : (word p U : ℤ) ≤ lim.word) (hd : d+2 ≤ lim.depth)
    (hread : Seg μ src xs) (hvalues : ∀ x ∈ xs, |x| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,xs.length,p,free] μ (time xs.length U)
      (fun r ν => r=(free : ℤ) ∧ Seg ν free (keys p xs) ∧ Kept μ ν free) := by
  let n := xs.length
  let work := free+3*n
  have hs : free+3*n+Nat.log 2 (U+1)+2 ≤ lim.space := hspace
  have hew : (4*U+4*p+16 : ℤ) ≤ lim.word := by
    simpa only [word,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hword
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hpw : 2*(p : ℤ) ≤ lim.word := by omega
  have horiginal (i : ℕ) (hi : i < n) : μ (src+i)=xs.getD i 0 := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hread i hi
  have hremNonneg (i : ℕ) : (0 : ℤ) ≤ xs.getD i 0%(p : ℤ) :=
    Int.emod_nonneg _ hpz.ne'
  have hremLt (i : ℕ) : xs.getD i 0%(p : ℤ) < (p : ℤ) :=
    Int.emod_lt_of_pos _ hpz
  apply Meets.of_body hmain
  unfold body time
  light_set (work : ℕ) using work,n,LightReportingAffine.time
  have hr := residues_meets (d := d+1) (μ := μ) (src := src) (dst := free+n)
    (work := work) (n := n) (p := p) (U := U) (c := 1) hres hem hw (by omega) hp
    (by dsimp [work]; omega) (by dsimp [work]; omega) (by dsimp [work]; omega)
    (by left; omega) (by norm_num) hew
    (fun i hi => by rw [horiginal i hi,List.getD_eq_getElem _ _ hi]; exact hvalues _ (List.getElem_mem hi))
  light_call hr using n,LightReportingAffine.time with vr μ₁ ⟨hresValues,hkeep₁⟩
  have hmid (i : ℕ) (hi : i < n) : μ₁ (free+n+i)=xs.getD i 0%(p : ℤ) := by
    rw [hresValues i hi,residue_cast hp,one_mul,horiginal i hi]
  have hl := LightReportingAffine.meets (d := d+1) (μ := μ₁) (src := free+n) (dst := free)
    (n := n) (b := -(p : ℤ)) (c := 1) haff hw (by omega) (by omega)
    (by right; right; omega)
    (fun i hi => by rw [one_mul,hmid i hi,abs_of_nonneg (hremNonneg i)]; have hh := hremLt i; omega)
    (fun i hi => by rw [one_mul,hmid i hi]; apply abs_le.mpr; have h0 := hremNonneg i; have h1 := hremLt i; constructor <;> omega)
  light_call hl using n,LightReportingAffine.time with vl μ₂ ⟨hleft,hkeep₂⟩
  have hmid₂ (i : ℕ) (hi : i < n) : μ₂ (free+n+i)=xs.getD i 0%(p : ℤ) := by
    rw [hkeep₂ _ (Or.inr (by omega)),hmid i hi]
  have hr := LightReportingAffine.meets (d := d+1) (μ := μ₂) (src := free+n) (dst := free+2*n)
    (n := n) (b := (p : ℤ)) (c := 1) haff hw (by omega) (by omega)
    (by right; left; omega)
    (fun i hi => by rw [one_mul,hmid₂ i hi,abs_of_nonneg (hremNonneg i)]; have hh := hremLt i; omega)
    (fun i hi => by rw [one_mul,hmid₂ i hi]; apply abs_le.mpr; have h0 := hremNonneg i; have h1 := hremLt i; constructor <;> omega)
  light_call hr using n,LightReportingAffine.time with vp μ₃ ⟨hright,hkeep₃⟩
  light_set (free : ℕ) using n,LightReportingAffine.time
  refine ⟨rfl,?_,?_⟩
  · rw [keys_eq_liftRows]
    apply LocalKeyArraySemantics.seg_flatMap_rows _ _ n free
      (fun j hj => by simp only [List.length_map]; rfl)
    intro j hj i hi
    have hj3 : j < 3 := by simpa only [List.length_finRange] using hj
    rw [List.getElem_map]
    have hget : xs[i]=xs.getD i 0 := (List.getD_eq_getElem _ _ hi).symm
    have hcases : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp only [Nat.zero_mul,Nat.add_zero]
      change μ₃ (free+i)=xs[i]%(p : ℤ)+lift (0 : Fin 3)*(p : ℤ)
      rw [hget,show lift (0 : Fin 3) = -1 from rfl,neg_one_mul]
      rw [hkeep₃ _ (Or.inl (by omega)),hleft i hi,one_mul,hmid i hi]
      omega
    · simp only [Nat.one_mul]
      change μ₃ (free+n+i)=xs[i]%(p : ℤ)+lift (1 : Fin 3)*(p : ℤ)
      rw [hget,show lift (1 : Fin 3) = 0 from rfl,zero_mul,add_zero]
      rw [hkeep₃ _ (Or.inl (by omega)),hmid₂ i hi]
    · change μ₃ (free+2*n+i)=xs[i]%(p : ℤ)+lift (2 : Fin 3)*(p : ℤ)
      rw [hget,show lift (2 : Fin 3) = 1 from rfl,one_mul,hright i hi,one_mul,hmid₂ i hi]
      omega
  · intro a ha
    change μ₃ a=μ a
    rw [hkeep₃ _ (Or.inl (by omega)),hkeep₂ _ (Or.inl ha),
      hkeep₁ _ ⟨by dsimp [work]; omega,Or.inl (by omega)⟩]

def program : Program := [body 1 2,residuesBody 3,LightReportingAffine.body,emodBody]

theorem program_meets {src free p U : ℕ} {μ : ℕ → ℤ} (xs : List ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p)
    (hsrc : src+xs.length ≤ free)
    (hspace : space free xs.length U ≤ lim.space)
    (hword : (word p U : ℤ) ≤ lim.word) (hd : d+2 ≤ lim.depth)
    (hread : Seg μ src xs) (hvalues : ∀ x ∈ xs, |x| ≤ (U : ℤ)) :
    Meets lim program 0 d [src,xs.length,p,free] μ (time xs.length U)
      (fun r ν => r=(free : ℤ) ∧ Seg ν free (keys p xs) ∧ Kept μ ν free) :=
  meets rfl rfl rfl rfl xs hw hp hsrc hspace hword hd hread hvalues

theorem time_bound (n U : ℕ) : time n U ≤ 220*(n+1)*(Nat.log 2 (U+1)+1) := by
  unfold time residuesTime residueBudget LightReportingAffine.time
  nlinarith

end ThreeSum.LightRawAKeys
