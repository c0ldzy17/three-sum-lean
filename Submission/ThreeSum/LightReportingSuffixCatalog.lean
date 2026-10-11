import Submission.ThreeSum.LightReportingSuffixSetup
import Submission.ThreeSum.ReportingHostQueryBounds

/-!
# Actual construction of a contiguous suffix-box catalog

Each input record is a physical pair of global prefix masks. The host invokes
complete suffix-local setup for every record, writes the corresponding table
pointer, and retains every previous table. The table stride is the exact
local-width storage size; the following setup host computes it explicitly.
-/

namespace ThreeSum.LightReportingSuffixCatalog

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix ReportingHostQueryBounds

set_option maxHeartbeats 1800000

variable {lim : Limits}

def stride (V cut : ℕ) : ℕ := (V+1)*downsetCap V cut

def roundBody (pSetup : ℕ) : Stmt :=
  .set 19 (M (v 10 +' v 18)) ;;
  .set 20 (M (v 11 +' v 18)) ;;
  .set 21 (v 14 +' v 18 *' v 15) ;;
  .call pSetup [v 0,v 1,v 2,v 3,v 4,v 19,v 5,v 20,v 6,v 7,v 8,v 9,v 21,v 16,v 17] 22 ;;
  .store (v 13 +' v 18) (v 21)

def body (pSetup : ℕ) : Stmt := .for 18 (v 12) (roundBody pSetup)

def program : Program := LightReportingSuffixSetup.program ++ [body 29]

def time (W V cut offset n : ℕ) : ℕ := n*(LightReportingSuffixSetup.time W V cut offset+200)+30

def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ)
    (preL preR : ℕ → Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (cut boxCut stage cL cR baseL baseR inL inR n ptrBase boxBase maskBase work j : ℕ)
    (σ : State) : Prop :=
  ∃ (a b addr r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,cut,boxCut,stage,cL,cR,V,offset,baseL,baseR,inL,inR,n,
      ptrBase,boxBase,stride V boxCut,maskBase,work,j,a,b,addr,r],μ'⟩ ∧
    (∀ i < j, μ' (ptrBase+i) = (boxBase+i*stride V boxCut : ℤ)) ∧
    (∀ i < j, LightBoxStages.StoredThrough μ' (boxBase+i*stride V boxCut) boxCut
      (leafWeight hfit f g stage (preL i) (preR i)) V) ∧
    Kept μ μ' ptrBase

theorem program_meets
    {μ : ℕ → ℤ} {W V offset cut boxCut stage cL cR baseL baseR inL inR n ptrBase boxBase maskBase work B D d : ℕ}
    (hfit : offset+V ≤ W) (preL preR : ℕ → Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hboxCut : boxCut ≤ V) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ ptrBase)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ ptrBase)
    (hinL : inL+n ≤ ptrBase) (hinR : inR+n ≤ ptrBase)
    (hptr : ptrBase+n ≤ boxBase) (hbox : boxBase+n*stride V boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap V boxCut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^V*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hcardL : ∀ i < n, (preL i).card = cL) (hcardR : ∀ i < n, (preR i).card = cR)
    (hpreL : cL+boxCut ≤ cut) (hpreR : cR+boxCut ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B) (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hreadL : ∀ i < n, μ (inL+i) = (subsetMask (preL i) : ℤ))
    (hreadR : ∀ i < n, μ (inR+i) = (subsetMask (preR i) : ℤ))
    (hd : d+W+12 ≤ lim.depth) :
    Meets lim program 30 d
      [W,cut,boxCut,stage,cL,cR,V,offset,baseL,baseR,inL,inR,n,
        ptrBase,boxBase,stride V boxCut,maskBase,work]
      μ (time W V boxCut offset n)
      (fun _ μ' =>
        SegN μ' ptrBase (List.ofFn fun i : Fin n => boxBase+i.val*stride V boxCut) ∧
        (∀ i < n, LightBoxStages.StoredThrough μ' (boxBase+i*stride V boxCut) boxCut
          (leafWeight hfit f g stage (preL i) (preR i)) V) ∧
        LightZetaStages.StoredThrough μ' baseL cut f W ∧
        LightZetaStages.StoredThrough μ' baseR cut g W ∧
        Kept μ μ' ptrBase) := by
  have hmask (S : Finset (Fin W)) : (subsetMask S : ℤ) ≤ lim.word := by
    have hpow : (2^W : ℕ) ≤ (W+1)*2^(W+1) :=
      (Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega))
    have hs := (Nat.le_of_lt (subsetMask_isMask S).1).trans hpow
    exact (by exact_mod_cast hs : (subsetMask S : ℤ) ≤ (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body (p := 30) (by rfl : program[30]? = some (body 29))
  unfold body time
  refine Ends.for (lim := lim) (P := program) (d := d) (i := 18) (hi := v 12) (body := roundBody 29)
    (Inv hfit μ preL preR f g cut boxCut stage cL cR baseL baseR inL inR n ptrBase boxBase maskBase work)
    n (LightReportingSuffixSetup.time W V boxCut offset+160) ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,0,0,0,μ,?_,by simp,by simp,SameOn.refl⟩
    simp [update_frame_setLocal]
    change frame [(W : ℤ),cut,boxCut,stage,cL,cR,V,offset,baseL,baseR,inL,inR,n,
      ptrBase,boxBase,stride V boxCut,maskBase,work,0] =
      frame ([(W : ℤ),cut,boxCut,stage,cL,cR,V,offset,baseL,baseR,inL,inR,n,
        ptrBase,boxBase,stride V boxCut,maskBase,work,0] ++ [0,0,0,0])
    exact (frame_append_zeros _ 4).symm
  case round =>
    rintro j _ hj _ ⟨a,b,addr,r,μ',rfl,hptrs,hboxes,hkeep⟩
    have htable : boxBase+j*stride V boxCut+stride V boxCut ≤ maskBase := by
      have hm := Nat.mul_le_mul_right (stride V boxCut) (show j+1 ≤ n by omega)
      nlinarith
    have hwriteBelow : ptrBase+j < boxBase+j*stride V boxCut := by omega
    have hcl := hcardL j hj
    have hcr := hcardR j hj
    have hlread : μ' (inL+j) = (subsetMask (preL j) : ℤ) :=
      (hkeep _ (by omega)).trans (hreadL j hj)
    have hrread : μ' (inR+j) = (subsetMask (preR j) : ℤ) :=
      (hkeep _ (by omega)).trans (hreadR j hj)
    have hlword := hmask (preL j)
    have hrword := hmask (preR j)
    have hstoredL' := LightSignedLeafBatch.storedThrough_of_on hstoredL
      (by intro i _ hi; exact hkeep i (by omega))
    have hstoredR' := LightSignedLeafBatch.storedThrough_of_on hstoredR
      (by intro i _ hi; exact hkeep i (by omega))
    unfold roundBody
    light_set (subsetMask (preL j) : ℕ) using hlread,LightReportingSuffixSetup.time
    light_set (subsetMask (preR j) : ℕ) using hrread,LightReportingSuffixSetup.time
    light_set (boxBase+j*stride V boxCut : ℕ) using LightReportingSuffixSetup.time
    have hcall := (LightReportingSuffixSetup.program_meets (d := d+1) (μ := μ')
      (boxBase := boxBase+j*stride V boxCut) hfit (preL j) (preR j) f g hw hcut hboxCut hstage
      (by omega) (by omega) htable hmasks hspace hword hvalueWord
      (by simpa only [hcl] using hpreL) (by simpa only [hcr] using hpreR)
      hf hg hstoredL' hstoredR' (by omega)).append [body 29]
    rw [hcl,hcr] at hcall
    light_call hcall using LightReportingSuffixSetup.time with result ν ⟨hnew,hLs,hRs,hkeepCall⟩
    light_store (ptrBase+j) (boxBase+j*stride V boxCut : ℕ) using LightReportingSuffixSetup.time
    refine ⟨by simp,(subsetMask (preL j) : ℤ),(subsetMask (preR j) : ℤ),
      (boxBase+j*stride V boxCut : ℤ),result,
      Function.update ν (ptrBase+j) (boxBase+j*stride V boxCut : ℤ),?_,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      by_cases he : i = j
      · subst i; simp
      · rw [Function.update_of_ne (by omega),hkeepCall (ptrBase+i) ⟨by omega,Or.inl (by omega)⟩]
        exact hptrs i (by omega)
    · intro i hi
      by_cases he : i = j
      · subst i
        apply boxStored_of_on hnew
        intro x hx₀ hx₁
        exact Function.update_of_ne (Nat.ne_of_gt (hwriteBelow.trans_le hx₀)) _ _
      · have hij : i < j := by omega
        apply boxStored_of_on (hboxes i hij)
        intro x hx₀ hx₁
        rw [Function.update_of_ne (by omega)]
        apply hkeepCall x
        have hm := Nat.mul_le_mul_right (stride V boxCut) (show i+1 ≤ j by omega)
        change x < boxBase+i*stride V boxCut+stride V boxCut at hx₁
        constructor
        · nlinarith
        · exact Or.inl (by nlinarith)
    · intro i hi
      rw [Function.update_of_ne (by omega)]
      exact (hkeepCall i ⟨by omega,Or.inl (by omega)⟩).trans (hkeep i hi)
  case done =>
    rintro _ _ ⟨a,b,addr,r,μ',rfl,hptrs,hboxes,hkeep⟩
    refine ⟨?_,hboxes,?_,?_,hkeep⟩
    · intro i hi
      have hin : i < n := by simpa using hi
      simpa only [List.getElem_map,List.getElem_ofFn,Nat.cast_add,Nat.cast_mul] using hptrs i hin
    · exact LightSignedLeafBatch.storedThrough_of_on hstoredL (by intro i _ hi; exact hkeep i (by omega))
    · exact LightSignedLeafBatch.storedThrough_of_on hstoredR (by intro i _ hi; exact hkeep i (by omega))
  case bound =>
    rintro j _ hj _ ⟨a,b,addr,r,μ',rfl,_,_,_⟩
    light_side

theorem time_bound {W V cut offset n : ℕ} (hfit : offset+V ≤ W) (hcut : cut ≤ V) :
    time W V cut offset n ≤ 21000*(W+1)^4*(downsetCap V cut+1)*(n+1) := by
  have hs := LightReportingSuffixSetup.time_bound hfit hcut
  have hp : 1 ≤ (W+1)^4*(downsetCap V cut+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hm := Nat.mul_le_mul_left n hs
  unfold time
  nlinarith

end ThreeSum.LightReportingSuffixCatalog
