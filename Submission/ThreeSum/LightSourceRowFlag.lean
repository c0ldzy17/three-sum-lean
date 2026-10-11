import Submission.ThreeSum.LightSourceRowScan
import Submission.ThreeSum.LightSourceFlagTest
import Submission.ThreeSum.LightResidues

/-!
# Constructing both independent trimming flags for one block row

The program counts and hashes the actual Boolean row, reduces both local
hashes, reads the selected map's retained bucket tables, and independently
tests the two endpoint buckets. The cardinality test is performed for both
orientations, with no disjoint-pair or shared trimming assumption.
-/

namespace ThreeSum.LightSourceRowFlag

open Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def flag (L h p cap : ℕ) (bits w0 w1 hist : ℕ → ℕ) : ℕ :=
  LightSourceFlagTest.flag (LightSourceRowScan.count bits L) h
    (hist (LightResidues.residue p 1 (LightSourceRowScan.hash bits w0 w1 L : ℤ))) cap

theorem flag_le (L h p cap : ℕ) (bits w0 w1 hist : ℕ → ℕ) :
    flag L h p cap bits w0 w1 hist ≤ 1 := LightSourceFlagTest.flag_le ..

/-- Arguments: Boolean row, coefficient-zero, coefficient-one, width,
required cardinality, left and right bucket tables, local modulus, cap,
two-cell flag output, and reusable scratch. -/
def body (pRow pEmod pFlag : ℕ) : Stmt :=
  .call pRow [v 0,v 1,v 2,v 3,v 10] 11 ;;
  .call pEmod [M (v 10 +' k 1),v 7,v 10 +' k 3] 12 ;;
  .call pEmod [M (v 10 +' k 2),v 7,v 10 +' k 3] 13 ;;
  .call pFlag [M (v 10),v 4,M (v 5 +' v 12),v 8] 14 ;;
  .call pFlag [M (v 10),v 4,M (v 6 +' v 13),v 8] 15 ;;
  .store (v 9) (v 14) ;;
  .store (v 9 +' k 1) (v 15)

def time (L U : ℕ) : ℕ := LightSourceRowScan.time L+
  2*LightResidues.residueBudget (L*U)+2*LightSourceFlagTest.time+160

def word (L p U V cap : ℕ) : ℕ := LightSourceRowScan.word L U+
  4*(L*U)+4*p+16+2*L+V+cap+2

def space (work L U : ℕ) : ℕ := work+3+(Nat.log 2 (L*U+1)+2)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pRow pEmod pFlag : ℕ}
    (hmain : P[pMain]? = some (body pRow pEmod pFlag))
    (hrow : P[pRow]? = some LightSourceRowScan.body)
    (hem : P[pEmod]? = some emodBody)
    (hflag : P[pFlag]? = some LightSourceFlagTest.body)
    {μ : ℕ → ℤ} {src src0 src1 L h histL histR p cap dst work U V : ℕ}
    (bits w0 w1 leftCount rightCount : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hp : 0 < p) (hh : h ≤ L)
    (hsrc : src+L ≤ work) (hsrc0 : src0+L ≤ work) (hsrc1 : src1+L ≤ work)
    (hleft : histL+p ≤ work) (hright : histR+p ≤ work) (hdst : dst+2 ≤ work)
    (hspace : space work L U ≤ lim.space) (hword : (word L p U V cap : ℤ) ≤ lim.word)
    (hbits : ∀ i < L, μ (src+i) = (bits i : ℤ))
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbitBound : ∀ i < L, bits i ≤ 1)
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U)
    (hcountL : ∀ r < p, μ (histL+r) = (leftCount r : ℤ))
    (hcountR : ∀ r < p, μ (histR+r) = (rightCount r : ℤ))
    (hcountBoundL : ∀ r < p, leftCount r ≤ V)
    (hcountBoundR : ∀ r < p, rightCount r ≤ V) :
    Meets lim P pMain d [src,src0,src1,L,h,histL,histR,p,cap,dst,work] μ (time L U)
      (fun _ ν => ν dst = (flag L h p cap bits w0 w1 leftCount : ℤ) ∧
        ν (dst+1) = (flag L h p cap bits w1 w0 rightCount : ℤ) ∧
        KeptBut μ ν work dst 2) := by
  have hsp : work+3+(Nat.log 2 (L*U+1)+2) ≤ lim.space := hspace
  have hbudget (x : ℕ) (hx : x ≤ word L p U V cap) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hrowWord := hbudget (LightSourceRowScan.word L U) (by unfold word; omega)
  have hemWord : (4*(L*U : ℕ)+4*p+16 : ℤ) ≤ lim.word := by
    have hh := hbudget (4*(L*U)+4*p+16) (by unfold word; omega)
    exact_mod_cast hh
  have hpre : Emod.Pre lim p (L*U) (work+3) := ⟨hp,hw,hemWord,hsp⟩
  have hcBound := LightSourceRowScan.count_le bits hbitBound (j := L) le_rfl
  have hlBound := LightSourceRowScan.hash_le bits w0 w1 hbound0 hbound1 (j := L) le_rfl
  have hrBound := LightSourceRowScan.hash_le bits w1 w0 hbound1 hbound0 (j := L) le_rfl
  have hlAbs : |(LightSourceRowScan.hash bits w0 w1 L : ℤ)| ≤ ((L*U : ℕ) : ℤ) := by
    rw [Int.abs_natCast]
    exact Int.ofNat_le.mpr hlBound
  have hrAbs : |(LightSourceRowScan.hash bits w1 w0 L : ℤ)| ≤ ((L*U : ℕ) : ℤ) := by
    rw [Int.abs_natCast]
    exact Int.ofNat_le.mpr hrBound
  have htimeL := LightResidues.emodTime_le (p := p) hlAbs
  have htimeR := LightResidues.emodTime_le (p := p) hrAbs
  unfold emodTime LightResidues.residueBudget at htimeL htimeR
  simp only [Int.natAbs_natCast] at htimeL htimeR
  have hlog : Nat.log 2 (1+L*U) = Nat.log 2 (L*U+1) := by rw [Nat.add_comm]
  have hlLt := LightResidues.residue_lt hp 1 (LightSourceRowScan.hash bits w0 w1 L : ℤ)
  have hrLt := LightResidues.residue_lt hp 1 (LightSourceRowScan.hash bits w1 w0 L : ℤ)
  have hlCast := LightResidues.residue_cast hp 1 (LightSourceRowScan.hash bits w0 w1 L : ℤ)
  have hrCast := LightResidues.residue_cast hp 1 (LightSourceRowScan.hash bits w1 w0 L : ℤ)
  simp only [one_mul] at hlCast hrCast
  apply Meets.of_body hmain
  unfold body time
  have hr := LightSourceRowScan.meets (d := d+1) (μ := μ) (src := src)
    (src0 := src0) (src1 := src1) (L := L) (dst := work) (U := U)
    hrow bits w0 w1 hw (by omega) (by omega) (by omega) (by omega) hrowWord
    hbits hread0 hread1 hbitBound hbound0 hbound1
  light_call hr using LightSourceRowScan.time,LightResidues.residueBudget,LightSourceFlagTest.time
    with q ν₁ ⟨cardRead,leftRead,rightRead,kept₁⟩
  light_call (emod_meets (x := (LightSourceRowScan.hash bits w0 w1 L : ℤ)) hem hpre hlAbs)
    using leftRead,LightSourceRowScan.time,LightResidues.residueBudget,LightSourceFlagTest.time
    with l ν₂ ⟨lResult,kept₂⟩
  rw [← hlCast] at lResult
  subst l
  have rightRead₂ : ν₂ (work+2) = (LightSourceRowScan.hash bits w1 w0 L : ℤ) :=
    (kept₂ _ (by omega)).trans rightRead
  have rightAddr : ((work : ℤ)+2).toNat = work+2 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using (Int.toNat_natCast (work+2))
  light_call (emod_meets (x := (LightSourceRowScan.hash bits w1 w0 L : ℤ)) hem hpre hrAbs)
    using rightRead₂,rightAddr,LightSourceRowScan.time,LightResidues.residueBudget,LightSourceFlagTest.time
    with r ν₃ ⟨rResult,kept₃⟩
  rw [← hrCast] at rResult
  subst r
  have cardRead₃ : ν₃ work = (LightSourceRowScan.count bits L : ℤ) :=
    (kept₃ _ (by omega)).trans ((kept₂ _ (by omega)).trans cardRead)
  have countLRead : ν₃ (histL+LightResidues.residue p 1
      (LightSourceRowScan.hash bits w0 w1 L : ℤ)) =
      (leftCount (LightResidues.residue p 1 (LightSourceRowScan.hash bits w0 w1 L : ℤ)) : ℤ) :=
    (kept₃ _ (by omega)).trans ((kept₂ _ (by omega)).trans
      ((kept₁ _ (Or.inl (by omega))).trans (hcountL _ hlLt)))
  have countRRead : ν₃ (histR+LightResidues.residue p 1
      (LightSourceRowScan.hash bits w1 w0 L : ℤ)) =
      (rightCount (LightResidues.residue p 1 (LightSourceRowScan.hash bits w1 w0 L : ℤ)) : ℤ) :=
    (kept₃ _ (by omega)).trans ((kept₂ _ (by omega)).trans
      ((kept₁ _ (Or.inl (by omega))).trans (hcountR _ hrLt)))
  have hflagWordL := hbudget (LightSourceRowScan.count bits L+h+
    leftCount (LightResidues.residue p 1 (LightSourceRowScan.hash bits w0 w1 L : ℤ))+cap+2)
    (by have := hcountBoundL _ hlLt; unfold word; omega)
  have hflagWordR := hbudget (LightSourceRowScan.count bits L+h+
    rightCount (LightResidues.residue p 1 (LightSourceRowScan.hash bits w1 w0 L : ℤ))+cap+2)
    (by have := hcountBoundR _ hrLt; unfold word; omega)
  light_call (LightSourceFlagTest.meets (d := d+1) hflag ν₃ hflagWordL)
    using cardRead₃,countLRead,LightSourceRowScan.time,LightResidues.residueBudget,LightSourceFlagTest.time
    with fl ν₄ ⟨flResult,hmem₄⟩
  subst ν₄
  light_call (LightSourceFlagTest.meets (d := d+1) hflag ν₃ hflagWordR)
    using cardRead₃,countRRead,LightSourceRowScan.time,LightResidues.residueBudget,LightSourceFlagTest.time
    with fr ν₅ ⟨frResult,hmem₅⟩
  subst ν₅
  have flEq : fl = (flag L h p cap bits w0 w1 leftCount : ℤ) := flResult
  have frEq : fr = (flag L h p cap bits w1 w0 rightCount : ℤ) := frResult
  have flBound := flag_le L h p cap bits w0 w1 leftCount
  have frBound := flag_le L h p cap bits w1 w0 rightCount
  have h1 := hbudget 1 (by unfold word; omega)
  light_store dst (flag L h p cap bits w0 w1 leftCount : ℕ)
    using flEq,LightSourceRowScan.time,LightResidues.residueBudget,LightSourceFlagTest.time
  light_store (dst+1) (flag L h p cap bits w1 w0 rightCount : ℕ)
    using frEq,LightSourceRowScan.time,LightResidues.residueBudget,LightSourceFlagTest.time
  refine ⟨by simp,by simp,?_⟩
  intro a ⟨ha,hout⟩
  simp only [Function.update_of_ne (show a ≠ dst+1 by omega),
    Function.update_of_ne (show a ≠ dst by omega)]
  exact (kept₃ a (by omega)).trans ((kept₂ a (by omega)).trans (kept₁ a (Or.inl ha)))

def program : Program :=
  [body 1 2 3,LightSourceRowScan.body,emodBody,LightSourceFlagTest.body]

theorem time_bound (L U : ℕ) :
    time L U ≤ 150*L+464*(Nat.log 2 (L*U+1)+1) := by
  unfold time LightSourceRowScan.time LightResidues.residueBudget LightSourceFlagTest.time
  nlinarith

end ThreeSum.LightSourceRowFlag
