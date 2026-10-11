import Submission.ThreeSum.LightSharedReportingCell
import Submission.ThreeSum.SharedReportingBankLevels
import Submission.ThreeSum.LightSharedReportingLoop

/-!
# Construct every level once for one occurrence and independent source bands

The loop executes the cubic switch, maintains the exact prefix count and
prefix-array span, and appends one compact catalog per level. Its budget is
the sum of the actual level budgets. Five-cell metadata records are
contiguous; completed payloads remain immutable.
-/

namespace ThreeSum.LightSharedReportingLevels

open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData SharedReportingBankLevels

set_option maxHeartbeats 3000000
set_option maxRecDepth 14000

/-- h,J,level count,source pointer cells,local choose/pair counts,record and
payload destinations. The surrounding initializer computes the level count. -/
def body (pSwitch pCell : ℕ) : Stmt :=
  .set 9 (k 1) ;;
  .set 10 (k 2) ;;
  .set 11 (v 8) ;;
  .for 12 (v 2) (
    .set 13 (k 2 *' v 0 *' (v 1 -' v 12)) ;;
    .call pSwitch [v 1,v 12,v 13] 14 ;;
    .set 15 (v 13 -' v 14) ;;
    .call pCell [v 0,v 1,v 12,v 3,v 4,v 14,v 15,v 5,v 6,v 9,v 10,
      v 7 +' k 5 *' v 12,v 11] 11 ;;
    .set 9 (v 9 *' v 6) ;;
    .set 10 (v 10 +' k 1 +' v 9)) ;;
  .set 0 (v 11)

def roundTime (h J i : ℕ) : ℕ :=
  LightSwitch.time (residual h J i)+LightSharedReportingCell.time h J i (boxCut h J i)+800
def time (h J K : ℕ) : ℕ := (∑ i ∈ Finset.range K, (roundTime h J i+8))+100

def program : Program :=
  ReportingHostRelocation.program LightSharedReportingCell.program LightSwitch.program ++ [body 63 62]

theorem program_length : program.length=65 := rfl

structure Resources (lim : Limits) (base h J K B D d : ℕ) : Prop where
  state : ((J+K+512+prefixSpan h K+count h K : ℕ) : ℤ) ≤ lim.word
  space : baseAt base h J K ≤ lim.space
  powers : ((2^(512*h+1) : ℕ) : ℤ) ≤ lim.word
  keys : ∀ i < K, (LightRadixKeys.word (2^(512*h)) (2^(512*h)) i : ℤ) ≤ lim.word
  width : (((J*(512*h)+1)*2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word
  index : ∀ i < K, (LightReportingSortedCatalog.word (J*(512*h)) (count h i) : ℤ) ≤ lim.word
  values : ∀ i < K, (((2^((J-i)*(512*h))*
    ((2^((J-i)*(512*h))*B)*(2^((J-i)*(512*h))*D))) : ℕ) : ℤ) ≤ lim.word
  switch : ∀ i < K, (LightSwitch.word J (residual h J i) : ℤ) ≤ lim.word
  pairDepth : d+512*h+K+8 ≤ lim.depth
  widthDepth : d+J*(512*h)+18 ≤ lim.depth
  sortDepth : ∀ i < K, d+Nat.clog 2 (count h i)+6 ≤ lim.depth

def Inv (μ : ℕ → ℤ) (record base h J K cellL cellR i : ℕ)
    (f g : Finset (Fin (J*(512*h))) → ℤ) (σ : State) : Prop :=
  ∃ (r t cut : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [h,J,K,cellL,cellR,localChoose h,localPairs h,record,base,
      count h i,prefixSpan h i,baseAt base h J i,i,r,t,cut],ν⟩ ∧
    Built ν record base h J i f g ∧ Kept μ ν record ∧ KeptBut μ ν base record (5*K)

theorem program_meets {lim : Limits} {μ : ℕ → ℤ}
    {record base h J K baseL baseR cellL cellR B D d : ℕ}
    (f g : Finset (Fin (J*(512*h))) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hK : K ≤ LightSwitchDepth.depth J+1)
    (hrecords : record+5*K ≤ base)
    (hcellL : cellL < record) (hcellR : cellR < record)
    (hdataL : baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) (2*h*J) ≤ record)
    (hdataR : baseR+(J*(512*h)+1)*downsetCap (J*(512*h)) (2*h*J) ≤ record)
    (R : Resources lim base h J K B D d)
    (hf : ∀ S, S.card ≤ 2*h*J → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ 2*h*J → |g S| ≤ D)
    (hleftRead : μ cellL=(baseL : ℤ)) (hrightRead : μ cellR=(baseR : ℤ))
    (hstoredL : LightZetaStages.StoredThrough μ baseL (2*h*J) f (J*(512*h)))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (2*h*J) g (J*(512*h))) :
    Meets lim program 64 d
      [h,J,K,cellL,cellR,localChoose h,localPairs h,record,base] μ (time h J K)
      (fun result ν => result=(baseAt base h J K : ℤ) ∧
        Built ν record base h J K f g ∧ Kept μ ν record ∧ KeptBut μ ν base record (5*K)) := by
  have hstate := R.state
  have hspace := R.space
  have hdepth := R.widthDepth
  have hbase : base ≤ lim.space := (Nat.le_add_right _ _).trans hspace
  have hKWord : (K : ℤ) ≤ lim.word := by omega
  have hJWord : (J : ℤ) ≤ lim.word := by omega
  have hconstants : (512 : ℤ) ≤ lim.word := by omega
  apply Meets.of_body (p := 64) (by rfl : program[64]?=some (body 63 62))
  unfold body time
  light_set (1 : ℕ)
  light_set (2 : ℕ)
  light_set (base : ℕ)
  refine Ends.pieceThen (LightSharedReportingLoop.forSum
    (T := (∑ i ∈ Finset.range K, (roundTime h J i+8))+6)
    (Q := Inv μ record base h J K cellL cellR K f g)
    (Inv μ record base h J K cellL cellR · f g) K (roundTime h J)
    ?start ?round ?done ?bound hKWord (by
      simp only [Expr.cost]
      have hs : (∑ i ∈ Finset.range K, (1+roundTime h J i+7))=
          ∑ i ∈ Finset.range K, (roundTime h J i+8) := by
        apply Finset.sum_congr rfl
        intro i hi
        omega
      omega)) ?finish
  case start =>
    refine ⟨0,0,0,μ,?_,Built.empty _ _ _ _ _ _ _,SameOn.refl,fun _ _ => rfl⟩
    simp only [SharedReportingBankLevels.count_zero,span_zero,baseAt_zero]
    simp [update_frame_setLocal]
    exact (frame_append_zeros [h,J,K,cellL,cellR,localChoose h,localPairs h,record,base,1,2,base,0] 3).symm
  case round =>
    rintro i _ hi _ ⟨r,t,cut,ν,rfl,built,kept,keptBlock⟩
    have hiDepth : i ≤ LightSwitchDepth.depth J := by omega
    have hiJ := level_le hiDepth
    have hnext := baseAt_mono base h J (show i+1 ≤ K by omega)
    have hcellSpace : finish (baseAt base h J i) h J i (boxCut h J i) ≤ lim.space := by
      rw [finish_baseAt]
      exact hnext.trans hspace
    have hbefore := baseAt_mono base h J (show i ≤ K by omega)
    have hcurrent : baseAt base h J i ≤ lim.space := hbefore.trans hspace
    have hlocalSpace := (pair_scratch (baseAt base h J i) h J i (boxCut h J i)).trans hcellSpace
    have hwidthSpace := (table_scratch (baseAt base h J i) h J i (boxCut h J i)).trans hcellSpace
    have hW : J*(512*h) ≤ lim.space := by omega
    have hL : 512*h ≤ lim.space := by omega
    have hV : (J-i)*(512*h) ≤ J*(512*h) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have hrV := residual_le_width h J i
    have hrNat : residual h J i ≤ lim.space := by omega
    have hrWord : (2 : ℤ)*(h : ℤ)*((J : ℤ)-(i : ℤ)) ≤ lim.word := by
      simpa only [SharedReportingBankLevels.residual,Nat.cast_mul,Nat.cast_sub hiJ,Nat.cast_ofNat] using
        (Int.ofNat_le.mpr hrNat).trans hw
    have hrNZ : (0 : ℤ) ≤ (2 : ℤ)*(h : ℤ)*((J : ℤ)-(i : ℤ)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (Int.ofNat_le.mpr hiJ))
    have hN := count_mono h (show i+1 ≤ K by omega)
    have hspan := span_mono h (show i+1 ≤ K by omega)
    have hprod : (count h i : ℤ)*(localPairs h : ℤ)=(count h (i+1) : ℤ) := by
      rw [SharedReportingBankLevels.count_succ,Nat.cast_mul]
    have hprodNZ : (0 : ℤ) ≤ (count h i : ℤ)*(localPairs h : ℤ) := by positivity
    have hspanEq := span_succ h i
    have hrecord : record+5*i+5 ≤ baseAt base h J i := by
      have hb : base ≤ baseAt base h J i := Nat.le_add_right _ _
      omega
    unfold roundTime
    light_set (residual h J i : ℕ) using SharedReportingBankLevels.residual,Nat.cast_sub hiJ
    have hs := (ReportingHostRelocation.meets
      (LightSwitch.program_meets (μ := ν) (d := d+1) hiJ (candidates_nonempty hiDepth) (R.switch i hi))
      LightSharedReportingCell.program).append [body 63 62]
    light_call hs using SharedReportingBankLevels.residual with actual νt ⟨hactual,hmem⟩
    subst νt
    have hswitch := switch_le (h := h) hiDepth
    change Switch.switchIndex J i (residual h J i) ≤ residual h J i at hswitch
    have htWord : (switch h J i : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hswitch.trans hrNat)).trans hw
    light_set (boxCut h J i : ℕ) using boxCut,switch,hactual
    have hsourceL : LightZetaStages.StoredThrough ν baseL (2*h*J) f (J*(512*h)) :=
      LightSignedLeafBatch.storedThrough_of_on hstoredL
        (by intro a _ ha; exact kept a (by omega))
    have hsourceR : LightZetaStages.StoredThrough ν baseR (2*h*J) g (J*(512*h)) :=
      LightSignedLeafBatch.storedThrough_of_on hstoredR
        (by intro a _ ha; exact kept a (by omega))
    have hreadL : ν cellL=(baseL : ℤ) := (kept cellL hcellL).trans hleftRead
    have hreadR : ν cellR=(baseR : ℤ) := (kept cellR hcellR).trans hrightRead
    have hc := ((LightSharedReportingCell.program_meets (μ := ν) (d := d+1)
      (k := i) (boxCut := boxCut h J i) (baseL := baseL) (baseR := baseR)
      (cellL := cellL) (cellR := cellR) (free := baseAt base h J i) (rec := record+5*i)
      (B := B) (D := D) (t := switch h J i) hiJ f g hw hconstants hJWord
      ((boxCut_le h J i).trans hrV) (by omega) (by omega) (by omega) (by omega) hrecord
      hcellSpace R.powers (R.keys i hi) R.width (R.index i hi) (R.values i hi) htWord
      (pre_cut hiJ) hf hg hreadL hreadR hsourceL hsourceR
      (by have hh := R.pairDepth; omega) (by have hh := R.widthDepth; omega)
      (by have hh := R.sortDepth i hi; omega)).append
        (LightSwitch.program.map (ReportingHostRelocation.relocate LightSharedReportingCell.program.length))).append
          [body 63 62]
    light_call hc using hactual,switch with next ν₁ ⟨hnextFree,hentry,_,_,hkeepCell⟩
    light_set (count h (i+1) : ℕ) using SharedReportingBankLevels.count_succ
    light_set (prefixSpan h (i+1) : ℕ) using span_succ
    refine ⟨by simp,residual h J i,switch h J i,boxCut h J i,ν₁,?_,?_,?_,?_⟩
    · simp [update_frame_setLocal,hnextFree,finish_baseAt,hactual,switch]
    · exact built.append hiJ hentry hkeepCell (by omega)
    · intro a ha
      exact (hkeepCell a ⟨by omega,Or.inl (by omega)⟩).trans (kept a ha)
    · intro a ⟨ha,houtside⟩
      have hb : base ≤ baseAt base h J i := Nat.le_add_right _ _
      exact (hkeepCell a ⟨by omega,by rcases houtside with h | h <;> omega⟩).trans
        (keptBlock a ⟨ha,houtside⟩)
  case done =>
    rintro _ _ ⟨r,t,cut,ν,rfl,built,kept,keptBlock⟩
    exact ⟨r,t,cut,ν,rfl,built,kept,keptBlock⟩
  case bound =>
    rintro i _ _ _ ⟨r,t,cut,ν,rfl,_,_,_⟩
    light_side
  case finish =>
    rintro _ ⟨r,t,cut,ν,rfl,built,kept,keptBlock⟩
    light_set (baseAt base h J K : ℕ)
    exact ⟨rfl,built,kept,keptBlock⟩

end ThreeSum.LightSharedReportingLevels
