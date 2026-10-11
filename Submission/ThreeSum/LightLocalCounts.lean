import Submission.ThreeSum.LightSubsetSetup
import Submission.ThreeSum.LocalCoverBounds

/-!
# Executing the local graph counts

One constructed Pascal table and one constructed power table provide all
integer counts needed by the local hash cover. The zero-mask rank call in
the reused setup wrapper takes only linear additional time. In particular,
none of these counts is an input oracle.
-/

namespace ThreeSum.LightLocalCounts

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

open Light LocalCoverBounds LightPascal LightSubsetAddress

def values (h : ℕ) : List ℤ :=
  [outputCount (512*h) h,vertexCount (512*h) h,degree (512*h) h,
    groupSize h,2^(2*h),localThreshold h]

def body (pSetup : ℕ) : Stmt :=
  .set 3 (k 512 *' v 0) ;;
  .set 4 (k 2 *' v 0) ;;
  .call pSetup [v 3,k 0,k 0,v 2] 5 ;;
  .set 6 (M (v 2 +' v 3 *' (v 3 +' k 1) +' v 4)) ;;
  .set 7 (M (v 2 +' v 3 *' (v 3 +' k 1) +' v 0)) ;;
  .set 8 (M (v 2 +' (v 3 -' v 0) *' (v 3 +' k 1) +' v 0)) ;;
  .set 9 (M (v 2 +' v 4 *' (v 3 +' k 1) +' v 0)) ;;
  .set 10 (M (v 2 +' (v 3 +' k 1) *' (v 3 +' k 1) +' v 4)) ;;
  .set 11 (v 6 *' v 10) ;;
  .store (v 1) (v 6) ;;
  .store (v 1 +' k 1) (v 7) ;;
  .store (v 1 +' k 2) (v 8) ;;
  .store (v 1 +' k 3) (v 9) ;;
  .store (v 1 +' k 4) (v 10) ;;
  .store (v 1 +' k 5) (v 11) ;;
  .set 0 (v 11)

def time (h : ℕ) : ℕ := LightSubsetSetup.time (512*h)+500
def space (work h : ℕ) : ℕ := work+tableSize (512*h)+(512*h+1)
def word (h : ℕ) : ℕ := 1024+4*(2^(512*h+1))^2

structure Procs (P : Program) (pMain : ℕ) where
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pPowers : ℕ
  pRank : ℕ
  setup : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  main : P[pMain]? = some (body pSetup)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {h dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+4 ≤ lim.depth)
    (hout : dst+6 ≤ work) (hspace : space work h ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h,dst,work] μ (time h)
      (fun r μ' => r = (localThreshold h : ℤ) ∧ Seg μ' dst (values h) ∧
        KeptBut μ μ' work dst 6) := by
  have htableSpace : work+tableSize (512*h) ≤ lim.space := by unfold space at hspace; omega
  have hbasePos : 0 < (2 : ℕ)^(512*h+1) := Nat.two_pow_pos _
  have hbaseWord : ((2^(512*h+1) : ℕ) : ℤ) ≤ lim.word := by
    have hb : 2^(512*h+1) ≤ word h := by unfold word; nlinarith
    exact (Int.ofNat_le.mpr hb).trans hword
  have hchoose (i j : ℕ) (hi : i ≤ 512*h) :
      i.choose j ≤ 2^(512*h+1) :=
    (Nat.choose_le_two_pow i j).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hchooseWord (i j : ℕ) (hi : i ≤ 512*h) : (i.choose j : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (hchoose i j hi)).trans hbaseWord
  have hMWord := hchooseWord (512*h) (2*h) le_rfl
  have hVWord := hchooseWord (512*h) h le_rfl
  have hDeltaWord := hchooseWord (512*h-h) h (by omega)
  have hGWord := hchooseWord (2*h) h (by omega)
  have hDle : 2^(2*h) ≤ 2^(512*h+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hDWord : ((2^(2*h) : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hDle).trans hbaseWord
  have hNle : localThreshold h ≤ word h := by
    have hm := Nat.mul_le_mul (hchoose (512*h) (2*h) le_rfl) hDle
    change (512*h).choose (2*h)*2^(2*h) ≤ _
    unfold word
    nlinarith
  have hNWord : (localThreshold h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hNle).trans hword
  have hconstant : (512 : ℤ) ≤ lim.word := by
    have hc : 512 ≤ word h := by unfold word; omega
    exact (Int.ofNat_le.mpr hc).trans hword
  have hproduct : ((512*h).choose (2*h) : ℤ)*(2 : ℤ)^(2*h) = (localThreshold h : ℤ) := by
    simp [localThreshold,outputCount]
  have hproductWord : ((512*h).choose (2*h) : ℤ)*(2 : ℤ)^(2*h) ≤ lim.word := by
    rw [hproduct]
    exact hNWord
  have hproductNonneg : (0 : ℤ) ≤ ((512*h).choose (2*h) : ℤ)*(2 : ℤ)^(2*h) := by positivity
  have hsize : 512*h+1 ≤ tableSize (512*h) := by unfold tableSize; nlinarith
  have hsub : ((512*h : ℕ) : ℤ)-(h : ℤ) = ((512*h-h : ℕ) : ℤ) := by omega
  have hMaddr := cell_offset_lt (W := 512*h) (i := 512*h) (j := 2*h) le_rfl (by omega)
  have hVaddr := cell_offset_lt (W := 512*h) (i := 512*h) (j := h) le_rfl (by omega)
  have hDeltaAddr := cell_offset_lt (W := 512*h) (i := 512*h-h) (j := h) (by omega) (by omega)
  have hGaddr := cell_offset_lt (W := 512*h) (i := 2*h) (j := h) (by omega) (by omega)
  have hrowNZ : (0 : ℤ) ≤ 512*(h : ℤ)*(512*(h : ℤ)+1) := by positivity
  have hrowAddr : (work : ℤ)+512*(h : ℤ)*(512*(h : ℤ)+1)+2*(h : ℤ) < (lim.space : ℤ) := by
    exact_mod_cast (show work+512*h*(512*h+1)+2*h < lim.space by omega)
  have hdeltaNZ : (0 : ℤ) ≤ (512*(h : ℤ)-(h : ℤ))*(512*(h : ℤ)+1) := by
    apply mul_nonneg <;> omega
  have hdeltaAddr : (work : ℤ)+(512*(h : ℤ)-(h : ℤ))*(512*(h : ℤ)+1)+(h : ℤ) < (lim.space : ℤ) := by
    rw [show 512*(h : ℤ)-(h : ℤ) = ((512*h-h : ℕ) : ℤ) by omega]
    exact_mod_cast (show work+(512*h-h)*(512*h+1)+h < lim.space by omega)
  have hgroupNZ : (0 : ℤ) ≤ 2*(h : ℤ)*(512*(h : ℤ)+1) := by positivity
  have hgroupAddr : (work : ℤ)+2*(h : ℤ)*(512*(h : ℤ)+1)+(h : ℤ) < (lim.space : ℤ) := by
    exact_mod_cast (show work+2*h*(512*h+1)+h < lim.space by omega)
  have hMcast : (work : ℤ)+512*(h : ℤ)*(512*(h : ℤ)+1)+2*(h : ℤ) =
      ((work+512*h*(512*h+1)+2*h : ℕ) : ℤ) := by push_cast; rfl
  have hVcast : (work : ℤ)+512*(h : ℤ)*(512*(h : ℤ)+1)+(h : ℤ) =
      ((work+512*h*(512*h+1)+h : ℕ) : ℤ) := by push_cast; rfl
  have hDeltaCast : (work : ℤ)+(512*(h : ℤ)-(h : ℤ))*(512*(h : ℤ)+1)+(h : ℤ) =
      ((work+(512*h-h)*(512*h+1)+h : ℕ) : ℤ) := by
    rw [show 512*(h : ℤ)-(h : ℤ) = ((512*h-h : ℕ) : ℤ) by omega]
    push_cast
    rfl
  have hGcast : (work : ℤ)+2*(h : ℤ)*(512*(h : ℤ)+1)+(h : ℤ) =
      ((work+2*h*(512*h+1)+h : ℕ) : ℤ) := by push_cast; rfl
  have hDcast : (work : ℤ)+(512*(h : ℤ)+1)*(512*(h : ℤ)+1)+2*(h : ℤ) =
      ((work+tableSize (512*h)+2*h : ℕ) : ℤ) := by
    simp [tableSize,pow_two]
  have hDaddrZ : (work : ℤ)+(512*(h : ℤ)+1)*(512*(h : ℤ)+1)+2*(h : ℤ) < (lim.space : ℤ) := by
    rw [hDcast]
    exact_mod_cast (show work+tableSize (512*h)+2*h < lim.space by
      unfold space at hspace
      omega)
  have hSquareNZ : (0 : ℤ) ≤ (512*(h : ℤ)+1)*(512*(h : ℤ)+1) := by positivity
  have hMnat : ((work : ℤ)+512*(h : ℤ)*(512*(h : ℤ)+1)+2*(h : ℤ)).toNat =
      work+512*h*(512*h+1)+2*h := by rw [hMcast,Int.toNat_natCast]
  have hVnat : ((work : ℤ)+512*(h : ℤ)*(512*(h : ℤ)+1)+(h : ℤ)).toNat =
      work+512*h*(512*h+1)+h := by rw [hVcast,Int.toNat_natCast]
  have hDeltaNat : ((work : ℤ)+(512*(h : ℤ)-(h : ℤ))*(512*(h : ℤ)+1)+(h : ℤ)).toNat =
      work+(512*h-h)*(512*h+1)+h := by rw [hDeltaCast,Int.toNat_natCast]
  have hGnat : ((work : ℤ)+2*(h : ℤ)*(512*(h : ℤ)+1)+(h : ℤ)).toNat =
      work+2*h*(512*h+1)+h := by rw [hGcast,Int.toNat_natCast]
  have hDnat : ((work : ℤ)+(512*(h : ℤ)+1)*(512*(h : ℤ)+1)+2*(h : ℤ)).toNat =
      work+tableSize (512*h)+2*h := by rw [hDcast,Int.toNat_natCast]
  apply Meets.of_body S.main
  unfold body time
  light_set (512*h : ℕ) using LightSubsetSetup.time,buildTime,rowTime,LightArray.linearTime,powTableTime,rankTime
  light_set (2*h : ℕ) using LightSubsetSetup.time,buildTime,rowTime,LightArray.linearTime,powTableTime,rankTime
  light_call (LightSubsetSetup.meets (d := d+1) (μ := μ) (L := 512*h) (k := 0) (m := 0)
    (work := work) S.setup hw hspace hbaseWord (by simp) (by omega))
    using LightSubsetSetup.time,buildTime,rowTime,LightArray.linearTime,powTableTime,rankTime
    with result μ₁ ⟨hr,htable,hpowers,hkept⟩
  have hMread := htable (512*h) le_rfl (2*h) (by omega)
  have hVread := htable (512*h) le_rfl h (by omega)
  have hDeltaRead := htable (512*h-h) (by omega) h (by omega)
  have hGread := htable (2*h) (by omega) h (by omega)
  have hDread := hpowers (2*h) (by omega)
  light_set ((512*h).choose (2*h) : ℕ) using hMnat,hMread,LightSubsetSetup.time,buildTime,rowTime,LightArray.linearTime,powTableTime,rankTime
  light_set ((512*h).choose h : ℕ) using hVnat,hVread,LightSubsetSetup.time,buildTime,rowTime,LightArray.linearTime,powTableTime,rankTime
  light_set ((512*h-h).choose h : ℕ) using hDeltaNat,hDeltaRead,LightSubsetSetup.time,buildTime,rowTime,LightArray.linearTime,powTableTime,rankTime
  light_set ((2*h).choose h : ℕ) using hGnat,hGread,LightSubsetSetup.time,buildTime,rowTime,LightArray.linearTime,powTableTime,rankTime
  light_set (2^(2*h) : ℕ) using hDnat,hDread,LightSubsetSetup.time,buildTime,rowTime,LightArray.linearTime,powTableTime,rankTime
  light_set (localThreshold h : ℕ) using hproduct,LightSubsetSetup.time,buildTime,rowTime,LightArray.linearTime,powTableTime,rankTime
  light_store dst ((512*h).choose (2*h) : ℕ) using LightSubsetSetup.time,buildTime,rowTime,LightArray.linearTime,powTableTime,rankTime
  light_store (dst+1) ((512*h).choose h : ℕ) using LightSubsetSetup.time,buildTime,rowTime,LightArray.linearTime,powTableTime,rankTime
  light_store (dst+2) ((512*h-h).choose h : ℕ) using LightSubsetSetup.time,buildTime,rowTime,LightArray.linearTime,powTableTime,rankTime
  light_store (dst+3) ((2*h).choose h : ℕ) using LightSubsetSetup.time,buildTime,rowTime,LightArray.linearTime,powTableTime,rankTime
  light_store (dst+4) (2^(2*h) : ℕ) using LightSubsetSetup.time,buildTime,rowTime,LightArray.linearTime,powTableTime,rankTime
  light_store (dst+5) (localThreshold h : ℕ) using LightSubsetSetup.time,buildTime,rowTime,LightArray.linearTime,powTableTime,rankTime
  light_set (localThreshold h : ℕ) using LightSubsetSetup.time,buildTime,rowTime,LightArray.linearTime,powTableTime,rankTime
  refine ⟨rfl,?_,?_⟩
  · simp [values,outputCount,vertexCount,degree,groupSize,seg_cons]
  · intro a ha
    change Function.update _ _ _ a = _
    repeat rw [Function.update_of_ne (by omega)]
    exact hkept a ha.1

def program : Program :=
  [body 1,LightSubsetSetup.body 2 6 7,buildBody 3 4,fillBody,rowBody 5,
    LightArray.linearBody,powTableBody,rankBody 7]

def procs : Procs program 0 := ⟨1,2,3,4,5,6,7,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {h dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+4 ≤ lim.depth)
    (hout : dst+6 ≤ work) (hspace : space work h ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim program 0 d [h,dst,work] μ (time h)
      (fun r μ' => r = (localThreshold h : ℤ) ∧ Seg μ' dst (values h) ∧
        KeptBut μ μ' work dst 6) := procs.meets hw hd hout hspace hword

theorem time_bound (h : ℕ) : time h ≤ 1700*(512*h+1)^2 := by
  have ht := LightSubsetSetup.time_bound (512*h)
  have hs : 0 < (512*h+1)^2 := Nat.pow_pos (by omega)
  unfold time
  nlinarith

end ThreeSum.LightLocalCounts
