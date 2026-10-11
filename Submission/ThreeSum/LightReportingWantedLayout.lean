import Submission.ThreeSum.ReportingHostWantedLayout
import Submission.ThreeSum.LightNatPower

/-!
# Compute the reusable reporting scratch pointers

The two retained scalar headers supply G and the representation cap.
One real power loop computes the mask span. Scalar arithmetic then lays out
all decoded, selected, packed, frontier, query and terminal buffers; no
buffer is initialized or scanned merely because it was reserved.
-/

namespace ThreeSum.LightReportingWantedLayout

open Light GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostFrontierLayout
open ReportingHostWantedLayout

set_option maxHeartbeats 4500000
set_option maxRecDepth 20000
set_option linter.unusedVariables false

def layout (dst h J K N NB NC : ℕ) : Layout :=
  make (ReportingHostWantedLayout.root dst J) K (width h J) (groupSize h) (2^(width h J))
    (capacityBound N NB NC (representationCap h J) (groupSize h))

def space (dst cover counter h J K N NB NC : ℕ) : ℕ :=
  (layout dst h J K N NB NC).work+N*NB+N*NB*NC+massBound N NB NC (representationCap h J)+
    cover+counter+J+512*h+K+N+NB+NC+representationCap h J+groupSize h+1024

def numericExtra (h J K N NB NC : ℕ) : ℕ :=
  N*NB+N*NB*NC+massBound N NB NC (representationCap h J)+
    J+512*h+K+N+NB+NC+representationCap h J+groupSize h+1024

/-- Each absolute address is bounded independently. This is invariant under
translating the pre-existing memory prefix. -/
def relativeSpace (dst cover counter h J K N NB NC : ℕ) : ℕ :=
  max ((layout dst h J K N NB NC).work+numericExtra h J K N NB NC)
    (max (cover+4) (counter+3))

theorem relativeSpace_le_space (dst cover counter h J K N NB NC : ℕ) :
    relativeSpace dst cover counter h J K N NB NC≤space dst cover counter h J K N NB NC := by
  unfold relativeSpace numericExtra space
  omega

def body (pPower : ℕ) : Stmt :=
  .set 9 (v 0 *' (k 512 *' v 1)) ;;
  .set 10 (M (v 3 +' k 3)) ;;
  .set 11 (M (v 4 +' k 2)) ;;
  .call pPower [k 2,v 9] 12 ;;
  .set 13 (v 5 *' v 6 *' v 7 *' v 11) ;;
  .set 14 ((v 13 +' k 1) *' v 10) ;;
  .set 15 (v 8 +' k 38 +' k 3 *' v 0) ;;
  .set 16 (v 15 +' (v 2 +' k 1) *' (k 4 +' k 2 *' v 14)) ;;
  .set 17 (v 16 +' v 10) ;;
  .set 18 (v 17 +' v 10) ;;
  .set 19 (v 18 +' v 10) ;;
  .set 20 (v 19 +' v 10) ;;
  .set 21 (v 20 +' v 10) ;;
  .set 22 (v 21 +' v 12) ;;
  .set 23 (v 22 +' v 12) ;;
  .set 24 (v 23 +' v 12) ;;
  .set 25 (v 24 +' v 12) ;;
  .set 26 (v 25 +' k 2 *' (k 2 *' v 9 +' k 4 *' v 12 +' k 2)) ;;
  .set 27 (v 26 +' v 9) ;;
  .set 28 (v 27 +' k 2) ;;
  .store (v 8) (v 15) ;;
  .store (v 8 +' k 1) (v 16) ;;
  .store (v 8 +' k 2) (v 17) ;;
  .store (v 8 +' k 3) (v 18) ;;
  .store (v 8 +' k 4) (v 19) ;;
  .store (v 8 +' k 5) (v 20) ;;
  .store (v 8 +' k 6) (v 21) ;;
  .store (v 8 +' k 7) (v 22) ;;
  .store (v 8 +' k 8) (v 23) ;;
  .store (v 8 +' k 9) (v 24) ;;
  .store (v 8 +' k 10) (v 25) ;;
  .store (v 8 +' k 11) (v 26) ;;
  .store (v 8 +' k 12) (v 27) ;;
  .store (v 8 +' k 13) (v 28) ;;
  .set 0 (v 28)

def program : Program := LightNatPower.program++[body 0]
def time (h J : ℕ) : ℕ := LightNatPower.time (width h J)+2500

theorem program_meets_relative {lim : Limits} {μ : ℕ→ℤ} {dst cover counter h J K N NB NC d : ℕ}
    (hgroup : μ (cover+3)=(groupSize h : ℤ))
    (hcap : μ (counter+2)=(representationCap h J : ℤ))
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth)
    (hs : relativeSpace dst cover counter h J K N NB NC≤lim.space) :
    Meets lim program 1 d [J,h,K,cover,counter,N,NB,NC,dst] μ (time h J)
      (fun result ν => result=((layout dst h J K N NB NC).work : ℤ) ∧
        SegN ν dst (values (layout dst h J K N NB NC)) ∧ SameOutside μ ν dst 14) := by
  let W := width h J
  let G := groupSize h
  let R := representationCap h J
  let T := 2^W
  let C := capacityBound N NB NC R G
  let L := layout dst h J K N NB NC
  have hwork : L.work≤lim.space := by dsimp only [L]; unfold relativeSpace numericExtra at hs; omega
  have hb := make_bounds (root := ReportingHostWantedLayout.root dst J)
    (K := K) (W := W) (G := G) (T := T) (cap' := C) (cap := C) le_rfl
  change Bounds L (ReportingHostWantedLayout.root dst J) K W G T C at hb
  have hroot : ReportingHostWantedLayout.root dst J≤L.masks := by
    exact (Nat.le_add_right _ _).trans hb.frontier
  have hstep : 4+2*C≤(K+1)*(4+2*C) := Nat.le_mul_of_pos_left _ (by omega)
  have hslot : (K+1)*(4+2*C)≤L.masks := by
    change _≤ReportingHostWantedLayout.root dst J+(K+1)*(4+2*C)
    omega
  have hchain : L.masks≤L.work ∧ L.childL≤L.work ∧ L.childR≤L.work ∧
      L.counts≤L.work ∧ L.selected≤L.work ∧ L.maskBase≤L.work ∧
      L.terminalMasks≤L.work ∧ L.masksL≤L.work ∧ L.masksR≤L.work ∧
      L.base≤L.work ∧ L.bitBase≤L.work ∧ L.rowOut≤L.work := by
    dsimp only [L,layout,make]
    omega
  obtain ⟨hm,hcl,hcr,hco,hse,hmb,htm,hml,hmr,hb0,hbb,hro⟩ := hchain
  have hnat : W≤lim.space ∧ T≤lim.space ∧ C≤lim.space ∧ dst+14≤lim.space ∧
      cover+4≤lim.space ∧ counter+3≤lim.space ∧ J≤lim.space ∧ 512*h≤lim.space ∧
      K+1≤lim.space ∧ N≤lim.space ∧ NB≤lim.space ∧ NC≤lim.space ∧ R≤lim.space ∧ G≤lim.space ∧
      N*NB≤lim.space ∧ N*NB*NC≤lim.space ∧ massBound N NB NC R+1≤lim.space := by
    have hbits := hb.bits
    have hmasks := hb.queryMasks
    have he := root_eq dst J
    unfold relativeSpace numericExtra at hs
    dsimp only [W,G,R,L] at *
    omega
  obtain ⟨hW,hT,hC,hdst,hcov,hcou,hJ,hL,hK,hN,hNB,hNC,hR,hG,hNNB,hNNBC,hM⟩ := hnat
  have word (n : ℕ) (hn : n≤lim.space) : (n : ℤ)≤lim.word := (Int.ofNat_le.mpr hn).trans hw
  have h512 : (512 : ℤ)≤lim.word := word 512 (by unfold relativeSpace numericExtra at hs; omega)
  have hCword := word C hC
  have hworkWord := word L.work hwork
  have hMword := word (massBound N NB NC R+1) hM
  have hNNBword : (N : ℤ)*(NB : ℤ)≤lim.word := by exact_mod_cast word (N*NB) hNNB
  have hNNBCword : (N : ℤ)*(NB : ℤ)*(NC : ℤ)≤lim.word := by exact_mod_cast word (N*NB*NC) hNNBC
  have hMZ : (N : ℤ)*(NB : ℤ)*(NC : ℤ)*(R : ℤ)=(massBound N NB NC R : ℤ) := by simp [massBound]
  have hCZ : ((massBound N NB NC R : ℤ)+1)*(G : ℤ)=(C : ℤ) := by simp [C,capacityBound]
  have hnn : (0 : ℤ)≤(N : ℤ)*(NB : ℤ) := by positivity
  have hnnc : (0 : ℤ)≤(N : ℤ)*(NB : ℤ)*(NC : ℤ) := by positivity
  have hrootZ : (dst : ℤ)+38+3*(J : ℤ)=(ReportingHostWantedLayout.root dst J : ℤ) := by
    rw [root_eq]; push_cast; ring
  have hmaskZ : (ReportingHostWantedLayout.root dst J : ℤ)+((K : ℤ)+1)*(4+2*(C : ℤ))=(L.masks : ℤ) := by
    simp [L,layout,make,slot,C,G,R]
  have hprod : (0 : ℤ)≤((K : ℤ)+1)*(4+2*(C : ℤ)) := by positivity
  have hgroupZ : μ (((cover : ℤ)+3).toNat)=(G : ℤ) := by
    rw [show ((cover : ℤ)+3).toNat=cover+3 by omega]; exact hgroup
  have hcapZ : μ (((counter : ℤ)+2).toNat)=(R : ℤ) := by
    rw [show ((counter : ℤ)+2).toNat=counter+2 by omega]; exact hcap
  have heqW : (J : ℤ)*(512*(h : ℤ))=(W : ℤ) := by simp [W,width]
  have eq_childL : (L.masks : ℤ)+(G : ℤ)=(L.childL : ℤ) := by
    change _=((L.masks+G : ℕ) : ℤ)
    push_cast
    rfl
  have eq_childR : (L.childL : ℤ)+(G : ℤ)=(L.childR : ℤ) := by
    change _=((L.childL+G : ℕ) : ℤ)
    push_cast
    rfl
  have eq_counts : (L.childR : ℤ)+(G : ℤ)=(L.counts : ℤ) := by
    change _=((L.childR+G : ℕ) : ℤ)
    push_cast
    rfl
  have eq_selected : (L.counts : ℤ)+(G : ℤ)=(L.selected : ℤ) := by
    change _=((L.counts+G : ℕ) : ℤ)
    push_cast
    rfl
  have eq_maskBase : (L.selected : ℤ)+(G : ℤ)=(L.maskBase : ℤ) := by
    change _=((L.selected+G : ℕ) : ℤ)
    push_cast
    rfl
  have eq_terminalMasks : (L.maskBase : ℤ)+(T : ℤ)=(L.terminalMasks : ℤ) := by
    change _=((L.maskBase+T : ℕ) : ℤ)
    push_cast
    rfl
  have eq_masksL : (L.terminalMasks : ℤ)+(T : ℤ)=(L.masksL : ℤ) := by
    change _=((L.terminalMasks+T : ℕ) : ℤ)
    push_cast
    rfl
  have eq_masksR : (L.masksL : ℤ)+(T : ℤ)=(L.masksR : ℤ) := by
    change _=((L.masksL+T : ℕ) : ℤ)
    push_cast
    rfl
  have eq_base : (L.masksR : ℤ)+(T : ℤ)=(L.base : ℤ) := by
    change _=((L.masksR+T : ℕ) : ℤ)
    push_cast
    rfl
  have eq_rowOut : (L.bitBase : ℤ)+(W : ℤ)=(L.rowOut : ℤ) := by
    change _=((L.bitBase+W : ℕ) : ℤ)
    push_cast
    rfl
  have eq_bitBase : (L.base : ℤ)+2*(2*(W : ℤ)+4*(T : ℤ)+2)=(L.bitBase : ℤ) := by
    change _=((L.base+2*(2*W+4*T+2) : ℕ) : ℤ)
    push_cast
    rfl
  have eq_work : (L.rowOut : ℤ)+2=(L.work : ℤ) := by
    change _=((L.rowOut+2 : ℕ) : ℤ)
    push_cast
    rfl
  have hbitWord : (L.base : ℤ)+2*(2*(W : ℤ)+4*(T : ℤ)+2)≤lim.word := by
    rw [eq_bitBase]
    exact word L.bitBase (hbb.trans hwork)
  apply Meets.of_body (p := 1) (by rfl : program[1]?=some (body 0))
  unfold body time LightNatPower.time
  light_set (W : ℕ) using heqW
  light_set (G : ℕ) using hgroupZ
  light_set (R : ℕ) using hcapZ
  have hp := (LightNatPower.program_meets (d := d+1) (b := 2) (e := W) μ (word W hW)
    (fun i hi => word (2^i) ((Nat.pow_le_pow_right (by decide) hi).trans hT))).append [body 0]
  unfold LightNatPower.time at hp
  change Meets lim program 0 (d+1) _ μ _ _ at hp
  light_call hp using W,width,LightNatPower.time with power μ₁ ⟨hpower,hmem⟩
  subst μ₁
  have hpower' : power=(T : ℤ) := hpower
  have hpowerNonneg : (0 : ℤ)≤power := by rw [hpower']; exact Int.natCast_nonneg T
  light_set (massBound N NB NC R : ℕ) using hMZ
  light_set (C : ℕ) using hCZ
  light_set (ReportingHostWantedLayout.root dst J : ℕ) using hrootZ
  light_set (L.masks : ℕ) using hmaskZ
  light_set (L.childL : ℕ) using eq_childL
  light_set (L.childR : ℕ) using eq_childR
  light_set (L.counts : ℕ) using eq_counts
  light_set (L.selected : ℕ) using eq_selected
  light_set (L.maskBase : ℕ) using eq_maskBase
  light_set (L.terminalMasks : ℕ) using eq_terminalMasks,hpower'
  light_set (L.masksL : ℕ) using eq_masksL,hpower'
  light_set (L.masksR : ℕ) using eq_masksR,hpower'
  light_set (L.base : ℕ) using eq_base,hpower'
  light_set (L.bitBase : ℕ) using eq_bitBase,hpower'
  light_set (L.rowOut : ℕ) using eq_rowOut
  light_set (L.work : ℕ) using eq_work
  light_store dst (L.root : ℕ) using hb.root_eq
  light_store (dst+1) (L.masks : ℕ)
  light_store (dst+2) (L.childL : ℕ)
  light_store (dst+3) (L.childR : ℕ)
  light_store (dst+4) (L.counts : ℕ)
  light_store (dst+5) (L.selected : ℕ)
  light_store (dst+6) (L.maskBase : ℕ)
  light_store (dst+7) (L.terminalMasks : ℕ)
  light_store (dst+8) (L.masksL : ℕ)
  light_store (dst+9) (L.masksR : ℕ)
  light_store (dst+10) (L.base : ℕ)
  light_store (dst+11) (L.bitBase : ℕ)
  light_store (dst+12) (L.rowOut : ℕ)
  light_store (dst+13) (L.work : ℕ)
  light_set (L.work : ℕ)
  refine ⟨rfl,?_,?_⟩
  · intro i hi
    have hi' : i<14 := by simpa only [values,List.length_map,List.length_cons,List.length_nil] using hi
    interval_cases i <;> simp [values,L,layout,make]
  · intro a ha
    dsimp only
    repeat rw [Function.update_of_ne (by omega)]

theorem program_meets {lim : Limits} {μ : ℕ→ℤ} {dst cover counter h J K N NB NC d : ℕ}
    (hgroup : μ (cover+3)=(groupSize h : ℤ))
    (hcap : μ (counter+2)=(representationCap h J : ℤ))
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth)
    (hs : space dst cover counter h J K N NB NC≤lim.space) :
    Meets lim program 1 d [J,h,K,cover,counter,N,NB,NC,dst] μ (time h J)
      (fun result ν => result=((layout dst h J K N NB NC).work : ℤ) ∧
        SegN ν dst (values (layout dst h J K N NB NC)) ∧ SameOutside μ ν dst 14) :=
  program_meets_relative hgroup hcap hw hd ((relativeSpace_le_space ..).trans hs)

end ThreeSum.LightReportingWantedLayout
