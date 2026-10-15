import Submission.ThreeSum.LightTernaryEnumerationSetup
import Submission.ThreeSum.LightNatPower
import Submission.ThreeSum.TernaryBankCanonical
import Submission.ThreeSum.TernaryDimensionBounds

/-! Runtime prefix dimensions, paid occurrence-vector count, and actual compact
bank enumeration. The eight-word header is written by this program. -/
namespace ThreeSum.LightTernaryPrefixSetup
open Light LightSubsetAddress TernaryAddresses TernaryBankEnumeration
open TernaryLocalParameters TernaryDimensionBounds
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

def N (m j : ℕ) : ℕ := 100000000*(j*m)
def T (m j : ℕ) : ℕ := 20384999*(j*m)
def nb (m j : ℕ) : ℕ := (codes (N m j) (T m j)).length

def header (m j F bank work : ℕ) : List ℤ :=
  [N m j,T m j,2*N m j,(F^j:ℕ),nb m j,bank,work,j]

def body (pPower pSetup : ℕ) : Stmt :=
  .set 6 (v 0 *' v 1) ;;
  .set 7 (k 100000000 *' v 6) ;;
  .set 8 (k 20384999 *' v 6) ;;
  .set 9 (k 2 *' v 7) ;;
  .call pPower [v 2,v 0] 10 ;;
  .call pSetup [v 7,v 8,v 4,v 5] 11 ;;
  .store (v 3) (v 7) ;;
  .store (v 3 +' k 1) (v 8) ;;
  .store (v 3 +' k 2) (v 9) ;;
  .store (v 3 +' k 3) (v 10) ;;
  .store (v 3 +' k 4) (v 11) ;;
  .store (v 3 +' k 5) (v 4) ;;
  .store (v 3 +' k 6) (v 5) ;;
  .store (v 3 +' k 7) (v 0) ;;
  .set 0 (v 3)

def word (m j F : ℕ) : ℕ :=
  100000000+2*N m j+j+m+F+(F+1)^(j+1)+4^(N m j+1)+100
def time (m j : ℕ) : ℕ := LightNatPower.time j+LightTernaryEnumerationSetup.time (N m j) (T m j)+500

theorem dimensions (m j : ℕ) :
    N m j=fixedLength (j*m) ∧ T m j=bankCut m j ∧ T m j≤ 2*N m j := by
  unfold N T fixedLength bankCut
  constructor
  · rfl
  constructor
  · ring
  · omega

theorem nb_eq_bankSize (m j : ℕ) : nb m j=bankSize m j :=by
  unfold nb bankSize
  rw [codes_length_eq_bank_card]
  rw [(dimensions m j).1,(dimensions m j).2.1]

variable {lim : Limits} {P : Program}

theorem meets {pMain pPower pSetup pPowers pEnum m j F dst bank work d : ℕ}
    (hmain : P[pMain]?=some (body pPower pSetup))
    (hpower : P[pPower]?=some LightNatPower.body)
    (hsetup : P[pSetup]?=some (LightTernaryEnumerationSetup.body pPowers pEnum))
    (hpowers : P[pPowers]?=some powTableBody)
    (henum : P[pEnum]?=some (LightTernaryEnumeration.body pEnum))
    (μ : ℕ→ ℤ) (hw : (lim.space:ℤ)≤ lim.word)
    (hbank : bank+nb m j≤ work) (hwork : work+(2*N m j+1)≤ dst)
    (hspace : dst+8≤ lim.space) (hword : (word m j F:ℤ)≤ lim.word)
    (hd : d+N m j+3≤ lim.depth) :
    Meets lim P pMain d [j,m,F,dst,bank,work] μ (time m j)
      (fun r ν=>r=(dst:ℤ) ∧ Seg ν dst (header m j F bank work) ∧
        Seg ν bank ((codes (N m j) (T m j)).map (fun (c:ℕ)=>(c:ℤ))) ∧
        Powers ν work (2*N m j) ∧ Kept μ ν bank) := by
  have h4nonneg : (0:ℤ)≤ (4:ℤ)^(N m j) := by positivity
  have hbudget (x : ℕ) (hx : x≤ word m j F) : (x:ℤ)≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hN:= hbudget (2*N m j) (by unfold word; generalize 4^(N m j+1)=q; omega)
  have hJ:= hbudget j (by unfold word; generalize 4^(N m j+1)=q; omega)
  have hM:= hbudget m (by unfold word; generalize 4^(N m j+1)=q; omega)
  have hF:= hbudget F (by unfold word; generalize 4^(N m j+1)=q; omega)
  have hconstant:= hbudget 100000000 (by unfold word; generalize 4^(N m j+1)=q; omega)
  have hconstantT : (20384999:ℤ)≤ lim.word := by omega
  have hprod : j*m≤ N m j := by unfold N; omega
  have hjm:= hbudget (j*m) (by unfold word; generalize 4^(N m j+1)=q; omega)
  have hcut:= (dimensions m j).2.2
  have hT:= hbudget (T m j) (by unfold word; generalize 4^(N m j+1)=q; omega)
  have hbig:= hbudget ((F+1)^(j+1)) (by unfold word; generalize 4^(N m j+1)=q; omega)
  have hmask:= hbudget (4^(N m j+1)) (by unfold word; generalize 4^(N m j+1)=q; omega)
  have hpbound : F^j≤ (F+1)^(j+1) :=
    (Nat.pow_le_pow_left (Nat.le_succ _) j).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hgroups:= hbudget (F^j) (by unfold word; generalize 4^(N m j+1)=q; omega)
  have hdW : (dst:ℤ)≤ lim.word := (Int.ofNat_le.mpr (by omega : dst≤ lim.space)).trans hw
  have hbW : (bank:ℤ)≤ lim.word := (Int.ofNat_le.mpr (by omega : bank≤ lim.space)).trans hw
  have hwW : (work:ℤ)≤ lim.word := (Int.ofNat_le.mpr (by omega : work≤ lim.space)).trans hw
  have hpm : (j:ℤ)*(m:ℤ)≤ lim.word := by simpa using hjm
  have hNN : (100000000:ℤ)*((j:ℤ)*(m:ℤ))≤ lim.word := by
    have hh:= hbudget (N m j) (by unfold word; generalize 4^(N m j+1)=q; omega)
    simpa [N,mul_assoc] using hh
  have hTT : (20384999:ℤ)*((j:ℤ)*(m:ℤ))≤ lim.word := by
    simpa [T,mul_assoc] using hT
  have hNP : LightNatPower.time j+LightTernaryEnumerationSetup.time (N m j) (T m j)+500=time m j:= rfl
  apply Meets.of_body hmain
  unfold body time
  light_set (j*m:ℕ) using LightNatPower.time,LightTernaryEnumerationSetup.time
  light_set (N m j:ℕ) using N,mul_assoc,LightNatPower.time,LightTernaryEnumerationSetup.time
  light_set (T m j:ℕ) using T,mul_assoc,LightNatPower.time,LightTernaryEnumerationSetup.time
  light_set (2*N m j:ℕ) using LightNatPower.time,LightTernaryEnumerationSetup.time
  light_call (LightNatPower.bounded_meets (d:= d+1) hpower μ hJ hbig)
    using LightNatPower.time,LightTernaryEnumerationSetup.time with rr ξ ⟨hr,hξ⟩
  subst ξ
  light_call (LightTernaryEnumerationSetup.meets (d:= d+1) hsetup hpowers henum
    hw (by omega) hmask hcut hbank (by omega))
    using LightNatPower.time,LightTernaryEnumerationSetup.time with bb ν ⟨hbb,hseg,hpow,hkeep⟩
  have hnbW : (nb m j:ℤ)≤ lim.word := by
    have hs : nb m j≤ lim.space := by omega
    exact (Int.ofNat_le.mpr hs).trans hw
  light_store dst (N m j) using LightNatPower.time,LightTernaryEnumerationSetup.time
  light_store (dst+1) (T m j) using LightNatPower.time,LightTernaryEnumerationSetup.time
  light_store (dst+2) (2*N m j) using LightNatPower.time,LightTernaryEnumerationSetup.time
  light_store (dst+3) (F^j) using hr,LightNatPower.time,LightTernaryEnumerationSetup.time
  light_store (dst+4) (nb m j) using nb,hbb,LightNatPower.time,LightTernaryEnumerationSetup.time
  light_store (dst+5) bank using LightNatPower.time,LightTernaryEnumerationSetup.time
  light_store (dst+6) work using LightNatPower.time,LightTernaryEnumerationSetup.time
  light_store (dst+7) j using LightNatPower.time,LightTernaryEnumerationSetup.time
  light_set (dst:ℕ) using LightNatPower.time,LightTernaryEnumerationSetup.time
  refine ⟨rfl,?_,?_,?_,?_⟩
  · simp [header,seg_cons,Nat.add_assoc]
  · intro i hi
    have hs:= hseg i hi
    simp only [List.length_map] at hi
    dsimp [nb] at hbank
    simp only [Function.update_of_ne (by omega : bank+i≠ dst+7),
      Function.update_of_ne (by omega : bank+i≠ dst+6),Function.update_of_ne (by omega : bank+i≠ dst+5),
      Function.update_of_ne (by omega : bank+i≠ dst+4),Function.update_of_ne (by omega : bank+i≠ dst+3),
      Function.update_of_ne (by omega : bank+i≠ dst+2),Function.update_of_ne (by omega : bank+i≠ dst+1),
      Function.update_of_ne (by omega : bank+i≠ dst)]
    exact hs
  · intro i hi
    simp only [Function.update_of_ne (by omega : work+i≠ dst+7),
      Function.update_of_ne (by omega : work+i≠ dst+6),Function.update_of_ne (by omega : work+i≠ dst+5),
      Function.update_of_ne (by omega : work+i≠ dst+4),Function.update_of_ne (by omega : work+i≠ dst+3),
      Function.update_of_ne (by omega : work+i≠ dst+2),Function.update_of_ne (by omega : work+i≠ dst+1),
      Function.update_of_ne (by omega : work+i≠ dst)]
    exact hpow i hi
  · intro a ha
    have hh:= (hkeep a ⟨by omega,Or.inl ha⟩)
    simp only [Function.update_of_ne (by omega : a≠ dst+7),
      Function.update_of_ne (by omega : a≠ dst+6),Function.update_of_ne (by omega : a≠ dst+5),
      Function.update_of_ne (by omega : a≠ dst+4),Function.update_of_ne (by omega : a≠ dst+3),
      Function.update_of_ne (by omega : a≠ dst+2),Function.update_of_ne (by omega : a≠ dst+1),
      Function.update_of_ne (by omega : a≠ dst)]
    exact hh

def program : Program := [body 1 2,LightNatPower.body,LightTernaryEnumerationSetup.body 3 4,
  powTableBody,LightTernaryEnumeration.body 4]

theorem program_meets {m j F dst bank work d : ℕ} (μ : ℕ→ ℤ)
    (hw : (lim.space:ℤ)≤ lim.word) (hbank : bank+nb m j≤ work)
    (hwork : work+(2*N m j+1)≤ dst) (hspace : dst+8≤ lim.space)
    (hword : (word m j F:ℤ)≤ lim.word) (hd : d+N m j+3≤ lim.depth) :
    Meets lim program 0 d [j,m,F,dst,bank,work] μ (time m j)
      (fun r ν=>r=(dst:ℤ) ∧ Seg ν dst (header m j F bank work) ∧
        Seg ν bank ((codes (N m j) (T m j)).map (fun (c:ℕ)=>(c:ℤ))) ∧
        Powers ν work (2*N m j) ∧ Kept μ ν bank) :=
  meets rfl rfl rfl rfl rfl μ hw hbank hwork hspace hword hd

theorem time_bound (m j : ℕ) :
    time m j≤ 600*(N m j+1)*(nb m j+1)+20*j+600 := by
  have hh:= LightTernaryEnumerationSetup.time_bound (N m j) (T m j)
  unfold time LightNatPower.time nb
  nlinarith only [hh]

theorem nb_le_mask (m j : ℕ) : nb m j≤ 4^(N m j) := by
  unfold nb
  rw [codes_length_eq_bank_card]
  have hh : (TernaryBank.bank (N m j) (T m j)).card≤ 3^(N m j) :=
    (Finset.card_le_univ _).trans_eq (by simp [TernaryJointType.TritWord])
  exact hh.trans (Nat.pow_le_pow_left (by decide) _)

def workAt (free m j : ℕ) : ℕ := free+4^(N m j)
def headerAt (free m j : ℕ) : ℕ := workAt free m j+2*N m j+1
def endAt (free m j : ℕ) : ℕ := headerAt free m j+8

/-- The physical locations are derived from the free pointer and a computed
mask span. No header address, bank length, or power-table pointer is advice. -/
def allocateBody (pPower pPrefix : ℕ) : Stmt :=
  .set 4 (v 0 *' v 1) ;;
  .set 5 (k 100000000 *' v 4) ;;
  .call pPower [k 4,v 5] 6 ;;
  .set 7 (v 3 +' v 6) ;;
  .set 8 (v 7 +' k 2 *' v 5 +' k 1) ;;
  .call pPrefix [v 0,v 1,v 2,v 8,v 3,v 7] 0

def allocateTime (m j : ℕ) : ℕ := LightNatPower.time (N m j)+time m j+200

theorem allocate_meets {pMain pPower pPrefix pSetup pPowers pEnum m j F free d : ℕ}
    (hmain : P[pMain]?=some (allocateBody pPower pPrefix))
    (hpower : P[pPower]?=some LightNatPower.body)
    (hprefix : P[pPrefix]?=some (body pPower pSetup))
    (hsetup : P[pSetup]?=some (LightTernaryEnumerationSetup.body pPowers pEnum))
    (hpowers : P[pPowers]?=some powTableBody)
    (henum : P[pEnum]?=some (LightTernaryEnumeration.body pEnum))
    (μ : ℕ→ ℤ) (hw : (lim.space:ℤ)≤ lim.word)
    (hspace : endAt free m j≤ lim.space) (hword : (word m j F:ℤ)≤ lim.word)
    (hd : d+N m j+4≤ lim.depth) :
    Meets lim P pMain d [j,m,F,free] μ (allocateTime m j)
      (fun r ν=>r=(headerAt free m j:ℤ) ∧
        Seg ν (headerAt free m j) (header m j F free (workAt free m j)) ∧
        Seg ν free ((codes (N m j) (T m j)).map (fun (c:ℕ)=>(c:ℤ))) ∧
        Powers ν (workAt free m j) (2*N m j) ∧ Kept μ ν free) := by
  have hbudget (x : ℕ) (hx : x≤ word m j F) : (x:ℤ)≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hprod : j*m≤ N m j := by unfold N; omega
  have hN:= hbudget (N m j) (by unfold word; generalize 4^(N m j+1)=q; omega)
  have h2N:= hbudget (2*N m j) (by unfold word; generalize 4^(N m j+1)=q; omega)
  have hjm:= hbudget (j*m) (by unfold word; generalize 4^(N m j+1)=q; omega)
  have hconstant:= hbudget 100000000 (by unfold word; generalize 4^(N m j+1)=q; omega)
  have hmask:= hbudget (4^(N m j+1)) (by unfold word; generalize 4^(N m j+1)=q; omega)
  have hspan : ((4^(N m j):ℕ):ℤ)≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))).trans hmask
  have h4 : (4:ℤ)≤ lim.word := by
    have hh : 4≤ 4^(N m j+1) := by
      have hp : 1≤ 4^(N m j) := Nat.one_le_pow _ _ (by decide)
      simpa [pow_succ] using Nat.mul_le_mul_right 4 hp
    exact (Int.ofNat_le.mpr hh).trans hmask
  have hpow (i : ℕ) (hi : i≤ N m j) : ((4^i:ℕ):ℤ)≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hi)).trans hspan
  have hspaceZ : ((endAt free m j:ℕ):ℤ)≤(lim.space:ℤ) := by exact_mod_cast hspace
  dsimp [endAt,headerAt,workAt] at hspaceZ
  push_cast at hspaceZ
  norm_num only [Nat.cast_ofNat] at hspaceZ
  have hpNnonneg : (0:ℤ)≤(4:ℤ)^(N m j) := by positivity
  have hbase : (free:ℤ)≤lim.word :=by omega
  have hwork : (workAt free m j:ℤ)≤lim.word :=by
    dsimp [workAt]; push_cast; norm_num only [Nat.cast_ofNat]; omega
  have hheader : (headerAt free m j:ℤ)≤lim.word :=by
    dsimp [headerAt,workAt]; push_cast; norm_num only [Nat.cast_ofNat]; omega
  have hNN : (100000000:ℤ)*((j:ℤ)*(m:ℤ))≤ lim.word := by simpa [N] using hN
  have hworkAdd : (free:ℤ)+(4:ℤ)^(N m j)≤ lim.word := by simpa [workAt] using hwork
  have hheaderAdd : (workAt free m j:ℤ)+2*(N m j:ℤ)+1≤ lim.word := by
    simpa [headerAt] using hheader
  apply Meets.of_body hmain
  unfold allocateBody allocateTime
  light_set (j*m:ℕ) using LightNatPower.time,time
  light_set (N m j:ℕ) using N,LightNatPower.time,time
  light_call (LightNatPower.meets (d:= d+1) hpower μ hN hpow)
    using LightNatPower.time,time with rr ξ ⟨hr,hξ⟩
  subst ξ
  light_set (workAt free m j:ℕ) using hr,workAt,Nat.cast_ofNat,LightNatPower.time,time
  light_set (headerAt free m j:ℕ) using headerAt,LightNatPower.time,time
  light_call (meets (d:= d+1) (m:=m) (j:=j) (F:=F) (dst:=headerAt free m j)
    (bank:=free) (work:=workAt free m j) hprefix hpower hsetup hpowers henum μ hw
    (by unfold workAt; exact Nat.add_le_add_left (nb_le_mask m j) _)
    (by unfold headerAt; omega) hspace hword (by omega))
    using LightNatPower.time,time
    with result ν hresult
  exact hresult

def allocatedProgram : Program := program++[allocateBody 1 0]

theorem allocated_program_meets {m j F free d : ℕ} (μ : ℕ→ ℤ)
    (hw : (lim.space:ℤ)≤ lim.word) (hspace : endAt free m j≤ lim.space)
    (hword : (word m j F:ℤ)≤ lim.word) (hd : d+N m j+4≤ lim.depth) :
    Meets lim allocatedProgram 5 d [j,m,F,free] μ (allocateTime m j)
      (fun r ν=>r=(headerAt free m j:ℤ) ∧
        Seg ν (headerAt free m j) (header m j F free (workAt free m j)) ∧
        Seg ν free ((codes (N m j) (T m j)).map (fun (c:ℕ)=>(c:ℤ))) ∧
        Powers ν (workAt free m j) (2*N m j) ∧ Kept μ ν free) :=
  allocate_meets rfl rfl rfl rfl rfl rfl μ hw hspace hword hd

theorem allocateTime_bound (m j : ℕ) :
    allocateTime m j≤ 1000*(N m j+1)*(nb m j+1)+20*j+1000 := by
  have hh:= time_bound m j
  unfold allocateTime LightNatPower.time
  nlinarith only [hh,Nat.zero_le (N m j*nb m j)]

theorem allocateTime_le_bank_work {m : ℕ} (hm : 0<m) (j : ℕ) :
    allocateTime m j≤2000*(N m j+1)*(nb m j+1) :=by
  have hjm : j≤j*m :=Nat.le_mul_of_pos_right _ hm
  have hjN : j≤N m j :=by unfold N; omega
  have hh:=allocateTime_bound m j
  nlinarith only [hh,hjN,Nat.zero_le (N m j*nb m j),Nat.zero_le (nb m j)]

end ThreeSum.LightTernaryPrefixSetup
