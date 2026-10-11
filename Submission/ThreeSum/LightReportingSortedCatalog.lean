import Submission.ThreeSum.LightReportingPackKeys
import Submission.ThreeSumApsp.Lang.Lib.MergeSort

/-!
# Actual packed-key construction and sorted catalog index

The powers table supplies the physical mask radix. A linear pass retains the
original catalog index as a low digit, and the benchmark's verified merge
sort orders these records without changing their multiplicity or payload.
-/

namespace ThreeSum.LightReportingSortedCatalog

open Light ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostPackedCatalog

variable {lim : Limits}

def body (pPowers pPack pSort : ℕ) : Stmt :=
  .call pPowers [v 5,v 0 +' k 1,k 2] 6 ;;
  .set 7 (M (v 5 +' v 0)) ;;
  .call pPack [v 1,v 2,v 3,v 7,v 4] 8 ;;
  .call pSort [v 3,v 4,v 5] 0

def program : Program :=
  [powTableBody,LightReportingPackKeys.body,sortBody 2 3 4 5,halfBody,mergeBody,copyBody,body 0 1 2]

def time (W n : ℕ) : ℕ := powTableTime (W+1)+LightReportingPackKeys.time n+sortTime n+120

def word (W n : ℕ) : ℕ := LightReportingPackKeys.word (2^W) n+2^(W+1)

theorem procs : MergeSort.Procs program 2 3 4 5 := ⟨rfl,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {W inL inR n dst work d : ℕ}
    (left right : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hleft : inL+n ≤ dst) (hright : inR+n ≤ dst) (hdst : dst+n ≤ work)
    (hpowSpace : work+(W+1) ≤ lim.space) (hsortSpace : work+n ≤ lim.space)
    (hword : (word W n : ℤ) ≤ lim.word)
    (hreadL : ∀ i < n, μ (inL+i) = (left i : ℤ))
    (hreadR : ∀ i < n, μ (inR+i) = (right i : ℤ))
    (hboundL : ∀ i < n, left i < 2^W) (hboundR : ∀ i < n, right i < 2^W)
    (hd : d+Nat.clog 2 n+2 ≤ lim.depth) :
    Meets lim program 6 d [W,inL,inR,n,dst,work] μ (time W n)
      (fun _ μ' =>
        (∃ S : List ℤ, Seg μ' dst S ∧ S.Perm (codes (fun i => pairKey (2^W) (left i) (right i)) n) ∧
          S.Pairwise (· ≤ ·)) ∧ Kept μ μ' dst) := by
  have hpackWord : (LightReportingPackKeys.word (2^W) n : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.le_add_right _ _)).trans hword
  have hpowWord : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.le_add_left _ _)).trans hword
  have h1 : (1 : ℤ) ≤ lim.word := by
    have hh : 1 ≤ (2^(W+1) : ℕ) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact (by exact_mod_cast hh : (1 : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hpowWord
  have hpowBound : ∀ j ≤ W+1, ((2^j : ℕ) : ℤ) ≤ lim.word := by
    intro j hj
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hj)).trans hpowWord
  have h2 : (2 : ℤ) ≤ lim.word := by simpa using hpowBound 1 (by omega)
  apply Meets.of_body (p := 6) (by rfl : program[6]? = some (body 0 1 2))
  unfold body time
  have hp := powTable_meets (P := program) (p := 0) (μ := μ) (d := d+1)
    (dst := work) (L := W+1) (b := 2) rfl hw hpowSpace hpowBound
  light_call hp using LightReportingPackKeys.time,sortTime,powTableTime
    with powRet μ₁ ⟨hpowers,hkeepPowers⟩
  have hradius := powers_of_segment hpowers W le_rfl
  have hradiusN : μ₁ (work+W) = ((2^W : ℕ) : ℤ) := by simpa using hradius
  have hradiusWord := hpowBound W (by omega)
  light_set (2^W : ℕ) using hradius,hradiusN,
    LightReportingPackKeys.time,sortTime,powTableTime
  have hreadL₁ : ∀ i < n, μ₁ (inL+i) = (left i : ℤ) := by
    intro i hi
    exact (hkeepPowers _ (Or.inl (by omega))).trans (hreadL i hi)
  have hreadR₁ : ∀ i < n, μ₁ (inR+i) = (right i : ℤ) := by
    intro i hi
    exact (hkeepPowers _ (Or.inl (by omega))).trans (hreadR i hi)
  have hpack := LightReportingPackKeys.meets (P := program) (p := 1) (d := d+1) (μ := μ₁)
    rfl left right hw hleft hright (hdst.trans (by omega)) hpackWord hreadL₁ hreadR₁ hboundL hboundR
  light_call hpack using LightReportingPackKeys.time,sortTime,powTableTime
    with packRet μ₂ ⟨hpacked,hkeepPack⟩
  have hsort := sort_meets (a := dst) (fr := work) procs hw h1 hpacked
    (by rw [codes_length]; exact hdst) (by rw [codes_length]; exact hsortSpace)
    (d+1) (by rw [codes_length]; omega)
  simp only [codes_length] at hsort
  light_call hsort using LightReportingPackKeys.time,sortTime,powTableTime
    with sortRet μ₃ ⟨⟨S,hseg,hperm,hordered⟩,hkeepSort⟩
  refine ⟨⟨S,hseg,hperm,hordered⟩,?_⟩
  intro i hi
  exact (hkeepSort _ ⟨by omega,Or.inl hi⟩).trans
    ((hkeepPack _ (Or.inl hi)).trans (hkeepPowers _ (Or.inl (by omega))))

theorem time_bound (W n : ℕ) : time W n ≤ 200*(W+1)+200*(n+1)*(Nat.clog 2 n+1) := by
  unfold time powTableTime LightReportingPackKeys.time sortTime
  have hh : n-1 ≤ n := Nat.sub_le _ _
  nlinarith

end ThreeSum.LightReportingSortedCatalog
