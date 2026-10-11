import Submission.ThreeSum.ReportingHostPackedCatalog
import Submission.ThreeSum.LightBandLookup
import Submission.ThreeSumApsp.Lang.Lib.Emod

/-!
# Actual logarithmic lookup of an original prefix-catalog index

The program constructs its own powers, forms the physical query pair key,
performs division-free binary search over the sorted packed records, and
uses the benchmark's binary remainder algorithm to recover the original
catalog position. No full-catalog scan or index oracle occurs.
-/

namespace ThreeSum.LightReportingCatalogLookup

open Light ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostPackedCatalog

set_option maxHeartbeats 1500000
set_option maxRecDepth 8000

variable {lim : Limits}

def valueBound (W n : ℕ) : ℕ := 2^(2*W)*(n+1)

def word (W n : ℕ) : ℕ :=
  4*valueBound W n+4*(n+1)+n+2^(2*W+2)+2^(W+1)+16

theorem word_components (U n A B : ℕ) :
    U ≤ 4*U+4*(n+1)+n+A+B+16 ∧ A ≤ 4*U+4*(n+1)+n+A+B+16 ∧
    n+A+16 ≤ 4*U+4*(n+1)+n+A+B+16 ∧ 4*U+4*(n+1)+16 ≤ 4*U+4*(n+1)+n+A+B+16 := by omega

theorem word_value (W n : ℕ) : valueBound W n ≤ word W n := (word_components _ _ _ _).1
theorem word_power (W n : ℕ) : 2^(2*W+2) ≤ word W n := (word_components _ _ _ _).2.1
theorem word_search (W n : ℕ) : n+2^((2*W+1)+1)+16 ≤ word W n := (word_components _ _ _ _).2.2.1
theorem word_emod (W n : ℕ) : 4*valueBound W n+4*(n+1)+16 ≤ word W n := (word_components _ _ _ _).2.2.2

def body (pPowers pSearch pEmod : ℕ) : Stmt :=
  .call pPowers [v 5,k 2 *' v 0 +' k 2,k 2] 6 ;;
  .set 7 (M (v 5 +' v 0)) ;;
  .set 8 (((v 3 +' v 7 *' v 4) *' (v 1 +' k 1)) +' v 1) ;;
  .call pSearch [v 2,v 1,v 8,v 5,k 2 *' v 0 +' k 1,k 0] 9 ;;
  .set 10 (M (v 2 +' v 9 -' k 1)) ;;
  .call pEmod [v 10,v 1 +' k 1,v 5] 0

def program : Program := [powTableBody,LightBandLookup.searchBody 1,emodBody,body 0 1 2]

def time (W n : ℕ) : ℕ := powTableTime (2*W+2)+LightBandLookup.searchTime (2*W+1)+
  100*(Nat.log 2 (valueBound W n+1)+2)+200

theorem program_meets {μ : ℕ → ℤ} {W n src work i d : ℕ} {S : List ℤ}
    (left right : ℕ → ℕ) (hi : i < n)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ work) (hpowSpace : work+(2*W+2) ≤ lim.space)
    (hemodSpace : work+(Nat.log 2 (valueBound W n+1)+2) ≤ lim.space)
    (hword : (word W n : ℤ) ≤ lim.word)
    (hn : n ≤ 2^(2*W))
    (hboundL : ∀ j < n, left j < 2^W) (hboundR : ∀ j < n, right j < 2^W)
    (hunique : ∀ a < n, ∀ b < n,
      pairKey (2^W) (left a) (right a)=pairKey (2^W) (left b) (right b) → a=b)
    (hperm : S.Perm (codes (fun j => pairKey (2^W) (left j) (right j)) n))
    (hsorted : S.Pairwise (· ≤ ·)) (hseg : Seg μ src S)
    (hd : d+2*W+2 ≤ lim.depth) :
    Meets lim program 3 d [W,n,src,left i,right i,work] μ (time W n)
      (fun r μ' => r = (i : ℤ) ∧ Kept μ μ' work) := by
  let key : ℕ → ℕ := fun j => pairKey (2^W) (left j) (right j)
  let threshold : ℕ := key i*(n+1)+n
  let K := BinarySearch.upperBound (fun j => S.getD j 0) n (threshold : ℤ)
  have hlen : S.length=n := hperm.length_eq.trans (codes_length key n)
  have hkey : key i < 2^(2*W) := by
    simpa only [key,← pow_mul,Nat.mul_comm] using pairKey_lt (hboundL i hi) (hboundR i hi)
  have hthreshold : threshold < valueBound W n := by unfold threshold valueBound; nlinarith
  have hcode : packed key n i < valueBound W n := packed_lt hi hkey
  have hUword : (valueBound W n : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (word_value W n)).trans hword
  have hthWord : (threshold : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hthreshold.le).trans hUword
  have hcodeWord : (packed key n i : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hcode.le).trans hUword
  have hpowWord : ((2^(2*W+2) : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (word_power W n)).trans hword
  have hpowBound : ∀ j ≤ 2*W+2, ((2^j : ℕ) : ℤ) ≤ lim.word := by
    intro j hj
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hj)).trans hpowWord
  have hsearchWord : ((n+2^((2*W+1)+1)+16 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (word_search W n)).trans hword
  have hEmod : Light.Emod.Pre lim (n+1) (valueBound W n) work :=
    ⟨by omega,hw,by
      have hh := (Int.ofNat_le.mpr (word_emod W n)).trans hword
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh,hemodSpace⟩
  have hkeyN : key i ≤ valueBound W n := by unfold valueBound; nlinarith
  have hmulN : 2^W*right i ≤ valueBound W n := by unfold key pairKey at hkeyN; omega
  have hprodN : key i*(n+1) ≤ valueBound W n := by unfold threshold at hthreshold; omega
  have hmulZ : ((2^W : ℕ) : ℤ)*(right i : ℤ) ≤ lim.word :=
    (by exact_mod_cast hmulN : ((2^W : ℕ) : ℤ)*(right i : ℤ) ≤ (valueBound W n : ℤ)).trans hUword
  have hkeyZ : (left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ) ≤ lim.word :=
    (by exact_mod_cast hkeyN : (left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ) ≤ (valueBound W n : ℤ)).trans hUword
  have hprodZ : ((left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ))*((n : ℤ)+1) ≤ lim.word :=
    (by exact_mod_cast hprodN :
      ((left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ))*((n : ℤ)+1) ≤ (valueBound W n : ℤ)).trans hUword
  have hmul0 : 0 ≤ ((2^W : ℕ) : ℤ)*(right i : ℤ) := by positivity
  have hprod0 : 0 ≤ ((left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ))*((n : ℤ)+1) := by positivity
  have hthZ : ((left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ))*((n : ℤ)+1)+(n : ℤ) ≤ lim.word := by
    simpa only [threshold,key,pairKey,Nat.cast_add,Nat.cast_mul,Nat.cast_one] using hthWord
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hmulZ hkeyZ hprodZ hmul0 hprod0 hthZ
  have hhit := upperBound_hit hi hunique hperm hsorted
  change 0 < K ∧ K ≤ n ∧ S.getD (K-1) 0 = (packed key n i : ℤ) at hhit
  have hnWidth : n < 2^(2*W+1) := by
    have hp : 0 < 2^(2*W) := Nat.two_pow_pos _
    rw [pow_succ]
    omega
  apply Meets.of_body (p := 3) (by rfl : program[3]? = some (body 0 1 2))
  unfold body time
  have hp := powTable_meets (P := program) (p := 0) (d := d+1) (μ := μ)
    (dst := work) (L := 2*W+2) (b := 2) rfl hw hpowSpace hpowBound
  light_call hp using powTableTime,LightBandLookup.searchTime
    with powRet μ₁ ⟨hpowers,hkeepPowers⟩
  have hPowers : Powers μ₁ work (2*W+1) := powers_of_segment hpowers
  have hradius := hPowers W (by omega)
  have hradiusN : μ₁ (work+W) = ((2^W : ℕ) : ℤ) := by simpa using hradius
  have hradiusWord := hpowBound W (by omega)
  light_set (2^W : ℕ) using hradius,hradiusN,powTableTime,LightBandLookup.searchTime
  light_set (threshold : ℕ) using threshold,key,pairKey,powTableTime,LightBandLookup.searchTime
  have hread : ∀ j < n, μ₁ (src+j) = S.getD j 0 := by
    intro j hj
    exact (hkeepPowers _ (Or.inl (by omega))).trans (hseg.getD (by omega) 0)
  have hsort : ∀ a b, a ≤ b → b < n → S.getD a 0 ≤ S.getD b 0 := by
    simpa only [hlen] using sorted_getD_le hsorted
  have hsearch := LightBandLookup.search_meets (P := program) (pSearch := 1)
    (a := src) (n := n) (powers := work) (W := 2*W+1) (x := (threshold : ℤ)) rfl μ₁
    (fun j => S.getD j 0) K hw (hsrc.trans (by omega)) (by omega) hsearchWord hread hPowers
    (BinarySearch.upperBound_correct _ _ _ hsort) (2*W+1) 0 le_rfl (by omega)
    (by omega) (d+1) (by omega)
  light_call hsearch using threshold,powTableTime,LightBandLookup.searchTime
    with found μ₂ ⟨hfound,hmem⟩
  subst μ₂
  have hreadHit : μ₁ (src+(K-1)) = (packed key n i : ℤ) :=
    (hread _ (by omega)).trans hhit.2.2
  have hreadHitZ : μ₁ (((src : ℤ)+(K : ℤ)-1).toNat) = (packed key n i : ℤ) := by
    have ha : ((src : ℤ)+(K : ℤ)-1).toNat = src+(K-1) := by omega
    rw [ha]
    exact hreadHit
  have hreadHitSub : μ₁ (src+K-1) = (packed key n i : ℤ) := by
    have ha : src+K-1 = src+(K-1) := by omega
    rw [ha]
    exact hreadHit
  light_set (packed key n i : ℕ) using hfound,hreadHit,hreadHitZ,hreadHitSub,powTableTime,LightBandLookup.searchTime
  have hem := emod_meets (P := program) (p := 2) (d := d+1) (μ := μ₁)
    (x := (packed key n i : ℤ)) rfl hEmod (by simpa only [Int.abs_natCast] using (Int.ofNat_le.mpr hcode.le))
  have hemTime : emodTime (packed key n i : ℤ).natAbs (n+1) ≤
      100*(Nat.log 2 (valueBound W n+1)+2) := by
    have hh := emodRounds_le (M := n+1) hcode.le
    simpa only [Int.natAbs_natCast,emodTime] using
      (show 43*emodRounds (packed key n i) (n+1)+34 ≤ 100*(Nat.log 2 (valueBound W n+1)+2) by omega)
  light_call (hem.mono_time hemTime) using powTableTime,LightBandLookup.searchTime
    with index μ₃ ⟨hindex,hkeepEmod⟩
  refine ⟨hindex.trans (packed_emod hi),?_⟩
  intro j hj
  exact (hkeepEmod j hj).trans (hkeepPowers j (Or.inl hj))

end ThreeSum.LightReportingCatalogLookup
