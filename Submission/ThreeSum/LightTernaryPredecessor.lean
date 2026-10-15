import Submission.ThreeSum.LightTernaryRankTable
import Submission.ThreeSum.TernaryEuler

/-! Actual predecessor addresses in two compressed dictionaries. -/

namespace ThreeSum.LightTernaryPredecessor

open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def digit (N low high m : ℕ) : ℕ := LightTernaryCodes.digit (2*N) low high m

def code (N low high m : ℕ) : ℕ :=
  if digit N low high m=1 then LightTernaryCodes.zeroCode (2*N) low high m
  else LightTernaryCodes.oneCode (2*N) high m

def predRank (N low high m : ℕ) : ℕ :=
  LightTernaryRank.partialRank N (code N low high m) N

def key (N low high m T active bankVals nearVals bankIndex nearIndex : ℕ) : ℕ :=
  if active=0 ∨ digit N low high m=0 then bankVals
  else if predRank N low high m≤T then bankVals+bankIndex else nearVals+nearIndex

def weight (N low high m active : ℕ) : ℕ :=
  if active=0 then 0 else digit N low high m

theorem code_lt {N low high m : ℕ} (hm : m<2^(2*N)) :
    code N low high m<2^(2*N) := by
  unfold code LightTernaryCodes.zeroCode LightTernaryCodes.oneCode
  split_ifs
  · exact (eraseMask_le ((eraseMask_le hm).trans_lt hm)).trans_lt
      ((eraseMask_le hm).trans_lt hm)
  · exact (eraseMask_le hm).trans_lt hm

theorem code_canonical {N : ℕ} (w : TritWord N) (i : Fin N) (hi : 0<(w i).val) :
    code N (low i) (high i) (address w)=address (predecessor w i) := by
  have hd := digit_eq w i
  have h2 := (w i).isLt
  unfold code digit
  rw [hd]
  by_cases h1 : (w i).val=1
  · rw [if_pos h1,zeroCode_eq_update]
    apply congrArg address
    funext j
    unfold predecessor
    simp only [Function.update_apply]
    split_ifs
    · apply Fin.ext
      simp [predDigit,h1]
    · rfl
  · have htwo : (w i).val=2 := by omega
    rw [if_neg h1,oneCode_eq_update_of_pos w i hi]
    apply congrArg address
    funext j
    unfold predecessor
    simp only [Function.update_apply]
    split_ifs
    · apply Fin.ext
      simp [predDigit,htwo]
    · rfl

def lowerBody (pZero pErase : ℕ) : Stmt :=
  .ite (v 14 =' k 1)
    (.call pZero [k 2 *' v 0,v 1,v 2,v 3,v 4] 15)
    (.call pErase [k 2 *' v 0,v 2,v 3,k 2 *' v 0,v 4] 15)

def tailBody (pRank pSearch : ℕ) : Stmt :=
  .call pRank [v 0,v 15,v 4] 16 ;;
  .ite (v 13 =' k 0) (.set 0 (v 7))
    (.ite (v 14 =' k 0) (.set 0 (v 7))
      (.ite (v 16 ≤' v 12)
        (.call pSearch [v 5,v 6,v 15,v 4,v 11,k 0] 17 ;;
          .set 0 (v 7 +' v 17 -' k 1))
        (.call pSearch [v 8,v 9,v 15,v 4,v 11,k 0] 17 ;;
          .set 0 (v 10 +' v 17 -' k 1))))

/-- N, low, high, wordcode, powers, bank codes/count/values,
near codes/count/values, lookup width, bank rank cutoff, active-coordinate flag. -/
def body (pDigit pZero pErase pRank pSearch : ℕ) : Stmt :=
  .call pDigit [k 2 *' v 0,v 1,v 2,v 3,v 4] 14 ;;
  lowerBody pZero pErase ;; tailBody pRank pSearch

def time (N L : ℕ) : ℕ := LightTernaryCodes.digitTime (2*N)+
  LightTernaryCodes.zeroTime (2*N)+LightMaskErase.time (2*N)+
  LightTernaryRank.time N+LightBandLookup.searchTime L+500

variable {lim : Limits} {P : Program}

theorem meets {pMain pDigit pZero pErase pRank pSearch N low high m powers
    bank nb bankVals near nn nearVals L T active bi ni d : ℕ}
    (hmain : P[pMain]?=some (body pDigit pZero pErase pRank pSearch))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hrank : P[pRank]?=some (LightTernaryRank.body pDigit))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (bankCodes nearCodes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbankSpace : bank+nb ≤ lim.space) (hnearSpace : near+nn ≤ lim.space)
    (hbankVals : bankVals+nb ≤ lim.space) (hnearVals : nearVals+nn ≤ lim.space)
    (hspace : powers+(2*N+1) ≤ lim.space)
    (hword : ((nb+nn+2^(2*N+1)+2*N+32 : ℕ) : ℤ) ≤ lim.word)
    (hcontrols : ((T+active+16 : ℕ) : ℤ) ≤ lim.word)
    (hbankRead : ∀ j<nb, μ (bank+j)=(bankCodes j : ℤ))
    (hnearRead : ∀ j<nn, μ (near+j)=(nearCodes j : ℤ))
    (hbankSorted : ∀ j k, j<k → k<nb → bankCodes j<bankCodes k)
    (hnearSorted : ∀ j k, j<k → k<nn → nearCodes j<nearCodes k)
    (hpowers : Powers μ powers (2*N)) (hm : m<2^(2*N))
    (hlow : low≤2*N) (hhigh : high≤2*N) (hL : L≤2*N)
    (hnb : nb<2^L) (hnn : nn<2^L) (hnbpos : 0<nb)
    (hbi : active≠0 → digit N low high m≠0 → predRank N low high m≤T →
      bi<nb ∧ bankCodes bi=code N low high m)
    (hni : active≠0 → digit N low high m≠0 → T<predRank N low high m →
      ni<nn ∧ nearCodes ni=code N low high m)
    (hd : d+2*N+3 ≤ lim.depth) :
    Meets lim P pMain d [N,low,high,m,powers,bank,nb,bankVals,near,nn,nearVals,L,T,active]
      μ (time N L)
      (fun r ν => r=(key N low high m T active bankVals nearVals bi ni : ℤ) ∧ ν=μ) := by
  have hpowWord : ((2^(2*N+1) : ℕ) : ℤ) ≤ lim.word := by omega
  have hscalar : ((2*N+16 : ℕ) : ℤ) ≤ lim.word := by omega
  have htwoword : (2 : ℤ) ≤ lim.word := by omega
  have hcode := code_lt (low := low) (high := high) hm
  have hrankBound := LightTernaryRank.partialRank_le N (code N low high m) N
  have hpredWord : (code N low high m : ℤ) < lim.word := by
    have hp : 2^(2*N)≤2^(2*N+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (Int.ofNat_lt.mpr hcode).trans_le ((Int.ofNat_le.mpr hp).trans hpowWord)
  have hdigitCall := LightTernaryCodes.digit_meets (d := d+1) hdigit herase μ hw
    hspace hpowWord hpowers hlow hhigh hm (by omega) htwoword
  have hzeroCall := LightTernaryCodes.zero_meets (d := d+1) hzero herase μ hw
    hspace hpowWord hpowers hlow hhigh hm (by omega)
  have honeCall := LightMaskErase.meets herase μ hw hspace hpowWord hpowers
    (2*N) high m le_rfl hhigh hm (d+1) (by omega)
  have hrankCall := LightTernaryRank.meets (d := d+1) hrank hdigit herase μ hw
    hspace hpowWord hscalar hpowers hcode (by omega)
  apply Meets.of_body hmain
  unfold body time
  light_call hdigitCall using LightTernaryCodes.digitTime,LightTernaryCodes.zeroTime,
    LightMaskErase.time,LightTernaryRank.time,LightBandLookup.searchTime
    with q ν ⟨hq,hmem⟩
  subst ν
  rcases hq with rfl
  refine Ends.pieceThen
    (T₁ := LightTernaryCodes.zeroTime (2*N)+LightMaskErase.time (2*N)+100)
    (R := fun σ => σ=⟨frame [N,low,high,m,powers,bank,nb,bankVals,near,nn,nearVals,
      L,T,active,digit N low high m,code N low high m],μ⟩)
    ?lower ?tail (hT := by light_time)
  case lower =>
    unfold lowerBody
    light_if h1 hn1 : digit N low high m=1 using digit,
      LightTernaryCodes.digitTime,LightTernaryCodes.zeroTime,LightMaskErase.time,
      LightTernaryRank.time,LightBandLookup.searchTime
    · light_call hzeroCall using digit,LightTernaryCodes.digitTime,
        LightTernaryCodes.zeroTime,LightMaskErase.time,LightTernaryRank.time,
        LightBandLookup.searchTime with z ν ⟨hz,hmem⟩
      subst ν
      rcases hz with rfl
      have h1' : LightTernaryCodes.digit (2*N) low high m=1 := h1
      simp [digit,code,h1',update_frame_setLocal]
    · light_call honeCall using digit,LightTernaryCodes.digitTime,
        LightTernaryCodes.zeroTime,LightMaskErase.time,LightTernaryRank.time,
        LightBandLookup.searchTime with z ν ⟨hz,hmem⟩
      subst ν
      rcases hz with rfl
      have hn1' : LightTernaryCodes.digit (2*N) low high m≠1 := hn1
      simp [digit,code,hn1',LightTernaryCodes.oneCode,update_frame_setLocal]
  case tail =>
    rintro σ rfl
    unfold tailBody
    light_call hrankCall using digit,predRank,LightTernaryCodes.digitTime,
      LightTernaryCodes.zeroTime,LightMaskErase.time,LightTernaryRank.time,
      LightBandLookup.searchTime with rk ν ⟨hrk,hmem⟩
    subst ν
    rcases hrk with rfl
    light_if ha hna : active=0 using digit,predRank,
      LightTernaryCodes.digitTime,LightTernaryCodes.zeroTime,LightMaskErase.time,
      LightTernaryRank.time,LightBandLookup.searchTime
    · light_set bankVals using LightTernaryCodes.digitTime,LightTernaryCodes.zeroTime,
        LightMaskErase.time,LightTernaryRank.time,LightBandLookup.searchTime
      exact ⟨by simp [key,ha],rfl⟩
    · light_if hq hnq : digit N low high m=0 using digit,predRank,
        LightTernaryCodes.digitTime,LightTernaryCodes.zeroTime,LightMaskErase.time,
        LightTernaryRank.time,LightBandLookup.searchTime
      · light_set bankVals using LightTernaryCodes.digitTime,LightTernaryCodes.zeroTime,
          LightMaskErase.time,LightTernaryRank.time,LightBandLookup.searchTime
        exact ⟨by simp [key,hq],rfl⟩
      · light_if hb hnb' : predRank N low high m≤T using digit,predRank,
          LightTernaryCodes.digitTime,LightTernaryCodes.zeroTime,LightMaskErase.time,
          LightTernaryRank.time,LightBandLookup.searchTime
        · obtain ⟨hi,he⟩ := hbi hna hnq hb
          have hs := LightTernaryLookup.code_meets (d := d+1) hsearch μ
            (fun j => (bankCodes j : ℤ)) hw hbankSpace hspace (by omega)
            hbankRead hpowers (fun j k hj hk => Int.ofNat_lt.mpr (hbankSorted j k hj hk))
            hi hL hnb (by omega)
          have haddr : (bankVals : ℤ)+((bi+1 : ℕ) : ℤ)-1=((bankVals+bi : ℕ) : ℤ) := by omega
          have haddrWord : ((bankVals+bi : ℕ) : ℤ)≤lim.word := by
            have hh : bankVals+bi≤lim.space := by omega
            exact (Int.ofNat_le.mpr hh).trans hw
          light_call hs using he,digit,predRank,LightTernaryCodes.digitTime,
            LightTernaryCodes.zeroTime,LightMaskErase.time,LightTernaryRank.time,
            LightBandLookup.searchTime with ix ν ⟨hix,hmem⟩
          subst ν
          light_set (bankVals+bi : ℕ) using hix,haddr,LightTernaryCodes.digitTime,
            LightTernaryCodes.zeroTime,LightMaskErase.time,LightTernaryRank.time,
            LightBandLookup.searchTime
          exact ⟨by simp [key,hna,hnq,hb],rfl⟩
        · have hnt : T<predRank N low high m := by omega
          obtain ⟨hi,he⟩ := hni hna hnq hnt
          have hs := LightTernaryLookup.code_meets (d := d+1) hsearch μ
            (fun j => (nearCodes j : ℤ)) hw hnearSpace hspace (by omega)
            hnearRead hpowers (fun j k hj hk => Int.ofNat_lt.mpr (hnearSorted j k hj hk))
            hi hL hnn (by omega)
          have haddr : (nearVals : ℤ)+((ni+1 : ℕ) : ℤ)-1=((nearVals+ni : ℕ) : ℤ) := by omega
          have haddrWord : ((nearVals+ni : ℕ) : ℤ)≤lim.word := by
            have hh : nearVals+ni≤lim.space := by omega
            exact (Int.ofNat_le.mpr hh).trans hw
          light_call hs using he,digit,predRank,LightTernaryCodes.digitTime,
            LightTernaryCodes.zeroTime,LightMaskErase.time,LightTernaryRank.time,
            LightBandLookup.searchTime with ix ν ⟨hix,hmem⟩
          subst ν
          light_set (nearVals+ni : ℕ) using hix,haddr,LightTernaryCodes.digitTime,
            LightTernaryCodes.zeroTime,LightMaskErase.time,LightTernaryRank.time,
            LightBandLookup.searchTime
          exact ⟨by simp [key,hna,hnq,hnb'],rfl⟩

theorem time_bound (N L : ℕ) : time N L≤3000*(N+L+1)^2 := by
  unfold time LightTernaryRank.time LightTernaryCodes.digitTime
    LightTernaryCodes.zeroTime LightMaskErase.time LightBandLookup.searchTime
  nlinarith

end ThreeSum.LightTernaryPredecessor
