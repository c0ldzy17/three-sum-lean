import Submission.ThreeSum.LightTernaryFrozenQueryMain
import Submission.ThreeSum.TernaryConvolution

/-! Frozen-query correctness from actual compact code/value arrays. -/
namespace ThreeSum.LightTernaryFrozenQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 5000000

variable {lim : Limits} {P : Program}

theorem rank_le_twice {N : ℕ} (R : TritWord N) : rank R≤2*N := by
  calc
    rank R≤∑ i : Fin N, 2 := Finset.sum_le_sum (fun i _ => by have := (R i).isLt; omega)
    _=2*N := by simp; omega

/-- Every leaf is instantiated by the checked physical binary search and load.
There is no supplied value-evaluation oracle in this statement. -/
theorem meets {N pMain pLookup pSearch pDigit pZero pErase : ℕ}
    (hmain : P[pMain]?=some (body pMain pLookup pDigit pZero pErase))
    (hlookup : P[pLookup]?=some (LightTernaryQueryLookup.body pSearch))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (T bankCodes bankCount bankValues nearCodes nearCount nearValues powers L U : ℕ)
    (bankWords nearWords : ℕ→TritWord N) (H : TritWord N→ℤ) (Q : TritWord N) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (hbankCodesSpace : bankCodes+bankCount≤lim.space)
    (hbankValuesSpace : bankValues+(N+1)*bankCount≤lim.space)
    (hnearCodesSpace : nearCodes+nearCount≤lim.space)
    (hnearValuesSpace : nearValues+nearCount≤lim.space)
    (hspace : powers+(2*N+1)≤lim.space)
    (hword : ((bankCount+nearCount+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcutWord : (T : ℤ)+1≤lim.word)
    (hvalueWord : 4*((4^N : ℕ) : ℤ)*(U : ℤ)+3≤lim.word)
    (hpowers : Powers μ powers (2*N)) (hL : L≤2*N)
    (hbankSmall : bankCount<2^L) (hnearSmall : nearCount<2^L)
    (hH : ∀ R, |H R|≤(U : ℤ))
    (hbankRead : ∀ j<bankCount, μ (bankCodes+j)=(address (bankWords j) : ℤ))
    (hbankSorted : ∀ i j, i<j → j<bankCount → address (bankWords i)<address (bankWords j))
    (hbankPresent : ∀ R : TritWord N, rank R≤T → ∃ j<bankCount, bankWords j=R)
    (hbankValues : ∀ K≤N, ∀ j<bankCount, μ (bankValues+K*bankCount+j)=stageValue K H (bankWords j))
    (hnearRead : ∀ j<nearCount, μ (nearCodes+j)=(address (nearWords j) : ℤ))
    (hnearSorted : ∀ i j, i<j → j<nearCount → address (nearWords i)<address (nearWords j))
    (hnearPresent : ∀ R : TritWord N, Below R Q → T<rank R → ∃ j<nearCount, nearWords j=R)
    (hnearValues : ∀ j<nearCount, μ (nearValues+j)=H (nearWords j)) :
    ∀ K≤N, ∀ R : TritWord N, Below R Q → ∀ d, d+K+2*N+L+3≤lim.depth →
      Meets lim P pMain d
        (inputs N K (rank R) T (address R) bankCodes bankCount bankValues
          nearCodes nearCount nearValues powers L) μ (queryTime L T K R)
        (fun v μ' => v=stageValue K H R ∧ μ'=μ) := by
  have hcast {a b : ℕ} (h : a≤b) : (a : ℤ)≤(b : ℤ) := by exact_mod_cast h
  have hwordPow : ((2^(2*N+1) : ℕ) : ℤ)≤lim.word :=
    (hcast (show 2^(2*N+1)≤bankCount+nearCount+2^(2*N+1)+16 by omega)).trans hword
  have hwordBank : ((bankCount+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word := by
    have hle : bankCount+2^(2*N+1)+16≤bankCount+nearCount+2^(2*N+1)+16 := by omega
    exact (hcast hle).trans hword
  have hwordNear : ((nearCount+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word := by
    have hle : nearCount+2^(2*N+1)+16≤bankCount+nearCount+2^(2*N+1)+16 := by omega
    exact (hcast hle).trans hword
  have hBnonneg : 0≤((4^N : ℕ) : ℤ)*(U : ℤ) := by positivity
  have hBword : ((4^N : ℕ) : ℤ)*(U : ℤ)≤lim.word := by nlinarith
  have hUword : ((4^N*U : ℕ) : ℤ)≤lim.word := by simpa [Nat.cast_mul] using hBword
  have hbound (K : ℕ) (hKN : K≤N) (R : TritWord N) :
      |stageValue K H R|≤((4^N*U : ℕ) : ℤ) := by
    have hs := stageValue_abs K hKN H U hH R
    have hp : ((4^K : ℕ) : ℤ)≤((4^N : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_le_pow_right (by decide : 1≤4) hKN
    simpa [Nat.cast_mul] using hs.trans (mul_le_mul_of_nonneg_right hp (by positivity))
  have hHbound (R : TritWord N) : |H R|≤((4^N*U : ℕ) : ℤ) := by
    simpa using hbound 0 (by omega) R
  have hargs : ∀ K≤N, ∀ R : TritWord N,
      ∀ x∈inputs N K (rank R) T (address R) bankCodes bankCount bankValues
        nearCodes nearCount nearValues powers L, |x|≤lim.word := by
    intro K hKN R x hx
    have hrank := rank_le_twice R
    have haddress := address_lt_pow_two R
    have haddressWord : (address R : ℤ)≤lim.word := by
      have hpow : 2^(2*N)≤2^(2*N+1) := Nat.pow_le_pow_right (by decide) (by omega)
      have hle : address R≤2^(2*N+1) := (Nat.le_of_lt haddress).trans hpow
      exact (hcast hle).trans hwordPow
    have hbc : (bankCodes : ℤ)≤lim.word := (hcast (show bankCodes≤lim.space by omega)).trans hw
    have hbn : (bankCount : ℤ)≤lim.word := (hcast (show bankCount≤lim.space by omega)).trans hw
    have hbv : (bankValues : ℤ)≤lim.word := (hcast (show bankValues≤lim.space by omega)).trans hw
    have hnc : (nearCodes : ℤ)≤lim.word := (hcast (show nearCodes≤lim.space by omega)).trans hw
    have hnn : (nearCount : ℤ)≤lim.word := (hcast (show nearCount≤lim.space by omega)).trans hw
    have hnv : (nearValues : ℤ)≤lim.word := (hcast (show nearValues≤lim.space by omega)).trans hw
    have hp : (powers : ℤ)≤lim.word := (hcast (show powers≤lim.space by omega)).trans hw
    simp only [inputs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals rw [abs_of_nonneg (by positivity)]; omega
  have hbankLeaf : ∀ K≤N, ∀ R : TritWord N, Below R Q → rank R≤T →
      ∀ d, d+L+1≤lim.depth →
      Meets lim P pLookup d [bankCodes,bankCount,address R,bankValues,powers,L,K] μ
        (LightTernaryQueryLookup.time L) (fun v μ' => v=stageValue K H R ∧ μ'=μ) := by
    intro K hKN R _ hr d hd
    obtain ⟨j,hj,heq⟩ := hbankPresent R hr
    have hvaluesSpace : bankValues+(K+1)*bankCount≤lim.space :=
      (Nat.add_le_add_left (Nat.mul_le_mul_right bankCount (by omega)) bankValues).trans hbankValuesSpace
    have hv : μ (bankValues+K*bankCount+j)=stageValue K H R := by rw [hbankValues K hKN j hj,heq]
    have hs : ∀ i j, i<j → j<bankCount →
        (address (bankWords i) : ℤ)<(address (bankWords j) : ℤ) := by
      intro i j hij hj
      exact_mod_cast hbankSorted i j hij hj
    have hc := LightTernaryQueryLookup.meets hlookup hsearch μ (fun j => (address (bankWords j) : ℤ))
      (stageValue K H R) hw hbankCodesSpace hvaluesSpace hspace hwordBank hbankRead hpowers hs hj
      hv (hbound K hKN R) hUword hL hbankSmall hd
    simpa only [heq,Nat.cast_zero] using hc
  have hnearLeaf : ∀ R : TritWord N, Below R Q → T<rank R →
      ∀ d, d+L+1≤lim.depth →
      Meets lim P pLookup d [nearCodes,nearCount,address R,nearValues,powers,L,0] μ
        (LightTernaryQueryLookup.time L) (fun v μ' => v=H R ∧ μ'=μ) := by
    intro R hRQ hr d hd
    obtain ⟨j,hj,heq⟩ := hnearPresent R hRQ hr
    have hv : μ (nearValues+0*nearCount+j)=H R := by simp [hnearValues j hj,heq]
    have hs : ∀ i j, i<j → j<nearCount →
        (address (nearWords i) : ℤ)<(address (nearWords j) : ℤ) := by
      intro i j hij hj
      exact_mod_cast hnearSorted i j hij hj
    have hc := LightTernaryQueryLookup.meets (stage := 0) hlookup hsearch μ
      (fun j => (address (nearWords j) : ℤ)) (H R) hw hnearCodesSpace
      (by simpa using hnearValuesSpace) hspace hwordNear hnearRead hpowers hs hj hv
      (hHbound R) hUword hL hnearSmall hd
    simpa only [heq,Nat.cast_zero] using hc
  exact meets_core hmain hdigit hzero herase T bankCodes bankCount bankValues nearCodes nearCount nearValues
    powers L U H Q μ hw hspace hwordPow hNword hcutWord hvalueWord hpowers hH hargs hbankLeaf hnearLeaf

/-- Full-stage query output is the original additive convolution, scaled by the
positive factorial of the physical target word. -/
theorem stageValue_count {N a b : ℕ} (f g : TritWord N→ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b) :
    stageValue N (fun R => ThreeSum.TernaryEuler.binomialZeta
      (fun A => ThreeSum.TernaryConvolution.factorial A*f A) R *
      ThreeSum.TernaryEuler.binomialZeta (fun B => ThreeSum.TernaryConvolution.factorial B*g B) R) Q =
      ThreeSum.TernaryConvolution.factorial Q*ThreeSum.TernaryConvolution.convolution f g Q := by
  have hall : (coords N N).toFinset=Finset.univ := by
    have ht : (List.finRange N).take N=List.finRange N := List.take_of_length_le (by simp)
    simp [coords,ht]
  rw [stageValue,ThreeSum.TernaryConvolution.frozenInverse_eq_binomialInverse
    (coords N N) (coords_nodup N N) hall]
  exact ThreeSum.TernaryConvolution.factorial_convolution f g hf hg Q hQ

/-- The physical result can be consumed as an exact zero/nonzero decision for
original source pairs; factorial scaling is always strictly positive. -/
theorem count_zero_iff {N a b : ℕ} (f g : TritWord N→ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b) :
    stageValue N (fun R => ThreeSum.TernaryEuler.binomialZeta
      (fun A => ThreeSum.TernaryConvolution.factorial A*f A) R *
      ThreeSum.TernaryEuler.binomialZeta (fun B => ThreeSum.TernaryConvolution.factorial B*g B) R) Q=0 ↔
      ThreeSum.TernaryConvolution.convolution f g Q=0 := by
  rw [stageValue_count f g hf hg Q hQ]
  simp [ThreeSum.TernaryConvolution.factorial_ne_zero Q]

/-- Rewrite an actual full query execution contract to the exact source-count
contract, retaining the same program, time bound and preserved memory. -/
theorem count_spec {N a b pMain d time : ℕ} (args : List ℤ) (μ : ℕ→ℤ)
    (f g : TritWord N→ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b)
    (hquery : Meets lim P pMain d args μ time (fun v μ' =>
      v=stageValue N (fun R => ThreeSum.TernaryEuler.binomialZeta
        (fun A => ThreeSum.TernaryConvolution.factorial A*f A) R *
        ThreeSum.TernaryEuler.binomialZeta (fun B => ThreeSum.TernaryConvolution.factorial B*g B) R) Q ∧ μ'=μ)) :
    Meets lim P pMain d args μ time (fun v μ' =>
      v=ThreeSum.TernaryConvolution.factorial Q*ThreeSum.TernaryConvolution.convolution f g Q ∧ μ'=μ) := by
  exact hquery.mono le_rfl (fun v μ' hv =>
    ⟨hv.1.trans (stageValue_count f g hf hg Q hQ),hv.2⟩)

/-- Standalone six-procedure query implementation; all preconditions and
conclusions are exactly those of the physical array theorem above. -/
def program_meets {N : ℕ} :=
  meets (N := N) (lim := lim) (P := program) program_main program_lookup program_search
    program_digit program_zero program_erase

/-- For an outside-bank target, the actual memo enumerator has exactly the
lower words that remain outside the bank. -/
theorem outside_near_iff {N : ℕ} (Q R : TritWord N) (T : ℕ) (hQ : T<rank Q) :
    R∈ThreeSum.TernaryBank.nearWords Q (rank Q-(T+1)) ↔ Below R Q ∧ T<rank R := by
  rw [mem_nearWords]
  constructor
  · intro ⟨hbelow,hdef⟩
    have hsum := rank_add_deficit hbelow
    exact ⟨hbelow,by omega⟩
  · intro ⟨hbelow,hrank⟩
    have hsum := rank_add_deficit hbelow
    exact ⟨hbelow,by omega⟩

end ThreeSum.LightTernaryFrozenQuery
