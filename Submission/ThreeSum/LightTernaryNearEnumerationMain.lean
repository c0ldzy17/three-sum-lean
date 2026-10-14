import Submission.ThreeSum.LightTernaryNearEnumeration
import Submission.ThreeSum.TernaryNearBankEnumeration

/-! Actual output-sensitive main recursion for the ternary deficit neighborhood. -/

namespace ThreeSum.LightTernaryNearEnumerationMain

open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration ThreeSum.LightTernaryNearEnumeration

set_option maxHeartbeats 3000000

variable {lim : Limits} {P : Program}

theorem meets {pMain pBranch W powers : ℕ}
    (hmain : P[pMain]?=some (body pBranch))
    (hbranch : P[pBranch]?=some (branchBody pMain))
    (hw : (lim.space : ℤ)≤lim.word)
    (hspace : powers+(2*W+1)≤lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ)≤lim.word) :
    ∀ qs : List ℕ, ∀ D pref dst caps : ℕ, ∀ μ : ℕ→ℤ,
      (∀ q∈qs, q<3) → qs.length≤W → D≤2*W → pref+4^qs.length≤4^W →
      dst+(words qs D).length≤powers → dst+(words qs D).length≤caps →
      caps+qs.length≤lim.space → Powers μ powers (2*W) →
      Seg μ caps (qs.map (fun q => (q : ℤ))) →
      ∀ d, d+2*qs.length≤lim.depth →
      Meets lim P pMain d [qs.length,D,pref,dst,powers,caps] μ (time qs D)
        (fun count μ' => count=((words qs D).length : ℤ) ∧
          Seg μ' dst (output qs D pref) ∧ SameOutside μ μ' dst (words qs D).length) := by
  have hpowWord : ((4^W : ℕ) : ℤ)≤lim.word :=
    (show ((4^W : ℕ) : ℤ)≤((4^(W+1) : ℕ) : ℤ) by
      exact_mod_cast Nat.pow_le_pow_right (by decide : 1≤4) (Nat.le_succ W)).trans hword
  intro qs
  induction qs with
  | nil =>
    intro D pref dst caps μ hqs hN hD hprefix hdstP hdstC hcspace hpowers hcaps d hd
    simp only [List.length_nil,pow_zero] at hprefix
    have hdspace : dst+1≤lim.space := by simpa [words] using hdstP.trans (by omega)
    have htime : 900≤900*visits [] D := by simp [visits]
    have hprefZ : (pref : ℤ)≤lim.word :=
      (show (pref : ℤ)≤((4^W : ℕ) : ℤ) by exact_mod_cast (show pref≤4^W by omega)).trans hpowWord
    apply Meets.of_body hmain
    unfold body time
    refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simpa using h))
    light_store dst (pref : ℕ) using visits
    light_set (1 : ℕ) using visits
    refine ⟨by simp [words],?_,?_⟩
    · simp [output,words,code,seg_cons]
    · intro a ha
      simp only [words,List.length_singleton] at ha
      change Function.update μ dst (pref : ℤ) a=_
      exact Function.update_of_ne (by omega) _ _
  | cons q qs ih =>
    intro D pref dst caps μ hqs hN hD hprefix hdstP hdstC hcspace hpowers hcaps d hd
    have hq : q<3 := hqs q (by simp)
    let qF : Fin 3 := ⟨q,hq⟩
    have hqF : qF.val=q := rfl
    have hlen : (q::qs).length=qs.length+1 := rfl
    have htail : ∀ r∈qs, r<3 := fun r hr => hqs r (by simp [hr])
    have hNW : qs.length≤W := by simpa using Nat.le_of_succ_le hN
    have htime : 900≤900*visits (q::qs) D := by simp [visits]
    have hv : visits (q::qs) D=1+branchVisits qs D q 0+
      branchVisits qs D q 1+branchVisits qs D q 2 := by
      simpa [hqF] using visits_cons qF qs D
    have hout : output (q::qs) D pref=branchOutput qs D pref q 0++
      branchOutput qs D pref q 1++branchOutput qs D pref q 2 := by
      simpa [hqF] using output_cons qF qs D pref
    have hcount : (words (q::qs) D).length=branchCount qs D q 0+
      branchCount qs D q 1+branchCount qs D q 2 := by
      have hh := congrArg List.length hout
      simpa [output_length,branchOutput_length,Nat.add_assoc] using hh
    have he : 4^(qs.length+1)=4^qs.length+4^qs.length+4^qs.length+4^qs.length := by
      rw [pow_succ]; omega
    have hp4 : (0 : ℤ)≤((4^qs.length : ℕ) : ℤ) := Int.natCast_nonneg _
    have hprefix' : pref+4^(qs.length+1)≤4^W := by simpa using hprefix
    have hprefZ : (pref : ℤ)≤lim.word :=
      (show (pref : ℤ)≤((4^W : ℕ) : ℤ) by exact_mod_cast (show pref≤4^W by omega)).trans hpowWord
    have hcapHead : μ caps=(q : ℤ) := by
      have hh := hcaps 0 (by simp)
      simpa using hh
    have hcapTail : Seg μ (caps+1) (qs.map (fun q => (q : ℤ))) := by
      have hh : μ caps=(q : ℤ) ∧ Seg μ (caps+1) (qs.map (fun q => (q : ℤ))) := by
        simpa [seg_cons] using hcaps
      exact hh.2
    have hdst0P : dst+branchCount qs D q 0≤powers := by omega
    have hdst0C : dst+branchCount qs D q 0≤caps := by omega
    have hprefix0 : pref+digitCode (0 : Fin 3).val*4^qs.length+4^qs.length≤4^W := by
      norm_num [digitCode]; omega
    have hchild0 : Allowed q 0 D →
      Meets lim P pMain (d+2)
        [qs.length,D-(q-0),pref+digitCode (0 : Fin 3).val*4^qs.length,dst,powers,caps+1] μ
        (time qs (D-(q-0)))
        (fun count μ' => count=((words qs (D-(q-0))).length : ℤ) ∧
          Seg μ' dst (output qs (D-(q-0)) (pref+digitCode (0 : Fin 3).val*4^qs.length)) ∧
          SameOutside μ μ' dst (words qs (D-(q-0))).length) := by
      intro ha
      have hbudget : ((D-(q-0) : ℕ) : ℤ)=(D : ℤ)-((q : ℤ)-0) := by
        unfold Allowed at ha
        omega
      have hc : branchCount qs D q 0=(words qs (D-(q-0))).length := by simp [branchCount,ha]
      have child := ih (D-(q-0)) (pref+digitCode (0 : Fin 3).val*4^qs.length) dst (caps+1) μ htail hNW (by omega) hprefix0
        (by simpa [hc] using hdst0P) (by rw [← hc]; omega) (by simp at hcspace ⊢; omega)
        hpowers hcapTail (d+2) (by simp at hd ⊢; omega)
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,hbudget] using child
    have hb0 := branch_meets (W := W) (N := qs.length) (D := D) (pref := pref)
      (dst := dst) (powers := powers) (caps := caps+1) (d := d+1) hbranch qs qF (0 : Fin 3) μ hw hspace hword
      hpowers hNW rfl hD (by omega) (by simp at hcspace; omega) hprefix0
      (by simpa [hqF] using hchild0) (by simp at hd; omega)
    norm_num [hqF] at hb0
    apply Meets.of_body hmain
    unfold body time
    refine Ends.iteLast (fun h => False.elim (by simp at h <;> omega)) (fun _ => ?_)
    light_set (qs.length : ℕ) using visits
    light_set (q : ℕ) using hcapHead,visits
    light_call hb0 using time,branchTime,hv,hqF,hcapHead
      with n0 μ1 ⟨hn0,hseg0,hsame0⟩
    have hpowers1 : Powers μ1 powers (2*W) := by
      intro i hi
      rw [hsame0 (powers+i) (Or.inr (by omega))]
      exact hpowers i hi
    have hcapTail1 : Seg μ1 (caps+1) (qs.map (fun q => (q : ℤ))) :=
      hcapTail.of_sameOutside hsame0 (Or.inr (by omega))
    have hdst1P : dst+branchCount qs D q 0+branchCount qs D q 1≤powers := by omega
    have hdst1C : dst+branchCount qs D q 0+branchCount qs D q 1≤caps := by omega
    have hprefix1 : pref+digitCode (1 : Fin 3).val*4^qs.length+4^qs.length≤4^W := by
      norm_num [digitCode]; omega
    have hchild1 : Allowed q 1 D →
      Meets lim P pMain (d+2)
        [qs.length,D-(q-1),pref+digitCode (1 : Fin 3).val*4^qs.length,
          dst+branchCount qs D q 0,powers,caps+1] μ1
        (time qs (D-(q-1)))
        (fun count μ' => count=((words qs (D-(q-1))).length : ℤ) ∧
          Seg μ' (dst+branchCount qs D q 0)
            (output qs (D-(q-1)) (pref+digitCode (1 : Fin 3).val*4^qs.length)) ∧
          SameOutside μ1 μ' (dst+branchCount qs D q 0) (words qs (D-(q-1))).length) := by
      intro ha
      have hbudget : ((D-(q-1) : ℕ) : ℤ)=(D : ℤ)-((q : ℤ)-1) := by
        unfold Allowed at ha
        omega
      have hc : branchCount qs D q 1=(words qs (D-(q-1))).length := by simp [branchCount,ha]
      have child := ih (D-(q-1)) (pref+digitCode (1 : Fin 3).val*4^qs.length)
        (dst+branchCount qs D q 0) (caps+1) μ1 htail hNW (by omega) hprefix1
        (by simpa [hc] using hdst1P) (by rw [← hc]; omega) (by simp at hcspace ⊢; omega)
        hpowers1 hcapTail1 (d+2) (by simp at hd ⊢; omega)
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,hbudget] using child
    have hb1 := branch_meets (W := W) (N := qs.length) (D := D) (pref := pref)
      (dst := dst+branchCount qs D q 0) (powers := powers) (caps := caps+1) (d := d+1)
      hbranch qs qF (1 : Fin 3) μ1 hw hspace hword
      hpowers1 hNW rfl hD (by omega) (by simp at hcspace; omega) hprefix1
      (by simpa [hqF] using hchild1) (by simp at hd; omega)
    norm_num [hqF] at hb1
    light_call hb1 using time,branchTime,hv,hqF,hn0
      with n1 μ2 ⟨hn1,hseg1,hsame1⟩
    have hpowers2 : Powers μ2 powers (2*W) := by
      intro i hi
      rw [hsame1 (powers+i) (Or.inr (by omega))]
      exact hpowers1 i hi
    have hcapTail2 : Seg μ2 (caps+1) (qs.map (fun q => (q : ℤ))) :=
      hcapTail1.of_sameOutside hsame1 (Or.inr (by omega))
    have hdst2P : dst+branchCount qs D q 0+branchCount qs D q 1+
      branchCount qs D q 2≤powers := by omega
    have hdst2C : dst+branchCount qs D q 0+branchCount qs D q 1+
      branchCount qs D q 2≤caps := by omega
    have hprefix2 : pref+digitCode (2 : Fin 3).val*4^qs.length+4^qs.length≤4^W := by
      norm_num [digitCode]; omega
    have hchild2 : Allowed q 2 D →
      Meets lim P pMain (d+2)
        [qs.length,D-(q-2),pref+digitCode (2 : Fin 3).val*4^qs.length,
          dst+branchCount qs D q 0+branchCount qs D q 1,powers,caps+1] μ2
        (time qs (D-(q-2)))
        (fun count μ' => count=((words qs (D-(q-2))).length : ℤ) ∧
          Seg μ' (dst+branchCount qs D q 0+branchCount qs D q 1)
            (output qs (D-(q-2)) (pref+digitCode (2 : Fin 3).val*4^qs.length)) ∧
          SameOutside μ2 μ' (dst+branchCount qs D q 0+branchCount qs D q 1)
            (words qs (D-(q-2))).length) := by
      intro ha
      have hbudget : ((D-(q-2) : ℕ) : ℤ)=(D : ℤ)-((q : ℤ)-2) := by
        unfold Allowed at ha
        omega
      have hc : branchCount qs D q 2=(words qs (D-(q-2))).length := by simp [branchCount,ha]
      have child := ih (D-(q-2)) (pref+digitCode (2 : Fin 3).val*4^qs.length)
        (dst+branchCount qs D q 0+branchCount qs D q 1) (caps+1) μ2 htail hNW (by omega) hprefix2
        (by simpa [hc] using hdst2P) (by rw [← hc]; omega) (by simp at hcspace ⊢; omega)
        hpowers2 hcapTail2 (d+2) (by simp at hd ⊢; omega)
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,hbudget] using child
    have hb2 := branch_meets (W := W) (N := qs.length) (D := D) (pref := pref)
      (dst := dst+branchCount qs D q 0+branchCount qs D q 1) (powers := powers) (caps := caps+1) (d := d+1)
      hbranch qs qF (2 : Fin 3) μ2 hw hspace hword
      hpowers2 hNW rfl hD (by omega) (by simp at hcspace; omega) hprefix2
      (by simpa [hqF] using hchild2) (by simp at hd; omega)
    norm_num [hqF] at hb2
    light_call hb2 using time,branchTime,hv,hqF,hn0,hn1
      with n2 μ3 ⟨hn2,hseg2,hsame2⟩
    have htotal : ((branchCount qs D q 0+branchCount qs D q 1+
        branchCount qs D q 2 : ℕ) : ℤ)≤lim.word :=
      (show ((branchCount qs D q 0+branchCount qs D q 1+
        branchCount qs D q 2 : ℕ) : ℤ)≤(lim.space : ℤ) by
        exact_mod_cast (show branchCount qs D q 0+branchCount qs D q 1+
        branchCount qs D q 2≤lim.space by omega)).trans hw
    have hseg0' : Seg μ2 dst (branchOutput qs D pref q 0) :=
      hseg0.of_sameOutside hsame1 (Or.inl (by simp))
    have hseg01 : Seg μ2 dst
        (branchOutput qs D pref q 0++branchOutput qs D pref q 1) := by
      rw [seg_append,branchOutput_length]
      exact ⟨hseg0',hseg1⟩
    have hseg01' : Seg μ3 dst
        (branchOutput qs D pref q 0++branchOutput qs D pref q 1) :=
      hseg01.of_sameOutside hsame2 (Or.inl (by simp [Nat.add_assoc]))
    have hsame01 : SameOutside μ μ2 dst (branchCount qs D q 0+branchCount qs D q 1) :=
      hsame0.then hsame1 (fun a ha => by constructor <;> omega)
    light_set (branchCount qs D q 0+branchCount qs D q 1+branchCount qs D q 2 : ℕ)
      using time,branchTime,hv,hn0,hn1,hn2
    refine ⟨by simp [hcount],?_,?_⟩
    · rw [hout,seg_append,List.length_append,branchOutput_length,branchOutput_length]
      exact ⟨hseg01',by simpa [Nat.add_assoc] using hseg2⟩
    · rw [hcount]
      exact hsame01.then hsame2 (fun a ha => by constructor <;> omega)

theorem program_meets {W powers D pref dst caps d : ℕ} {qs : List ℕ} {μ : ℕ→ℤ}
    (hw : (lim.space : ℤ)≤lim.word)
    (hspace : powers+(2*W+1)≤lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ)≤lim.word)
    (hqs : ∀ q∈qs, q<3) (hN : qs.length≤W) (hD : D≤2*W)
    (hprefix : pref+4^qs.length≤4^W)
    (hdstP : dst+(words qs D).length≤powers)
    (hdstC : dst+(words qs D).length≤caps) (hcspace : caps+qs.length≤lim.space)
    (hpowers : Powers μ powers (2*W)) (hcaps : Seg μ caps (qs.map (fun q => (q : ℤ))))
    (hd : d+2*qs.length≤lim.depth) :
    Meets lim LightTernaryNearEnumeration.program 0 d
      [qs.length,D,pref,dst,powers,caps] μ (time qs D)
      (fun count μ' => count=((words qs D).length : ℤ) ∧
        Seg μ' dst (output qs D pref) ∧ SameOutside μ μ' dst (words qs D).length) :=
  meets rfl rfl hw hspace hword qs D pref dst caps μ
    hqs hN hD hprefix hdstP hdstC hcspace hpowers hcaps d hd

theorem time_bank_bound {N : ℕ} (Q : ThreeSum.TernaryJointType.TritWord N) (D : ℕ) :
    time (ThreeSum.TernaryBankEnumeration.wordList Q) D ≤
      900*((N+1)*(ThreeSum.TernaryBank.nearWords Q D).card) :=
  Nat.mul_le_mul_left 900 (ThreeSum.TernaryNearBankEnumeration.visits_le_nearWords Q D)

/-- The actual recursive machine time is paid by the same finite Gibbs query bound. -/
theorem time_gibbs_counts {N : ℕ} (Q : ThreeSum.TernaryJointType.TritWord N)
    (D : ℕ) (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    (time (ThreeSum.TernaryBankEnumeration.wordList Q) D : ℝ)*z^D ≤
      900*(N+1)*(1+z)^ThreeSum.TernaryJointType.digitCount Q 1 *
        (1+z+z^2)^ThreeSum.TernaryJointType.digitCount Q 2 := by
  have htime : (time (ThreeSum.TernaryBankEnumeration.wordList Q) D : ℝ) ≤
      900*(N+1)*(ThreeSum.TernaryBank.nearWords Q D).card := by
    exact_mod_cast (show time (ThreeSum.TernaryBankEnumeration.wordList Q) D ≤
      900*(N+1)*(ThreeSum.TernaryBank.nearWords Q D).card by
        simpa [Nat.mul_assoc] using time_bank_bound Q D)
  have hg := ThreeSum.TernaryBank.nearWords_card_gibbs_counts Q D z hz hz1
  calc
    (time (ThreeSum.TernaryBankEnumeration.wordList Q) D : ℝ)*z^D ≤
        (900*(N+1)*(ThreeSum.TernaryBank.nearWords Q D).card)*z^D :=
      mul_le_mul_of_nonneg_right htime (pow_nonneg hz D)
    _ = (900*(N+1))*((ThreeSum.TernaryBank.nearWords Q D).card*z^D) := by ring
    _ ≤ (900*(N+1))*((1+z)^ThreeSum.TernaryJointType.digitCount Q 1 *
        (1+z+z^2)^ThreeSum.TernaryJointType.digitCount Q 2) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = 900*(N+1)*(1+z)^ThreeSum.TernaryJointType.digitCount Q 1 *
        (1+z+z^2)^ThreeSum.TernaryJointType.digitCount Q 2 := by ring

end ThreeSum.LightTernaryNearEnumerationMain
