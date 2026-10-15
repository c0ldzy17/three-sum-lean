import Submission.ThreeSum.LightSubsetEnumeration
import Submission.ThreeSum.TernaryAddresses

/-! Output-sensitive enumeration of canonical ternary bank addresses in Light. -/

namespace ThreeSum.LightTernaryEnumeration

open Light ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def output (N T pref : ℕ) : List ℤ :=
  (codes N T).map (fun a => ((pref+a : ℕ) : ℤ))

@[simp] theorem output_length (N T pref : ℕ) :
    (output N T pref).length = (codes N T).length := by simp [output]

@[simp] theorem output_zero (T pref : ℕ) : output 0 T pref = [pref] := by
  simp [output,codes]

theorem digits_zero : digits 0 = [0] := by norm_num [digits,List.range_succ]
theorem digits_one : digits 1 = [0,1] := by norm_num [digits,List.range_succ]
theorem digits_full {T : ℕ} (hT : 2 ≤ T) : digits T = [0,1,2] := by
  simp [digits,List.range_succ,show 0 ≤ T by omega,show 1 ≤ T by omega,hT]

theorem output_succ_zero (N pref : ℕ) :
    output (N+1) 0 pref = output N 0 pref := by
  simp [output,codes,digits_zero,digitCode]

theorem output_succ_one (N pref : ℕ) :
    output (N+1) 1 pref = output N 1 pref ++ output N 0 (pref+4^N) := by
  simp [output,codes,digits_one,digitCode,List.map_append,List.map_map,
    Function.comp_def,Nat.add_assoc]

theorem output_succ_full {T : ℕ} (hT : 2 ≤ T) (N pref : ℕ) :
    output (N+1) T pref = output N T pref ++
      output N (T-1) (pref+4^N) ++ output N (T-2) (pref+3*4^N) := by
  simp [output,codes,digits_full hT,digitCode,List.map_append,List.map_map,
    Function.comp_def,Nat.add_assoc,List.append_assoc]

theorem visits_zero_succ (N : ℕ) : visits (N+1) 0 = 1+visits N 0 := by
  simp [visits,digits_zero]
theorem visits_one_succ (N : ℕ) :
    visits (N+1) 1 = 1+visits N 1+visits N 0 := by
  simp [visits,digits_one,Nat.add_assoc]
theorem visits_full_succ {T : ℕ} (hT : 2 ≤ T) (N : ℕ) :
    visits (N+1) T = 1+visits N T+visits N (T-1)+visits N (T-2) := by
  simp [visits,digits_full hT,Nat.add_assoc]

theorem visits_pos (N T : ℕ) : 1 ≤ visits N T := by
  cases N <;> simp [visits]

theorem visits_child0 (N T : ℕ) : 1+visits N T ≤ visits (N+1) T := by
  cases T with
  | zero => simp [visits,digits_zero]
  | succ T =>
    cases T with
    | zero => simp [visits,digits_one] <;> omega
    | succ T => simp [visits,digits_full (by omega : 2 ≤ T+2)] <;> omega

theorem visits_child01 {T : ℕ} (hT : 1 ≤ T) (N : ℕ) :
    1+visits N T+visits N (T-1) ≤ visits (N+1) T := by
  cases T with
  | zero => omega
  | succ T =>
    cases T with
    | zero => simp [visits,digits_one,Nat.add_assoc]
    | succ T => simp [visits,digits_full (by omega : 2 ≤ T+2),Nat.add_assoc] <;> omega

theorem pow_two_even (N : ℕ) : 2^(2*N) = 4^N := by
  rw [pow_mul]
  norm_num

/-- Arguments: remaining trits, rank cutoff, prefix, output base, powers-of-two base. -/
def body (pSelf : ℕ) : Stmt :=
  .ite (v 0 <' k 1)
    (.store (v 3) (v 2) ;; .set 0 (k 1))
    (.set 5 (v 0 -' k 1) ;;
      .call pSelf [v 5,v 1,v 2,v 3,v 4] 6 ;;
      .ite (v 1 <' k 1)
        (.set 0 (v 6))
        (.call pSelf [v 5,v 1 -' k 1,
          v 2 +' M (v 4 +' k 2 *' v 5),v 3 +' v 6,v 4] 7 ;;
          .ite (v 1 <' k 2)
            (.set 0 (v 6 +' v 7))
            (.call pSelf [v 5,v 1 -' k 2,
              v 2 +' k 3 *' M (v 4 +' k 2 *' v 5),v 3 +' v 6 +' v 7,v 4] 8 ;;
              .set 0 (v 6 +' v 7 +' v 8))))

def time (N T : ℕ) : ℕ := 300*visits N T

theorem time_bound (N T : ℕ) :
    time N T ≤ 300*((N+1)*(codes N T).length) := by
  exact Nat.mul_le_mul_left 300 (visits_le_codes N T)

theorem meets {pEnum W powers : ℕ}
    (hprog : P[pEnum]? = some (body pEnum))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*W+1) ≤ lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ) ≤ lim.word) :
    ∀ N T pref dst : ℕ, ∀ μ : ℕ → ℤ,
      N ≤ W → T ≤ 2*W → pref+4^N ≤ 4^W →
      dst+(codes N T).length ≤ powers → Powers μ powers (2*W) →
      ∀ d, d+N ≤ lim.depth →
      Meets lim P pEnum d [N,T,pref,dst,powers] μ (time N T)
        (fun r μ' => r = ((codes N T).length : ℤ) ∧
          Seg μ' dst (output N T pref) ∧
          SameOutside μ μ' dst (codes N T).length) := by
  have hpowWord : ((4^W : ℕ) : ℤ) ≤ lim.word := by
    have hn : (4^W : ℕ) ≤ 4^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (show ((4^W : ℕ) : ℤ) ≤ ((4^(W+1) : ℕ) : ℤ) by exact_mod_cast hn).trans hword
  intro N
  induction N with
  | zero =>
    intro T pref dst μ hN hT hprefix hdst hpowers d hd
    have htime : 300 ≤ 300*visits 0 T := by simp [visits]
    have hdspace : dst+1 ≤ lim.space := by simpa [codes] using hdst.trans (by omega)
    have hprefZ : (pref : ℤ) ≤ lim.word := by
      exact (show (pref : ℤ) ≤ ((4^W : ℕ) : ℤ) by exact_mod_cast (show pref ≤ 4^W by omega)).trans hpowWord
    apply Meets.of_body hprog
    unfold body time
    refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simpa using h))
    light_store dst (pref : ℕ) using visits
    light_set (1 : ℕ) using visits
    refine ⟨by simp [codes],?_,?_⟩
    · simp [output_zero,seg_cons]
    · intro a ha
      simp only [codes,List.length_singleton] at ha
      change Function.update μ dst (pref : ℤ) a = _
      exact Function.update_of_ne (by omega) _ _
  | succ N ih =>
    intro T pref dst μ hN hT hprefix hdst hpowers d hd
    have hNW : N ≤ W := by omega
    have hp4Z : (0 : ℤ) ≤ ((4^N : ℕ) : ℤ) := Int.natCast_nonneg _
    have hp4Int : (0 : ℤ) ≤ (4 : ℤ)^N := by positivity
    have he : 4^(N+1)=4^N+4^N+4^N+4^N := by rw [pow_succ]; omega
    have hprefZ : (pref : ℤ) ≤ lim.word := by
      exact (show (pref : ℤ) ≤ ((4^W : ℕ) : ℤ) by exact_mod_cast (show pref ≤ 4^W by omega)).trans hpowWord
    have hn0le : (codes N T).length ≤ (codes (N+1) T).length := by
      cases T with
      | zero => simp [codes,digits_zero,digitCode]
      | succ T =>
        cases T with
        | zero => simp [codes,digits_one,digitCode]
        | succ T => simp [codes,digits_full (by omega : 2 ≤ T+2),digitCode]
    have hdst0 : dst+(codes N T).length ≤ powers := by omega
    have hdst0Words : dst+(words N T).length ≤ powers := by simpa using hdst0
    have hprefix0 : pref+4^N ≤ 4^W := by omega
    have hchild0 := ih T pref dst μ hNW hT hprefix0 hdst0 hpowers (d+1) (by omega)
    have htime : 300 ≤ 300*visits (N+1) T := Nat.mul_le_mul_left 300 (visits_pos _ _)
    have hv0 := visits_child0 N T
    apply Meets.of_body hprog
    unfold body time
    refine Ends.iteLast (fun h => False.elim (by simp at h <;> omega)) (fun _ => ?_)
    light_set (N : ℕ) using visits
    light_call hchild0 using time,hv0 with n0 μ1 ⟨hn0,hseg0,hsame0⟩
    have hpowers1 : Powers μ1 powers (2*W) := by
      intro i hi
      rw [hsame0 (powers+i) (Or.inr (by omega))]
      exact hpowers i hi
    light_if hzeroZ hposZ : (T : ℤ) < 1 using time,hv0
    · have hzero : T=0 := by omega
      subst T
      light_set ((codes N 0).length : ℕ) using time,hn0,visits_zero_succ
      refine ⟨by simpa [codes,digits_zero,digitCode] using hn0,?_,?_⟩
      · simpa [output_succ_zero] using hseg0
      · simpa [codes,digits_zero,digitCode] using hsame0
    · have hpos : 1 ≤ T := by omega
      have hv01 := visits_child01 hpos N
      have hn01le : (codes N T).length+(codes N (T-1)).length ≤
          (codes (N+1) T).length := by
        cases T with
        | zero => omega
        | succ T =>
          cases T with
          | zero => simp [codes,digits_one,digitCode]
          | succ T => simp [codes,digits_full (by omega : 2 ≤ T+2),digitCode] <;> omega
      have hdst1 : dst+(codes N T).length+(codes N (T-1)).length ≤ powers := by omega
      have hdst1Words : dst+(words N T).length+(words N (T-1)).length ≤ powers := by
        simpa using hdst1
      have hprefix1 : pref+4^N+4^N ≤ 4^W := by omega
      have hpowerRead := hpowers1 (2*N) (by omega)
      rw [pow_two_even] at hpowerRead
      have haddrCast : (powers : ℤ)+2*(N : ℤ) = ((powers+2*N : ℕ) : ℤ) := by
        push_cast; rfl
      have hpowerReadZ : μ1 ((powers : ℤ)+2*(N : ℤ)).toNat = ((4^N : ℕ) : ℤ) := by
        rw [haddrCast,Int.toNat_natCast,hpowerRead]
      have hargPrefix1 : (pref : ℤ)+μ1 (powers+2*N) = ((pref+4^N : ℕ) : ℤ) := by
        rw [hpowerRead]; push_cast; rfl
      have hprefixArg1 : (pref : ℤ)+μ1 (powers+2*N) ≤ lim.word := by
        rw [hargPrefix1]
        exact (show ((pref+4^N : ℕ) : ℤ) ≤ ((4^W : ℕ) : ℤ) by exact_mod_cast (show pref+4^N ≤ 4^W by omega)).trans hpowWord
      have hprefixInt1 : (pref : ℤ)+(4 : ℤ)^N ≤ lim.word := by
        simpa [hpowerRead] using hprefixArg1
      have hreadNonneg : (0 : ℤ) ≤ μ1 (powers+2*N) := by rw [hpowerRead]; positivity
      have hreadWord : μ1 (powers+2*N) ≤ lim.word := by
        rw [hpowerRead]
        exact (show ((4^N : ℕ) : ℤ) ≤ ((4^W : ℕ) : ℤ) by exact_mod_cast (Nat.pow_le_pow_right (by decide : 1 ≤ 4) hNW)).trans hpowWord
      have hchild1 := ih (T-1) (pref+4^N) (dst+(codes N T).length) μ1
        hNW (by omega) hprefix1 hdst1 hpowers1 (d+1) (by omega)
      light_call hchild1 using time,hv01,hn0,hargPrefix1,hpowerRead,hpowerReadZ
        with n1 μ2 ⟨hn1,hseg1,hsame1⟩
      have hseg0' : Seg μ2 dst (output N T pref) :=
        hseg0.of_sameOutside hsame1 (Or.inl (by simp))
      have hsame01 : SameOutside μ μ2 dst
          ((codes N T).length+(codes N (T-1)).length) :=
        hsame0.then hsame1 (fun a ha => by constructor <;> omega)
      light_if honeZ htwoZ : (T : ℤ) < 2 using time,hv01
      · have hone : T=1 := by omega
        subst T
        simp only [Nat.sub_self] at *
        have htotalBound : (((codes N 1).length+(codes N 0).length : ℕ) : ℤ) ≤ lim.word := by
          exact (show (((codes N 1).length+(codes N 0).length : ℕ) : ℤ) ≤ (lim.space : ℤ) by exact_mod_cast (show (codes N 1).length+(codes N 0).length ≤ lim.space by omega)).trans hw
        have htotalWords : (((words N 1).length+(words N 0).length : ℕ) : ℤ) ≤ lim.word := by
          simpa using htotalBound
        light_set ((codes N 1).length+(codes N 0).length : ℕ)
          using time,hn0,hn1,visits_one_succ
        refine ⟨?_,?_,?_⟩
        · simp [codes,digits_one,digitCode]
        · rw [output_succ_one,seg_append,output_length]
          exact ⟨hseg0',by simpa using hseg1⟩
        · simpa [codes,digits_one,digitCode] using hsame01
      · have htwo : 2 ≤ T := by omega
        have hcount : (codes (N+1) T).length = (codes N T).length+
            (codes N (T-1)).length+(codes N (T-2)).length := by
          simp [codes,digits_full htwo,digitCode,Nat.add_assoc]
        have hdst2 : dst+(codes N T).length+(codes N (T-1)).length+
            (codes N (T-2)).length ≤ powers := by omega
        have hdst2Words : dst+(words N T).length+(words N (T-1)).length+
            (words N (T-2)).length ≤ powers := by simpa using hdst2
        have hpowers2 : Powers μ2 powers (2*W) := by
          intro i hi
          rw [hsame1 (powers+i) (Or.inr (by omega))]
          exact hpowers1 i hi
        have hpowerRead2 := hpowers2 (2*N) (by omega)
        rw [pow_two_even] at hpowerRead2
        have hpowerRead2Z : μ2 ((powers : ℤ)+2*(N : ℤ)).toNat = ((4^N : ℕ) : ℤ) := by
          rw [haddrCast,Int.toNat_natCast,hpowerRead2]
        have hargPrefix2 : (pref : ℤ)+3*μ2 (powers+2*N) = ((pref+3*4^N : ℕ) : ℤ) := by
          rw [hpowerRead2]; push_cast; rfl
        have hprefixArg2 : (pref : ℤ)+3*μ2 (powers+2*N) ≤ lim.word := by
          rw [hargPrefix2]
          exact (show ((pref+3*4^N : ℕ) : ℤ) ≤ ((4^W : ℕ) : ℤ) by exact_mod_cast (show pref+3*4^N ≤ 4^W by omega)).trans hpowWord
        have hprefixInt2 : (pref : ℤ)+3*(4 : ℤ)^N ≤ lim.word := by
          simpa [hpowerRead2] using hprefixArg2
        have hreadNonneg2 : (0 : ℤ) ≤ μ2 (powers+2*N) := by rw [hpowerRead2]; positivity
        have hreadTripleWord : 3*μ2 (powers+2*N) ≤ lim.word := by
          rw [hpowerRead2]
          exact (show 3*((4^N : ℕ) : ℤ) ≤ ((4^W : ℕ) : ℤ) by exact_mod_cast (show 3*4^N ≤ 4^W by omega)).trans hpowWord
        have hprefix2 : pref+3*4^N+4^N ≤ 4^W := by omega
        have hchild2 := ih (T-2) (pref+3*4^N)
          (dst+(codes N T).length+(codes N (T-1)).length) μ2
          hNW (by omega) hprefix2 hdst2 hpowers2 (d+1) (by omega)
        light_call hchild2 using time,visits_full_succ htwo,hn0,hn1,hargPrefix2,hpowerRead2,hpowerRead2Z
          with n2 μ3 ⟨hn2,hseg2,hsame2⟩
        have htotalBound : (((codes N T).length+(codes N (T-1)).length+
            (codes N (T-2)).length : ℕ) : ℤ) ≤ lim.word := by
          exact (show (((codes N T).length+(codes N (T-1)).length+
            (codes N (T-2)).length : ℕ) : ℤ) ≤ (lim.space : ℤ) by exact_mod_cast (show (codes N T).length+(codes N (T-1)).length+(codes N (T-2)).length ≤ lim.space by omega)).trans hw
        have hseg01 : Seg μ2 dst
            (output N T pref ++ output N (T-1) (pref+4^N)) := by
          rw [seg_append,output_length]
          exact ⟨hseg0',hseg1⟩
        have hseg01' : Seg μ3 dst
            (output N T pref ++ output N (T-1) (pref+4^N)) :=
          hseg01.of_sameOutside hsame2 (Or.inl (by simp [Nat.add_assoc]))
        light_set ((codes N T).length+(codes N (T-1)).length+(codes N (T-2)).length : ℕ)
          using time,visits_full_succ htwo,hn0,hn1,hn2
        refine ⟨by simp [hcount],?_,?_⟩
        · rw [output_succ_full htwo,seg_append,List.length_append,output_length,output_length]
          exact ⟨hseg01',by simpa [Nat.add_assoc] using hseg2⟩
        · rw [hcount]
          exact hsame01.then hsame2 (fun a ha => by constructor <;> omega)

def program : Program := [body 0]

theorem program_meets {W powers N T pref dst d : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*W+1) ≤ lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hN : N ≤ W) (hT : T ≤ 2*W) (hprefix : pref+4^N ≤ 4^W)
    (hdst : dst+(codes N T).length ≤ powers) (hpowers : Powers μ powers (2*W))
    (hd : d+N ≤ lim.depth) :
    Meets lim program 0 d [N,T,pref,dst,powers] μ (time N T)
      (fun r μ' => r = ((codes N T).length : ℤ) ∧
        Seg μ' dst (output N T pref) ∧ SameOutside μ μ' dst (codes N T).length) :=
  meets rfl hw hspace hword N T pref dst μ hN hT hprefix hdst hpowers d hd

end ThreeSum.LightTernaryEnumeration
