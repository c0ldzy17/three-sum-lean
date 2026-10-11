import Submission.ThreeSum.BruteTripleIndex
import Submission.ThreeSum.LightColorParameters

/-! # Execute one exact original-position triple test -/

namespace ThreeSum.LightOriginalTripleRow

open Light BruteTripleIndex

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def body (pDivide : ℕ) : Stmt :=
  .call pDivide [v 2,v 1] 3 ;;
  .call pDivide [v 3,v 1] 4 ;;
  .set 5 (v 3 -' v 4 *' v 1) ;;
  .set 6 (v 2 -' v 3 *' v 1) ;;
  .set 7 (M (v 0 +' v 4)) ;;
  .set 8 (M (v 0 +' v 5)) ;;
  .set 9 (M (v 0 +' v 6)) ;;
  .set 10 (v 7 +' v 8 +' v 9) ;;
  .ite (v 4 =' v 5) (.set 0 (k 0))
    (.ite (v 4 =' v 6) (.set 0 (k 0))
      (.ite (v 5 =' v 6) (.set 0 (k 0))
        (.ite (v 10 =' k 0) (.set 0 (k 1)) (.set 0 (k 0)))))

def time (n : ℕ) : ℕ := 20*(n*n+n)+500
def word (n U : ℕ) : ℕ := n^3+3*U+n+20

variable {lim : Limits} {P : Program}

theorem meets {pMain pDivide src n t U d : ℕ} (x : Fin n → ℤ) (μ : ℕ → ℤ)
    (hp : P[pMain]?=some (body pDivide)) (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (hn : 0 < n) (ht : t < n^3)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : src+n ≤ lim.space)
    (hword : (word n U : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,t] μ (time n)
      (fun result ν => (result=0 ∨ result=1) ∧
        (result=1 ↔ witness x hn ht) ∧ ν=μ) := by
  have hb := bounds hn ht
  let a : Fin n := ⟨first n t,hb.1⟩
  let b : Fin n := ⟨second n t,hb.2.1⟩
  let c : Fin n := ⟨third n t,hb.2.2⟩
  have hwit : witness x hn ht ↔ a≠b ∧ a≠c ∧ b≠c ∧ x a+x b+x c=0 := Iff.rfl
  have hs (i : ℕ) (hi : i ≤ word n U) : (i : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hi).trans hword
  have hqBound : t/n < n*n := (Nat.div_lt_iff_lt_mul hn).mpr (by
    simpa only [pow_succ,pow_zero,one_mul] using ht)
  have hqle : t/n ≤ t := Nat.div_le_self _ _
  have hale : t/n/n ≤ t := (Nat.div_le_self _ _).trans hqle
  have hprodq : (t : ℤ)/(n : ℤ)*(n : ℤ) ≤ lim.word := by
    have hh := (Nat.div_mul_le_self t n).trans (by unfold word; omega : t ≤ word n U)
    exact (by exact_mod_cast hh : (t : ℤ)/(n : ℤ)*(n : ℤ) ≤ (word n U : ℤ)).trans hword
  have hproda : (t : ℤ)/(n : ℤ)/(n : ℤ)*(n : ℤ) ≤ lim.word := by
    have hh := (Nat.div_mul_le_self (t/n) n).trans (by unfold word; omega : t/n ≤ word n U)
    exact (by exact_mod_cast hh : (t : ℤ)/(n : ℤ)/(n : ℤ)*(n : ℤ) ≤ (word n U : ℤ)).trans hword
  have hprodq0 : (0 : ℤ) ≤ (t : ℤ)/(n : ℤ)*(n : ℤ) := by positivity
  have hproda0 : (0 : ℤ) ≤ (t : ℤ)/(n : ℤ)/(n : ℤ)*(n : ℤ) := by positivity
  have hj : (t : ℤ)/(n : ℤ)-(t : ℤ)/(n : ℤ)/(n : ℤ)*(n : ℤ)=(second n t : ℤ) := by
    simpa only [second,Int.natCast_ediv,Int.natCast_emod] using LightColorParameters.remainder (t/n) n
  have hk : (t : ℤ)-(t : ℤ)/(n : ℤ)*(n : ℤ)=(third n t : ℤ) := by
    simpa only [third,Int.natCast_ediv,Int.natCast_emod] using LightColorParameters.remainder t n
  have hA := abs_le.mp (hbound a)
  have hB := abs_le.mp (hbound b)
  have hC := abs_le.mp (hbound c)
  have hleft : |x a+x b| ≤ lim.word := by
    have hh := hs (2*U) (by unfold word; omega)
    push_cast at hh
    exact abs_le.mpr ⟨by omega,by omega⟩
  have hsum : |x a+x b+x c| ≤ lim.word := by
    have hh := hs (3*U) (by unfold word; omega)
    push_cast at hh
    exact abs_le.mpr ⟨by omega,by omega⟩
  have hleftSigned := abs_le.mp hleft
  have hsumSigned := abs_le.mp hsum
  have haWord := (hbound a).trans (hs U (by unfold word; omega))
  have hbWord := (hbound b).trans (hs U (by unfold word; omega))
  have hcWord := (hbound c).trans (hs U (by unfold word; omega))
  have haSigned := abs_le.mp haWord
  have hbSigned := abs_le.mp hbWord
  have hcSigned := abs_le.mp hcWord
  have hreadA := hread a
  have hreadB := hread b
  have hreadC := hread c
  apply Meets.of_body hp
  unfold body time
  have hq := (LightSmallDivide.meets (d := d+1) (a := t) (b := n) hdivide μ
    (hs _ (by unfold word; omega))).mono_time
      (show LightSmallDivide.time t n ≤ 20*(n*n)+40 by unfold LightSmallDivide.time; omega)
  light_call hq with q ν₁ ⟨hq,hν₁⟩
  subst ν₁
  have hqI : q=(t : ℤ)/(n : ℤ) := by simpa only [Int.natCast_ediv] using hq
  have hi := (LightSmallDivide.meets (d := d+1) (a := t/n) (b := n) hdivide μ
    (hs _ (by unfold word; omega))).mono_time
      (show LightSmallDivide.time (t/n) n ≤ 20*n+40 by unfold LightSmallDivide.time; dsimp [first] at hb; omega)
  light_call hi using hq with i ν₂ ⟨hi,hν₂⟩
  subst ν₂
  have hiI : i=(t : ℤ)/(n : ℤ)/(n : ℤ) := by simpa only [Int.natCast_ediv] using hi
  have hi' : i=(first n t : ℤ) := hi
  light_set (second n t : ℕ) using hqI,hiI,hj
  light_set (third n t : ℕ) using hqI,hk
  light_set (x a) using hi',hreadA,a
  light_set (x b) using hreadB,b
  light_set (x c) using hreadC,c
  light_set (x a+x b+x c)
  light_if hAB hNAB : (first n t : ℤ)=(second n t : ℤ) using hi'
  · have hab : a=b := Fin.ext (by exact_mod_cast hAB)
    light_set (0 : ℕ)
    exact ⟨by simp,by simp [hwit,hab],rfl⟩
  · have hab : a≠b := by intro hh; apply hNAB; exact_mod_cast congrArg Fin.val hh
    light_if hAC hNAC : (first n t : ℤ)=(third n t : ℤ) using hi'
    · have hac : a=c := Fin.ext (by exact_mod_cast hAC)
      light_set (0 : ℕ)
      exact ⟨by simp,by simp [hwit,hac],rfl⟩
    · have hac : a≠c := by intro hh; apply hNAC; exact_mod_cast congrArg Fin.val hh
      light_if hBC hNBC : (second n t : ℤ)=(third n t : ℤ)
      · have hbc : b=c := Fin.ext (by exact_mod_cast hBC)
        light_set (0 : ℕ)
        exact ⟨by simp,by simp [hwit,hbc],rfl⟩
      · have hbc : b≠c := by intro hh; apply hNBC; exact_mod_cast congrArg Fin.val hh
        light_if hz hnz : x a+x b+x c=0
        · light_set (1 : ℕ)
          exact ⟨by simp,by simp [hwit,hab,hac,hbc,hz],rfl⟩
        · light_set (0 : ℕ)
          exact ⟨by simp,by simp [hwit,hab,hac,hbc,hnz],rfl⟩

def program : Program := [body 1,LightSmallDivide.body]

end ThreeSum.LightOriginalTripleRow
