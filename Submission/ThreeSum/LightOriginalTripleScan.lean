import Submission.ThreeSum.LightOriginalTripleRow

/-! # Execute the exact finite fallback scan over original triples -/

namespace ThreeSum.LightOriginalTripleScan

open Light BruteTripleIndex

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

def body (pSelf pRow : ℕ) : Stmt :=
  .ite (k 0 <' v 2)
    (.call pSelf [v 0,v 1,v 2 -' k 1] 3 ;;
      .call pRow [v 0,v 1,v 2 -' k 1] 4 ;;
      .ite (k 0 <' v 3 +' v 4) (.set 0 (k 1)) (.set 0 (k 0)))
    (.set 0 (k 0))

def time (n t : ℕ) : ℕ := t*(LightOriginalTripleRow.time n+150)+50

variable {lim : Limits} {P : Program}

theorem meets {pMain pRow pDivide src n t U d : ℕ} (x : Fin n → ℤ) (μ : ℕ → ℤ)
    (hp : P[pMain]?=some (body pMain pRow))
    (hrow : P[pRow]?=some (LightOriginalTripleRow.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (hn : 0 < n) (ht : t ≤ n^3)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : src+n ≤ lim.space)
    (hword : (LightOriginalTripleRow.word n U : ℤ) ≤ lim.word)
    (hd : d+t+2 ≤ lim.depth)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,t] μ (time n t)
      (fun result ν => (result=0 ∨ result=1) ∧ (result=1 ↔ Hit x hn t) ∧ ν=μ) := by
  have htwo : (2 : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show (2 : ℕ) ≤ LightOriginalTripleRow.word n U by
      unfold LightOriginalTripleRow.word; omega)).trans hword
  have hcube : ((n^3 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show n^3 ≤ LightOriginalTripleRow.word n U by
      unfold LightOriginalTripleRow.word; omega)).trans hword
  induction t generalizing d with
  | zero =>
      apply Meets.of_body hp
      unfold body time
      light_if hbad hno : (0 : ℤ)<0
      · omega
      · light_set (0 : ℕ)
        exact ⟨by simp,by simp [hit_zero],rfl⟩
  | succ t ih =>
      have ht' : t < n^3 := by omega
      apply Meets.of_body hp
      unfold body time
      light_if hyes hbad : (0 : ℤ)<((t+1 : ℕ) : ℤ) using LightOriginalTripleRow.time
      · have hrec := ih (d := d+1) (by omega) (by omega)
        light_call hrec using time,LightOriginalTripleRow.time with prev ν₁ ⟨hprevBool,hprev,hν₁⟩
        subst ν₁
        have hcall := LightOriginalTripleRow.meets (d := d+1) x μ hrow hdivide hn ht'
          hw hspace hword (by omega) hread hbound
        light_call hcall using time,LightOriginalTripleRow.time with found ν₂ ⟨hfoundBool,hfound,hν₂⟩
        subst ν₂
        have hpRange : 0 ≤ prev ∧ prev ≤ 1 := by rcases hprevBool with hh | hh <;> omega
        have hfRange : 0 ≤ found ∧ found ≤ 1 := by rcases hfoundBool with hh | hh <;> omega
        have hsum : (0 : ℤ)<prev+found ↔ Hit x hn (t+1) := by
          rw [hit_succ x hn ht',show (0 : ℤ)<prev+found ↔ prev=1 ∨ found=1 by omega,hprev,hfound]
        light_if hhit hmiss : (0 : ℤ)<prev+found using time,LightOriginalTripleRow.time
        · have hh := hsum.mp hhit
          light_set (1 : ℕ) using time,LightOriginalTripleRow.time
          exact ⟨by simp,by simpa using hh,rfl⟩
        · have hh : ¬ Hit x hn (t+1) := fun h => hmiss (hsum.mpr h)
          light_set (0 : ℕ) using time,LightOriginalTripleRow.time
          exact ⟨by simp,by simp [hh],rfl⟩
      · omega

def program : Program := LightOriginalTripleRow.program ++ [body 2 0]

end ThreeSum.LightOriginalTripleScan
