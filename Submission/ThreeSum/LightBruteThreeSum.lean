import Submission.ThreeSum.LightOriginalTripleScan
import Submission.ThreeSum.OriginalThreeSum

/-!
# A complete original-input solver for the finite exceptional sizes

This four-procedure program checks every original-position triple and all
three inequalities between its indices. Its time is polynomial but is not
the target subquadratic bound. It supplies the exact fallback needed before
the asymptotic parameter regime, with no hypothesis on the integer values
beyond the task's given magnitude bound.
-/

namespace ThreeSum.LightBruteThreeSum

open Light ThreeSumApsp.Spec

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def body (pScan : ℕ) : Stmt :=
  .set 4 (v 0 *' v 0 *' v 0) ;;
  .call pScan [v 2,v 0,v 4] 0

def time (n : ℕ) : ℕ := LightOriginalTripleScan.time n (n^3)+100

def need (n U : ℕ) : Need :=
  ⟨LightOriginalTripleRow.word n U,0,n^3+3⟩

def program : Program := LightOriginalTripleScan.program ++ [body 2]

theorem program_length : program.length=4 := rfl

variable {lim : Limits} {P : Program}

theorem meets {pMain pScan pRow pDivide src n U fr d : ℕ} (x : Fin n → ℤ) (μ : ℕ → ℤ)
    (hp : P[pMain]?=some (body pScan))
    (hscan : P[pScan]?=some (LightOriginalTripleScan.body pScan pRow))
    (hrow : P[pRow]?=some (LightOriginalTripleRow.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (hn : 0 < n) (hsrc : src+n ≤ fr) (H : (need n U).Ok lim fr d)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d [n,U,src,fr] μ (time n)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ ν=μ) := by
  have hw := H.word
  have hs := H.space
  have hspace : src+n ≤ lim.space := hsrc.trans (by have := H.cells; simp only [need,add_zero] at this; exact this)
  have hd : d+n^3+3 ≤ lim.depth := H.depth
  have hn3 : (n^3 : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by dsimp [need,LightOriginalTripleRow.word]; omega)).trans hw
  have hn2 : n*n ≤ n^3 := by
    have hh := Nat.le_mul_of_pos_right (n*n) hn
    simpa only [pow_succ,pow_zero,one_mul] using hh
  have h2Word : (n : ℤ)*(n : ℤ) ≤ lim.word :=
    (by exact_mod_cast hn2 : (n : ℤ)*(n : ℤ) ≤ (n^3 : ℤ)).trans hn3
  have h3Eq : (n : ℤ)*(n : ℤ)*(n : ℤ)=(n^3 : ℕ) := by push_cast; ring
  apply Meets.of_body hp
  unfold body time
  light_set (n^3 : ℕ) using h3Eq,LightOriginalTripleScan.time,LightOriginalTripleRow.time
  have hc := LightOriginalTripleScan.meets (d := d+1) x μ hscan hrow hdivide hn le_rfl
    hs hspace H.word (by omega) hread hbound
  light_call hc using LightOriginalTripleScan.time,LightOriginalTripleRow.time with r ν ⟨hbool,hcorrect,hmem⟩
  exact ⟨hbool,hcorrect.trans (BruteTripleIndex.hit_complete x hn),hmem⟩

theorem poly_need : PolyNeed need := by
  refine ⟨5,3,fun n U => ?_⟩
  let B : ℕ := ((n+1)*(U+1))^3
  have hbaseN : n+1 ≤ (n+1)*(U+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hbaseU : U+1 ≤ (n+1)*(U+1) := Nat.le_mul_of_pos_left _ (by omega)
  have hbase : 1 ≤ (n+1)*(U+1) := Nat.mul_le_mul (by omega : 1 ≤ n+1) (by omega : 1 ≤ U+1)
  have hcube : (n+1)*(U+1) ≤ B := by
    have hh := Nat.le_mul_of_pos_left ((n+1)*(U+1))
      (Nat.one_le_pow 2 _ hbase)
    simpa only [B,pow_succ,pow_zero,one_mul] using hh
  have hN : n ≤ B := (by omega : n ≤ n+1).trans (hbaseN.trans hcube)
  have hU : U ≤ B := (by omega : U ≤ U+1).trans (hbaseU.trans hcube)
  have hN3 : n^3 ≤ B := Nat.pow_le_pow_left (by omega : n ≤ (n+1)*(U+1)) 3
  have h1 : 1 ≤ B := Nat.one_le_pow _ _ hbase
  have hp : polyBound 5 3 [n,U]=32*B := by simp [polyBound,B]
  rw [hp]
  simp only [need,LightOriginalTripleRow.word]
  omega

theorem solves : Solves s3Task program 3 (fun n _ => time n) need := by
  refine ⟨body 2,rfl,fun R lim d x μ fr H hok => ?_⟩
  have hp : (program++R)[3]?=some (body 2) := getElem?_append_of_eq_some (by rfl) R
  have hs : (program++R)[2]?=some (LightOriginalTripleScan.body 2 0) := getElem?_append_of_eq_some (by rfl) R
  have hr : (program++R)[0]?=some (LightOriginalTripleRow.body 1) := getElem?_append_of_eq_some (by rfl) R
  have hv : (program++R)[1]?=some LightSmallDivide.body := getElem?_append_of_eq_some (by rfl) R
  have hh := meets (P := program++R) (pMain := 3) (d := d) (vecOf x.N x.X) μ hp hs hr hv
    H.N_pos H.below hok (OriginalThreeSum.task_read H) (OriginalThreeSum.task_bound H)
  obtain ⟨b,hb,he⟩ := hh.mono le_rfl (fun r ν ⟨hbool,hcorrect,hmem⟩ =>
    OriginalThreeSum.task_post (x := x) (μ := μ) (ν := ν) (fr := fr)
      hbool hcorrect (by subst ν; exact SameOn.refl))
  have heq : b=body 2 := Option.some.inj (hb.symm.trans hp)
  subst b
  exact he

end ThreeSum.LightBruteThreeSum
