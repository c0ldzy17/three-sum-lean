import Submission.ThreeSum.LightTernaryWeightedSum
import Submission.ThreeSum.LightTernaryDivide

/-!
# Actual outside-bank Euler row arithmetic

The row reads physical trinary coordinate weights and physical predecessor
addresses.  It computes their signed weighted sum with a real loop, then
performs the exact positive-denominator division with the proved logarithmic
integer procedure.  No transform value is an abstract machine operation.
-/

namespace ThreeSum.LightTernaryEulerRow

open Light

/-- Arguments: coefficient row, predecessor-index row, value base, row width,
value-range bound, positive Euler denominator, and scratch free pointer. -/
def body (pSum pDivide : ℕ) : Stmt :=
  .call pSum [v 0,v 1,v 2,v 3,v 4] 7 ;;
  .call pDivide [v 7,v 5,v 6] 0

def time (N V : ℕ) : ℕ :=
  LightTernaryWeightedSum.time N + LightTernaryDivide.time V + 100

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Correctness is from the stored predecessor values and the exact Euler
identity for the desired row.  Key-scoped bounds permit bank and memo values
to occupy separate physical regions, without copying the bank per query. -/
theorem meets {pMain pSum pDivide pNaturalDivide ws ks table N pcount Mo V fr U : ℕ}
    {q : ℤ}
    (hmain : P[pMain]? = some (body pSum pDivide))
    (hsum : P[pSum]? = some LightTernaryWeightedSum.body)
    (hdivide : P[pDivide]? = some (LightTernaryDivide.body pNaturalDivide))
    (hnatural : P[pNaturalDivide]? = some LightOutputDecodeDivide.body)
    (μ : ℕ → ℤ) (weights keys : ℕ → ℕ) (f : ℕ → ℤ)
    (F : Light.Emod.Pre lim Mo V fr)
    (hws : ws+N ≤ lim.space) (hks : ks+N ≤ lim.space)
    (htable : table+pcount ≤ lim.space)
    (hweights : ∀ i < N, μ (ws+i) = (weights i : ℤ))
    (hkeys : ∀ i < N, μ (ks+i) = (keys i : ℤ))
    (hrange : ∀ i < N, keys i < pcount)
    (hread : ∀ i < N, μ (table+keys i) = f (keys i))
    (hweight : ∀ i < N, weights i ≤ 2)
    (hvalue : ∀ i < N, |f (keys i)| ≤ U)
    (hV : 2*(N+1)*U ≤ V)
    (hEuler : LightTernaryWeightedSum.sum weights keys f N = (Mo : ℤ)*q)
    (hd : d+2 ≤ lim.depth) :
    Meets lim P pMain d [ws,ks,table,N,pcount,Mo,fr] μ (time N V)
      (fun r μ' => r=q ∧ Kept μ μ' fr) := by
  light_facts F
  have hvalueWord : 2*(N+1)*(U : ℤ)+3 ≤ lim.word := by
    have hVcast : 2*(N+1)*(U : ℤ) ≤ (V : ℤ) := by exact_mod_cast hV
    omega
  have hsumCall := LightTernaryWeightedSum.meets_on_keys (d := d+1) hsum μ
    weights keys f F.space hws hks htable hweights hkeys hrange hread
    hweight hvalue hvalueWord
  have hnum : (LightTernaryWeightedSum.sum weights keys f N).natAbs ≤ V := by
    have hh := LightTernaryWeightedSum.sum_abs_le weights keys f hweight hvalue
      (j := N) le_rfl
    have hbound : 2*N*(U : ℤ) ≤ (V : ℤ) := by
      have hc : 2*N*U ≤ V := (Nat.mul_le_mul_right U (by omega : 2*N ≤ 2*(N+1))).trans hV
      exact_mod_cast hc
    rw [← Int.natCast_natAbs] at hh
    exact_mod_cast hh.trans hbound
  have hdivideCall := LightTernaryDivide.meets (d := d+1) hdivide hnatural μ F
    hnum hEuler (by omega)
  apply Meets.of_body hmain
  unfold body time
  light_call hsumCall using LightTernaryWeightedSum.time,LightTernaryDivide.time
    with numerator ν ⟨hresult,hmem⟩
  subst ν
  light_call hdivideCall using hresult,LightTernaryWeightedSum.time,LightTernaryDivide.time
    with result μ' ⟨hresult,hkeep⟩
  exact ⟨hresult,hkeep⟩

def program : Program := [body 1 2,LightTernaryWeightedSum.body,
  LightTernaryDivide.body 3,LightOutputDecodeDivide.body]

theorem time_bound (N V : ℕ) :
    time N V ≤ 400*(N+Nat.log 2 (V+1)+3) := by
  have hd := LightTernaryDivide.time_bound V
  unfold time LightTernaryWeightedSum.time
  omega

/-- Compute a row once and write its compact memo cell. -/
def fillBody (pRow : ℕ) : Stmt :=
  .call pRow [v 0,v 1,v 2,v 3,v 4,v 5,v 6] 8 ;;
  .store (v 7) (v 8) ;;
  .set 0 (v 8)

def fillTime (N V : ℕ) : ℕ := time N V+100

theorem fill_meets
    {pMain pRow pSum pDivide pNaturalDivide ws ks table N pcount Mo V fr U dst : ℕ}
    {q : ℤ}
    (hmain : P[pMain]? = some (fillBody pRow))
    (hrow : P[pRow]? = some (body pSum pDivide))
    (hsum : P[pSum]? = some LightTernaryWeightedSum.body)
    (hdivide : P[pDivide]? = some (LightTernaryDivide.body pNaturalDivide))
    (hnatural : P[pNaturalDivide]? = some LightOutputDecodeDivide.body)
    (μ : ℕ → ℤ) (weights keys : ℕ → ℕ) (f : ℕ → ℤ)
    (F : Light.Emod.Pre lim Mo V fr)
    (hws : ws+N ≤ lim.space) (hks : ks+N ≤ lim.space)
    (htable : table+pcount ≤ lim.space)
    (hweights : ∀ i < N, μ (ws+i) = (weights i : ℤ))
    (hkeys : ∀ i < N, μ (ks+i) = (keys i : ℤ))
    (hrange : ∀ i < N, keys i < pcount)
    (hread : ∀ i < N, μ (table+keys i) = f (keys i))
    (hweight : ∀ i < N, weights i ≤ 2)
    (hvalue : ∀ i < N, |f (keys i)| ≤ U)
    (hV : 2*(N+1)*U ≤ V)
    (hEuler : LightTernaryWeightedSum.sum weights keys f N = (Mo : ℤ)*q)
    (hdst : dst < fr) (hd : d+3 ≤ lim.depth) :
    Meets lim P pMain d [ws,ks,table,N,pcount,Mo,fr,dst] μ (fillTime N V)
      (fun r μ' => r=q ∧ μ' dst=q ∧
        ∀ a < fr, a ≠ dst → μ' a=μ a) := by
  light_facts F
  have hsumAbs := LightTernaryWeightedSum.sum_abs_le weights keys f hweight hvalue
    (j := N) le_rfl
  have hnum : |LightTernaryWeightedSum.sum weights keys f N| ≤ (V : ℤ) := by
    have hc : 2*N*(U : ℤ) ≤ (V : ℤ) := by
      have hb : 2*N*U ≤ V :=
        (Nat.mul_le_mul_right U (by omega : 2*N ≤ 2*(N+1))).trans hV
      exact_mod_cast hb
    exact hsumAbs.trans hc
  have hq : |q| ≤ (V : ℤ) := by
    have hM : 1 ≤ |(Mo : ℤ)| := by
      rw [abs_of_nonneg (Int.natCast_nonneg Mo)]
      exact_mod_cast F.mod_pos
    rw [hEuler,abs_mul] at hnum
    nlinarith [abs_nonneg q]
  have hqb := abs_le.mp hq
  have hcall := meets (d := d+1) hrow hsum hdivide hnatural μ weights keys f F
    hws hks htable hweights hkeys hrange hread hweight hvalue hV hEuler (by omega)
  apply Meets.of_body hmain
  unfold fillBody fillTime
  light_call hcall using time,LightTernaryWeightedSum.time,LightTernaryDivide.time
    with result ν ⟨hr,hkeep⟩
  light_store dst q using hr,time,LightTernaryWeightedSum.time,LightTernaryDivide.time
  light_set q using hr,time,LightTernaryWeightedSum.time,LightTernaryDivide.time
  refine ⟨rfl,by simp,?_⟩
  intro a ha hne
  change Function.update ν dst q a = μ a
  rw [Function.update_of_ne hne]
  exact hkeep a ha

end ThreeSum.LightTernaryEulerRow
