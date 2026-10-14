import Submission.ThreeSum.LightLookupSum

/-! # Actual signed indirect sum with ternary coordinate weights -/

namespace ThreeSum.LightTernaryWeightedSum

open Light Finset

def sum (weights keys : ℕ → ℕ) (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ range n, (weights i : ℤ) * f (keys i)

@[simp] theorem sum_zero (weights keys : ℕ → ℕ) (f : ℕ → ℤ) : sum weights keys f 0 = 0 := by
  simp [sum]

theorem sum_succ (weights keys : ℕ → ℕ) (f : ℕ → ℤ) (j : ℕ) :
    sum weights keys f (j+1) = sum weights keys f j + (weights j : ℤ)*f (keys j) :=
  sum_range_succ _ _

theorem sum_abs_le (weights keys : ℕ → ℕ) (f : ℕ → ℤ) {n j U : ℕ}
    (hw : ∀ i < n, weights i ≤ 2) (hf : ∀ i < n, |f (keys i)| ≤ U)
    (hj : j ≤ n) : |sum weights keys f j| ≤ 2*j*(U : ℤ) := by
  unfold sum
  calc
    |∑ i ∈ range j, (weights i : ℤ)*f (keys i)| ≤
        ∑ i ∈ range j, |(weights i : ℤ)*f (keys i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range j, 2*(U : ℤ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i < n := (mem_range.mp hi).trans_le hj
      rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
      exact mul_le_mul (by exact_mod_cast hw i hin) (hf i hin) (abs_nonneg _)
        (by norm_num)
    _ = _ := by simp; ring

def loopBody : Stmt :=
  .set 5 (v 5 +' M (v 0 +' v 6) *' M (v 2 +' M (v 1 +' v 6)))

def body : Stmt :=
  .set 5 (k 0) ;;
  .for 6 (v 3) loopBody ;;
  .set 0 (v 5)

def time (n : ℕ) : ℕ := 40*n+20

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets_on_keys {p ws ks table n pcount U : ℕ}
    (hmain : P[p]? = some body) (μ : ℕ → ℤ)
    (weights keys : ℕ → ℕ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hws : ws+n ≤ lim.space) (hks : ks+n ≤ lim.space)
    (htable : table+pcount ≤ lim.space)
    (hweights : ∀ i < n, μ (ws+i) = (weights i : ℤ))
    (hkeys : ∀ i < n, μ (ks+i) = (keys i : ℤ))
    (hrange : ∀ i < n, keys i < pcount)
    (hread : ∀ i < n, μ (table+keys i) = f (keys i))
    (hweight : ∀ i < n, weights i ≤ 2)
    (hvalue : ∀ i < n, |f (keys i)| ≤ U)
    (hword : 2*(n+1)*(U : ℤ)+3 ≤ lim.word) :
    Meets lim P p d [ws,ks,table,n,pcount] μ (time n)
      (fun r μ' => r = sum weights keys f n ∧ μ' = μ) := by
  have hf : ∀ i < n, |f (keys i)| ≤ U := hvalue
  apply Meets.of_body hmain
  unfold body time
  light_set 0
  refine Ends.pieceThen (Ends.for (T := 40*n+6)
    (Q := fun σ => σ = ⟨frame [ws,ks,table,n,pcount,sum weights keys f n,n],μ⟩)
    (fun j σ => σ = ⟨frame [ws,ks,table,n,pcount,sum weights keys f j,j],μ⟩)
    n 30 ?start ?round ?done ?bound (hT := by light_time)) ?after
  case start => simp [sum_zero,update_frame_setLocal]
  case round =>
    rintro j _ hj _ rfl
    have hwr := hweights j hj
    have hkr := hkeys j hj
    have hkRange := hrange j hj
    have hr := hread j hj
    have hwrange := hweight j hj
    have hfrange := abs_le.mp (hf j hj)
    have hprod : |(weights j : ℤ)*f (keys j)| ≤ 2*(U : ℤ) := by
      rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
      exact mul_le_mul (by exact_mod_cast hwrange) (hf j hj) (abs_nonneg _) (by norm_num)
    have hprodb := abs_le.mp hprod
    have hprodWord : 2*(U : ℤ) ≤ lim.word := by
      nlinarith [Int.natCast_nonneg n,Int.natCast_nonneg U]
    have hsum := abs_le.mp (sum_abs_le weights keys f hweight hf (j := j+1) (by omega))
    have hsum0 := abs_le.mp (sum_abs_le weights keys f hweight hf (j := j) (by omega))
    have hsumcast := sum_succ weights keys f j
    have hmul : 2*(j+1)*(U : ℤ) ≤ 2*(n+1)*(U : ℤ) := by gcongr
    have hmulcast : 2*((j+1 : ℕ) : ℤ)*(U : ℤ) ≤ 2*(n+1)*(U : ℤ) := by
      push_cast
      exact hmul
    have hsw : |sum weights keys f (j+1)| ≤ lim.word :=
      (sum_abs_le weights keys f hweight hf (j := j+1) (by omega)).trans
        (hmulcast.trans (by omega))
    have hswbounds := abs_le.mp hsw
    have hmul0 : 2*(j : ℤ)*(U : ℤ) ≤ 2*(n+1)*(U : ℤ) := by gcongr; omega
    have hsw0 : |sum weights keys f j| ≤ lim.word :=
      (sum_abs_le weights keys f hweight hf (j := j) (by omega)).trans
        (hmul0.trans (by omega))
    have hsw0bounds := abs_le.mp hsw0
    unfold loopBody
    refine Ends.setLast ?_ (hs := by light_side [hwr,hkr,hr,← hsumcast])
      (hT := by light_time)
    simp [hwr,hkr,hr,← hsumcast,update_frame_setLocal]
  case done => intro σ hcounter hshape; exact hshape
  case bound => rintro j _ hj _ rfl; light_side
  case after =>
    intro σ hshape
    rw [hshape]
    light_set (sum weights keys f n)
    exact ⟨rfl,rfl⟩

def program : Program := [body]

end ThreeSum.LightTernaryWeightedSum
