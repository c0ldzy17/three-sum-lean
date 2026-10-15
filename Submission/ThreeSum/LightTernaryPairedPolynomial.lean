import Submission.ThreeSum.LightMomentDeterminant
import Submission.ThreeSum.TernaryPairedTensor

/-! The fixed polynomial of fourth mixed tensor entries is a literal
arithmetic circuit. Its atoms read the actual tensor array at a supplied
column tuple; there is no determinant or paired-potential machine oracle. -/

noncomputable section
namespace ThreeSum.LightTernaryPairedPolynomial

open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators

abbrev Quad (m : ℕ) := PairedIndex m × PairedIndex m × PairedIndex m × PairedIndex m

def encode {m : ℕ} (q : Quad m) : ℕ := (Fintype.equivFin (Quad m) q).val

def channel {m : ℕ} (σ τ : Equiv.Perm (PairedIndex m)) (i : Fin m) : Quad m :=
  (σ (.inl i),τ (.inl i),σ (.inr i),τ (.inr i))

def polynomial (m : ℕ) : Circuit :=
  sumCircuits ((Finset.univ : Finset (Equiv.Perm (PairedIndex m))).toList.map fun σ =>
    sumCircuits ((Finset.univ : Finset (Equiv.Perm (PairedIndex m))).toList.map fun τ =>
      .mul (.literal ((Equiv.Perm.sign σ : ℤ)*(Equiv.Perm.sign τ : ℤ)))
        (prodCircuits ((Finset.univ : Finset (Fin m)).toList.map fun i =>
          .atom (encode (channel σ τ i))))))

theorem polynomial_eval (m : ℕ) (x : ℕ → ℤ) :
    (polynomial m).eval x =
      ∑ σ : Equiv.Perm (PairedIndex m), ∑ τ : Equiv.Perm (PairedIndex m),
        ((Equiv.Perm.sign σ : ℤ)*(Equiv.Perm.sign τ : ℤ)) *
          ∏ i : Fin m, x (encode (channel σ τ i)) := by
  classical
  simp only [polynomial,eval_sumCircuits,List.map_map,Function.comp_apply,
    Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.sum_congr rfl
  intro τ hτ
  simp only [Circuit.eval,eval_prodCircuits,List.map_map,Function.comp_apply,
    Finset.prod_map_toList]
  rfl

def tensorIndex (Λ a b c d : ℕ) : ℕ := ((a*Λ+b)*Λ+c)*Λ+d

theorem tensorIndex_lt {Λ a b c d : ℕ} (ha : a<Λ) (hb : b<Λ) (hc : c<Λ) (hd : d<Λ) :
    tensorIndex Λ a b c d < Λ^4 := by
  have h₁ : a*Λ+b < Λ^2 := by nlinarith
  have h₂ : (a*Λ+b)*Λ+c < Λ^3 := by nlinarith [Nat.zero_le Λ]
  unfold tensorIndex
  nlinarith [Nat.zero_le Λ]

def atomExpr (m : ℕ) (q : Quad m) : Expr :=
  let read := fun r : PairedIndex m => M (v 2 +' k (Fintype.equivFin (PairedIndex m) r).val)
  M (v 0 +' (((read q.1 *' v 1 +' read q.2.1) *' v 1 +' read q.2.2.1) *' v 1 +' read q.2.2.2))

def atoms (m : ℕ) (j : ℕ) : Expr :=
  if hj : j < Fintype.card (Quad m) then
    atomExpr m ((Fintype.equivFin (Quad m)).symm ⟨j,hj⟩) else k 0

theorem atoms_encode (m : ℕ) (q : Quad m) : atoms m (encode q) = atomExpr m q := by
  unfold atoms encode
  rw [dif_pos (Fintype.equivFin (Quad m) q).isLt]
  simp

def value {m : ℕ} (T : Quad m → ℤ) : ℤ :=
  ∑ σ : Equiv.Perm (PairedIndex m), ∑ τ : Equiv.Perm (PairedIndex m),
    ((Equiv.Perm.sign σ : ℤ)*(Equiv.Perm.sign τ : ℤ)) *
      ∏ i : Fin m, T (channel σ τ i)

theorem value_scaled {m : ℕ} (T : Quad m → ℤ) (s : ℤ) :
    value (fun q => s*T q)=s^m*value T := by
  unfold value
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ hτ
  ring

theorem value_abs_le {m : ℕ} (T : Quad m → ℤ) (U : ℤ) (hU : 0≤U)
    (hT : ∀ q, |T q|≤U) : |value T|≤(polynomial m).bound U := by
  let x := fun j => if hj : j<Fintype.card (Quad m) then
    T ((Fintype.equivFin (Quad m)).symm ⟨j,hj⟩) else 0
  have he (q : Quad m) : x (encode q)=T q := by
    dsimp [x,encode]
    rw [if_pos (Fintype.equivFin (Quad m) q).isLt]
    simp
  have hp : (polynomial m).eval x=value T := by
    rw [polynomial_eval]
    apply Finset.sum_congr rfl
    intro σ hσ
    apply Finset.sum_congr rfl
    intro τ hτ
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    exact he _
  rw [←hp]
  apply (polynomial m).eval_abs_le x hU
  intro j
  dsimp [x]
  split_ifs
  · exact hT _
  · simpa using hU

theorem polynomial_value (m : ℕ) (T : Quad m → ℤ) (σ : State)
    (hT : ∀ q, (atomExpr m q).val σ=T q) :
    ((polynomial m).compile (atoms m)).val σ=value T := by
  rw [Circuit.compile_val,polynomial_eval]
  apply Finset.sum_congr rfl
  intro perm hperm
  apply Finset.sum_congr rfl
  intro τ hτ
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [atoms_encode,hT]

def body (m : ℕ) : Stmt := .set 0 ((polynomial m).compile (atoms m))
def time (m : ℕ) : ℕ := ((polynomial m).compile (atoms m)).cost+2

theorem body_ends (m : ℕ) (T : Quad m → ℤ) (σ : State) {lim : Limits} {P : Program} {depth : ℕ}
    (U : ℤ) (hU : 0≤U)
    (hSafe : ∀ j, (atoms m j).Safe lim σ)
    (hAbs : ∀ j, |(atoms m j).val σ|≤U)
    (hWord : (polynomial m).coefficient*(U+1)^(polynomial m).degree≤lim.word)
    (hRead : ∀ q, (atomExpr m q).val σ=T q) :
    Ends lim P depth (body m) σ (time m) (fun τ => τ.loc 0=value T ∧ τ.mem=σ.mem) := by
  have hbound := ((polynomial m).bound_polynomial hU).trans hWord
  have hs := (polynomial m).compile_safe (atoms m) σ hU hSafe hAbs hbound
  apply Ends.set hs (by unfold time; omega)
  exact ⟨polynomial_value m T σ hRead,rfl⟩

theorem atomExpr_memory (m base Λ colsBase : ℕ) (cols : PairedIndex m → ℕ)
    (μ : ℕ → ℤ)
    (hcols : ∀ r, μ (colsBase+(Fintype.equivFin (PairedIndex m) r).val)=(cols r : ℤ))
    (q : Quad m) :
    (atomExpr m q).val ⟨frame [base,Λ,colsBase],μ⟩ =
      μ (base+tensorIndex Λ (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2)) := by
  simp [atomExpr,Expr.val,Op.eval,frame,hcols,tensorIndex]
  congr 1

theorem atomExpr_safe (m base Λ colsBase : ℕ) (cols : PairedIndex m → ℕ)
    (μ : ℕ → ℤ) {lim : Limits}
    (hΛ : 1≤Λ) (hbound : ∀ r, cols r<Λ)
    (hcols : ∀ r, μ (colsBase+(Fintype.equivFin (PairedIndex m) r).val)=(cols r : ℤ))
    (hTspace : base+Λ^4≤lim.space) (hCspace : colsBase+Fintype.card (PairedIndex m)≤lim.space)
    (hw : (lim.space : ℤ)≤lim.word) (q : Quad m) :
    (atomExpr m q).Safe lim ⟨frame [base,Λ,colsBase],μ⟩ := by
  let a := cols q.1
  let b := cols q.2.1
  let c := cols q.2.2.1
  let e := cols q.2.2.2
  have ha : a<Λ := hbound _
  have hb : b<Λ := hbound _
  have hc : c<Λ := hbound _
  have he : e<Λ := hbound _
  have h₁ : a*Λ+b<Λ^2 := by nlinarith
  have h₂ : (a*Λ+b)*Λ+c<Λ^3 := by nlinarith
  have h₃ : ((a*Λ+b)*Λ+c)*Λ+e<Λ^4 := tensorIndex_lt ha hb hc he
  have hpow₁ : Λ≤Λ^4 := by simpa using Nat.pow_le_pow_right hΛ (by decide : 1≤4)
  have hpow₂ : Λ^2≤Λ^4 := Nat.pow_le_pow_right hΛ (by decide : 2≤4)
  have hpow₃ : Λ^3≤Λ^4 := Nat.pow_le_pow_right hΛ (by decide : 3≤4)
  have hread₁ := hcols q.1
  have hread₂ := hcols q.2.1
  have hread₃ := hcols q.2.2.1
  have hread₄ := hcols q.2.2.2
  have hind₁ := (Fintype.equivFin (PairedIndex m) q.1).isLt
  have hind₂ := (Fintype.equivFin (PairedIndex m) q.2.1).isLt
  have hind₃ := (Fintype.equivFin (PairedIndex m) q.2.2.1).isLt
  have hind₄ := (Fintype.equivFin (PairedIndex m) q.2.2.2).isLt
  have hnatword (x : ℕ) (hx : x≤lim.space) : (x : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr hx).trans hw
  have hΛWord := hnatword Λ (by omega)
  have h₁word := hnatword (a*Λ+b) (by omega)
  have h₂word := hnatword ((a*Λ+b)*Λ+c) (by omega)
  have h₃word := hnatword (((a*Λ+b)*Λ+c)*Λ+e) (by omega)
  have hmul₁ := hnatword (a*Λ) (by omega)
  have hmul₂ := hnatword ((a*Λ+b)*Λ) (by omega)
  have hmul₃ := hnatword (((a*Λ+b)*Λ+c)*Λ) (by omega)
  dsimp [a,b,c,e] at *
  push_cast at h₁word h₂word h₃word hmul₁ hmul₂ hmul₃
  have hn₁ : (0 : ℤ)≤(cols q.1 : ℤ)*Λ := by positivity
  have hn₂ : (0 : ℤ)≤((cols q.1 : ℤ)*Λ+cols q.2.1)*Λ := by positivity
  have hn₃ : (0 : ℤ)≤(((cols q.1 : ℤ)*Λ+cols q.2.1)*Λ+cols q.2.2.1)*Λ := by positivity
  have haddr : base+tensorIndex Λ (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2)<lim.space :=
    (Nat.add_lt_add_left (tensorIndex_lt ha hb hc he) base).trans_le hTspace
  have haddrZ : (base : ℤ)+((((cols q.1 : ℤ)*Λ+cols q.2.1)*Λ+cols q.2.2.1)*Λ+cols q.2.2.2)<lim.space := by
    simpa [tensorIndex,Nat.cast_add,Nat.cast_mul] using (Int.ofNat_lt.mpr haddr)
  unfold atomExpr
  light_side [hread₁,hread₂,hread₃,hread₄]

theorem meets (m base Λ colsBase : ℕ) (cols : PairedIndex m → ℕ)
    (μ : ℕ → ℤ) {lim : Limits} {P : Program} {p depth : ℕ}
    (hp : P[p]?=some (body m)) (hΛ : 1≤Λ) (hbound : ∀ r, cols r<Λ)
    (hcols : ∀ r, μ (colsBase+(Fintype.equivFin (PairedIndex m) r).val)=(cols r : ℤ))
    (hTspace : base+Λ^4≤lim.space) (hCspace : colsBase+Fintype.card (PairedIndex m)≤lim.space)
    (hw : (lim.space : ℤ)≤lim.word)
    (U : ℤ) (hU : 0≤U) (hTabs : ∀ k<Λ^4, |μ (base+k)|≤U)
    (hWord : (polynomial m).coefficient*(U+1)^(polynomial m).degree≤lim.word) :
    Meets lim P p depth [base,Λ,colsBase] μ (time m)
      (fun r ν => r=value (fun q =>
        μ (base+tensorIndex Λ (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2))) ∧ ν=μ) := by
  apply Meets.of_body hp
  apply body_ends m _ _ U hU
  · intro j
    unfold atoms
    split_ifs with hj
    · exact atomExpr_safe m base Λ colsBase cols μ hΛ hbound hcols hTspace hCspace hw _
    · change (0 : ℤ)≤lim.word
      omega
  · intro j
    unfold atoms
    split_ifs with hj
    · rw [atomExpr_memory m base Λ colsBase cols μ hcols]
      exact hTabs _ (tensorIndex_lt (hbound _) (hbound _) (hbound _) (hbound _))
    · simpa [Expr.val] using hU
  · exact hWord
  · exact atomExpr_memory m base Λ colsBase cols μ hcols

end ThreeSum.LightTernaryPairedPolynomial
