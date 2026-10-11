import Submission.ThreeSum.Scales
import Submission.ThreeSum.LightSmallDivide
import Submission.ThreeSumApsp.Lang.Lib.Seg

/-!
# Actual initialization of the integer block schedule

The fixed program computes all initial size parameters from the input
length. It uses the benchmark's proved logarithm, ceiling cube-root and
ceiling-half loops, with exact rounding bridges below. Division is used
only through an actual counting routine on the logarithmic numerator.
-/

namespace ThreeSum.LightScales

open Light ThreeSum.Scales

variable {lim : Limits} {P : Program}

theorem inputBits_le_self (n : ℕ) : inputBits n ≤ n := by
  simpa [inputBits,Nat.log2_eq_log_two] using Nat.log_le_self 2 n

theorem root_le_self (m : ℕ) : Nat.nthRoot 3 m ≤ m :=
  (Nat.le_self_pow (by decide : 3 ≠ 0) (Nat.nthRoot 3 m)).trans
    (Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0)))

theorem microSize_le_self (m : ℕ) : microSize m ≤ m :=
  (microSize_rounding m).1.trans (root_le_self m)

theorem microHalf_le_self (m : ℕ) : microHalf m ≤ m :=
  (Nat.div_le_self (Nat.nthRoot 3 m) 2).trans (root_le_self m)

theorem blockCount_le (m : ℕ) : blockCount m ≤ 20*m :=
  Nat.mul_le_mul_left 20 (Nat.div_le_self m (100*microSize m))

theorem totalSize_le_self (m : ℕ) : totalSize m ≤ m := by
  have h := totalSize_upper m
  omega

theorem cbrtLeast_successor (m : ℕ) : cbrtLeast (m+1) = Nat.nthRoot 3 m+1 := by
  have hlo : Nat.nthRoot 3 m ^ 3 ≤ m := Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0))
  have hhi : m < (Nat.nthRoot 3 m+1)^3 := Nat.lt_pow_nthRoot_add_one (by decide) m
  have hup : cbrtLeast (m+1) ≤ Nat.nthRoot 3 m+1 := cbrtLeast_le (by omega)
  have hstrict : Nat.nthRoot 3 m < cbrtLeast (m+1) := by
    by_contra h
    have hp := Nat.pow_le_pow_left (show cbrtLeast (m+1) ≤ Nat.nthRoot 3 m by omega) 3
    have hneed := le_cbrtLeast_pow (m+1)
    omega
  omega

theorem half_cbrtLeast (m : ℕ) : (cbrtLeast (m+1)+1)/2 = microHalf m+1 := by
  rw [cbrtLeast_successor]
  unfold microHalf
  omega

def values (n : ℕ) : List ℤ :=
  [inputBits n,microHalf (inputBits n),muZero n,blockCount (inputBits n),mu n]

/-- Arguments: original input length and destination of the five parameters.
The result is `mu`; the destination stores bits, micro-half, micro-size,
block count, and total size in that order. -/
def body (pLog pCube pHalf pDiv : ℕ) : Stmt :=
  .call pLog [v 0] 2 ;;
  .call pCube [v 2 +' k 1] 3 ;;
  .call pHalf [v 3] 4 ;;
  .set 5 (v 4 -' k 1) ;;
  .set 6 (k 2 *' v 5) ;;
  .call pDiv [v 2,k 100 *' v 6] 7 ;;
  .set 8 (k 20 *' v 7) ;;
  .set 9 (v 8 *' v 6) ;;
  .store (v 1) (v 2) ;;
  .store (v 1 +' k 1) (v 5) ;;
  .store (v 1 +' k 2) (v 6) ;;
  .store (v 1 +' k 3) (v 8) ;;
  .store (v 1 +' k 4) (v 9) ;;
  .set 0 (v 9)

def time (n : ℕ) : ℕ := log2Time n + cbrtCeilTime (inputBits n+1) +
  halfTime (cbrtLeast (inputBits n+1)) +
  LightSmallDivide.time (inputBits n) (100*muZero n)+200

theorem meets {pMain pLog pCube pHalf pDiv : ℕ}
    (hmain : P[pMain]? = some (body pLog pCube pHalf pDiv))
    (hlog : P[pLog]? = some log2Body)
    (hcube : P[pCube]? = some cbrtCeilBody)
    (hhalf : P[pHalf]? = some halfBody)
    (hdiv : P[pDiv]? = some LightSmallDivide.body)
    {μ : ℕ → ℤ} {n dst d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : dst+5 ≤ lim.space)
    (hword : ((1000*(n+1) : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim P pMain d [n,dst] μ (time n)
      (fun r μ' => r = (mu n : ℤ) ∧ Seg μ' dst (values n) ∧ SameOutside μ μ' dst 5) := by
  have hm : (inputBits n) ≤ n := inputBits_le_self n
  have hm₀ : microSize (inputBits n) ≤ (inputBits n) := microSize_le_self (inputBits n)
  have hh : microHalf (inputBits n) ≤ (inputBits n) := microHalf_le_self (inputBits n)
  have hJ : blockCount (inputBits n) ≤ 20*(inputBits n) := blockCount_le (inputBits n)
  have hmu : totalSize (inputBits n) ≤ (inputBits n) := totalSize_le_self (inputBits n)
  have hu : cbrtLeast ((inputBits n)+1) ≤ (inputBits n)+1 := cbrtLeast_le_self ((inputBits n)+1)
  have hall (x : ℕ) (hx : x ≤ 1000*(n+1)) : (x : ℤ) ≤ lim.word := by
    have hz : (x : ℤ) ≤ ((1000*(n+1) : ℕ) : ℤ) := by exact_mod_cast hx
    exact hz.trans hword
  have hmWord := hall (inputBits n) (by omega)
  have hhWord := hall (microHalf (inputBits n)) (by omega)
  have hm₀Word := hall (microSize (inputBits n)) (by omega)
  have hJWord := hall (blockCount (inputBits n)) (by omega)
  have hmuWord := hall (totalSize (inputBits n)) (by omega)
  have hdenWord : (100 : ℤ)*(microSize (inputBits n) : ℤ) ≤ lim.word := by
    simpa using hall (100*microSize (inputBits n)) (by omega)
  have hproductWord : (blockCount (inputBits n) : ℤ)*(microSize (inputBits n) : ℤ) ≤ lim.word := by
    simpa [totalSize] using hmuWord
  have hproductNonneg : (0 : ℤ) ≤ (blockCount (inputBits n) : ℤ)*(microSize (inputBits n) : ℤ) := by positivity
  have hsizeEq : (2 : ℤ)*(microHalf (inputBits n) : ℤ) = (microSize (inputBits n) : ℤ) := by
    simp [microSize,microHalf]
  have hcountEq : (20 : ℤ)*((inputBits n/(100*microSize (inputBits n)) : ℕ) : ℤ) =
      (blockCount (inputBits n) : ℤ) := by simp [blockCount]
  have hproductEq : (blockCount (inputBits n) : ℤ)*(microSize (inputBits n) : ℤ) =
      (totalSize (inputBits n) : ℤ) := by simp [totalSize]
  apply Meets.of_body hmain
  unfold body time
  have hlogCall := log2_meets (d := d+1) (x := n) hlog μ (hall _ (by omega))
  light_call hlogCall using cbrtCeilTime,halfTime,LightSmallDivide.time
    with bits μ₁ ⟨hbits,hmem₁⟩
  subst μ₁
  have hbits' : bits = ((inputBits n) : ℤ) := by simpa [inputBits,Nat.log2_eq_log_two] using hbits
  have hcubeCall := cbrtCeil_meets (d := d+1) (n := (inputBits n)+1) hcube μ (hall _ (by omega))
  light_call hcubeCall using hbits',cbrtCeilTime,halfTime,LightSmallDivide.time
    with cube μ₂ ⟨hc,hmem₂⟩
  subst μ₂
  have hhalfCall := half_meets (d := d+1) (h := cbrtLeast ((inputBits n)+1)) hhalf μ (hall _ (by omega))
  light_call hhalfCall using hc,cbrtCeilTime,halfTime,LightSmallDivide.time
    with half μ₃ ⟨hv,hmem₃⟩
  subst μ₃
  have hv' : half = ((microHalf (inputBits n)+1 : ℕ) : ℤ) := by simpa [half_cbrtLeast] using hv
  light_set (microHalf (inputBits n) : ℕ) using hv',cbrtCeilTime,halfTime,LightSmallDivide.time
  light_set (microSize (inputBits n) : ℕ) using hsizeEq,cbrtCeilTime,halfTime,LightSmallDivide.time
  have hdivCall := LightSmallDivide.meets (d := d+1) (a := (inputBits n)) (b := 100*microSize (inputBits n))
    hdiv μ (hall _ (by omega))
  light_call hdivCall using hbits',cbrtCeilTime,halfTime,LightSmallDivide.time,muZero
    with q μ₄ ⟨hq,hmem₄⟩
  subst μ₄
  have hquotNonneg : (0 : ℤ) ≤ (inputBits n : ℤ)/(100*(microSize (inputBits n) : ℤ)) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Int.natCast_ediv] using
      (Int.natCast_nonneg (inputBits n/(100*microSize (inputBits n))))
  have hquotWord : (20 : ℤ)*((inputBits n : ℤ)/(100*(microSize (inputBits n) : ℤ))) ≤ lim.word := by
    simpa only [blockCount,Nat.cast_mul,Nat.cast_ofNat,Int.natCast_ediv] using hJWord
  have hqZ : q = (inputBits n : ℤ)/(100*(microSize (inputBits n) : ℤ)) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Int.natCast_ediv] using hq
  light_set (blockCount (inputBits n) : ℕ) using hqZ,hcountEq,cbrtCeilTime,halfTime,LightSmallDivide.time,muZero
  light_set (totalSize (inputBits n) : ℕ) using hproductEq,cbrtCeilTime,halfTime,LightSmallDivide.time,muZero
  light_store dst ((inputBits n) : ℕ) using hbits',cbrtCeilTime,halfTime,LightSmallDivide.time,muZero
  light_store (dst+1) (microHalf (inputBits n) : ℕ) using cbrtCeilTime,halfTime,LightSmallDivide.time,muZero
  light_store (dst+2) (microSize (inputBits n) : ℕ) using cbrtCeilTime,halfTime,LightSmallDivide.time,muZero
  light_store (dst+3) (blockCount (inputBits n) : ℕ) using cbrtCeilTime,halfTime,LightSmallDivide.time,muZero
  light_store (dst+4) (totalSize (inputBits n) : ℕ) using cbrtCeilTime,halfTime,LightSmallDivide.time,muZero
  light_set (totalSize (inputBits n) : ℕ) using cbrtCeilTime,halfTime,LightSmallDivide.time,muZero
  refine ⟨by simp [mu],?_,by light_keep⟩
  simp [values,seg_cons,muZero,mu]

def program : Program := [body 1 2 3 4,log2Body,cbrtCeilBody,halfBody,LightSmallDivide.body]

theorem program_meets {μ : ℕ → ℤ} {n dst d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : dst+5 ≤ lim.space)
    (hword : ((1000*(n+1) : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim program 0 d [n,dst] μ (time n)
      (fun r μ' => r = (mu n : ℤ) ∧ Seg μ' dst (values n) ∧ SameOutside μ μ' dst 5) :=
  meets rfl rfl rfl rfl rfl hw hspace hword hd

theorem time_bound (n : ℕ) : time n ≤ 500*(inputBits n+1) := by
  have hu := cbrtLeast_le_self (inputBits n+1)
  have hh := Nat.div_le_self (cbrtLeast (inputBits n+1)+1) 2
  have hq := Nat.div_le_self (inputBits n) (100*muZero n)
  unfold time log2Time cbrtCeilTime halfTime LightSmallDivide.time
  simp only [inputBits,Nat.log2_eq_log_two] at *
  omega

/-- A syntax-only placement interface for embedding the initializer into a
larger fixed program. -/
structure Procs (P : Program) (pMain : ℕ) where
  pLog : ℕ
  pCube : ℕ
  pHalf : ℕ
  pDiv : ℕ
  main : P[pMain]? = some (body pLog pCube pHalf pDiv)
  log : P[pLog]? = some log2Body
  cube : P[pCube]? = some cbrtCeilBody
  half : P[pHalf]? = some halfBody
  divide : P[pDiv]? = some LightSmallDivide.body

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {n dst d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : dst+5 ≤ lim.space)
    (hword : ((1000*(n+1) : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim P pMain d [n,dst] μ (time n)
      (fun r μ' => r = (mu n : ℤ) ∧ Seg μ' dst (values n) ∧ SameOutside μ μ' dst 5) :=
  LightScales.meets S.main S.log S.cube S.half S.divide hw hspace hword hd

end ThreeSum.LightScales
