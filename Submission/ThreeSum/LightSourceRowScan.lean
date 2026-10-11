import Submission.ThreeSum.LightArray
import Submission.ThreeSum.LightMaskBits
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting and hashing one physical block row

A single scan of the Boolean row constructs its cardinality and both raw
one-hot hashes. The two orientations are accumulated independently from the
stored unscaled map rows. All arithmetic is explicitly word bounded.
-/

namespace ThreeSum.LightSourceRowScan

open Light Finset
open scoped BigOperators

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def count (bits : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, bits i

def hash (bits w0 w1 : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ range n, if bits i=1 then w1 i else w0 i

@[simp] theorem count_zero (bits : ℕ → ℕ) : count bits 0=0 := by simp [count]
@[simp] theorem hash_zero (bits w0 w1 : ℕ → ℕ) : hash bits w0 w1 0=0 := by simp [hash]

theorem count_succ (bits : ℕ → ℕ) (n : ℕ) : count bits (n+1)=count bits n+bits n :=
  Finset.sum_range_succ _ _

theorem hash_succ (bits w0 w1 : ℕ → ℕ) (n : ℕ) :
    hash bits w0 w1 (n+1)=hash bits w0 w1 n+(if bits n=1 then w1 n else w0 n) :=
  Finset.sum_range_succ _ _

theorem count_le {L j : ℕ} (bits : ℕ → ℕ) (hb : ∀ i < L, bits i ≤ 1) (hj : j ≤ L) :
    count bits j ≤ j := by
  unfold count
  calc
    _ ≤ ∑ _i ∈ range j, (1 : ℕ) :=
      Finset.sum_le_sum (fun i hi => hb i ((mem_range.mp hi).trans_le hj))
    _ = j := by simp

theorem hash_le {L j U : ℕ} (bits w0 w1 : ℕ → ℕ)
    (h0 : ∀ i < L, w0 i ≤ U) (h1 : ∀ i < L, w1 i ≤ U) (hj : j ≤ L) :
    hash bits w0 w1 j ≤ j*U := by
  unfold hash
  calc
    _ ≤ ∑ _i ∈ range j, U := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := (mem_range.mp hi).trans_le hj
      split
      · exact h1 i hi'
      · exact h0 i hi'
    _ = j*U := by simp

def roundBody : Stmt :=
  .set 9 (M (v 0 +' v 8)) ;;
  .set 5 (v 5 +' v 9) ;;
  .ite (v 9 =' k 1)
    (.set 6 (v 6 +' M (v 2 +' v 8)) ;;
      .set 7 (v 7 +' M (v 1 +' v 8)))
    (.set 6 (v 6 +' M (v 1 +' v 8)) ;;
      .set 7 (v 7 +' M (v 2 +' v 8)))

/-- Arguments: Boolean row, zero coefficients, one coefficients, width,
and three-cell output (cardinality, left hash, right hash). -/
def body : Stmt :=
  .set 5 (k 0) ;;
  .set 6 (k 0) ;;
  .set 7 (k 0) ;;
  .for 8 (v 3) roundBody ;;
  .store (v 4) (v 5) ;;
  .store (v 4 +' k 1) (v 6) ;;
  .store (v 4 +' k 2) (v 7)

def time (L : ℕ) : ℕ := 150*L+100
def word (L U : ℕ) : ℕ := (L+1)*(U+1)+1

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain : ℕ} (hmain : P[pMain]? = some body)
    {μ : ℕ → ℤ} {src src0 src1 L dst U : ℕ} (bits w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+L ≤ lim.space) (hsrc0 : src0+L ≤ lim.space)
    (hsrc1 : src1+L ≤ lim.space) (hdst : dst+3 ≤ lim.space)
    (hword : (word L U : ℤ) ≤ lim.word)
    (hbits : ∀ i < L, μ (src+i) = (bits i : ℤ))
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbitBound : ∀ i < L, bits i ≤ 1)
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    Meets lim P pMain d [src,src0,src1,L,dst] μ (time L) (fun _ ν =>
      ν dst = (count bits L : ℤ) ∧
      ν (dst+1) = (hash bits w0 w1 L : ℤ) ∧
      ν (dst+2) = (hash bits w1 w0 L : ℤ) ∧ SameOutside μ ν dst 3) := by
  have hbudget (x : ℕ) (hx : x ≤ word L U) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have h1 := hbudget 1 (by unfold word; nlinarith)
  have hU := hbudget U (by unfold word; nlinarith)
  have hL := hbudget L (by unfold word; nlinarith)
  have hLU := hbudget (L*U) (by unfold word; nlinarith)
  have hc := count_le bits hbitBound (j := L) le_rfl
  have hl := hash_le bits w0 w1 hbound0 hbound1 (j := L) le_rfl
  have hr := hash_le bits w1 w0 hbound1 hbound0 (j := L) le_rfl
  have hcWord := (Int.ofNat_le.mpr hc).trans hL
  have hlWord := (Int.ofNat_le.mpr hl).trans hLU
  have hrWord := (Int.ofNat_le.mpr hr).trans hLU
  apply Meets.of_body hmain
  unfold body time
  light_set 0
  light_set 0
  light_set 0
  let shape := fun j (σ : State) => ∃ b : ℤ,
    σ = ⟨frame [src,src0,src1,L,dst,count bits j,hash bits w0 w1 j,
      hash bits w1 w0 j,j,b],μ⟩
  refine Ends.pieceThen (Ends.for shape L 142 ?start ?round ?done ?bound
    (Q := shape L) (T := 150*L+6) (hT := by light_time)) ?finish
  case start =>
    refine ⟨0,?_⟩
    simp only [count_zero,hash_zero]
    exact congrArg (fun loc => (⟨loc,μ⟩ : State))
      ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
  case round =>
    rintro i _ hi _ ⟨b,rfl⟩
    have hb := hbitBound i hi
    have hbRead := hbits i hi
    have h0 := hread0 i hi
    have h1' := hread1 i hi
    have h0B := hbound0 i hi
    have h1B := hbound1 i hi
    have hc' := count_le bits hbitBound (j := i+1) (by omega)
    have hl' := hash_le bits w0 w1 hbound0 hbound1 (j := i+1) (by omega)
    have hr' := hash_le bits w1 w0 hbound1 hbound0 (j := i+1) (by omega)
    have hcW : (count bits (i+1) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hc'.trans (by omega))).trans hL
    have hiU : (i+1)*U ≤ L*U := Nat.mul_le_mul_right U (by omega)
    have hlW : (hash bits w0 w1 (i+1) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hl'.trans hiU)).trans hLU
    have hrW : (hash bits w1 w0 (i+1) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hr'.trans hiU)).trans hLU
    have hcCast : (count bits i : ℤ)+(bits i : ℤ) = (count bits (i+1) : ℤ) := by
      rw [count_succ,Nat.cast_add]
    unfold roundBody
    light_set (bits i : ℕ) using hbRead
    light_set (count bits (i+1) : ℕ) using hcCast
    light_if hy hn : (bits i : ℤ)=1
    · have he : bits i=1 := by exact_mod_cast hy
      have hlCast : (hash bits w0 w1 i : ℤ)+(w1 i : ℤ) = hash bits w0 w1 (i+1) := by
        rw [hash_succ,if_pos he,Nat.cast_add]
      have hrCast : (hash bits w1 w0 i : ℤ)+(w0 i : ℤ) = hash bits w1 w0 (i+1) := by
        rw [hash_succ,if_pos he,Nat.cast_add]
      light_set (hash bits w0 w1 (i+1) : ℕ) using h1',hlCast
      light_set (hash bits w1 w0 (i+1) : ℕ) using h0,hrCast
      exact ⟨by simp, bits i, by simp [update_frame_setLocal]⟩
    · have he : bits i≠1 := by exact_mod_cast hn
      have hlCast : (hash bits w0 w1 i : ℤ)+(w0 i : ℤ) = hash bits w0 w1 (i+1) := by
        rw [hash_succ,if_neg he,Nat.cast_add]
      have hrCast : (hash bits w1 w0 i : ℤ)+(w1 i : ℤ) = hash bits w1 w0 (i+1) := by
        rw [hash_succ,if_neg he,Nat.cast_add]
      light_set (hash bits w0 w1 (i+1) : ℕ) using h0,hlCast
      light_set (hash bits w1 w0 (i+1) : ℕ) using h1',hrCast
      exact ⟨by simp, bits i, by simp [update_frame_setLocal]⟩
  case done =>
    intro σ hi hshape
    exact hshape
  case bound =>
    rintro i _ hi _ ⟨b,rfl⟩
    simp
  case finish =>
    rintro _ ⟨b,rfl⟩
    light_store dst (count bits L : ℕ)
    light_store (dst+1) (hash bits w0 w1 L : ℕ)
    light_store (dst+2) (hash bits w1 w0 L : ℕ)
    refine ⟨by simp,by simp,by simp,?_⟩
    intro a ha
    simp only [Function.update_of_ne (show a ≠ dst+2 by omega),
      Function.update_of_ne (show a ≠ dst+1 by omega),
      Function.update_of_ne (show a ≠ dst by omega)]

def program : Program := [body]

end ThreeSum.LightSourceRowScan
