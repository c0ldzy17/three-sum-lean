import Submission.ThreeSum.LightLocalCounts
import Submission.ThreeSum.LightSelectedPrime
import Submission.ThreeSum.LightSmallDivide

/-!
# Complete local integer parameter initialization

From the microblock half-size this program constructs the graph counts,
selects the deterministic prime, and computes the exact separable bucket
cap. The first six output cells are the graph counts; the next two contain
the prime and cap. Scratch may be reused by every stage.
-/

namespace ThreeSum.LightLocalParameters

open Light LocalCoverBounds

def numerator (h : ℕ) : ℕ :=
  4*(localPrime h+vertexCount (512*h) h)+localPrime h-1

def values (h : ℕ) : List ℤ :=
  LightLocalCounts.values h ++ [(localPrime h : ℤ),localBucketCap h]

def body (pCounts pPrime pDiv : ℕ) : Stmt :=
  .call pCounts [v 0,v 1,v 2] 3 ;;
  .call pPrime [v 3,v 2] 4 ;;
  .set 5 (M (v 1 +' k 1)) ;;
  .set 6 (k 4 *' (v 4 +' v 5) +' v 4 -' k 1) ;;
  .call pDiv [v 6,v 4] 7 ;;
  .store (v 1 +' k 6) (v 4) ;;
  .store (v 1 +' k 7) (v 7) ;;
  .set 0 (v 4)

def time (h : ℕ) : ℕ := LightLocalCounts.time h+
  LightSelectedPrime.time (localThreshold h)+
  LightSmallDivide.time (numerator h) (localPrime h)+200

def space (work h : ℕ) : ℕ :=
  max (LightLocalCounts.space work h) (LightSelectedPrime.space work (localThreshold h))

def word (h : ℕ) : ℕ := LightLocalCounts.word h+
  LightSelectedPrime.word (localThreshold h)+20*(localPrime h+vertexCount (512*h) h+1)

structure Procs (P : Program) (pMain : ℕ) where
  pCounts : ℕ
  pPrime : ℕ
  pDiv : ℕ
  counts : LightLocalCounts.Procs P pCounts
  prime : LightSelectedPrime.Procs P pPrime
  divide : P[pDiv]? = some LightSmallDivide.body
  main : P[pMain]? = some (body pCounts pPrime pDiv)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {h dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+5 ≤ lim.depth)
    (hout : dst+8 ≤ work) (hspace : space work h ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h,dst,work] μ (time h)
      (fun r μ' => r = (localPrime h : ℤ) ∧ Seg μ' dst (values h) ∧
        KeptBut μ μ' work dst 8) := by
  have hcs : LightLocalCounts.space work h ≤ lim.space := (le_max_left _ _).trans hspace
  have hps : LightSelectedPrime.space work (localThreshold h) ≤ lim.space := (le_max_right _ _).trans hspace
  have hcw : (LightLocalCounts.word h : ℤ) ≤ lim.word := by
    have hn : LightLocalCounts.word h ≤ word h := by unfold word; omega
    exact (Int.ofNat_le.mpr hn).trans hword
  have hpw : (LightSelectedPrime.word (localThreshold h) : ℤ) ≤ lim.word := by
    have hn : LightSelectedPrime.word (localThreshold h) ≤ word h := by unfold word; omega
    exact (Int.ofNat_le.mpr hn).trans hword
  have hnumw : ((numerator h+localPrime h+2 : ℕ) : ℤ) ≤ lim.word := by
    have hn : numerator h+localPrime h+2 ≤ word h := by unfold numerator word; omega
    exact (Int.ofNat_le.mpr hn).trans hword
  have hsmall : ((20*(localPrime h+vertexCount (512*h) h+1) : ℕ) : ℤ) ≤ lim.word := by
    have hn : 20*(localPrime h+vertexCount (512*h) h+1) ≤ word h := by unfold word; omega
    exact (Int.ofNat_le.mpr hn).trans hword
  have hp := localPrime_pos h
  have hN := localThreshold_pos h
  have hwork : work ≤ lim.space := by unfold LightLocalCounts.space at hcs; omega
  have hhsize : 512*h+1 ≤ LightPascal.tableSize (512*h) := by
    unfold LightPascal.tableSize
    nlinarith
  have hh : h < lim.space := by unfold LightLocalCounts.space at hcs; omega
  have hNWord : (localThreshold h : ℤ) ≤ lim.word := by
    have hh : 100*((localThreshold h : ℤ)+1) ≤ lim.word := by
      simpa [LightSelectedPrime.word] using hpw
    omega
  have hnumEq : (4 : ℤ)*((localPrime h : ℤ)+(vertexCount (512*h) h : ℤ))+
      (localPrime h : ℤ)-1 = (numerator h : ℤ) := by unfold numerator; omega
  have hcapEq : numerator h/localPrime h = localBucketCap h := by
    rfl
  have hcapLe : localBucketCap h ≤ numerator h := by
    rw [← hcapEq]
    exact Nat.div_le_self _ _
  have hcapWord : (localBucketCap h : ℤ) ≤ lim.word := by omega
  apply Meets.of_body S.main
  unfold body time
  light_call (S.counts.meets (d := d+1) (μ := μ) (h := h) (dst := dst) (work := work)
    hw (by omega) (by omega) hcs hcw)
    with threshold μ₁ ⟨ht,hseg,hkept₁⟩
  light_call (S.prime.meets (d := d+1) (μ := μ₁) (N := localThreshold h) (free := work)
    hw (by omega) hN hps hpw)
    using ht with pval μ₂ ⟨hpval,hpool,hkept₂⟩
  have hpval' : pval = (localPrime h : ℤ) := hpval
  have hseg₂ : Seg μ₂ dst (LightLocalCounts.values h) := by
    apply hseg.congr
    intro i hi
    have hi' : i < 6 := by simpa [LightLocalCounts.values] using hi
    exact hkept₂ _ (by omega)
  have hvread : μ₂ (dst+1) = (vertexCount (512*h) h : ℤ) := by
    simpa [LightLocalCounts.values] using hseg₂ 1 (by simp [LightLocalCounts.values])
  light_set (vertexCount (512*h) h : ℕ) using hvread
  light_set (numerator h : ℕ) using hpval',hnumEq
  light_call (LightSmallDivide.meets (d := d+1) (a := numerator h) (b := localPrime h) S.divide μ₂ hnumw)
    using hpval' with cap μ₃ ⟨hcap,hmem₃⟩
  subst μ₃
  have hcap' : cap = (localBucketCap h : ℤ) := by simpa [hcapEq] using hcap
  light_store (dst+6) (localPrime h : ℕ) using hpval'
  light_store (dst+7) (localBucketCap h : ℕ) using hcap'
  light_set (localPrime h : ℕ) using hpval'
  refine ⟨rfl,?_,?_⟩
  · simpa [values,LightLocalCounts.values] using
      ((hseg₂.snoc (localPrime h : ℤ)).snoc (localBucketCap h : ℤ))
  · intro a ha
    change Function.update (Function.update μ₂ (dst+6) _) (dst+7) _ a = μ a
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact (hkept₂ a ha.1).trans (hkept₁ a ⟨ha.1,by omega⟩)

def program : Program :=
  [body 1 9 14,LightLocalCounts.body 2,LightSubsetSetup.body 3 7 8,
    LightPascal.buildBody 4 5,fillBody,LightPascal.rowBody 6,LightArray.linearBody,
    powTableBody,LightSubsetAddress.rankBody 8,
    LightSelectedPrime.body 10 11,sqrtBody,LightPrimePool.body 12,
    LightPrimality.body 13,emodBody,LightSmallDivide.body]

def procs : Procs program 0 :=
  ⟨1,9,14,⟨2,3,4,5,6,7,8,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,
    ⟨10,11,rfl,⟨12,⟨13,rfl,rfl⟩,rfl⟩,rfl⟩,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {h dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+5 ≤ lim.depth)
    (hout : dst+8 ≤ work) (hspace : space work h ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim program 0 d [h,dst,work] μ (time h)
      (fun r μ' => r = (localPrime h : ℤ) ∧ Seg μ' dst (values h) ∧
        KeptBut μ μ' work dst 8) := procs.meets hw hd hout hspace hword

end ThreeSum.LightLocalParameters
