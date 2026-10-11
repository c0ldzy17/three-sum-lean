import Submission.ThreeSum.LightPairFlags
import Submission.ThreeSum.LightSupportMark

/-!
# Actual construction of one retained local-cover row

The program constructs all pair keys and trimming flags, clears the output
row, and marks exactly the keys with retained representations. Repeated
representations are handled by the support operation. Earlier matrix rows
and inputs below the scratch boundary are preserved.
-/

namespace ThreeSum.LightLocalCoverRow

open Light

def body (pPair pSupport : ℕ) : Stmt :=
  .call pPair [v 0,v 1,v 2,v 3,v 4,v 10,v 6,v 7,v 8,v 9] 11 ;;
  .call pSupport [v 10,v 10 +' v 6 *' v 6,v 5,v 6 *' v 6,v 8 *' v 8] 11

def time (L n p : ℕ) : ℕ :=
  LightPairFlags.time L n+LightSupportMark.time (n*n) (p*p)+100

structure Procs (P : Program) (pMain : ℕ) where
  pPair : ℕ
  pDivide : ℕ
  pDot : ℕ
  pTrim : ℕ
  pSupport : ℕ
  pFill : ℕ
  pair : P[pPair]? = some (LightPairFlags.body pDivide pDot pTrim)
  divide : P[pDivide]? = some LightSmallDivide.body
  dot : P[pDot]? = some LightBooleanDot.body
  trim : P[pTrim]? = some LightTrimTest.body
  support : P[pSupport]? = some (LightSupportMark.body pFill)
  fill : P[pFill]? = some fillBody
  main : P[pMain]? = some (body pPair pSupport)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap keys : ℕ}
    (bits : ℕ → ℕ → ℕ) (left right leftCount rightCount : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth) (hn : 0 < n) (hp : 0 < p)
    (hbits : bitPtr+n*L ≤ keys) (hleft : leftPtr+n ≤ keys) (hright : rightPtr+n ≤ keys)
    (hleftHist : leftHist+p ≤ keys) (hrightHist : rightHist+p ≤ keys)
    (hdst : dst+p*p ≤ keys) (hspace : keys+2*(n*n) ≤ lim.space)
    (hword : (LightPairFlags.word L n p cap : ℤ) ≤ lim.word)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hleftRead : ∀ i < n, μ (leftPtr+i) = (left i : ℤ))
    (hrightRead : ∀ i < n, μ (rightPtr+i) = (right i : ℤ))
    (hleftLt : ∀ i < n, left i < p) (hrightLt : ∀ i < n, right i < p)
    (hleftCount : ∀ r < p, μ (leftHist+r) = (leftCount r : ℤ))
    (hrightCount : ∀ r < p, μ (rightHist+r) = (rightCount r : ℤ))
    (hleftBound : ∀ r < p, leftCount r ≤ n) (hrightBound : ∀ r < p, rightCount r ≤ n) :
    Meets lim P pMain d [bitPtr,leftPtr,rightPtr,leftHist,rightHist,dst,n,L,p,cap,keys] μ (time L n p)
      (fun _ μ' =>
        (∀ r < p*p, μ' (dst+r) =
          (LightSupportMark.bit (LightPairFlags.pairKey n p left right)
            (LightPairFlags.pairFlag L n cap bits left right leftCount rightCount) r (n*n) : ℤ)) ∧
        KeptBut μ μ' keys dst (p*p)) := by
  have hbudget (x : ℕ) (hx : x ≤ LightPairFlags.word L n p cap) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hnWord := hbudget n (by unfold LightPairFlags.word; omega)
  have hpWord := hbudget p (by unfold LightPairFlags.word; omega)
  have hLWord := hbudget L (by unfold LightPairFlags.word; omega)
  have hcapWord := hbudget cap (by unfold LightPairFlags.word; omega)
  have heWord := hbudget (n*n) (by unfold LightPairFlags.word; omega)
  have htWord := hbudget (p*p) (by unfold LightPairFlags.word; omega)
  have h1Word := hbudget 1 (by unfold LightPairFlags.word; omega)
  have heWordZ : (n : ℤ)*n ≤ lim.word := by exact_mod_cast heWord
  have htWordZ : (p : ℤ)*p ≤ lim.word := by exact_mod_cast htWord
  apply Meets.of_body S.main
  unfold body time
  have hpair := LightPairFlags.meets (d := d+1) (μ := μ) (bitPtr := bitPtr)
    (leftPtr := leftPtr) (rightPtr := rightPtr) (leftHist := leftHist) (rightHist := rightHist)
    (dst := keys) (n := n) (L := L) (p := p) (cap := cap)
    S.pair S.divide S.dot S.trim bits left right leftCount rightCount
    hw (by omega) hn hp hbits hleft hright hleftHist hrightHist hspace hword
    hbitsRead hbitsValue hleftRead hrightRead hleftLt hrightLt hleftCount hrightCount hleftBound hrightBound
  light_call hpair using LightPairFlags.time,LightPairFlags.roundTime,LightBooleanDot.time,
    LightTrimTest.time,LightSupportMark.time,LightSupportMark.markTime
    with value₀ μ₁ ⟨hkeys,hflags,hkept₀⟩
  have hkeyLt : ∀ i < n*n, LightPairFlags.pairKey n p left right i < p*p := by
    intro i hi
    have hq : i/n < n := (Nat.div_lt_iff_lt_mul hn).mpr hi
    have hr := Nat.mod_lt i hn
    have hl := hleftLt _ hq
    have hh := hrightLt _ hr
    unfold LightPairFlags.pairKey
    nlinarith
  have hs := LightSupportMark.meets (d := d+1) (μ := μ₁)
    (keys := keys) (flags := keys+n*n) (dst := dst) (n := n*n) (p := p*p)
    S.support S.fill (LightPairFlags.pairKey n p left right)
    (LightPairFlags.pairFlag L n cap bits left right leftCount rightCount)
    hw (by omega) (by omega) (by omega) (by omega) (Or.inr hdst) (Or.inr (by omega))
    hkeys hflags hkeyLt h1Word
  light_call hs using LightPairFlags.time,LightPairFlags.roundTime,LightBooleanDot.time,
    LightTrimTest.time,LightSupportMark.time,LightSupportMark.markTime
    with value₁ μ₂ ⟨hrow,hkept₁⟩
  refine ⟨hrow,?_⟩
  intro a ⟨ha,hout⟩
  change μ₂ a = μ a
  rw [hkept₁ a hout]
  exact hkept₀ a (Or.inl ha)

def program : Program :=
  [body 1 5,LightPairFlags.body 2 3 4,LightSmallDivide.body,LightBooleanDot.body,
    LightTrimTest.body,LightSupportMark.body 6,fillBody]

def programProcs : Procs program 0 := ⟨1,2,3,4,5,6,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem time_bound (L n p : ℕ) : time L n p ≤ 600*(n*n+1)*(L+n+p*p+1) := by
  have ht := LightPairFlags.time_bound L n
  unfold time LightSupportMark.time LightSupportMark.markTime fillTime
  nlinarith

end ThreeSum.LightLocalCoverRow
