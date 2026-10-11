import Submission.ThreeSum.LightNormalize
import Submission.ThreeSum.LightBandPartition
import Submission.ThreeSum.LightBandEnumeration

/-!
# Normalizing one color class and constructing all its band endpoints

This closed eleven-procedure program joins the actual merge sort, adjacent
deduplication, quotient computation, and endpoint passes. It writes the
distinct-value length and band count in a two-cell header. The following
cells are the lower endpoints and, after the distinct-value length, the
upper endpoints. The membership witness still refers to the original class.
-/

namespace ThreeSum.LightSortedBands

open Light ThreeSum.BandPartition

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

variable {lim : Limits} {P : Program}

theorem getD_strict {L : List ℤ} (hs : L.Pairwise (· < ·)) :
    ∀ i j, i < j → j < L.length → L.getD i 0 < L.getD j 0 := by
  intro i j hij hj
  rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ hj]
  exact List.pairwise_iff_getElem.mp hs i j (by omega) hj hij

def Prepared (μ : ℕ → ℤ) (values endpoints g : ℕ) (original : List ℤ) : Prop :=
  ∃ L : List ℤ,
    Seg μ values L ∧ L.Pairwise (· < ·) ∧ L.length ≤ original.length ∧
    (∀ z, z ∈ L ↔ z ∈ original) ∧
    μ endpoints = (L.length : ℤ) ∧ μ (endpoints+1) = (size L.length g : ℤ) ∧
    (∀ i < size L.length g, μ (endpoints+2+i) = L.getD (start g i) 0) ∧
    (∀ i < size L.length g, μ (endpoints+2+L.length+i) = L.getD (stop L.length g i-1) 0)

/-- Arguments: class source and length, band size, values output, endpoint
header, merge scratch. -/
def body (pNormalize pPartition : ℕ) : Stmt :=
  .call pNormalize [v 0,v 1,v 3,v 5] 6 ;;
  .call pPartition [v 3,v 6,v 2,v 4 +' k 2] 7 ;;
  .store (v 4) (v 6) ;;
  .store (v 4 +' k 1) (v 7) ;;
  .set 0 (v 7)

def time (n : ℕ) : ℕ := LightNormalize.time n+200*n+300
def space (work n : ℕ) : ℕ := work+n

structure Procs (P : Program) (pMain : ℕ) where
  pNormalize : ℕ
  pPartition : ℕ
  pDivide : ℕ
  pLower : ℕ
  pUpper : ℕ
  normalize : LightNormalize.Procs P pNormalize
  partition : P[pPartition]? = some (LightBandPartition.body pDivide pLower pUpper)
  divide : P[pDivide]? = some LightSmallDivide.body
  lower : P[pLower]? = some LightBandPartition.lowerBody
  upper : P[pUpper]? = some LightBandPartition.upperBody
  main : P[pMain]? = some (body pNormalize pPartition)

theorem Procs.meets {pMain src values endpoints work g d : ℕ}
    {μ : ℕ → ℤ} {original : List ℤ} (R : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+original.length ≤ values) (hvalues : values+original.length ≤ endpoints)
    (hendpoints : endpoints+2+2*original.length ≤ work)
    (hspace : space work original.length ≤ lim.space)
    (hword : ((original.length+g+2 : ℕ) : ℤ) ≤ lim.word)
    (hd : d+original.length+Nat.clog 2 original.length+3 ≤ lim.depth)
    (hread : Seg μ src original) :
    Meets lim P pMain d [src,original.length,g,values,endpoints,work] μ (time original.length)
      (fun r μ' => r = μ' (endpoints+1) ∧ Prepared μ' values endpoints g original ∧
        ∀ a, a < work → (a < src ∨ src+original.length ≤ a) →
          (a < values ∨ values+original.length ≤ a) →
          (a < endpoints ∨ endpoints+2+2*original.length ≤ a) → μ' a = μ a) := by
  have h1 : (1 : ℤ) ≤ lim.word := by omega
  have hspace' : work+original.length ≤ lim.space := hspace
  apply Meets.of_body R.main
  unfold body time
  light_call (R.normalize.meets (d := d+1) (src := src) (dst := values) (work := work)
    hw h1 hread hsrc (by omega) hspace (by omega))
    using LightNormalize.time,sortTime,LightNormalize.dedupTime,space
    with len μ₁ ⟨L,hlen,hL,hstrict,hcount,hmem,hkept₁⟩
  have hLread : ∀ i < L.length, μ₁ (values+i) = L.getD i 0 := by
    intro i hi
    exact hL.getD hi 0
  have hpart := LightBandPartition.meets (d := d+1) (src := values) (dst := endpoints+2)
    R.partition R.divide R.lower R.upper μ₁ (fun i => L.getD i 0) hw hg
    (by omega) (by unfold space at hspace; omega)
    ((Int.ofNat_le.mpr (by omega : L.length+g+2 ≤ original.length+g+2)).trans hword)
    hLread (by omega)
  have hpartTime : LightBandPartition.time L.length g ≤ 200*original.length+200 :=
    (LightBandPartition.time_bound _ _).trans (by omega)
  light_call (hpart.mono_time hpartTime)
    using hlen,LightNormalize.time,sortTime,LightNormalize.dedupTime,space
    with bands μ₂ ⟨hbands,hlo,hhi,hkept₂⟩
  have hL₂ : Seg μ₂ values L := by
    intro i hi
    rw [hkept₂ (values+i) (Or.inl (by omega))]
    exact hL i hi
  light_store endpoints (L.length : ℕ)
    using hlen,LightNormalize.time,sortTime,LightNormalize.dedupTime,space
  light_store (endpoints+1) (size L.length g : ℕ)
    using hbands,LightNormalize.time,sortTime,LightNormalize.dedupTime,space
  light_set (size L.length g : ℕ)
    using hbands,LightNormalize.time,sortTime,LightNormalize.dedupTime,space
  refine ⟨by simp,⟨L,?_,hstrict,hcount,hmem,?_,?_,?_,?_⟩,?_⟩
  · intro i hi
    change Function.update (Function.update μ₂ endpoints (L.length : ℤ)) (endpoints+1)
      (size L.length g : ℤ) (values+i) = _
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hL₂ i hi
  · simp
  · simp
  · intro i hi
    change Function.update (Function.update μ₂ endpoints (L.length : ℤ)) (endpoints+1)
      (size L.length g : ℤ) (endpoints+2+i) = _
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hlo i hi
  · intro i hi
    change Function.update (Function.update μ₂ endpoints (L.length : ℤ)) (endpoints+1)
      (size L.length g : ℤ) (endpoints+2+L.length+i) = _
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hhi i hi
  · intro a ha hsrc hvalues hendpoints
    change Function.update (Function.update μ₂ endpoints (L.length : ℤ)) (endpoints+1)
      (size L.length g : ℤ) a = _
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),hkept₂ a (by omega)]
    exact hkept₁ a ha hsrc hvalues

def program : Program :=
  [body 1 7,LightNormalize.body 2 6,sortBody 2 3 4 5,halfBody,mergeBody,copyBody,
    LightNormalize.dedupBody 6,LightBandPartition.body 8 9 10,
    LightSmallDivide.body,LightBandPartition.lowerBody,LightBandPartition.upperBody]

def program_procs : Procs program 0 where
  pNormalize := 1
  pPartition := 7
  pDivide := 8
  pLower := 9
  pUpper := 10
  normalize := ⟨2,3,4,5,6,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩
  partition := rfl
  divide := rfl
  lower := rfl
  upper := rfl
  main := rfl

theorem program_meets {src values endpoints work g d : ℕ}
    {μ : ℕ → ℤ} {original : List ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+original.length ≤ values) (hvalues : values+original.length ≤ endpoints)
    (hendpoints : endpoints+2+2*original.length ≤ work)
    (hspace : space work original.length ≤ lim.space)
    (hword : ((original.length+g+2 : ℕ) : ℤ) ≤ lim.word)
    (hd : d+original.length+Nat.clog 2 original.length+3 ≤ lim.depth)
    (hread : Seg μ src original) :
    Meets lim program 0 d [src,original.length,g,values,endpoints,work] μ (time original.length)
      (fun r μ' => r = μ' (endpoints+1) ∧ Prepared μ' values endpoints g original ∧
        ∀ a, a < work → (a < src ∨ src+original.length ≤ a) →
          (a < values ∨ values+original.length ≤ a) →
          (a < endpoints ∨ endpoints+2+2*original.length ≤ a) → μ' a = μ a) :=
  program_procs.meets hw hg hsrc hvalues hendpoints hspace hword hd hread

/-- The constructed endpoint arrays directly instantiate the exact family
interface of the owner-listing machine. -/
theorem Prepared.family {μ : ℕ → ℤ} {values endpoints g : ℕ} {original : List ℤ}
    (h : Prepared μ values endpoints g original) (hg : 0 < g) :
    ∃ (L : List ℤ) (hs : L.Pairwise (· < ·)),
      Seg μ values L ∧ L.length ≤ original.length ∧ (∀ z, z ∈ L ↔ z ∈ original) ∧
      μ endpoints = (L.length : ℤ) ∧
      μ (endpoints+1) = (BandPartition.family (fun i => L.getD i 0) L.length g hg
        (getD_strict hs)).size ∧
      LightBandEnumeration.At μ (endpoints+2) (endpoints+2+L.length)
        (BandPartition.family (fun i => L.getD i 0) L.length g hg (getD_strict hs)) := by
  obtain ⟨L,hL,hs,hn,hmem,hlen,hcount,hlo,hhi⟩ := h
  exact ⟨L,hs,hL,hn,hmem,hlen,hcount,hlo,hhi⟩

/-- Later stages may alter other memory, provided the value and endpoint
regions of this class are retained. -/
theorem Prepared.transfer {μ μ' : ℕ → ℤ} {values endpoints g : ℕ} {original : List ℤ}
    (h : Prepared μ values endpoints g original)
    (hk : ∀ a, (values ≤ a ∧ a < values+original.length) ∨
      (endpoints ≤ a ∧ a < endpoints+2+2*original.length) → μ' a = μ a) :
    Prepared μ' values endpoints g original := by
  obtain ⟨L,hL,hs,hn,hmem,hlen,hcount,hlo,hhi⟩ := h
  refine ⟨L,?_,hs,hn,hmem,?_,?_,?_,?_⟩
  · intro i hi
    rw [hk (values+i) (Or.inl (by omega))]
    exact hL i hi
  · rw [hk endpoints (Or.inr (by omega))]
    exact hlen
  · rw [hk (endpoints+1) (Or.inr (by omega))]
    exact hcount
  · intro i hi
    have hm := size_le L.length g
    rw [hk (endpoints+2+i) (Or.inr (by omega))]
    exact hlo i hi
  · intro i hi
    have hm := size_le L.length g
    rw [hk (endpoints+2+L.length+i) (Or.inr (by omega))]
    exact hhi i hi

theorem Prepared.keep {μ μ' : ℕ → ℤ} {values endpoints g bound : ℕ}
    {original : List ℤ} (h : Prepared μ values endpoints g original)
    (hk : Kept μ μ' bound) (hv : values+original.length ≤ bound)
    (he : endpoints+2+2*original.length ≤ bound) : Prepared μ' values endpoints g original := by
  apply h.transfer
  intro a ha
  exact hk a (by rcases ha with ha | ha <;> omega)

theorem family_bounded {L original : List ℤ} {g U : ℕ} (hg : 0 < g)
    (hs : L.Pairwise (· < ·)) (hmem : ∀ z, z ∈ L ↔ z ∈ original)
    (hU : ∀ z ∈ original, |z| ≤ (U : ℤ)) :
    LightBandEnumeration.Bounded
      (BandPartition.family (fun i => L.getD i 0) L.length g hg (getD_strict hs)) U := by
  have hget (i : ℕ) (hi : i < L.length) : |L.getD i 0| ≤ (U : ℤ) := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hU _ ((hmem _).mp (List.getElem_mem hi))
  intro i hi
  exact ⟨hget _ (start_lt hg hi),hget _ (stop_sub_one_lt hg hi)⟩

/-- Membership witnesses from the original class lie in an emitted band.
Thus deduplication does not lose an original-position witness. -/
theorem family_covers {L original : List ℤ} {g : ℕ} (hg : 0 < g)
    (hs : L.Pairwise (· < ·)) (hmem : ∀ z, z ∈ L ↔ z ∈ original)
    {z : ℤ} (hz : z ∈ original) :
    let A := BandPartition.family (fun i => L.getD i 0) L.length g hg (getD_strict hs)
    ∃ i < A.size, A.lower i ≤ z ∧ z ≤ A.upper i := by
  obtain ⟨i,hi,heq⟩ := List.mem_iff_getElem.mp ((hmem z).mpr hz)
  refine ⟨i/g,index_lt_size hi,?_⟩
  have hc := BandPartition.covers (fun i => L.getD i 0) L.length g hg (getD_strict hs) hi
  simpa only [List.getD_eq_getElem _ _ hi,heq] using hc

theorem time_bound (n : ℕ) : time n ≤ 700*(n+1)*(Nat.clog 2 n+1) := by
  have h := LightNormalize.time_bound n
  unfold time
  nlinarith [Nat.zero_le (n*Nat.clog 2 n)]

end ThreeSum.LightSortedBands
