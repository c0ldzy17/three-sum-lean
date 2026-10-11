import Submission.ThreeSum.LightBandPreprocessing

/-!
# Finite bounds and original-value witness coverage for band preprocessing

These corollaries refer to the memory written by the closed twenty-procedure
program. An exact equation between members of the three original classes
produces a positive owner-table cell and three bands containing the values.
-/

namespace ThreeSum.LightBandPreprocessing

open Light ThreeSum.BandPartition

def storedCount (μ : ℕ → ℤ) (header : ℕ) : ℕ := (μ (header+1)).toNat

def InBand (μ : ℕ → ℤ) (header i : ℕ) (z : ℤ) : Prop :=
  μ (header+2+i) ≤ z ∧ z ≤ μ (header+2+(μ header).toNat+i)

/-- An in-range candidate found in one of the actual owner tables. -/
def Candidate (μ : ℕ → ℤ) (ae be ce dst i j k : ℕ) : Prop :=
  i < storedCount μ ae ∧ j < storedCount μ be ∧ k < storedCount μ ce ∧
    (μ (dst+j*storedCount μ ce+k) = (i+1 : ℕ) ∨
      μ (dst+storedCount μ be*storedCount μ ce+i*storedCount μ be+j) = (k+1 : ℕ) ∨
      μ (dst+storedCount μ be*storedCount μ ce+storedCount μ ae*storedCount μ be+
        i*storedCount μ ce+k) = (j+1 : ℕ))

theorem Represents.storedCount_eq {μ : ℕ → ℤ} {values endpoints g : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (h : Represents μ values endpoints g hg original L hs) :
    storedCount μ endpoints = size L.length g := by
  obtain ⟨_,_,_,_,hc,_⟩ := h
  simp only [storedCount,hc,Int.toNat_natCast]
  rfl

theorem Represents.inBand_iff {μ : ℕ → ℤ} {values endpoints g i : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)} {z : ℤ}
    (h : Represents μ values endpoints g hg original L hs) (hi : i < size L.length g) :
    InBand μ endpoints i z ↔
      L.getD (start g i) 0 ≤ z ∧ z ≤ L.getD (stop L.length g i-1) 0 := by
  obtain ⟨_,_,_,hlen,_,hlo,hhi⟩ := h
  simp only [InBand,hlen,Int.toNat_natCast,hlo i hi,hhi i hi]
  rfl

/-- Every original three-set equation reaches a positive stored candidate.
The conclusion includes the actual memory interval containing each value. -/
theorem Output.covers {μ : ℕ → ℤ} {av ae bv be cv ce dst g : ℕ} {hg : 0 < g}
    {originalA originalB originalC : List ℤ} {r x y z : ℤ}
    (h : Output μ av ae bv be cv ce dst g hg originalA originalB originalC r)
    (hx : x ∈ originalA) (hy : y ∈ originalB) (hz : z ∈ originalC) (heq : x+y=z) :
    ∃ i j k, InBand μ ae i x ∧ InBand μ be j y ∧ InBand μ ce k z ∧
      Candidate μ ae be ce dst i j k := by
  obtain ⟨A,hsA,B,hsB,C,hsC,_,hA,hB,hC,ht⟩ := h
  let aFamily := family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA)
  let bFamily := family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB)
  let cFamily := family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)
  obtain ⟨i,hi,hix,hxi⟩ := LightSortedBands.family_covers hg hsA hA.2.2.1 hx
  obtain ⟨j,hj,hjy,hyj⟩ := LightSortedBands.family_covers hg hsB hB.2.2.1 hy
  obtain ⟨k,hk,hkz,hzk⟩ := LightSortedBands.family_covers hg hsC hC.2.2.1 hz
  change aFamily.lower i ≤ x at hix
  change x ≤ aFamily.upper i at hxi
  change bFamily.lower j ≤ y at hjy
  change y ≤ bFamily.upper j at hyj
  change cFamily.lower k ≤ z at hkz
  change z ≤ cFamily.upper k at hzk
  have hr : BandEnumeration.relevant aFamily bFamily cFamily (⟨i,hi⟩,⟨j,hj⟩,⟨k,hk⟩) := by
    change aFamily.lower i ≤ cFamily.upper k-bFamily.lower j ∧
      cFamily.lower k-bFamily.upper j ≤ aFamily.upper i
    exact ⟨by omega,by omega⟩
  have hcand := ht.covers (⟨i,hi⟩ : aFamily.Index) (⟨j,hj⟩ : bFamily.Index) (⟨k,hk⟩ : cFamily.Index) hr
  refine ⟨i,j,k,(hA.inBand_iff hi).mpr ⟨hix,hxi⟩,
    (hB.inBand_iff hj).mpr ⟨hjy,hyj⟩,(hC.inBand_iff hk).mpr ⟨hkz,hzk⟩,?_⟩
  unfold Candidate
  rw [hA.storedCount_eq,hB.storedCount_eq,hC.storedCount_eq]
  exact ⟨hi,hj,hk,hcand⟩

theorem Output.count_bound {μ : ℕ → ℤ} {av ae bv be cv ce dst g : ℕ} {hg : 0 < g}
    {originalA originalB originalC : List ℤ} {r : ℤ}
    (h : Output μ av ae bv be cv ce dst g hg originalA originalB originalC r) :
    0 ≤ r ∧ r ≤ (LightBandEnumeration.count (size originalA.length g)
      (size originalB.length g) (size originalC.length g) : ℤ) := by
  obtain ⟨A,hsA,B,hsB,C,hsC,hr,hA,hB,hC,_⟩ := h
  rw [hr]
  exact ⟨Int.natCast_nonneg _,Int.ofNat_le.mpr
    (LightBandEnumeration.count_mono (size_mono hA.2.1) (size_mono hB.2.1) (size_mono hC.2.1))⟩

theorem time_bound (a b c g : ℕ) :
    time a b c g ≤
      2100*(a+b+c+1)*(Nat.clog 2 (a+b+c)+1)+
      1000*(LightBandEnumeration.count (size a g) (size b g) (size c g)+a+b+c+1)*
        (LightBandEnumeration.width (size a g) (size b g) (size c g)+1)+400 := by
  have hn (n : ℕ) (hn : n ≤ a+b+c) :
      LightSortedBands.time n ≤ 700*(a+b+c+1)*(Nat.clog 2 (a+b+c)+1) := by
    apply (LightSortedBands.time_bound n).trans
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 700 (by omega))
      (Nat.add_le_add_right (Nat.clog_mono_right 2 hn) 1)
  have ha := hn a (by omega)
  have hb := hn b (by omega)
  have hc := hn c (by omega)
  have henum := LightBandEnumeration.time_bound (size a g) (size b g) (size c g)
  have henum' : LightBandEnumeration.time (size a g) (size b g) (size c g) ≤
      1000*(LightBandEnumeration.count (size a g) (size b g) (size c g)+a+b+c+1)*
        (LightBandEnumeration.width (size a g) (size b g) (size c g)+1) := by
    apply henum.trans
    have hsum : size a g+size b g+size c g ≤ a+b+c :=
      Nat.add_le_add (Nat.add_le_add (size_le a g) (size_le b g)) (size_le c g)
    apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_left
    omega
  unfold time LightHeaderBands.time
  nlinarith

theorem count_square_bound (a b c g : ℕ) :
    LightBandEnumeration.count (size a g) (size b g) (size c g) ≤
      3*(size (a+b+c) g)^2 := by
  have h := LightBandEnumeration.count_mono (size_mono (g := g) (show a ≤ a+b+c by omega))
    (size_mono (g := g) (show b ≤ a+b+c by omega)) (size_mono (g := g) (show c ≤ a+b+c by omega))
  convert h using 1 <;> unfold LightBandEnumeration.count <;> ring

theorem program_length : program.length = 20 := by decide

end ThreeSum.LightBandPreprocessing
