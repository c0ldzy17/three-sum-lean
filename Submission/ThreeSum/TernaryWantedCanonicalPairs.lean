import Submission.ThreeSum.TernaryWantedCanonical
import Submission.ThreeSum.TernaryAddresses

namespace ThreeSum.TernaryWantedCanonicalPairs
open TernaryWantedRadix

def wantedCodes (p : ℤ) (raws : List ℤ) (words maps : List ℕ) (j : ℕ)
    (x : ℤ) (code R mapCode S : ℕ) : List (ℕ × ℕ) :=
  (wantedOutputs p raws j x).map fun is =>
    (TernaryWantedCanonical.encode words R code is,TernaryWantedCanonical.encode maps S mapCode is)

@[simp] theorem wantedCodes_length (p : ℤ) (raws : List ℤ) (words maps : List ℕ) (j : ℕ)
    (x : ℤ) (code R mapCode S : ℕ) :
    (wantedCodes p raws words maps j x code R mapCode S).length=(wantedOutputs p raws j x).length := by
  simp [wantedCodes]

theorem wantedCodes_succ (p : ℤ) (raws : List ℤ) (words maps : List ℕ) (j : ℕ)
    (x : ℤ) (code R mapCode S : ℕ) :
    wantedCodes p raws words maps (j+1) x code R mapCode S =
      (localBucket p raws x).flatMap fun i =>
        wantedCodes p raws words maps j ((x-raws.getD i 0)/p)
          (code*R+words.getD i 0) R (mapCode*S+maps.getD i 0) S := by
  simp [wantedCodes,wantedOutputs,List.map_flatMap,List.map_map,Function.comp_def,TernaryWantedCanonical.encode]

/-- One output row per physical representation, even when its three fields coincide. -/
def rowCells (original : ℕ) (codes : List (ℕ × ℕ)) : List ℤ :=
  codes.flatMap fun code => [(original : ℤ),(code.1 : ℤ),(code.2 : ℤ)]

@[simp] theorem rowCells_length (original : ℕ) (codes : List (ℕ × ℕ)) :
    (rowCells original codes).length=3*codes.length := by
  induction codes with
  | nil => simp [rowCells]
  | cons code codes ih => simp only [rowCells,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *; omega

@[simp] theorem rowCells_append (original : ℕ) (as bs : List (ℕ × ℕ)) :
    rowCells original (as++bs)=rowCells original as++rowCells original bs := by
  exact List.flatMap_append ..

theorem mem_wantedCodes {p : ℤ} (hp : p ≠ 0) (raws : List ℤ) (words maps : List ℕ)
    (j : ℕ) (x : ℤ) (code R mapCode S : ℕ) (w f : ℕ) :
    (w,f) ∈ wantedCodes p raws words maps j x code R mapCode S ↔
      ∃ is : List ℕ, is.length=j ∧ (∀ i ∈ is, i<raws.length) ∧
        p^j ∣ x-Radix.positionalHash p (fun i => raws.getD i 0) is ∧
        TernaryWantedCanonical.encode words R code is=w ∧
        TernaryWantedCanonical.encode maps S mapCode is=f := by
  simp only [wantedCodes,List.mem_map,Prod.mk.injEq,mem_wantedOutputs p hp raws]
  aesop

/-- The canonical two-bit address concatenates actual local word blocks. -/
theorem address_append (as bs : List ℕ) :
    TernaryAddresses.code (as++bs)=
      TernaryAddresses.code as*4^bs.length+TernaryAddresses.code bs := by
  induction as with
  | nil => simp [TernaryAddresses.code]
  | cons a as ih =>
    simp only [List.cons_append,TernaryAddresses.code,List.length_append,ih,pow_add]
    ring

def blockWords (localWords : ℕ → List ℕ) (is : List ℕ) : List ℕ := is.flatMap localWords

theorem encode_append_address (L : ℕ) (localWords : ℕ → List ℕ) (digits : List ℕ)
    (hblocks : ∀ i, (localWords i).length=L)
    (hdigits : ∀ i, digits.getD i 0=TernaryAddresses.code (localWords i)) :
    ∀ (is : List ℕ) (preword : List ℕ),
      TernaryWantedCanonical.encode digits (4^L) (TernaryAddresses.code preword) is=
        TernaryAddresses.code (preword++blockWords localWords is) := by
  intro is
  induction is with
  | nil => intro preword; simp [TernaryWantedCanonical.encode,blockWords]
  | cons i is ih =>
    intro preword
    have hcode : TernaryAddresses.code preword*4^L+TernaryAddresses.code (localWords i) =
        TernaryAddresses.code (preword++localWords i) := by rw [address_append,hblocks]
    rw [TernaryWantedCanonical.encode,hdigits,hcode,ih]
    simp [blockWords,List.append_assoc]

end ThreeSum.TernaryWantedCanonicalPairs
