import Submission.ThreeSum.TernaryWantedCanonicalPairs
namespace ThreeSum.TernaryWantedLittleEndian
open TernaryWantedRadix

def encode (digits : List ℕ) (R code scale : ℕ) : List ℕ → ℕ
  | [] => code
  | i::is => encode digits R (code+scale*digits.getD i 0) (scale*R) is

def wantedCodes (p : ℤ) (raws : List ℤ) (words maps : List ℕ) (j : ℕ)
    (x : ℤ) (R S code scale mapCode mapScale : ℕ) : List (ℕ × ℕ) :=
  (wantedOutputs p raws j x).map fun is =>
    (encode words R code scale is,encode maps S mapCode mapScale is)

@[simp] theorem wantedCodes_length (p : ℤ) (raws : List ℤ) (words maps : List ℕ) (j : ℕ)
    (x : ℤ) (R S code scale mapCode mapScale : ℕ) :
    (wantedCodes p raws words maps j x R S code scale mapCode mapScale).length=
      (wantedOutputs p raws j x).length := by simp [wantedCodes]

theorem wantedCodes_succ (p : ℤ) (raws : List ℤ) (words maps : List ℕ) (j : ℕ)
    (x : ℤ) (R S code scale mapCode mapScale : ℕ) :
    wantedCodes p raws words maps (j+1) x R S code scale mapCode mapScale =
      (localBucket p raws x).flatMap fun i => wantedCodes p raws words maps j
        ((x-raws.getD i 0)/p) R S (code+scale*words.getD i 0) (scale*R)
          (mapCode+mapScale*maps.getD i 0) (mapScale*S) := by
  simp [wantedCodes,wantedOutputs,List.map_flatMap,List.map_map,Function.comp_def,encode]

/-- The runtime accumulates least-native-position first. Canonical addresses
are high-first, so the corresponding word reverses block order, not digits. -/
theorem encode_reverse_address (L : ℕ) (localWords : ℕ → List ℕ) (digits : List ℕ)
    (hblocks : ∀ i, (localWords i).length=L)
    (hdigits : ∀ i, digits.getD i 0=TernaryAddresses.code (localWords i)) :
    ∀ (is : List ℕ) (code scale : ℕ),
      encode digits (4^L) code scale is = code+scale*
        TernaryAddresses.code (is.reverse.flatMap localWords) := by
  intro is
  induction is with
  | nil => intro code scale; simp [encode,TernaryAddresses.code]
  | cons i is ih =>
    intro code scale
    rw [encode,ih,List.reverse_cons,List.flatMap_append,List.flatMap_singleton,
      TernaryWantedCanonicalPairs.address_append,hblocks,hdigits]
    ring

theorem mem_wantedCodes {p : ℤ} (hp : p ≠ 0) (raws : List ℤ) (words maps : List ℕ)
    (j : ℕ) (x : ℤ) (R S code scale mapCode mapScale w f : ℕ) :
    (w,f) ∈ wantedCodes p raws words maps j x R S code scale mapCode mapScale ↔
      ∃ is : List ℕ, is.length=j ∧ (∀ i ∈ is, i<raws.length) ∧
        p^j ∣ x-Radix.positionalHash p (fun i => raws.getD i 0) is ∧
        encode words R code scale is=w ∧ encode maps S mapCode mapScale is=f := by
  simp only [wantedCodes,List.mem_map,Prod.mk.injEq,mem_wantedOutputs p hp raws]
  aesop

/-- Integer target hashes use least-significant block first; canonical words
use the corresponding reversed sequence of blocks, with each block unchanged. -/
theorem wanted_word_address {p : ℤ} (raws : List ℤ) (localWords : ℕ → List ℕ)
    (digits maps : List ℕ) (L J S : ℕ) (x : ℤ) (w f : ℕ)
    (hp : p ≠ 0) (hblocks : ∀ i, (localWords i).length=L)
    (hdigits : ∀ i, digits.getD i 0=TernaryAddresses.code (localWords i))
    (h : (w,f) ∈ wantedCodes p raws digits maps J x (4^L) S 0 1 0 1) :
    ∃ is : List ℕ, is.length=J ∧ (∀ i ∈ is, i<raws.length) ∧
      p^J ∣ x-Radix.positionalHash p (fun i => raws.getD i 0) is ∧
      w=TernaryAddresses.code (is.reverse.flatMap localWords) ∧
      f=encode maps S 0 1 is := by
  obtain ⟨is,hlen,hvalid,hdiv,hw,hf⟩ := (mem_wantedCodes hp raws digits maps J x (4^L) S 0 1 0 1 w f).mp h
  refine ⟨is,hlen,hvalid,hdiv,?_,hf.symm⟩
  rw [← hw,encode_reverse_address L localWords digits hblocks hdigits]
  simp

end ThreeSum.TernaryWantedLittleEndian
