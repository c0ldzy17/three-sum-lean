import Submission.ThreeSum.EncodedColorPrimeReadyData
import Submission.ThreeSum.LightEncodedColorWantedSources
import Submission.ThreeSum.LightEncodedColorResult

/-! # One retained selected-color payload, from original input to shared sources -/

namespace ThreeSum.EncodedColorPipelineData

open Light Scales BandScales ColorClassLists EncodedColorNormalizedData

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩

def coverBase (free n : ℕ) : ℕ :=
  EncodedColorLayout.cover free n (bandSize n) (radix n) (primeWindow n)

def wantedHeader (free n len : ℕ) : ℕ :=
  LightGuardedWanted.wantedFree (coverBase free n) (microHalf (inputBits n)) (blockCount (inputBits n)) len

def controls (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  LightEncodedColorFiniteSources.base (coverBase free n) n
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (radix n) (incidences n A B C hsA hsB hsC)

def bankHeader (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase (controls free n A B C hsA hsB hsC))
    B.length C.length (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n))

def finish (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  LightSourceControlsHost.finish (controls free n A B C hsA hsB hsC) B.length C.length (bandSize n)
    (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n)

def values (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : List ℤ :=
  LightEncodedColorResult.values (EncodedColorLayout.prime free n (bandSize n)) (coverBase free n)
    (wantedHeader free n (incidences n A B C hsA hsB hsC).length) (controls free n A B C hsA hsB hsC)
    (bankHeader free n A B C hsA hsB hsC) (finish free n A B C hsA hsB hsC)
    (incidences n A B C hsA hsB hsC).length (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)

structure Stored (μ : ℕ → ℤ) (free n : ℕ) (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ)
    (A B C : List ℤ) (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : Prop where
  heads : Seg μ (finish free n A B C hsA hsB hsC) (values free n A B C hsA hsB hsC)
  normalizedHeads : Seg μ free (EncodedColorLayout.normalizedHeads free n (bandSize n))
  countCell : μ (EncodedColorLayout.normalizedEnd free n (bandSize n))=
    ((incidences n A B C hsA hsB hsC).length : ℤ)
  normalized : SourceFiniteData.Normalized μ
    (EncodedColorLayout.av free n) (EncodedColorLayout.ae free n)
    (EncodedColorLayout.bv free n) (EncodedColorLayout.be free n)
    (EncodedColorLayout.cv free n) (EncodedColorLayout.ce free n)
    (EncodedColorLayout.tables free n) (EncodedColorLayout.rec free n (bandSize n))
    (EncodedColorLayout.vals free n (bandSize n)) (bandSize n) (bandSize_pos n)
    (classList color x 0 1) (classList color x 1 1) (classList color x 2 (-1))
    A B C hsA hsB hsC ((incidences n A B C hsA hsB hsC).length : ℤ)
  primes : EncodedColorPrimeData.Stored μ (EncodedColorLayout.prime free n (bandSize n))
    (radix n) (primeWindow n) (EncodedColorPrimeReadyData.moduli n A B C hsA hsB hsC)
  cover : LightCoverKeyData.Stored μ (coverBase free n) (microHalf (inputBits n)) (blockCount (inputBits n))
  wanted : LightWantedSetup.Output μ (wantedHeader free n (incidences n A B C hsA hsB hsC).length) (radix n)
    (LightGuardedWanted.left (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (incidences n A B C hsA hsB hsC))
    (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
    (3*(incidences n A B C hsA hsB hsC).length)
    (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
    (RawAKeyLists.selected (radix n) (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
      (incidences n A B C hsA hsB hsC) (microHalf (inputBits n)) (blockCount (inputBits n)))
  sources : SourceFiniteData.Stored μ (controls free n A B C hsA hsB hsC) (bandSize n)
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) B C
    (RawAKeyLists.selected (radix n) (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
      (incidences n A B C hsA hsB hsC) (microHalf (inputBits n)) (blockCount (inputBits n)) : ℤ)
    (finish free n A B C hsA hsB hsC : ℤ)
  countBound : radix n*(μ (wantedHeader free n (incidences n A B C hsA hsB hsC).length)).toNat ≤
    3*(incidences n A B C hsA hsB hsC).length*
      LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n))
  lifts : Seg μ (LightCoverKeyData.keyEnd (coverBase free n) (microHalf (inputBits n)) (blockCount (inputBits n)))
    (RawAKeyLists.keys (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (incidences n A B C hsA hsB hsC))

def Output (μ : ℕ → ℤ) (free n : ℕ) (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ) (r : ℤ) : Prop :=
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·)) (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
    r=(finish free n A B C hsA hsB hsC : ℤ) ∧ Stored μ free n color x A B C hsA hsB hsC

theorem ordered (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    EncodedColorLayout.prime free n (bandSize n)+6 ≤ coverBase free n ∧
    free+8 ≤ coverBase free n ∧ coverBase free n ≤ controls free n A B C hsA hsB hsC ∧
    wantedHeader free n (incidences n A B C hsA hsB hsC).length+4 ≤ controls free n A B C hsA hsB hsC ∧
    controls free n A B C hsA hsB hsC+3 ≤ finish free n A B C hsA hsB hsC ∧
    bankHeader free n A B C hsA hsB hsC+5 ≤ finish free n A B C hsA hsB hsC := by
  have hp := EncodedColorLayout.prime_le_cover free n (bandSize n) (radix n) (primeWindow n)
  have hf := EncodedColorLayout.free_le_prime free n (bandSize n)
  have hc := LightEncodedColorFiniteSources.free_le_base (coverBase free n) n
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (radix n) (incidences n A B C hsA hsB hsC)
  have hw := EncodedColorWantedData.header_le_nextFree
    (wantedHeader free n (incidences n A B C hsA hsB hsC).length) (radix n)
    (LightGuardedWanted.left (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (incidences n A B C hsA hsB hsC))
    (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
    (3*(incidences n A B C hsA hsB hsC).length)
    (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
    (RawAKeyLists.selected (radix n) (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
      (incidences n A B C hsA hsB hsC) (microHalf (inputBits n)) (blockCount (inputBits n)) : ℤ)
  have hs := SourceFiniteData.source_ends (controls free n A B C hsA hsB hsC) B.length C.length
    (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n)
  change _ ≤ coverBase free n at hp
  change _ ≤ controls free n A B C hsA hsB hsC at hc hw
  change controls free n A B C hsA hsB hsC+3 ≤ finish free n A B C hsA hsB hsC ∧ _ ∧
    bankHeader free n A B C hsA hsB hsC+5 ≤ finish free n A B C hsA hsB hsC at hs
  exact ⟨hp,by omega,hc,hw,hs.1,hs.2.2⟩

end ThreeSum.EncodedColorPipelineData
