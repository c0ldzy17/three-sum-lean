import Submission.ThreeSum.TernaryActualSeedEnumeration
import Submission.ThreeSum.TernaryArenaFamilyBudget
import Submission.ThreeSum.LightTernaryGlobalPreludeProof

noncomputable section
namespace ThreeSum.TernaryComputedExtensionMenu
open Polynomial TernaryExtensionEncoding LightExtensionBackendLayout
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]

abbrev modulus (p d c : ℕ) [Fact p.Prime] : (ZMod p)[X] := monicOfCode d c

theorem monic (d c : ℕ) : (modulus p d c).Monic := monicCandidate_monic _

@[simp] theorem degree (d c : ℕ) : (modulus p d c).natDegree=d := monicCandidate_degree _

/-- A proof-level finite enumeration of the particular field actually found
by the backend. It introduces no runtime table or advice. -/
instance fieldFintype (d c : ℕ) : Fintype (AdjoinRoot (modulus p d c)) :=
  Fintype.ofEquiv (Fin (modulus p d c).natDegree→ZMod p) (coefficients (monic (p:=p) d c)).symm.toEquiv

variable {d c : ℕ} [Fact (Irreducible (modulus p d c))]

def seeds : (AdjoinRoot (modulus p d c)×AdjoinRoot (modulus p d c))≃Fin ((p^d)*(p^d)) :=
  (TernaryActualSeedEnumeration.equiv (monic (p:=p) d c)).trans (finCongr (by rw [degree]))

@[simp] theorem seeds_val (pair : AdjoinRoot (modulus p d c)×AdjoinRoot (modulus p d c)) :
    (seeds pair).val=(TernaryActualSeedEnumeration.equiv (monic (p:=p) d c) pair).val := rfl

def functional (hd : 0<d) : AdjoinRoot (modulus p d c)→ₗ[ZMod p] ZMod p :=
  constantCoefficient (monic (p:=p) d c) (by simpa only [degree] using hd)

theorem functional_ne_zero (hd : 0<d) : (functional (p:=p) (c:=c) hd)≠0 :=
  constantCoefficient_ne_zero (monic (p:=p) d c) _

theorem field_card : Fintype.card (AdjoinRoot (modulus p d c))=p^d := by
  simpa only [Nat.card_eq_fintype_card,degree] using extension_card (monic (p:=p) d c)

/-- The literal q² menu read is the exact coefficient of the corresponding
proof-level field pair, including the physical digit-coordinate reversal. -/
theorem coefficient_read {base J : ℕ} (hd : 0<d) (μ : ℕ→ℤ)
    (H : LightTernaryGlobalPreludeProof.Menu μ base d p (p^d) J c)
    (ordinal : ℕ) (ho : ordinal<(p^d)*(p^d)) (k : ℕ) (hk : k<J+2) :
    μ (physical base d (p^d) J+ordinal*(J+2)+k)=
      ((TernaryOriginalRowMenu.seedRow (J+2) (functional (p:=p) (c:=c) hd)
        (TernaryArenaFamilyBudget.seedAt (seeds (p:=p) (d:=d) (c:=c)) ordinal)
        (digitOrder J ⟨k,hk⟩)).val : ℤ) := by
  let hf := monic (p:=p) d c
  let pair := TernaryArenaFamilyBudget.seedAt (seeds (p:=p) (d:=d) (c:=c)) ordinal
  have hp : (seeds (p:=p) (d:=d) (c:=c) pair).val=ordinal := by
    simp [pair,TernaryArenaFamilyBudget.seedAt,dif_pos ho]
  have he := TernaryActualSeedEnumeration.matrix_row hf
    (show 0<(modulus p d c).natDegree by simpa only [degree] using hd) J pair.1 pair.2 ⟨k,hk⟩
  have hi : (TernaryActualSeedEnumeration.equiv hf pair).val=ordinal := by
    simpa only [seeds_val,hf] using hp
  rw [H ordinal ho k hk]
  exact_mod_cast (by simpa only [degree,hi,functional,hf,pair,LightExtensionBackend.modulusMonic,LightExtensionBackendLayout.factor,Prod.eta] using he)

end ThreeSum.TernaryComputedExtensionMenu
