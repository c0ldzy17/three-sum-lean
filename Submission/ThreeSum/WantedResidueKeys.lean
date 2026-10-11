import Submission.ThreeSum.WantedPairs
import Submission.ThreeSum.LightSourceResidues

/-!
# The actual residue scans and the selected wanted mass

The two-remainder source scanner specializes to an ordinary shifted residue
when its moduli agree. Its actual fiber count is exactly the incidence mass
minimized by the original signed-array offset program.
-/

namespace ThreeSum.WantedResidueKeys

open Light
open scoped BigOperators

def code (M : ℕ) (shift x : ℤ) : ℕ := LightSourceResidues.key M M shift x

theorem code_eq_residue (M : ℕ) (shift x : ℤ) :
    code M shift x=LightResidues.residue M 1 (x+shift) := by
  simp only [code,LightSourceResidues.key,LightResidues.residue,one_mul]
  congr 1
  rw [Int.add_emod,Int.emod_emod,← Int.add_emod]

theorem code_lt {M : ℕ} (hM : 0 < M) (shift x : ℤ) : code M shift x < M :=
  LightSourceResidues.key_lt hM shift x

theorem code_eq_iff {M : ℕ} (hM : 0 < M) (a b shift : ℤ) :
    code M 0 b=code M shift a ↔ (M : ℤ) ∣ a+shift-b := by
  rw [code_eq_residue,code_eq_residue,add_zero]
  exact WantedPairs.residue_eq_iff hM a b shift

def total (M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) : ℕ :=
  WantedPairs.count (fun i => code M shift (left i)) (fun j => code M 0 (right j)) NR NL

theorem total_eq_pairMass (M : ℕ) (hM : 0 < M) (left right : ℕ → ℤ)
    (NL NR : ℕ) (shift : ℤ) :
    total M left right NL NR shift =
      Histograms.pairMass (Finset.range NL) (Finset.range NR)
        (fun i => (left i : ZMod M)) (fun j => (right j : ZMod M))
        (fun _ => 1) (fun _ => 1) (shift : ZMod M) := by
  unfold total WantedPairs.count LightHistogram.count Histograms.pairMass
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,one_mul,
    code_eq_iff hM,GlobalKeyOffset.residue_relation_iff]

theorem selected_total_bound (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR : ℕ) :
    M*total M left right NL NR (LightOriginalOffset.selected M left right NL NR) ≤ NL*NR := by
  rw [total_eq_pairMass M (Nat.pos_of_ne_zero (NeZero.ne M))]
  simpa only [Int.cast_natCast] using LightOriginalOffset.selected_pairMass_bound M left right NL NR

theorem selected_congr {M NL NR : ℕ} [NeZero M] {left left' right right' : ℕ → ℤ}
    (hleft : ∀ i < NL, left i=left' i) (hright : ∀ i < NR, right i=right' i) :
    LightOriginalOffset.selected M left right NL NR=
      LightOriginalOffset.selected M left' right' NL NR := by
  unfold LightOriginalOffset.selected
  rw [ModuloCounts.signedHistogram_congr (p := M) (c := 1) hleft,
    ModuloCounts.signedHistogram_congr (p := M) (c := 1) hright]

theorem total_raw_global (M : ℕ) (P : ℤ) (xs : List ℤ) (h J : ℕ) (shift : ℤ) :
    total M (fun i => (RawAKeyLists.keys P xs).getD i 0)
      (fun j => (GlobalKeyEnumeration.globalKeys h J).getD j 0)
      (RawAKeyLists.keys P xs).length (GlobalKeyEnumeration.globalKeys h J).length shift =
    WantedPairs.count
      (fun i => LightResidues.residue M 1 ((RawAKeyLists.keys P xs).getD i 0+shift))
      (fun j => LightResidues.residue M 1 ((GlobalKeyEnumeration.globalKeys h J).getD j 0))
      (GlobalKeyEnumeration.globalKeys h J).length (RawAKeyLists.keys P xs).length := by
  simp only [total,code_eq_residue,add_zero]

end ThreeSum.WantedResidueKeys
