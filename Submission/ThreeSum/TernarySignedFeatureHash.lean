import Submission.ThreeSum.TernaryOriginalKeyCodes
import Submission.ThreeSum.TernaryNativeRequesterCoverage
import Submission.ThreeSum.TernarySignedModes

noncomputable section
namespace ThreeSum.TernarySignedFeatureHash
open TernarySignedReduction TernarySignedLayout TernaryNativeRequesterCoverage
variable {p J r : ℕ} [Fact p.Prime]

def unfeature (J : ℕ) : (Fin (J+2)→ZMod p)→ₗ[ZMod p] (Coordinate J→ZMod p) where
  toFun v := Sum.elim (fun j => v ⟨j.val,by omega⟩)
    (fun t => if t then v ⟨J+1,by omega⟩ else v ⟨J,by omega⟩)
  map_add' v w := by funext k; cases k with
    | inl j => rfl
    | inr t => cases t <;> rfl
  map_smul' c v := by funext k; cases k with
    | inl j => rfl
    | inr t => cases t <;> rfl

theorem unfeature_cast (raw : Coordinate J→ℤ) :
    unfeature J (fun i => (feature raw i.val : ZMod p))=field raw := by
  funext k
  cases k with
  | inl j => simp [unfeature,feature,field,j.isLt]
  | inr t => cases t <;> simp [unfeature,feature,field]

def hash (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p)) :
    (Fin (J+2)→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p) := H.comp (unfeature J)

theorem hash_raw (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (raw : Coordinate J→ℤ) :
    hash H (fun i => (feature raw i.val : ZMod p))=H (field raw) := by
  exact congrArg H (unfeature_cast raw)

theorem left_hash (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p)) (U radix : ℕ) (b : ℤ) :
    hash H (fun i => (feature (leftRaw U radix J b) i.val : ZMod p))=sourceLeft H U radix b :=
  hash_raw H _
theorem right_hash (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p)) (U radix : ℕ) (c : ℤ) :
    hash H (fun i => (feature (rightRaw U radix J c) i.val : ZMod p))=sourceRight H U radix c :=
  hash_raw H _

theorem left_tags (U radix J : ℕ) (b : ℤ) :
    feature (leftRaw U radix J b) J=1 ∧ feature (leftRaw U radix J b) (J+1)=0 := by
  simp [feature,leftRaw]
theorem right_tags (U radix J : ℕ) (c : ℤ) :
    feature (rightRaw U radix J c) J=0 ∧ feature (rightRaw U radix J c) (J+1)=1 := by
  simp [feature,rightRaw]

theorem physical_sound {U radix : ℕ} {b c b' c' : ℤ}
    (hb : 1<radix) (hp : 2*radix<p)
    (hB : |b|≤(U : ℤ)) (hC : |c|≤(U : ℤ)) (hB' : |b'|≤(U : ℤ)) (hC' : |c'|≤(U : ℤ))
    (hcap : 4*U<radix^J)
    (he : (fun i : Fin (J+2) => (feature (leftRaw U radix J b) i.val : ZMod p))+
      (fun i => (feature (rightRaw U radix J c) i.val : ZMod p))=
      (fun i : Fin (J+2) => (feature (leftRaw U radix J b') i.val : ZMod p))+
      (fun i => (feature (rightRaw U radix J c') i.val : ZMod p))) : c-b=c'-b' := by
  apply TernarySignedModes.fieldMode_physical_sound hb hp hB hC hB' hC' hcap
  have hh := congrArg (unfeature (p := p) J) he
  rw [map_add,map_add,unfeature_cast,unfeature_cast,unfeature_cast,unfeature_cast] at hh
  intro k
  simpa only [field,TernarySignedModes.fieldMode,TernarySignedModes.rawMode,
    Int.cast_add,Pi.add_apply] using congrFun hh k

/-- Distinct original integers remain distinct full signed feature vectors
before the row menu is applied. -/
theorem left_injective {U radix n : ℕ} (B : Fin n→ℤ)
    (hb : 1<radix) (hp : 2*radix<p) (hcap : 4*U<radix^J)
    (hB : ∀ i, |B i|≤(U : ℤ)) (hinj : Function.Injective B) :
    Function.Injective (fun i : Fin n => fun t : Fin (J+2) =>
      (feature (leftRaw U radix J (B i)) t.val : ZMod p)) := by
  intro i j he
  apply hinj
  have hh := physical_sound hb hp (hB i) (show |(0 : ℤ)|≤(U : ℤ) by simp)
    (hB j) (show |(0 : ℤ)|≤(U : ℤ) by simp) hcap
    (congrArg (fun v : Fin (J+2)→ZMod p => v+
      (fun t => (feature (rightRaw U radix J 0) t.val : ZMod p))) he)
  simpa only [zero_sub,neg_inj] using hh

theorem right_injective {U radix n : ℕ} (C : Fin n→ℤ)
    (hb : 1<radix) (hp : 2*radix<p) (hcap : 4*U<radix^J)
    (hC : ∀ i, |C i|≤(U : ℤ)) (hinj : Function.Injective C) :
    Function.Injective (fun i : Fin n => fun t : Fin (J+2) =>
      (feature (rightRaw U radix J (C i)) t.val : ZMod p)) := by
  intro i j he
  apply hinj
  have hh := physical_sound hb hp (show |(0 : ℤ)|≤(U : ℤ) by simp) (hC i)
    (show |(0 : ℤ)|≤(U : ℤ) by simp) (hC j) hcap
    (congrArg (fun v : Fin (J+2)→ZMod p =>
      (fun t => (feature (leftRaw U radix J 0) t.val : ZMod p))+v) he)
  simpa only [sub_zero] using hh

end ThreeSum.TernarySignedFeatureHash
