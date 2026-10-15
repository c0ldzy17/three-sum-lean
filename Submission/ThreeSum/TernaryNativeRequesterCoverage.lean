import Submission.ThreeSum.TernaryNativePairAccess
import Submission.ThreeSum.LightTernaryRequesterMatrix

noncomputable section
namespace ThreeSum.TernaryNativeRequesterCoverage
open TernarySignedReduction TernarySignedDigits TernaryExtensionEncoding
set_option maxHeartbeats 2500000
variable {p : ℕ} [Fact p.Prime]

def field {J : ℕ} (v : Coordinate J→ℤ) : Coordinate J→ZMod p := fun k => (v k : ZMod p)

def sourceLeft {J r : ℕ} (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (U radix : ℕ) (b : ℤ) : Fin r→ZMod p := H (field (leftRaw U radix J b))
def sourceRight {J r : ℕ} (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (U radix : ℕ) (c : ℤ) : Fin r→ZMod p := H (field (rightRaw U radix J c))

def position (J t : ℕ) : ℕ := t/(2^J)
def target {J r : ℕ} (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (U radix : ℕ) (A : ℕ→ℤ) (t : ℕ) : ℤ :=
  (coefficientCode (H (field (requesterRaw U radix J (A (position J t))
    (TernaryCarryCode.carryFromCode J (t%(2^J)))))) : ℕ)

/-- Every original requester and every genuine signed difference is present
in the actual finite carry-code enumeration, with its original position. -/
theorem complete {J r U radix n i : ℕ}
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p)) (A : ℕ→ℤ) (b c : ℤ)
    (hi : i<n) (ha : |A i|≤(U : ℤ)) (hb : |b|≤(U : ℤ)) (hc : |c|≤(U : ℤ))
    (hcap : 4*U<radix^J) (hrel : c=A i+b) :
    ∃ t<n*2^J, position J t=i ∧ target H U radix A t=
      (coefficientCode (sourceLeft H U radix b+sourceRight H U radix c) : ℤ) := by
  classical
  obtain ⟨carry,hcarry,hraw⟩ := (original_difference_iff ha hb hc hcap).mp (by omega)
  have hv := (mem_carryCatalog carry).mp hcarry
  let q := TernaryCarryCode.codeOfCarry carry
  have hq : q<2^J := TernaryCarryCode.codeOfCarry_lt carry
  have hQ : 0<2^J := by positivity
  let t := i*2^J+q
  have ht : t<n*2^J := by dsimp [t]; nlinarith
  have hpos : position J t=i := by
    unfold position
    dsimp only [t]
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hQ,Nat.div_eq_of_lt hq,Nat.zero_add]
  have hmod : t%(2^J)=q := by simp [t,Nat.add_mod,Nat.mod_eq_of_lt hq]
  have hfield : field (p := p) (requesterRaw U radix J (A i) carry)=
      field (leftRaw U radix J b)+field (rightRaw U radix J c) := by
    funext k
    change (requesterRaw U radix J (A i) carry k : ZMod p)=
      (leftRaw U radix J b k : ZMod p)+(rightRaw U radix J c k : ZMod p)
    rw [← Int.cast_add,hraw k]
  refine ⟨t,ht,hpos,?_⟩
  unfold target
  rw [hpos,hmod,TernaryCarryCode.carryFromCode_code hv,hfield,map_add]
  rfl

theorem position_lt {J n t : ℕ} (ht : t<n*2^J) : position J t<n := by
  unfold position
  exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by simpa only [Nat.mul_comm] using ht)

end ThreeSum.TernaryNativeRequesterCoverage
