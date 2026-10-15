import Submission.ThreeSum.TernaryArenaSelectedTerminal
import Submission.ThreeSum.TernarySignedFeatureHash
import Submission.ThreeSum.TernaryArenaNativeComplete

noncomputable section
namespace ThreeSum.TernaryArenaSelectedSigned
open TernarySignedReduction TernarySignedLayout TernaryNativeRequesterCoverage
open TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryArenaSelectedBudgets
open TernaryArenaSelectedTerminal TernaryArenaBudgetExistence TernaryCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]

def featureMap (J : ℕ) : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin (J+2)→ZMod p) where
  toFun v i := if h : i.val<J then v (.inl ⟨i.val,h⟩) else if i.val=J then v (.inr false) else v (.inr true)
  map_add' v w := by funext i; dsimp; split_ifs <;> rfl
  map_smul' c v := by funext i; dsimp; split_ifs <;> rfl

theorem featureMap_raw {J : ℕ} (raw : Coordinate J→ℤ) :
    featureMap J (field raw)=(fun i => (feature raw i.val : ZMod p)) := by
  funext i
  unfold featureMap field feature
  dsimp
  split_ifs <;> rfl

def selectedHash (A : Inputs) (s : State (p := p) A) (r : ℕ) :
    (Coordinate A.J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p) :=
  (hashMap A s r).comp (featureMap A.J)

theorem selectedHash_raw (A : Inputs) (s : State (p := p) A) (r : ℕ) (raw : Coordinate A.J→ℤ) :
    selectedHash A s r (field raw)=hashMap A s r (fun i => (feature raw i.val : ZMod p)) := by
  exact congrArg (hashMap A s r) (featureMap_raw raw)

def left (U radix J : ℕ) (B : ℕ→ℤ) (j i : ℕ) : ℤ := feature (leftRaw U radix J (B j)) i
def right (U radix J : ℕ) (C : ℕ→ℤ) (j i : ℕ) : ℤ := feature (rightRaw U radix J (C j)) i
def requester (U radix J : ℕ) (A : ℕ→ℤ) (t i : ℕ) : ℤ :=
  feature (requesterRaw U radix J (A (position J t)) (TernaryCarryCode.carryFromCode J (t%(2^J)))) i

def base (I : Input) (J nA : ℕ) : Input :=
  {I with positions:=position J, requesterCount:=nA*2^J}

/-- Both the requester/carry occurrence count and its provenance match the
literal actual native-completeness input, including all repeated targets. -/
theorem input_eq (I : Input) (A : Inputs) (s : State (p := p) A) (r U radix nA : ℕ)
    (X B C : ℕ→ℤ) :
    TernaryArenaSelectedTerminal.input (base I A.J nA) A s
      (left U radix A.J B) (right U radix A.J C) (requester U radix A.J X) r=
      TernaryArenaNativeComplete.input I U radix nA (selectedHash A s r) X B C := by
  have hL (j : ℕ) : sourceLeft (selectedHash A s r) U radix (B j)=
      hashMap A s r (fun t => (left U radix A.J B j t.val : ZMod p)) := selectedHash_raw A s r _
  have hR (j : ℕ) : sourceRight (selectedHash A s r) U radix (C j)=
      hashMap A s r (fun t => (right U radix A.J C j t.val : ZMod p)) := selectedHash_raw A s r _
  have hO (j : ℕ) : target (selectedHash A s r) U radix X j=
      (TernaryExtensionEncoding.coefficientCode
        (hashMap A s r (fun t => (requester U radix A.J X j t.val : ZMod p))) : ℤ) := by
    unfold target
    rw [selectedHash_raw]
    rfl
  unfold TernaryArenaSelectedTerminal.input TernaryArenaPrefixGroups.input base TernaryArenaNativeComplete.input
  congr 1
  · funext j
    rw [hL]
    rfl
  · funext j
    rw [hR]
    rfl
  · funext j
    rw [hO]
    rfl

/-- Direct final-solver interface: exact literal signed native potential is
zero for the selected original row state. -/
theorem native_signed_zero (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs)
    (K n U0 r U radix nA M C0 : ℕ) (s : State (p := p) A) (X B C : ℕ→ℤ)
    (hbudget : Budget maps τ cap Q (base I A.J nA) A K n U0
      (left U radix A.J B) (right U radix A.J C) (requester U radix A.J X) r s)
    (hb : 0<9*pairFactor m F K)
    (hdrift : (9*pairFactor m F K)^4*M^(4*K+3)≤(p^(2*K))^4)
    (hcover : n^2≤M^r) (hinit : U0^4≤C0*n^(8*K+5)) (hn : C0<n) :
    TernaryNativeTensorScore.pairedPotential
      (setup (r := r) maps τ cap Q
        (TernaryArenaNativeComplete.input I U radix nA (selectedHash A s r) X B C)) K A.J
      (fun j i => feature (leftRaw U radix A.J (B j)) i)
      (fun j i => feature (rightRaw U radix A.J (C j)) i)=0 := by
  have hz := native_zero maps τ cap Q (base I A.J nA) A K n U0
    (left U radix A.J B) (right U radix A.J C) (requester U radix A.J X) r s M C0
    hbudget hb hdrift hcover hinit hn
  rw [input_eq] at hz
  exact hz

theorem left_bound {U radix J : ℕ} (hb : 1<radix) (B : ℕ→ℤ) (j i : ℕ) :
    (left U radix J B j i).natAbs≤radix := by
  have hh := feature_abs (TernarySignedModes.leftRaw_abs (U := U) (J := J) hb (B j)) i
  rw [←Int.natCast_natAbs] at hh
  exact_mod_cast hh

theorem right_bound {U radix J : ℕ} (hb : 1<radix) (C : ℕ→ℤ) (j i : ℕ) :
    (right U radix J C j i).natAbs≤radix := by
  have hh := feature_abs (TernarySignedModes.rightRaw_abs (U := U) (J := J) hb (C j)) i
  rw [←Int.natCast_natAbs] at hh
  exact_mod_cast hh

theorem requester_bound {U radix J : ℕ} (hb : 1<radix) (X : ℕ→ℤ) (j i : ℕ) :
    (requester U radix J X j i).natAbs≤radix := by
  have hh := feature_abs (TernarySignedModes.requesterRaw_abs (U := U) (J := J) hb
    (X (position J j)) (TernaryCarryCode.carryFromCode J (j%(2^J)))) i
  rw [←Int.natCast_natAbs] at hh
  exact_mod_cast hh

theorem signed_nonnegative {x : ℤ} {b : ℕ} (hb : b≤p) (hx : x.natAbs≤b) : 0≤(p : ℤ)+x := by
  have hab : |x|≤(b : ℤ) := by rw [←Int.natCast_natAbs]; exact_mod_cast hx
  have hp : (b : ℤ)≤p := by exact_mod_cast hb
  have hh := (abs_le.mp hab).1
  omega

/-- No multiplicity is lost when packed keys replace original row vectors. -/
theorem key_collisions (A : Inputs) (s : State (p := p) A) (r q : ℕ) (L : ℕ→ℕ→ℤ) :
    (TernaryOriginalCollisions.collisionPairs (fun i : Fin q =>
      TernaryExtensionEncoding.coefficientCode (hashMap A s r (fun t => (L i.val t.val : ZMod p))))).card=
      collisions A s.row L r q := by
  congr 1
  ext ab
  simp only [TernaryOriginalCollisions.collisionPairs,Finset.mem_filter,Finset.mem_univ,true_and,
    (TernaryExtensionEncoding.coefficientCode_injective r).eq_iff]
  rfl

theorem left_key_collisions (A : Inputs) (s : State (p := p) A) (r q U radix : ℕ) (B : ℕ→ℤ) :
    (TernaryOriginalCollisions.collisionPairs (fun i : Fin q =>
      TernaryExtensionEncoding.coefficientCode (sourceLeft (selectedHash A s r) U radix (B i.val)))).card=
      collisions A s.row (left U radix A.J B) r q := by
  simp_rw [sourceLeft,selectedHash_raw]
  exact key_collisions A s r q (left U radix A.J B)

theorem right_key_collisions (A : Inputs) (s : State (p := p) A) (r q U radix : ℕ) (C : ℕ→ℤ) :
    (TernaryOriginalCollisions.collisionPairs (fun i : Fin q =>
      TernaryExtensionEncoding.coefficientCode (sourceRight (selectedHash A s r) U radix (C i.val)))).card=
      collisions A s.row (right U radix A.J C) r q := by
  simp_rw [sourceRight,selectedHash_raw]
  exact key_collisions A s r q (right U radix A.J C)

end ThreeSum.TernaryArenaSelectedSigned
