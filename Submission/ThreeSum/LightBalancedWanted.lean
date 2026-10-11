import Submission.ThreeSum.LightWantedSetup

/-!
# Executable balancing followed by the complete wanted-pair join

The host chooses the common shift from the two original signed arrays and
then builds every matching original-position pair. The returned count obeys
the exact incidence mean bound. The offset and the residue/bucket inputs are
computed by the closed program, with the same duplicate multiplicities.
-/

namespace ThreeSum.LightBalancedWanted

open Light WantedResidueKeys

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

/-- Two original signed arrays, their lengths, modulus, and free address. -/
def body (pOffset pWanted : ℕ) : Stmt :=
  .set 6 (v 2 +' v 3) ;;
  .call pOffset [v 0,v 1,v 2,v 3,v 4,v 6,v 5] 7 ;;
  .call pWanted [v 0,v 1,v 2,v 3,v 4,v 7,v 5] 0

def program : Program := ReportingHostRelocation.program
  LightOriginalOffset.program LightWantedSetup.program ++ [body 0 24]

theorem program_length : program.length=26 := rfl

def time (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR U : ℕ) : ℕ :=
  LightOriginalOffset.time M NL NR U+
    LightWantedSetup.time M left right NL NR U M
      (LightOriginalOffset.selected M left right NL NR)+100

def space (free M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR U : ℕ) : ℕ :=
  max (LightOriginalOffset.space free M (NL+NR) U)
    (LightWantedSetup.space free M left right NL NR U M
      (LightOriginalOffset.selected M left right NL NR))

def word (M NL NR U : ℕ) : ℕ :=
  max (LightOriginalOffset.word M (NL+NR) U) (LightSourceResidues.word M M U M)

variable {lim : Limits}

theorem program_meets {μ : ℕ → ℤ} {a b NL NR M free U d : ℕ} [NeZero M]
    (left right : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+NL ≤ free) (hb : b+NR ≤ free)
    (hspace : space free M left right NL NR U ≤ lim.space)
    (hword : (word M NL NR U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 M+NL+6 ≤ lim.depth)
    (hleft : ∀ i < NL, μ (a+i)=left i) (hright : ∀ j < NR, μ (b+j)=right j)
    (hvaluesL : ∀ i < NL, |left i| ≤ (U : ℤ))
    (hvaluesR : ∀ j < NR, |right j| ≤ (U : ℤ)) :
    Meets lim program 25 d [a,b,NL,NR,M,free] μ (time M left right NL NR U)
      (fun r ν => r=(free : ℤ) ∧
        LightWantedSetup.Output ν free M left right NL NR
          (LightOriginalOffset.selected M left right NL NR) ∧
        M*(ν free).toNat ≤ NL*NR ∧ Kept μ ν free) := by
  let shift := LightOriginalOffset.selected M left right NL NR
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hshift : shift < M := LightOriginalOffset.selected_lt ..
  have hshiftAbs : |(shift : ℤ)| ≤ (M : ℤ) := by
    rw [Int.abs_natCast]
    exact Int.ofNat_le.mpr (by omega)
  have hoffSpace : LightOriginalOffset.space free M (NL+NR) U ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hwantedSpace : LightWantedSetup.space free M left right NL NR U M shift ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hoffWord : (LightOriginalOffset.word M (NL+NR) U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hwantedWord : (LightSourceResidues.word M M U M : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  have hNWord : ((NL+NR : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold LightOriginalOffset.space at hoffSpace; omega)).trans hw
  have hselected : LightOriginalOffset.selected M (fun i => μ (a+i)) (fun j => μ (b+j)) NL NR=shift :=
    selected_congr hleft hright
  apply Meets.of_body (p := 25) (by rfl : program[25]? = some (body 0 24))
  unfold body time
  light_set (NL+NR : ℕ)
  have ho := ((LightOriginalOffset.program_meets (d := d+1) (μ := μ)
    (a := a) (b := b) (nLeft := NL) (nRight := NR) (p := M) (N := NL+NR)
    (free := free) (U := U) hw ha hb (by omega) (by omega) hoffSpace hoffWord (by omega)
    (fun i hi => by rw [hleft i hi]; exact hvaluesL i hi)
    (fun j hj => by rw [hright j hj]; exact hvaluesR j hj)).append
      (LightWantedSetup.program.map (ReportingHostRelocation.relocate 13))).append [body 0 24]
  light_call ho with chosen μ₁ ⟨hchosen,hkeepO⟩
  have hchosenShift : chosen=(shift : ℤ) := hchosen.trans (congrArg Nat.cast hselected)
  have hs := (ReportingHostRelocation.meets
    (LightWantedSetup.program_meets (d := d+1) (μ := μ₁) (a := a) (b := b)
      (NL := NL) (NR := NR) (M := M) (free := free) (U := U) (D := M) (shift := shift)
      left right hw hM ha hb hwantedSpace hwantedWord hshiftAbs (by omega)
      (fun i hi => (hkeepO _ (by omega)).trans (hleft i hi))
      (fun j hj => (hkeepO _ (by omega)).trans (hright j hj)) hvaluesL hvaluesR)
    LightOriginalOffset.program).append [body 0 24]
  light_call hs using hchosenShift,shift with result ν ⟨hresult,houtput,hkeepS⟩
  refine ⟨hresult,houtput,?_,?_⟩
  · change M*(ν free).toNat ≤ NL*NR
    rw [houtput.1,Int.toNat_natCast]
    exact selected_total_bound M left right NL NR
  · intro i hi
    exact (hkeepS i hi).trans (hkeepO i hi)

theorem total_le_div (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR : ℕ) :
    total M left right NL NR (LightOriginalOffset.selected M left right NL NR) ≤ NL*NR/M := by
  apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (NeZero.ne M))).mpr
  simpa only [Nat.mul_comm] using selected_total_bound M left right NL NR

theorem time_bound (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR U : ℕ) :
    time M left right NL NR U ≤ LightOriginalOffset.time M NL NR U+
      2000*(NL+NR+M+NL*NR/M+1)*(Nat.log 2 (U+1)+Nat.log 2 (M+M+1)+1)+100 := by
  have hh := LightWantedSetup.time_bound M left right NL NR U M
    (LightOriginalOffset.selected M left right NL NR)
  have hc := total_le_div M left right NL NR
  calc
    time M left right NL NR U ≤ LightOriginalOffset.time M NL NR U+
      2000*(NL+NR+M+total M left right NL NR (LightOriginalOffset.selected M left right NL NR)+1)*
        (Nat.log 2 (U+1)+Nat.log 2 (M+M+1)+1)+100 := by unfold time; omega
    _ ≤ _ := by gcongr

end ThreeSum.LightBalancedWanted
