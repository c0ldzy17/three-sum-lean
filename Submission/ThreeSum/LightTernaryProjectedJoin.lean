import Submission.ThreeSum.LightTernaryOriginalJoin

/-!
# Two different moduli in the original-position join

The first scan reduces each original signed record modulo the selected
scalar modulus, then adds its fixed carry shift and reduces modulo the
native radix modulus.  The following actual bucket/join host consumes those
computed keys.  Every original position is retained, including duplicates.
-/

namespace ThreeSum.LightTernaryProjectedJoin

open Light

set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

/-- Original array, literal dictionary, lengths, scalar/native moduli, shift,
computed-key address, initial residue scratch, and join free address. -/
def body (pResidues pJoin : ℕ) : Stmt :=
  .call pResidues [v 0,v 7,v 2,v 4,v 5,v 8,v 6] 10 ;;
  .call pJoin [v 7,v 1,v 2,v 3,v 5,k 0,v 9] 11 ;;
  .set 0 (v 11)

def joinedProgram : Program := ReportingHostRelocation.program
  LightSourceResidues.program LightWantedSetup.program

def program : Program := joinedProgram ++ [body 0 13]

theorem program_length : program.length=15 := rfl

def projected (q M : ℕ) (shift : ℤ) (input : ℕ → ℤ) (i : ℕ) : ℤ :=
  LightSourceResidues.key q M shift (input i)

theorem projected_dvd_iff {q M : ℕ} (hM : 0 < M)
    (shift x y : ℤ) :
    (M : ℤ) ∣ (LightSourceResidues.key q M shift x : ℤ)-y ↔
      (M : ℤ) ∣ x%(q : ℤ)+shift-y := by
  rw [LightSourceResidues.key_cast hM]
  rw [Int.dvd_iff_emod_eq_zero,Int.dvd_iff_emod_eq_zero]
  simp only [Int.sub_emod,Int.emod_emod]

theorem output_original_positions {q M NL NR free : ℕ} {ν : ℕ → ℤ}
    {input dictionary : ℕ → ℤ} {shift : ℤ} (hM : 0 < M)
    (H : LightWantedSetup.Output ν free M (projected q M shift input)
      dictionary NL NR 0) :
    ∃ ps : List (ℕ × ℕ),
      ps.length=WantedResidueKeys.total M (projected q M shift input) dictionary NL NR 0 ∧
      ps.Nodup ∧
      (∀ i j, (i,j) ∈ ps ↔ i < NL ∧ j < NR ∧
        (M : ℤ) ∣ input i%(q : ℤ)+shift-dictionary j) ∧
      Seg ν (LightWantedSetup.pairBase free NL NR M) (WantedPairs.cells ps) := by
  obtain ⟨_,_,_,_,ps,hlen,hnodup,hmem,hseg⟩ := H
  refine ⟨ps,hlen,hnodup,?_,hseg⟩
  intro i j
  rw [hmem]
  simp only [projected,add_zero,projected_dvd_iff hM]

def time (q M : ℕ) (input dictionary : ℕ → ℤ) (NL NR U D : ℕ)
    (shift : ℤ) : ℕ :=
  LightSourceResidues.time NL q U D+
    LightWantedSetup.time M (projected q M shift input) dictionary NL NR (U+M) 0 0+50

theorem time_bound (q M : ℕ) (input dictionary : ℕ → ℤ)
    (NL NR U D : ℕ) (shift : ℤ) :
    time q M input dictionary NL NR U D shift ≤
      254*NL*(Nat.log 2 (U+1)+Nat.log 2 (q+D+1)+1)+
      2000*(NL+NR+M+
        WantedResidueKeys.total M (projected q M shift input) dictionary NL NR 0+1)*
        (Nat.log 2 (U+M+1)+Nat.log 2 (M+1)+1)+56 := by
  have hscan := LightSourceResidues.time_bound NL q U D
  have hjoin := LightWantedSetup.time_bound M (projected q M shift input)
    dictionary NL NR (U+M) 0 0
  simp only [Nat.add_zero] at hjoin
  unfold time
  omega

theorem mass_le_of_cap {q M NL NR cap : ℕ} {input dictionary : ℕ → ℤ} {shift : ℤ}
    (hcap : ∀ i < NL, LightHistogram.count
      (fun j => WantedResidueKeys.code M 0 (dictionary j))
      (WantedResidueKeys.code M 0 (projected q M shift input i)) NR ≤ cap) :
    WantedResidueKeys.total M (projected q M shift input) dictionary NL NR 0 ≤ NL*cap := by
  unfold WantedResidueKeys.total
  induction NL with
  | zero => simp
  | succ n ih =>
    rw [WantedPairs.count_succ]
    have hn := hcap n (by omega)
    have hp := ih (fun i hi => hcap i (by omega))
    simpa only [Nat.add_mul,Nat.one_mul] using Nat.add_le_add hp hn

theorem time_bound_of_cap {q M NL NR U D cap : ℕ} {input dictionary : ℕ → ℤ} {shift : ℤ}
    (hcap : ∀ i < NL, LightHistogram.count
      (fun j => WantedResidueKeys.code M 0 (dictionary j))
      (WantedResidueKeys.code M 0 (projected q M shift input i)) NR ≤ cap) :
    time q M input dictionary NL NR U D shift ≤
      254*NL*(Nat.log 2 (U+1)+Nat.log 2 (q+D+1)+1)+
      2000*(NL+NR+M+NL*cap+1)*
        (Nat.log 2 (U+M+1)+Nat.log 2 (M+1)+1)+56 := by
  have hm := mass_le_of_cap hcap
  have hs : NL+NR+M+WantedResidueKeys.total M (projected q M shift input)
      dictionary NL NR 0+1 ≤ NL+NR+M+NL*cap+1 := by omega
  have hp := Nat.mul_le_mul_right (Nat.log 2 (U+M+1)+Nat.log 2 (M+1)+1)
    (Nat.mul_le_mul_left 2000 hs)
  exact (time_bound q M input dictionary NL NR U D shift).trans (by omega)

variable {lim : Limits}

theorem program_meets {μ : ℕ → ℤ}
    {src dict NL NR q M codeBase work free U D d : ℕ} {shift : ℤ}
    (input dictionary : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hq : 0 < q) (hM : 0 < M)
    (hsrc : src+NL ≤ codeBase) (hdict : dict+NR ≤ codeBase)
    (hcodes : codeBase+NL ≤ free) (hfree : free ≤ work)
    (hresidueSpace : LightSourceResidues.space work q U D ≤ lim.space)
    (hjoinSpace : LightWantedSetup.space free M (projected q M shift input)
      dictionary NL NR (U+M) 0 0 ≤ lim.space)
    (hresidueWord : (LightSourceResidues.word q M U D : ℤ) ≤ lim.word)
    (hjoinWord : (LightSourceResidues.word M M (U+M) 0 : ℤ) ≤ lim.word)
    (hshift : |shift| ≤ (D : ℤ)) (hd : d+NL+6 ≤ lim.depth)
    (hinput : ∀ i < NL, μ (src+i)=input i)
    (hdictionary : ∀ j < NR, μ (dict+j)=dictionary j)
    (hvalues : ∀ i < NL, |input i| ≤ (U : ℤ))
    (hkeys : ∀ j < NR, |dictionary j| ≤ (U : ℤ)) :
    Meets lim program 14 d [src,dict,NL,NR,q,M,shift,codeBase,work,free] μ
      (time q M input dictionary NL NR U D shift)
      (fun r ν => r=(free : ℤ) ∧
        LightWantedSetup.Output ν free M (projected q M shift input)
          dictionary NL NR 0 ∧ Kept μ ν codeBase) := by
  have hc := (LightSourceResidues.program_meets (d := d+1) (μ := μ)
    (src := src) (dst := codeBase) (n := NL) (p := q) (m := M)
    (work := work) (U := U) (D := D) (shift := shift)
    hw (by omega) hq hM (by omega) (by omega) hresidueSpace
    (Or.inl hsrc) hshift hresidueWord
    (fun i hi => by rw [hinput i hi]; exact hvalues i hi)).append
      (LightWantedSetup.program.map (ReportingHostRelocation.relocate 2))
  have hc' := hc.append [body 0 13]
  apply Meets.of_body (by rfl : program[14]?=some (body 0 13))
  unfold body time
  light_call hc' using projected with unused μ₁ ⟨hcomputed,hkeep⟩
  have hcomputed' (i : ℕ) (hi : i < NL) :
      μ₁ (codeBase+i)=projected q M shift input i := by
    rw [hcomputed i hi,hinput i hi]
    rfl
  have hdict' (j : ℕ) (hj : j < NR) : μ₁ (dict+j)=dictionary j := by
    rw [hkeep _ ⟨by omega,Or.inl (by omega)⟩,hdictionary j hj]
  have hpval (i : ℕ) (hi : i < NL) :
      |projected q M shift input i| ≤ ((U+M : ℕ) : ℤ) := by
    unfold projected
    rw [Int.abs_natCast]
    have h := LightSourceResidues.key_lt (p := q) hM shift (input i)
    exact_mod_cast (show LightSourceResidues.key q M shift (input i) ≤ U+M by omega)
  have hj := (ReportingHostRelocation.meets
    (LightWantedSetup.program_meets (d := d+1) (μ := μ₁)
      (a := codeBase) (b := dict) (NL := NL) (NR := NR) (M := M)
      (free := free) (U := U+M) (D := 0) (shift := 0)
      (projected q M shift input) dictionary hw hM hcodes (by omega)
      hjoinSpace hjoinWord (by simp) (by omega) hcomputed' hdict' hpval
      (fun j hj => (hkeys j hj).trans (by exact_mod_cast (Nat.le_add_right U M))))
    LightSourceResidues.program).append [body 0 13]
  light_call hj with result ν ⟨hresult,hout,hkeepJoin⟩
  light_set (free : ℕ) using hresult
  refine ⟨rfl,hout,?_⟩
  intro a ha
  exact (hkeepJoin a (by omega)).trans (hkeep a ⟨by omega,Or.inl ha⟩)

end ThreeSum.LightTernaryProjectedJoin
