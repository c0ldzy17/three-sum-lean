import Submission.ThreeSum.LightWantedJoin
import Submission.ThreeSum.WantedResidueKeys
import Submission.ThreeSum.LightSourceBucketSetup
import Submission.ThreeSum.ReportingHostRelocation

/-!
# Original signed arrays to an actual shifted wanted-pair array

The closed host computes all residue and bucket addresses, runs both signed
scans, builds the right fibers, and executes the output-sensitive join. Four
header cells retain the pair count, pair-array address, next free address and
the actual shift. No residue array, histogram or matching list is supplied.
-/

namespace ThreeSum.LightWantedSetup

open Light WantedResidueKeys

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def leftCodes (free : ℕ) : ℕ := free+4
def rightCodes (free NL : ℕ) : ℕ := leftCodes free+NL
def bucketBase (free NL NR : ℕ) : ℕ := rightCodes free NL+NR
def pairBase (free NL NR M : ℕ) : ℕ :=
  LightSourceBucketSetup.next (bucketBase free NL NR) NR M

/-- Left/right signed arrays, lengths, modulus, shift, and free address. -/
def body (pResidues pBuckets pJoin : ℕ) : Stmt :=
  .set 7 (v 6 +' k 4) ;;
  .set 8 (v 7 +' v 2) ;;
  .set 9 (v 8 +' v 3) ;;
  .set 10 (v 9 +' v 4) ;;
  .set 11 (v 9 +' k 3 *' v 4 +' k 1) ;;
  .set 12 (v 11 +' v 3) ;;
  .call pResidues [v 0,v 7,v 2,v 4,v 4,v 12,v 5] 13 ;;
  .call pResidues [v 1,v 8,v 3,v 4,v 4,v 12,k 0] 13 ;;
  .call pBuckets [v 8,v 3,v 4,v 9] 13 ;;
  .call pJoin [v 7,v 10,v 11,v 2,v 3,v 4,v 12] 14 ;;
  .store (v 6) (v 14) ;;
  .store (v 6 +' k 1) (v 12) ;;
  .store (v 6 +' k 2) (v 12 +' k 2 *' v 14) ;;
  .store (v 6 +' k 3) (v 5) ;;
  .set 0 (v 6)

def bucketProgram : Program := ReportingHostRelocation.program
  LightSourceResidues.program LightSourceBucketSetup.program

def joinedProgram : Program := ReportingHostRelocation.program
  bucketProgram LightWantedJoin.program

def program : Program := joinedProgram ++ [body 0 2 9]

theorem program_length : program.length=12 := rfl

def time (M : ℕ) (left right : ℕ → ℤ) (NL NR U D : ℕ) (shift : ℤ) : ℕ :=
  LightSourceResidues.time NL M U D+LightSourceResidues.time NR M U D+
    LightSourceBucketSetup.time NR M+
    LightWantedJoin.time (fun i => code M shift (left i)) (fun j => code M 0 (right j)) NR NL+500

def space (free M : ℕ) (left right : ℕ → ℤ) (NL NR U D : ℕ) (shift : ℤ) : ℕ :=
  max (LightSourceResidues.space (pairBase free NL NR M) M U D)
    (pairBase free NL NR M+2*total M left right NL NR shift)

def Output (ν : ℕ → ℤ) (free M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) : Prop :=
  ν free=(total M left right NL NR shift : ℤ) ∧
  ν (free+1)=(pairBase free NL NR M : ℤ) ∧
  ν (free+2)=((pairBase free NL NR M+2*total M left right NL NR shift : ℕ) : ℤ) ∧
  ν (free+3)=shift ∧
  ∃ ps : List (ℕ × ℕ), ps.length=total M left right NL NR shift ∧ ps.Nodup ∧
    (∀ i j, (i,j) ∈ ps ↔ i < NL ∧ j < NR ∧ (M : ℤ) ∣ left i+shift-right j) ∧
    Seg ν (pairBase free NL NR M) (WantedPairs.cells ps)

variable {lim : Limits}

theorem program_meets {μ : ℕ → ℤ} {a b NL NR M free U D d : ℕ} {shift : ℤ}
    (left right : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hM : 0 < M)
    (ha : a+NL ≤ free) (hb : b+NR ≤ free)
    (hspace : space free M left right NL NR U D shift ≤ lim.space)
    (hword : (LightSourceResidues.word M M U D : ℤ) ≤ lim.word)
    (hshift : |shift| ≤ (D : ℤ)) (hd : d+NL+5 ≤ lim.depth)
    (hleft : ∀ i < NL, μ (a+i)=left i) (hright : ∀ j < NR, μ (b+j)=right j)
    (hvaluesL : ∀ i < NL, |left i| ≤ (U : ℤ))
    (hvaluesR : ∀ j < NR, |right j| ≤ (U : ℤ)) :
    Meets lim program 11 d [a,b,NL,NR,M,shift,free] μ (time M left right NL NR U D shift)
      (fun r ν => r=(free : ℤ) ∧ Output ν free M left right NL NR shift ∧ Kept μ ν free) := by
  let lc := leftCodes free
  let rc := rightCodes free NL
  let bb := bucketBase free NL NR
  let off := LightSourceBucketSetup.offsets bb M
  let flat := LightSourceBucketSetup.flat bb M
  let dst := pairBase free NL NR M
  let lkey := fun i => code M shift (left i)
  let rkey := fun j => code M 0 (right j)
  have hjoinTime : LightWantedJoin.time lkey rkey NR NL=
      LightWantedJoin.time (fun i => code M shift (left i)) (fun j => code M 0 (right j)) NR NL := rfl
  have hscanSpace : LightSourceResidues.space dst M U D ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hpairSpace : dst+2*total M left right NL NR shift ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hdst : dst=free+4+NL+NR+3*M+1+NR := rfl
  have hlc : lc=free+4 := rfl
  have hrc : rc=free+4+NL := rfl
  have hbb : bb=free+4+NL+NR := rfl
  have hoff : off=bb+M := rfl
  have hflat : flat=bb+3*M+1 := rfl
  have h3M : (3*(M : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show 3*M ≤ lim.space by omega) : (3*(M : ℤ)) ≤ lim.space).trans hw
  have hDWord : (D : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold LightSourceResidues.word; omega)).trans hword
  have hlkey : ∀ i < NL, lkey i < M := fun _ _ => code_lt hM _ _
  have hrkey : ∀ j < NR, rkey j < M := fun _ _ => code_lt hM _ _
  apply Meets.of_body (p := 11) (by rfl : program[11]? = some (body 0 2 9))
  unfold body time
  light_set (lc : ℕ) using lc,leftCodes
  light_set (rc : ℕ) using rc,rightCodes,lc
  light_set (bb : ℕ) using bb,bucketBase,rc
  light_set (off : ℕ) using off,LightSourceBucketSetup.offsets
  light_set (flat : ℕ) using flat,LightSourceBucketSetup.flat
  light_set (dst : ℕ) using dst,pairBase,LightSourceBucketSetup.next,flat
  have hsL := (((LightSourceResidues.program_meets (d := d+1) (μ := μ)
    (src := a) (dst := lc) (n := NL) (p := M) (m := M) (work := dst)
    (U := U) (D := D) (shift := shift) hw (by omega) hM hM (by omega) (by omega)
    hscanSpace (Or.inl (by omega)) hshift hword
    (fun i hi => by rw [hleft i hi]; exact hvaluesL i hi)).append
      (LightSourceBucketSetup.program.map (ReportingHostRelocation.relocate 2))).append
      (LightWantedJoin.program.map (ReportingHostRelocation.relocate 9))).append [body 0 2 9]
  light_call hsL using code with _ μ₁ ⟨hcodesL,hkeepL⟩
  have hreadL (i : ℕ) (hi : i < NL) : μ₁ (lc+i)=(lkey i : ℤ) := by
    rw [hcodesL i hi,hleft i hi]
    rfl
  have hsR := (((LightSourceResidues.program_meets (d := d+1) (μ := μ₁)
    (src := b) (dst := rc) (n := NR) (p := M) (m := M) (work := dst)
    (U := U) (D := D) (shift := 0) hw (by omega) hM hM (by omega) (by omega)
    hscanSpace (Or.inl (by omega)) (by simp) hword
    (fun j hj => by rw [hkeepL _ ⟨by omega,Or.inl (by omega)⟩,hright j hj]; exact hvaluesR j hj)).append
      (LightSourceBucketSetup.program.map (ReportingHostRelocation.relocate 2))).append
      (LightWantedJoin.program.map (ReportingHostRelocation.relocate 9))).append [body 0 2 9]
  light_call hsR using code with _ μ₂ ⟨hcodesR,hkeepR⟩
  have hreadR (j : ℕ) (hj : j < NR) : μ₂ (rc+j)=(rkey j : ℤ) := by
    rw [hcodesR j hj,hkeepL _ ⟨by omega,Or.inl (by omega)⟩,hright j hj]
    rfl
  have hleft₂ (i : ℕ) (hi : i < NL) : μ₂ (lc+i)=(lkey i : ℤ) :=
    (hkeepR _ ⟨by omega,Or.inl (by omega)⟩).trans (hreadL i hi)
  have hbuckets := ((ReportingHostRelocation.meets
    (LightSourceBucketSetup.programProcs.meets (d := d+1) (μ := μ₂)
      (keys := rc) (N := NR) (M := M) (base := bb) rkey hw (by omega) hM
      (by omega) (by change dst ≤ lim.space; omega) hrkey hreadR)
    LightSourceResidues.program).append
      (LightWantedJoin.program.map (ReportingHostRelocation.relocate 9))).append [body 0 2 9]
  light_call hbuckets using LightSourceBucketSetup.time with next μ₃ ⟨hnext,H,hcounts,hkeepB⟩
  have hleft₃ (i : ℕ) (hi : i < NL) : μ₃ (lc+i)=(lkey i : ℤ) :=
    (hkeepB _ (by omega)).trans (hleft₂ i hi)
  have hj := (ReportingHostRelocation.meets
    (LightWantedJoin.program_meets (d := d+1) (μ := μ₃) (keys := lc)
      (offsets := off) (flat := flat) (NR := NR) (M := M) (dst := dst) (n := NL)
      lkey rkey hrkey hw (by omega) (by omega) (by omega) hpairSpace (by omega)
      hlkey hleft₃ H) bucketProgram).append [body 0 2 9]
  light_call hj using lkey,rkey,code with matchCount μ₄ ⟨hmatch,hpairs,hkeepJ⟩
  have hmatchTotal : matchCount=(total M left right NL NR shift : ℤ) := hmatch
  have htwoWord : (2*(total M left right NL NR shift : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show 2*total M left right NL NR shift ≤ lim.space by omega) :
      (2*(total M left right NL NR shift : ℤ)) ≤ lim.space).trans hw
  light_store free (total M left right NL NR shift : ℕ) using hmatchTotal
  light_store (free+1) (dst : ℕ)
  light_store (free+2) (dst+2*total M left right NL NR shift : ℕ) using hmatchTotal
  light_store (free+3) shift
  light_set (free : ℕ)
  refine ⟨rfl,?_,?_⟩
  · refine ⟨?_,?_,?_,?_,WantedPairs.pairs μ₃ off flat lkey NL,?_,?_,?_,?_⟩
    · simp
    · simp [dst]
    · simp [dst]
    · simp
    · exact WantedPairs.pairs_length H NL hlkey
    · exact WantedPairs.pairs_nodup H hlkey hrkey
    · intro i j
      rw [WantedPairs.mem_pairs H hlkey hrkey]
      simp only [lkey,rkey,code_eq_iff hM]
    · intro i hi
      change Function.update (Function.update (Function.update (Function.update μ₄ free _)
        (free+1) _) (free+2) _) (free+3) _ (dst+i)=_
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
        Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact hpairs i hi
  · intro i hi
    change Function.update (Function.update (Function.update (Function.update μ₄ free _)
      (free+1) _) (free+2) _) (free+3) _ i=μ i
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    rw [hkeepJ _ (by omega),hkeepB _ (by omega),
      hkeepR _ ⟨by omega,Or.inl (by omega)⟩,hkeepL _ ⟨by omega,Or.inl (by omega)⟩]

theorem time_bound (M : ℕ) (left right : ℕ → ℤ) (NL NR U D : ℕ) (shift : ℤ) :
    time M left right NL NR U D shift ≤
      2000*(NL+NR+M+total M left right NL NR shift+1)*
        (Nat.log 2 (U+1)+Nat.log 2 (M+D+1)+1) := by
  have hL := LightSourceResidues.time_bound NL M U D
  have hR := LightSourceResidues.time_bound NR M U D
  have hB := LightSourceBucketSetup.time_bound NR M
  have hJ := LightWantedJoin.time_bound (fun i => code M shift (left i))
    (fun j => code M 0 (right j)) NR NL
  change LightWantedJoin.time _ _ NR NL ≤ 400*(NL+total M left right NL NR shift+1) at hJ
  unfold time
  nlinarith

end ThreeSum.LightWantedSetup
