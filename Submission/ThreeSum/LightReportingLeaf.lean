import Submission.ThreeSum.LightReportingBucketTest
import Submission.ThreeSum.LightResidues

/-!
# Executable residue selection and original-value leaf decision

The host reduces the two actual endpoint values, selects the independently
trimmed physical buckets, and tests original values. Its Boolean result has
a memory-independent physical-index specification, suitable for sequential
candidate batching with the exact sum of the selected pair costs.
-/

namespace ThreeSum.LightReportingLeaf

open Light SourceBuckets LightResidues ReportingHostBucketTest

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def Hit (a xL xR : ℤ) (left right : ℕ→ℤ) (keyL keyR : ℕ→ℕ)
    (NL NR Mo flagL flagR : ℕ) : Prop :=
  flagL=1 ∧ flagR=1 ∧ ∃ i<NL, ∃ j<NR,
    keyL i=residue Mo 1 xL ∧ keyR j=residue Mo 1 xR ∧ right j-left i-a=0

def body (pEmod pTest : ℕ) : Stmt :=
  .call pEmod [v 5,v 13,v 14 +' k 4] 15 ;;
  .call pEmod [v 9,v 13,v 14 +' k 4] 16 ;;
  .call pTest [v 0,v 1,v 2,v 3,v 4,v 15,v 6,v 7,v 8,v 16,v 10,v 11,v 12,v 13,v 14] 17 ;;
  .ite (k 0 <' v 17) (.set 0 (k 1)) (.set 0 (k 0))

def program : Program := LightReportingBucketTest.program ++ [emodBody,body 4 3]

def time (keyL keyR : ℕ→ℕ) (NL NR Mo flagL flagR U : ℕ) (xL xR : ℤ) : ℕ :=
  LightReportingBucketTest.time keyL keyR NL NR (residue Mo 1 xL) (residue Mo 1 xR) flagL flagR+
    2*residueBudget U+300

theorem stored_of_kept {μ ν : ℕ→ℤ} {key : ℕ→ℕ} {N Mo offsets flat stop : ℕ}
    (H : Stored μ key N Mo offsets flat) (hkey : ∀ i<N, key i<Mo)
    (hoffsets : offsets+Mo+1≤stop) (hflat : flat+N≤stop) (hkeep : Kept μ ν stop) :
    Stored ν key N Mo offsets flat := by
  constructor
  · intro r hr
    exact (hkeep _ (by omega)).trans (H.offsets r hr)
  · intro i hi
    have hpos := position_lt hkey hi
    exact (hkeep _ (by omega)).trans (H.indices i hi)

variable {lim : Limits}

theorem program_meets {μ : ℕ→ℤ}
    {srcL srcR offsetsL offsetsR flatL flatR NL NR Mo flagL flagR work U d : ℕ}
    (a xL xR : ℤ) (left right : ℕ→ℤ) (keyL keyR : ℕ→ℕ)
    (HL : Stored μ keyL NL Mo offsetsL flatL) (HR : Stored μ keyR NR Mo offsetsR flatR)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+3≤lim.depth) (hMo : 0<Mo)
    (hsrcL : srcL+NL≤work) (hsrcR : srcR+NR≤work)
    (hoffsetsL : offsetsL+Mo+1≤work) (hoffsetsR : offsetsR+Mo+1≤work)
    (hflatL : flatL+NL≤work) (hflatR : flatR+NR≤work)
    (hspace : work+4+(Nat.log 2 (U+1)+2)≤lim.space)
    (hword : (4*U+4*Mo+16 : ℤ)≤lim.word)
    (hkeyL : ∀ i<NL, keyL i<Mo) (hkeyR : ∀ j<NR, keyR j<Mo)
    (hflagL : flagL≤1) (hflagR : flagR≤1)
    (hreadL : ∀ i<NL, μ (srcL+i)=left i) (hreadR : ∀ j<NR, μ (srcR+j)=right j)
    (hvaluesL : ∀ i<NL, |left i|≤lim.word) (hvaluesR : ∀ j<NR, |right j|≤lim.word)
    (ha : |a|≤lim.word) (htarget : ∀ i<NL, |a+left i|≤lim.word)
    (hxL : |xL|≤(U : ℤ)) (hxR : |xR|≤(U : ℤ))
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    Meets lim program 5 d [a,srcL,srcR,offsetsL,flatL,xL,flagL,offsetsR,flatR,xR,flagR,NL,NR,Mo,work]
      μ (time keyL keyR NL NR Mo flagL flagR U xL xR)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Hit a xL xR left right keyL keyR NL NR Mo flagL flagR) ∧
        Kept μ ν work) := by
  have hpre : Emod.Pre lim Mo U (work+4) := ⟨hMo,hw,hword,hspace⟩
  have htimeL := emodTime_le (p := Mo) hxL
  have htimeR := emodTime_le (p := Mo) hxR
  unfold emodTime residueBudget at htimeL htimeR
  have hlog : Nat.log 2 (1+U)=Nat.log 2 (U+1) := by rw [Nat.add_comm]
  have hlLt := residue_lt hMo 1 xL
  have hrLt := residue_lt hMo 1 xR
  have hlCast := residue_cast hMo 1 xL
  have hrCast := residue_cast hMo 1 xR
  simp only [one_mul] at hlCast hrCast
  have haBounds := abs_le.mp ha
  have hxLBounds := abs_le.mp hxL
  have hxRBounds := abs_le.mp hxR
  apply Meets.of_body (p := 5) (by rfl : program[5]?=some (body 4 3))
  unfold body time
  light_call (emod_meets (P := program) (p := 4) (x := xL) rfl hpre hxL)
    using residueBudget,LightReportingBucketTest.time,LightReportingBucketPairs.time
    with l ν₁ ⟨hl,hkeepL⟩
  rw [← hlCast] at hl
  subst l
  light_call (emod_meets (P := program) (p := 4) (x := xR) rfl hpre hxR)
    using residueBudget,LightReportingBucketTest.time,LightReportingBucketPairs.time
    with r ν₂ ⟨hr,hkeepR⟩
  rw [← hrCast] at hr
  subst r
  have hkeep : Kept μ ν₂ work := fun i hi =>
    (hkeepR i (by omega)).trans (hkeepL i (by omega))
  have HL₂ := stored_of_kept HL hkeyL hoffsetsL hflatL hkeep
  have HR₂ := stored_of_kept HR hkeyR hoffsetsR hflatR hkeep
  have htest := (LightReportingBucketTest.program_meets (d := d+1) (μ := ν₂)
    (srcL := srcL) (srcR := srcR) (work := work) a left right keyL keyR HL₂ HR₂ hw (by omega)
    hsrcL hsrcR hoffsetsL hoffsetsR hflatL hflatR (by omega) hkeyL hkeyR hlLt hrLt hflagL hflagR
    (fun i hi => (hkeep _ (by omega)).trans (hreadL i hi))
    (fun j hj => (hkeep _ (by omega)).trans (hreadR j hj))
    hvaluesL hvaluesR ha htarget hcountWord).append [emodBody,body 4 3]
  light_call htest using residueBudget,LightReportingBucketTest.time,LightReportingBucketPairs.time
    with found ν₃ ⟨hfound,hkeepTest⟩
  have hwhole : Kept μ ν₃ work := fun i hi =>
    (hkeepTest i (Or.inl hi)).trans (hkeep i hi)
  have hhit : (0 : ℤ)<found ↔ Hit a xL xR left right keyL keyR NL NR Mo flagL flagR := by
    have hpos := testCount_pos_iff (rL := residue Mo 1 xL) (rR := residue Mo 1 xR)
      (flagL := flagL) (flagR := flagR) HL₂ HR₂ hkeyL hkeyR hlLt hrLt a left right
    change _ ↔ Hit a xL xR left right keyL keyR NL NR Mo flagL flagR at hpos
    rw [hfound]
    constructor
    · intro hh
      exact hpos.mp (by omega)
    · intro hh
      have hh' := hpos.mpr hh
      omega
  light_if hyes hno : (0 : ℤ)<found
    using residueBudget,LightReportingBucketTest.time,LightReportingBucketPairs.time
  · have htrue := hhit.mp hyes
    light_set (1 : ℕ) using residueBudget,LightReportingBucketTest.time,LightReportingBucketPairs.time
    exact ⟨by simp,by simpa using htrue,hwhole⟩
  · have hfalse : ¬Hit a xL xR left right keyL keyR NL NR Mo flagL flagR :=
      fun hh => hno (hhit.mpr hh)
    light_set (0 : ℕ) using residueBudget,LightReportingBucketTest.time,LightReportingBucketPairs.time
    exact ⟨by simp,by simp [hfalse],hwhole⟩

end ThreeSum.LightReportingLeaf
