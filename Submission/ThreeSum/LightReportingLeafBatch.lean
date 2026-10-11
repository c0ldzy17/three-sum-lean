import Submission.ThreeSum.LightReportingLeaf

/-!
# Actual terminal-candidate batch with a sum of physical pair charges

All endpoint and independent flag arrays are read from retained memory.
The recursion evaluates each candidate and retains a Boolean disjunction.
Its cost sums the actual leaf costs instead of multiplying a worst fiber
size by the number of candidates.
-/

namespace ThreeSum.LightReportingLeafBatch

open Light Finset SourceBuckets LightResidues
open scoped BigOperators

set_option maxHeartbeats 2600000
set_option maxRecDepth 10000

def Hit (a : ℤ) (xL xR left right : ℕ→ℤ) (keyL keyR flagL flagR : ℕ→ℕ)
    (NL NR Mo n : ℕ) : Prop :=
  ∃ i<n, LightReportingLeaf.Hit a (xL i) (xR i) left right keyL keyR NL NR Mo (flagL i) (flagR i)

theorem hit_succ (a : ℤ) (xL xR left right : ℕ→ℤ) (keyL keyR flagL flagR : ℕ→ℕ)
    (NL NR Mo n : ℕ) :
    Hit a xL xR left right keyL keyR flagL flagR NL NR Mo (n+1) ↔
      Hit a xL xR left right keyL keyR flagL flagR NL NR Mo n ∨
      LightReportingLeaf.Hit a (xL n) (xR n) left right keyL keyR NL NR Mo (flagL n) (flagR n) := by
  constructor
  · rintro ⟨i,hi,hh⟩
    by_cases hin : i<n
    · exact Or.inl ⟨i,hin,hh⟩
    · have he : i=n := by omega
      exact Or.inr (he ▸ hh)
  · rintro (⟨i,hi,hh⟩ | hh)
    · exact ⟨i,by omega,hh⟩
    · exact ⟨n,by omega,hh⟩

def time (keyL keyR flagL flagR : ℕ→ℕ) (NL NR Mo U : ℕ) (xL xR : ℕ→ℤ) : ℕ→ℕ
  | 0 => 30
  | n+1 => time keyL keyR flagL flagR NL NR Mo U xL xR n+
      LightReportingLeaf.time keyL keyR NL NR Mo (flagL n) (flagR n) U (xL n) (xR n)+300

theorem time_eq_sum (keyL keyR flagL flagR : ℕ→ℕ) (NL NR Mo U : ℕ) (xL xR : ℕ→ℤ) (n : ℕ) :
    time keyL keyR flagL flagR NL NR Mo U xL xR n=30+
      ∑ i∈range n, (LightReportingLeaf.time keyL keyR NL NR Mo (flagL i) (flagR i) U (xL i) (xR i)+300) := by
  induction n with
  | zero => simp [time]
  | succ n ih => simp only [time,Finset.sum_range_succ,ih]; omega

/-- a, source and bucket pointers, source lengths, modulus, four retained
endpoint/flag arrays, candidate count, and scratch. -/
def body (pSelf pLeaf : ℕ) : Stmt :=
  .ite (k 0 <' v 14)
    (.call pSelf [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14 -' k 1,v 15] 16 ;;
      .set 17 (v 14 -' k 1) ;;
      .set 18 (M (v 10 +' v 17)) ;;
      .set 19 (M (v 11 +' v 17)) ;;
      .set 20 (M (v 12 +' v 17)) ;;
      .set 21 (M (v 13 +' v 17)) ;;
      .call pLeaf [v 0,v 1,v 2,v 3,v 4,v 18,v 20,v 5,v 6,v 19,v 21,v 7,v 8,v 9,v 15] 22 ;;
      .ite (k 0 <' v 16 +' v 22) (.set 0 (k 1)) (.set 0 (k 0)))
    (.set 0 (k 0))

def program : Program := LightReportingLeaf.program ++ [body 6 5]

variable {lim : Limits}

theorem program_meets {μ : ℕ→ℤ}
    {srcL srcR offsetsL offsetsR flatL flatR NL NR Mo rawL rawR flagsL flagsR n work U d : ℕ}
    (a : ℤ) (xL xR left right : ℕ→ℤ) (keyL keyR flagL flagR : ℕ→ℕ)
    (HL : Stored μ keyL NL Mo offsetsL flatL) (HR : Stored μ keyR NR Mo offsetsR flatR)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+n+4≤lim.depth) (hMo : 0<Mo)
    (hsrcL : srcL+NL≤work) (hsrcR : srcR+NR≤work)
    (hoffsetsL : offsetsL+Mo+1≤work) (hoffsetsR : offsetsR+Mo+1≤work)
    (hflatL : flatL+NL≤work) (hflatR : flatR+NR≤work)
    (hrawL : rawL+n≤work) (hrawR : rawR+n≤work)
    (hflagsL : flagsL+n≤work) (hflagsR : flagsR+n≤work)
    (hspace : work+4+(Nat.log 2 (U+1)+2)≤lim.space)
    (hword : (4*U+4*Mo+16 : ℤ)≤lim.word)
    (hkeyL : ∀ i<NL, keyL i<Mo) (hkeyR : ∀ j<NR, keyR j<Mo)
    (hflagL : ∀ i<n, flagL i≤1) (hflagR : ∀ i<n, flagR i≤1)
    (hreadL : ∀ i<NL, μ (srcL+i)=left i) (hreadR : ∀ j<NR, μ (srcR+j)=right j)
    (hreadXL : ∀ i<n, μ (rawL+i)=xL i) (hreadXR : ∀ i<n, μ (rawR+i)=xR i)
    (hreadFL : ∀ i<n, μ (flagsL+i)=(flagL i : ℤ))
    (hreadFR : ∀ i<n, μ (flagsR+i)=(flagR i : ℤ))
    (hvaluesL : ∀ i<NL, |left i|≤lim.word) (hvaluesR : ∀ j<NR, |right j|≤lim.word)
    (ha : |a|≤lim.word) (htarget : ∀ i<NL, |a+left i|≤lim.word)
    (hxL : ∀ i<n, |xL i|≤(U : ℤ)) (hxR : ∀ i<n, |xR i|≤(U : ℤ))
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    Meets lim program 6 d [a,srcL,srcR,offsetsL,flatL,offsetsR,flatR,NL,NR,Mo,rawL,rawR,flagsL,flagsR,n,work]
      μ (time keyL keyR flagL flagR NL NR Mo U xL xR n)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Hit a xL xR left right keyL keyR flagL flagR NL NR Mo n) ∧
        Kept μ ν work) := by
  have haBounds := abs_le.mp ha
  induction n generalizing μ d with
  | zero =>
      apply Meets.of_body (p := 6) (by rfl : program[6]?=some (body 6 5))
      unfold body time
      light_if hbad hno : (0 : ℤ)<0
      · omega
      · light_set (0 : ℕ)
        exact ⟨by simp,by simp [Hit],SameOn.refl⟩
  | succ n ih =>
      apply Meets.of_body (p := 6) (by rfl : program[6]?=some (body 6 5))
      unfold body
      rw [time]
      light_if hyes hbad : (0 : ℤ)<((n+1 : ℕ) : ℤ)
        using LightReportingLeaf.time,LightReportingBucketTest.time,LightReportingBucketPairs.time,residueBudget
      · have hrun := ih (μ := μ) (d := d+1) HL HR (by omega)
          (by omega) (by omega) (by omega) (by omega)
          (fun i hi => hflagL i (by omega)) (fun i hi => hflagR i (by omega))
          hreadL hreadR (fun i hi => hreadXL i (by omega)) (fun i hi => hreadXR i (by omega))
          (fun i hi => hreadFL i (by omega)) (fun i hi => hreadFR i (by omega))
          (fun i hi => hxL i (by omega)) (fun i hi => hxR i (by omega))
        light_call hrun using LightReportingLeaf.time,LightReportingBucketTest.time,LightReportingBucketPairs.time,residueBudget
          with prev ν ⟨hprevBool,hprev,hkeep⟩
        have HLν := LightReportingLeaf.stored_of_kept HL hkeyL hoffsetsL hflatL hkeep
        have HRν := LightReportingLeaf.stored_of_kept HR hkeyR hoffsetsR hflatR hkeep
        have hxL' := abs_le.mp (hxL n (by omega))
        have hxR' := abs_le.mp (hxR n (by omega))
        have hfL := hflagL n (by omega)
        have hfR := hflagR n (by omega)
        have hXL : ν (rawL+n)=xL n := (hkeep _ (by omega)).trans (hreadXL n (by omega))
        have hXR : ν (rawR+n)=xR n := (hkeep _ (by omega)).trans (hreadXR n (by omega))
        have hFL : ν (flagsL+n)=(flagL n : ℤ) := (hkeep _ (by omega)).trans (hreadFL n (by omega))
        have hFR : ν (flagsR+n)=(flagR n : ℤ) := (hkeep _ (by omega)).trans (hreadFR n (by omega))
        light_set (n : ℕ) using LightReportingLeaf.time,LightReportingBucketTest.time,LightReportingBucketPairs.time,residueBudget
        light_set (xL n) using hXL,LightReportingLeaf.time,LightReportingBucketTest.time,LightReportingBucketPairs.time,residueBudget
        light_set (xR n) using hXR,LightReportingLeaf.time,LightReportingBucketTest.time,LightReportingBucketPairs.time,residueBudget
        light_set (flagL n : ℕ) using hFL,LightReportingLeaf.time,LightReportingBucketTest.time,LightReportingBucketPairs.time,residueBudget
        light_set (flagR n : ℕ) using hFR,LightReportingLeaf.time,LightReportingBucketTest.time,LightReportingBucketPairs.time,residueBudget
        have hleaf := (LightReportingLeaf.program_meets (μ := ν) (d := d+1) (srcL := srcL) (srcR := srcR)
          a (xL n) (xR n) left right keyL keyR HLν HRν hw (by omega) hMo
          hsrcL hsrcR hoffsetsL hoffsetsR hflatL hflatR hspace hword hkeyL hkeyR hfL hfR
          (fun i hi => (hkeep _ (by omega)).trans (hreadL i hi))
          (fun i hi => (hkeep _ (by omega)).trans (hreadR i hi))
          hvaluesL hvaluesR ha htarget (hxL n (by omega)) (hxR n (by omega)) hcountWord).append [body 6 5]
        light_call hleaf using LightReportingLeaf.time,LightReportingBucketTest.time,LightReportingBucketPairs.time,residueBudget
          with found ν₂ ⟨hfoundBool,hfound,hkeepLeaf⟩
        have hprevRange : 0≤prev ∧ prev≤1 := by rcases hprevBool with h | h <;> omega
        have hfoundRange : 0≤found ∧ found≤1 := by rcases hfoundBool with h | h <;> omega
        have hwhole : Kept μ ν₂ work := fun i hi => (hkeepLeaf i hi).trans (hkeep i hi)
        have hsum : (0 : ℤ)<prev+found ↔ Hit a xL xR left right keyL keyR flagL flagR NL NR Mo (n+1) := by
          rw [hit_succ]
          rw [show (0 : ℤ)<prev+found ↔ prev=1 ∨ found=1 by omega,hprev,hfound]
        light_if hfoundSome hfoundNone : (0 : ℤ)<prev+found
          using LightReportingLeaf.time,LightReportingBucketTest.time,LightReportingBucketPairs.time,residueBudget
        · have htrue := hsum.mp hfoundSome
          light_set (1 : ℕ) using LightReportingLeaf.time,LightReportingBucketTest.time,LightReportingBucketPairs.time,residueBudget
          exact ⟨by simp,by simpa using htrue,hwhole⟩
        · have hfalse : ¬Hit a xL xR left right keyL keyR flagL flagR NL NR Mo (n+1) :=
            fun hh => hfoundNone (hsum.mpr hh)
          light_set (0 : ℕ) using LightReportingLeaf.time,LightReportingBucketTest.time,LightReportingBucketPairs.time,residueBudget
          exact ⟨by simp,by simp [hfalse],hwhole⟩
      · omega

end ThreeSum.LightReportingLeafBatch
