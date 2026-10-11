import Submission.ThreeSum.ReportingHostBucketTest

/-!
# Actual independent bucket selection followed by original tuple testing

The host reads the two retained offset headers, applies each endpoint's
independent flag, and runs the exact original-value Cartesian scanner. Its
time is linear in the actual selected physical pair mass plus a constant.
-/

namespace ThreeSum.LightReportingBucketTest

open Light SourceBuckets LightHistogram LightSourceBucketSelect ReportingHostBucketTest

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def body (pSelect pPairs : ℕ) : Stmt :=
  .call pSelect [v 3,v 4,v 5,v 6,v 14,v 13,v 11] 15 ;;
  .call pSelect [v 7,v 8,v 9,v 10,v 14 +' k 2,v 13,v 12] 15 ;;
  .set 16 (M (v 14)) ;;
  .set 17 (M (v 14 +' k 1)) ;;
  .set 18 (M (v 14 +' k 2)) ;;
  .set 19 (M (v 14 +' k 3)) ;;
  .call pPairs [v 0,v 1,v 2,v 16,v 18,v 17,v 19,v 11,v 12] 0

def program : Program :=
  [LightSourceBucketSelect.body,LightReportingBucketRow.body,
    LightReportingBucketPairs.body 1,body 0 2]

def time (keyL keyR : ℕ → ℕ) (NL NR rL rR flagL flagR : ℕ) : ℕ :=
  LightReportingBucketPairs.time (countSelected keyL NL rL flagL) (countSelected keyR NR rR flagR)+600

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pSelect pPairs pRow srcL srcR offsetsL offsetsR flatL flatR NL NR M rL rR flagL flagR work : ℕ}
    {μ : ℕ → ℤ}
    (hmain : P[pMain]?=some (body pSelect pPairs))
    (hselect : P[pSelect]?=some LightSourceBucketSelect.body)
    (hpairs : P[pPairs]?=some (LightReportingBucketPairs.body pRow))
    (hrow : P[pRow]?=some LightReportingBucketRow.body)
    (a : ℤ) (left right : ℕ → ℤ) (keyL keyR : ℕ → ℕ)
    (HL : Stored μ keyL NL M offsetsL flatL) (HR : Stored μ keyR NR M offsetsR flatR)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 ≤ lim.depth)
    (hsrcL : srcL+NL ≤ work) (hsrcR : srcR+NR ≤ work)
    (hoffsetsL : offsetsL+M+1 ≤ work) (hoffsetsR : offsetsR+M+1 ≤ work)
    (hflatL : flatL+NL ≤ work) (hflatR : flatR+NR ≤ work) (hspace : work+4 ≤ lim.space)
    (hkeyL : ∀ i < NL, keyL i<M) (hkeyR : ∀ j < NR, keyR j<M)
    (hrL : rL<M) (hrR : rR<M) (hflagL : flagL≤1) (hflagR : flagR≤1)
    (hreadL : ∀ i < NL, μ (srcL+i)=left i) (hreadR : ∀ j < NR, μ (srcR+j)=right j)
    (hvaluesL : ∀ i < NL, |left i|≤lim.word) (hvaluesR : ∀ j < NR, |right j|≤lim.word)
    (ha : |a|≤lim.word) (htarget : ∀ i < NL, |a+left i|≤lim.word)
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    Meets lim P pMain d [a,srcL,srcR,offsetsL,flatL,rL,flagL,offsetsR,flatR,rR,flagR,NL,NR,M,work]
      μ (time keyL keyR NL NR rL rR flagL flagR)
      (fun r ν => r=(testCount μ a left right keyL keyR NL NR flatL flatR rL rR flagL flagR : ℤ) ∧
        SameOutside μ ν work 4) := by
  let startL := offset keyL NL rL
  let startR := offset keyR NR rR
  let nL := countSelected keyL NL rL flagL
  let nR := countSelected keyR NR rR flagR
  have hendL : startL+nL≤NL := selected_end hkeyL hrL
  have hendR : startR+nR≤NR := selected_end hkeyR hrR
  have haBounds := abs_le.mp ha
  have hselectedWord : ((nL*nR : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.mul_le_mul (by omega) (by omega))).trans hcountWord
  apply Meets.of_body hmain
  unfold body time
  light_call (LightSourceBucketSelect.meets (d := d+1) hselect HL hw hoffsetsL hflatL (by omega)
    hkeyL hrL hflagL) using LightReportingBucketPairs.time
    with unused μ₁ ⟨hptrL,hlenL,hkeepL⟩
  have HR₁ : Stored μ₁ keyR NR M offsetsR flatR := by
    constructor
    · intro r hr
      exact (hkeepL _ (Or.inl (by omega))).trans (HR.offsets r hr)
    · intro i hi
      have hpos := position_lt hkeyR hi
      exact (hkeepL _ (Or.inl (by omega))).trans (HR.indices i hi)
  light_call (LightSourceBucketSelect.meets (d := d+1) (dst := work+2) hselect HR₁ hw
    (by omega) (by omega) (by omega) hkeyR hrR hflagR) using LightReportingBucketPairs.time
    with unused μ₂ ⟨hptrR,hlenR,hkeepR⟩
  have hkeepBelow (i : ℕ) (hi : i<work) : μ₂ i=μ i :=
    (hkeepR i (Or.inl (by omega))).trans (hkeepL i (Or.inl hi))
  have hptrL' : μ₂ work=((flatL+startL : ℕ) : ℤ) :=
    (hkeepR work (Or.inl (by omega))).trans hptrL
  have hlenL' : μ₂ (work+1)=(nL : ℤ) :=
    (hkeepR (work+1) (Or.inl (by omega))).trans hlenL
  change μ₂ (work+2)=((flatR+startR : ℕ) : ℤ) at hptrR
  change μ₂ (work+2+1)=(nR : ℤ) at hlenR
  have hlenR' : μ₂ (work+3)=(nR : ℤ) := by simpa only [Nat.add_assoc] using hlenR
  have hptrRZ : μ₂ (((work : ℤ)+2).toNat)=((flatR+startR : ℕ) : ℤ) := by
    rw [show ((work : ℤ)+2).toNat=work+2 by omega]
    exact hptrR
  have hlenRZ : μ₂ (((work : ℤ)+3).toNat)=(nR : ℤ) := by
    rw [show ((work : ℤ)+3).toNat=work+3 by omega]
    exact hlenR'
  light_set (flatL+startL : ℕ) using hptrL',LightReportingBucketPairs.time
  light_set (nL : ℕ) using hlenL',LightReportingBucketPairs.time
  light_set (flatR+startR : ℕ) using hptrRZ,LightReportingBucketPairs.time
  light_set (nR : ℕ) using hlenRZ,LightReportingBucketPairs.time
  have hreadIL (i : ℕ) (hi : i<nL) :
      μ₂ (flatL+startL+i)=(index μ flatL keyL NL rL i : ℤ) :=
    (hkeepBelow _ (by omega)).trans (selected_read HL hkeyL hrL hi).2
  have hreadIR (i : ℕ) (hi : i<nR) :
      μ₂ (flatR+startR+i)=(index μ flatR keyR NR rR i : ℤ) :=
    (hkeepBelow _ (by omega)).trans (selected_read HR hkeyR hrR hi).2
  have hrun := LightReportingBucketPairs.meets (d := d+1) (μ := μ₂)
    (indicesL := flatL+startL) (indicesR := flatR+startR) hpairs hrow a left right
    (index μ flatL keyL NL rL) (index μ flatR keyR NR rR) hw (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (fun _ hi => (selected_read HL hkeyL hrL hi).1)
    (fun _ hi => (selected_read HR hkeyR hrR hi).1) hreadIL hreadIR
    (fun i hi => (hkeepBelow _ (by omega)).trans (hreadL i hi))
    (fun i hi => (hkeepBelow _ (by omega)).trans (hreadR i hi))
    hvaluesL hvaluesR ha htarget hselectedWord
  light_call hrun using LightReportingBucketPairs.time,startL,startR,nL,nR
    with found ν ⟨hfound,hmem⟩
  subst ν
  refine ⟨hfound,?_⟩
  intro i hi
  exact (hkeepR i (by rcases hi with hi | hi <;> omega)).trans
    (hkeepL i (by rcases hi with hi | hi <;> omega))

theorem program_meets {srcL srcR offsetsL offsetsR flatL flatR NL NR M rL rR flagL flagR work : ℕ}
    {μ : ℕ → ℤ} (a : ℤ) (left right : ℕ → ℤ) (keyL keyR : ℕ → ℕ)
    (HL : Stored μ keyL NL M offsetsL flatL) (HR : Stored μ keyR NR M offsetsR flatR)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2≤lim.depth)
    (hsrcL : srcL+NL≤work) (hsrcR : srcR+NR≤work)
    (hoffsetsL : offsetsL+M+1≤work) (hoffsetsR : offsetsR+M+1≤work)
    (hflatL : flatL+NL≤work) (hflatR : flatR+NR≤work) (hspace : work+4≤lim.space)
    (hkeyL : ∀ i<NL, keyL i<M) (hkeyR : ∀ j<NR, keyR j<M)
    (hrL : rL<M) (hrR : rR<M) (hflagL : flagL≤1) (hflagR : flagR≤1)
    (hreadL : ∀ i<NL, μ (srcL+i)=left i) (hreadR : ∀ j<NR, μ (srcR+j)=right j)
    (hvaluesL : ∀ i<NL, |left i|≤lim.word) (hvaluesR : ∀ j<NR, |right j|≤lim.word)
    (ha : |a|≤lim.word) (htarget : ∀ i<NL, |a+left i|≤lim.word)
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    Meets lim program 3 d [a,srcL,srcR,offsetsL,flatL,rL,flagL,offsetsR,flatR,rR,flagR,NL,NR,M,work]
      μ (time keyL keyR NL NR rL rR flagL flagR)
      (fun r ν => r=(testCount μ a left right keyL keyR NL NR flatL flatR rL rR flagL flagR : ℤ) ∧
        SameOutside μ ν work 4) :=
  meets rfl rfl rfl rfl a left right keyL keyR HL HR hw hd hsrcL hsrcR hoffsetsL hoffsetsR
    hflatL hflatR hspace hkeyL hkeyR hrL hrR hflagL hflagR hreadL hreadR hvaluesL hvaluesR ha htarget hcountWord

theorem time_eq (keyL keyR : ℕ → ℕ) (NL NR rL rR flagL flagR : ℕ) :
    time keyL keyR NL NR rL rR flagL flagR =
      240*(countSelected keyL NL rL flagL*countSelected keyR NR rR flagR)+700 := by
  unfold time LightReportingBucketPairs.time
  ring

end ThreeSum.LightReportingBucketTest
