import Submission.ThreeSum.ReportingHostTerminalFrontier

/-!
# Executed terminal iteration over the retained prefix arrays

The recursion reads the two aligned prefix masks from retained memory and
runs the complete terminal program for each prefix. Its cost is the sum of
the actual prefix costs. Reused scratch never changes the prefix arrays or
the original source buckets, occurrence rows, and selected cover data.
-/

namespace ThreeSum.LightReportingTerminalFrontier

open Light Finset BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open GlobalEncoding LocalCoverBounds BlockSourceEncoding LightSourceResidues SourceBuckets
open BlockIndexedQuery BlockForced StoredReporting LightBlockQuery
open LightReportingTerminalMasks LightBlockSourceBuild ReportingHostTerminalFrontier

set_option maxHeartbeats 3800000
set_option maxRecDepth 14000

/-- The terminal host's 31 arguments, with arguments 22 and 23 now the
retained prefix-array pointers, followed by the number of prefixes. -/
def body (pSelf pTerminal : ℕ) : Stmt :=
  .ite (k 0 <' v 31)
    (.call pSelf [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,
        v 20,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28,v 29,v 30,v 31 -' k 1] 32 ;;
      .set 33 (v 31 -' k 1) ;;
      .set 34 (M (v 22 +' v 33)) ;;
      .set 35 (M (v 23 +' v 33)) ;;
      .call pTerminal [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,
        v 20,v 21,v 34,v 35,v 24,v 25,v 26,v 27,v 28,v 29,v 30] 36 ;;
      .ite (k 0 <' v 32 +' v 36) (.set 0 (k 1)) (.set 0 (k 0)))
    (.set 0 (k 0))

def program : Program := LightReportingTerminal.program ++ [body 39 38]

variable {lim : Limits}

theorem program_meets {μ : ℕ→ℤ}
    {h J k srcL srcR offsetsL offsetsR flatL flatR NL NR occ maps candidates histL histR inL inR
      masks masksL masksR base bitBase rowOut work n d : ℕ}
    (av : ℤ) (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ)
    (q : GlobalOutput h J) (pres : List (List (Finset (Fin (512*h))))) (hk : k≤J) (hn : n≤pres.length)
    (HL : Stored μ (fun i => key p (modulus h J) 0 (left i)) NL (modulus h J) offsetsL flatL)
    (HR : Stored μ (fun i => key p (modulus h J) shift (right i)) NR (modulus h J) offsetsR flatR)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+n+count h J k+J*(512*h)+10≤lim.depth)
    (hsrcL : srcL+NL≤masks) (hsrcR : srcR+NR≤masks)
    (hoffsetsL : offsetsL+modulus h J+1≤masks) (hoffsetsR : offsetsR+modulus h J+1≤masks)
    (hflatL : flatL+NL≤masks) (hflatR : flatR+NR≤masks)
    (hocc : occ+J≤masks) (hmaps : maps+2*(512*h)*scheduleSize h≤masks)
    (hcandidates : candidates+scheduleSize h≤masks)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h≤masks)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h≤masks)
    (hinL : inL+pres.length≤masks) (hinR : inR+pres.length≤masks)
    (hmasks : masks+count h J k≤masksL) (hmasksL : masksL+count h J k≤masksR)
    (hmasksR : masksR+count h J k≤base)
    (hstop : LightReportingTerminalPreparation.stop base (J*(512*h)) (count h J k)≤bitBase)
    (hbits : bitBase+J*(512*h)≤rowOut) (hrowOut : rowOut+2≤work)
    (hspace : LightReportingTerminal.space work h J≤lim.space)
    (hword : (LightReportingTerminal.word h J : ℤ)≤lim.word)
    (hoccRead : ∀ j<J, μ (occ+j)=(occurrenceIndices (outputOccurrences q) j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR)
    (hreadL : ∀ i<NL, μ (srcL+i)=left i) (hreadR : ∀ j<NR, μ (srcR+j)=right j)
    (hreadInL : ∀ i<pres.length, μ (inL+i)=
      (SubsetAddress.subsetMask (leftPrefix k (prefixRows (J := J) (prefixAt pres i))) : ℤ))
    (hreadInR : ∀ i<pres.length, μ (inR+i)=
      (SubsetAddress.subsetMask (rightPrefix k (outputRows q) (prefixRows (J := J) (prefixAt pres i))) : ℤ))
    (hvaluesL : ∀ i<NL, |left i|≤lim.word) (hvaluesR : ∀ j<NR, |right j|≤lim.word)
    (ha : |av|≤lim.word) (htarget : ∀ i<NL, |av+left i|≤lim.word)
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    Meets lim program 39 d
      [av,srcL,srcR,offsetsL,flatL,offsetsR,flatR,NL,NR,modulus h J,J,512*h,h,localPrime h,localBucketCap h,
        occ,maps,candidates,histL,histR,k,SubsetAddress.subsetMask (querySet k (outputRows q)),
        inL,inR,masks,masksL,masksR,base,bitBase,rowOut,work,n]
      μ (time p shift left right NL NR q k pres n)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ Hit av p shift left right NL NR q k pres n) ∧ Kept μ ν masks) := by
  have hsOther := (le_max_right _ _).trans hspace
  have hsWork : work≤lim.space := by have hh := (le_max_right _ _).trans hsOther; omega
  have hstop' : base+2*(2*(J*(512*h))+4*count h J k+2)≤bitBase := hstop
  have hmaskSpace : masks≤lim.space := by omega
  have htwo : (2 : ℤ)≤lim.word := by omega
  have hpWord : ((2^(J*(512*h)+1) : ℕ) : ℤ)≤lim.word := by
    exact (Int.ofNat_le.mpr (Nat.le_add_left _ _)).trans hword
  have hmaskWord (S : Finset (Fin (J*(512*h)))) : |(SubsetAddress.subsetMask S : ℤ)|≤lim.word := by
    rw [Int.abs_natCast]
    exact (Int.ofNat_le.mpr ((SubsetAddress.subsetMask_isMask S).1.le.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))).trans hpWord
  have hkeyL : ∀ i<NL, key p (modulus h J) 0 (left i)<modulus h J :=
    fun i _ => key_lt (modulus_pos h J) 0 (left i)
  have hkeyR : ∀ i<NR, key p (modulus h J) shift (right i)<modulus h J :=
    fun i _ => key_lt (modulus_pos h J) shift (right i)
  induction n generalizing μ d with
  | zero =>
      apply Meets.of_body (p := 39) (by rfl : program[39]?=some (body 39 38))
      unfold body ReportingHostTerminalFrontier.time
      light_if hbad hno : (0 : ℤ)<0
      · omega
      · light_set (0 : ℕ)
        exact ⟨by simp,by simp [Hit],SameOn.refl⟩
  | succ n ih =>
      apply Meets.of_body (p := 39) (by rfl : program[39]?=some (body 39 38))
      unfold body
      rw [ReportingHostTerminalFrontier.time]
      light_if hyes hbad : (0 : ℤ)<((n+1 : ℕ) : ℤ) using LightReportingTerminal.time
      · have hrun := ih (μ := μ) (d := d+1) (by omega) HL HR (by omega)
          hoccRead hcover hreadL hreadR hreadInL hreadInR
        light_call hrun using LightReportingTerminal.time with prev ν ⟨hprevBool,hprev,hkeep⟩
        have HLν := LightReportingLeaf.stored_of_kept HL hkeyL hoffsetsL hflatL hkeep
        have HRν := LightReportingLeaf.stored_of_kept HR hkeyR hoffsetsR hflatR hkeep
        have hcoverν := hcover.of_kept hkeep hmaps hcandidates hleft hright
        have hLmask : ν (inL+n)=
            (SubsetAddress.subsetMask (leftPrefix k (prefixRows (J := J) (prefixAt pres n))) : ℤ) :=
          (hkeep _ (by omega)).trans (hreadInL n (by omega))
        have hRmask : ν (inR+n)=
            (SubsetAddress.subsetMask (rightPrefix k (outputRows q) (prefixRows (J := J) (prefixAt pres n))) : ℤ) :=
          (hkeep _ (by omega)).trans (hreadInR n (by omega))
        have hLword := abs_le.mp (hmaskWord (leftPrefix k (prefixRows (J := J) (prefixAt pres n))))
        have hRword := abs_le.mp (hmaskWord (rightPrefix k (outputRows q) (prefixRows (J := J) (prefixAt pres n))))
        light_set (n : ℕ) using LightReportingTerminal.time
        light_set (SubsetAddress.subsetMask (leftPrefix k (prefixRows (J := J) (prefixAt pres n))) : ℕ)
          using hLmask,LightReportingTerminal.time
        light_set (SubsetAddress.subsetMask (rightPrefix k (outputRows q) (prefixRows (J := J) (prefixAt pres n))) : ℕ)
          using hRmask,LightReportingTerminal.time
        have hterminal := (LightReportingTerminal.program_meets (μ := ν) (d := d+1)
          (srcL := srcL) (srcR := srcR) (occ := occ) (maps := maps) (candidates := candidates)
          (histL := histL) (histR := histR) (masks := masks) (masksL := masksL) (masksR := masksR)
          (base := base) (bitBase := bitBase) (rowOut := rowOut) (work := work)
          av p shift left right q (prefixAt pres n) hk HLν HRν hw (by omega)
          hsrcL hsrcR hoffsetsL hoffsetsR hflatL hflatR hocc hmaps hcandidates hleft hright
          hmasks hmasksL hmasksR hstop hbits hrowOut hspace hword
          (fun j hj => (hkeep _ (by omega)).trans (hoccRead j hj)) hcoverν
          (fun i hi => (hkeep _ (by omega)).trans (hreadL i hi))
          (fun j hj => (hkeep _ (by omega)).trans (hreadR j hj)) hvaluesL hvaluesR ha htarget hcountWord).append [body 39 38]
        light_call hterminal using LightReportingTerminal.time with found ν₂ ⟨hfoundBool,hfound,hkeepTerminal⟩
        have hprevRange : 0≤prev ∧ prev≤1 := by rcases hprevBool with hh | hh <;> omega
        have hfoundRange : 0≤found ∧ found≤1 := by rcases hfoundBool with hh | hh <;> omega
        have hwhole : Kept μ ν₂ masks := fun i hi => (hkeepTerminal i hi).trans (hkeep i hi)
        have hsum : (0 : ℤ)<prev+found ↔ Hit av p shift left right NL NR q k pres (n+1) := by
          rw [hit_succ]
          rw [show (0 : ℤ)<prev+found ↔ prev=1 ∨ found=1 by omega,hprev,hfound]
        light_if hfoundSome hfoundNone : (0 : ℤ)<prev+found using LightReportingTerminal.time
        · have htrue := hsum.mp hfoundSome
          light_set (1 : ℕ) using LightReportingTerminal.time
          exact ⟨by simp,by simpa using htrue,hwhole⟩
        · have hfalse : ¬Hit av p shift left right NL NR q k pres (n+1) :=
            fun hh => hfoundNone (hsum.mpr hh)
          light_set (0 : ℕ) using LightReportingTerminal.time
          exact ⟨by simp,by simp [hfalse],hwhole⟩
      · omega

end ThreeSum.LightReportingTerminalFrontier
