import Submission.ThreeSum.LightLocalCoverHost
import Submission.ThreeSum.LightSubsetEnumerationSetup
import Submission.ThreeSum.LightMaskBitTable

/-!
# A complete local-cover construction from the initialized parameters

The enumerated local vertices and their Boolean coordinate rows are built
inside this program. It then constructs all candidate tables, executes the
original greedy schedule, and gathers the exact occurrence coefficient
rows. There are no supplied mask, coefficient, histogram, or matrix tables.
-/

namespace ThreeSum.LightLocalCoverBuild

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables

set_option maxHeartbeats 1500000
set_option maxRecDepth 6000

def body (pEnum pBits pHost : ℕ) : Stmt :=
  .call pEnum [v 0,v 1,v 6,v 14] 17 ;;
  .call pBits [v 0,v 6,v 7,v 4,v 14] 17 ;;
  .call pHost [v 0,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16] 0

def time (h : ℕ) : ℕ := LightSubsetEnumerationSetup.time (512*h) h+
  LightMaskBitTable.time (512*h) (LocalMaskGraph.vertexCount (512*h) h)+
  LightLocalCoverHost.time h+200

def word (h : ℕ) : ℕ := LightLocalCoverHost.word h+2^(512*h+1)

structure Procs (P : Program) (pMain : ℕ) where
  pEnum : ℕ
  pPowers : ℕ
  pEnumRec : ℕ
  pBits : ℕ
  pOneBits : ℕ
  pErase : ℕ
  pHost : ℕ
  enum : P[pEnum]? = some (LightSubsetEnumerationSetup.body pPowers pEnumRec)
  powers : P[pPowers]? = some powTableBody
  enumRec : P[pEnumRec]? = some (LightSubsetEnumeration.body pEnumRec)
  bits : P[pBits]? = some (LightMaskBitTable.body pOneBits)
  oneBits : P[pOneBits]? = some (LightMaskBits.body pPowers pErase)
  erase : P[pErase]? = some (LightMaskErase.body pErase)
  host : LightLocalCoverHost.Procs P pHost
  main : P[pMain]? = some (body pEnum pBits pHost)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {h masks bitPtr maps raw0 raw1 hist0 hist1 matrixPtr work scheduleMaps : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+7 ≤ lim.depth)
    (hspace : LightLocalCoverCandidate.space work (512*h)
      (LocalMaskGraph.vertexCount (512*h) h) (localPrime h) ≤ lim.space)
    (hmasks : masks+LocalMaskGraph.vertexCount (512*h) h ≤ bitPtr)
    (hbits : bitPtr+LocalMaskGraph.vertexCount (512*h) h*(512*h) ≤ maps)
    (hmaps : maps+rows h*(2*(512*h)) ≤ raw0)
    (hraw0 : raw0+2*LocalMaskGraph.vertexCount (512*h) h ≤ raw1)
    (hraw1 : raw1+2*LocalMaskGraph.vertexCount (512*h) h ≤ hist0)
    (hhist0 : hist0+rows h*localPrime h ≤ hist1)
    (hhist1 : hist1+rows h*localPrime h ≤ matrixPtr)
    (hmatrix : matrixPtr+rows h*cols h ≤ work)
    (hschedule : work+LightCoverGreedy.total (rows h) (cols h) (scheduleSize h) ≤ scheduleMaps)
    (houtSpace : scheduleMaps+scheduleSize h*(2*(512*h)) ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d
      [512*h,h,localPrime h,rows h,LocalMaskGraph.vertexCount (512*h) h,localBucketCap h,
        masks,bitPtr,maps,raw0,raw1,hist0,hist1,matrixPtr,work,scheduleSize h,scheduleMaps]
      μ (time h)
      (fun r ν => r = (scheduleMaps : ℤ) ∧
        Data ν h maps hist0 hist1 matrixPtr ∧ ScheduleRows ν h scheduleMaps ∧
        (∀ s : Occurrence h,
          ν (LightCoverGreedy.out work (rows h) (cols h)+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν masks) := by
  have hwork : work ≤ lim.space := by unfold LightLocalCoverCandidate.space at hspace; omega
  have hpowSpace : work+(512*h+1) ≤ lim.space := by
    unfold LightLocalCoverCandidate.space at hspace
    omega
  have hmaskWork : masks+LocalMaskGraph.vertexCount (512*h) h ≤ work := by omega
  have hbitsWork : bitPtr+LocalMaskGraph.vertexCount (512*h) h*(512*h) ≤ work := by omega
  have hhostWord : (LightLocalCoverHost.word h : ℤ) ≤ lim.word := by
    have hb : LightLocalCoverHost.word h ≤ word h := Nat.le_add_right ..
    exact (Int.ofNat_le.mpr hb).trans hword
  have hpowerWord : ((2^(512*h+1) : ℕ) : ℤ) ≤ lim.word := by
    have hb : 2^(512*h+1) ≤ word h := Nat.le_add_left ..
    exact (Int.ofNat_le.mpr hb).trans hword
  have hbudget (x : ℕ) (hx : x ≤ LightLocalCoverHost.word h) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hhostWord
  have hLWord := hbudget (512*h) (by unfold LightLocalCoverHost.word LightWeightGather.word; omega)
  have hhWord : (h : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : h ≤ 512*h)).trans hLWord
  have hnWord := hbudget (LocalMaskGraph.vertexCount (512*h) h) (by
    unfold LightLocalCoverHost.word LightLocalCoverCandidate.word LightPairFlags.word
    omega)
  have hpWord := hbudget (localPrime h) (by
    unfold LightLocalCoverHost.word LightLocalCoverCandidate.word LightPairFlags.word
    omega)
  have hcapWord := hbudget (localBucketCap h) (by
    unfold LightLocalCoverHost.word LightLocalCoverCandidate.word LightPairFlags.word
    omega)
  have hNWord := hbudget (rows h) (by unfold LightLocalCoverHost.word LightWeightGather.word; omega)
  have hTWord := hbudget (scheduleSize h) (by unfold LightLocalCoverHost.word LightWeightGather.word; omega)
  apply Meets.of_body S.main
  unfold body time
  have he := LightSubsetEnumerationSetup.meets (d := d+1) (μ := μ) (L := 512*h) (k := h)
    (dst := masks) (work := work) S.enum S.powers S.enumRec hw hpowSpace hpowerWord
    (by omega) hmaskWork (by omega)
  light_call he using time with ve μ₁ ⟨hve,hmaskSeg,hpowers,hkeep₁⟩
  have hmaskRead₁ : ∀ i < LocalMaskGraph.vertexCount (512*h) h,
      μ₁ (masks+i) = (LocalMaskGraph.maskAt (512*h) h i : ℤ) := by
    intro i hi
    have hi' : i < (SubsetAddress.enumerateLayer (512*h) h).length := by
      simpa only [SubsetAddress.enumerateLayer_length,LocalMaskGraph.vertexCount] using hi
    have he := hmaskSeg i (by simpa only [List.length_map] using hi')
    simpa only [LocalMaskGraph.maskAt,List.getD_eq_getElem _ _ hi',List.getElem_map] using he
  have hmaskLt : ∀ i < LocalMaskGraph.vertexCount (512*h) h,
      LocalMaskGraph.maskAt (512*h) h i < 2^(512*h) := fun _ hi => (LocalMaskGraph.maskAt_spec hi).1
  have hb := LightMaskBitTable.meets (d := d+1) (μ := μ₁) (L := 512*h) (masks := masks)
    (dst := bitPtr) (n := LocalMaskGraph.vertexCount (512*h) h) (work := work)
    S.bits S.oneBits S.powers S.erase (LocalMaskGraph.maskAt (512*h) h)
    hw (by omega) hpowSpace hmasks hbitsWork hpowerWord hmaskRead₁ hmaskLt
  light_call hb using time with vb μ₂ ⟨hbitsRead,hkeep₂⟩
  have hmaskRead₂ : ∀ i < LocalMaskGraph.vertexCount (512*h) h,
      μ₂ (masks+i) = (LocalMaskGraph.maskAt (512*h) h i : ℤ) := by
    intro i hi
    rw [hkeep₂ _ ⟨by omega,Or.inl (by omega)⟩]
    exact hmaskRead₁ i hi
  have hh := S.host.meets (d := d+1) (μ := μ₂) (h := h) (masks := masks) (bitPtr := bitPtr)
    (maps := maps) (raw0 := raw0) (raw1 := raw1) (hist0 := hist0) (hist1 := hist1)
    (matrixPtr := matrixPtr) (work := work) (scheduleMaps := scheduleMaps)
    hw (by omega) hspace (by omega) hbits hmaps hraw0 hraw1 hhist0 hhist1 hmatrix hschedule houtSpace
    hhostWord hmaskRead₂ hbitsRead
  light_call hh using time with vh μ₃ ⟨hvh,hdata,hrows,hselection,hkeep₃⟩
  refine ⟨hvh,hdata,hrows,hselection,?_⟩
  intro a ha
  change μ₃ a = μ a
  rw [hkeep₃ a (by omega),hkeep₂ a ⟨by omega,Or.inl (by omega)⟩]
  exact hkeep₁ a ⟨by omega,Or.inl ha⟩

def program : Program :=
  [body 28 30 1,LightLocalCoverHost.body 2 21 26,LightLocalCoverMatrix.body 3,
    LightLocalCoverCandidate.body 4 9 16,LightWeightDecode.body 5 6,powTableBody,
    LightWeightRow.body 7,LightRadixDigit.body 8,LightSmallDivide.body,
    LightHashHistogram.body 10 12 14,LightMaskHashes.body 5 11,LightOneHot.body 11,
    LightResidues.residuesBody 13,emodBody,LightHistogram.histogramBody 15,fillBody,
    LightLocalCoverRow.body 17 20,LightPairFlags.body 8 18 19,LightBooleanDot.body,
    LightTrimTest.body,LightSupportMark.body 15,LightCoverGreedy.body 15 22 25,
    LightCoverSelect.body 23 24,LightCoverScores.body 18,LightMinimum.body,LightCoverUpdate.body,
    LightWeightGather.body 27,copyBody,LightSubsetEnumerationSetup.body 5 29,
    LightSubsetEnumeration.body 29,LightMaskBitTable.body 31,LightMaskBits.body 5 32,
    LightMaskErase.body 32]

def programProcs : Procs program 0 :=
  ⟨28,5,29,30,31,32,1,rfl,rfl,rfl,rfl,rfl,rfl,
    ⟨2,21,26,⟨3,⟨4,9,16,⟨5,6,7,8,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨10,5,11,12,13,14,15,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨17,8,18,19,20,15,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,
      ⟨15,22,25,rfl,⟨23,18,24,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,⟨27,rfl,rfl⟩,rfl⟩,rfl⟩

end ThreeSum.LightLocalCoverBuild
