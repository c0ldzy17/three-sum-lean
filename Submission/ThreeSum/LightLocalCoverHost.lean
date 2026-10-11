import Submission.ThreeSum.LightLocalCoverTables
import Submission.ThreeSum.LightWeightGather

/-!
# Constructing the exact local schedule and its retained tables

This fixed program constructs every candidate table, executes the unchanged
first-maximum greedy routine, and gathers the selected coefficient rows.
Its output contains the original schedule maps in exact occurrence order,
including ties and repetitions, and retains both candidate count tables.
-/

namespace ThreeSum.LightLocalCoverHost

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables

set_option maxHeartbeats 2000000
set_option maxRecDepth 6000

def body (pMatrix pGreedy pGather : ℕ) : Stmt :=
  .call pMatrix [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13] 16 ;;
  .set 17 (v 1 *' v 1) ;;
  .call pGreedy [v 12,v 13,v 2,v 17,v 14] 16 ;;
  .set 18 (k 2 *' v 0) ;;
  .call pGather [v 16,v 7,v 15,v 14,v 18] 16 ;;
  .set 0 (v 15)

def time (h : ℕ) : ℕ :=
  LightLocalCoverMatrix.time (512*h) (LocalMaskGraph.vertexCount (512*h) h) (localPrime h) (rows h)+
  LightCoverGreedy.time (rows h) (cols h) (scheduleSize h)+
  LightWeightGather.time (scheduleSize h) (2*(512*h))+200

def word (h : ℕ) : ℕ :=
  LightLocalCoverCandidate.word (512*h) (LocalMaskGraph.vertexCount (512*h) h)
    (localPrime h) (localBucketCap h) (rows h)+
  LightWeightGather.word (rows h) (scheduleSize h) (2*(512*h))

structure Procs (P : Program) (pMain : ℕ) where
  pMatrix : ℕ
  pGreedy : ℕ
  pGather : ℕ
  matrix : LightLocalCoverMatrix.Procs P pMatrix
  greedy : LightCoverGreedy.Procs P pGreedy
  gather : LightWeightGather.Procs P pGather
  main : P[pMain]? = some (body pMatrix pGreedy pGather)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {h masks bitPtr maps raw0 raw1 hist0 hist1 matrixPtr work scheduleMaps : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+6 ≤ lim.depth)
    (hspace : LightLocalCoverCandidate.space work (512*h)
      (LocalMaskGraph.vertexCount (512*h) h) (localPrime h) ≤ lim.space)
    (hmasks : masks+LocalMaskGraph.vertexCount (512*h) h ≤ maps)
    (hbits : bitPtr+LocalMaskGraph.vertexCount (512*h) h*(512*h) ≤ maps)
    (hmaps : maps+rows h*(2*(512*h)) ≤ raw0)
    (hraw0 : raw0+2*LocalMaskGraph.vertexCount (512*h) h ≤ raw1)
    (hraw1 : raw1+2*LocalMaskGraph.vertexCount (512*h) h ≤ hist0)
    (hhist0 : hist0+rows h*localPrime h ≤ hist1)
    (hhist1 : hist1+rows h*localPrime h ≤ matrixPtr)
    (hmatrix : matrixPtr+rows h*cols h ≤ work)
    (hschedule : work+LightCoverGreedy.total (rows h) (cols h) (scheduleSize h) ≤ scheduleMaps)
    (houtSpace : scheduleMaps+scheduleSize h*(2*(512*h)) ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < LocalMaskGraph.vertexCount (512*h) h,
      μ (masks+i) = (LocalMaskGraph.maskAt (512*h) h i : ℤ))
    (hbitsRead : ∀ i < LocalMaskGraph.vertexCount (512*h) h, ∀ j < 512*h,
      μ (bitPtr+i*(512*h)+j) = (LocalCoverMatrix.bits (512*h) h i j : ℤ)) :
    Meets lim P pMain d
      [512*h,localPrime h,rows h,LocalMaskGraph.vertexCount (512*h) h,localBucketCap h,
        masks,bitPtr,maps,raw0,raw1,hist0,hist1,matrixPtr,work,scheduleSize h,scheduleMaps]
      μ (time h)
      (fun r ν => r = (scheduleMaps : ℤ) ∧
        Data ν h maps hist0 hist1 matrixPtr ∧ ScheduleRows ν h scheduleMaps ∧
        (∀ s : Occurrence h,
          ν (LightCoverGreedy.out work (rows h) (cols h)+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν maps) := by
  have hwork : work ≤ lim.space := by unfold LightLocalCoverCandidate.space at hspace; omega
  have hscheduleWork : work ≤ scheduleMaps := by omega
  have hbudget (x : ℕ) (hx : x ≤ word h) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hmatrixWord := hbudget
    (LightLocalCoverCandidate.word (512*h) (LocalMaskGraph.vertexCount (512*h) h)
      (localPrime h) (localBucketCap h) (rows h)) (by unfold word; omega)
  have hgatherWord := hbudget
    (LightWeightGather.word (rows h) (scheduleSize h) (2*(512*h))) (by unfold word; omega)
  have hLWord := hbudget (512*h) (by unfold word LightWeightGather.word; omega)
  have hWWord := hbudget (2*(512*h)) (by unfold word LightWeightGather.word; omega)
  have hWWordZ : (2 : ℤ)*(512*(h : ℤ)) ≤ lim.word := by exact_mod_cast hWWord
  have h2Word := hbudget 2 (by
    unfold word LightLocalCoverCandidate.word LightPairFlags.word
    omega)
  have hpWord := hbudget (localPrime h) (by
    unfold word LightLocalCoverCandidate.word LightPairFlags.word
    omega)
  have hp2Word := hbudget (localPrime h*localPrime h) (by
    unfold word LightLocalCoverCandidate.word LightPairFlags.word
    omega)
  have hp2WordZ : (localPrime h : ℤ)*localPrime h ≤ lim.word := by exact_mod_cast hp2Word
  have hNWord := hbudget (rows h) (by unfold word LightWeightGather.word; omega)
  have hTWord := hbudget (scheduleSize h) (by unfold word LightWeightGather.word; omega)
  have hnWord := hbudget (LocalMaskGraph.vertexCount (512*h) h) (by
    unfold word LightLocalCoverCandidate.word LightPairFlags.word
    omega)
  have hcapWord := hbudget (localBucketCap h) (by
    unfold word LightLocalCoverCandidate.word LightPairFlags.word
    omega)
  have hn : 0 < LocalMaskGraph.vertexCount (512*h) h := Nat.choose_pos (by omega)
  have hmapsWork : maps+rows h*(2*(512*h)) ≤ work := by omega
  have hhist0Work : hist0+rows h*localPrime h ≤ work := by omega
  have hhist1Work : hist1+rows h*localPrime h ≤ work := by omega
  have hgreedySpace : work+LightCoverGreedy.total (rows h) (cols h) (scheduleSize h) ≤ lim.space := by omega
  have houtEnd : LightCoverGreedy.out work (rows h) (cols h)+scheduleSize h ≤ scheduleMaps := by
    unfold LightCoverGreedy.out LightCoverGreedy.total at *
    omega
  have hm := S.matrix.meets (d := d+1) (μ := μ) (L := 512*h)
    (n := LocalMaskGraph.vertexCount (512*h) h) (p := localPrime h) (cap := localBucketCap h)
    (N := rows h) (masks := masks) (bitPtr := bitPtr) (maps := maps) (raw0 := raw0)
    (raw1 := raw1) (hist0 := hist0) (hist1 := hist1) (dst := matrixPtr) (work := work)
    (LocalMaskGraph.maskAt (512*h) h) (LocalCoverMatrix.bits (512*h) h)
    (fun j => LocalMaskHashes.coeff false (candidate h j))
    (fun j => LocalMaskHashes.coeff true (candidate h j))
    hw (by omega) (localPrime_pos h) hn hspace hmasks hbits hmaps hraw0 hraw1 hhist0 hhist1
    hmatrix hmatrixWord hmaskRead (fun _ hi => (LocalMaskGraph.maskAt_spec hi).1) hbitsRead
    (fun i _ j _ => LightMaskBits.bit_le (512*h) (LocalMaskGraph.maskAt (512*h) h i) j)
    (by intro j _ i hi; simpa only [Bool.false_eq_true,ite_false,Nat.add_zero] using coeff_digit h j false ⟨i,hi⟩)
    (by intro j _ i hi; simpa only [ite_true] using coeff_digit h j true ⟨i,hi⟩)
  apply Meets.of_body S.main
  unfold body time
  light_call hm using time with vm μ₁ ⟨hdata₁,hkeep₁⟩
  have H₁ : Data μ₁ h maps hist0 hist1 matrixPtr := hdata₁
  light_set (localPrime h*localPrime h : ℕ) using time
  have hg := S.greedy.meets (d := d+1) (μ := μ₁) (src := matrixPtr) (activePtr := work)
    (rows := rows h) (cols := cols h) (rounds := scheduleSize h) (LightLocalCoverSchedule.matrix h)
    hw (by omega) (rows_pos h) hmatrix hgreedySpace
    (fun _ hi _ hr => H₁.matrix_read hi hr) (fun _ _ _ _ => LocalCoverMatrix.entry_le ..) (by omega)
  light_call hg using time,cols with vg μ₂ ⟨hvg,hchoices,hactive,hkeep₂⟩
  have H₂ : Data μ₂ h maps hist0 hist1 matrixPtr :=
    H₁.of_kept (fun a ha => hkeep₂ a (Or.inl ha)) hmapsWork hhist0Work hhist1Work hmatrix
  have hselection : ∀ s < scheduleSize h,
      μ₂ (LightCoverGreedy.out work (rows h) (cols h)+s) = ((indices h).getD s 0 : ℤ) := by
    intro s hs
    have hs' : s < (indices h).length := by rw [indices_length]; exact hs
    have hr := hchoices s (by simpa only [List.length_map,BooleanGreedy.choices_length] using hs)
    rw [List.getD_eq_getElem _ _ hs']
    simpa only [List.getElem_map,indices] using hr
  have hselectionLt : ∀ s < scheduleSize h, (indices h).getD s 0 < rows h := by
    intro s hs
    exact candidateAt_lt h ⟨s,hs⟩
  light_set (2*(512*h) : ℕ) using time
  have hc := S.gather.meets (d := d+1) (μ := μ₂)
    (indices := LightCoverGreedy.out work (rows h) (cols h)) (src := maps) (dst := scheduleMaps)
    (N := rows h) (rows := scheduleSize h) (width := 2*(512*h)) (fun s => (indices h).getD s 0)
    hw (by omega) houtEnd (by omega) houtSpace hgatherWord hselectionLt hselection
  light_call hc using time,hvg,LightCoverGreedy.out,cols with vc μ₃ ⟨hcopy,hkeep₃⟩
  have H₃ : Data μ₃ h maps hist0 hist1 matrixPtr :=
    H₂.of_kept (fun a ha => hkeep₃ a (Or.inl (by omega))) hmapsWork hhist0Work hhist1Work hmatrix
  have hrows₃ : ScheduleRows μ₃ h scheduleMaps := H₂.gathered_schedule hcopy
  have hselection₃ : ∀ s : Occurrence h,
      μ₃ (LightCoverGreedy.out work (rows h) (cols h)+s.val) = (candidateAt h s : ℤ) := by
    intro s
    rw [hkeep₃ _ (Or.inl (by have hs := s.isLt; omega))]
    exact hselection s.val s.isLt
  light_set (scheduleMaps : ℕ) using time
  refine ⟨rfl,H₃,hrows₃,hselection₃,?_⟩
  intro a ha
  change μ₃ a = μ a
  rw [hkeep₃ a (Or.inl (by omega)),hkeep₂ a (Or.inl (by omega))]
  exact hkeep₁ a ha

def program : Program :=
  [body 1 20 25,LightLocalCoverMatrix.body 2,LightLocalCoverCandidate.body 3 8 15,
    LightWeightDecode.body 4 5,powTableBody,LightWeightRow.body 6,LightRadixDigit.body 7,
    LightSmallDivide.body,LightHashHistogram.body 9 11 13,LightMaskHashes.body 4 10,
    LightOneHot.body 10,LightResidues.residuesBody 12,emodBody,LightHistogram.histogramBody 14,
    fillBody,LightLocalCoverRow.body 16 19,LightPairFlags.body 7 17 18,LightBooleanDot.body,
    LightTrimTest.body,LightSupportMark.body 14,LightCoverGreedy.body 14 21 24,
    LightCoverSelect.body 22 23,LightCoverScores.body 17,LightMinimum.body,LightCoverUpdate.body,
    LightWeightGather.body 26,copyBody]

def programProcs : Procs program 0 :=
  ⟨1,20,25,⟨2,⟨3,8,15,⟨4,5,6,7,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨9,4,10,11,12,13,14,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨16,7,17,18,19,14,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,
    ⟨14,21,24,rfl,⟨22,17,23,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,⟨26,rfl,rfl⟩,rfl⟩

end ThreeSum.LightLocalCoverHost
