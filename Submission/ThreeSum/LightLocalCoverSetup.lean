import Submission.ThreeSum.LightLocalCoverLayout
import Submission.ThreeSum.LightNatPower

/-!
# The complete local cover from four scalar graph parameters

Only `h`, the selected prime, the vertex count, the bucket cap, and one
starting address are arguments. The candidate count, original schedule
length, and every table address are computed by this fixed program before
it invokes the fully checked local-cover builder.
-/

namespace ThreeSum.LightLocalCoverSetup

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout

set_option maxHeartbeats 2000000
set_option maxRecDepth 6500

def body (pPower pLog pBuild : ℕ) : Stmt :=
  .set 5 (k 512 *' v 0) ;;
  .set 6 (k 2 *' v 5) ;;
  .call pPower [v 1,v 6] 7 ;;
  .set 8 (v 1 *' v 1) ;;
  .call pLog [v 8] 9 ;;
  .set 10 (k 320 *' (k 2 *' v 0 +' k 1) *' (v 9 +' k 1)) ;;
  .set 11 (v 4 +' v 2) ;;
  .set 12 (v 11 +' v 2 *' v 5) ;;
  .set 13 (v 12 +' v 7 *' v 6) ;;
  .set 14 (v 13 +' k 2 *' v 2) ;;
  .set 15 (v 14 +' k 2 *' v 2) ;;
  .set 16 (v 15 +' v 7 *' v 1) ;;
  .set 17 (v 16 +' v 7 *' v 1) ;;
  .set 18 (v 17 +' v 7 *' v 8) ;;
  .set 19 (v 18 +' v 8 +' v 7 +' v 10) ;;
  .call pBuild [v 5,v 0,v 1,v 7,v 2,v 3,v 4,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 10,v 19] 0

def time (h : ℕ) : ℕ := LightNatPower.time (2*(512*h))+log2Time (cols h)+
  LightLocalCoverBuild.time h+500

def word (h : ℕ) : ℕ := LightLocalCoverBuild.word h+1024+scheduleSize h+rows h+2*cols h+512*h

structure Procs (P : Program) (pMain : ℕ) where
  pPower : ℕ
  pLog : ℕ
  pBuild : ℕ
  power : P[pPower]? = some LightNatPower.body
  log : P[pLog]? = some log2Body
  build : LightLocalCoverBuild.Procs P pBuild
  main : P[pMain]? = some (body pPower pLog pBuild)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {base h : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+8 ≤ lim.depth)
    (hspace : space base h ≤ lim.space) (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h,localPrime h,vertices h,localBucketCap h,base] μ (time h)
      (fun r ν => r = (scheduleMaps base h : ℤ) ∧
        Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) ∧
        ScheduleRows ν h (scheduleMaps base h) ∧
        (∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν base) := by
  have hbudget (x : ℕ) (hx : x ≤ word h) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hbuildWord := hbudget (LightLocalCoverBuild.word h) (by unfold word; omega)
  have h1024Word := hbudget 1024 (by unfold word; omega)
  have hLWord := hbudget (512*h) (by unfold word; omega)
  have hNWord := hbudget (rows h) (by unfold word; omega)
  have hTWord := hbudget (scheduleSize h) (by unfold word; omega)
  have hcolsWord := hbudget (cols h) (by unfold word; omega)
  have hlogWord := hbudget (2*cols h+2) (by unfold word; omega)
  have hhostLe : LightLocalCoverHost.word h ≤ word h := by
    have hfirst : LightLocalCoverHost.word h ≤ LightLocalCoverBuild.word h := Nat.le_add_right ..
    have hsecond : LightLocalCoverBuild.word h ≤ word h := by unfold word; omega
    exact hfirst.trans hsecond
  have hcoreBudget (x : ℕ) (hx : x ≤ LightLocalCoverHost.word h) : (x : ℤ) ≤ lim.word :=
    hbudget x (hx.trans hhostLe)
  have hwidthWord := hcoreBudget (2*(512*h)) (by
    unfold LightLocalCoverHost.word LightWeightGather.word
    omega)
  have hnWord := hcoreBudget (vertices h) (by
    unfold LightLocalCoverHost.word LightLocalCoverCandidate.word
      LightPairFlags.word vertices
    omega)
  have hpWord := hcoreBudget (localPrime h) (by
    unfold LightLocalCoverHost.word LightLocalCoverCandidate.word
      LightPairFlags.word
    omega)
  have hcapWord := hcoreBudget (localBucketCap h) (by
    unfold LightLocalCoverHost.word LightLocalCoverCandidate.word
      LightPairFlags.word
    omega)
  have hwidthWordZ : (2 : ℤ)*(512*(h : ℤ)) ≤ lim.word := by exact_mod_cast hwidthWord
  have hLWordZ : (512 : ℤ)*h ≤ lim.word := by exact_mod_cast hLWord
  have hp2WordZ : (localPrime h : ℤ)*localPrime h ≤ lim.word := by
    simpa only [cols,Nat.cast_mul] using hcolsWord
  have hcolsEq : (cols h : ℤ) = (localPrime h : ℤ)*localPrime h := by
    simp only [cols,Nat.cast_mul]
  have hp2Nonneg : (0 : ℤ) ≤ (localPrime h : ℤ)*localPrime h := by positivity
  have hlogBound : Nat.log2 (localPrime h^2) ≤ cols h := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.log_le_self 2 (localPrime h^2)).trans (by simp [cols,pow_two])
  have hlogResultWord : ((Nat.log2 (localPrime h^2)+1 : ℕ) : ℤ) ≤ lim.word := by
    apply hbudget
    unfold word
    omega
  have hscale : 320*(2*h+1) ≤ scheduleSize h := by
    change 320*(2*h+1) ≤ 320*(2*h+1)*(Nat.log2 (localPrime h^2)+1)
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hscaleWord : ((320*(2*h+1) : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hscale).trans hTWord
  have hscaleWordZ : (320 : ℤ)*(2*(h : ℤ)+1) ≤ lim.word := by exact_mod_cast hscaleWord
  have hroundWordZ : (320 : ℤ)*(2*(h : ℤ)+1)*(Nat.log2 (localPrime h^2)+1) ≤ lim.word := by
    simpa only [scheduleSize,LocalHashMoments.scheduleLength,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
      Nat.cast_ofNat] using hTWord
  have hroundNonneg : (0 : ℤ) ≤ 320*(2*(h : ℤ)+1)*(Nat.log2 (localPrime h^2)+1) := by positivity
  have hworkSpace : work base h ≤ lim.space := (work_le_space base h).trans hspace
  have hschedSpace : scheduleMaps base h+scheduleSize h*(2*(512*h)) ≤ lim.space :=
    (schedule_end_le_space base h).trans hspace
  have hsmall (x : ℕ) (hx : x ≤ work base h) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (hx.trans hworkSpace)).trans hw
  have hbitPtr := hsmall (bitPtr base h) (by
    unfold work matrixPtr hist1 hist0 raw1 raw0 maps
    omega)
  have hmaps := hsmall (maps base h) (by unfold work matrixPtr hist1 hist0 raw1 raw0; omega)
  have hraw0 := hsmall (raw0 base h) (by unfold work matrixPtr hist1 hist0 raw1; omega)
  have hraw1 := hsmall (raw1 base h) (by unfold work matrixPtr hist1 hist0; omega)
  have hhist0 := hsmall (hist0 base h) (by unfold work matrixPtr hist1; omega)
  have hhist1 := hsmall (hist1 base h) (by unfold work matrixPtr; omega)
  have hmatrix := hsmall (matrixPtr base h) (by unfold work; omega)
  have hwork := hsmall (work base h) le_rfl
  have hbase := hsmall base (by unfold work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr; omega)
  have hprodBits := hsmall (vertices h*(512*h)) (by
    unfold work matrixPtr hist1 hist0 raw1 raw0 maps
    omega)
  have hprodRows := hsmall (rows h*(2*(512*h))) (by
    unfold work matrixPtr hist1 hist0 raw1 raw0
    omega)
  have hprodRaw := hsmall (2*vertices h) (by unfold work matrixPtr hist1 hist0; omega)
  have hprodHist := hsmall (rows h*localPrime h) (by unfold work matrixPtr hist1; omega)
  have hprodMatrix := hsmall (rows h*cols h) (by unfold work; omega)
  have hprodBitsZ : (vertices h : ℤ)*(512*(h : ℤ)) ≤ lim.word := by exact_mod_cast hprodBits
  have hprodRowsZ : (rows h : ℤ)*(2*(512*(h : ℤ))) ≤ lim.word := by exact_mod_cast hprodRows
  have hprodHistZ : (rows h : ℤ)*localPrime h ≤ lim.word := by exact_mod_cast hprodHist
  have hprodMatrixZ : (rows h : ℤ)*((localPrime h : ℤ)*localPrime h) ≤ lim.word := by
    simpa only [cols,Nat.cast_mul] using hprodMatrix
  have hbitPtrZ : (base : ℤ)+vertices h ≤ lim.word := by
    simpa only [bitPtr,Nat.cast_add] using hbitPtr
  have hmapsZ : (bitPtr base h : ℤ)+(vertices h : ℤ)*(512*(h : ℤ)) ≤ lim.word := by
    simpa only [maps,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hmaps
  have hraw0Z : (maps base h : ℤ)+(rows h : ℤ)*(2*(512*(h : ℤ))) ≤ lim.word := by
    simpa only [raw0,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hraw0
  have hraw1Z : (raw0 base h : ℤ)+2*(vertices h : ℤ) ≤ lim.word := by
    simpa only [raw1,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hraw1
  have hhist0Z : (raw1 base h : ℤ)+2*(vertices h : ℤ) ≤ lim.word := by
    simpa only [hist0,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hhist0
  have hhist1Z : (hist0 base h : ℤ)+(rows h : ℤ)*localPrime h ≤ lim.word := by
    simpa only [hist1,Nat.cast_add,Nat.cast_mul] using hhist1
  have hmatrixZ : (hist1 base h : ℤ)+(rows h : ℤ)*localPrime h ≤ lim.word := by
    simpa only [matrixPtr,Nat.cast_add,Nat.cast_mul] using hmatrix
  have hworkZ : (matrixPtr base h : ℤ)+(rows h : ℤ)*((localPrime h : ℤ)*localPrime h) ≤ lim.word := by
    simpa only [work,cols,Nat.cast_add,Nat.cast_mul] using hwork
  have hbitsNonneg : (0 : ℤ) ≤ (vertices h : ℤ)*(512*(h : ℤ)) := by positivity
  have hrowsNonneg : (0 : ℤ) ≤ (rows h : ℤ)*(2*(512*(h : ℤ))) := by positivity
  have hhistNonneg : (0 : ℤ) ≤ (rows h : ℤ)*localPrime h := by positivity
  have hmatrixNonneg : (0 : ℤ) ≤ (rows h : ℤ)*((localPrime h : ℤ)*localPrime h) := by positivity
  have hscheduleWord : (scheduleMaps base h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by omega : scheduleMaps base h ≤ lim.space)).trans hw
  have hscheduleWordZ : (work base h : ℤ)+(localPrime h : ℤ)*localPrime h+(rows h : ℤ)+
      (scheduleSize h : ℤ) ≤ lim.word := by
    simpa only [scheduleMaps,LightCoverGreedy.total,cols,Nat.cast_add,Nat.cast_mul,
      Int.add_assoc] using hscheduleWord
  have hscheduleWork : work base h+cols h+rows h+scheduleSize h = scheduleMaps base h := by
    unfold scheduleMaps LightCoverGreedy.total
    omega
  apply Meets.of_body S.main
  unfold body time
  light_set (512*h : ℕ) using time
  light_set (2*(512*h) : ℕ) using time
  have hpowers : ∀ e ≤ 2*(512*h), (((localPrime h)^e : ℕ) : ℤ) ≤ lim.word := by
    intro e he
    have hp : (localPrime h)^e ≤ rows h := Nat.pow_le_pow_right (localPrime_pos h) he
    exact (Int.ofNat_le.mpr hp).trans hNWord
  have hpower := LightNatPower.meets (d := d+1) (b := localPrime h) (e := 2*(512*h))
    S.power μ hwidthWord hpowers
  light_call hpower using time with vc μ₁ ⟨hvc,hmem₁⟩
  subst μ₁
  have hvc' : vc = (rows h : ℤ) := hvc
  light_set (cols h : ℕ) using time,cols
  have hl := log2_meets (d := d+1) (x := cols h) S.log μ hlogWord
  light_call hl using time,cols with vl μ₂ ⟨hvl,hmem₂⟩
  subst μ₂
  have hvl' : vl = (Nat.log2 (localPrime h^2) : ℤ) := by
    simpa only [Nat.log2_eq_log_two,pow_two,cols] using hvl
  light_set (scheduleSize h : ℕ) using time,hvl',scheduleSize,LocalHashMoments.scheduleLength
  light_set (bitPtr base h : ℕ) using time,bitPtr
  light_set (maps base h : ℕ) using time,maps
  light_set (raw0 base h : ℕ) using time,raw0,hvc'
  light_set (raw1 base h : ℕ) using time,raw1
  light_set (hist0 base h : ℕ) using time,hist0
  light_set (hist1 base h : ℕ) using time,hist1,hvc'
  light_set (matrixPtr base h : ℕ) using time,matrixPtr,hvc'
  light_set (work base h : ℕ) using time,work,hvc',cols
  light_set (scheduleMaps base h : ℕ) using time,hscheduleWork,hvc',cols
  have hb := build_meets (d := d+1) (μ := μ) (base := base) (h := h) S.build
    hw (by omega) hspace hbuildWord
  light_call hb using time,hvc' with vb μ₃ ⟨hvb,hdata,hrows,hcandidates,hkept⟩
  exact ⟨hvb,hdata,hrows,hcandidates,hkept⟩

def program : Program :=
  [body 1 2 3,LightNatPower.body,log2Body,LightLocalCoverBuild.body 31 33 4,
    LightLocalCoverHost.body 5 24 29,LightLocalCoverMatrix.body 6,
    LightLocalCoverCandidate.body 7 12 19,LightWeightDecode.body 8 9,powTableBody,
    LightWeightRow.body 10,LightRadixDigit.body 11,LightSmallDivide.body,
    LightHashHistogram.body 13 15 17,LightMaskHashes.body 8 14,LightOneHot.body 14,
    LightResidues.residuesBody 16,emodBody,LightHistogram.histogramBody 18,fillBody,
    LightLocalCoverRow.body 20 23,LightPairFlags.body 11 21 22,LightBooleanDot.body,
    LightTrimTest.body,LightSupportMark.body 18,LightCoverGreedy.body 18 25 28,
    LightCoverSelect.body 26 27,LightCoverScores.body 21,LightMinimum.body,LightCoverUpdate.body,
    LightWeightGather.body 30,copyBody,LightSubsetEnumerationSetup.body 8 32,
    LightSubsetEnumeration.body 32,LightMaskBitTable.body 34,LightMaskBits.body 8 35,
    LightMaskErase.body 35]

def programProcs : Procs program 0 :=
  ⟨1,2,3,rfl,rfl,⟨31,8,32,33,34,35,4,rfl,rfl,rfl,rfl,rfl,rfl,
    ⟨5,24,29,⟨6,⟨7,12,19,⟨8,9,10,11,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,8,14,15,16,17,18,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨20,11,21,22,23,18,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,
      ⟨18,25,28,rfl,⟨26,21,27,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,⟨30,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩

end ThreeSum.LightLocalCoverSetup
