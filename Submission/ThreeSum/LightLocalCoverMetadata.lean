import Submission.ThreeSum.LightLocalCoverSetup

/-!
# Stored dimensions and pointers for the actual local cover

The twelve header fields are: L, 2h, schedule length, candidate count,
schedule coefficients, selected candidate indices, left counts, right
counts, candidate coefficients, cover matrix, first reusable address, p².
All values are computed from h, p, the vertex count, and the layout base.
-/

namespace ThreeSum.LightLocalCoverMetadata

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
open LightLocalCoverSetup (word)

set_option maxHeartbeats 2000000
set_option maxRecDepth 8500

def nextFree (base h : ℕ) : ℕ := scheduleMaps base h+scheduleSize h*(2*(512*h))

def values (base h : ℕ) : List ℤ :=
  [512*h,2*h,scheduleSize h,rows h,scheduleMaps base h,candidates base h,
    hist0 base h,hist1 base h,maps base h,matrixPtr base h,nextFree base h,cols h]

def body (pPower pLog : ℕ) : Stmt :=
  .set 5 (k 512 *' v 0) ;;
  .set 6 (k 2 *' v 5) ;;
  .call pPower [v 1,v 6] 7 ;;
  .set 8 (v 1 *' v 1) ;;
  .call pLog [v 8] 9 ;;
  .set 10 (k 320 *' (k 2 *' v 0 +' k 1) *' (v 9 +' k 1)) ;;
  .set 11 (v 3 +' v 2) ;;
  .set 12 (v 11 +' v 2 *' v 5) ;;
  .set 13 (v 12 +' v 7 *' v 6) ;;
  .set 14 (v 13 +' k 2 *' v 2) ;;
  .set 15 (v 14 +' k 2 *' v 2) ;;
  .set 16 (v 15 +' v 7 *' v 1) ;;
  .set 17 (v 16 +' v 7 *' v 1) ;;
  .set 18 (v 17 +' v 7 *' v 8) ;;
  .set 19 (v 18 +' v 8 +' v 7 +' v 10) ;;
  .set 20 (v 18 +' v 8 +' v 7) ;;
  .set 21 (v 19 +' v 10 *' v 6) ;;
  .set 22 (k 2 *' v 0) ;;
  .store (v 4) (v 5) ;;
  .store (v 4 +' k 1) (v 22) ;;
  .store (v 4 +' k 2) (v 10) ;;
  .store (v 4 +' k 3) (v 7) ;;
  .store (v 4 +' k 4) (v 19) ;;
  .store (v 4 +' k 5) (v 20) ;;
  .store (v 4 +' k 6) (v 15) ;;
  .store (v 4 +' k 7) (v 16) ;;
  .store (v 4 +' k 8) (v 12) ;;
  .store (v 4 +' k 9) (v 17) ;;
  .store (v 4 +' k 10) (v 21) ;;
  .store (v 4 +' k 11) (v 8) ;;
  .set 0 (v 21)

def time (h : ℕ) : ℕ := LightNatPower.time (2*(512*h))+log2Time (cols h)+1000

structure Procs (P : Program) (pMain : ℕ) where
  pPower : ℕ
  pLog : ℕ
  power : P[pPower]? = some LightNatPower.body
  log : P[pLog]? = some log2Body
  main : P[pMain]? = some (body pPower pLog)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {base h dst : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 ≤ lim.depth)
    (hout : dst+12 ≤ base)
    (hspace : space base h ≤ lim.space) (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h,localPrime h,vertices h,base,dst] μ (time h)
      (fun r ν => r = (nextFree base h : ℤ) ∧ Seg ν dst (values base h) ∧
        SameOutside μ ν dst 12) := by
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

  have hbaseSpace : base ≤ lim.space := by
    unfold work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr at hworkSpace
    omega
  have hcandidateSpace : candidates base h ≤ lim.space := by
    unfold candidates LightCoverGreedy.out scheduleMaps LightCoverGreedy.total at *
    omega
  have hcandidateWord : (candidates base h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hcandidateSpace).trans hw
  have hcandidateWordZ : (work base h : ℤ)+(localPrime h : ℤ)*localPrime h+(rows h : ℤ) ≤ lim.word := by
    simpa only [candidates,LightCoverGreedy.out,cols,Nat.cast_add,Nat.cast_mul] using hcandidateWord
  have hnextWord : (nextFree base h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hschedSpace).trans hw
  have hnextWordZ : (scheduleMaps base h : ℤ)+(scheduleSize h : ℤ)*(2*(512*(h : ℤ))) ≤ lim.word := by
    simpa only [nextFree,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hnextWord
  have hproductWordZ : (scheduleSize h : ℤ)*(2*(512*(h : ℤ))) ≤ lim.word := by
    have hm : scheduleSize h*(2*(512*h)) ≤ lim.space := by omega
    exact (by exact_mod_cast hm : (scheduleSize h : ℤ)*(2*(512*(h : ℤ))) ≤ lim.space).trans hw
  have hproductNonneg : (0 : ℤ) ≤ (scheduleSize h : ℤ)*(2*(512*(h : ℤ))) := by positivity
  have htwoWord : ((2*h : ℕ) : ℤ) ≤ lim.word := by omega
  have htwoWordZ : (2 : ℤ)*h ≤ lim.word := by exact_mod_cast htwoWord
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
  light_set (candidates base h : ℕ) using time,candidates,LightCoverGreedy.out,hvc',cols
  light_set (nextFree base h : ℕ) using time,nextFree
  light_set (2*h : ℕ) using time
  light_store dst (512*h : ℕ) using time
  light_store (dst+1) (2*h : ℕ) using time
  light_store (dst+2) (scheduleSize h : ℕ) using time
  light_store (dst+3) (rows h : ℕ) using time,hvc'
  light_store (dst+4) (scheduleMaps base h : ℕ) using time
  light_store (dst+5) (candidates base h : ℕ) using time
  light_store (dst+6) (hist0 base h : ℕ) using time
  light_store (dst+7) (hist1 base h : ℕ) using time
  light_store (dst+8) (maps base h : ℕ) using time
  light_store (dst+9) (matrixPtr base h : ℕ) using time
  light_store (dst+10) (nextFree base h : ℕ) using time
  light_store (dst+11) (cols h : ℕ) using time
  light_set (nextFree base h : ℕ) using time
  refine ⟨rfl,?_,?_⟩
  · have hn : Seg μ dst [] := Seg.nil
    simpa [values] using
      ((((((((((((hn.snoc (512*h : ℕ)).snoc (2*h : ℕ)).snoc (scheduleSize h : ℕ)).snoc
        (rows h : ℕ)).snoc (scheduleMaps base h : ℕ)).snoc (candidates base h : ℕ)).snoc
        (hist0 base h : ℕ)).snoc (hist1 base h : ℕ)).snoc (maps base h : ℕ)).snoc
        (matrixPtr base h : ℕ)).snoc (nextFree base h : ℕ)).snoc (cols h : ℕ))
  · have hp : SameOutside μ μ dst 12 := SameOutside.refl
    exact ((((((((((((hp.update (by omega : dst ≤ dst ∧ dst < dst+12) (512*h : ℕ)).update
      (by omega : dst ≤ dst+1 ∧ dst+1 < dst+12) (2*h : ℕ)).update
      (by omega : dst ≤ dst+2 ∧ dst+2 < dst+12) (scheduleSize h : ℕ)).update
      (by omega : dst ≤ dst+3 ∧ dst+3 < dst+12) (rows h : ℕ)).update
      (by omega : dst ≤ dst+4 ∧ dst+4 < dst+12) (scheduleMaps base h : ℕ)).update
      (by omega : dst ≤ dst+5 ∧ dst+5 < dst+12) (candidates base h : ℕ)).update
      (by omega : dst ≤ dst+6 ∧ dst+6 < dst+12) (hist0 base h : ℕ)).update
      (by omega : dst ≤ dst+7 ∧ dst+7 < dst+12) (hist1 base h : ℕ)).update
      (by omega : dst ≤ dst+8 ∧ dst+8 < dst+12) (maps base h : ℕ)).update
      (by omega : dst ≤ dst+9 ∧ dst+9 < dst+12) (matrixPtr base h : ℕ)).update
      (by omega : dst ≤ dst+10 ∧ dst+10 < dst+12) (nextFree base h : ℕ)).update
      (by omega : dst ≤ dst+11 ∧ dst+11 < dst+12) (cols h : ℕ))

def program : Program := [body 1 2,LightNatPower.body,log2Body]
def programProcs : Procs program 0 := ⟨1,2,rfl,rfl,rfl⟩

end ThreeSum.LightLocalCoverMetadata
