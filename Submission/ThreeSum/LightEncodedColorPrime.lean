import Submission.ThreeSum.LightEncodedColorPrimeCore
import Submission.ThreeSum.SourceFiniteRetention
import Submission.ThreeSum.LightBandPrimeStage

/-! # Read the actual normalized band headers and construct one common prime -/

namespace ThreeSum.LightEncodedColorPrime

open Light BandPartition BandCandidateRows BandRawA SourceFiniteInputs

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

def count (nA nB nC g : ℕ) : ℕ :=
  size nB g*size nC g+size nA g*size nB g+size nA g*size nC g

def moduli (A B C : List ℤ) (g : ℕ) (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) (y : ℕ) : ℕ → ℕ :=
  LightBandPrimeConstruction.modulus y A.length B.length C.length g
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (sortedRecords A B C g hg hsA hsB hsC)

def body (pCore : ℕ) : Stmt :=
  .set 11 (M (v 1)) ;;
  .set 12 (M (v 3)) ;;
  .set 13 (M (v 5)) ;;
  .set 14 (M (v 1 +' k 1)) ;;
  .set 15 (M (v 3 +' k 1)) ;;
  .set 16 (M (v 5 +' k 1)) ;;
  .set 17 (v 15 *' v 16 +' v 14 *' v 15 +' v 14 *' v 16) ;;
  .call pCore [v 0,v 2,v 4,v 11,v 12,v 13,v 6,v 7,v 17,v 8,v 9,v 10] 0

def program : Program := LightEncodedColorPrimeCore.program ++ [body 23]

theorem program_length : program.length=25 := rfl

def time (maxMod nA nB nC g M y U : ℕ) : ℕ :=
  LightEncodedColorPrimeCore.time maxMod g (count nA nB nC g) M y U+400

def word (maxMod nA nB nC g M y U : ℕ) : ℕ :=
  LightEncodedColorPrimeCore.word maxMod nA nB nC g (count nA nB nC g) M y U+
    nA+nB+nC+count nA nB nC g+100

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}

theorem program_meets {av ae bv be cv ce tables rec vals g M y free maxMod U : ℕ} {hg : 0 < g}
    {originalA originalB originalC A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} {rA : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hy : 0 < y)
    (hav : av+A.length ≤ free) (hbv : bv+B.length ≤ free) (hcv : cv+C.length ≤ free)
    (hae : ae+2 ≤ free) (hbe : be+2 ≤ free) (hce : ce+2 ≤ free)
    (hrec : rec+4*count A.length B.length C.length g ≤ free)
    (hspace : LightEncodedColorPrimeCore.space free maxMod g M y U ≤ lim.space)
    (hword : (word maxMod A.length B.length C.length g M y U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+10 ≤ lim.depth)
    (hA : ∀ z ∈ originalA, |z| ≤ (U : ℤ))
    (hB : ∀ z ∈ originalB, |z| ≤ (U : ℤ))
    (hC : ∀ z ∈ originalC, |z| ≤ (U : ℤ))
    (H : SourceFiniteData.Normalized μ av ae bv be cv ce tables rec vals g hg
      originalA originalB originalC A B C hsA hsB hsC rA)
    (hmax : (4*y)^(LightBandPrimeDepth.depth M y+1) ≤ maxMod) :
    Meets lim program 24 d [av,ae,bv,be,cv,ce,g,rec,M,y,free] μ
      (time maxMod A.length B.length C.length g M y U)
      (fun result ν =>
        result=(moduli A B C g hg hsA hsB hsC y (LightBandPrimeDepth.depth M y) : ℤ) ∧
        EncodedColorPrimeData.Stored ν free M y (moduli A B C g hg hsA hsB hsC y) ∧ Kept μ ν free) := by
  obtain ⟨_,repA,repB,repC,_,recordRows,_⟩ := H
  obtain ⟨hlenA,hcountA⟩ := prepared_headers repA
  obtain ⟨hlenB,hcountB⟩ := prepared_headers repB
  obtain ⟨hlenC,hcountC⟩ := prepared_headers repC
  let rs := sortedRecords A B C g hg hsA hsB hsC
  have hrs : rs.length=count A.length B.length C.length g := by
    simp only [rs,sortedRecords,records_length]
    rfl
  have hsrcA := prepared_read repA
  have hsrcB := prepared_read repB
  have hsrcC := prepared_read repC
  have hbA := prepared_bound repA hA
  have hbB := prepared_bound repB hB
  have hbC := prepared_bound repC hC
  have hcoreWord : (LightEncodedColorPrimeCore.word maxMod A.length B.length C.length g
      (count A.length B.length C.length g) M y U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show LightEncodedColorPrimeCore.word maxMod A.length B.length C.length g
      (count A.length B.length C.length g) M y U ≤ word maxMod A.length B.length C.length g M y U by unfold word; omega)).trans hword
  have hall (z : ℕ) (hz : z ≤ word maxMod A.length B.length C.length g M y U) : (z : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hz).trans hword
  have hnA := hall A.length (by unfold word; omega)
  have hnB := hall B.length (by unfold word; omega)
  have hnC := hall C.length (by unfold word; omega)
  have hGA := size_le A.length g
  have hGB := size_le B.length g
  have hGC := size_le C.length g
  have hcount := hall (count A.length B.length C.length g) (by unfold word; omega)
  have hcountZ : (size B.length g : ℤ)*(size C.length g : ℤ)+
      (size A.length g : ℤ)*(size B.length g : ℤ)+(size A.length g : ℤ)*(size C.length g : ℤ) ≤ lim.word := by
    simpa only [count,Nat.cast_add,Nat.cast_mul] using hcount
  have hBC0 : (0 : ℤ) ≤ (size B.length g : ℤ)*(size C.length g : ℤ) := by positivity
  have hAB0 : (0 : ℤ) ≤ (size A.length g : ℤ)*(size B.length g : ℤ) := by positivity
  have hAC0 : (0 : ℤ) ≤ (size A.length g : ℤ)*(size C.length g : ℤ) := by positivity
  have hfree : free+6 ≤ lim.space := by
    have hh := (le_max_left _ _).trans hspace
    unfold LightPrimePool.space EncodedColorPrimeData.poolBase at hh
    omega
  have haa : ((ae : ℤ)+1).toNat=ae+1 := by omega
  have hba : ((be : ℤ)+1).toNat=be+1 := by omega
  have hca : ((ce : ℤ)+1).toNat=ce+1 := by omega
  apply Meets.of_body (p := 24) (by rfl : program[24]?=some (body 23))
  unfold body time
  light_set (A.length : ℕ) using hlenA
  light_set (B.length : ℕ) using hlenB
  light_set (C.length : ℕ) using hlenC
  light_set (size A.length g : ℕ) using hcountA,haa
  light_set (size B.length g : ℕ) using hcountB,hba
  light_set (size C.length g : ℕ) using hcountC,hca
  light_set (count A.length B.length C.length g : ℕ) using count
  have hflags : ∀ r ∈ rs, r.flag=0 ∨ r.flag=1 := fun _ hr => records_flag hr
  have hvalid : ∀ r ∈ rs, r.flag=1 → r.a*g ≤ A.length ∧ r.b*g ≤ B.length ∧ r.c*g ≤ C.length :=
    LightBandPrimeStage.records_valid rfl rfl rfl hg
  have hCore := (LightEncodedColorPrimeCore.program_meets (d := d+1) (μ := μ)
    (a := av) (b := bv) (c := cv) (nA := A.length) (nB := B.length) (nC := C.length)
    (g := g) (recs := rec) (M := M) (y := y) (free := free) (maxMod := maxMod) (U := U)
    rs hw hy hg hav hbv hcv (by simpa only [hrs] using hrec) hspace
    (by simpa only [hrs] using hcoreWord) (by omega) recordRows hflags hvalid
    (fun i hi => by rw [hsrcA i hi]; exact hbA i hi)
    (fun i hi => by rw [hsrcB i hi]; exact hbB i hi)
    (fun i hi => by rw [hsrcC i hi]; exact hbC i hi) hmax).append [body 23]
  light_call hCore using hrs with result ν ⟨hresult,hdata,hkeep⟩
  have hmod : LightBandPrimeConstruction.modulus y A.length B.length C.length g
      (fun j => μ (av+j)) (fun j => μ (bv+j)) (fun j => μ (cv+j)) rs=
      moduli A B C g hg hsA hsB hsC y := by
    funext i
    exact BandPrimeChoice.modulus_congr rs hsrcA hsrcB hsrcC i
  rw [hmod] at hresult hdata
  exact ⟨hresult,hdata,hkeep⟩

end ThreeSum.LightEncodedColorPrime
