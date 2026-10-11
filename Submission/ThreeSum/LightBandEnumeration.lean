import Submission.ThreeSum.LightBandTable
import Submission.ThreeSum.BandEnumeration
import Submission.ThreeSum.LightCapacity

/-!
# A closed machine program listing all relevant sorted-band candidates

The program computes its own binary width and power table, then executes
exactly the three rectangular owner tables. Every table cell contains an
interval lookup result (index plus one, zero for a miss). The source arrays
remain intact. The coverage theorem below connects these actual memory cells
to every relevant triple, and hence to every exact equation in the bands.
-/

namespace ThreeSum.LightBandEnumeration

set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def At (μ : ℕ → ℤ) (lo hi : ℕ) (A : Family) : Prop :=
  (∀ i < A.size, μ (lo+i) = A.lower i) ∧
  (∀ i < A.size, μ (hi+i) = A.upper i)

def Bounded (A : Family) (U : ℕ) : Prop :=
  ∀ i < A.size, |A.lower i| ≤ (U : ℤ) ∧ |A.upper i| ≤ (U : ℤ)

theorem At.keep {μ μ' : ℕ → ℤ} {lo hi bound : ℕ} {A : Family}
    (h : At μ lo hi A) (hk : Kept μ μ' bound)
    (hlo : lo+A.size ≤ bound) (hhi : hi+A.size ≤ bound) : At μ' lo hi A := by
  constructor
  · intro i hi
    rw [hk (lo+i) (by omega)]
    exact h.1 i hi
  · intro i hi'
    rw [hk (hi+i) (by omega)]
    exact h.2 i hi'

def count (nA nB nC : ℕ) : ℕ := nB*nC+nA*nB+nA*nC
def width (nA nB nC : ℕ) : ℕ := Nat.clog 2 (nA+nB+nC+1)
def space (dst nA nB nC : ℕ) : ℕ := dst+count nA nB nC+width nA nB nC+1
def word (nA nB nC U : ℕ) : ℕ := 8*(nA+nB+nC+U+1)+32

def Tables (μ : ℕ → ℤ) (dst : ℕ) (A B C : Family) : Prop :=
  (∀ j < B.size, ∀ k < C.size,
    μ (dst+j*C.size+k) =
      (LightBandLookup.result A.lower A.upper A.size (C.lower k-B.upper j) : ℤ)) ∧
  (∀ i < A.size, ∀ j < B.size,
    μ (dst+B.size*C.size+i*B.size+j) =
      (LightBandLookup.result C.lower C.upper C.size (A.lower i+B.lower j) : ℤ)) ∧
  (∀ i < A.size, ∀ k < C.size,
    μ (dst+B.size*C.size+A.size*B.size+i*C.size+k) =
      (LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i) : ℤ))

/-- Arguments: six endpoint pointers, three band counts, output base. -/
def body (pClog pPowers pTable : ℕ) : Stmt :=
  .set 10 (v 6 +' v 7 +' v 8) ;;
  .set 11 (v 7 *' v 8) ;;
  .set 12 (v 6 *' v 7) ;;
  .set 13 (v 6 *' v 8) ;;
  .set 14 (v 9 +' v 11) ;;
  .set 15 (v 14 +' v 12) ;;
  .set 16 (v 15 +' v 13) ;;
  .call pClog [v 10 +' k 1] 17 ;;
  .call pPowers [v 16,v 17 +' k 1,k 2] 18 ;;
  .call pTable [v 3,v 4,v 0,v 1,v 7,v 8,v 6,v 9,v 16,v 17,k 0 -' k 1] 18 ;;
  .call pTable [v 0,v 2,v 4,v 5,v 6,v 7,v 8,v 14,v 16,v 17,k 1] 18 ;;
  .call pTable [v 0,v 4,v 2,v 3,v 6,v 8,v 7,v 15,v 16,v 17,k 0 -' k 1] 18 ;;
  .set 0 (v 11 +' v 12 +' v 13)

def time (nA nB nC : ℕ) : ℕ :=
  clog2Time (nA+nB+nC+1)+powTableTime (width nA nB nC+1)+
    LightBandTable.time nB nC (width nA nB nC)+
    LightBandTable.time nA nB (width nA nB nC)+
    LightBandTable.time nA nC (width nA nB nC)+500

structure Procs (P : Program) (pMain : ℕ) where
  pClog : ℕ
  pPowers : ℕ
  pTable : ℕ
  pRow : ℕ
  pLookup : ℕ
  pSearch : ℕ
  main : P[pMain]? = some (body pClog pPowers pTable)
  clog : P[pClog]? = some clog2Body
  powers : P[pPowers]? = some powTableBody
  table : P[pTable]? = some (LightBandTable.body pRow)
  row : P[pRow]? = some (LightBandTable.rowBody pLookup)
  lookup : P[pLookup]? = some (LightBandLookup.body pSearch)
  search : P[pSearch]? = some (LightBandLookup.searchBody pSearch)

theorem Procs.meets {pMain al ah bl bh cl ch dst U d : ℕ} {μ : ℕ → ℤ}
    (R : Procs P pMain) (A B C : Family)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hal : al+A.size ≤ dst) (hah : ah+A.size ≤ dst)
    (hbl : bl+B.size ≤ dst) (hbh : bh+B.size ≤ dst)
    (hcl : cl+C.size ≤ dst) (hch : ch+C.size ≤ dst)
    (hspace : space dst A.size B.size C.size ≤ lim.space)
    (hword : (word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d+width A.size B.size C.size+4 ≤ lim.depth)
    (hA : At μ al ah A) (hB : At μ bl bh B) (hC : At μ cl ch C)
    (hAU : Bounded A U) (hBU : Bounded B U) (hCU : Bounded C U) :
    Meets lim P pMain d [al,ah,bl,bh,cl,ch,A.size,B.size,C.size,dst] μ
      (time A.size B.size C.size)
      (fun r μ' => r = (count A.size B.size C.size : ℤ) ∧
        Tables μ' dst A B C ∧ Kept μ μ' dst) := by
  let N := A.size+B.size+C.size
  let W := width A.size B.size C.size
  let bc := B.size*C.size
  let ab := A.size*B.size
  let ac := A.size*C.size
  let outAB := dst+bc
  let outAC := outAB+ab
  let powers := outAC+ac
  have hNdef : N = A.size+B.size+C.size := rfl
  have hWdef : W = Nat.clog 2 (N+1) := rfl
  have hspace' : powers+(W+1) ≤ lim.space := by
    simpa [powers,outAC,outAB,bc,ab,ac,W,space,count,Nat.add_assoc] using hspace
  have hWWord : ((width A.size B.size C.size+1 : ℕ) : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (by change W+1 ≤ lim.space; omega)).trans hw
  have hwidthN : Nat.clog 2 (N+1) = width A.size B.size C.size := rfl
  have hcapacity : 2^W < 2*(N+1) := by
    exact KaratsubaInterface.capacity_lt_twice (p := N+1) (by omega)
  have hpow : 2^(W+1) < 4*(N+1) := by rw [pow_succ]; omega
  have hN : N < 2^W := by
    have hp : N+1 ≤ 2^W := Nat.le_pow_clog (by decide) _
    omega
  have hlookupWord : ((N+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word := by
    have hn : N+2^(W+1)+16 ≤ word A.size B.size C.size U := by
      unfold word N at *
      omega
    exact (Int.ofNat_le.mpr hn).trans hword
  have hwordA : ((A.size+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by dsimp [N]; omega)).trans hlookupWord
  have hwordB : ((B.size+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by dsimp [N]; omega)).trans hlookupWord
  have hwordC : ((C.size+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by dsimp [N]; omega)).trans hlookupWord
  have hqueryWord : 2*(U : ℤ) ≤ lim.word := by
    have hh : 2*U ≤ word A.size B.size C.size U := by unfold word; omega
    exact (by exact_mod_cast hh : 2*(U : ℤ) ≤ (word A.size B.size C.size U : ℤ)).trans hword
  have hlogWord : ((2*(N+1)+1 : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2*(N+1)+1 ≤ word A.size B.size C.size U := by unfold word N; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hpowWord (j : ℕ) (hj : j ≤ W+1) : ((2^j : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^j ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) hj
    exact (Int.ofNat_le.mpr (by omega : 2^j ≤ N+2^(W+1)+16)).trans hlookupWord
  have hbcNonneg : (0 : ℤ) ≤ (B.size : ℤ)*(C.size : ℤ) := by positivity
  have habNonneg : (0 : ℤ) ≤ (A.size : ℤ)*(B.size : ℤ) := by positivity
  have hacNonneg : (0 : ℤ) ≤ (A.size : ℤ)*(C.size : ℤ) := by positivity
  have hbcWord : (B.size : ℤ)*(C.size : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast (show bc ≤ lim.space by omega) :
      (B.size : ℤ)*(C.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have habWord : (A.size : ℤ)*(B.size : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast (show ab ≤ lim.space by omega) :
      (A.size : ℤ)*(B.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have hacWord : (A.size : ℤ)*(C.size : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast (show ac ≤ lim.space by omega) :
      (A.size : ℤ)*(C.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  apply Meets.of_body R.main
  unfold body time
  light_set (N : ℕ) using width,← hNdef,← hWdef,LightBandTable.time,LightBandTable.rowTime,
    LightBandLookup.time,LightBandLookup.searchTime,powTableTime
  light_set (bc : ℕ) using bc,width,← hNdef,← hWdef,LightBandTable.time,LightBandTable.rowTime,
    LightBandLookup.time,LightBandLookup.searchTime,powTableTime
  light_set (ab : ℕ) using ab,width,← hNdef,← hWdef,LightBandTable.time,LightBandTable.rowTime,
    LightBandLookup.time,LightBandLookup.searchTime,powTableTime
  light_set (ac : ℕ) using ac,width,← hNdef,← hWdef,LightBandTable.time,LightBandTable.rowTime,
    LightBandLookup.time,LightBandLookup.searchTime,powTableTime
  light_set (outAB : ℕ) using outAB,width,← hNdef,← hWdef,LightBandTable.time,LightBandTable.rowTime,
    LightBandLookup.time,LightBandLookup.searchTime,powTableTime
  light_set (outAC : ℕ) using outAC,width,← hNdef,← hWdef,LightBandTable.time,LightBandTable.rowTime,
    LightBandLookup.time,LightBandLookup.searchTime,powTableTime
  light_set (powers : ℕ) using powers,width,← hNdef,← hWdef,LightBandTable.time,LightBandTable.rowTime,
    LightBandLookup.time,LightBandLookup.searchTime,powTableTime
  light_call (clog2_meets (d := d+1) (x := N+1) R.clog μ hlogWord)
    using width,← hNdef,← hWdef,LightBandTable.time,LightBandTable.rowTime,
    LightBandLookup.time,LightBandLookup.searchTime,powTableTime with wid μ₀ ⟨hwid,hmem₀⟩
  subst μ₀
  rw [← hWdef] at hwid
  subst wid
  light_call (powTable_meets (d := d+1) (dst := powers) (L := W+1) (b := 2)
    R.powers hw hspace' hpowWord)
    using width,← hNdef,← hWdef,LightBandTable.time,LightBandTable.rowTime,
    LightBandLookup.time,LightBandLookup.searchTime,powTableTime with unused μ₁ ⟨hpowersSeg,hkeep₁⟩
  have hkept₁ : Kept μ μ₁ dst := fun a ha => hkeep₁ a (Or.inl (by omega))
  have hA₁ := hA.keep hkept₁ hal hah
  have hB₁ := hB.keep hkept₁ hbl hbh
  have hC₁ := hC.keep hkept₁ hcl hch
  have hpowers₁ := powers_of_segment hpowersSeg
  light_call (LightBandTable.meets (d := d+1) (dst := dst) (s := -1)
    R.table R.row R.lookup R.search μ₁ B.upper C.lower A.lower A.upper hw
    hbh hcl hal hah (by omega) hspace' hwordA hqueryWord hB₁.2 hC₁.1 hA₁.1 hA₁.2
    hpowers₁ A.sorted (by dsimp [N] at hN; omega) (by norm_num)
    (fun i hi => (hBU i hi).2) (fun i hi => (hCU i hi).1) (by omega))
    using width,← hNdef,← hWdef,bc,LightBandTable.time,LightBandTable.rowTime,
    LightBandLookup.time,LightBandLookup.searchTime,powTableTime with unused μ₂ ⟨hBC,hkeep₂⟩
  have hkept₂ : Kept μ μ₂ dst := fun a ha =>
    (hkeep₂ a (Or.inl ha)).trans (hkept₁ a ha)
  have hA₂ := hA.keep hkept₂ hal hah
  have hB₂ := hB.keep hkept₂ hbl hbh
  have hC₂ := hC.keep hkept₂ hcl hch
  have hpowers₂ : Powers μ₂ powers W := by
    intro i hi
    rw [hkeep₂ (powers+i) (Or.inr (by omega))]
    exact hpowers₁ i hi
  light_call (LightBandTable.meets (d := d+1) (dst := outAB) (s := 1)
    R.table R.row R.lookup R.search μ₂ A.lower B.lower C.lower C.upper hw
    (by omega) (by omega) (by omega) (by omega) (by omega) hspace' hwordC hqueryWord
    hA₂.1 hB₂.1 hC₂.1 hC₂.2 hpowers₂ C.sorted (by dsimp [N] at hN; omega)
    (by norm_num) (fun i hi => (hAU i hi).1) (fun i hi => (hBU i hi).1) (by omega))
    using width,← hNdef,← hWdef,bc,ab,outAB,LightBandTable.time,LightBandTable.rowTime,
    LightBandLookup.time,LightBandLookup.searchTime,powTableTime with unused μ₃ ⟨hAB,hkeep₃⟩
  have hkept₃ : Kept μ μ₃ dst := fun a ha =>
    (hkeep₃ a (Or.inl (by omega))).trans (hkept₂ a ha)
  have hA₃ := hA.keep hkept₃ hal hah
  have hB₃ := hB.keep hkept₃ hbl hbh
  have hC₃ := hC.keep hkept₃ hcl hch
  have hpowers₃ : Powers μ₃ powers W := by
    intro i hi
    rw [hkeep₃ (powers+i) (Or.inr (by omega))]
    exact hpowers₂ i hi
  light_call (LightBandTable.meets (d := d+1) (dst := outAC) (s := -1)
    R.table R.row R.lookup R.search μ₃ A.lower C.lower B.lower B.upper hw
    (by omega) (by omega) (by omega) (by omega) (by omega) hspace' hwordB hqueryWord
    hA₃.1 hC₃.1 hB₃.1 hB₃.2 hpowers₃ B.sorted (by dsimp [N] at hN; omega)
    (by norm_num) (fun i hi => (hAU i hi).1) (fun i hi => (hCU i hi).1) (by omega))
    using width,← hNdef,← hWdef,bc,ab,ac,outAB,outAC,LightBandTable.time,LightBandTable.rowTime,
    LightBandLookup.time,LightBandLookup.searchTime,powTableTime with unused μ₄ ⟨hAC,hkeep₄⟩
  light_set (count A.size B.size C.size : ℕ)
    using count,bc,ab,ac,width,← hNdef,← hWdef,LightBandTable.time,LightBandTable.rowTime,
    LightBandLookup.time,LightBandLookup.searchTime,powTableTime
  refine ⟨rfl,⟨?_,?_,?_⟩,?_⟩
  · intro j hj k hk
    have hoff : j*C.size+k < bc := by
      have hh := Nat.mul_le_mul_right C.size (show j+1 ≤ B.size by omega)
      dsimp [bc]
      nlinarith
    change μ₄ (dst+j*C.size+k) = _
    rw [hkeep₄ _ (Or.inl (by omega)),hkeep₃ _ (Or.inl (by omega))]
    simpa [LightBandTable.rowValue,sub_eq_add_neg,add_comm] using hBC j hj k hk
  · intro i hi j hj
    have hoff : i*B.size+j < ab := by
      have hh := Nat.mul_le_mul_right B.size (show i+1 ≤ A.size by omega)
      dsimp [ab]
      nlinarith
    change μ₄ (dst+bc+i*B.size+j) = _
    rw [hkeep₄ _ (Or.inl (by omega))]
    simpa [LightBandTable.rowValue,outAB] using hAB i hi j hj
  · intro i hi k hk
    simpa [LightBandTable.rowValue,outAC,outAB,bc,ab,sub_eq_add_neg,add_comm] using hAC i hi k hk
  · intro a ha
    change μ₄ a = μ a
    exact (hkeep₄ a (Or.inl (by omega))).trans (hkept₃ a ha)

def program : Program :=
  [body 1 2 3,clog2Body,powTableBody,LightBandTable.body 4,
    LightBandTable.rowBody 5,LightBandLookup.body 6,LightBandLookup.searchBody 6]

def program_procs : Procs program 0 := ⟨1,2,3,4,5,6,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets {al ah bl bh cl ch dst U d : ℕ} {μ : ℕ → ℤ}
    (A B C : Family) (hw : (lim.space : ℤ) ≤ lim.word)
    (hal : al+A.size ≤ dst) (hah : ah+A.size ≤ dst)
    (hbl : bl+B.size ≤ dst) (hbh : bh+B.size ≤ dst)
    (hcl : cl+C.size ≤ dst) (hch : ch+C.size ≤ dst)
    (hspace : space dst A.size B.size C.size ≤ lim.space)
    (hword : (word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d+width A.size B.size C.size+4 ≤ lim.depth)
    (hA : At μ al ah A) (hB : At μ bl bh B) (hC : At μ cl ch C)
    (hAU : Bounded A U) (hBU : Bounded B U) (hCU : Bounded C U) :
    Meets lim program 0 d [al,ah,bl,bh,cl,ch,A.size,B.size,C.size,dst] μ
      (time A.size B.size C.size)
      (fun r μ' => r = (count A.size B.size C.size : ℤ) ∧
        Tables μ' dst A B C ∧ Kept μ μ' dst) :=
  program_procs.meets A B C hw hal hah hbl hbh hcl hch hspace hword hd hA hB hC hAU hBU hCU

theorem lookup_complete (A : Family) {i : ℕ} {x : ℤ} (hi : i < A.size)
    (hl : A.lower i ≤ x) (hh : x ≤ A.upper i) :
    LightBandLookup.result A.lower A.upper A.size x = i+1 := by
  have h := BinarySearch.locate_complete A.lower A.upper A.size x
    A.sorted A.separated hi hl hh
  simp [LightBandLookup.result,h]

theorem lookup_sound (A : Family) {i : ℕ} {x : ℤ}
    (hr : LightBandLookup.result A.lower A.upper A.size x = i+1) :
    i < A.size ∧ A.lower i ≤ x ∧ x ≤ A.upper i := by
  unfold LightBandLookup.result at hr
  cases h : BinarySearch.locate A.lower A.upper A.size x with
  | none => simp [h] at hr
  | some j =>
      simp only [h,Option.map_some,Option.getD_some] at hr
      have heq : j = i := by omega
      subst j
      exact BinarySearch.locate_sound A.lower A.upper A.size x A.sorted h

theorem Tables.sound_bc {μ : ℕ → ℤ} {dst i j k : ℕ} {A B C : Family}
    (ht : Tables μ dst A B C) (hj : j < B.size) (hk : k < C.size)
    (hr : μ (dst+j*C.size+k) = (i+1 : ℕ)) :
    i < A.size ∧ Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (i,j,k) := by
  rw [ht.1 j hj k hk] at hr
  have hs := lookup_sound A (i := i) (by exact_mod_cast hr)
  have hB := B.nonempty j hj
  have hC := C.nonempty k hk
  refine ⟨hs.1,?_⟩
  constructor <;> dsimp only <;> omega

theorem Tables.sound_ab {μ : ℕ → ℤ} {dst i j k : ℕ} {A B C : Family}
    (ht : Tables μ dst A B C) (hi : i < A.size) (hj : j < B.size)
    (hr : μ (dst+B.size*C.size+i*B.size+j) = (k+1 : ℕ)) :
    k < C.size ∧ Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (i,j,k) := by
  rw [ht.2.1 i hi j hj] at hr
  have hs := lookup_sound C (i := k) (by exact_mod_cast hr)
  have hA := A.nonempty i hi
  have hB := B.nonempty j hj
  refine ⟨hs.1,?_⟩
  constructor <;> dsimp only <;> omega

theorem Tables.sound_ac {μ : ℕ → ℤ} {dst i j k : ℕ} {A B C : Family}
    (ht : Tables μ dst A B C) (hi : i < A.size) (hk : k < C.size)
    (hr : μ (dst+B.size*C.size+A.size*B.size+i*C.size+k) = (j+1 : ℕ)) :
    j < B.size ∧ Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (i,j,k) := by
  rw [ht.2.2 i hi k hk] at hr
  have hs := lookup_sound B (i := j) (by exact_mod_cast hr)
  have hA := A.nonempty i hi
  have hC := C.nonempty k hk
  refine ⟨hs.1,?_⟩
  constructor <;> dsimp only <;> omega

/-- The actual emitted owner tables cover every relevant triple. -/
theorem Tables.covers {μ : ℕ → ℤ} {dst : ℕ} {A B C : Family}
    (ht : Tables μ dst A B C) (i : A.Index) (j : B.Index) (k : C.Index)
    (hr : relevant A B C (i,j,k)) :
    μ (dst+j.val*C.size+k.val) = (i.val+1 : ℕ) ∨
      μ (dst+B.size*C.size+i.val*B.size+j.val) = (k.val+1 : ℕ) ∨
      μ (dst+B.size*C.size+A.size*B.size+i.val*C.size+k.val) = (j.val+1 : ℕ) := by
  change A.lower i ≤ C.upper k-B.lower j ∧ C.lower k-B.upper j ≤ A.upper i at hr
  by_cases hfirst : A.lower i < C.lower k-B.upper j
  · left
    rw [ht.1 j j.isLt k k.isLt,lookup_complete A i.isLt (by omega) hr.2]
  · by_cases hsecond : A.lower i+B.lower j ≤ C.lower k
    · right; right
      rw [ht.2.2 i i.isLt k k.isLt,lookup_complete B j.isLt (by omega) (by omega)]
    · right; left
      rw [ht.2.1 i i.isLt j j.isLt,lookup_complete C k.isLt (by omega) (by omega)]

theorem count_eq_owner_count (A B C : Family) :
    count A.size B.size C.size = (owners A B C).length := by
  rw [owners_length]
  unfold count
  ring

theorem time_bound (nA nB nC : ℕ) :
    time nA nB nC ≤ 1000*(count nA nB nC+nA+nB+nC+1)*(width nA nB nC+1) := by
  have heq : time nA nB nC = count nA nB nC*(120*width nA nB nC+190)+
      76*(nB+2*nA)+29*width nA nB nC+553 := by
    unfold time clog2Time powTableTime LightBandTable.time LightBandTable.rowTime
      LightBandLookup.time LightBandLookup.searchTime count width
    ring
  rw [heq]
  generalize count nA nB nC = D
  generalize width nA nB nC = W
  nlinarith [Nat.zero_le (D*W),Nat.zero_le (nA*W),Nat.zero_le (nB*W),Nat.zero_le (nC*W)]

theorem count_mono {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    count a b c ≤ count a' b' c' := by
  unfold count
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul hb hc) (Nat.mul_le_mul ha hb))
    (Nat.mul_le_mul ha hc)

theorem width_mono {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    width a b c ≤ width a' b' c' := Nat.clog_mono_right 2 (by omega)

theorem time_mono {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    time a b c ≤ time a' b' c' := by
  have hw := width_mono ha hb hc
  have hlog := Nat.clog_mono_right 2 (show a+b+c+1 ≤ a'+b'+c'+1 by omega)
  unfold time clog2Time powTableTime LightBandTable.time LightBandTable.rowTime
    LightBandLookup.time LightBandLookup.searchTime
  gcongr

end ThreeSum.LightBandEnumeration
