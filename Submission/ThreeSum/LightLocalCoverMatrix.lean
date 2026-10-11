import Submission.ThreeSum.LightLocalCoverCandidate

/-!
# Constructing every candidate coefficient, histogram, and cover-matrix row

One literal loop visits the radix candidates in increasing index order.
Temporary raw/residue buffers are reused. All candidate coefficient rows,
both histogram tables, and all Boolean matrix rows remain in memory.
-/

namespace ThreeSum.LightLocalCoverMatrix

open Light

set_option maxHeartbeats 2000000
set_option maxRecDepth 6000

def body (pCandidate : ℕ) : Stmt :=
  .set 16 (v 1 *' v 1) ;;
  .for 14 (v 2) (
    .call pCandidate [v 0,v 1,v 14,v 3,v 4,v 5,v 6,
      v 7 +' v 14 *' (k 2 *' v 0),v 8,v 9,
      v 10 +' v 14 *' v 1,v 11 +' v 14 *' v 1,v 12 +' v 14 *' v 16,v 13] 15)

def time (L n p N : ℕ) : ℕ := N*(LightLocalCoverCandidate.time L n p N+200)+30

def Tables (μ : ℕ → ℤ) (L n p cap maps hist0 hist1 dst : ℕ)
    (mask : ℕ → ℕ) (bits : ℕ → ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ j < N,
    LightWeightDecode.Rows μ (maps+j*(2*L)) L p j ∧
    (∀ r < p,
      μ (hist0+j*p+r) = (LightHistogram.count (LightHashHistogram.code L p mask (w0 j) (w1 j)) r n : ℤ) ∧
      μ (hist1+j*p+r) = (LightHistogram.count (LightHashHistogram.code L p mask (w1 j) (w0 j)) r n : ℤ)) ∧
    (∀ r < p*p, μ (dst+j*(p*p)+r) = (LightLocalCoverCandidate.entry L n p cap mask bits (w0 j) (w1 j) r : ℤ))

def Inv (μ : ℕ → ℤ) (L n p cap N masks bitPtr maps raw0 raw1 hist0 hist1 dst work : ℕ)
    (mask : ℕ → ℕ) (bits : ℕ → ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,p,N,n,cap,masks,bitPtr,maps,raw0,raw1,hist0,hist1,dst,work,i,r,p*p],μ'⟩ ∧
    Tables μ' L n p cap maps hist0 hist1 dst mask bits w0 w1 i ∧ Kept μ μ' maps

structure Procs (P : Program) (pMain : ℕ) where
  pCandidate : ℕ
  candidate : LightLocalCoverCandidate.Procs P pCandidate
  main : P[pMain]? = some (body pCandidate)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {L n p cap N masks bitPtr maps raw0 raw1 hist0 hist1 dst work : ℕ}
    (mask : ℕ → ℕ) (bits : ℕ → ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+5 ≤ lim.depth) (hp : 0 < p) (hn : 0 < n)
    (hspace : LightLocalCoverCandidate.space work L n p ≤ lim.space)
    (hmasks : masks+n ≤ maps) (hbits : bitPtr+n*L ≤ maps) (hmaps : maps+N*(2*L) ≤ raw0)
    (hraw0 : raw0+2*n ≤ raw1) (hraw1 : raw1+2*n ≤ hist0)
    (hhist0 : hist0+N*p ≤ hist1) (hhist1 : hist1+N*p ≤ dst) (hdst : dst+N*(p*p) ≤ work)
    (hword : (LightLocalCoverCandidate.word L n p cap N : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hw0 : ∀ j < N, ∀ i < L, w0 j i = WeightEnumeration.digit p (2*L) j (2*i))
    (hw1 : ∀ j < N, ∀ i < L, w1 j i = WeightEnumeration.digit p (2*L) j (2*i+1)) :
    Meets lim P pMain d [L,p,N,n,cap,masks,bitPtr,maps,raw0,raw1,hist0,hist1,dst,work] μ (time L n p N)
      (fun _ μ' => Tables μ' L n p cap maps hist0 hist1 dst mask bits w0 w1 N ∧ Kept μ μ' maps) := by
  have hwork : work ≤ lim.space := by unfold LightLocalCoverCandidate.space at hspace; omega
  have hbudget (x : ℕ) (hx : x ≤ LightLocalCoverCandidate.word L n p cap N) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hNWord := hbudget N (by
    unfold LightLocalCoverCandidate.word LightWeightDecode.word LightWeightRow.word
    omega)
  have hnWord := hbudget n (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hpWord := hbudget p (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hLWord := hbudget L (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hcapWord := hbudget cap (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hWWord := hbudget (2*L) (by
    unfold LightLocalCoverCandidate.word LightWeightDecode.word LightWeightRow.word
    omega)
  have h2Word := hbudget 2 (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hWWordZ : (2 : ℤ)*L ≤ lim.word := by exact_mod_cast hWWord
  have hp2Word := hbudget (p*p) (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hp2WordZ : (p : ℤ)*p ≤ lim.word := by exact_mod_cast hp2Word
  apply Meets.of_body S.main
  unfold body time
  light_set (p*p : ℕ) using LightLocalCoverCandidate.time
  refine Ends.for (Inv μ L n p cap N masks bitPtr maps raw0 raw1 hist0 hist1 dst work mask bits w0 w1)
    N (LightLocalCoverCandidate.time L n p N+192) ?_ ?_ ?_ ?_
    (hT := by light_time [LightLocalCoverCandidate.time])
  · refine ⟨0,μ,?_,?_,fun _ _ => rfl⟩
    · simp [update_frame_setLocal]
    · intro j hj; omega
  · rintro i _ hi _ ⟨r,μ',rfl,written,kept⟩
    have himaps := Nat.mul_le_mul_right (2*L) (show i+1 ≤ N by omega)
    have hihist := Nat.mul_le_mul_right p (show i+1 ≤ N by omega)
    have himatrix := Nat.mul_le_mul_right (p*p) (show i+1 ≤ N by omega)
    simp only [Nat.add_mul,one_mul] at himaps hihist himatrix
    have hcoef : maps+i*(2*L)+2*L ≤ raw0 := by omega
    have hlhist : hist0+i*p+p ≤ hist1+i*p := by omega
    have hrhist : hist1+i*p+p ≤ dst+i*(p*p) := by omega
    have hrow : dst+i*(p*p)+p*p ≤ work := by omega
    have hmulCoef : ((i*(2*L) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (by omega : i*(2*L) ≤ lim.space)).trans hw
    have hmulHist : ((i*p : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (by omega : i*p ≤ lim.space)).trans hw
    have hmulMatrix : ((i*(p*p) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (by omega : i*(p*p) ≤ lim.space)).trans hw
    have hcoefAddr : ((maps : ℤ)+(i : ℤ)*(2*(L : ℤ))).toNat = maps+i*(2*L) := by
      norm_cast
    have hlhistAddr : ((hist0 : ℤ)+(i : ℤ)*p).toNat = hist0+i*p := by norm_cast
    have hrhistAddr : ((hist1 : ℤ)+(i : ℤ)*p).toNat = hist1+i*p := by norm_cast
    have hmatrixAddr : ((dst : ℤ)+(i : ℤ)*((p : ℤ)*p)).toNat = dst+i*(p*p) := by norm_cast
    have hmask' : ∀ j < n, μ' (masks+j) = (mask j : ℤ) := by
      intro j hj
      rw [kept _ (by omega)]
      exact hmaskRead j hj
    have hbits' : ∀ a < n, ∀ j < L, μ' (bitPtr+a*L+j) = (bits a j : ℤ) := by
      intro a ha j hj
      have hm := Nat.mul_le_mul_right L (show a+1 ≤ n by omega)
      simp only [Nat.add_mul,one_mul] at hm
      have hab : bitPtr+a*L+j < maps := by omega
      rw [kept _ hab]
      exact hbitsRead a ha j hj
    have hword' : (LightLocalCoverCandidate.word L n p cap i : ℤ) ≤ lim.word := by
      apply hbudget
      unfold LightLocalCoverCandidate.word LightWeightDecode.word LightWeightRow.word
      omega
    have htime' : LightLocalCoverCandidate.time L n p i ≤ LightLocalCoverCandidate.time L n p N := by
      unfold LightLocalCoverCandidate.time LightWeightDecode.time LightWeightRow.time LightRadixDigit.time
      gcongr
    have hcall := S.candidate.meets (d := d+1) (μ := μ') (L := L) (n := n) (p := p) (cap := cap)
      (index := i) (masks := masks) (bitPtr := bitPtr) (coef := maps+i*(2*L))
      (raw0 := raw0) (raw1 := raw1) (hist0 := hist0+i*p) (hist1 := hist1+i*p)
      (dst := dst+i*(p*p)) (work := work) mask (w0 i) (w1 i) bits
      hw (by omega) hp hn hspace (by omega) (by omega) hcoef hraw0 (by omega) hlhist hrhist hrow
      hword' hmask' hmaskLt hbits' hbitsValue (hw0 i hi) (hw1 i hi)
    light_call (hcall.mono_time htime') using hcoefAddr,hlhistAddr,hrhistAddr,hmatrixAddr,
      LightLocalCoverCandidate.time with value μ₁ ⟨hcoeffs,hcounts,hentry,hpres⟩
    have hprevCoef : ∀ j < i, ∀ a < 2*L,
        μ₁ (maps+j*(2*L)+a) = μ' (maps+j*(2*L)+a) := by
      intro j hj a ha
      have hjm := Nat.mul_le_mul_right (2*L) (show j+1 ≤ i by omega)
      simp only [Nat.add_mul,one_mul] at hjm
      have hbefore : maps+j*(2*L)+a < maps+i*(2*L) := by omega
      exact hpres _ (by omega) (Or.inl hbefore) (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    have hprevLeft : ∀ j < i, ∀ a < p,
        μ₁ (hist0+j*p+a) = μ' (hist0+j*p+a) := by
      intro j hj a ha
      have hjm := Nat.mul_le_mul_right p (show j+1 ≤ i by omega)
      simp only [Nat.add_mul,one_mul] at hjm
      have hbefore : hist0+j*p+a < hist0+i*p := by omega
      have hbound : hist0+j*p+a < hist1 := by omega
      exact hpres _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inl hbefore) (Or.inl (by omega)) (Or.inl (by omega))
    have hprevRight : ∀ j < i, ∀ a < p,
        μ₁ (hist1+j*p+a) = μ' (hist1+j*p+a) := by
      intro j hj a ha
      have hjm := Nat.mul_le_mul_right p (show j+1 ≤ i by omega)
      simp only [Nat.add_mul,one_mul] at hjm
      have hbefore : hist1+j*p+a < hist1+i*p := by omega
      have hbound : hist1+j*p+a < dst := by omega
      have hleft : hist0+i*p+p ≤ hist1 := by omega
      exact hpres _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inl hbefore) (Or.inl (by omega))
    have hprevMatrix : ∀ j < i, ∀ a < p*p,
        μ₁ (dst+j*(p*p)+a) = μ' (dst+j*(p*p)+a) := by
      intro j hj a ha
      have hjm := Nat.mul_le_mul_right (p*p) (show j+1 ≤ i by omega)
      simp only [Nat.add_mul,one_mul] at hjm
      have hbefore : dst+j*(p*p)+a < dst+i*(p*p) := by omega
      have hleft : hist0+i*p+p ≤ hist1 := by omega
      have hright : hist1+i*p+p ≤ dst := by omega
      exact hpres _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl hbefore)
    refine ⟨by simp,value,μ₁,by simp [update_frame_setLocal],?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · obtain ⟨hc,hh,he⟩ := written j hj
        refine ⟨?_,?_,?_⟩
        · intro a ha
          constructor
          · rw [hprevCoef j hj a (by omega)]
            exact (hc a ha).1
          · have ha' : L+a < 2*L := by omega
            have hkeep := hprevCoef j hj (L+a) ha'
            rw [← Nat.add_assoc] at hkeep
            rw [hkeep]
            exact (hc a ha).2
        · intro a ha
          rw [hprevLeft j hj a ha,hprevRight j hj a ha]
          exact hh a ha
        · intro a ha
          rw [hprevMatrix j hj a ha]
          exact he a ha
      · exact ⟨hcoeffs,hcounts,hentry⟩
    · intro a ha
      rw [hpres a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
      exact kept a ha
  · rintro _ _ ⟨r,μ',rfl,written,kept⟩
    exact ⟨written,kept⟩
  · rintro i _ _ _ ⟨r,μ',rfl,_,_⟩
    light_side

def program : Program :=
  [body 1,LightLocalCoverCandidate.body 2 7 14,LightWeightDecode.body 3 4,powTableBody,
    LightWeightRow.body 5,LightRadixDigit.body 6,LightSmallDivide.body,
    LightHashHistogram.body 8 10 12,LightMaskHashes.body 3 9,LightOneHot.body 9,
    LightResidues.residuesBody 11,emodBody,LightHistogram.histogramBody 13,fillBody,
    LightLocalCoverRow.body 15 18,LightPairFlags.body 6 16 17,LightBooleanDot.body,
    LightTrimTest.body,LightSupportMark.body 13]

def programProcs : Procs program 0 :=
  ⟨1,⟨2,7,14,⟨3,4,5,6,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨8,3,9,10,11,12,13,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨15,6,16,17,18,13,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩

end ThreeSum.LightLocalCoverMatrix
