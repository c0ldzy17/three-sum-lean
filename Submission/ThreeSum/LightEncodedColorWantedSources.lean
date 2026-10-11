import Submission.ThreeSum.LightEncodedColorFiniteSources

/-! # Execute wanted records and shared original source banks consecutively -/

namespace ThreeSum.LightEncodedColorWantedSources

open Light Scales TrimScales BandScales

set_option maxHeartbeats 2500000
set_option maxRecDepth 13000

/-- h,J,cut,A-incidences,length,P,M,cover base,B value/header,C value/header,g. -/
def body (pWanted pSources : ℕ) : Stmt :=
  .call pWanted [v 0,v 1,v 3,v 4,v 5,v 6,v 7] 13 ;;
  .call pSources [v 0,v 1,v 2,v 8,v 9,v 10,v 11,v 12,v 5,v 13,v 7] 0

def joined : Program := ReportingHostRelocation.program LightGuardedWanted.program LightEncodedColorSources.program
def program : Program := joined ++ [body 98 179]

theorem program_length : program.length=181 := rfl

def args (a free bv be cv ce n p M len : ℕ) : List ℤ :=
  [microHalf (inputBits n),blockCount (inputBits n),mu n,a,len,p,M,free,bv,be,cv,ce,bandSize n]

def time (n p M U : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  LightGuardedWanted.time p M (microHalf (inputBits n)) (blockCount (inputBits n)) U xs+
    EncodedColorSourcesCosts.time n p U M+400

def space (free n p M U : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  max (LightGuardedWanted.space free p M (microHalf (inputBits n)) (blockCount (inputBits n)) U xs)
    (SourceFiniteCosts.space (LightEncodedColorFiniteSources.base free n p M xs) n p U M)

def word (n p M U len : ℕ) : ℕ :=
  max (LightGuardedWanted.word p M (microHalf (inputBits n)) (blockCount (inputBits n)) U len)
    (SourceFiniteCosts.word n p U M)

def depth (n M len : ℕ) : ℕ :=
  max (512*microHalf (inputBits n)+blockCount (inputBits n)+Nat.clog 2 M+3*len+13)
    (256*mu n+18)

variable {lim : Limits} {d : ℕ}

theorem program_meets {μ : ℕ → ℤ} {a free av ae bv be cv ce tables rec vals n p U M : ℕ} [NeZero M]
    {originalA originalB originalC A B C xs : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} {rA : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+depth n M xs.length ≤ lim.depth)
    (hn : 0 < n) (hp : 0 < p)
    (hA : originalA.length ≤ n) (hB : originalB.length ≤ n) (hC : originalC.length ≤ n)
    (ha : a+xs.length ≤ free)
    (hav : av+n ≤ free) (hae : ae+2+2*n ≤ free)
    (hbv : bv+n ≤ free) (hbe : be+2+2*n ≤ free)
    (hcv : cv+n ≤ free) (hce : ce+2+2*n ≤ free)
    (htables : tables+ColorBandBounds.count n (bandSize n) ≤ free)
    (hrecords : rec+4*ColorBandBounds.count n (bandSize n) ≤ free)
    (hcatalog : LightBandRawA.space vals (ColorBandBounds.count n (bandSize n)) (bandSize n) ≤ free)
    (hspace : space free n p M U xs ≤ lim.space)
    (hword : (word n p M U xs.length : ℤ) ≤ lim.word)
    (hread : Seg μ a xs) (hvalues : ∀ z ∈ xs, |z| ≤ (U : ℤ))
    (hboundB : ∀ z ∈ originalB, |z| ≤ (U : ℤ)) (hboundC : ∀ z ∈ originalC, |z| ≤ (U : ℤ))
    (H : SourceFiniteData.Normalized μ av ae bv be cv ce tables rec vals (bandSize n) (bandSize_pos n)
      originalA originalB originalC A B C hsA hsB hsC rA) :
    Meets lim program 180 d (args a free bv be cv ce n p M xs.length) μ (time n p M U xs)
      (fun r ν =>
        SourceFiniteData.Normalized ν av ae bv be cv ce tables rec vals (bandSize n) (bandSize_pos n)
          originalA originalB originalC A B C hsA hsB hsC rA ∧
        SourceFiniteData.Stored ν (LightEncodedColorFiniteSources.base free n p M xs) (bandSize n) p
          (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) B C
          (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n)) : ℤ) r ∧
        LightCoverKeyData.Stored ν free (microHalf (inputBits n)) (blockCount (inputBits n)) ∧
        LightWantedSetup.Output ν
          (LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) xs.length) M
          (LightGuardedWanted.left p xs) (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
          (3*xs.length) (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
          (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n))) ∧
        M*(ν (LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) xs.length)).toNat ≤
          3*xs.length*LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)) ∧
        Seg ν (LightCoverKeyData.keyEnd free (microHalf (inputBits n)) (blockCount (inputBits n)))
          (RawAKeyLists.keys p xs) ∧ Kept μ ν free) := by
  have hsWanted : LightGuardedWanted.space free p M (microHalf (inputBits n))
      (blockCount (inputBits n)) U xs ≤ lim.space := (le_max_left _ _).trans hspace
  have hsSource : SourceFiniteCosts.space (LightEncodedColorFiniteSources.base free n p M xs) n p U M ≤
      lim.space := (le_max_right _ _).trans hspace
  have hwWanted : (LightGuardedWanted.word p M (microHalf (inputBits n))
      (blockCount (inputBits n)) U xs.length : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hwSource : (SourceFiniteCosts.word n p U M : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  have hdWanted : d+1+512*microHalf (inputBits n)+blockCount (inputBits n)+Nat.clog 2 M+3*xs.length+12 ≤
      lim.depth := by unfold depth at hd; omega
  have hdSource : d+1+256*mu n+17 ≤ lim.depth := by unfold depth at hd; omega
  have hbase := LightEncodedColorFiniteSources.free_le_base free n p M xs
  have hheader : LightGuardedWanted.wantedFree free (microHalf (inputBits n))
      (blockCount (inputBits n)) xs.length+4 ≤ LightEncodedColorFiniteSources.base free n p M xs :=
    EncodedColorWantedData.header_le_nextFree ..
  apply Meets.of_body (p := 180) (by rfl : program[180]?=some (body 98 179))
  unfold body args time
  have hWanted := ((LightGuardedWanted.program_meets (d := d+1) (μ := μ) (a := a) (free := free)
    xs hw hp ha hsWanted hwWanted hdWanted hread hvalues).append
      (LightEncodedColorSources.program.map (ReportingHostRelocation.relocate 99))).append [body 98 179]
  light_call hWanted with out μ₁ ⟨hout,wanted,hcount,cover,lifts,kept⟩
  have H₁ := H.keep kept hA hB hC hav hae hbv hbe hcv hce htables hrecords hcatalog
  have hSources := (ReportingHostRelocation.meets
    (LightEncodedColorFiniteSources.program_meets (d := d+1) (μ := μ₁) (free := free) (p := p) (U := U) (M := M)
      (xs := xs) hw hdSource hn hp hA hB hC hav hae hbv hbe hcv hce htables hrecords hcatalog
      hsSource hwSource hboundB hboundC H₁ cover wanted) LightGuardedWanted.program).append [body 98 179]
  light_call hSources using LightEncodedColorFiniteSources.args,hout
    with r ν ⟨normalized,sources,cover',wanted',kept'⟩
  refine ⟨normalized,sources,cover',wanted',?_,?_,?_⟩
  · dsimp only
    rw [kept' _ (by omega)]
    exact hcount
  · apply lifts.of_kept kept'
    rw [RawAKeyLists.keys_length]
    unfold LightGuardedWanted.wantedFree at hheader
    omega
  · intro q hq
    exact (kept' q (hq.trans_le hbase)).trans (kept q hq)

end ThreeSum.LightEncodedColorWantedSources
