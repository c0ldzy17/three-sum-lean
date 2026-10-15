import Submission.ThreeSum.TernaryPhysicalEuler

/-! Actual rank, predecessor-metadata, and ascending-rank near-source construction. -/
namespace ThreeSum.LightTernaryNearSource

open Light ThreeSum.LightSubsetAddress
open ThreeSum.LightTernaryEulerMetadata

set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

def body (pRanks pMetadata pMemo : ℕ) : Stmt :=
  .call pRanks [v 0,v 1,v 2,v 3,v 11] 17 ;;
  .call pMetadata [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 1,v 2,v 12,v 7,v 8,v 9,v 10] 17 ;;
  .call pMemo [v 0,v 2,v 10,v 10 +' v 0 *' v 2,v 11,v 12,v 8,v 13,v 14,v 15,v 16] 17 ;;
  .set 0 (k 0)

def time (N L rows stages V : ℕ) : ℕ := LightTernaryRankTable.time N rows+
  LightTernaryEulerMetadata.time N L rows+LightTernaryEulerMemo.time N rows stages V+500

def weights (N : ℕ) (codes active : ℕ → ℕ) (j i : ℕ) : ℕ :=
  LightTernaryPredecessor.weight N (lowAt N i) (highAt N i) (codes j) (active i)

def keys (N rows T bv vals : ℕ) (codes active : ℕ → ℕ) (bi ni : ℕ → ℕ → ℕ) (j i : ℕ) : ℕ :=
  LightTernaryPredecessor.key N (lowAt N i) (highAt N i) (codes j) T (active i) bv vals (bi i j) (ni i j)

def ranks (N : ℕ) (codes : ℕ → ℕ) (j : ℕ) : ℕ := LightTernaryRank.partialRank N (codes j) N

variable {lim : Limits} {P : Program}

theorem meets {pMain pRanks pMetadata pMemo pColumn pCell pDigit pZero pErase pRank pSearch
    pScan pFill pRow pSum pDivide pNaturalDivide N a rows powers bank nb bv L T activeBase ws rankBase
    vals h maxRank pcount fr U V d : ℕ}
    (hmain : P[pMain]?=some (body pRanks pMetadata pMemo))
    (hranks : P[pRanks]?=some (LightTernaryRankTable.body pRank))
    (hmetadata : P[pMetadata]?=some (LightTernaryEulerMetadata.body pColumn))
    (hmemo : P[pMemo]?=some (LightTernaryEulerMemo.body pScan))
    (hcolumn : P[pColumn]?=some (LightTernaryPredecessorTable.body pCell pDigit))
    (hcell : P[pCell]?=some (LightTernaryPredecessor.body pDigit pZero pErase pRank pSearch))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hrank : P[pRank]?=some (LightTernaryRank.body pDigit))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (hscan : P[pScan]?=some (LightTernaryEulerScan.body pFill))
    (hfill : P[pFill]?=some (LightTernaryEulerRow.fillBody pRow))
    (hrow : P[pRow]?=some (LightTernaryEulerRow.body pSum pDivide))
    (hsum : P[pSum]?=some LightTernaryWeightedSum.body)
    (hdivide : P[pDivide]?=some (LightTernaryDivide.body pNaturalDivide))
    (hnatural : P[pNaturalDivide]?=some LightOutputDecodeDivide.body)
    (μ : ℕ → ℤ) (codes bankCodes active : ℕ → ℕ) (bi ni : ℕ → ℕ → ℕ)
    (g f : ℕ → ℤ)
    (F : ∀ current, T<current → current≤maxRank → Light.Emod.Pre lim (current-h) V fr)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+rows≤ws) (hb : bank+nb≤ws) (hp : powers+(2*N+1)≤ws)
    (hactiveSpace : activeBase+N≤ws) (hbankVals : bv+nb≤ws)
    (hmetadataRanks : ws+2*N*rows+N≤rankBase)
    (hrankVals : rankBase+rows≤vals) (hvals : vals+rows≤fr) (hfr : fr≤lim.space)
    (hspace : pcount≤lim.space)
    (hword : ((nb+rows+2^(2*N+1)+2*N+32 : ℕ) : ℤ)≤lim.word)
    (hcontrols : ((T+N+32 : ℕ) : ℤ)≤lim.word)
    (hmemoWord : ((N+rows+maxRank+h+20 : ℕ) : ℤ)≤lim.word)
    (hread : ∀ j<rows, μ (a+j)=(codes j : ℤ))
    (hbankRead : ∀ j<nb, μ (bank+j)=(bankCodes j : ℤ))
    (hactiveRead : ∀ i<N, μ (activeBase+i)=(active i : ℤ))
    (hbankSorted : ∀ j k, j<k → k<nb → bankCodes j<bankCodes k)
    (hnearSorted : ∀ j k, j<k → k<rows → codes j<codes k)
    (hpowers : Powers μ powers (2*N)) (hcodes : ∀ j<rows, codes j<2^(2*N))
    (hL : L≤2*N) (hnb : nb<2^L) (hnn : rows<2^L) (hnbpos : 0<nb)
    (hactive : ∀ i<N, active i≤1)
    (hbi : ∀ i<N, ∀ j<rows, active i≠0 → LightTernaryPredecessor.digit N (lowAt N i) (highAt N i) (codes j)≠0 →
      LightTernaryPredecessor.predRank N (lowAt N i) (highAt N i) (codes j)≤T →
      bi i j<nb ∧ bankCodes (bi i j)=LightTernaryPredecessor.code N (lowAt N i) (highAt N i) (codes j))
    (hni : ∀ i<N, ∀ j<rows, active i≠0 → LightTernaryPredecessor.digit N (lowAt N i) (highAt N i) (codes j)≠0 →
      T<LightTernaryPredecessor.predRank N (lowAt N i) (highAt N i) (codes j) →
      ni i j<rows ∧ codes (ni i j)=LightTernaryPredecessor.code N (lowAt N i) (highAt N i) (codes j))
    (hT : T≤maxRank) (hh : h≤T)
    (hrankRange : ∀ j<rows, T<ranks N codes j ∧ ranks N codes j≤maxRank)
    (hrange : ∀ j<rows, ∀ i<N, keys N rows T bv vals codes active bi ni j i<pcount ∧
      keys N rows T bv vals codes active bi ni j i<fr)
    (hbank : ∀ j<rows, ∀ i<N, keys N rows T bv vals codes active bi ni j i<vals →
      keys N rows T bv vals codes active bi ni j i<ws ∧
      μ (keys N rows T bv vals codes active bi ni j i)=g (keys N rows T bv vals codes active bi ni j i))
    (hmemoval : ∀ j<rows, g (vals+j)=f j)
    (hweight : ∀ j<rows, ∀ i<N, weights N codes active j i≤2)
    (hvalue : ∀ j<rows, ∀ i<N, |g (keys N rows T bv vals codes active bi ni j i)|≤U)
    (hpre : ∀ j<rows, ∀ i<N, keys N rows T bv vals codes active bi ni j i<vals ∨
      ∃ k<rows, keys N rows T bv vals codes active bi ni j i=vals+k ∧ ranks N codes k<ranks N codes j)
    (hEuler : ∀ j<rows, LightTernaryWeightedSum.sum (weights N codes active j)
      (keys N rows T bv vals codes active bi ni j) g N=(ranks N codes j-h : ℕ)*f j)
    (hV : 2*(N+1)*U≤V) (hd : d+2*N+7≤lim.depth) :
    Meets lim P pMain d [N,a,rows,powers,bank,nb,bv,L,T,activeBase,ws,rankBase,vals,h,maxRank,pcount,fr]
      μ (time N L rows (maxRank-T) V)
      (fun r ν => r=0 ∧ Kept μ ν ws ∧ ∀ j<rows, ν (vals+j)=f j) := by
  have hmetaRanks : ws+2*(N*rows)+N≤rankBase := by
    simpa only [Nat.mul_assoc] using hmetadataRanks
  have hmetaSpan : ws+2*N*rows+N≤lim.space := by omega
  have hrSpan : rankBase+rows≤lim.space := by omega
  have hrCall := LightTernaryRankTable.meets (d := d+1) hranks hrank hdigit herase μ codes hw
    (by omega) (by omega) hrSpan (by omega) (by omega) hread hpowers hcodes (by omega)
  apply Meets.of_body hmain
  unfold body time
  light_call hrCall using LightTernaryRankTable.time,LightTernaryEulerMetadata.time,LightTernaryEulerMemo.time
    with r₁ ν ⟨hRankRead,hRankOutside⟩
  have hν {x : ℕ} (hx : x<ws) : ν x=μ x := hRankOutside x (Or.inl (by omega))
  have hRead : ∀ j<rows, ν (a+j)=(codes j : ℤ) := by
    intro j hj; rw [hν (by omega),hread j hj]
  have hbRead : ∀ j<nb, ν (bank+j)=(bankCodes j : ℤ) := by
    intro j hj; rw [hν (by omega),hbankRead j hj]
  have haRead : ∀ i<N, ν (activeBase+i)=(active i : ℤ) := by
    intro i hi; rw [hν (by omega),hactiveRead i hi]
  have hPowers : Powers ν powers (2*N) := by
    intro i hi; rw [hν (by omega),hpowers i hi]
  have hmCall := LightTernaryEulerMetadata.meets (d := d+1) (bv := bv) (nv := vals) hmetadata hcolumn hcell hdigit hzero herase hrank hsearch
    ν codes bankCodes codes active bi ni hw ha hb ha hp hactiveSpace hmetaSpan
    (by omega) (by omega) hword hcontrols hRead hbRead hRead haRead hbankSorted hnearSorted hPowers hcodes
    hL hnb hnn hnbpos hactive hbi hni (by omega)
  light_call hmCall using LightTernaryRankTable.time,LightTernaryEulerMetadata.time,LightTernaryEulerMemo.time
    with r₂ ξ ⟨hRecords,hMetadataOutside⟩
  have hξ {x : ℕ} (hx : x<ws) : ξ x=μ x := (hMetadataOutside x (Or.inl hx)).trans (hν hx)
  have hRanks : ∀ j<rows, ξ (rankBase+j)=(ranks N codes j : ℤ) := by
    intro j hj
    rw [hMetadataOutside _ (Or.inr (by omega))]
    exact hRankRead j hj
  have hWeights : ∀ j<rows, ∀ i<N, ξ (ws+N*j+i)=(weights N codes active j i : ℤ) := by
    intro j hj i hi
    exact (hRecords i hi j hj).1
  have hKeys : ∀ j<rows, ∀ i<N, ξ (ws+N*rows+N*j+i)=(keys N rows T bv vals codes active bi ni j i : ℤ) := by
    intro j hj i hi
    simpa only [RecordAt,rowAddr,keys,Nat.mul_add,Nat.add_assoc] using (hRecords i hi j hj).2
  have hc := LightTernaryEulerMemo.meets (d := d+1) hmemo hscan hfill hrow hsum hdivide hnatural
    ξ (weights N codes active) (keys N rows T bv vals codes active bi ni) g f (ranks N codes)
    F hT hh (by omega) (by omega) hrankVals hvals hspace hRanks hrankRange hWeights hKeys
    hrange (fun j hj i hi hk => by rw [hξ (hbank j hj i hi hk).1]; exact (hbank j hj i hi hk).2)
    hmemoval hweight hvalue hpre hEuler hV (by omega) hmemoWord hw hfr
  light_call hc using LightTernaryRankTable.time,LightTernaryEulerMetadata.time,LightTernaryEulerMemo.time
    with r₃ η ⟨hr₃,hKept,hValues⟩
  light_set 0 using LightTernaryRankTable.time,LightTernaryEulerMetadata.time,LightTernaryEulerMemo.time
  refine ⟨rfl,?_,hValues⟩
  intro x hx
  exact (hKept x (by omega)).trans (hξ hx)

/-- The entire initialization and memo computation costs only a polynomial in
the word dimension and value bit length per actually stored near row. -/
theorem time_bound {N L rows stages V : ℕ} (hstages : stages≤2*N) :
    time N L rows stages V≤
      11000*(N+L+Nat.log 2 (V+1)+3)^3*(rows+1) := by
  let K := N+L+Nat.log 2 (V+1)+3
  have hK : 1≤K := by omega
  have hN : N+1≤K := by omega
  have hNL : N+L+1≤K := by omega
  have hNlog : N+Nat.log 2 (V+1)+3≤K := by omega
  have hpow : K^2≤K^3 := Nat.pow_le_pow_right hK (by decide)
  have hRank := LightTernaryRankTable.time_bound N rows
  have hMeta := LightTernaryEulerMetadata.time_bound N L rows
  have hMemo := LightTernaryEulerMemo.time_bound N rows stages V
  have hr : LightTernaryRankTable.time N rows≤2000*K^3*(rows+1) := by
    calc
      _≤2000*(N+1)^2*(rows+1) := hRank
      _≤2000*K^2*(rows+1) := by gcongr
      _≤2000*K^3*(rows+1) := by gcongr
  have hm : LightTernaryEulerMetadata.time N L rows≤5000*K^3*(rows+1) := by
    calc
      _≤5000*(N+L+1)^3*(rows+1) := hMeta
      _≤5000*K^3*(rows+1) := by gcongr
  have he : LightTernaryEulerMemo.time N rows stages V≤2700*K^3*(rows+1) := by
    have hs : stages+1≤3*K := by omega
    have ht : 400*(N+Nat.log 2 (V+1)+3)+500≤900*K := by omega
    calc
      _≤(stages+1)*(rows+1)*(400*(N+Nat.log 2 (V+1)+3)+500) := hMemo
      _≤(3*K)*(rows+1)*(900*K) := by gcongr
      _=2700*K^2*(rows+1) := by ring
      _≤2700*K^3*(rows+1) := by gcongr
  have hlarge : 1≤K^3*(rows+1) := by
    have hkpow : 1≤K^3 := one_le_pow₀ hK
    nlinarith
  unfold time
  change _≤11000*K^3*(rows+1)
  nlinarith only [hr,hm,he,hlarge]

end ThreeSum.LightTernaryNearSource
