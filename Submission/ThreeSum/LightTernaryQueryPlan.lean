import Submission.ThreeSum.LightTernaryWantedQuery
import Submission.ThreeSum.LightTernaryNearSetup

/-! Reconstruction resources separated from the memory reads furnished by
actual setup and the retained banks. -/
namespace ThreeSum.LightTernaryQueryPlan
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.LightTernaryNearPair

structure Resources (lim : Limits) {N : ℕ} (rows : ℕ) (c : Config)
    (source : TritWord N→ℤ) : Prop where
  homogeneous : ∀ A, source A≠0 → rank A=c.h
  division : ∀ current, c.T<current → current≤2*N → Light.Emod.Pre lim (current-c.h) c.V c.fr
  hw : (lim.space : ℤ)≤lim.word
  ha : c.a+rows≤c.ws
  hb : c.bank+c.nb≤c.ws
  hp : c.powers+(2*N+1)≤c.ws
  hactiveSpace : c.activeBase+N≤c.ws
  hbankVals : c.bv+c.nb≤c.ws
  hmetadataRanks : c.ws+2*N*rows+N≤c.rankBase
  hrankVals : c.rankBase+rows≤c.vals
  hvals : c.vals+rows≤c.fr
  hfr : c.fr≤lim.space
  hcount : c.vals+rows≤c.pcount
  hspace : c.pcount≤lim.space
  hword : ((c.nb+rows+2^(2*N+1)+2*N+32 : ℕ) : ℤ)≤lim.word
  hcontrols : ((c.T+N+32 : ℕ) : ℤ)≤lim.word
  hmemoWord : ((N+rows+2*N+c.h+20 : ℕ) : ℤ)≤lim.word
  hL : c.L≤2*N
  hnb : c.nb<2^c.L
  hnn : rows<2^c.L
  hnbpos : 0<c.nb
  hT : c.T≤2*N
  hh : c.h≤c.T
  hvalue : ∀ R, |binomialZeta source R|≤c.U
  hV : 2*(N+1)*c.U≤c.V

theorem ready {lim : Limits} {N rows : ℕ} {c : Config} {μ : ℕ→ℤ}
    {Q : TritWord N} {bankWords nearWords : ℕ→TritWord N} {source : TritWord N→ℤ}
    (R : Resources lim rows c source)
    (hread : ∀ j<rows, μ (c.a+j)=(address (nearWords j) : ℤ))
    (hbankRead : ∀ j<c.nb, μ (c.bank+j)=(address (bankWords j) : ℤ))
    (hactiveRead : ∀ i<N, μ (c.activeBase+i)=1)
    (hpowers : Powers μ c.powers (2*N))
    (hbankValues : ∀ j<c.nb, μ (c.bv+j)=binomialZeta source (bankWords j))
    (hbankSorted : ∀ j k, j<k → k<c.nb → address (bankWords j)<address (bankWords k))
    (hnearSorted : ∀ j k, j<k → k<rows → address (nearWords j)<address (nearWords k))
    (hbankPresent : ∀ W, rank W≤c.T → ∃ j<c.nb, bankWords j=W)
    (hnearPresent : ∀ W, Below W Q → c.T<rank W → ∃ j<rows, nearWords j=W)
    (hnearRows : ∀ j<rows, Below (nearWords j) Q ∧ c.T<rank (nearWords j)) :
    Ready lim rows c μ Q bankWords nearWords source := by
  exact { R with
    hread := hread
    hbankRead := hbankRead
    hactiveRead := hactiveRead
    hpowers := hpowers
    hbankValues := hbankValues
    hbankSorted := hbankSorted
    hnearSorted := hnearSorted
    hbankPresent := hbankPresent
    hnearPresent := hnearPresent
    hnearRows := hnearRows }

end ThreeSum.LightTernaryQueryPlan
