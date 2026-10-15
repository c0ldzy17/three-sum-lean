import Submission.ThreeSum.LightTernaryBankSweep

/-! Concrete retained-stage sweeps. Every coordinate call uses the actual
metadata constructor and compact lookup pass. -/
namespace ThreeSum.LightTernaryBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem forward_bound {N : ℕ} (k : ℕ) (hk : k≤N)
    (F : TritWord N→ℤ) (V : ℕ) (hF : ∀ R, |F R|≤(V : ℤ)) (R : TritWord N) :
    |forwardStage k F R|≤((4^N*V : ℕ) : ℤ) := by
  have hb := forwardStage_abs k hk F V hF R
  have hp : 4^k≤4^N := Nat.pow_le_pow_right (by omega) hk
  have hm := Nat.mul_le_mul_right V hp
  have hmz : ((4^k : ℕ) : ℤ)*(V : ℤ)≤((4^N*V : ℕ) : ℤ) := by exact_mod_cast hm
  exact hb.trans hmz

theorem inverse_bound {N : ℕ} (k : ℕ) (hk : k≤N)
    (H : TritWord N→ℤ) (V : ℕ) (hH : ∀ R, |H R|≤(V : ℤ)) (R : TritWord N) :
    |stageValue k H R|≤((4^N*V : ℕ) : ℤ) := by
  have hb := stageValue_abs k hk H V hH R
  have hp : 4^k≤4^N := Nat.pow_le_pow_right (by omega) hk
  have hm := Nat.mul_le_mul_right V hp
  have hmz : ((4^k : ℕ) : ℤ)*(V : ℤ)≤((4^N*V : ℕ) : ℤ) := by exact_mod_cast hm
  exact hb.trans hmz

theorem zeta_meets {N T n pMain pCoord pMeta pZero pDigit pErase pPass pCell pSearch pValue
    a powers L keyBase base d V : ℕ}
    (hmain : P[pMain]?=some (LightTernaryBankSweep.body pCoord))
    (hcoord : P[pCoord]?=some (LightTernaryBankCoordinate.body pMeta pPass))
    (hmetaProg : P[pMeta]?=some (LightTernaryMetadata.body pZero pDigit pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hpass : P[pPass]?=some (LightTernaryPass.body pCell))
    (hcell : P[pCell]?=some (LightTernaryLookup.body pSearch pValue))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (hvalue : P[pValue]?=some LightTernaryCell.zetaBody)
    (E : Enumeration N T n) (F : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hmeta : keyBase+4*n≤powers)
    (hpows : powers+(2*N+1)≤base) (hspace : base+(N+1)*n≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsource : ∀ j<n, μ (base+j)=F (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hF : ∀ R, |F R|≤(V : ℤ)) (hvalword : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+5≤lim.depth) :
    Meets lim P pMain d [N,a,n,powers,L,keyBase,base] μ (time N L n)
      (fun _ μ' => Stages E (fun s => forwardStage s F) base N μ' ∧
        Preserved μ μ' keyBase n base N ∧ Powers μ' powers (2*N)) := by
  apply meets_core hmain E (fun s => forwardStage s F) μ hw ha hmeta hpows hspace
    hNword hL hcodes (by simpa using hsource) hpowers (by omega)
  intro k hk μ' hcodes' hpowers' hsource'
  have hmul := Nat.mul_le_mul_right n (show k+2≤N+1 by omega)
  have hcc := LightTernaryBankCoordinate.zeta_meets (d := d+1) (src := base+k*n) (dst := base+(k+1)*n)
    hcoord hmetaProg hzero hdigit herase hpass hcell hsearch hvalue
    E ⟨k,hk⟩ (forwardStage k F) μ' hw ha hmeta
    (by omega) (by nlinarith) (by nlinarith)
    hword hNword hcodes' hsource' hpowers' hsorted
    (fun j _ => forward_bound k (by omega) F V hF (E.word j)) hvalword hL hn (by omega)
  simpa only [forwardStage_succ hk,Nat.cast_add,Nat.cast_mul,Nat.cast_one] using hcc

theorem inverse_meets {N T n pMain pCoord pMeta pZero pDigit pErase pPass pCell pSearch pValue
    a powers L keyBase base d V : ℕ}
    (hmain : P[pMain]?=some (LightTernaryBankSweep.body pCoord))
    (hcoord : P[pCoord]?=some (LightTernaryBankCoordinate.body pMeta pPass))
    (hmetaProg : P[pMeta]?=some (LightTernaryMetadata.body pZero pDigit pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hpass : P[pPass]?=some (LightTernaryInversePass.body pCell))
    (hcell : P[pCell]?=some (LightTernaryLookup.body pSearch pValue))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (hvalue : P[pValue]?=some LightTernaryCell.inverseBody)
    (E : Enumeration N T n) (H : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hmeta : keyBase+4*n≤powers)
    (hpows : powers+(2*N+1)≤base) (hspace : base+(N+1)*n≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsource : ∀ j<n, μ (base+j)=H (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hH : ∀ R, |H R|≤(V : ℤ)) (hvalword : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+5≤lim.depth) :
    Meets lim P pMain d [N,a,n,powers,L,keyBase,base] μ (time N L n)
      (fun _ μ' => Stages E (fun s => stageValue s H) base N μ' ∧
        Preserved μ μ' keyBase n base N ∧ Powers μ' powers (2*N)) := by
  apply meets_core hmain E (fun s => stageValue s H) μ hw ha hmeta hpows hspace
    hNword hL hcodes (by simpa using hsource) hpowers (by omega)
  intro k hk μ' hcodes' hpowers' hsource'
  have hmul := Nat.mul_le_mul_right n (show k+2≤N+1 by omega)
  have hcc := LightTernaryBankCoordinate.inverse_meets (d := d+1) (src := base+k*n) (dst := base+(k+1)*n)
    hcoord hmetaProg hzero hdigit herase hpass hcell hsearch hvalue
    E ⟨k,hk⟩ (stageValue k H) μ' hw ha hmeta
    (by omega) (by nlinarith) (by nlinarith)
    hword hNword hcodes' hsource' hpowers' hsorted
    (fun j _ => inverse_bound k (by omega) H V hH (E.word j)) hvalword hL hn (by omega)
  simpa only [stageValue_succ hk,coordinateInverse,Nat.cast_add,Nat.cast_mul,Nat.cast_one] using hcc

/-- Ten procedures, including real metadata, binary compact lookup, and the
arithmetic value kernel. The argument toggles only the finite value/pass code. -/
def program (inverse : Bool) : Program :=
  [LightTernaryBankSweep.body 1,
   LightTernaryBankCoordinate.body 2 6,
   LightTernaryMetadata.body 3 4 5,
   LightTernaryCodes.zeroBody 5,
   LightTernaryCodes.digitBody 5,
   LightMaskErase.body 5,
   if inverse then LightTernaryInversePass.body 7 else LightTernaryPass.body 7,
   LightTernaryLookup.body 8 9,
   LightBandLookup.searchBody 8,
   if inverse then LightTernaryCell.inverseBody else LightTernaryCell.zetaBody]

@[simp] theorem program_length (inverse : Bool) : (program inverse).length=10 := by rfl

theorem zeta_program_meets {N T n a powers L keyBase base d V : ℕ}
    (E : Enumeration N T n) (F : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hmeta : keyBase+4*n≤powers)
    (hpows : powers+(2*N+1)≤base) (hspace : base+(N+1)*n≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsource : ∀ j<n, μ (base+j)=F (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hF : ∀ R, |F R|≤(V : ℤ)) (hvalword : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+5≤lim.depth) :
    Meets lim (program false) 0 d [N,a,n,powers,L,keyBase,base] μ (time N L n)
      (fun _ μ' => Stages E (fun s => forwardStage s F) base N μ' ∧
        Preserved μ μ' keyBase n base N ∧ Powers μ' powers (2*N)) := by
  exact zeta_meets (pMain := 0) (pCoord := 1) (pMeta := 2) (pZero := 3)
    (pDigit := 4) (pErase := 5) (pPass := 6) (pCell := 7) (pSearch := 8) (pValue := 9)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    E F μ hw ha hmeta hpows hspace hword hNword hcodes hsource hpowers hsorted
    hF hvalword hL hn hd

theorem inverse_program_meets {N T n a powers L keyBase base d V : ℕ}
    (E : Enumeration N T n) (H : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hmeta : keyBase+4*n≤powers)
    (hpows : powers+(2*N+1)≤base) (hspace : base+(N+1)*n≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsource : ∀ j<n, μ (base+j)=H (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hH : ∀ R, |H R|≤(V : ℤ)) (hvalword : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+5≤lim.depth) :
    Meets lim (program true) 0 d [N,a,n,powers,L,keyBase,base] μ (time N L n)
      (fun _ μ' => Stages E (fun s => stageValue s H) base N μ' ∧
        Preserved μ μ' keyBase n base N ∧ Powers μ' powers (2*N)) := by
  exact inverse_meets (pMain := 0) (pCoord := 1) (pMeta := 2) (pZero := 3)
    (pDigit := 4) (pErase := 5) (pPass := 6) (pCell := 7) (pSearch := 8) (pValue := 9)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    E H μ hw ha hmeta hpows hspace hword hNword hcodes hsource hpowers hsorted
    hH hvalword hL hn hd

end ThreeSum.LightTernaryBankStages
