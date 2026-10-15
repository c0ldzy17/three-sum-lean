import Submission.ThreeSum.TernaryArenaLayout
import Submission.ThreeSum.TernaryFrontendResources

noncomputable section
namespace ThreeSum.TernaryArenaFrontendResources
open Light TernaryArenaLayout TernaryJointType TernaryBank TernaryEuler
open TernaryFrontendResources LightTernaryNearPair LightTernaryQueryPlan
open LightTernaryPreparedWanted TernaryBankStageModel TernaryCodeSemantics
set_option maxHeartbeats 6000000

/-- Prefix dimensions vary while all workspace pointers stay fixed. -/
def config (free C N A bank nb bv T h wsSlot : ℕ) : Config where
  a:=addr free C 54; powers:=addr free C 57; bank:=bank; nb:=nb; bv:=bv
  L:=2*N; T:=T; activeBase:=addr free C 56
  ws:=addr free C wsSlot; rankBase:=addr free C (wsSlot+1)
  vals:=addr free C (wsSlot+2); h:=h
  pcount:=addr free C (wsSlot+3); fr:=addr free C (wsSlot+3)
  U:=sourceZeta N A; V:=eulerBound N A

theorem word_lower (N nb groups count R A : ℕ) :
    100*(N+R+100)≤word N nb groups count R A := by
  unfold word
  generalize (N+1)*nb=s
  generalize 2^(2*N+1)=p
  generalize 4^(N+1)=w
  generalize sourceZeta N A=z
  generalize eulerBound N A=v
  generalize z^2=zz
  generalize 4^N*zz=prod
  omega

theorem resources {lim : Limits} {free C N R A bank nb bv T h wsSlot rows groups count : ℕ}
    (hws : wsSlot=58 ∨ wsSlot=62)
    (hrows : rows≤R) (hR : R≤C) (hN : N≤C) (hpowers : 2*N+1≤C)
    (hmetadata : 2*N*R+N≤C) (hdivision : eulerBound N A+3≤C)
    (hT : T≤2*N) (hh : h≤T) (hnb : nb<2^(2*N)) (hnn : rows<2^(2*N)) (hpos : 0<nb)
    (hbank : bank+nb≤addr free C 54) (hbv : bv+nb≤addr free C 54)
    (hend : finish free C≤lim.space) (hw : (lim.space : ℤ)≤lim.word)
    (hword : (word N nb groups count R A : ℤ)≤lim.word)
    (F : TritWord N→ℤ) (hhom : ∀ W, F W≠0 → rank W=h)
    (hF : ∀ W, |F W|≤(A : ℤ)) :
    Resources lim rows (config free C N A bank nb bv T h wsSlot) F := by
  have hwsLow : 58≤wsSlot := by rcases hws with rfl|rfl <;> omega
  have hwsHigh : wsSlot≤62 := by rcases hws with rfl|rfl <;> omega
  have hrowC : rows≤C := hrows.trans hR
  have hmetaC : 2*N*rows+N≤C := by nlinarith
  have hnear : addr free C 54≤addr free C wsSlot := before (by omega) (by omega : 0≤C)
  have hdivend : addr free C (wsSlot+3)+(eulerBound N A+3)≤lim.space :=
    region_space (by unfold slots; omega) hdivision hend
  have hlog : Nat.log 2 (eulerBound N A+1)≤eulerBound N A+1 := Nat.log_le_self _ _
  obtain ⟨hc,hc',hd,_,_,_,_,_,_⟩ := controls N nb groups count R A
  have hcZ : ((nb+rows+2^(2*N+1)+2*N+32 : ℕ) : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (by omega)).trans hword
  have hdZ : ((4*eulerBound N A+8*N+16 : ℕ) : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr hd).trans hword
  refine {
    homogeneous:=hhom
    division:=?_
    hw:=hw
    ha:=before (by omega) hrowC
    hb:=hbank.trans hnear
    hp:=before (by omega) hpowers
    hactiveSpace:=before (by omega) hN
    hbankVals:=hbv.trans hnear
    hmetadataRanks:=by
      simpa only [config,Nat.add_assoc] using
        (before (free := free) (i := wsSlot) (j := wsSlot+1) (by omega) hmetaC)
    hrankVals:=before (by omega) hrowC
    hvals:=before (by omega) hrowC
    hfr:=by dsimp [config]; omega
    hcount:=before (by omega) hrowC
    hspace:=by dsimp [config]; omega
    hword:=hcZ
    hcontrols:=?_
    hmemoWord:=?_
    hL:=le_rfl
    hnb:=hnb
    hnn:=hnn
    hnbpos:=hpos
    hT:=hT
    hh:=hh
    hvalue:=zeta_abs F hF
    hV:=le_rfl }
  · intro current hl hu
    refine ⟨by dsimp [config] at *; omega,hw,?_,?_⟩
    · dsimp [config]
      have hsZ : ((current-h : ℕ) : ℤ)≤2*(N : ℤ) := by exact_mod_cast (show current-h≤2*N by omega)
      push_cast at hdZ ⊢
      omega
    · dsimp [config]; omega
  · dsimp [config]
    have hcN : T+N+32≤word N nb groups count R A :=
      (show T+N+32≤100*(N+R+100) by omega).trans (word_lower N nb groups count R A)
    exact (Int.ofNat_le.mpr hcN).trans hword
  · dsimp [config]
    have hm : N+rows+2*N+h+20≤word N nb groups count R A :=
      (show N+rows+2*N+h+20≤100*(N+R+100) by omega).trans (word_lower N nb groups count R A)
    exact (Int.ofNat_le.mpr hm).trans hword

theorem plan {lim : Limits} {free C N R A bank nb fbv gbv T fh gh bankValues groups count : ℕ}
    (Q : TritWord N) (E : Enumeration N T nb) (F G : TritWord N→ℤ)
    (hrows : rows Q T≤R) (hR : R≤C) (hN : N≤C) (hpowers : 2*N+1≤C)
    (hmetadata : 2*N*R+N≤C) (hdivision : eulerBound N A+3≤C)
    (hT : T≤2*N) (hfh : fh≤T) (hgh : gh≤T)
    (hnb : nb<2^(2*N)) (hnn : rows Q T<2^(2*N)) (hpos : 0<nb)
    (hbank : bank+nb≤addr free C 54) (hfbv : fbv+nb≤addr free C 54)
    (hgbv : gbv+nb≤addr free C 54) (hH : bankValues+(N+1)*nb≤addr free C 54)
    (hend : finish free C≤lim.space) (hw : (lim.space : ℤ)≤lim.word)
    (hword : (word N nb groups count R A : ℤ)≤lim.word)
    (hFhom : ∀ W, F W≠0 → rank W=fh) (hGhom : ∀ W, G W≠0 → rank W=gh)
    (hF : ∀ W, |F W|≤(A : ℤ)) (hG : ∀ W, |G W|≤(A : ℤ))
    (houtside : T<rank Q)
    (hsorted : ∀ j k, j<k → k<nb → address (E.word j)<address (E.word k)) :
    LightTernaryPreparedState.Plan lim (addr free C 66) bankValues (addr free C 55)
      (config free C N A bank nb fbv T fh 58)
      (config free C N A bank nb gbv T gh 62) Q E F G := by
  have hrowC : rows Q T≤C := hrows.trans hR
  have hrf := resources (Or.inl rfl) hrows hR hN hpowers hmetadata hdivision hT hfh
    hnb hnn hpos hbank hfbv hend hw hword F hFhom hF
  have hrg := resources (Or.inr rfl) hrows hR hN hpowers hmetadata hdivision hT hgh
    hnb hnn hpos hbank hgbv hend hw hword G hGhom hG
  obtain ⟨_,_,_,hsetup,_,hprod,hquery,_,_⟩ := controls N nb groups count R A
  have h54 : addr free C 54≤addr free C 58 := before (by decide) (by omega : 0≤C)
  refine {
    fResources:=hrf
    gResources:=hrg
    outside:=houtside
    ga:=rfl
    gp:=rfl
    gactive:=rfl
    gbank:=rfl
    gnb:=rfl
    gT:=rfl
    bankSorted:=hsorted
    bankBefore:=hbank
    Fbefore:=hfbv
    Gbefore:=hgbv
    Hbefore:=hH
    dst:=before (by decide) hrowC
    caps:=before (by decide) hN
    active:=before (by decide) hN
    setupWord:=(Int.ofNat_le.mpr hsetup).trans hword
    GRead:=?_
    FbeforeG:=before (by decide) hrowC
    Fout:=before (by decide) hrowC
    Gout:=before (by decide) hrowC
    outSpace:=region_space (by decide) hrowC hend
    outKeep:=before (by decide) (by omega : 0≤C)
    productWord:=?_
    queryWord:=?_ }
  · exact ⟨before (by decide) hrowC,hbank.trans h54,before (by decide) hpowers,
      before (by decide) hN,hgbv.trans h54⟩
  · dsimp [config]
    simpa [pow_two] using (Int.ofNat_le.mpr hprod).trans hword
  · dsimp [config]
    simpa [pow_two,Nat.cast_mul,mul_assoc] using (Int.ofNat_le.mpr hquery).trans hword

end ThreeSum.TernaryArenaFrontendResources
