import Submission.ThreeSum.LightTernaryTensorHeader

namespace ThreeSum.LightTernaryQuarticStep
open Light
set_option maxHeartbeats 2400000

def body (pChannel pCount pScatter : ℕ) : Stmt :=
  .call pChannel [v 1,v 2,v 5,v 11,v 12,v 6] 17 ;;
  .call pChannel [v 3,v 4,v 5,v 13,v 14,v 7] 18 ;;
  .call pCount LightTernaryTensorDriver.countArgs 19 ;;
  .call pScatter [v 10,v 8,v 9,v 16,v 15] 0

theorem meets {lim : Limits} {P : Program}
    {pMain pChannel pOffset pProduct pCount pScatter d : ℕ}
    (config ls nL rs nR J wL wR tensor H countOut a b c e q W keep : ℕ)
    (μ : ℕ→ℤ) (L R : ℕ→ℕ→ℤ) (counts : ℕ→ℤ) (argv : List ℤ) (hostTime : ℕ)
    (hmain : P[pMain]?=some (body pChannel pCount pScatter))
    (hChannel : P[pChannel]?=some (LightTernaryTaggedChannel.body pOffset pProduct))
    (hOffset : P[pOffset]?=some LightTernaryTaggedChannel.offsetBody)
    (hProduct : P[pProduct]?=some LightTernaryProductChannel.body)
    (hScatter : P[pScatter]?=some LightTernaryTensorScatter.body)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+1<lim.depth)
    (ha : a<J+2) (hb : b<J+2) (hc : c<J+2) (he : e<J+2) (hq : q<W) (hW : 0<W)
    (hconfig : config+106≤wL) (hconfigSpace : config+106≤lim.space)
    (hls : ls+nL*(J+2)≤wL) (hrs : rs+nR*(J+2)≤wL)
    (hweights : wL+nL≤wR) (hweightsSpace : wR+nR≤lim.space)
    (htensor : tensor+H*W≤wL) (hkeep : wL≤keep)
    (hcount : countOut+H≤lim.space) (hcountSep : tensor+H*W≤countOut)
    (hWword : (W : ℤ)≤lim.word) (hHword : (H : ℤ)≤lim.word)
    (U : ℕ) (hword : ((U : ℤ)+1)^2≤lim.word) (hindex : ((J+3 : ℕ) : ℤ)≤lim.word)
    (hL : ∀ i<nL, ∀ j<J+2, μ (ls+i*(J+2)+TernarySignedLayout.offset J j)=L i j)
    (hR : ∀ i<nR, ∀ j<J+2, μ (rs+i*(J+2)+TernarySignedLayout.offset J j)=R i j)
    (hLb : ∀ i<nL, ∀ j<J+2, |L i j|≤(U : ℤ))
    (hRb : ∀ i<nR, ∀ j<J+2, |R i j|≤(U : ℤ))
    (hlen : argv.length=106) (hargs : ∀ i<106, μ (config+i)=argv.getD i 0)
    (hHost : ∀ ν, SameOutside2 μ ν wL nL wR nR →
      (∀ i<nL, ν (wL+i)=L i a*L i b) → (∀ i<nR, ν (wR+i)=R i c*R i e) →
      Meets lim P pCount (d+1) argv ν hostTime
        (fun _ ξ => Kept ν ξ keep ∧ ∀ j<H, ξ (countOut+j)=counts j)) :
    Meets lim P pMain d
      [config,ls,nL,rs,nR,J,wL,wR,tensor,H,countOut,a,b,c,e,q,W] μ
      (LightTernaryTaggedChannel.time nL+LightTernaryTaggedChannel.time nR+
        hostTime+LightTernaryTensorScatter.time H+1500)
      (fun _ ν => (∀ j<H, ν (tensor+j*W+q)=counts j) ∧
        ∀ x<wL, (∀ j<H, x≠tensor+j*W+q) → ν x=μ x) := by
  apply Meets.of_body hmain
  unfold body
  light_call (LightTernaryTaggedChannel.meets (d := d+1) hChannel hOffset hProduct μ L hw
    (by omega) ha hb hls (by omega) hL hLb hword hindex)
    with rL ν ⟨hleft,hkeepL⟩
  have hRν : ∀ i<nR, ∀ j<J+2,
      ν (rs+i*(J+2)+TernarySignedLayout.offset J j)=R i j := by
    intro i hi j hj
    rw [hkeepL _ (Or.inl (by
      have hoff := TernarySignedLayout.offset_lt hj
      have := Nat.mul_le_mul_right (J+2) (by omega : i+1≤nR)
      nlinarith))]
    exact hR i hi j hj
  light_call (LightTernaryTaggedChannel.meets (d := d+1) hChannel hOffset hProduct ν R hw
    (by omega) hc he (by omega) hweightsSpace hRν hRb hword hindex)
    with rR ξ ⟨hright,hkeepR⟩
  have hleftξ : ∀ i<nL, ξ (wL+i)=L i a*L i b := by
    intro i hi
    rw [hkeepR _ (by omega)]
    exact hleft i hi
  have hboth : SameOutside2 μ ξ wL nL wR nR := by
    intro x hx
    exact (hkeepR x hx.2).trans (hkeepL x hx.1)
  have hargsξ : ∀ i<106, ξ (config+i)=argv.getD i 0 := by
    intro i hi
    rw [hkeepR _ (by omega),hkeepL _ (by omega)]
    exact hargs i hi
  have hhost := hHost ξ hboth hleftξ hright
  refine Ends.callToThen hhost ?_
    (ha := ⟨LightTernaryTensorHeader.args_safe _ config (by simp) hconfigSpace hw,
      LightTernaryTensorHeader.args_values _ config argv (by simp) hlen hargsξ⟩)
    (hT := by simp only [LightTernaryTensorHeader.args_cost]; light_time)
  rintro rCount θ ⟨hprefix,hcounts⟩
  light_call (LightTernaryTensorScatter.meets (d := d+1) hScatter θ hw hW hq hcount
    (by omega) (Or.inr hcountSep) hWword hHword) with rOut ω ⟨hwritten,hrest⟩
  refine ⟨?_,?_⟩
  · intro j hj
    exact (hwritten j hj).trans (hcounts j hj)
  · intro x hx hnot
    change ω x=μ x
    rw [hrest x hnot,hprefix x (by omega),hkeepR x (by omega),hkeepL x (by omega)]

end ThreeSum.LightTernaryQuarticStep
