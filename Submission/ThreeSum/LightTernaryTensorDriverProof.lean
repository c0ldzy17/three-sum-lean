import Submission.ThreeSum.LightTernaryTensorDriver

noncomputable section
namespace ThreeSum.LightTernaryTensorDriver
open Light
open scoped BigOperators
set_option maxHeartbeats 4000000

def digit (J q i : ℕ) : ℕ := WeightEnumeration.digit (J+2) 4 q i

def InputKept (μ ν : ℕ→ℤ) (cut tensor H W : ℕ) : Prop := KeptBut μ ν cut tensor (H*W)

def Inv (μ : ℕ→ℤ) (vals : List ℤ) (J H tensor cut pow : ℕ)
    (T : ℕ→ℕ→ℤ) (q : ℕ) (σ : State) : Prop :=
  ∃ (powRet rowRet stepRet : ℤ) (ν : ℕ→ℤ),
    σ=⟨frame (vals++([J+2,(J+2)^4,powRet,q,rowRet,stepRet] : List ℤ)),ν⟩ ∧
    InputKept μ ν cut tensor H ((J+2)^4) ∧
    (∀ e≤4, ν (pow+e)=(((J+2)^e : ℕ) : ℤ)) ∧
    (∀ w<H, ∀ z<q, ν (tensor+w*((J+2)^4)+z)=T w z)

theorem meets {lim : Limits} {P : Program}
    {pMain pPowers pRow pDigit pDivide pStep pBatch d : ℕ}
    (K config ls nL rs nR J wL wR tensor H countOut quad powers cols potPowers : ℕ)
    (μ : ℕ→ℤ) (T : ℕ→ℕ→ℤ) (hostTime : ℕ)
    (hmain : P[pMain]?=some (body pPowers pRow pStep pBatch))
    (hPowers : P[pPowers]?=some powTableBody)
    (hRow : P[pRow]?=some (LightWeightRow.body pDigit))
    (hDigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hDivide : P[pDivide]?=some LightSmallDivide.body)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+4<lim.depth)
    (hTend : tensor+H*(J+2)^4≤quad) (hquad : quad+4≤powers) (hpow : powers+5≤wL)
    (hwL : wL≤lim.space) (hwR : wR≤lim.space) (hcols : cols≤lim.space) (hpot : potPowers≤lim.space)
    (hspace : quad+4≤lim.space) (hpowSpace : powers+5≤lim.space)
    (hJword : ((J+3 : ℕ) : ℤ)≤lim.word)
    (hHword : (H : ℤ)≤lim.word)
    (hWword : (((J+2)^4 : ℕ) : ℤ)≤lim.word)
    (hRowWord : (LightWeightRow.word 4 (J+2) ((J+2)^4) 0 1 : ℤ)≤lim.word)
    (hStep : ∀ q<(J+2)^4, ∀ ν,
      InputKept μ ν quad tensor H ((J+2)^4) →
      (∀ s<4, ν (quad+s)=(digit J q s : ℤ)) →
      Meets lim P pStep (d+1)
        [config,ls,nL,rs,nR,J,wL,wR,tensor,H,countOut,digit J q 0,digit J q 1,
          digit J q 2,digit J q 3,q,(J+2)^4] ν
        (LightTernaryTaggedChannel.time nL+LightTernaryTaggedChannel.time nR+
          hostTime+LightTernaryTensorScatter.time H+1500)
        (fun _ ξ => (∀ w<H, ξ (tensor+w*((J+2)^4)+q)=T w q) ∧
          ∀ x<wL, (∀ w<H, x≠tensor+w*((J+2)^4)+q) → ξ x=ν x))
    (hBatch : ∀ ν, (∀ w<H, ∀ z<(J+2)^4, ν (tensor+w*((J+2)^4)+z)=T w z) →
      Meets lim P pBatch (d+1) [tensor,J+2,H,cols,potPowers] ν
        (LightTernaryPairedPotentialBatch.time K (J+2) H)
        (fun r ξ => r=LightTernaryPairedPotentialBatch.total K tensor (J+2) ξ H ∧
          Kept ν ξ quad)) :
    Meets lim P pMain d [config,ls,nL,rs,nR,J,wL,wR,tensor,H,countOut,quad,powers,cols,potPowers] μ
      (time K J nL nR H hostTime)
      (fun r ν => r=LightTernaryPairedPotentialBatch.total K tensor (J+2) ν H ∧
        (∀ w<H, ∀ z<(J+2)^4, ν (tensor+w*((J+2)^4)+z)=T w z) ∧
        InputKept μ ν quad tensor H ((J+2)^4)) := by
  let vals : List ℤ := [config,ls,nL,rs,nR,J,wL,wR,tensor,H,countOut,quad,powers,cols,potPowers]
  let W := (J+2)^4
  let rowT := LightWeightRow.time 4 W
  let stepT := LightTernaryTaggedChannel.time nL+LightTernaryTaggedChannel.time nR+
    hostTime+LightTernaryTensorScatter.time H+1500
  have hΛ : 1≤J+2 := by omega
  have hW : 0<W := pow_pos (by omega) 4
  have haddr (w z : ℕ) (hw : w<H) (hz : z<W) : tensor+w*W+z<quad := by
    have hh := Nat.mul_le_mul_right W (by omega : w+1≤H)
    dsimp [W] at *
    nlinarith
  apply Meets.of_body hmain
  unfold body time
  light_set (J+2 : ℕ)
  have h5word : (((J+2)^5 : ℕ) : ℤ)≤lim.word := by
    unfold LightWeightRow.word at hRowWord
    push_cast at hRowWord ⊢
    have h4 : 0≤((J : ℤ)+2)^4 := by positivity
    have h5 : 0≤((J : ℤ)+2)^5 := by positivity
    omega
  have hp := powTable_meets (d := d+1) (μ := μ) (dst := powers) (L := 5) (b := J+2)
    hPowers hw hpowSpace (by
      intro e he
      have hh : (J+2)^e≤(J+2)^5 := Nat.pow_le_pow_right hΛ he
      exact (Int.ofNat_le.mpr hh).trans h5word)
  light_call hp using rowT,stepT,W with powRet ν₀ ⟨hpread,hpkeep⟩
  have hpread₀ (e : ℕ) (he : e≤4) : ν₀ (powers+e)=(((J+2)^e : ℕ) : ℤ) := by
    simpa [powList] using hpread e (by simp; omega)
  have hlast : ν₀ (powers+4)=(W : ℤ) := hpread₀ 4 le_rfl
  have hlastInt : ν₀ ((powers : ℤ)+4).toNat=(W : ℤ) := by
    have he : ((powers : ℤ)+4).toNat=powers+4 := by omega
    rw [he]
    exact hlast
  light_set (W : ℕ) using hlastInt
  refine Ends.pieceThen (Ends.for
    (T := W*(rowT+stepT+300)+20)
    (Q := Inv μ vals J H tensor quad powers T W)
    (Inv μ vals J H tensor quad powers T) W (rowT+stepT+290)
    ?_ ?_ ?_ ?_ (hT := by light_time [rowT,stepT,W])) ?_
    (hT := by light_time [rowT,stepT,W])
  · refine ⟨powRet,0,0,ν₀,?_,?_,hpread₀,?_⟩
    · simp [Inv,vals,update_frame_setLocal,W]
      exact (frame_append_zeros ([config,ls,nL,rs,nR,J,wL,wR,tensor,H,countOut,quad,powers,cols,potPowers,J+2,W,powRet,0] : List ℤ) 2).symm
    · intro x hx
      exact hpkeep x (by omega)
    · intro w hw z hz; omega
  · rintro q _ hq _ ⟨pr,rr,sr,ν,rfl,hinput,hpower,hseen⟩
    have hword : (LightWeightRow.word 4 (J+2) q 0 1 : ℤ)≤lim.word := by
      have hh : LightWeightRow.word 4 (J+2) q 0 1≤LightWeightRow.word 4 (J+2) W 0 1 := by
        unfold LightWeightRow.word
        omega
      exact (Int.ofNat_le.mpr hh).trans hRowWord
    have hr := LightWeightRow.meets (d := d+1) (μ := ν) (W := 4) (p := J+2) (k := q)
      (powers := powers) (start := 0) (stride := 1) (dst := quad) (n := 4)
      hRow hDigit hDivide hw (by omega) hΛ hspace hpowSpace (Or.inr hquad) hword
      (by intro s hs; omega) hpower
    have hrUniform := hr.mono_time (show LightWeightRow.time 4 q≤rowT by
      unfold rowT LightWeightRow.time LightRadixDigit.time
      omega)
    light_call hrUniform using vals,rowT,stepT,W with rowRet ν₁ ⟨hcoords,hrowkeep⟩
    have hinput₁ : InputKept μ ν₁ quad tensor H W := by
      intro x hx
      exact (hrowkeep x (Or.inl hx.1)).trans (hinput x hx)
    have hc (s : ℕ) (hs : s<4) : ν₁ (quad+s)=(digit J q s : ℤ) := by
      simpa [digit] using hcoords s hs
    have hc0 : ν₁ quad=(digit J q 0 : ℤ) := by simpa using hc 0 (by decide)
    have hc1 := hc 1 (by decide)
    have hc2 := hc 2 (by decide)
    have hc3 := hc 3 (by decide)
    have hcI (s : ℕ) (hs : s<4) : ν₁ ((quad : ℤ)+s).toNat=(digit J q s : ℤ) := by
      have he : ((quad : ℤ)+s).toNat=quad+s := by omega
      rw [he]
      exact hc s hs
    have hc1I := hcI 1 (by decide)
    have hc2I := hcI 2 (by decide)
    have hc3I := hcI 3 (by decide)
    norm_num only [Nat.cast_ofNat] at hc1I hc2I hc3I
    have hs := hStep q hq ν₁ hinput₁ hc
    light_call hs using vals,rowT,stepT,W,hc0,hc1,hc2,hc3,hc1I,hc2I,hc3I with stepRet ν₂ ⟨hnew,hrest⟩
    refine ⟨by simp [vals],pr,rowRet,stepRet,ν₂,?_,?_,?_,?_⟩
    · simp [vals,update_frame_setLocal]
    · intro x hx
      have hnot : ∀ w<H, x≠tensor+w*W+q := by
        intro w hw heq
        have hi := haddr w q hw hq
        have hh : x<tensor ∨ tensor+H*W≤x := hx.2
        rcases hh with hh | hh <;> nlinarith
      exact (hrest x (by omega) hnot).trans (hrowkeep x (Or.inl hx.1) |>.trans (hinput x hx))
    · intro e he
      have hnot : ∀ w<H, powers+e≠tensor+w*W+q := by
        intro w hw heq
        have := haddr w q hw hq
        omega
      rw [hrest _ (by omega) hnot,hrowkeep _ (Or.inr (by omega))]
      exact hpower e he
    · intro w hw z hz
      rcases Nat.lt_succ_iff_lt_or_eq.mp hz with hz | rfl
      · have hnot : ∀ w'<H, tensor+w*W+z≠tensor+w'*W+q := by
          intro w' hw' heq
          have hh := (LightTernaryTensorScatter.address_injective (by omega : z<W) hq
            (by omega : w*W+z=w'*W+q)).2
          omega
        rw [hrest _ (by have := haddr w z hw (by omega); omega) hnot,
          hrowkeep _ (Or.inl (haddr w z hw (by omega)))]
        exact hseen w hw z hz
      · exact hnew w hw
  · intro σ hcounter hinv
    exact hinv
  · rintro q _ hq _ ⟨pr,rr,sr,ν,rfl,hinput,hpower,hseen⟩
    light_side [vals,W]
  · rintro σ ⟨pr,rr,sr,ν,rfl,hinput,hpower,hseen⟩
    have hb := hBatch ν hseen
    light_call hb using vals,rowT,stepT,W with r ξ ⟨hvalue,hkept⟩
    refine ⟨hvalue,?_,?_⟩
    · intro w hw z hz
      exact (hkept _ (haddr w z hw hz)).trans (hseen w hw z hz)
    · intro x hx
      exact (hkept x hx.1).trans (hinput x hx)

end ThreeSum.LightTernaryTensorDriver
