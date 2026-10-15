import Submission.ThreeSum.LightTernaryRank
import Submission.ThreeSum.LightTernaryPass

/-! Actual rank-table construction over a compressed ternary code segment. -/

namespace ThreeSum.LightTernaryRankTable

open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType
  ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics

set_option maxHeartbeats 2000000

variable {lim : Limits} {P : Program}

def roundBody (pRank : ℕ) : Stmt :=
  .set 6 (M (v 1 +' v 5)) ;;
  .call pRank [v 0,v 6,v 3] 7 ;;
  .store (v 4 +' v 5) (v 7)

/-- Arguments: number of trits, compact code base, count, powers base, rank destination. -/
def body (pRank : ℕ) : Stmt := .for 5 (v 2) (roundBody pRank)

def time (N n : ℕ) : ℕ := n*(LightTernaryRank.time N+100)+20

def values (N : ℕ) (codes : ℕ → ℕ) (j : ℕ) : ℤ :=
  LightTernaryRank.partialRank N (codes j) N

def Inv (μ : ℕ → ℤ) (N a n powers dst : ℕ) (codes : ℕ → ℕ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ code result : ℤ, σ=⟨frame [N,a,n,powers,dst,j,code,result],
    wrote μ dst (values N codes) j⟩

theorem meets {pMain pRank pDigit pErase N a n powers dst d : ℕ}
    (hmain : P[pMain]?=some (body pRank))
    (hrank : P[pRank]?=some (LightTernaryRank.body pDigit))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (codes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ dst) (hp : powers+(2*N+1) ≤ dst)
    (hdst : dst+n ≤ lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ) ≤ lim.word)
    (hscalar : ((2*N+16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (a+j)=(codes j : ℤ))
    (hpowers : Powers μ powers (2*N))
    (hcodes : ∀ j < n, codes j < 2^(2*N))
    (hdepth : d+2*N+3 ≤ lim.depth) :
    Meets lim P pMain d [N,a,n,powers,dst] μ (time N n)
      (fun _ ν => (∀ j < n, ν (dst+j)=values N codes j) ∧
        SameOutside μ ν dst n) := by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ N a n powers dst codes) n
    (LightTernaryRank.time N+85) ?start ?round ?done ?bound
    (hT := by light_time)
  case start =>
    refine ⟨0,0,?_⟩
    simp [Inv,update_frame_setLocal,wrote_zero]
    change frame [(N : ℤ),a,n,powers,dst,0]=
      frame ([(N : ℤ),a,n,powers,dst,0] ++ [0,0])
    exact (frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨code,result,rfl⟩
    let μj := wrote μ dst (values N codes) j
    have hkeep : ∀ x < dst, μj x=μ x := fun x hx => wrote_rest (Or.inl hx)
    have hreadj : μj (a+j)=(codes j : ℤ) := by
      rw [hkeep _ (by omega),hread j hj]
    have hpj : Powers μj powers (2*N) := by
      intro k hk
      rw [hkeep _ (by omega),hpowers k hk]
    have hm := hcodes j hj
    have hpow : 2^(2*N) ≤ 2^(2*N+1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hcodeWord : (codes j : ℤ) < lim.word :=
      (Int.ofNat_lt.mpr hm).trans_le ((Int.ofNat_le.mpr hpow).trans hword)
    have hv := LightTernaryRank.partialRank_le N (codes j) N
    have hvalueWord : (LightTernaryRank.partialRank N (codes j) N : ℤ) ≤ lim.word := by
      omega
    have hc := LightTernaryRank.meets (d := d+1) hrank hdigit herase μj hw
      (by omega) hword hscalar hpj hm (by omega)
    unfold roundBody
    light_set (codes j : ℕ) using μj,hreadj,LightTernaryRank.time
    light_call hc using μj,LightTernaryRank.time
      with out ν ⟨hout,hmem⟩
    subst ν
    light_store (dst+j) (values N codes j) using hout,values,LightTernaryRank.time
    refine ⟨by simp,(codes j : ℤ),out,?_⟩
    simp [Inv,update_frame_setLocal,wrote_succ,μj]
  case done =>
    rintro _ _ ⟨code,result,rfl⟩
    exact ⟨fun j hj => wrote_done hj,fun x hx => wrote_rest hx⟩
  case bound =>
    rintro j _ hj _ ⟨code,result,rfl⟩
    light_side

/-- In particular, the constructed table contains actual word ranks. -/
theorem meets_words {pMain pRank pDigit pErase N a n powers dst d : ℕ}
    (hmain : P[pMain]?=some (body pRank))
    (hrank : P[pRank]?=some (LightTernaryRank.body pDigit))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (words : ℕ → TritWord N)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ dst) (hp : powers+(2*N+1) ≤ dst)
    (hdst : dst+n ≤ lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ) ≤ lim.word)
    (hscalar : ((2*N+16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (a+j)=(address (words j) : ℤ))
    (hpowers : Powers μ powers (2*N))
    (hdepth : d+2*N+3 ≤ lim.depth) :
    Meets lim P pMain d [N,a,n,powers,dst] μ (time N n)
      (fun _ ν => (∀ j < n, ν (dst+j)=(rank (words j) : ℤ)) ∧
        SameOutside μ ν dst n) := by
  have h := meets hmain hrank hdigit herase μ (fun j => address (words j))
    hw ha hp hdst hword hscalar hread hpowers
    (fun j _ => address_lt_pow_two (words j)) hdepth
  simpa only [values,LightTernaryRank.partialRank_address] using h

def program : Program := [body 1,LightTernaryRank.body 2,
  LightTernaryCodes.digitBody 3,LightMaskErase.body 3]

theorem time_bound (N n : ℕ) : time N n ≤ 2000*(N+1)^2*(n+1) := by
  unfold time LightTernaryRank.time LightTernaryCodes.digitTime LightMaskErase.time
  nlinarith

end ThreeSum.LightTernaryRankTable
