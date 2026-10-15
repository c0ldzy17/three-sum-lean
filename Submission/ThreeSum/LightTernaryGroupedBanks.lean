import Submission.ThreeSum.LightTernaryGroupBankStep

/-! Every fixed-map occurrence vector has its own paid source and product
banks. This loop constructs each group once, before any wanted-row queries. -/
namespace ThreeSum.LightTernaryGroupedBanks
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}

def roundBody (pStep : ℕ) : Stmt :=
  .call pStep [v 0,v 1,v 2,v 3,v 4,v 5,
    v 7 +' v 12 *' v 2,v 8 +' v 12 *' v 2,
    v 9 +' v 12 *' ((v 0 +' k 1) *' v 2),
    v 10 +' v 12 *' ((v 0 +' k 1) *' v 2),
    v 11 +' v 12 *' ((v 0 +' k 1) *' v 2)] 13

def body (pStep : ℕ) : Stmt := .for 12 (v 6) (roundBody pStep)

def program : Program :=LightTernaryBankAssembly.program++
  [LightTernaryGroupBankStep.body 18,copyBody,body 17]

@[simp] theorem program_length : program.length=20 := rfl

def time (groups N L n : ℕ) : ℕ :=groups*(LightTernaryGroupBankStep.time N L n+200)+100

def GroupStages {N T n : ℕ} (E : Enumeration N T n) (φ : ℕ→ℕ→TritWord N→ℤ)
    (base groups : ℕ) (μ : ℕ→ℤ) : Prop :=
  ∀ g<groups, Stages E (φ g) (base+g*((N+1)*n)) N μ

def Preserved (μ μ' : ℕ→ℤ) (keyBase n fbase gbase hbase N groups : ℕ) : Prop :=
  ∀ x, (x<keyBase ∨ keyBase+4*n≤x) →
    (x<fbase ∨ fbase+groups*((N+1)*n)≤x) →
    (x<gbase ∨ gbase+groups*((N+1)*n)≤x) →
    (x<hbase ∨ hbase+groups*((N+1)*n)≤x) → μ' x=μ x

def Inv {N T n : ℕ} (E : Enumeration N T n) (F G : ℕ→TritWord N→ℤ)
    (μ : ℕ→ℤ) (a powers L keyBase groups fsource gsource fbase gbase hbase : ℕ)
    (k : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ→ℤ),
    σ=⟨frame [N,a,n,powers,L,keyBase,groups,fsource,gsource,fbase,gbase,hbase,k,r],μ'⟩ ∧
    GroupStages E (fun g s => forwardStage s (F g)) fbase k μ' ∧
    GroupStages E (fun g s => forwardStage s (G g)) gbase k μ' ∧
    GroupStages E (fun g s => stageValue s (LightTernaryBankAssembly.product (F g) (G g))) hbase k μ' ∧
    Preserved μ μ' keyBase n fbase gbase hbase N groups ∧ Powers μ' powers (2*N)

theorem meets {N T n a powers L keyBase groups fsource gsource fbase gbase hbase d V : ℕ}
    (E : Enumeration N T n) (F G : ℕ→TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hfs : fsource+groups*n≤keyBase) (hgs : gsource+groups*n≤keyBase)
    (hmeta : keyBase+4*n≤powers) (hpows : powers+(2*N+1)≤fbase)
    (hfg : fbase+groups*((N+1)*n)≤gbase) (hgh : gbase+groups*((N+1)*n)≤hbase)
    (hspace : hbase+groups*((N+1)*n)≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word) (hgroupsWord : (groups : ℤ)+1≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsourceF : ∀ g<groups, ∀ j<n, μ (fsource+g*n+j)=F g (E.word j))
    (hsourceG : ∀ g<groups, ∀ j<n, μ (gsource+g*n+j)=G g (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hF : ∀ g<groups, ∀ R, |F g R|≤(V : ℤ)) (hG : ∀ g<groups, ∀ R, |G g R|≤(V : ℤ))
    (hforwardWord : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hproductWord : (LightTernaryBankAssembly.valueBound N V : ℤ)≤lim.word)
    (hinverseWord : 4*((4^N*LightTernaryBankAssembly.valueBound N V : ℕ) : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+8≤lim.depth) :
    Meets lim program 19 d [N,a,n,powers,L,keyBase,groups,fsource,gsource,fbase,gbase,hbase] μ
      (time groups N L n)
      (fun _ μ' => GroupStages E (fun g s => forwardStage s (F g)) fbase groups μ' ∧
        GroupStages E (fun g s => forwardStage s (G g)) gbase groups μ' ∧
        GroupStages E (fun g s => stageValue s (LightTernaryBankAssembly.product (F g) (G g))) hbase groups μ' ∧
        Preserved μ μ' keyBase n fbase gbase hbase N groups ∧ Powers μ' powers (2*N)) := by
  apply Meets.of_body (show program[19]?=some (body 17) from rfl)
  unfold body time
  refine Ends.for (Inv E F G μ a powers L keyBase groups fsource gsource fbase gbase hbase) groups
    (LightTernaryGroupBankStep.time N L n+180) ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,μ,?_,?_,?_,?_,?_,hpowers⟩
    · simp only [update_frame_setLocal]
      congr 1
      simp only [setLocal]
      change frame [(N : ℤ),a,n,powers,L,keyBase,groups,fsource,gsource,fbase,gbase,hbase,0]=
        frame ([(N : ℤ),a,n,powers,L,keyBase,groups,fsource,gsource,fbase,gbase,hbase,0]++[0])
      exact (frame_append_zeros _ 1).symm
    · intro g hg; omega
    · intro g hg; omega
    · intro g hg; omega
    · intro x _ _ _ _; rfl
  case round =>
    rintro g _ hg _ ⟨r,μ',rfl,hstF,hstG,hstH,hkeep,hpow⟩
    let stride := (N+1)*n
    have hnext : g*stride+stride≤groups*stride := by
      have hm := Nat.mul_le_mul_right stride (show g+1≤groups by omega)
      simpa only [Nat.add_mul,Nat.one_mul] using hm
    have hsrcNext : g*n+n≤groups*n := by
      have hm := Nat.mul_le_mul_right n (show g+1≤groups by omega)
      simpa only [Nat.add_mul,Nat.one_mul] using hm
    have hcode' : ∀ j<n, μ' (a+j)=(address (E.word j) : ℤ) := by
      intro j hj
      exact (hkeep _ (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans (hcodes j hj)
    have hsf : ∀ j<n, μ' (fsource+g*n+j)=F g (E.word j) := by
      intro j hj
      exact (hkeep _ (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans (hsourceF g hg j hj)
    have hsg : ∀ j<n, μ' (gsource+g*n+j)=G g (E.word j) := by
      intro j hj
      exact (hkeep _ (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans (hsourceG g hg j hj)
    have hc := LightTernaryGroupBankStep.meets
      (tail := [LightTernaryGroupBankStep.body 18,copyBody,body 17])
      (pMain := 17) (pCopy := 18) (d := d+1)
      (fsource := fsource+g*n) (gsource := gsource+g*n)
      (fbase := fbase+g*stride) (gbase := gbase+g*stride) (hbase := hbase+g*stride)
      rfl rfl E (F g) (G g) μ' hw ha (by omega) (by omega) hmeta
      (by omega) (by dsimp [stride] at *; omega) (by dsimp [stride] at *; omega)
      (by dsimp [stride] at *; omega) hword hNword hcode' hsf hsg hpow hsorted
      (hF g hg) (hG g hg) hforwardWord hproductWord hinverseWord hL hn (by omega)
    have hgstride : ((g : ℤ)*((N : ℤ)+1)*(n : ℤ))≤lim.word := by
      have : g*stride≤lim.space := by dsimp [stride] at *; omega
      exact (by dsimp [stride] at this; simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,mul_assoc] using Int.ofNat_le.mpr this : (g : ℤ)*((N : ℤ)+1)*(n : ℤ)≤(lim.space : ℤ)).trans hw
    have hstrideWord : ((N : ℤ)+1)*(n : ℤ)≤lim.word := by
      have : stride≤lim.space := by dsimp [stride] at *; omega
      exact (by dsimp [stride] at this; simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,mul_assoc] using Int.ofNat_le.mpr this : ((N : ℤ)+1)*(n : ℤ)≤(lim.space : ℤ)).trans hw
    have haddr (b : ℕ) (hb : b≤hbase) : (b : ℤ)+(g : ℤ)*((N : ℤ)+1)*(n : ℤ)≤lim.word := by
      have : b+g*stride≤lim.space := by dsimp [stride] at *; omega
      exact (by dsimp [stride] at this; simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,mul_assoc] using Int.ofNat_le.mpr this : (b : ℤ)+(g : ℤ)*((N : ℤ)+1)*(n : ℤ)≤(lim.space : ℤ)).trans hw
    have hfaddr := haddr fbase (by omega)
    have hgaddr := haddr gbase (by omega)
    have hhaddr := haddr hbase le_rfl
    have hsrcMulWord : (g : ℤ)*(n : ℤ)≤lim.word := by
      exact (by exact_mod_cast (show g*n≤lim.space by omega) : (g : ℤ)*(n : ℤ)≤(lim.space : ℤ)).trans hw
    have hfsaddr : (fsource : ℤ)+(g : ℤ)*(n : ℤ)≤lim.word := by
      exact (by exact_mod_cast (show fsource+g*n≤lim.space by omega) : (fsource : ℤ)+(g : ℤ)*(n : ℤ)≤(lim.space : ℤ)).trans hw
    have hgsaddr : (gsource : ℤ)+(g : ℤ)*(n : ℤ)≤lim.word := by
      exact (by exact_mod_cast (show gsource+g*n≤lim.space by omega) : (gsource : ℤ)+(g : ℤ)*(n : ℤ)≤(lim.space : ℤ)).trans hw
    have hstrideNN : 0≤((N : ℤ)+1)*(n : ℤ) := by positivity
    have hmulNN : 0≤(g : ℤ)*((N : ℤ)+1)*(n : ℤ) := by positivity
    have hmulAssoc : (g : ℤ)*(((N : ℤ)+1)*(n : ℤ))=(g : ℤ)*((N : ℤ)+1)*(n : ℤ) := by ring
    unfold roundBody
    light_call hc using stride,LightTernaryGroupBankStep.time with out ν ⟨houtF,houtG,houtH,hstepKeep,hpow'⟩
    refine ⟨by simp,out,ν,?_,?_,?_,?_,?_,hpow'⟩
    · simp [Inv,update_frame_setLocal]
    · intro j hj
      by_cases he : j=g
      · subst j; exact houtF
      · have hjg : j<g := by omega
        intro s hs k hk
        have hm := Nat.mul_le_mul_right stride (show j+1≤g by omega)
        have hs' := Nat.mul_le_mul_right n hs
        have hlen : stride=N*n+n := by dsimp [stride]; ring
        have hpart : s*n+k<stride := by omega
        have hprior : j*stride+s*n+k<g*stride := by
          rw [Nat.add_mul,Nat.one_mul] at hm
          omega
        have hFtoG : fbase+g*stride+stride≤gbase := by dsimp [stride] at *; omega
        have hGtoH : gbase+g*stride+stride≤hbase := by dsimp [stride] at *; omega
        exact (hstepKeep _ (Or.inr (by dsimp only [stride] at *; omega)) (Or.inl (by dsimp only [stride] at *; omega)) (Or.inl (by dsimp only [stride] at *; omega)) (Or.inl (by dsimp only [stride] at *; omega))).trans (hstF j hjg s hs k hk)
    · intro j hj
      by_cases he : j=g
      · subst j; exact houtG
      · have hjg : j<g := by omega
        intro s hs k hk
        have hm := Nat.mul_le_mul_right stride (show j+1≤g by omega)
        have hs' := Nat.mul_le_mul_right n hs
        have hlen : stride=N*n+n := by dsimp [stride]; ring
        have hpart : s*n+k<stride := by omega
        have hprior : j*stride+s*n+k<g*stride := by
          rw [Nat.add_mul,Nat.one_mul] at hm
          omega
        have hFtoG : fbase+g*stride+stride≤gbase := by dsimp [stride] at *; omega
        have hGtoH : gbase+g*stride+stride≤hbase := by dsimp [stride] at *; omega
        exact (hstepKeep _ (Or.inr (by dsimp only [stride] at *; omega)) (Or.inr (by dsimp only [stride] at *; omega)) (Or.inl (by dsimp only [stride] at *; omega)) (Or.inl (by dsimp only [stride] at *; omega))).trans (hstG j hjg s hs k hk)
    · intro j hj
      by_cases he : j=g
      · subst j; exact houtH
      · have hjg : j<g := by omega
        intro s hs k hk
        have hm := Nat.mul_le_mul_right stride (show j+1≤g by omega)
        have hs' := Nat.mul_le_mul_right n hs
        have hlen : stride=N*n+n := by dsimp [stride]; ring
        have hpart : s*n+k<stride := by omega
        have hprior : j*stride+s*n+k<g*stride := by
          rw [Nat.add_mul,Nat.one_mul] at hm
          omega
        have hFtoG : fbase+g*stride+stride≤gbase := by dsimp [stride] at *; omega
        have hGtoH : gbase+g*stride+stride≤hbase := by dsimp [stride] at *; omega
        exact (hstepKeep _ (Or.inr (by dsimp only [stride] at *; omega)) (Or.inr (by dsimp only [stride] at *; omega)) (Or.inr (by dsimp only [stride] at *; omega)) (Or.inl (by dsimp only [stride] at *; omega))).trans (hstH j hjg s hs k hk)
    · intro x hm hf hg' hh
      have hfgap : x<fbase+g*stride ∨ fbase+g*stride+stride≤x := by dsimp [stride] at *; omega
      have hggap : x<gbase+g*stride ∨ gbase+g*stride+stride≤x := by dsimp [stride] at *; omega
      have hhgap : x<hbase+g*stride ∨ hbase+g*stride+stride≤x := by dsimp [stride] at *; omega
      exact (hstepKeep x hm hfgap hggap hhgap).trans (hkeep x hm hf hg' hh)
  case done =>
    rintro _ _ ⟨r,μ',rfl,hF',hG',hH',hkeep,hpow⟩
    exact ⟨hF',hG',hH',hkeep,hpow⟩
  case bound =>
    rintro g _ hg _ ⟨r,μ',rfl,hF',hG',hH',hkeep,hpow⟩
    light_side

end ThreeSum.LightTernaryGroupedBanks
