import Submission.ThreeSum.LightTernaryPrefixLoop

namespace ThreeSum.LightTernaryPrefixHeader
open Light
open LightTernaryPrefixLoop
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000

def patch (base : ℕ) (loc : ℕ→ ℤ) : (ℕ→ ℤ)→ List (ℕ×ℕ)→ (ℕ→ ℤ)
  | μ,[]=>μ
  | μ,(i,r)::xs=>patch base loc (Function.update μ (base+i) (loc r)) xs

theorem stores_ends {lim : Limits} {P : Program} {d base : ℕ}
    (fs : List (ℕ×ℕ)) (loc μ : ℕ→ ℤ)
    (hbase : loc 1=(base:ℤ)) (hw : (lim.space:ℤ)≤lim.word)
    (hspace : base+106≤lim.space)
    (hgood : ∀ ir∈fs, ir.1<106 ∧ |loc ir.2|≤lim.word) :
    Ends lim P d (stores fs) ⟨loc,μ⟩ (10*fs.length)
      (fun σ=>σ.loc=loc ∧ σ.mem=patch base loc μ fs) := by
  induction fs generalizing μ with
  | nil => exact Ends.skip ⟨rfl,rfl⟩
  | cons ir fs ih =>
    obtain ⟨hi,hr⟩:=hgood ir (by simp)
    have ha : base+ir.1<lim.space :=by omega
    have haZ : (base:ℤ)+(ir.1:ℤ)≤lim.word :=by exact_mod_cast (Int.ofNat_le.mpr ha.le).trans hw
    have ha0 : (0:ℤ)≤(base:ℤ)+(ir.1:ℤ) :=by positivity
    have haa : lim.Addr ((base:ℤ)+(ir.1:ℤ)) :=by constructor; positivity; exact_mod_cast ha
    simp only [stores,List.length_cons]
    refine Ends.seq 10 (10*fs.length) ?_ (by omega)
    refine Ends.storeLast ?_ (hs:=by light_side [hbase]) (hT:=by light_time)
    have hn : ((base:ℤ)+(ir.1:ℤ)).toNat=base+ir.1 :=by omega
    simpa only [v,k,Expr.val,Op.eval,hbase,hn,patch] using
      ih (Function.update μ (base+ir.1) (loc ir.2)) (fun ir hir=>hgood ir (by simp [hir]))

theorem patch_outside (base : ℕ) (loc μ : ℕ→ ℤ) (fs : List (ℕ×ℕ))
    (hgood : ∀ ir∈fs, ir.1<106) : SameOutside μ (patch base loc μ fs) base 106 :=by
  induction fs generalizing μ with
  | nil=>exact SameOutside.refl
  | cons ir fs ih=>
    intro x hx
    have hh:=ih (Function.update μ (base+ir.1) (loc ir.2)) (fun ir hir=>hgood ir (by simp [hir])) x hx
    have hn : x≠base+ir.1 :=by have hf:=hgood ir (by simp); omega
    exact hh.trans (Function.update_of_ne hn _ _)

theorem patch_read_same (base : ℕ) (loc μ : ℕ→ ℤ) (fs : List (ℕ×ℕ)) (i : ℕ)
    (hn : ∀ ir∈fs, ir.1≠i) : patch base loc μ fs (base+i)=μ (base+i) :=by
  induction fs generalizing μ with
  | nil=>rfl
  | cons ir fs ih=>
    rw [patch,ih _ (fun ir hir=>hn ir (by simp [hir]))]
    exact Function.update_of_ne (by have hh:=hn ir (by simp); omega) _ _

theorem patch_read_written (base : ℕ) (loc μ : ℕ→ ℤ) (fs : List (ℕ×ℕ))
    (hn : (fs.map Prod.fst).Nodup) (ir : ℕ×ℕ) (hir : ir∈fs) :
    patch base loc μ fs (base+ir.1)=loc ir.2 :=by
  induction fs generalizing μ with
  | nil=>simp at hir
  | cons f fs ih=>
    have hh : f.1∉fs.map Prod.fst ∧ (fs.map Prod.fst).Nodup :=by simpa using hn
    rcases List.mem_cons.mp hir with he|hir
    · subst ir
      rw [patch,patch_read_same]
      · simp
      · intro g hg he
        exact hh.1 (List.mem_map.mpr ⟨g,hg,he⟩)
    · exact ih (Function.update μ (base+f.1) (loc f.2)) hh.2 hir

theorem headerWrites_good : ∀ir∈headerWrites, ir.1<106 ∧ ir.2<30 := by decide
theorem headerWrites_nodup : (headerWrites.map Prod.fst).Nodup :=by decide


def args (template live hdr s m p power alpha2 alphaRank localQ radix J : ℕ) : List ℤ :=
  [template,live,hdr,s,m,p,power,alpha2,alphaRank,localQ,radix,J]

def locals (N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase : ℕ) : List ℤ :=
  [N,T,L,groups,nb,bank,powers,power*p,alpha2*s,2^(alpha2*s),alphaRank*s,
    (N+1)*nb,N*nb,2*(alphaRank*s),((2*(alphaRank*s)-T-1:ℕ):ℤ),
    LightTernaryRepeatWord.value localQ radix s,Fbase+N*nb,Gbase+N*nb]

def time (s alpha2 : ℕ) : ℕ := LightNatPower.time (alpha2*s)+LightTernaryRepeatWord.time s+5000

/-- Header values are read from the executed prefix setup. All remaining
premises are address separation and bounds on arithmetic actually executed. -/
theorem meets {lim : Limits} {P : Program}
    {main template live hdr s m p power alpha2 alphaRank localQ radix J
      N T L groups nb bank powers Fbase Gbase d : ℕ}
    (hmain : P[main]?=some headerBody)
    (hcopy : P[177]?=some copyBody) (hpow : P[168]?=some LightNatPower.body)
    (hrepeat : P[178]?=some LightTernaryRepeatWord.body)
    (μ : ℕ→ ℤ) (hw : (lim.space:ℤ)≤lim.word)
    (htemplate : template+106≤live) (hlive : live+106≤hdr)
    (hhdr : hdr+8≤lim.space) (hd : d<lim.depth)
    (hread : Seg μ hdr [N,T,L,groups,nb,bank,powers,s])
    (hF : μ (template+99)=(Fbase:ℤ)) (hG : μ (template+100)=(Gbase:ℤ))
    (hD : T+1≤2*(alphaRank*s)) (hN1 : (N:ℤ)+1≤lim.word)
    (hfits : ∀x∈(args template live hdr s m p power alpha2 alphaRank localQ radix J++
      locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase),
      |x|≤lim.word)
    (hpower : ∀i≤alpha2*s, ((2^i:ℕ):ℤ)≤lim.word)
    (hquery : ∀i≤s, (LightTernaryRepeatWord.value localQ radix i:ℤ)≤lim.word) :
    Meets lim P main d (args template live hdr s m p power alpha2 alphaRank localQ radix J)
      μ (time s alpha2)
      (fun r ν=>r=((power*p:ℕ):ℤ) ∧ ∃ μ₀ ret,
        (∀i<106, μ₀ (live+i)=μ (template+i)) ∧ SameOutside μ μ₀ live 106 ∧
        ν=Function.update (patch live
          (frame (args template live hdr s m p power alpha2 alphaRank localQ radix J++
            locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase++[ret]))
          μ₀ headerWrites) (live+104) 0) :=by
  have hbound (x : ℤ) (hx : x∈args template live hdr s m p power alpha2 alphaRank localQ radix J++
      locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase) :
      |x|≤lim.word :=hfits x hx
  have hwN : ((N:ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((N:ℕ):ℤ) (by simp [args,locals]))
  have hwT : ((T:ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((T:ℕ):ℤ) (by simp [args,locals]))
  have hwL : ((L:ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((L:ℕ):ℤ) (by simp [args,locals]))
  have hwgroups : ((groups:ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((groups:ℕ):ℤ) (by simp [args,locals]))
  have hwnb : ((nb:ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((nb:ℕ):ℤ) (by simp [args,locals]))
  have hwbank : ((bank:ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((bank:ℕ):ℤ) (by simp [args,locals]))
  have hwpowers : ((powers:ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((powers:ℕ):ℤ) (by simp [args,locals]))
  have hwprod : ((power*p:ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((power*p:ℕ):ℤ) (by simp [args,locals]))
  have hwexp : ((alpha2*s:ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((alpha2*s:ℕ):ℤ) (by simp [args,locals]))
  have hwfactor : ((2^(alpha2*s):ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((2^(alpha2*s):ℕ):ℤ) (by simp [args,locals]))
  have hwrank : ((alphaRank*s:ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((alphaRank*s:ℕ):ℤ) (by simp [args,locals]))
  have hwstride : (((N+1)*nb:ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound (((N+1)*nb:ℕ):ℤ) (by simp [args,locals]))
  have hwtail : ((N*nb:ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((N*nb:ℕ):ℤ) (by simp [args,locals]))
  have hwqrank : ((2*(alphaRank*s):ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((2*(alphaRank*s):ℕ):ℤ) (by simp [args,locals]))
  have hwD : ((2*(alphaRank*s)-T-1:ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((2*(alphaRank*s)-T-1:ℕ):ℤ) (by simp [args,locals]))
  have hwQ : ((LightTernaryRepeatWord.value localQ radix s:ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((LightTernaryRepeatWord.value localQ radix s:ℕ):ℤ) (by simp [args,locals]))
  have hwFbv : ((Fbase+N*nb:ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((Fbase+N*nb:ℕ):ℤ) (by simp [args,locals]))
  have hwGbv : ((Gbase+N*nb:ℕ):ℤ)≤lim.word := (le_abs_self _).trans (hbound ((Gbase+N*nb:ℕ):ℤ) (by simp [args,locals]))
  have hS : (s:ℤ)≤lim.word :=(le_abs_self _).trans (hbound s (by simp [args]))
  have hQlocal : (localQ:ℤ)≤lim.word :=(le_abs_self _).trans (hbound localQ (by simp [args]))
  have hRadix : (radix:ℤ)≤lim.word :=(le_abs_self _).trans (hbound radix (by simp [args]))
  have h2 : (2:ℤ)≤lim.word :=by
    have hh : 2≤(hdr+8:ℕ) :=by omega
    exact (Int.ofNat_le.mpr (hh.trans hhdr)).trans hw
  have hProd0 : (0:ℤ)≤(power:ℤ)*(p:ℤ) :=by positivity
  have hExp0 : (0:ℤ)≤(alpha2:ℤ)*(s:ℤ) :=by positivity
  have hRank0 : (0:ℤ)≤(alphaRank:ℤ)*(s:ℤ) :=by positivity
  have hStride0 : (0:ℤ)≤((N:ℤ)+1)*(nb:ℤ) :=by positivity
  have hTail0 : (0:ℤ)≤(N:ℤ)*(nb:ℤ) :=by positivity
  have hQrank0 : (0:ℤ)≤2*((alphaRank:ℤ)*(s:ℤ)) :=by positivity
  have hDsub : (2*(alphaRank*s)-T-1:ℕ) = 2*(alphaRank*s)-T-1 :=rfl
  have hDcast : ((2*(alphaRank*s)-T-1:ℕ):ℤ)=2*((alphaRank:ℤ)*(s:ℤ))-(T:ℤ)-1 :=by omega
  have hD0 : (0:ℤ)≤2*((alphaRank:ℤ)*(s:ℤ))-(T:ℤ)-1 :=by omega
  have hDfirst : 2*((alphaRank:ℤ)*(s:ℤ))-(T:ℤ)≤lim.word :=by
    have hz : (0:ℤ)≤(T:ℤ) :=by positivity
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hwqrank
    omega
  push_cast at hwprod hwexp hwrank hwstride hwtail hwqrank hwFbv hwGbv
  have hc:=copy_meets (μ:=μ) (d:=d+1) (src:=template) (dst:=live) (n:=106) hcopy hw
    (by omega) (by omega) (Or.inl htemplate)
  apply Meets.of_body hmain
  unfold headerBody time
  light_call hc using args,LightNatPower.time,LightTernaryRepeatWord.time with ret μ₀ ⟨hcopied,hkept⟩
  have hr (i : ℕ) (hi : i<8) : μ₀ (hdr+i)=μ (hdr+i) :=hkept _ (Or.inr (by omega))
  have ha (i : ℕ) : ((hdr:ℤ)+(i:ℤ)).toNat=hdr+i :=by omega
  have hrN : μ₀ (hdr+0)=(N:ℤ) := by rw [hr 0 (by decide)]; simpa using hread 0 (by simp)
  have ha0 : ((hdr:ℤ)+0).toNat=hdr+0 :=by omega
  simp only [Nat.add_zero] at hrN
  have hrT : μ₀ (hdr+1)=(T:ℤ) := by rw [hr 1 (by decide)]; simpa using hread 1 (by simp)
  have ha1 : ((hdr:ℤ)+1).toNat=hdr+1 :=by omega
  have hrL : μ₀ (hdr+2)=(L:ℤ) := by rw [hr 2 (by decide)]; simpa using hread 2 (by simp)
  have ha2 : ((hdr:ℤ)+2).toNat=hdr+2 :=by omega
  have hrgroups : μ₀ (hdr+3)=(groups:ℤ) := by rw [hr 3 (by decide)]; simpa using hread 3 (by simp)
  have ha3 : ((hdr:ℤ)+3).toNat=hdr+3 :=by omega
  have hrnb : μ₀ (hdr+4)=(nb:ℤ) := by rw [hr 4 (by decide)]; simpa using hread 4 (by simp)
  have ha4 : ((hdr:ℤ)+4).toNat=hdr+4 :=by omega
  have hrbank : μ₀ (hdr+5)=(bank:ℤ) := by rw [hr 5 (by decide)]; simpa using hread 5 (by simp)
  have ha5 : ((hdr:ℤ)+5).toNat=hdr+5 :=by omega
  have hrpowers : μ₀ (hdr+6)=(powers:ℤ) := by rw [hr 6 (by decide)]; simpa using hread 6 (by simp)
  have ha6 : ((hdr:ℤ)+6).toNat=hdr+6 :=by omega
  light_set (N:ℕ) using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,hrN,ha0,LightNatPower.time,LightTernaryRepeatWord.time
  light_set (T:ℕ) using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,hrT,ha1,LightNatPower.time,LightTernaryRepeatWord.time
  light_set (L:ℕ) using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,hrL,ha2,LightNatPower.time,LightTernaryRepeatWord.time
  light_set (groups:ℕ) using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,hrgroups,ha3,LightNatPower.time,LightTernaryRepeatWord.time
  light_set (nb:ℕ) using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,hrnb,ha4,LightNatPower.time,LightTernaryRepeatWord.time
  light_set (bank:ℕ) using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,hrbank,ha5,LightNatPower.time,LightTernaryRepeatWord.time
  light_set (powers:ℕ) using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,hrpowers,ha6,LightNatPower.time,LightTernaryRepeatWord.time
  light_set (power*p:ℕ) using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,LightNatPower.time,LightTernaryRepeatWord.time
  light_set (alpha2*s:ℕ) using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,LightNatPower.time,LightTernaryRepeatWord.time
  light_call (LightNatPower.meets (d:=d+1) hpow μ₀ hwexp hpower)
    using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,LightNatPower.time,LightTernaryRepeatWord.time with factor μ₁ ⟨hfactor,hμ₁⟩
  subst μ₁
  light_set (alphaRank*s:ℕ) using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,LightNatPower.time,LightTernaryRepeatWord.time
  light_set ((N+1)*nb:ℕ) using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,LightNatPower.time,LightTernaryRepeatWord.time
  light_set (N*nb:ℕ) using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,LightNatPower.time,LightTernaryRepeatWord.time
  light_set (2*(alphaRank*s):ℕ) using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,LightNatPower.time,LightTernaryRepeatWord.time
  light_set (2*(alphaRank*s)-T-1:ℕ) using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,hDcast,LightNatPower.time,LightTernaryRepeatWord.time
  light_call (LightTernaryRepeatWord.meets (d:=d+1) hrepeat μ₀ hQlocal hRadix hS hquery)
    using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,LightNatPower.time,LightTernaryRepeatWord.time with query μ₂ ⟨hqueryResult,hμ₂⟩
  subst μ₂
  have hrf : μ₀ (template+99)=(Fbase:ℤ) :=(hkept _ (Or.inl (by omega))).trans hF
  have hrg : μ₀ (template+100)=(Gbase:ℤ) :=(hkept _ (Or.inl (by omega))).trans hG
  have hat99 : ((template:ℤ)+99).toNat=template+99 :=by omega
  have hat100 : ((template:ℤ)+100).toNat=template+100 :=by omega
  have hF0 : (0:ℤ)≤(Fbase:ℤ)+(N:ℤ)*(nb:ℤ) :=by positivity
  have hG0 : (0:ℤ)≤(Gbase:ℤ)+(N:ℤ)*(nb:ℤ) :=by positivity
  light_set (Fbase+N*nb:ℕ) using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,hrf,hat99,LightNatPower.time,LightTernaryRepeatWord.time
  light_set (Gbase+N*nb:ℕ) using args,hrN,hrT,hrL,hrgroups,hrnb,hrbank,hrpowers,ha0,ha1,ha2,ha3,ha4,ha5,ha6,hrg,hat100,LightNatPower.time,LightTernaryRepeatWord.time
  let loc:=frame (args template live hdr s m p power alpha2 alphaRank localQ radix J++
    locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase++[ret])
  have hlocBase : loc 1=(live:ℤ) :=by simp [loc,args,locals]
  have hlocFit : ∀ir∈headerWrites, ir.1<106 ∧ |loc ir.2|≤lim.word :=by
    intro ir hir
    obtain ⟨hi,hr⟩:=headerWrites_good ir hir
    refine ⟨hi,?_⟩
    apply hfits
    have hlen : ir.2<(args template live hdr s m p power alpha2 alphaRank localQ radix J++
      locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase).length :=by simpa [args,locals] using hr
    change (args template live hdr s m p power alpha2 alphaRank localQ radix J++
      locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase++[ret]).getD ir.2 0∈_
    rw [List.getD_append _ _ _ _ hlen,List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  subst factor
  subst query
  simp only [args,locals,setLocal] at ⊢
  change Ends _ _ _ _ ⟨loc,μ₀⟩ _ _
  refine Ends.pieceThen (stores_ends headerWrites loc μ₀ hlocBase hw (by omega) hlocFit) ?_
    (hT:=by norm_num [headerWrites]; light_time)
  rintro ⟨loc₁,ν⟩ ⟨hloc₁,hν⟩
  dsimp only at hloc₁
  subst loc₁
  dsimp only at hν
  subst ν
  light_store (live+104) (0:ℕ) using loc,args,locals,headerWrites,LightNatPower.time,LightTernaryRepeatWord.time
  light_set (power*p:ℕ) using loc,args,locals,headerWrites,LightNatPower.time,LightTernaryRepeatWord.time
  exact ⟨rfl,μ₀,ret,hcopied,hkept,rfl⟩

end ThreeSum.LightTernaryPrefixHeader
