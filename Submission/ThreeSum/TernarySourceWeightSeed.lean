import Submission.ThreeSum.TernarySourceExecutionFactory

/-! Pure readiness before the reusable weight array has been initialized. -/
noncomputable section
namespace ThreeSum.TernarySourceExecutionFactory
open Light LightSubsetAddress LightTernarySourceHost

structure Seed {N : ℕ} (S : Setup) (lim : Limits) (d : ℕ) (μ : ℕ→ℤ)
    (weight : ℕ→ℤ) (enumeration : ℕ→TernaryJointType.TritWord N) : Prop where
  hxy : S.ys.length=S.xs.length
  hxz : S.zs.length=S.xs.length
  hw : (lim.space : ℤ)≤lim.word
  hm : 0<S.xs.length
  hbase0 : S.base0+S.xs.length≤S.dst0
  hnext0 : LightRadixKeys.space S.dst0 S.xs.length S.J≤S.base1
  hbase1 : S.base1+S.xs.length≤S.dst1
  hnext1 : LightRadixKeys.space S.dst1 S.xs.length S.J≤S.base2
  hbase2 : S.base2+S.xs.length≤S.dst2
  hinitEnd : LightRadixKeys.space S.dst2 S.xs.length S.J≤S.free
  hsrc : S.src+S.NL≤S.base0
  hweights : S.weightBase+S.NL≤S.base0
  hbank : S.a+S.bank≤S.base0
  hpowerEnd : S.powers+(S.W+1)≤S.base0
  hkeyBase : LightWantedSetup.space S.free S.M S.input (dictionary S.xs S.p0 S.J)
      S.NL (size S.xs S.J) S.U 0 0≤S.keyBase
  hkeyEnd : S.keyBase+count S.xs S.p0 S.J S.M S.NL S.input≤S.valueBase
  hvalues : S.valueBase+S.groups*S.bank≤lim.space
  hb0 : ∀ x∈S.xs, |x|≤(S.U0 : ℤ)
  hb1 : ∀ x∈S.ys, |x|≤(S.U1 : ℤ)
  hb2 : ∀ x∈S.zs, |x|≤(S.U2 : ℤ)
  hw0 : (LightRadixKeys.word S.p0 S.U0 S.J : ℤ)≤lim.word
  hw1 : (LightRadixKeys.word S.p1 S.U1 S.J : ℤ)≤lim.word
  hw2 : (LightRadixKeys.word S.p2 S.U2 S.J : ℤ)≤lim.word
  hM : 0<S.M
  hjoinWord : (LightSourceResidues.word S.M S.M S.U 0 : ℤ)≤lim.word
  hlookupWord : ((S.bank+2^(S.W+1)+16 : ℕ) : ℤ)≤lim.word
  hgroupWord : ((S.groups*S.bank+1 : ℕ) : ℤ)≤lim.word
  hgroupSpace : S.groups*S.bank+1≤lim.space
  hfactor : (S.factor : ℤ)≤lim.word
  hweighted : (S.factor : ℤ)*(count S.xs S.p0 S.J S.M S.NL S.input*S.weightU : ℕ)≤lim.word
  hhistWord : ((count S.xs S.p0 S.J S.M S.NL S.input+1 : ℕ) : ℤ)*S.weightU≤lim.word
  hinput : ∀ i<S.NL, μ (S.src+i)=S.input i
  hinputBound : ∀ i<S.NL, |S.input i|≤(S.U : ℤ)
  hweightBound : ∀ i<S.NL, |weight i|≤(S.weightU : ℤ)
  hglobal : S.U0*(S.p0+1)^S.J≤S.U
  hcodes : ∀ i<S.bank, μ (S.a+i)=(S.codes i : ℤ)
  hcodeBound : ∀ i<S.bank, S.codes i<2^S.W
  hpowers : Powers μ S.powers S.W
  hsorted : ∀ i k, i<k → k<S.bank → S.codes i<S.codes k
  hwordCode : ∀ j<size S.xs S.J, dictionary S.ys S.p1 S.J j=(S.codes (S.key j) : ℤ)
  hkey : ∀ j<size S.xs S.J, S.key j<S.bank
  hgroupCode : ∀ j<size S.xs S.J, dictionary S.zs S.p2 S.J j=(S.group j : ℤ)
  hgroup : ∀ j<size S.xs S.J, S.group j<S.groups
  hL : S.L≤S.W
  hn : S.bank<2^S.L
  hd : d+S.NL+S.L+S.J+8≤lim.depth
  hinjective : ∀ i j, i<S.bank → j<S.bank → enumeration i=enumeration j → i=j
  hfactorModel : ∀ pair∈S.records,
    (S.factor : ℤ)=TernaryConvolution.factorial (enumeration (S.key pair.2))

theorem Seed.finish {N : ℕ} {S : Setup} {lim : Limits} {d : ℕ} {μ : ℕ→ℤ}
    {weight : ℕ→ℤ} {enumeration : ℕ→TernaryJointType.TritWord N}
    (H : Seed S lim d μ weight enumeration)
    (hread : ∀ i<S.NL, μ (S.weightBase+i)=weight i) :
    Ready S lim d μ weight enumeration where
  hxy := H.hxy
  hxz := H.hxz
  hw := H.hw
  hm := H.hm
  hbase0 := H.hbase0
  hnext0 := H.hnext0
  hbase1 := H.hbase1
  hnext1 := H.hnext1
  hbase2 := H.hbase2
  hinitEnd := H.hinitEnd
  hsrc := H.hsrc
  hweights := H.hweights
  hbank := H.hbank
  hpowerEnd := H.hpowerEnd
  hkeyBase := H.hkeyBase
  hkeyEnd := H.hkeyEnd
  hvalues := H.hvalues
  hb0 := H.hb0
  hb1 := H.hb1
  hb2 := H.hb2
  hw0 := H.hw0
  hw1 := H.hw1
  hw2 := H.hw2
  hM := H.hM
  hjoinWord := H.hjoinWord
  hlookupWord := H.hlookupWord
  hgroupWord := H.hgroupWord
  hgroupSpace := H.hgroupSpace
  hfactor := H.hfactor
  hweighted := H.hweighted
  hhistWord := H.hhistWord
  hinput := H.hinput
  hinputBound := H.hinputBound
  hweightBound := H.hweightBound
  hglobal := H.hglobal
  hcodes := H.hcodes
  hcodeBound := H.hcodeBound
  hpowers := H.hpowers
  hsorted := H.hsorted
  hwordCode := H.hwordCode
  hkey := H.hkey
  hgroupCode := H.hgroupCode
  hgroup := H.hgroup
  hL := H.hL
  hn := H.hn
  hd := H.hd
  hinjective := H.hinjective
  hfactorModel := H.hfactorModel
  hweightRead := hread

theorem Seed.transport {N : ℕ} {S : Setup} {lim : Limits} {d keep : ℕ}
    {μ ν : ℕ→ℤ} {weight : ℕ→ℤ} {enumeration : ℕ→TernaryJointType.TritWord N}
    (H : Seed S lim d μ weight enumeration) (hkeep : Kept μ ν keep)
    (hsrc : S.src+S.NL≤keep) (hcodes : S.a+S.bank≤keep)
    (hpowers : S.powers+(S.W+1)≤keep) : Seed S lim d ν weight enumeration := by
  refine {H with hinput := ?_,hcodes := ?_,hpowers := ?_}
  · intro i hi
    exact (hkeep _ (by omega)).trans (H.hinput i hi)
  · intro i hi
    exact (hkeep _ (by omega)).trans (H.hcodes i hi)
  · intro i hi
    exact (hkeep _ (by omega)).trans (H.hpowers i hi)

end ThreeSum.TernarySourceExecutionFactory
