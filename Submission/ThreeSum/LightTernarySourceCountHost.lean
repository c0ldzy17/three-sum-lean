import Submission.ThreeSum.LightTernarySourceHost
import Submission.ThreeSum.LightTernaryCountFrontend
import Submission.ThreeSum.TernarySourceHostModel

/-! Actual source construction on both sides, followed by actual bank counting.
The source procedures construct their dictionaries, joins and weighted banks;
the counting procedure initializes its own bank powers and metadata. -/
noncomputable section
namespace ThreeSum.LightTernarySourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

def sources (xl yl zl xr yr zr : List ℤ) : Program :=
  ReportingHostRelocation.program (LightTernarySourceHost.program xl yl zl)
    (LightTernarySourceHost.program xr yr zr)

def libraries (xl yl zl xr yr zr : List ℤ) : Program :=
  ReportingHostRelocation.program (sources xl yl zl xr yr zr)
    LightTernaryCountFrontend.program

def callArgs (offset count : ℕ) : List Expr :=
  (List.range count).map (fun i => v (offset+i))

/-- Slots 0--22: left source; 23--45: right source; 46--105: count frontend.
Original coefficient-array pointers occupy slots 20 and 43. The wanted count
and output pointer occupy slots 104 and 105. -/
def body : Stmt :=
  .call 34 (callArgs 0 23) 106 ;;
  .call 69 (callArgs 23 23) 107 ;;
  .call 120 (callArgs 46 60) 0

def program (xl yl zl xr yr zr : List ℤ) : Program :=
  libraries xl yl zl xr yr zr++[body]

def sourceArgs (base0 dst0 base1 dst1 base2 dst2 J p0 p1 p2
    src count modulus free bankCodes bankSize oldPowers lookupDepth
    keyBase valueBase weightBase factor groups : ℕ) : List ℤ :=
  [base0,dst0,base1,dst1,base2,dst2,J,p0,p1,p2,src,count,modulus,free,
    bankCodes,bankSize,oldPowers,lookupDepth,keyBase,valueBase,weightBase,factor,groups]

def args (left right frontend : List ℤ) : List ℤ :=left++right++frontend

def time (leftTime rightTime frontendTime : ℕ) : ℕ :=
  leftTime+rightTime+frontendTime+500

@[simp] theorem sourceArgs_length (a b c e f g h i j k l m n o p q r s t u w x y : ℕ) :
    (sourceArgs a b c e f g h i j k l m n o p q r s t u w x y).length=23 := rfl

@[simp] theorem args_length (left right frontend : List ℤ)
    (hl : left.length=23) (hr : right.length=23) (hf : frontend.length=60) :
    (args left right frontend).length=106 := by simp [args,hl,hr,hf]

@[simp] theorem source_length (x y z : List ℤ) :
    (LightTernarySourceHost.program x y z).length=35 := by
  simp only [LightTernarySourceHost.program,LightTernarySourceHost.libraries,
    LightTernarySourceHost.joined,ReportingHostRelocation.program,
    LightTernaryParallelDictionaries.program,LightTernaryParallelDictionaries.libraries,
    LightFixedRadixDictionary.program,LightTernaryOriginalJoin.program,
    LightWantedSetup.program_length,LightTernaryGroupedSources.program,
    List.length_append,List.length_map,List.length_cons,List.length_nil,Nat.reduceAdd]

@[simp] theorem sources_length (xl yl zl xr yr zr : List ℤ) :
    (sources xl yl zl xr yr zr).length=70 := by
  simp only [sources,ReportingHostRelocation.program,List.length_append,List.length_map,
    source_length,Nat.reduceAdd]

@[simp] theorem libraries_length (xl yl zl xr yr zr : List ℤ) :
    (libraries xl yl zl xr yr zr).length=122 := by
  simp only [libraries,ReportingHostRelocation.program,List.length_append,List.length_map,
    sources_length,LightTernaryCountFrontend.program_length,Nat.reduceAdd]

@[simp] theorem program_length (xl yl zl xr yr zr : List ℤ) :
    (program xl yl zl xr yr zr).length=123 := by simp [program]

def Reads (loc : ℕ → ℤ) (offset : ℕ) (vals : List ℤ) : Prop :=
  ∀ i<vals.length, loc (offset+i)=vals.getD i 0

theorem callArgs_safe (lim : Limits) (σ : State) (offset count : ℕ) :
    ∀ e∈callArgs offset count, e.Safe lim σ := by
  intro e he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
  trivial

theorem callArgs_values (loc μ : ℕ → ℤ) (offset count : ℕ) (vals : List ℤ)
    (hlen : vals.length=count) (hread : Reads loc offset vals) :
    (callArgs offset count).map (·.val ⟨loc,μ⟩)=vals := by
  apply List.ext_getElem (by simp [callArgs,hlen])
  intro i hi hi'
  have hic : i<count := by simpa [callArgs] using hi
  have hr := hread i (by omega)
  simpa [callArgs,Expr.val,v,List.getD,List.getElem?_eq_getElem hi'] using hr

@[simp] theorem callArgs_cost (offset count : ℕ) :
    ((callArgs offset count).map Expr.cost).sum=count := by
  simp [callArgs,List.map_map,Function.comp_def,v,Expr.cost,List.map_const,List.sum_replicate]

theorem initial_reads (left right frontend : List ℤ)
    (hl : left.length=23) (hr : right.length=23) :
    Reads (frame (args left right frontend)) 0 left ∧
    Reads (frame (args left right frontend)) 23 right ∧
    Reads (frame (args left right frontend)) 46 frontend := by
  constructor
  · intro i hi
    simp only [Nat.zero_add,frame,args]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append,hl,hr]; omega),
      List.getD_append _ _ _ _ hi]
  constructor
  · intro i hi
    simp only [frame,args]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append,hl,hr]; omega),
      List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl,Nat.add_sub_cancel_left]
  · intro i hi
    simp only [frame,args]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append,hl,hr]; omega)]
    simp only [List.length_append,hl,hr,Nat.reduceAdd,Nat.add_sub_cancel_left]

theorem Reads.update {loc : ℕ → ℤ} {offset x : ℕ} {vals : List ℤ}
    (h : Reads loc offset vals) (hx : offset+vals.length≤x) (r : ℤ) :
    Reads (Function.update loc x r) offset vals := by
  intro i hi
  rw [Function.update_of_ne (by omega)]
  exact h i hi

def BankReads (μ : ℕ → ℤ) (base groups bank : ℕ) (values : ℕ → ℕ → ℤ) : Prop :=
  ∀ g<groups, ∀ j<bank, μ (base+g*bank+j)=values g j

/-- Composition uses execution receipts of the actual included source and
counting libraries. In particular, neither input histogram is advice: both
are established by preceding calls. The source receipts are discharged by
`LightTernarySourceHost.program_meets` and the counting receipt by
`LightTernaryCountFrontend.meets`. -/
theorem program_meets {lim : Limits} {d TL TR TC keepLeft keepRight keepFront
    fbase gbase groups bank count dst : ℕ}
    (xl yl zl xr yr zr left right frontend : List ℤ) (μ : ℕ → ℤ)
    (F G : ℕ → ℕ → ℤ) (value : ℕ → ℤ)
    (hl : left.length=23) (hr : right.length=23) (hf : frontend.length=60)
    (hkeepRight : keepLeft≤keepRight) (hkeepFront : keepLeft≤keepFront)
    (hFend : fbase+groups*bank≤keepRight)
    (hleft : Meets lim (LightTernarySourceHost.program xl yl zl) 34 (d+1) left μ TL
      (fun _ ν => Kept μ ν keepLeft ∧ BankReads ν fbase groups bank F))
    (hright : ∀ ν, Kept μ ν keepLeft →
      Meets lim (LightTernarySourceHost.program xr yr zr) 34 (d+1) right ν TR
        (fun _ ξ => Kept ν ξ keepRight ∧ BankReads ξ gbase groups bank G))
    (hfrontend : ∀ ν, Kept μ ν keepLeft →
      BankReads ν fbase groups bank F → BankReads ν gbase groups bank G →
      Meets lim LightTernaryCountFrontend.program 50 (d+1) frontend ν TC
        (fun _ ξ => Kept ν ξ keepFront ∧ ∀ j<count, ξ (dst+j)=value j))
    (hd : d<lim.depth) :
    Meets lim (program xl yl zl xr yr zr) 122 d (args left right frontend) μ
      (time TL TR TC)
      (fun _ ν => Kept μ ν keepLeft ∧ ∀ j<count, ν (dst+j)=value j) := by
  have h0 := hleft.append
    ((LightTernarySourceHost.program xr yr zr).map (ReportingHostRelocation.relocate 35)++
      LightTernaryCountFrontend.program.map (ReportingHostRelocation.relocate 70)++[body])
  have h0' : Meets lim (program xl yl zl xr yr zr) 34 (d+1) left μ TL
      (fun _ ν => Kept μ ν keepLeft ∧ BankReads ν fbase groups bank F) := by
    simpa only [program,libraries,sources,ReportingHostRelocation.program,source_length,
      List.length_append,List.length_map,Nat.reduceAdd,List.append_assoc] using h0
  obtain ⟨hlr,hrr,hfr⟩ := initial_reads left right frontend hl hr
  apply Meets.of_body (by
    change (libraries xl yl zl xr yr zr++[body])[122]?=some body
    rw [← libraries_length xl yl zl xr yr zr]
    simp)
  unfold body time
  refine Ends.callThen h0' ?_
    (ha := ⟨callArgs_safe _ _ _ _,callArgs_values _ _ _ _ _ hl hlr⟩)
    (hd := hd) (hT := by simp only [callArgs_cost]; omega)
  intro a ν ⟨hkeepL,hF⟩
  have h1 := (ReportingHostRelocation.meets (hright ν hkeepL)
    (LightTernarySourceHost.program xl yl zl)).append
      (LightTernaryCountFrontend.program.map (ReportingHostRelocation.relocate 70)++[body])
  have h1' : Meets lim (program xl yl zl xr yr zr) 69 (d+1) right ν TR
      (fun _ ξ => Kept ν ξ keepRight ∧ BankReads ξ gbase groups bank G) := by
    simpa only [program,libraries,sources,ReportingHostRelocation.program,source_length,
      List.length_append,List.length_map,Nat.reduceAdd,List.append_assoc] using h1
  refine Ends.callThen h1' ?_
    (ha := ⟨callArgs_safe _ _ _ _,callArgs_values _ _ _ _ _ hr (hrr.update (by omega) a)⟩)
    (hd := hd) (hT := by simp only [callArgs_cost]; omega)
  intro b ξ ⟨hkeepR,hG⟩
  have hprefix : Kept μ ξ keepLeft := by
    intro x hx
    exact (hkeepR x (by omega)).trans (hkeepL x hx)
  have hF' : BankReads ξ fbase groups bank F := by
    intro g hg j hj
    have hm := Nat.mul_le_mul_right bank (show g+1≤groups by omega)
    rw [Nat.add_mul,Nat.one_mul] at hm
    rw [hkeepR _ (by omega)]
    exact hF g hg j hj
  have h2 := (ReportingHostRelocation.meets (hfrontend ξ hprefix hF' hG)
    (sources xl yl zl xr yr zr)).append [body]
  have h2' : Meets lim (program xl yl zl xr yr zr) 120 (d+1) frontend ξ TC
      (fun _ ζ => Kept ξ ζ keepFront ∧ ∀ j<count, ζ (dst+j)=value j) := by
    simpa only [program,libraries,sources_length] using h2
  refine Ends.callLast h2' ?_
    (ha := ⟨callArgs_safe _ _ _ _,callArgs_values _ _ _ _ _ hf
      ((hfr.update (by omega) a).update (by omega) b)⟩)
    (hd := hd) (hT := by simp only [callArgs_cost]; omega)
  intro c ζ ⟨hkeepC,hvalue⟩
  exact ⟨fun x hx => (hkeepC x (by omega)).trans (hprefix x hx),hvalue⟩

/-- Direct conversion of the existing source-host execution theorem into the
bank reads needed above. All physical source records retain their original
positions and coefficients; the run's join order is existentially hidden. -/
theorem source_receipt {lim : Limits} {P : Program}
    {p d t N M NL NR bank groups valueBase factor keep hits : ℕ}
    (argv : List ℤ) (μ : ℕ → ℤ) (input dictionary : ℕ → ℤ)
    (enumeration : ℕ → TernaryJointType.TritWord N)
    (key group : ℕ → ℕ) (weight : ℕ → ℤ)
    (hkey : ∀ j<NR, key j<bank)
    (hinj : ∀ i j, i<bank → j<bank → enumeration i=enumeration j → i=j)
    (hfactor : ∀ pair∈TernarySourceHostModel.records M NL NR input dictionary,
      (factor : ℤ)=TernaryConvolution.factorial (enumeration (key pair.2)))
    (h : Meets lim P p d argv μ t
      (fun r ν => r=(valueBase : ℤ) ∧ Kept μ ν keep ∧
        ∃ ps : List (ℕ × ℕ), ps.length=hits ∧ ps.Nodup ∧
          (∀ i j, (i,j)∈ps ↔ i<NL ∧ j<NR ∧ (M : ℤ)∣input i-dictionary j) ∧
          ∀ r<groups*bank, ν (valueBase+r)=(factor : ℤ)*
            LightTernaryWeightedHistogram.total
              (fun i => group (ps.getD i (0,0)).2*bank+key (ps.getD i (0,0)).2)
              (fun i => weight (ps.getD i (0,0)).1) r hits)) :
    Meets lim P p d argv μ t (fun _ ν => Kept μ ν keep ∧
      BankReads ν valueBase groups bank (fun g r =>
        TernaryConvolution.factorial (enumeration r)*
        TernarySourceHostModel.physical
          (TernarySourceHostModel.records M NL NR input dictionary)
          enumeration key group weight g (enumeration r))) := by
  apply h.mono le_rfl
  rintro r ν ⟨_,hkeep,ps,hlen,hn,hmem,hread⟩
  refine ⟨hkeep,?_⟩
  have hs := TernarySourceHostModel.read_physical M NL NR bank groups valueBase factor
    input dictionary enumeration key group weight ν ps hn hmem hkey hinj
      (by simpa only [hlen] using hread)
  intro g hg r hr
  rw [hs g hg r hr]
  exact TernarySourceHostModel.factor_physical _ enumeration key group weight factor hfactor g _

/-- The resulting literal wanted-row score is the exact factorial-scaled
weighted sum over physical original-record pairs in the same map bank. -/
theorem physical_count_spec {lim : Limits} {P : Program}
    {N a b p d t count dst keep : ℕ} (argv : List ℤ) (μ : ℕ → ℤ)
    (S T : Finset (ℕ × ℕ))
    (enumeration : ℕ → TernaryJointType.TritWord N)
    (leftKey leftGroup rightKey rightGroup : ℕ → ℕ)
    (leftWeight rightWeight : ℕ → ℤ)
    (group : ℕ → ℕ) (Q : ℕ → TernaryJointType.TritWord N)
    (hleft : ∀ pair∈S, TernaryBank.rank (enumeration (leftKey pair.2))=a)
    (hright : ∀ pair∈T, TernaryBank.rank (enumeration (rightKey pair.2))=b)
    (hQ : ∀ j<count, TernaryBank.rank (Q j)=a+b)
    (h : Meets lim P p d argv μ t (fun _ ν => Kept μ ν keep ∧ ∀ j<count,
      ν (dst+j)=LightTernaryWantedRows.score
        (fun g A => TernaryConvolution.factorial A*
          TernarySourceHostModel.physical S enumeration leftKey leftGroup leftWeight g A)
        (fun g B => TernaryConvolution.factorial B*
          TernarySourceHostModel.physical T enumeration rightKey rightGroup rightWeight g B)
        group Q j)) :
    Meets lim P p d argv μ t (fun _ ν => Kept μ ν keep ∧ ∀ j<count,
      ν (dst+j)=TernaryConvolution.factorial (Q j)*
        TernaryWeightedPhysicalSources.pairWeight
          (TernarySourceHostModel.channel S leftGroup (group j))
          (TernarySourceHostModel.channel T rightGroup (group j))
          (fun pair => enumeration (leftKey pair.2))
          (fun pair => enumeration (rightKey pair.2))
          (fun pair => leftWeight pair.1) (fun pair => rightWeight pair.1) (Q j)) := by
  have hc := LightTernaryCountFrontend.weighted_count_spec argv μ
    (TernarySourceHostModel.physical S enumeration leftKey leftGroup leftWeight)
    (TernarySourceHostModel.physical T enumeration rightKey rightGroup rightWeight) group Q
    (fun _ _ => TernarySourceHostModel.physical_homogeneous S enumeration leftKey leftGroup leftWeight a hleft _)
    (fun _ _ => TernarySourceHostModel.physical_homogeneous T enumeration rightKey rightGroup rightWeight b hright _)
    hQ h
  apply hc.mono le_rfl
  intro r ν hv
  refine ⟨hv.1,?_⟩
  intro j hj
  rw [hv.2 j hj]
  unfold TernarySourceHostModel.physical
  rw [TernaryWeightedPhysicalSources.convolution_histograms]

end ThreeSum.LightTernarySourceCountHost
