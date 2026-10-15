import Submission.ThreeSum.LightTernaryFastProgram
import Submission.ThreeSum.TernaryGlobalPreludeTime

noncomputable section
namespace ThreeSum.LightTernaryFastProgramProof
open Light LightTernaryFastProgram LightTernaryGlobalPrelude
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

def scanFree (M b p K κ n free : ℕ) : ℕ :=
  finish free (LightTernaryDimensions.dim M b p K n (n^κ)) p
    (p^(LightTernaryDimensions.dim M b p K n (n^κ))) (LightTernaryDimensions.J M b n (n^κ))

/-- Facts furnished by execution of the genuine once-per-input prelude. -/
def Receipt (M b p K κ n free c : ℕ) [Fact p.Prime] (μ ν : ℕ→ℤ) : Prop :=
  Irreducible (TernaryExtensionEncoding.monicOfCode (p:=p)
    (LightTernaryDimensions.dim M b p K n (n^κ)) c) ∧
  Seg ν free (header n (n^κ) (LightTernaryDimensions.r M n)
    (LightTernaryDimensions.J M b n (n^κ)) (LightTernaryDimensions.dim M b p K n (n^κ)) p
    (p^(LightTernaryDimensions.dim M b p K n (n^κ))) free c) ∧
  Seg ν (params free) (LightScales.values n) ∧
  LightTernaryGlobalPreludeProof.Menu ν (backend free) (LightTernaryDimensions.dim M b p K n (n^κ)) p
    (p^(LightTernaryDimensions.dim M b p K n (n^κ))) (LightTernaryDimensions.J M b n (n^κ)) c ∧
  Kept μ ν free

theorem lift_global {lim : Limits} {M b p K κ entry depth T : ℕ}
    {vals : List ℤ} {μ : ℕ→ℤ} {Post : ℤ→(ℕ→ℤ)→Prop}
    (color : Program) (colorMain : ℕ)
    (h : Meets lim (LightTernaryGlobalPrelude.program M b p K κ) entry depth vals μ T Post) :
    Meets lim (program M b p K κ color colorMain) entry depth vals μ T Post := by
  have hh := h.append (color.map (ReportingHostRelocation.relocate 50)++
    LightColorParameters.program.map (ReportingHostRelocation.relocate (50+color.length))++
    [LightColorScan.body (scanEntry color) (50+color.length) (50+colorMain),
      LightColorScanHost.body (scanEntry color),LightTernaryFastProgram.body (hostEntry color)])
  simpa only [LightTernaryFastProgram.program,parameterLibrary,colorsLibrary,ReportingHostRelocation.program,
    LightTernaryGlobalPrelude.program_length,colorsLibrary_length,List.length_append,List.length_map,List.append_assoc] using hh

def time (M b p K κ colorTime n : ℕ) : ℕ :=
  TernaryGlobalPreludeTime.uniformTime M b p K κ n+LightColorScanHost.time colorTime n+1000

/-- Operational composition of the actual global prelude, complete coloring
scan and main entry. The color premise is the child program's contract; the
final unconditional solver must instantiate it with the concrete color proof. -/
theorem meets_of_colors {lim : Limits} {M b p K κ n src free depth colorMain colorTime colorDepth : ℕ}
    [Fact p.Prime] (color : Program) (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hM : 1<M) (hb : 1<b) (hn : 0<n) (hsrc : src≤free)
    (H : (TernaryGlobalPreludeResources.need M b p K κ n (n^κ)).Ok lim free (depth+1))
    (hspace : scanFree M b p K κ n free+6≤lim.space)
    (hword : (LightColorScanHost.word n : ℤ)≤lim.word)
    (hd : depth+ColorParameters.count (LightColorParametersCosts.width n)+colorDepth+5≤lim.depth)
    (hcolor : ∀c<p^(LightTernaryDimensions.dim M b p K n (n^κ)), ∀ν₀,
      Receipt M b p K κ n free c μ ν₀→
      ∀ (i : ℕ) (hi : i < ColorParameters.count (LightColorParametersCosts.width n)) (ν : ℕ→ℤ),
      Kept ν₀ ν (scanFree M b p K κ n free)→
      Seg ν (scanFree M b p K κ n free) (ColorParameters.fields (ColorParameters.parameter hi))→
      ∀dd, dd+colorDepth≤lim.depth→
      Meets lim (program M b p K κ color colorMain) (50+colorMain) dd
        [src,n,params free,scanFree M b p K κ n free,scanFree M b p K κ n free+6] ν colorTime
        (fun z ξ=>(z=0∨z=1) ∧ (z=1↔ColorClassLists.witness (ColorParameters.parameter hi) x) ∧
          Kept ν ξ (scanFree M b p K κ n free))) :
    Meets lim (program M b p K κ color colorMain) (mainEntry color) depth [src,n,free] μ
      (time M b p K κ colorTime n)
      (fun z ν=>(z=0∨z=1) ∧ (z=1↔Coloring.DistinctZeroSum x) ∧ Kept μ ν free) := by
  have hw := H.space
  have hfree : free+33≤scanFree M b p K κ n free := by
    unfold scanFree finish backend
    omega
  have hparams : params free<scanFree M b p K κ n free := by unfold params; omega
  have hsrc' : src≤scanFree M b p K κ n free := by omega
  have hglobal := lift_global color colorMain
    (TernaryGlobalPreludeTime.need_meets_uniform μ hM hb hn H)
  apply Meets.of_body (main_lookup M b p K κ color colorMain)
  unfold LightTernaryFastProgram.body time
  light_call hglobal with result ν₀ ⟨c,hc,hresult,hirred,hheader,hscales,hmenu,hkeep⟩
  have receipt : Receipt M b p K κ n free c μ ν₀ := ⟨hirred,hheader,hscales,hmenu,hkeep⟩
  have h6 : ν₀ (free+6)=(params free : ℤ) := by
    simpa only [header,List.getElem_cons_succ,List.getElem_cons_zero] using hheader 6 (by simp [header])
  have h8 : ν₀ (free+8)=(scanFree M b p K κ n free : ℤ) := by
    simpa only [header,List.getElem_cons_succ,List.getElem_cons_zero,scanFree] using hheader 8 (by simp [header])
  have ha6 : ((free:ℤ)+6).toNat=free+6 := by omega
  have ha8 : ((free:ℤ)+8).toNat=free+8 := by omega
  have hpword : (params free : ℤ)≤lim.word := (Int.ofNat_le.mpr (hparams.le.trans (by omega))).trans hw
  have hfword : (scanFree M b p K κ n free : ℤ)≤lim.word := (Int.ofNat_le.mpr (by omega)).trans hw
  light_set (params free : ℕ) using hresult,h6,ha6
  light_set (scanFree M b p K κ n free : ℕ) using hresult,h8,ha8
  have hbits : ν₀ (params free)=(Scales.inputBits n : ℤ) := by
    simpa [LightScales.values] using hscales 0 (by simp [LightScales.values])
  have hhost := (host_procs M b p K κ color colorMain).meets (d:=depth+1) x ν₀ hw hspace hsrc'
    hparams hword (by omega) hbits (hcolor c hc ν₀ receipt)
  light_call hhost with z ξ ⟨hbool,hresult,hkeep'⟩
  refine ⟨hbool,hresult,?_⟩
  intro i hi
  exact (hkeep' i (by omega)).trans (hkeep i hi)

end ThreeSum.LightTernaryFastProgramProof
