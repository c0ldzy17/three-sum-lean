import Submission.ThreeSum.LightTernaryFastProgramProof
import Submission.ThreeSum.ThreeSumColorDriverResources

noncomputable section
namespace ThreeSum.TernaryFastProgramResources
open Light LightTernaryFastProgram LightTernaryFastProgramProof
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

/-- The backend persists before the coloring record. Per-color storage is
reused, and the word bound includes both actually executed stages. -/
def need (M b p K κ : ℕ) (colorNeed : ℕ→ℕ→Need) (n U : ℕ) : Need :=
  let g := TernaryGlobalPreludeResources.need M b p K κ n U
  let c := ThreeSumColorDriverResources.need colorNeed n U
  ⟨g.word+c.word,g.cells+c.cells,g.depth+c.depth+2⟩

theorem scanFree_eq (M b p K κ n U free : ℕ) :
    scanFree M b p K κ n free=free+(TernaryGlobalPreludeResources.need M b p K κ n U).cells := by
  simp only [scanFree,LightTernaryGlobalPrelude.finish,LightTernaryGlobalPrelude.backend,
    TernaryGlobalPreludeResources.need,Nat.add_assoc]

theorem global_ok {M b p K κ n U free depth : ℕ} {colorNeed : ℕ→ℕ→Need} {lim : Limits}
    (H : (need M b p K κ colorNeed n U).Ok lim free depth) :
    (TernaryGlobalPreludeResources.need M b p K κ n U).Ok lim free (depth+1) :=
  H.mono (by dsimp only [need]; omega) (by dsimp only [need]; omega)
    (by dsimp only [need]; omega)

theorem scan_ok {M b p K κ n U free depth : ℕ} {colorNeed : ℕ→ℕ→Need} {lim : Limits}
    (H : (need M b p K κ colorNeed n U).Ok lim free depth) :
    (ThreeSumColorDriverResources.need colorNeed n U).Ok lim
      (scanFree M b p K κ n free) (depth+1) :=
  H.mono (by dsimp only [need]; omega)
    (by rw [scanFree_eq M b p K κ n U free]; dsimp only [need]; omega)
    (by dsimp only [need]; omega)

theorem color_ok {M b p K κ n U free depth dd : ℕ} {colorNeed : ℕ→ℕ→Need} {lim : Limits}
    (H : (need M b p K κ colorNeed n U).Ok lim free depth)
    (hd : dd+(colorNeed n U).depth≤lim.depth) :
    (colorNeed n U).Ok lim (scanFree M b p K κ n free+6) dd :=
  ThreeSumColorDriverResources.color_of_ok (scan_ok H) hd

theorem scan_bounds {M b p K κ n U free depth : ℕ} {colorNeed : ℕ→ℕ→Need} {lim : Limits}
    (H : (need M b p K κ colorNeed n U).Ok lim free depth) :
    scanFree M b p K κ n free+6≤lim.space ∧
    (LightColorScanHost.word n : ℤ)≤lim.word ∧
    depth+ColorParameters.count (LightColorParametersCosts.width n)+(colorNeed n U).depth+5≤lim.depth := by
  have h := ThreeSumColorDriverResources.scan_bounds_of_ok (scan_ok H)
  exact ⟨h.1,h.2.1,by omega⟩

theorem polyNeed {M b p K : ℕ} [Fact p.Prime] (hM : 1<M) (hb : 1<b) (κ : ℕ)
    {colorNeed : ℕ→ℕ→Need} (hc : PolyNeed colorNeed) :
    PolyNeed (need M b p K κ colorNeed) := by
  obtain ⟨sa,ka,ha⟩ := TernaryGlobalPreludeResources.need_poly (p:=p) (K:=K) hM hb κ
  obtain ⟨sb,kb,hb⟩ := ThreeSumColorDriverResources.poly_need hc
  refine ⟨sa+sb+2,ka+kb,fun n U=>?_⟩
  let F := Light.polyBound (sa+sb) (ka+kb) [n,U]
  have hA := ha n U
  have hB := hb n U
  have hma : Light.polyBound sa ka [n,U]≤F := Light.polyBound_mono (by omega) (by omega) _
  have hmb : Light.polyBound sb kb [n,U]≤F := Light.polyBound_mono (by omega) (by omega) _
  have hF : 1≤F := by
    unfold F Light.polyBound
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    exact Nat.mul_pos (by positivity) (by positivity)
  have he : Light.polyBound (sa+sb+2) (ka+kb) [n,U]=4*F := by
    unfold F Light.polyBound
    rw [pow_add]
    norm_num
    ring
  rw [he]
  dsimp only [need]
  exact ⟨by omega,by omega,by omega⟩

/-- Relocation of the concrete per-color solver into the actual fast
program; the global backend occupies exactly its first fifty procedures. -/
theorem lift_color {lim : Limits} {M b p K κ entry depth T colorMain : ℕ}
    {vals : List ℤ} {μ : ℕ→ℤ} {Post : ℤ→(ℕ→ℤ)→Prop} {color : Program}
    (h : Meets lim color entry depth vals μ T Post) :
    Meets lim (program M b p K κ color colorMain) (50+entry) depth vals μ T Post := by
  have hh := (ReportingHostRelocation.meets h (LightTernaryGlobalPrelude.program M b p K κ)).append
    (LightColorParameters.program.map (ReportingHostRelocation.relocate (50+color.length))++
      [LightColorScan.body (scanEntry color) (50+color.length) (50+colorMain),
        LightColorScanHost.body (scanEntry color),LightTernaryFastProgram.body (hostEntry color)])
  simpa only [LightTernaryFastProgram.program,parameterLibrary,colorsLibrary,
    ReportingHostRelocation.program,List.length_append,List.length_map,
    LightTernaryGlobalPrelude.program_length,List.append_assoc] using hh

/-- Resource and entry composition for the real fast program. The child
contract is stated for the literal per-color program before relocation. -/
theorem meets_of_color {lim : Limits} {M b p K κ n src free depth colorMain colorTime : ℕ}
    [Fact p.Prime] (color : Program) (colorNeed : ℕ→ℕ→Need) (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hM : 1<M) (hb : 1<b) (hn : 0<n) (hsrc : src≤free)
    (H : (need M b p K κ colorNeed n (n^κ)).Ok lim free depth)
    (hcolor : ∀c<p^(LightTernaryDimensions.dim M b p K n (n^κ)), ∀ν₀,
      Receipt M b p K κ n free c μ ν₀→
      ∀ (i : ℕ) (hi : i < ColorParameters.count (LightColorParametersCosts.width n)) (ν : ℕ→ℤ),
      Kept ν₀ ν (scanFree M b p K κ n free)→
      Seg ν (scanFree M b p K κ n free) (ColorParameters.fields (ColorParameters.parameter hi))→
      ∀dd, (colorNeed n (n^κ)).Ok lim (scanFree M b p K κ n free+6) dd→
      Meets lim color colorMain dd
        [src,n,LightTernaryGlobalPrelude.params free,scanFree M b p K κ n free,
          scanFree M b p K κ n free+6] ν colorTime
        (fun z ξ=>(z=0∨z=1) ∧ (z=1↔ColorClassLists.witness (ColorParameters.parameter hi) x) ∧
          Kept ν ξ (scanFree M b p K κ n free))) :
    Meets lim (program M b p K κ color colorMain) (mainEntry color) depth [src,n,free] μ
      (time M b p K κ colorTime n)
      (fun z ν=>(z=0∨z=1) ∧ (z=1↔Coloring.DistinctZeroSum x) ∧ Kept μ ν free) := by
  have B := scan_bounds H
  apply meets_of_colors color x μ hM hb hn hsrc (global_ok H) B.1 B.2.1 B.2.2
  intro c hc ν₀ hreceipt i hi ν hkeep hfields dd hd
  exact lift_color (hcolor c hc ν₀ hreceipt i hi ν hkeep hfields dd (color_ok H hd))

end ThreeSum.TernaryFastProgramResources
