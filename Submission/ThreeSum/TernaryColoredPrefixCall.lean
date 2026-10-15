import Submission.ThreeSum.LightTernaryColoredSolver
import Submission.ThreeSum.LightTernaryPrefixInit

noncomputable section
namespace ThreeSum.TernaryColoredPrefixCall
open Light LightTernaryColoredSolver
set_option maxHeartbeats 1500000
set_option maxRecDepth 24000

/-- The actual prefix initializer182 is procedure237 in the fixed per-color
executable, with every controller, replay and commit procedure relocated. -/
theorem lift {lim : Limits} {radix D E K bDigit a b scaleBase p R F m alpha2 alphaRank localQ L : ℕ}
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ)
    (post : Program) (postMain : ℕ) {entry depth T : ℕ} {args : List ℤ}
    {μ : ℕ→ℤ} {Q : ℤ→(ℕ→ℤ)→Prop}
    (h : Meets lim (LightTernaryPrefixLoop.program p R F K raws words maps xl yl zl xr yr zr)
      entry depth args μ T Q) :
    Meets lim (program radix D E K bDigit a b scaleBase p R F m alpha2 alphaRank localQ L
      raws words maps xl yl zl xr yr zr post postMain) (55+entry) depth args μ T Q := by
  have hh:=(ReportingHostRelocation.meets h (budgetLibrary radix D E K bDigit a b scaleBase)).append
    (post.map (ReportingHostRelocation.relocate 240)++
      [body (240+postMain) m F p alpha2 alphaRank localQ R a b scaleBase L])
  convert hh using 1
  · unfold program libraries ReportingHostRelocation.program
    simp only [List.length_append,List.length_map,budgetLibrary_length,
      LightTernaryPrefixLoop.program_length,List.append_assoc]
  · simp only [budgetLibrary_length]

theorem main_lookup (radix D E K bDigit a b scaleBase p R F m alpha2 alphaRank localQ L : ℕ)
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ)
    (post : Program) (postMain : ℕ) :
    (program radix D E K bDigit a b scaleBase p R F m alpha2 alphaRank localQ L
      raws words maps xl yl zl xr yr zr post postMain)[240+post.length]?=
      some (body (240+postMain) m F p alpha2 alphaRank localQ R a b scaleBase L) := by
  let pre:=libraries radix D E K bDigit a b scaleBase p R F raws words maps xl yl zl xr yr zr
  have hpre : pre.length=240 := libraries_length _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hlen : (ReportingHostRelocation.program pre post).length=240+post.length := by
    simp only [ReportingHostRelocation.program,List.length_append,List.length_map,hpre]
  change (ReportingHostRelocation.program pre post++
    [body (pre.length+postMain) m F p alpha2 alphaRank localQ R a b scaleBase L])[240+post.length]?=_
  rw [List.getElem?_append_right (by rw [hlen]),hlen,Nat.sub_self]
  simp only [List.getElem?_cons_zero,hpre]

end ThreeSum.TernaryColoredPrefixCall
