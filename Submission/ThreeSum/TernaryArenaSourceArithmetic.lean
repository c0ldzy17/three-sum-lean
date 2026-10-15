import Submission.ThreeSum.TernaryArenaSourceBounds
import Submission.ThreeSum.TernaryArenaSourceControls
import Submission.ThreeSum.TernaryArenaSourceLayout

noncomputable section
namespace ThreeSum.TernaryArenaSourceArithmetic
open Light TernaryArenaPrefixFootprints TernaryArenaSourceSetup TernaryArenaSourceBounds
open TernaryCoverGoodMaps TernaryLocalParameters TernaryNativeCompleteFrontend
open LightTernarySourceHost TernaryArenaLayout
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem geometry {lim : Limits} (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (n U : ℕ) (hnB : I.nB≤n) (hnC : I.nC≤n)
    (HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r))
    (hend : finish I.free I.capacity≤lim.space) (right : Bool) :
    TernaryArenaSourceLayout.Geometry (source (r := r) maps cap I right) lim.space := by
  let S := source (r := r) maps cap I right
  let A := numbers maps τ cap M b K H drift scale n U r
  have hs := source_space (r := r) maps cap I right n hnB hnC
  have hl : S.xs.length≤I.capacity := by
    have h := local_le maps cap right
    have hA := HC.localSize
    dsimp [S,source,A,numbers] at hA ⊢
    simp only [List.length_map]
    omega
  have hr : LightRadixKeys.space 0 S.xs.length r≤I.capacity := hs.1.trans HC.radixCells
  have hJC : 10+n+2*(sourceWidth maps cap)^r+4*p^r+p*(p+1)^r+2*n*(sourceWidth maps cap)^r≤I.capacity := by
    simpa only [numbers,Nat.mul_assoc] using HC.joinCells
  have hj : LightWantedSetup.space 0 (p^r) S.input (dictionary S.xs p r) S.NL
      (size S.xs r) (p*(p+1)^r) 0 0≤I.capacity := hs.2.2.trans hJC
  have hh : count S.xs p r (p^r) S.NL S.input≤I.capacity := hs.2.1.trans HC.hits
  have hv : S.groups*S.bank≤I.capacity := by
    have hb := bank_size m r
    have h := HC.sourceHistogram
    dsimp [S,source,numbers] at h ⊢
    nlinarith [Nat.mul_le_mul_left (F^r) hb]
  have G := TernaryArenaSourceLayout.geometry S
    (start := if right then 39 else 30)
    (by cases right <;> simp) hend hl hr hj hh hv
  cases right <;> simpa [TernaryArenaSourceLayout.setup,S,source] using G

theorem controls {lim : Limits} {d : ℕ} (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (n U : ℕ) (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hweight : I.weightCap≤weight H (4^fixedLength m) U)
    (HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r))
    (hw : (I.capacity : ℤ)≤lim.word) (hd : d+I.capacity≤lim.depth) (right : Bool) :
    TernaryArenaSourceControls.Controls (r := r) maps cap I right lim d := by
  let A := numbers maps τ cap M b K H drift scale n U r
  have hword : (A.sourceWord : ℤ)≤lim.word := (Int.ofNat_le.mpr HC.sourceWord).trans hw
  have leWord (x : ℕ) (hx : x≤A.sourceWord) : (x : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  obtain ⟨h0,h1,h2,hj,hl,hg,hf,hv,hh⟩ := source_words (r := r) maps τ cap M b K H drift scale
    I right n U hnB hnC hweight (bank_size m r)
  refine ⟨leWord _ h0,leWord _ h1,leWord _ h2,leWord _ hj,
    leWord _ hl,leWord _ hg,leWord _ hf,?_,?_,?_⟩
  · simpa only [Nat.cast_mul] using leWord _ hv
  · simpa only [Nat.cast_mul] using leWord _ hh
  · have hn : (source (r := r) maps cap I right).NL≤n := by
      cases right
      · simpa [source] using hnB
      · simpa [source] using hnC
    have hcap := HC.depth
    have hN : N m r=fixedLength m*r := by unfold N; ring
    dsimp [numbers] at hcap
    rw [hN]
    omega

end ThreeSum.TernaryArenaSourceArithmetic
