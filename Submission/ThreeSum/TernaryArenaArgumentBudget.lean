import Submission.ThreeSum.TernaryArenaArgumentWords
import Submission.ThreeSum.TernaryArenaSourceControlBudget

noncomputable section
namespace ThreeSum.TernaryArenaArgumentBudget
open Light TernaryArenaSourceSetup TernaryArenaArgumentWords TernaryArenaSourceControlBudget
open TernaryLocalParameters

private theorem radix_base_le (P r : ℕ) : P≤LightRadixKeys.word P P r := by
  unfold LightRadixKeys.word LightRadixRows.word
  exact (Nat.le_add_right P _).trans ((Nat.le_add_right _ P).trans (Nat.le_add_right _ 1))

private theorem cut_le (m r : ℕ) : cut m r≤2*N m r := by
  simp only [cut,LightTernaryPrefixSetup.T,N,fixedLength]
  ring_nf
  omega
private theorem source_rank_le (m r : ℕ) : r*alphaRank m≤2*N m r := by
  simp [alphaRank,fixedAlpha,N,fixedLength]
  ring_nf
  omega

theorem scalar_le (m p F r count B D : ℕ)
    (hbase : baseWord m p F r≤B) (hdepth : 2*N m r+r+8≤D) :
    scalarControl m p F r count≤16*(B+D+1)^2+count := by
  let parts := [LightRadixKeys.word p p r,
    LightRadixKeys.word (4^fixedLength m) (4^fixedLength m) r,
    LightRadixKeys.word F F r,
    LightSourceResidues.word (p^r) (p^r) (p*(p+1)^r) 0,
    4^(N m r)+2^(2*N m r+1)+16,F^r*4^(N m r)+1,2^(r*fixedAlpha m 2)]
  have hpart (x : ℕ) (hx : x∈parts) : x≤B := by
    calc
      _≤parts.sum := List.le_sum_of_mem hx
      _=baseWord m p F r := by simp only [parts,baseWord,List.sum_cons,List.sum_nil]; ring
      _≤B := hbase
  have hp : p≤B := (radix_base_le p r).trans (hpart _ (by simp [parts]))
  have hw : 4^fixedLength m≤B := (radix_base_le _ r).trans (hpart _ (by simp [parts]))
  have hF : F≤B := (radix_base_le F r).trans (hpart _ (by simp [parts]))
  have hmod : p^r≤B := by
    have hh : p^r≤LightSourceResidues.word (p^r) (p^r) (p*(p+1)^r) 0 := by
      generalize p^r=a, p*(p+1)^r=u
      unfold LightSourceResidues.word
      omega
    exact hh.trans (hpart _ (by simp [parts]))
  have hfour : 4^(N m r)≤B :=
    (Nat.le_add_right (4^(N m r)) (2^(2*N m r+1))).trans
      ((Nat.le_add_right _ 16).trans (hpart (4^(N m r)+2^(2*N m r+1)+16) (by simp [parts])))
  have hfactor : 2^(r*fixedAlpha m 2)≤B := hpart _ (by simp [parts])
  have hgroup : F^r≤B := by
    have hh : F^r≤F^r*4^(N m r) := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by decide))
    exact (hh.trans (Nat.le_add_right _ 1)).trans (hpart _ (by simp [parts]))
  have hnb : nb m r≤B := (bank_le m r).trans hfour
  have hN : N m r+1≤D := by omega
  have h2N : 2*N m r≤D := by omega
  have hr : r≤D := by omega
  have hT : 1≤B+D+1 := by omega
  have hB2 : B≤(B+D+1)^2 := (show B≤B+D+1 by omega).trans
    (by nlinarith only [hT])
  have hD2 : D≤(B+D+1)^2 := (show D≤B+D+1 by omega).trans
    (by nlinarith only [hT])
  have hprod : D*B≤(B+D+1)^2 := by nlinarith only [Nat.zero_le B,Nat.zero_le D]
  have hstride : (N m r+1)*nb m r≤(B+D+1)^2 := (Nat.mul_le_mul hN hnb).trans hprod
  have htail : N m r*nb m r≤(B+D+1)^2 :=
    (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans hstride
  have hall : ∀ x∈scalars m p F r 0, x≤(B+D+1)^2 := by
    intro x hx
    simp only [scalars,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact hr.trans hD2 | exact hp.trans hB2 | exact hw.trans hB2 | exact hF.trans hB2
      | exact hmod.trans hB2 | exact hnb.trans hB2 | exact h2N.trans hD2
      | exact ((cut_le m r).trans h2N).trans hD2
      | exact ((source_rank_le m r).trans h2N).trans hD2
      | exact hfactor.trans hB2 | exact hgroup.trans hB2 | exact hstride | exact htail
      | exact hfour.trans hB2 | exact Nat.zero_le _ | nlinarith only [hT]
  have hs := (scalars m p F r 0).sum_le_card_nsmul ((B+D+1)^2) hall
  have hs' : scalarControl m p F r 0≤16*(B+D+1)^2 := by simpa [scalarControl,scalars] using hs
  have he : scalarControl m p F r count=scalarControl m p F r 0+count := by
    simp only [scalarControl,scalars,List.sum_cons,List.sum_nil]
    ring
  rw [he]
  exact Nat.add_le_add_right hs' count

def need (m p F M n U : ℕ) : Need :=
  let S := budget m p F 1 M 0 0 n U
  ⟨16*(S.word+S.depth+1)^2,0,0⟩

theorem actual_scalar_le {m p F M r n U count : ℕ}
    (hp : 1≤p) (hF : 1≤F) (hr : r≤Nat.clog M (n^2)) :
    scalarControl m p F r count≤(need m p F M n U).word+count := by
  let S := budget m p F 1 M 0 0 n U
  have hb : baseWord m p F r≤S.word := by
    have hm := upperWord_mono (m := m) hp hF (by decide : 1≤1) hr (le_refl n) (le_refl 0)
    have hm' : baseWord m p F r≤baseWord m p F (Nat.clog M (n^2)) := by
      simpa [upperWord] using hm
    exact hm'.trans (by dsimp [S,budget]; omega)
  have hd : 2*N m r+r+8≤S.depth := by
    have hNr := Nat.mul_le_mul_right (fixedLength m) hr
    dsimp only [S,budget,N] at *
    omega
  exact scalar_le m p F r count S.word S.depth hb hd

theorem polyNeed (m p F M : ℕ) (hM : 1<M) : PolyNeed (need m p F M) := by
  obtain ⟨s,k,h⟩ := budget_polyNeed m p F 1 M 0 0 hM
  refine ⟨2*s+8,2*k,?_⟩
  intro n U
  let X := polyBound s k [n,U]
  have hX : 1≤X := Nat.succ_le_of_lt (by
    simp only [X,polyBound,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    positivity)
  have hx : (budget m p F 1 M 0 0 n U).word+(budget m p F 1 M 0 0 n U).depth+1≤3*X := by
    have hw := (h n U).1
    have hd := (h n U).2.2
    change _≤X at hw hd
    omega
  have he : polyBound (2*s+8) (2*k) [n,U]=256*X^2 := by
    dsimp [X,polyBound]
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    rw [show 2*s+8=s*2+8 by omega,pow_add,show 2*k=k*2 by omega,pow_mul,pow_mul,mul_pow]
    norm_num
    ring
  refine ⟨?_,Nat.zero_le _,Nat.zero_le _⟩
  change 16*((budget m p F 1 M 0 0 n U).word+(budget m p F 1 M 0 0 n U).depth+1)^2≤_
  rw [he]
  exact (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hx 2)).trans (by nlinarith)

end ThreeSum.TernaryArenaArgumentBudget
