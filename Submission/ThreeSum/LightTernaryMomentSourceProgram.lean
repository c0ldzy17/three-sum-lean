import Submission.ThreeSum.LightTernarySourceCountHost
import Submission.ThreeSum.LightTernaryMomentChannelStep

/-! The signed moment channel is linked to the actual 123-procedure source
and count host, including its dictionary, join, bank, and query programs. -/
noncomputable section
namespace ThreeSum.LightTernaryMomentSourceProgram
open Light TernaryWeightChannels

def positions : List ℕ := (List.range 106).map (fun i => 9+i)

def extra (k j : ℕ) : Program := [
  LightTernaryScalarChannel.body (leftMoment k j),
  LightTernaryScalarChannel.body (rightMoment k j),
  LightTernaryMomentAccumulate.body,
  LightTernaryMomentChannelStep.body k j 123 124 122 125 positions 115]

def program (xl yl zl xr yr zr : List ℤ) (k j : ℕ) : Program :=
  LightTernarySourceCountHost.program xl yl zl xr yr zr++extra k j

@[simp] theorem program_length (xl yl zl xr yr zr : List ℤ) (k j : ℕ) :
    (program xl yl zl xr yr zr k j).length=127 := by
  simp [program,extra]

def procs (xl yl zl xr yr zr : List ℤ) (k j arity : ℕ) :
    LightTernaryMomentChannelStep.Procs k j positions arity (program xl yl zl xr yr zr k j) 126 where
  pLeft := 123
  pRight := 124
  pHost := 122
  pAdd := 125
  left := by
    change (LightTernarySourceCountHost.program xl yl zl xr yr zr++extra k j)[123]?=_
    rw [List.getElem?_append_right (by simp),LightTernarySourceCountHost.program_length]
    rfl
  right := by
    change (LightTernarySourceCountHost.program xl yl zl xr yr zr++extra k j)[124]?=_
    rw [List.getElem?_append_right (by simp),LightTernarySourceCountHost.program_length]
    rfl
  add := by
    change (LightTernarySourceCountHost.program xl yl zl xr yr zr++extra k j)[125]?=_
    rw [List.getElem?_append_right (by simp),LightTernarySourceCountHost.program_length]
    rfl
  main := by
    change (LightTernarySourceCountHost.program xl yl zl xr yr zr++extra k j)[126]?=_
    rw [List.getElem?_append_right (by simp),LightTernarySourceCountHost.program_length]
    rfl

theorem positions_range (arity : ℕ) (h : arity=115) :
    ∀ a∈positions, 9≤a ∧ a<arity := by
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
  have hi' := List.mem_range.mp hi
  omega

/-- Backend argument locations are ordinary local-variable reads, and give
exactly the source/count host's complete 106-argument runtime frame. -/
theorem values_positions (originalB nB originalC nC leftWeight rightWeight matrix count out : ℕ)
    (backend : List ℤ) (hlen : backend.length=106) :
    LightTernaryMomentChannelStep.values positions
      (LightTernaryMomentChannelStep.args originalB nB originalC nC
        leftWeight rightWeight matrix count out backend)=backend := by
  apply List.ext_getElem (by simp [LightTernaryMomentChannelStep.values,positions,hlen])
  intro i hi hi'
  have hi106 : i<106 := by omega
  simp only [LightTernaryMomentChannelStep.values,positions,List.getElem_map,List.getElem_range]
  change (LightTernaryMomentChannelStep.args originalB nB originalC nC
    leftWeight rightWeight matrix count out backend).getD (9+i) 0=backend[i]
  rw [LightTernaryMomentChannelStep.args,List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.add_sub_cancel_left]
  exact List.getD_eq_getElem _ _ hi'

/-- The registered host receipt is obtained from the actual included host
execution theorem and remains valid after adjoining the channel kernels. -/
theorem host_meets {lim : Limits} {d TL TR TC keepLeft keepRight keepFront
    fbase gbase groups bank count dst k j : ℕ}
    (xl yl zl xr yr zr left right frontend : List ℤ) (μ : ℕ→ℤ)
    (F G : ℕ→ℕ→ℤ) (value : ℕ→ℤ)
    (hl : left.length=23) (hr : right.length=23) (hf : frontend.length=60)
    (hkeepRight : keepLeft≤keepRight) (hkeepFront : keepLeft≤keepFront)
    (hFend : fbase+groups*bank≤keepRight)
    (hleft : Meets lim (LightTernarySourceHost.program xl yl zl) 34 (d+1) left μ TL
      (fun _ ν => Kept μ ν keepLeft ∧ LightTernarySourceCountHost.BankReads ν fbase groups bank F))
    (hright : ∀ ν, Kept μ ν keepLeft →
      Meets lim (LightTernarySourceHost.program xr yr zr) 34 (d+1) right ν TR
        (fun _ ξ => Kept ν ξ keepRight ∧ LightTernarySourceCountHost.BankReads ξ gbase groups bank G))
    (hfrontend : ∀ ν, Kept μ ν keepLeft →
      LightTernarySourceCountHost.BankReads ν fbase groups bank F →
      LightTernarySourceCountHost.BankReads ν gbase groups bank G →
      Meets lim LightTernaryCountFrontend.program 50 (d+1) frontend ν TC
        (fun _ ξ => Kept ν ξ keepFront ∧ ∀ i<count, ξ (dst+i)=value i))
    (hd : d<lim.depth) :
    Meets lim (program xl yl zl xr yr zr k j) 122 d
      (LightTernarySourceCountHost.args left right frontend) μ
      (LightTernarySourceCountHost.time TL TR TC)
      (fun _ ν => Kept μ ν keepLeft ∧ ∀ i<count, ν (dst+i)=value i) := by
  exact (LightTernarySourceCountHost.program_meets xl yl zl xr yr zr left right frontend μ
    F G value hl hr hf hkeepRight hkeepFront hFend hleft hright hfrontend hd).append (extra k j)

end ThreeSum.LightTernaryMomentSourceProgram
