import Submission.ThreeSum.TernaryArenaSourceSetup
import Submission.ThreeSum.TernaryArenaPairMass
import Submission.ThreeSum.PolynomialResources

/-! Word and depth controls for the actual canonical source initializer.
No advice values, source enumeration, or execution receipts are inputs. -/
noncomputable section
namespace ThreeSum.TernaryArenaSourceControls
open Light TernaryArenaSourceSetup TernaryLocalParameters TernaryNativeCompleteFrontend
open TernaryCoverGoodMaps LightTernarySourceHost
variable {p m F r : ℕ} [Fact p.Prime]

def rowBound (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) : ℕ :=
  (source (r := r) maps cap I right).NL*(localRecords maps cap right).length^r

theorem count_le (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) :
    count (source (r := r) maps cap I right).xs p r (p^r)
      (source (r := r) maps cap I right).NL (source (r := r) maps cap I right).input≤
      rowBound (r := r) maps cap I right := by
  unfold count WantedResidueKeys.total WantedPairs.count LightHistogram.count rowBound
  simp only [source,List.length_map,size]
  calc
    _≤∑ _i∈Finset.range (if right then I.nC else I.nB), (localRecords maps cap right).length^r := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
    _=_ := by simp

def components (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) : List ℕ :=
  let S := source (r := r) maps cap I right
  [LightRadixKeys.word S.p0 S.U0 r,LightRadixKeys.word S.p1 S.U1 r,
    LightRadixKeys.word S.p2 S.U2 r,LightSourceResidues.word S.M S.M S.U 0,
    S.bank+2^(S.W+1)+16,S.groups*S.bank+1,S.factor,
    S.factor*(rowBound (r := r) maps cap I right*S.weightU),
    (rowBound (r := r) maps cap I right+1)*S.weightU]

def word (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) : ℕ :=
  (components (r := r) maps cap I right).sum

def depth (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) : ℕ :=
  let S := source (r := r) maps cap I right
  S.NL+S.L+S.J+8

def need (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) : Need :=
  ⟨word (r := r) maps cap I right,0,depth (r := r) maps cap I right⟩

structure Controls (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (lim : Limits) (d : ℕ) : Prop where
  hword0 : (LightRadixKeys.word (source (r := r) maps cap I right).p0
    (source (r := r) maps cap I right).U0 r : ℤ)≤lim.word
  hword1 : (LightRadixKeys.word (source (r := r) maps cap I right).p1
    (source (r := r) maps cap I right).U1 r : ℤ)≤lim.word
  hword2 : (LightRadixKeys.word (source (r := r) maps cap I right).p2
    (source (r := r) maps cap I right).U2 r : ℤ)≤lim.word
  join : (LightSourceResidues.word (p^r) (p^r) (p*(p+1)^r) 0 : ℤ)≤lim.word
  lookup : (((nb m r)+2^(2*N m r+1)+16 : ℕ) : ℤ)≤lim.word
  group : (((F^r)*(nb m r)+1 : ℕ) : ℤ)≤lim.word
  factor : (((2^(r*fixedAlpha m 2)) : ℕ) : ℤ)≤lim.word
  weighted : ((source (r := r) maps cap I right).factor : ℤ)*
    (count (source (r := r) maps cap I right).xs p r (p^r)
      (source (r := r) maps cap I right).NL (source (r := r) maps cap I right).input*I.weightCap : ℕ)≤lim.word
  hist : ((count (source (r := r) maps cap I right).xs p r (p^r)
      (source (r := r) maps cap I right).NL (source (r := r) maps cap I right).input+1 : ℕ) : ℤ)*I.weightCap≤lim.word
  callDepth : d+(source (r := r) maps cap I right).NL+2*N m r+r+8≤lim.depth

theorem controls {lim : Limits} {d fr : ℕ} (maps : Fin F→Weight m p) (cap : ℕ)
    (I : Input) (right : Bool) (h : (need (r := r) maps cap I right).Ok lim fr d) :
    Controls (r := r) maps cap I right lim d := by
  have hw := h.word
  change (word (r := r) maps cap I right : ℤ)≤lim.word at hw
  have hpart (x : ℕ) (hx : x∈components (r := r) maps cap I right) :
      (x : ℤ)≤lim.word := (Int.ofNat_le.mpr (List.le_sum_of_mem hx)).trans hw
  have hcount := count_le (r := r) maps cap I right
  have hweighted := Nat.mul_le_mul_left (2^(r*fixedAlpha m 2))
    (Nat.mul_le_mul_right I.weightCap hcount)
  have hhist := Nat.mul_le_mul_right I.weightCap (Nat.add_le_add_right hcount 1)
  refine ⟨hpart _ (by simp [components]),hpart _ (by simp [components]),
    hpart _ (by simp [components]),hpart _ (by simp [components,source]),
    hpart _ (by simp [components,source]),hpart _ (by simp [components,source]),
    hpart _ (by simp [components,source]),?_,?_,?_⟩
  · have hh := hpart (2^(r*fixedAlpha m 2)*(rowBound (r := r) maps cap I right*I.weightCap))
      (by simp [components,source])
    exact (by exact_mod_cast hweighted :
      ((source (r := r) maps cap I right).factor : ℤ)*
        (count (source (r := r) maps cap I right).xs p r (p^r)
          (source (r := r) maps cap I right).NL (source (r := r) maps cap I right).input*I.weightCap : ℕ)≤
        (2^(r*fixedAlpha m 2)*(rowBound (r := r) maps cap I right*I.weightCap) : ℕ)).trans hh
  · have hh := hpart ((rowBound (r := r) maps cap I right+1)*I.weightCap)
      (by simp [components,source])
    exact (by exact_mod_cast hhist :
      ((count (source (r := r) maps cap I right).xs p r (p^r)
          (source (r := r) maps cap I right).NL (source (r := r) maps cap I right).input+1 : ℕ) : ℤ)*I.weightCap≤
        (((rowBound (r := r) maps cap I right+1)*I.weightCap : ℕ) : ℤ)).trans hh
  · have hd := h.depth
    simpa only [need,depth,source,Nat.add_assoc] using hd

end ThreeSum.TernaryArenaSourceControls
