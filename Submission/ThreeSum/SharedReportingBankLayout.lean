import Submission.ThreeSum.SharedReportingBankData
import Submission.ThreeSum.LightDownsetSize

/-!
# Exact compact layout for a shared reporting catalog cell

The local pair and prefix counts are retained exactly. Each cell reserves
the two prefix arrays, its pointer row, all suffix boxes, the sorted index,
and the polynomial scratch used by the existing constructor. Layout sums
are later computed by the bank setup loop.
-/

namespace ThreeSum.SharedReportingBankLayout

open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog

set_option maxHeartbeats 1400000
set_option maxRecDepth 9000

def localWidth (h : ℕ) : ℕ := 512*h
def width (h J : ℕ) : ℕ := J*localWidth h
def suffixWidth (h J k : ℕ) : ℕ := (J-k)*localWidth h
def localChoose (h : ℕ) : ℕ := (localWidth h).choose h
def localPairs (h : ℕ) : ℕ := LightReportingPrefixArrays.localCount (localWidth h) h
def prefixSpan (h k : ℕ) : ℕ := LightRadixKeys.offset (localPairs h) k+1+count h k
def cap (h J k boxCut : ℕ) : ℕ := downsetCap (suffixWidth h J k) boxCut

def pairL (base h : ℕ) : ℕ := base+localChoose h
def pairR (base h : ℕ) : ℕ := pairL base h+localPairs h
def stageL (base h : ℕ) : ℕ := pairR base h+localPairs h
def stageR (base h k : ℕ) : ℕ := stageL base h+prefixSpan h k
def pointers (base h k : ℕ) : ℕ := stageR base h k+prefixSpan h k
def boxes (base h k : ℕ) : ℕ := pointers base h k+count h k
def masks (base h J k boxCut : ℕ) : ℕ :=
  boxes base h k+count h k*stride (suffixWidth h J k) boxCut
def index (base h J k boxCut : ℕ) : ℕ := masks base h J k boxCut
def work (base h J k boxCut : ℕ) : ℕ := masks base h J k boxCut+cap h J k boxCut+count h k
def finish (base h J k boxCut : ℕ) : ℕ :=
  work base h J k boxCut+2*localWidth h+2+1+tableSize (width h J)+(width h J+1)+count h k
def cellSize (h J k boxCut : ℕ) : ℕ := finish 0 h J k boxCut

def catalog (base h J k boxCut t : ℕ) : ReportingHostLevelData.Catalog :=
  ⟨t,boxCut,boxes base h k,index base h J k boxCut,pointers base h k⟩

theorem stageR_eq (base h k : ℕ) :
    stageR base h k=LightRadixKeys.space (stageL base h) (localPairs h) k := by
  unfold stageR prefixSpan LightRadixKeys.space count localPairs localWidth
  omega

theorem pointers_eq (base h k : ℕ) :
    pointers base h k=LightRadixKeys.space (stageR base h k) (localPairs h) k := by
  unfold pointers prefixSpan LightRadixKeys.space count localPairs localWidth
  omega

theorem ordered (base h J k boxCut : ℕ) :
    base ≤ pairL base h ∧ pairL base h ≤ pairR base h ∧ pairR base h ≤ stageL base h ∧
      stageL base h ≤ stageR base h k ∧ stageR base h k ≤ pointers base h k ∧
      pointers base h k ≤ boxes base h k ∧ boxes base h k ≤ masks base h J k boxCut ∧
      masks base h J k boxCut ≤ work base h J k boxCut ∧
      work base h J k boxCut ≤ finish base h J k boxCut := by
  simp only [finish,work,masks,boxes,pointers,stageR,stageL,pairR,pairL]
  omega

theorem finish_add (base h J k boxCut : ℕ) :
    finish base h J k boxCut=base+cellSize h J k boxCut := by
  unfold cellSize finish work masks boxes pointers stageR stageL pairR pairL
  omega

theorem finish_pos (base h J k boxCut : ℕ) : base < finish base h J k boxCut := by
  have hh := ordered base h J k boxCut
  unfold finish
  omega

theorem index_end (base h J k boxCut : ℕ) :
    index base h J k boxCut+count h k ≤ work base h J k boxCut := by
  unfold index work
  omega

theorem cap_end (base h J k boxCut : ℕ) :
    masks base h J k boxCut+cap h J k boxCut ≤ work base h J k boxCut := by
  unfold work
  omega

theorem pair_scratch (base h J k boxCut : ℕ) :
    work base h J k boxCut+2*(512*h)+2 ≤ finish base h J k boxCut := by
  unfold finish localWidth
  omega

theorem table_scratch (base h J k boxCut : ℕ) :
    work base h J k boxCut+1+tableSize (J*(512*h))+(J*(512*h)+1) ≤
      finish base h J k boxCut := by
  unfold finish width localWidth
  omega

theorem sort_scratch (base h J k boxCut : ℕ) :
    work base h J k boxCut+count h k ≤ finish base h J k boxCut := by
  unfold finish
  omega

theorem downset_scratch {h J k : ℕ} (hk : k ≤ J) (base boxCut : ℕ) :
    base+tableSize ((J-k)*(512*h))+((J-k)*(512*h)+1) ≤ finish base h J k boxCut := by
  have hV : (J-k)*(512*h) ≤ J*(512*h) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have htable : tableSize ((J-k)*(512*h)) ≤ tableSize (J*(512*h)) := by
    exact Nat.pow_le_pow_left (Nat.add_le_add_right hV 1) 2
  have ho := ordered base h J k boxCut
  have hs := table_scratch base h J k boxCut
  omega

theorem reporting_bounds {h J k base baseL baseR cut stop : ℕ}
    (t boxCut : ℕ)
    (hleft : baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ base)
    (hright : baseR+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ base)
    (hcut : cut=LightBlockQuery.sourceCut h J)
    (hstop : finish base h J k boxCut ≤ stop) :
    ReportingHostLevelData.Bounds h J k (catalog base h J k boxCut t) baseL baseR stop := by
  subst cut
  have ho := ordered base h J k boxCut
  have hi := index_end base h J k boxCut
  constructor
  · exact hleft.trans (by omega)
  · exact hright.trans (by omega)
  · change index base h J k boxCut+count h k ≤ stop
    omega
  · change pointers base h k+count h k ≤ stop
    have hh : boxes base h k ≤ stop := by omega
    exact hh
  · change boxes base h k+count h k*stride ((J-k)*(512*h)) boxCut ≤ stop
    have hm : masks base h J k boxCut ≤ stop := by omega
    exact hm

def levelOffset (h J : ℕ) (boxCut : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => levelOffset h J boxCut k+cellSize h J k (boxCut k)

theorem levelOffset_step (h J : ℕ) (boxCut : ℕ → ℕ) (k : ℕ) :
    levelOffset h J boxCut k ≤ levelOffset h J boxCut (k+1) := by
  rw [levelOffset]
  omega

theorem levelOffset_mono (h J : ℕ) (boxCut : ℕ → ℕ) : Monotone (levelOffset h J boxCut) :=
  monotone_nat_of_le_succ (levelOffset_step h J boxCut)

theorem finish_level (base h J k : ℕ) (boxCut : ℕ → ℕ) :
    finish (base+levelOffset h J boxCut k) h J k (boxCut k)=
      base+levelOffset h J boxCut (k+1) := by
  rw [finish_add,levelOffset]
  omega

end ThreeSum.SharedReportingBankLayout
