import Submission.ThreeSum.LightHistogram
import Submission.ThreeSum.TernaryOriginalCollisions

/-! Actual original-record histogram and ordered distinct collision score. -/
noncomputable section
namespace ThreeSum.LightOriginalCollisionScore
open Light Finset
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000

def prefixScore (keys : ℕ → ℕ) (n j : ℕ) : ℕ := ∑ i∈range j, (LightHistogram.count keys (keys i) n-1)

def score (keys : ℕ → ℕ) (n : ℕ) : ℕ := prefixScore keys n n

theorem prefixScore_succ (keys : ℕ → ℕ) (n j : ℕ) : prefixScore keys n (j+1)=
    prefixScore keys n j+(LightHistogram.count keys (keys j) n-1) := sum_range_succ _ _

theorem prefixScore_le (keys : ℕ → ℕ) (n j : ℕ) : prefixScore keys n j≤j*n := by
  calc
    _≤∑ _i∈range j, n := Finset.sum_le_sum (fun i _ => by have := LightHistogram.count_le keys (keys i) n; omega)
    _=j*n := by simp

theorem own_count_positive {keys : ℕ → ℕ} {n i : ℕ} (hi : i<n) : 0<LightHistogram.count keys (keys i) n := by
  apply Finset.card_pos.mpr
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,rfl⟩⟩

theorem other_count {keys : ℕ → ℕ} {n i : ℕ} (hi : i<n) :
    LightHistogram.count keys (keys i) n-1=
      ((range n).filter (fun j => j≠i ∧ keys j=keys i)).card := by
  let S := (range n).filter (fun j => keys j=keys i)
  have hm : i∈S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,rfl⟩
  have he : S.erase i=(range n).filter (fun j => j≠i ∧ keys j=keys i) := by
    ext j
    simp only [S,Finset.mem_erase,Finset.mem_filter,Finset.mem_range]
    tauto
  rw [←he,Finset.card_erase_of_mem hm]
  rfl

theorem score_eq_collision_card (keys : ℕ → ℕ) (n : ℕ) :
    score keys n=(TernaryOriginalCollisions.collisionPairs (fun i : Fin n => keys i.val)).card := by
  unfold score prefixScore TernaryOriginalCollisions.collisionPairs
  rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_prod_type,←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [other_count i.isLt,Finset.card_eq_sum_ones,Finset.sum_filter,←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp [Fin.ext_iff,eq_comm,and_comm]

def roundBody : Stmt :=
  .set 6 (M (v 0 +' v 5)) ;;
  .set 7 (M (v 2 +' v 6)) ;;
  .set 4 (v 4 +' v 7 -' k 1)

def sumBody : Stmt := .set 4 (k 0) ;; .for 5 (v 1) roundBody ;; .set 0 (v 4)
def sumTime (n : ℕ) : ℕ := 50*n+100

def Inv (μ : ℕ → ℤ) (src n hist q : ℕ) (keys : ℕ → ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ key count : ℤ, σ=⟨frame [src,n,hist,q,prefixScore keys n j,j,key,count],μ⟩

variable {lim : Limits} {P : Program}

theorem sum_meets {pMain src n hist q d : ℕ} (hmain : P[pMain]?=some sumBody)
    (μ : ℕ → ℤ) (keys : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+n≤lim.space) (hhist : hist+q≤lim.space)
    (hword : ((n*n+n+q+16 : ℕ) : ℤ)≤lim.word)
    (hkeys : ∀ i<n, keys i<q) (hread : ∀ i<n, μ (src+i)=(keys i : ℤ))
    (hcounts : ∀ r<q, μ (hist+r)=(LightHistogram.count keys r n : ℤ)) :
    Meets lim P pMain d [src,n,hist,q] μ (sumTime n)
      (fun r ν => r=(score keys n : ℤ) ∧ ν=μ) := by
  apply Meets.of_body hmain
  unfold sumBody sumTime
  light_set 0
  refine Ends.pieceThen (Ends.for (T := 50*n+30)
    (Q := Inv μ src n hist q keys n) (Inv μ src n hist q keys) n 30
    ?start ?round ?done ?bound (hT := by light_time)) ?after (hT := by light_time)
  case start =>
    refine ⟨0,0,?_⟩
    simp [update_frame_setLocal,prefixScore]
    change frame [(src : ℤ),n,hist,q,0,0]=frame ([(src : ℤ),n,hist,q,0,0]++[0,0])
    exact (frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨key,count,rfl⟩
    have hk := hkeys j hj
    have hRead := hread j hj
    have hCountRead := hcounts _ hk
    have hCount := LightHistogram.count_le keys (keys j) n
    have hPos := own_count_positive (keys := keys) hj
    have hPartial := prefixScore_le keys n j
    have hjn : j*n≤n*n := Nat.mul_le_mul_right n (Nat.le_of_lt hj)
    have hNext := prefixScore_succ keys n j
    have hCast : (prefixScore keys n j : ℤ)+(LightHistogram.count keys (keys j) n : ℤ)-1=
        (prefixScore keys n (j+1) : ℤ) := by rw [hNext,Nat.cast_add,Nat.cast_sub (by omega)]; push_cast; ring
    unfold roundBody
    light_set (keys j : ℕ) using hRead
    light_set (LightHistogram.count keys (keys j) n : ℕ) using hCountRead
    light_set (prefixScore keys n (j+1) : ℕ) using hCast
    refine ⟨by simp,(keys j : ℤ),(LightHistogram.count keys (keys j) n : ℤ),?_⟩
    simp [update_frame_setLocal]
  case done => intro σ _ H; exact H
  case bound => rintro j _ hj _ ⟨key,count,rfl⟩; light_side
  case after =>
    rintro _ ⟨key,count,rfl⟩
    have hp := prefixScore_le keys n n
    light_set (score keys n : ℕ) using score
    exact ⟨by simp,rfl⟩

def body (pHist pSum : ℕ) : Stmt :=
  .call pHist [v 0,v 2,v 1,v 3] 4 ;;
  .call pSum [v 0,v 1,v 2,v 3] 0

def time (n q : ℕ) : ℕ := LightHistogram.histogramTime n q+sumTime n+100

theorem meets {pMain pHist pFill pSum src n hist q d : ℕ}
    (hmain : P[pMain]?=some (body pHist pSum))
    (hhist : P[pHist]?=some (LightHistogram.histogramBody pFill))
    (hfill : P[pFill]?=some fillBody) (hsum : P[pSum]?=some sumBody)
    (μ : ℕ → ℤ) (keys : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+n≤lim.space) (hhistSpace : hist+q≤lim.space)
    (hsep : Apart src n hist q)
    (hword : ((n*n+n+q+16 : ℕ) : ℤ)≤lim.word)
    (hkeys : ∀ i<n, keys i<q) (hread : ∀ i<n, μ (src+i)=(keys i : ℤ))
    (hd : d+2≤lim.depth) :
    Meets lim P pMain d [src,n,hist,q] μ (time n q)
      (fun r ν => r=((TernaryOriginalCollisions.collisionPairs (fun i : Fin n => keys i.val)).card : ℤ) ∧
        (∀ k<q, ν (hist+k)=(LightHistogram.count keys k n : ℤ)) ∧ SameOutside μ ν hist q) := by
  have hc := LightHistogram.histogram_meets (d := d+1) hhist hfill keys hw (by omega)
    hsrc hhistSpace hsep hread hkeys
  apply Meets.of_body hmain
  unfold body time
  light_call hc using LightHistogram.histogramTime,sumTime
    with count ν ⟨hCounts,H⟩
  have hRead : ∀ i<n, ν (src+i)=(keys i : ℤ) := by
    intro i hi; rw [H _ (by omega),hread i hi]
  have hs := sum_meets (d := d+1) hsum ν keys hw hsrc hhistSpace hword hkeys hRead hCounts
  light_call hs using LightHistogram.histogramTime,sumTime
    with result ξ ⟨hResult,hMem⟩
  subst ξ
  refine ⟨?_,hCounts,H⟩
  change result=_
  simpa only [score_eq_collision_card] using hResult

theorem time_eq (n q : ℕ) : time n q=74*n+13*q+217 := by
  unfold time LightHistogram.histogramTime LightHistogram.countTime fillTime sumTime
  ring

def program : Program := [body 1 3,LightHistogram.histogramBody 2,fillBody,sumBody]
@[simp] theorem program_length : program.length=4 := rfl

def program_meets {lim : Limits} {src n hist q d : ℕ} :=
  meets (lim := lim) (P := program) (pMain := 0) (pHist := 1) (pFill := 2) (pSum := 3)
    (src := src) (n := n) (hist := hist) (q := q) (d := d) rfl rfl rfl rfl

end ThreeSum.LightOriginalCollisionScore
