import Submission.ThreeSum.LightTernaryFrozenQuery
import Submission.ThreeSum.TernaryFrozenQueryStages

namespace ThreeSum.LightTernaryFrozenQuery
open Light ThreeSum.TernaryQuery
set_option maxHeartbeats 3000000

def branches (pSelf : ℕ) : Stmt :=
  .ite (v 13 =' k 0)
    (.call pSelf (childArgs (v 14) (k 0)) 0)
    (.ite (v 13 =' k 1)
      (.call pSelf (childArgs (v 14) (k 1)) 18 ;;
        .call pSelf (childArgs (v 15) (k 0)) 19 ;;
        .set 0 (v 19 -' v 18))
      (.call pSelf (childArgs (v 14) (k 2)) 18 ;;
        .call pSelf (childArgs (v 15) (k 1)) 19 ;;
        .call pSelf (childArgs (v 4) (k 0)) 20 ;;
        .set 0 (v 20 -' k 2 *' v 19 +' v 18)))

def preparedInputs (N K rank cut : ℕ) (code : ℤ)
    (bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ)
    (q : Fin 3) (c0 c1 : ℤ) : List ℤ :=
  inputs N (K+1) rank cut code bankCodes bankCount bankValues nearCodes nearCount nearValues powers L ++
    [(q.val : ℤ),c0,c1,(K : ℤ)]

variable {lim : Limits} {P : Program}

theorem branches_meets {pSelf d : ℕ}
    (N K rank cut bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ)
    (code c0 c1 : ℤ) (q : Fin 3) (f : Fin 3 → ℤ) (t : Fin 3 → ℕ)
    (μ : ℕ → ℤ)
    (hargs : ∀ x ∈ preparedInputs N K rank cut code bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L q c0 c1, |x| ≤ lim.word)
    (hword : 4 * (max (|f 0|) (max (|f 1|) (|f 2|))) + 3 ≤ lim.word)
    (hrank : q.val ≤ rank) (hd : d+1 ≤ lim.depth)
    (hchild : ∀ r : Fin 3, r ≤ q → Meets lim P pSelf (d+1)
      (inputs N K (rank-(q.val-r.val)) cut
        (if r=0 then c0 else if r=1 then c1 else code)
        bankCodes bankCount bankValues nearCodes nearCount nearValues powers L) μ (t r)
      (fun v μ' => v=f r ∧ μ'=μ)) :
    Ends lim P d (branches pSelf) ⟨frame (preparedInputs N K rank cut code bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L q c0 c1),μ⟩
      (t 0+t 1+t 2+200)
      (fun σ => σ.loc 0 = inverseDigit f q ∧ σ.mem=μ) := by
  have ha (x : ℤ) (hx : x ∈ preparedInputs N K rank cut code bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L q c0 c1) := abs_le.mp (hargs x hx)
  have hN := ha N (by simp [preparedInputs,inputs])
  have hK := ha K (by simp [preparedInputs,inputs])
  have hR := ha rank (by simp [preparedInputs,inputs])
  have hT := ha cut (by simp [preparedInputs,inputs])
  have hC := ha code (by simp [preparedInputs,inputs])
  have hBC := ha bankCodes (by simp [preparedInputs,inputs])
  have hBN := ha bankCount (by simp [preparedInputs,inputs])
  have hBV := ha bankValues (by simp [preparedInputs,inputs])
  have hNC := ha nearCodes (by simp [preparedInputs,inputs])
  have hNN := ha nearCount (by simp [preparedInputs,inputs])
  have hNV := ha nearValues (by simp [preparedInputs,inputs])
  have hP := ha powers (by simp [preparedInputs,inputs])
  have hL := ha L (by simp [preparedInputs,inputs])
  have hC0 := ha c0 (by simp [preparedInputs,inputs])
  have hC1 := ha c1 (by simp [preparedInputs,inputs])
  have hf0 := abs_le.mp (le_max_left (|f 0|) (max (|f 1|) (|f 2|)))
  have hf1 := abs_le.mp ((le_max_left (|f 1|) (|f 2|)).trans (le_max_right (|f 0|) (max (|f 1|) (|f 2|))))
  have hf2 := abs_le.mp ((le_max_right (|f 1|) (|f 2|)).trans (le_max_right (|f 0|) (max (|f 1|) (|f 2|))))
  have hm : 0 ≤ max (|f 0|) (max (|f 1|) (|f 2|)) := (abs_nonneg (f 0)).trans (le_max_left _ _)
  have hcast (a : ℕ) (ha : a ≤ rank) : (rank : ℤ)-(a : ℤ)=((rank-a : ℕ) : ℤ) := by omega
  have hdropFirst (a : ℕ) (ha : a ≤ q.val) := hcast a (ha.trans hrank)
  unfold branches childArgs preparedInputs inputs
  fin_cases q
  · have hc := hchild 0 (by decide)
    simp [inputs] at hc
    light_if he hn : (0 : ℤ) = 0
    · light_call hc using inputs with v μ' ⟨hv,hm⟩
      exact ⟨by simpa [inverseDigit] using hv,hm⟩
    · exfalso; exact hn rfl
  · have hc0 := hchild 0 (by decide)
    have hc1 := hchild 1 (by decide)
    norm_num [inputs] at hc0 hc1 hrank 
    have hdrop := hdropFirst 1 (by decide)
    light_if he hn : (1 : ℤ) = 0
    · exfalso; omega
    · light_if he hn : (1 : ℤ) = 1
      · light_call hc0 using hdrop with v0 μ0 ⟨hv0,hm0⟩
        subst μ0
        light_call hc1 with v1 μ1 ⟨hv1,hm1⟩
        subst μ1
        light_set (f 1-f 0) using hv0,hv1
        exact ⟨by simp [inverseDigit],rfl⟩
      · exfalso; exact hn rfl
  · have hc0 := hchild 0 (by decide)
    have hc1 := hchild 1 (by decide)
    have hc2 := hchild 2 (by decide)
    norm_num [inputs] at hc0 hc1 hc2 hrank 
    have hdrop1 := hdropFirst 1 (by decide)
    have hdrop2 := hdropFirst 2 (by decide)
    light_if he hn : (2 : ℤ) = 0
    · exfalso; omega
    · light_if he hn : (2 : ℤ) = 1
      · exfalso; omega
      · light_call hc0 using hdrop2 with v0 μ0 ⟨hv0,hm0⟩
        subst μ0
        light_call hc1 using hdrop1 with v1 μ1 ⟨hv1,hm1⟩
        subst μ1
        light_call hc2 with v2 μ2 ⟨hv2,hm2⟩
        subst μ2
        light_set (f 2-2*f 1+f 0) using hv0,hv1,hv2
        exact ⟨by simp [inverseDigit],rfl⟩

end ThreeSum.LightTernaryFrozenQuery
