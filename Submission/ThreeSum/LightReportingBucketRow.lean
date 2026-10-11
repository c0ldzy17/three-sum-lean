import Submission.ThreeSum.LightHistogram

/-!
# Exact original-value testing of one retained physical bucket

The procedure visits the bucket's physical index array and reads the original
value at each index. It counts exact integer equalities with the supplied
target and preserves every memory cell. Equal values at distinct original
indices remain separate tests.
-/

namespace ThreeSum.LightReportingBucketRow

open Light Finset

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

def count (target : ℤ) (value : ℕ → ℤ) (index : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((range n).filter fun j => value (index j)=target).card

@[simp] theorem count_zero (target : ℤ) (value : ℕ → ℤ) (index : ℕ → ℕ) :
    count target value index 0 = 0 := by simp [count]

theorem count_le (target : ℤ) (value : ℕ → ℤ) (index : ℕ → ℕ) (n : ℕ) :
    count target value index n ≤ n :=
  (Finset.card_filter_le _ _).trans (by simp)

theorem count_succ (target : ℤ) (value : ℕ → ℤ) (index : ℕ → ℕ) (n : ℕ) :
    count target value index (n+1) = count target value index n +
      if value (index n)=target then 1 else 0 := by
  unfold count
  rw [Finset.range_add_one,Finset.filter_insert]
  by_cases he : value (index n)=target
  · rw [if_pos he,Finset.card_insert_of_notMem (by simp)]
    simp [he]
  · simp [he]

theorem count_pos_iff (target : ℤ) (value : ℕ → ℤ) (index : ℕ → ℕ) (n : ℕ) :
    0 < count target value index n ↔ ∃ j < n, value (index j)=target := by
  simp [count,Finset.card_pos,Finset.Nonempty]

def roundBody : Stmt :=
  .ite (M (v 1 +' M (v 2 +' v 6)) =' v 0)
    (.set 5 (v 5 +' k 1)) .skip

/-- Target value, original value array, retained physical indices, bucket
length, original value-array length. -/
def body : Stmt :=
  .set 5 (k 0) ;; .for 6 (v 3) roundBody ;; .set 0 (v 5)

def time (n : ℕ) : ℕ := 60*n+30
def program : Program := [body]

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {p src indices n N : ℕ} {μ : ℕ → ℤ}
    (hp : P[p]? = some body) (target : ℤ) (value : ℕ → ℤ) (index : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+N ≤ lim.space) (hindices : indices+n ≤ lim.space)
    (hindex : ∀ i < n, index i < N)
    (hreadI : ∀ i < n, μ (indices+i) = (index i : ℤ))
    (hreadV : ∀ i < N, μ (src+i) = value i)
    (hvalues : ∀ i < N, |value i| ≤ lim.word) (htarget : |target| ≤ lim.word) :
    Meets lim P p d [target,src,indices,n,N] μ (time n)
      (fun r ν => r=(count target value index n : ℤ) ∧ ν=μ) := by
  have ht := abs_le.mp htarget
  apply Meets.of_body hp
  unfold body time
  light_set (0 : ℕ)
  refine Ends.pieceThen (Ends.for (lim := lim) (P := P) (d := d) (i := 6) (hi := v 3)
    (body := roundBody) (T := 60*n+15)
    (Q := fun σ => σ=⟨frame [target,src,indices,n,N,count target value index n,n],μ⟩)
    (fun j σ => σ=⟨frame [target,src,indices,n,N,count target value index j,j],μ⟩)
    n 45 ?start ?round ?done ?bound (hT := by light_time)) ?after
  case start => simp [update_frame_setLocal]
  case round =>
    rintro j _ hj _ rfl
    have hidx := hindex j hj
    have hreadIdx := hreadI j hj
    have hreadVal := hreadV _ hidx
    have hv := abs_le.mp (hvalues _ hidx)
    have hcnt := count_le target value index j
    have hcntNext := count_le target value index (j+1)
    have hnext := count_succ target value index j
    unfold roundBody
    light_if hy hn : value (index j)=target using hreadIdx,hreadVal
    · have he : count target value index (j+1)=count target value index j+1 := by
        simpa only [hy,ite_true] using hnext
      light_set (count target value index (j+1) : ℕ) using he
      simp [update_frame_setLocal]
    · have he : count target value index (j+1)=count target value index j := by
        simpa only [hn,ite_false,Nat.add_zero] using hnext
      light_skip
      simp [update_frame_setLocal,he]
  case done => intro σ _ hs; exact hs
  case bound => rintro j _ hj _ rfl; light_side
  case after =>
    rintro _ rfl
    have hc := count_le target value index n
    light_set (count target value index n : ℕ)
    exact ⟨rfl,rfl⟩

theorem program_meets {src indices n N : ℕ} {μ : ℕ → ℤ}
    (target : ℤ) (value : ℕ → ℤ) (index : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+N ≤ lim.space) (hindices : indices+n ≤ lim.space)
    (hindex : ∀ i < n, index i < N)
    (hreadI : ∀ i < n, μ (indices+i) = (index i : ℤ))
    (hreadV : ∀ i < N, μ (src+i) = value i)
    (hvalues : ∀ i < N, |value i| ≤ lim.word) (htarget : |target| ≤ lim.word) :
    Meets lim program 0 d [target,src,indices,n,N] μ (time n)
      (fun r ν => r=(count target value index n : ℤ) ∧ ν=μ) :=
  meets rfl target value index hw hsrc hindices hindex hreadI hreadV hvalues htarget

end ThreeSum.LightReportingBucketRow
