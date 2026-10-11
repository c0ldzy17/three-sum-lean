import Submission.ThreeSum.RadixKeyLists
import Submission.ThreeSum.LightReportingAffine

/-!
# Costed Cartesian rows for positional keys

For every local key, an actual affine scan writes one entire row of extended
keys. The arrays contain the complete product list, including equal integer
keys attached to different original records. No division or decoding loop is
used to locate Cartesian coordinates at runtime.
-/

namespace ThreeSum.LightRadixRows

open Light RadixKeyLists

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

def body (pAffine : ℕ) : Stmt :=
  .for 6 (v 3)
    (.call pAffine [v 1,v 2 +' v 6 *' v 4,v 4,M (v 0 +' v 6),v 5] 7)

def time (m n : ℕ) : ℕ := m*(LightReportingAffine.time n+100)+20
def word (p U V : ℕ) : ℕ := U+p*V+p+1

def Inv (μ : ℕ → ℤ) (srcBase srcPrev dst p : ℕ) (base prev : List ℤ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [srcBase,srcPrev,dst,base.length,prev.length,p,j,r],ν⟩ ∧
    Seg ν dst (step (p : ℤ) (base.take j) prev) ∧
    SameOutside μ ν dst (base.length*prev.length)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pAffine srcBase srcPrev dst p U V : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some (body pAffine))
    (haffine : P[pAffine]? = some LightReportingAffine.body)
    (base prev : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hbaseEnd : srcBase+base.length ≤ dst) (hprevEnd : srcPrev+prev.length ≤ dst)
    (hspace : dst+base.length*prev.length ≤ lim.space)
    (hword : (word p U V : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hbaseRead : Seg μ srcBase base) (hprevRead : Seg μ srcPrev prev)
    (hbaseBound : ∀ x ∈ base, |x| ≤ (U : ℤ))
    (hprevBound : ∀ y ∈ prev, |y| ≤ (V : ℤ)) :
    Meets lim P pMain d [srcBase,srcPrev,dst,base.length,prev.length,p] μ
      (time base.length prev.length)
      (fun _ ν => Seg ν dst (step (p : ℤ) base prev) ∧
        SameOutside μ ν dst (base.length*prev.length)) := by
  have hbudget (n : ℕ) (hn : n ≤ word p U V) : (n : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hn).trans hword
  have hpWord := hbudget p (by unfold word; omega)
  have hsumWord := hbudget (U+p*V) (by unfold word; omega)
  have hmulWord := hbudget (p*V) (by unfold word; omega)
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ srcBase srcPrev dst p base prev) base.length
    (LightReportingAffine.time prev.length+75) ?start ?round ?done ?bound
    (hT := by light_time)
  case start =>
    refine ⟨0,μ,?_,?_,SameOutside.refl⟩
    · simp [update_frame_setLocal]
      change frame [(srcBase : ℤ),srcPrev,dst,base.length,prev.length,p,0] =
        frame ([(srcBase : ℤ),srcPrev,dst,base.length,prev.length,p,0] ++ [0])
      exact (frame_append_zeros _ 1).symm
    · simp [step]
  case round =>
    rintro j _ hj _ ⟨r,ν,rfl,hout,hkeep⟩
    have hend : j*prev.length+prev.length ≤ base.length*prev.length := by
      calc
        j*prev.length+prev.length = (j+1)*prev.length := by ring
        _ ≤ base.length*prev.length := Nat.mul_le_mul_right prev.length (by omega)
    have hjProd : (j : ℤ)*(prev.length : ℤ) ≤ lim.word := by
      have hh : j*prev.length ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (j : ℤ)*(prev.length : ℤ) ≤ lim.space).trans hw
    have hrowAddr : (dst : ℤ)+(j : ℤ)*(prev.length : ℤ) ≤ lim.word := by
      have hh : dst+j*prev.length ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (dst : ℤ)+(j : ℤ)*(prev.length : ℤ) ≤ lim.space).trans hw
    have hreadBase : ν (srcBase+j)=base[j] :=
      (hkeep _ (Or.inl (by omega))).trans (hbaseRead j hj)
    have hreadPrev (i : ℕ) (hi : i < prev.length) : ν (srcPrev+i)=prev[i] :=
      (hkeep _ (Or.inl (by omega))).trans (hprevRead i hi)
    have hkey := hbaseBound _ (List.getElem_mem hj)
    have hmul : ∀ i < prev.length, |(p : ℤ)*ν (srcPrev+i)| ≤ lim.word := by
      intro i hi
      rw [hreadPrev i hi,abs_mul,Int.abs_natCast]
      exact (mul_le_mul_of_nonneg_left (hprevBound _ (List.getElem_mem hi))
        (Int.natCast_nonneg _)).trans (by simpa only [Nat.cast_mul] using hmulWord)
    have hsum : ∀ i < prev.length, |base[j]+(p : ℤ)*ν (srcPrev+i)| ≤ lim.word := by
      intro i hi
      have hv : |(p : ℤ)*ν (srcPrev+i)| ≤ (p : ℤ)*V := by
        rw [hreadPrev i hi,abs_mul,Int.abs_natCast]
        exact mul_le_mul_of_nonneg_left (hprevBound _ (List.getElem_mem hi))
          (Int.natCast_nonneg _)
      exact (abs_add_le _ _).trans ((add_le_add hkey hv).trans
        (by simpa only [Nat.cast_add,Nat.cast_mul] using hsumWord))
    have hc := LightReportingAffine.meets (d := d+1) (src := srcPrev)
      (dst := dst+j*prev.length) (n := prev.length) (b := base[j]) (c := (p : ℤ))
      haffine hw (by omega) (by omega) (Or.inr (Or.inl (by omega))) hmul hsum
    light_call hc using hreadBase,LightReportingAffine.time with result ν₁ ⟨hrow,hrowKeep⟩
    refine ⟨by simp,result,ν₁,by simp [update_frame_setLocal],?_,?_⟩
    · rw [step_take_succ _ _ _ hj]
      have hlen : (step (p : ℤ) (base.take j) prev).length=j*prev.length := by
        rw [step_length,List.length_take,min_eq_left (Nat.le_of_lt hj)]
      apply seg_append.mpr
      constructor
      · exact hout.of_sameOutside hrowKeep (Or.inl (by rw [hlen]))
      · rw [hlen]
        intro i hi
        have hi' : i < prev.length := by simpa only [List.length_map] using hi
        rw [List.getElem_map,hrow i hi',hreadPrev i hi']
    · intro a ha
      exact (hrowKeep a (by omega)).trans (hkeep a ha)
  case done =>
    rintro _ _ ⟨r,ν,rfl,hout,hkeep⟩
    exact ⟨by simpa only [List.take_length] using hout,hkeep⟩
  case bound =>
    rintro j _ hj _ ⟨r,ν,rfl,_,_⟩
    light_side

def program : Program := [body 1,LightReportingAffine.body]

theorem program_meets {srcBase srcPrev dst p U V : ℕ} {μ : ℕ → ℤ}
    (base prev : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hbaseEnd : srcBase+base.length ≤ dst) (hprevEnd : srcPrev+prev.length ≤ dst)
    (hspace : dst+base.length*prev.length ≤ lim.space)
    (hword : (word p U V : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hbaseRead : Seg μ srcBase base) (hprevRead : Seg μ srcPrev prev)
    (hbaseBound : ∀ x ∈ base, |x| ≤ (U : ℤ))
    (hprevBound : ∀ y ∈ prev, |y| ≤ (V : ℤ)) :
    Meets lim program 0 d [srcBase,srcPrev,dst,base.length,prev.length,p] μ
      (time base.length prev.length)
      (fun _ ν => Seg ν dst (step (p : ℤ) base prev) ∧
        SameOutside μ ν dst (base.length*prev.length)) :=
  meets rfl rfl base prev hw hbaseEnd hprevEnd hspace hword hd hbaseRead hprevRead
    hbaseBound hprevBound

theorem time_bound (m n : ℕ) : time m n ≤ 130*(m+1)*(n+1) := by
  unfold time LightReportingAffine.time
  nlinarith

theorem time_bound_product (m n : ℕ) (hn : 0 < n) : time m n ≤ 130*m*n+20 := by
  unfold time LightReportingAffine.time
  have hmn : m ≤ m*n := Nat.le_mul_of_pos_right m hn
  nlinarith

end ThreeSum.LightRadixRows
