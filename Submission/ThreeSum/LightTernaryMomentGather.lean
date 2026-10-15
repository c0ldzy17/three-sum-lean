import Submission.ThreeSum.LightArray

/-! Actual column gathering from the channel-major wanted-query matrix. -/
namespace ThreeSum.LightTernaryMomentGather
open Light

/-- Arguments: matrix, wanted-count, wanted-row, scratch, moment-count. -/
def body : Stmt := pass 5 (v 4) (v 3) (M (v 0 +' v 5 *' v 1 +' v 2))
def time (terms : ℕ) : ℕ := 30*terms+10

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {p matrix count row scratch terms U : ℕ}
    (hmain : P[p]?=some body) (μ : ℕ→ℤ) (M : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hr : row<count)
    (hbefore : matrix+terms*count≤scratch) (hspace : scratch+terms≤lim.space)
    (hread : ∀ k<terms, μ (matrix+k*count+row)=M k)
    (hbound : ∀ k<terms, |M k|≤(U : ℤ)) (hword : (U : ℤ)≤lim.word) :
    Meets lim P p d [matrix,count,row,scratch,terms] μ (time terms)
      (fun _ ν => (∀ k<terms, ν (scratch+k)=M k) ∧ SameOutside μ ν scratch terms) := by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.pass M ?round
    ⟨fun k hk => by dsimp only; exact wrote_done hk,by light_keep⟩ hw hspace rfl rfl
  case round =>
    intro k hk
    have hm := Nat.mul_le_mul_right count (show k+1≤terms by omega)
    simp only [Nat.add_mul,one_mul] at hm
    have haddr : matrix+k*count+row<scratch := by omega
    have hcur : wrote μ scratch M k (matrix+k*count+row)=M k :=
      (wrote_rest (Or.inl haddr)).trans (hread k hk)
    have hC : (count : ℤ)≤lim.word := by
      have hh : count≤lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have hmul : (k : ℤ)*(count : ℤ)≤lim.word := by
      have hh : k*count≤lim.space := by omega
      have hhZ : (k : ℤ)*(count : ℤ)≤(lim.space : ℤ) := by exact_mod_cast hh
      exact hhZ.trans hw
    have hval := abs_le.mp (hbound k hk)
    have hnat : ((matrix : ℤ)+(k : ℤ)*(count : ℤ)+(row : ℤ)).toNat=matrix+k*count+row := by norm_cast
    light_side [hcur,hnat]

def program : Program := [body]

end ThreeSum.LightTernaryMomentGather
