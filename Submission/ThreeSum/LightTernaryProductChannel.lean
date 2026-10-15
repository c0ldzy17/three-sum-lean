import Submission.ThreeSum.LightArray
import Submission.ThreeSum.TernaryWeightChannels

/-! Actual two-coordinate source channels for the fourth mixed tensor. -/
namespace ThreeSum.LightTernaryProductChannel
open Light TernaryWeightChannels

def body : Stmt := pass 6 (v 1) (v 5)
  (M (v 0 +' v 6 *' v 2 +' v 3) *' M (v 0 +' v 6 *' v 2 +' v 4))
def time (n : ℕ) : ℕ := 40*n+10

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {p src n width a b dst U : ℕ}
    (hmain : P[p]?=some body) (μ : ℕ→ℤ) (F : ℕ→ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (ha : a<width) (hb : b<width)
    (hsrc : src+n*width≤dst) (hdst : dst+n≤lim.space)
    (hread : ∀ i<n, ∀ j<width, μ (src+i*width+j)=F i j)
    (hf : ∀ i<n, ∀ j<width, |F i j|≤(U : ℤ))
    (hword : ((U : ℤ)+1)^2≤lim.word) :
    Meets lim P p d [src,n,width,a,b,dst] μ (time n)
      (fun _ ν => (∀ i<n, ν (dst+i)=F i a*F i b) ∧ SameOutside μ ν dst n) := by
  have hU : (U : ℤ)≤lim.word := by
    have hu : (0 : ℤ)≤U := by positivity
    nlinarith
  apply Meets.of_body hmain
  unfold body time
  refine Ends.pass (fun i => F i a*F i b) ?round
    ⟨fun i hi => by dsimp only; exact wrote_done hi,by light_keep⟩ hw hdst rfl rfl
  case round =>
    intro i hi
    have hm := Nat.mul_le_mul_right width (show i+1≤n by omega)
    simp only [Nat.add_mul,one_mul] at hm
    have hlowA : src+i*width+a<dst := by omega
    have hlowB : src+i*width+b<dst := by omega
    have hrA : wrote μ dst (fun i => F i a*F i b) i (src+i*width+a)=F i a :=
      (wrote_rest (Or.inl hlowA)).trans (hread i hi a ha)
    have hrB : wrote μ dst (fun i => F i a*F i b) i (src+i*width+b)=F i b :=
      (wrote_rest (Or.inl hlowB)).trans (hread i hi b hb)
    have hwidth : width≤lim.space := by omega
    have hwidthW : (width : ℤ)≤lim.word := (Int.ofNat_le.mpr hwidth).trans hw
    have hmulW : (i : ℤ)*(width : ℤ)≤lim.word := by
      have hh : i*width≤lim.space := by omega
      have hhZ : (i : ℤ)*(width : ℤ)≤(lim.space : ℤ) := by exact_mod_cast hh
      exact hhZ.trans hw
    have hA := abs_le.mp (hf i hi a ha)
    have hB := abs_le.mp (hf i hi b hb)
    have hprod : |F i a*F i b|≤lim.word := by
      rw [abs_mul]
      have hh := mul_le_mul (hf i hi a ha) (hf i hi b hb) (abs_nonneg _) (Int.natCast_nonneg U)
      exact hh.trans (by nlinarith [Int.natCast_nonneg U])
    have hprod' := abs_le.mp hprod
    have haddrA : ((src : ℤ)+(i : ℤ)*(width : ℤ)+(a : ℤ)).toNat=src+i*width+a := by norm_cast
    have haddrB : ((src : ℤ)+(i : ℤ)*(width : ℤ)+(b : ℤ)).toNat=src+i*width+b := by norm_cast
    light_side [hrA,hrB,haddrA,haddrB]

def program : Program := [body]

end ThreeSum.LightTernaryProductChannel
