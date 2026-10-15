import Submission.ThreeSum.LightTernaryBankAssembly

/-! Explicit polynomial overhead and linear bank layout for the concrete
seventeen-procedure bank assembler. -/
namespace ThreeSum.LightTernaryBankCoordinate

theorem time_bound (N L n : ℕ) : time N L n≤3000*(N+L+1)*(n+1) := by
  have hm := LightTernaryMetadata.time_bound (2*N) n
  have hp := LightTernaryPass.time_bound L n
  unfold time
  nlinarith only [hm,hp]

end ThreeSum.LightTernaryBankCoordinate

namespace ThreeSum.LightTernaryBankSweep

theorem time_bound (N L n : ℕ) : time N L n≤4000*(N+1)*(N+L+1)*(n+1) := by
  have hc := LightTernaryBankCoordinate.time_bound N L n
  have hm := Nat.mul_le_mul_left N hc
  unfold time
  nlinarith only [hm]

end ThreeSum.LightTernaryBankSweep

namespace ThreeSum.LightTernaryBankAssembly

theorem time_bound (N L n : ℕ) : time N L n≤20000*(N+1)*(N+L+1)*(n+1) := by
  have hs := LightTernaryBankSweep.time_bound N L n
  have hscale : n+1≤(N+1)*(N+L+1)*(n+1) := by
    have hpos : 1≤(N+1)*(N+L+1) := Nat.succ_le_of_lt (by positivity)
    simpa using Nat.mul_le_mul_right (n+1) hpos
  unfold time LightTernaryProduct.time
  nlinarith only [hs,hscale]

def keyBase (a n : ℕ) : ℕ := a+n
def powersBase (a n : ℕ) : ℕ := keyBase a n+4*n
def fBase (a n N : ℕ) : ℕ := powersBase a n+(2*N+1)
def gBase (a n N : ℕ) : ℕ := fBase a n N+(N+1)*n
def hBase (a n N : ℕ) : ℕ := gBase a n N+(N+1)*n
def space (a n N : ℕ) : ℕ :=hBase a n N+(N+1)*n

theorem space_eq (a n N : ℕ) : space a n N=a+(3*N+8)*n+2*N+1 := by
  unfold space hBase gBase fBase powersBase keyBase
  ring

theorem layout (a n N : ℕ) :
    a+n≤keyBase a n ∧ keyBase a n+4*n≤powersBase a n ∧
    powersBase a n+(2*N+1)≤fBase a n N ∧
    fBase a n N+(N+1)*n≤gBase a n N ∧
    gBase a n N+(N+1)*n≤hBase a n N ∧
    hBase a n N+(N+1)*n≤space a n N := by
  exact ⟨le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl⟩

def word (a n N V : ℕ) : ℕ :=space a n N+n+2^(2*N+1)+2*N+
  4*(4^N*V)+4*(4^N*valueBound N V)+valueBound N V+100

def depth (d N L : ℕ) : ℕ := d+2*N+L+6

theorem word_bounds (a n N V : ℕ) :
    space a n N≤word a n N V ∧ n+2^(2*N+1)+16≤word a n N V ∧
    2*N+3≤word a n N V ∧ 4*(4^N*V)+3≤word a n N V ∧
    valueBound N V≤word a n N V ∧ 4*(4^N*valueBound N V)+3≤word a n N V := by
  unfold word
  generalize 2^(2*N+1)=p
  generalize 4^N=q
  generalize valueBound N V=b
  omega

end ThreeSum.LightTernaryBankAssembly
