import Submission.ThreeSum.LightWantedSetup
import Submission.ThreeSum.RadixKeyLists

/-!
# Original positions joined to a literal ternary radix dictionary

This is the actual twelve-procedure residue/bucket/join program.  The
dictionary is a physical signed array produced by the radix constructor.
Its indices, including repeated key occurrences, remain distinct.  No
matching list, residue scan, or bucket table is supplied to the program.
-/

namespace ThreeSum.LightTernaryOriginalJoin

open Light

set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

def program : Program := LightWantedSetup.program

def keys (p : ℤ) (base : List ℤ) (J : ℕ) : List ℤ :=
  RadixKeyLists.values p base J

def joinCount (M : ℕ) (input : ℕ → ℤ) (NL : ℕ)
    (p : ℤ) (base : List ℤ) (J : ℕ) (shift : ℤ) : ℕ :=
  WantedResidueKeys.total M input (fun j => (keys p base J).getD j 0)
    NL (keys p base J).length shift

theorem joinCount_le_of_cap {M NL cap : ℕ} {input : ℕ → ℤ}
    {p : ℤ} {base : List ℤ} {J : ℕ} {shift : ℤ}
    (hcap : ∀ i < NL,
      LightHistogram.count
        (fun j => WantedResidueKeys.code M 0 ((keys p base J).getD j 0))
        (WantedResidueKeys.code M shift (input i)) (keys p base J).length ≤ cap) :
    joinCount M input NL p base J shift ≤ NL*cap := by
  unfold joinCount WantedResidueKeys.total
  induction NL with
  | zero => simp [WantedPairs.count]
  | succ n ih =>
    rw [WantedPairs.count_succ]
    have hn := hcap n (by omega)
    have hp := ih (fun i hi => hcap i (by omega))
    simpa only [Nat.add_mul,Nat.one_mul] using Nat.add_le_add hp hn

variable {lim : Limits}

theorem program_meets {μ : ℕ → ℤ} {src dict NL M free U D d J : ℕ}
    {p : ℤ} {base : List ℤ} {shift : ℤ} (input : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hM : 0 < M)
    (hsrc : src+NL ≤ free) (hdict : dict+(keys p base J).length ≤ free)
    (hspace : LightWantedSetup.space free M input
      (fun j => (keys p base J).getD j 0) NL (keys p base J).length U D shift ≤ lim.space)
    (hword : (LightSourceResidues.word M M U D : ℤ) ≤ lim.word)
    (hshift : |shift| ≤ (D : ℤ)) (hd : d+NL+5 ≤ lim.depth)
    (hinput : ∀ i < NL, μ (src+i)=input i)
    (hdictionary : Seg μ dict (keys p base J))
    (hvalues : ∀ i < NL, |input i| ≤ (U : ℤ))
    (hkeyBound : ∀ z ∈ keys p base J, |z| ≤ (U : ℤ)) :
    Meets lim program 11 d [src,dict,NL,(keys p base J).length,M,shift,free] μ
      (LightWantedSetup.time M input (fun j => (keys p base J).getD j 0)
        NL (keys p base J).length U D shift)
      (fun r ν => r=(free : ℤ) ∧
        LightWantedSetup.Output ν free M input
          (fun j => (keys p base J).getD j 0) NL (keys p base J).length shift ∧
        Kept μ ν free) := by
  apply LightWantedSetup.program_meets input (fun j => (keys p base J).getD j 0) hw hM hsrc hdict hspace hword hshift hd hinput
  · intro j hj
    simpa only [List.getD_eq_getElem (keys p base J) 0 hj] using hdictionary j hj
  · exact hvalues
  · intro j hj
    rw [List.getD_eq_getElem (keys p base J) 0 hj]
    exact hkeyBound _ (List.getElem_mem hj)

theorem time_bound_of_cap {M NL U D cap : ℕ} {input : ℕ → ℤ}
    {p : ℤ} {base : List ℤ} {J : ℕ} {shift : ℤ}
    (hcap : ∀ i < NL,
      LightHistogram.count
        (fun j => WantedResidueKeys.code M 0 ((keys p base J).getD j 0))
        (WantedResidueKeys.code M shift (input i)) (keys p base J).length ≤ cap) :
    LightWantedSetup.time M input (fun j => (keys p base J).getD j 0)
      NL (keys p base J).length U D shift ≤
      2000*(NL+base.length^J+M+NL*cap+1)*
        (Nat.log 2 (U+1)+Nat.log 2 (M+D+1)+1) := by
  have ht := LightWantedSetup.time_bound M input
    (fun j => (keys p base J).getD j 0) NL (keys p base J).length U D shift
  have hc := joinCount_le_of_cap hcap
  have hl : (keys p base J).length=base.length^J := RadixKeyLists.values_length p base J
  unfold joinCount at hc
  have hs : NL+(keys p base J).length+M+
      WantedResidueKeys.total M input (fun j => (keys p base J).getD j 0)
        NL (keys p base J).length shift+1 ≤
      NL+(keys p base J).length+M+NL*cap+1 := by omega
  have hm := Nat.mul_le_mul_left 2000 hs
  have hf := Nat.mul_le_mul_right
    (Nat.log 2 (U+1)+Nat.log 2 (M+D+1)+1) hm
  have he := ht.trans hf
  simpa only [hl] using he

end ThreeSum.LightTernaryOriginalJoin
