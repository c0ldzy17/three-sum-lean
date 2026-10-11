import Submission.ThreeSum.LightSortedBands

/-!
# Running the owner tables directly from constructed class headers

This wrapper reads the three stored distinct-value lengths and band counts.
All six endpoint pointers and all three counts passed to the owner-table
program are therefore obtained by actual RAM expressions.
-/

namespace ThreeSum.LightHeaderBands

open Light ThreeSum.BandEnumeration

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

variable {lim : Limits} {P : Program}

def At (μ : ℕ → ℤ) (header n : ℕ) (A : Family) : Prop :=
  μ header = (n : ℤ) ∧ μ (header+1) = (A.size : ℤ) ∧
    LightBandEnumeration.At μ (header+2) (header+2+n) A

/-- Arguments: three endpoint-header addresses and output address. -/
def body (pEnumerate : ℕ) : Stmt :=
  .call pEnumerate
    [v 0 +' k 2,v 0 +' k 2 +' M (v 0),
      v 1 +' k 2,v 1 +' k 2 +' M (v 1),
      v 2 +' k 2,v 2 +' k 2 +' M (v 2),
      M (v 0 +' k 1),M (v 1 +' k 1),M (v 2 +' k 1),v 3] 0

def time (a b c : ℕ) : ℕ := LightBandEnumeration.time a b c+100

structure Procs (P : Program) (pMain : ℕ) where
  pEnumerate : ℕ
  enumerate : LightBandEnumeration.Procs P pEnumerate
  main : P[pMain]? = some (body pEnumerate)

theorem Procs.meets {pMain a b c nA nB nC dst U d : ℕ} {μ : ℕ → ℤ}
    (R : Procs P pMain) (A B C : Family)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+2+nA+A.size ≤ dst) (hb : b+2+nB+B.size ≤ dst)
    (hc : c+2+nC+C.size ≤ dst)
    (hspace : LightBandEnumeration.space dst A.size B.size C.size ≤ lim.space)
    (hword : (LightBandEnumeration.word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d+LightBandEnumeration.width A.size B.size C.size+5 ≤ lim.depth)
    (hA : At μ a nA A) (hB : At μ b nB B) (hC : At μ c nC C)
    (hAU : LightBandEnumeration.Bounded A U) (hBU : LightBandEnumeration.Bounded B U)
    (hCU : LightBandEnumeration.Bounded C U) :
    Meets lim P pMain d [a,b,c,dst] μ (time A.size B.size C.size)
      (fun r μ' => r = (LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
        LightBandEnumeration.Tables μ' dst A B C ∧ Kept μ μ' dst) := by
  obtain ⟨han,has,hA⟩ := hA
  obtain ⟨hbn,hbs,hB⟩ := hB
  obtain ⟨hcn,hcs,hC⟩ := hC
  have hspace' : dst+LightBandEnumeration.count A.size B.size C.size+
      LightBandEnumeration.width A.size B.size C.size+1 ≤ lim.space := hspace
  apply Meets.of_body R.main
  unfold body time
  light_call (R.enumerate.meets (d := d+1) A B C hw
    (by omega) ha (by omega) hb (by omega) hc hspace hword (by omega) hA hB hC hAU hBU hCU)
    using han,has,hbn,hbs,hcn,hcs,LightBandEnumeration.time
    with result μ' hresult
  exact hresult

def program : Program :=
  [body 1,LightBandEnumeration.body 2 3 4,clog2Body,powTableBody,
    LightBandTable.body 5,LightBandTable.rowBody 6,LightBandLookup.body 7,LightBandLookup.searchBody 7]

def program_procs : Procs program 0 :=
  ⟨1,⟨2,3,4,5,6,7,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩

theorem program_meets {a b c nA nB nC dst U d : ℕ} {μ : ℕ → ℤ}
    (A B C : Family) (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+2+nA+A.size ≤ dst) (hb : b+2+nB+B.size ≤ dst)
    (hc : c+2+nC+C.size ≤ dst)
    (hspace : LightBandEnumeration.space dst A.size B.size C.size ≤ lim.space)
    (hword : (LightBandEnumeration.word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d+LightBandEnumeration.width A.size B.size C.size+5 ≤ lim.depth)
    (hA : At μ a nA A) (hB : At μ b nB B) (hC : At μ c nC C)
    (hAU : LightBandEnumeration.Bounded A U) (hBU : LightBandEnumeration.Bounded B U)
    (hCU : LightBandEnumeration.Bounded C U) :
    Meets lim program 0 d [a,b,c,dst] μ (time A.size B.size C.size)
      (fun r μ' => r = (LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
        LightBandEnumeration.Tables μ' dst A B C ∧ Kept μ μ' dst) :=
  program_procs.meets A B C hw ha hb hc hspace hword hd hA hB hC hAU hBU hCU

end ThreeSum.LightHeaderBands
