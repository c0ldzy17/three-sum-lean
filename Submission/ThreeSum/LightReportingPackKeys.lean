import Submission.ThreeSum.ReportingHostPackedCatalog
import Submission.ThreeSum.LightArray

/-! # The actual linear pass that packs prefix keys and original catalog indices -/

namespace ThreeSum.LightReportingPackKeys

open Light LightArray ReportingHostPackedCatalog

variable {lim : Limits} {P : Program} {d : ℕ}

def body : Stmt :=
  pass 5 (v 2) (v 4)
    (((M (v 0 +' v 5) +' v 3 *' M (v 1 +' v 5)) *' (v 2 +' k 1)) +' v 5)

def time (n : ℕ) : ℕ := 50*n+10

def word (radix n : ℕ) : ℕ := radix^2*(n+1)+n+radix+2

theorem meets {p inL inR n radix dst : ℕ} {μ : ℕ → ℤ}
    (hp : P[p]? = some body) (left right : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hleft : inL+n ≤ dst) (hright : inR+n ≤ dst) (hdst : dst+n ≤ lim.space)
    (hword : (word radix n : ℤ) ≤ lim.word)
    (hreadL : ∀ i < n, μ (inL+i) = (left i : ℤ))
    (hreadR : ∀ i < n, μ (inR+i) = (right i : ℤ))
    (hboundL : ∀ i < n, left i < radix) (hboundR : ∀ i < n, right i < radix) :
    Meets lim P p d [inL,inR,n,radix,dst] μ (time n)
      (fun _ μ' => Seg μ' dst (codes (fun i => pairKey radix (left i) (right i)) n) ∧
        SameOutside μ μ' dst n) := by
  have hnWord : ((n+1 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega : n+1 ≤ word radix n)).trans hword
  have hsepL : SourceSafe inL dst n := Or.inr (Or.inl hleft)
  have hsepR : SourceSafe inR dst n := Or.inr (Or.inl hright)
  refine .of_body hp (Ends.pass
    (fun i => (packed (fun j => pairKey radix (left j) (right j)) n i : ℤ))
    (fun i hi => ?_) ⟨?_,by light_keep⟩ hw hdst rfl rfl (hT := by light_time [time]))
  · have hrL := source_read (μ := μ)
      (f := fun i => (packed (fun j => pairKey radix (left j) (right j)) n i : ℤ)) hsepL hi
    have hrR := source_read (μ := μ)
      (f := fun i => (packed (fun j => pairKey radix (left j) (right j)) n i : ℤ)) hsepR hi
    have hb := pairKey_lt (hboundL i hi) (hboundR i hi)
    have hf := packed_lt (key := fun j => pairKey radix (left j) (right j)) hi hb
    simp only [packed,pairKey,Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hrL hrR
    have hmN : radix*right i ≤ word radix n := by unfold pairKey at hb; unfold word; nlinarith
    have hkN : pairKey radix (left i) (right i) ≤ word radix n := by unfold word; nlinarith
    have hpN : pairKey radix (left i) (right i)*(n+1) ≤ word radix n := by
      simp only [packed] at hf
      unfold word
      omega
    have hfN : packed (fun j => pairKey radix (left j) (right j)) n i ≤ word radix n := by
      unfold word
      omega
    have hmZ : (radix : ℤ)*(right i : ℤ) ≤ lim.word := (by exact_mod_cast hmN :
      (radix : ℤ)*(right i : ℤ) ≤ (word radix n : ℤ)).trans hword
    have hkZ : (left i : ℤ)+(radix : ℤ)*(right i : ℤ) ≤ lim.word := (by exact_mod_cast hkN :
      (left i : ℤ)+(radix : ℤ)*(right i : ℤ) ≤ (word radix n : ℤ)).trans hword
    have hpZ : ((left i : ℤ)+(radix : ℤ)*(right i : ℤ))*((n : ℤ)+1) ≤ lim.word :=
      (by exact_mod_cast hpN :
        ((left i : ℤ)+(radix : ℤ)*(right i : ℤ))*((n : ℤ)+1) ≤ (word radix n : ℤ)).trans hword
    have hfZ : ((left i : ℤ)+(radix : ℤ)*(right i : ℤ))*((n : ℤ)+1)+(i : ℤ) ≤ lim.word :=
      (by exact_mod_cast hfN :
        ((left i : ℤ)+(radix : ℤ)*(right i : ℤ))*((n : ℤ)+1)+(i : ℤ) ≤ (word radix n : ℤ)).trans hword
    have hm0 : 0 ≤ (radix : ℤ)*(right i : ℤ) := by positivity
    have hp0 : 0 ≤ ((left i : ℤ)+(radix : ℤ)*(right i : ℤ))*((n : ℤ)+1) := by positivity
    light_side [hrL,hrR,hreadL i hi,hreadR i hi,packed,pairKey]
  · intro i hi
    have hi' : i < n := by simpa only [codes,List.length_ofFn] using hi
    simpa only [codes,List.getElem_ofFn] using
      (wrote_done (μ := μ) (dst := dst)
        (f := fun i => (packed (fun j => pairKey radix (left j) (right j)) n i : ℤ)) hi')

def program : Program := [body]

theorem program_meets {inL inR n radix dst : ℕ} {μ : ℕ → ℤ}
    (left right : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hleft : inL+n ≤ dst) (hright : inR+n ≤ dst) (hdst : dst+n ≤ lim.space)
    (hword : (word radix n : ℤ) ≤ lim.word)
    (hreadL : ∀ i < n, μ (inL+i) = (left i : ℤ))
    (hreadR : ∀ i < n, μ (inR+i) = (right i : ℤ))
    (hboundL : ∀ i < n, left i < radix) (hboundR : ∀ i < n, right i < radix) :
    Meets lim program 0 d [inL,inR,n,radix,dst] μ (time n)
      (fun _ μ' => Seg μ' dst (codes (fun i => pairKey radix (left i) (right i)) n) ∧
        SameOutside μ μ' dst n) :=
  meets rfl left right hw hleft hright hdst hword hreadL hreadR hboundL hboundR

end ThreeSum.LightReportingPackKeys
