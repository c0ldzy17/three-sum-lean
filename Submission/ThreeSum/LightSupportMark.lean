import Submission.ThreeSum.LightArray
import Mathlib.Data.Finset.Range

/-!
# A Boolean support table with repeated keys

The routine clears the destination, then marks a key only when its validity
flag is one. Repeated retained representations set the same bit; this is
the support operation needed for a local hash-cover row.
-/

namespace ThreeSum.LightSupportMark

open Light Finset

def Hit (key valid : ℕ → ℕ) (r i : ℕ) : Prop :=
  ∃ j ∈ range i, valid j = 1 ∧ key j = r

instance (key valid : ℕ → ℕ) (r i : ℕ) : Decidable (Hit key valid r i) := by
  unfold Hit
  infer_instance

def bit (key valid : ℕ → ℕ) (r i : ℕ) : ℕ := if Hit key valid r i then 1 else 0

theorem bit_zero (key valid : ℕ → ℕ) (r : ℕ) : bit key valid r 0 = 0 := by
  simp [bit,Hit]

theorem hit_succ (key valid : ℕ → ℕ) (r i : ℕ) :
    Hit key valid r (i+1) ↔ Hit key valid r i ∨ (valid i=1 ∧ key i=r) := by
  simp only [Hit,mem_range]
  constructor
  · rintro ⟨j,hj,hv,hk⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact Or.inl ⟨j,hj,hv,hk⟩
    · exact Or.inr ⟨hv,hk⟩
  · rintro (⟨j,hj,hv,hk⟩ | ⟨hv,hk⟩)
    · exact ⟨j,by omega,hv,hk⟩
    · exact ⟨i,by omega,hv,hk⟩

theorem bit_succ_of_hit (key valid : ℕ → ℕ) (r i : ℕ)
    (hv : valid i=1) (hk : key i=r) : bit key valid r (i+1) = 1 :=
  if_pos ((hit_succ key valid r i).mpr (Or.inr ⟨hv,hk⟩))

theorem bit_succ_of_not (key valid : ℕ → ℕ) (r i : ℕ)
    (h : ¬(valid i=1 ∧ key i=r)) : bit key valid r (i+1) = bit key valid r i := by
  unfold bit
  by_cases hh : Hit key valid r i
  · have hn : Hit key valid r (i+1) := (hit_succ key valid r i).mpr (Or.inl hh)
    simp only [if_pos hh,if_pos hn]
  · have hn : ¬Hit key valid r (i+1) := by
      intro hi
      rcases (hit_succ key valid r i).mp hi with hi | hi
      · exact hh hi
      · exact h hi
    simp only [if_neg hh,if_neg hn]

def markBody : Stmt :=
  .for 5 (v 3) (
    .ite (M (v 1 +' v 5) =' k 1)
      (.store (v 2 +' M (v 0 +' v 5)) (k 1)) .skip)

def markTime (n : ℕ) : ℕ := 40*n+6

variable {lim : Limits} {P : Program} {d : ℕ}

theorem mark_ends {μ : ℕ → ℤ} {loc : ℕ → ℤ} {keys flags dst n p : ℕ}
    (key valid : ℕ → ℕ)
    (hkeysLoc : loc 0=keys) (hflagsLoc : loc 1=flags) (hdstLoc : loc 2=dst) (hlen : loc 3=n)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hK : keys+n ≤ lim.space) (hF : flags+n ≤ lim.space) (hD : dst+p ≤ lim.space)
    (hsepK : Apart keys n dst p) (hsepF : Apart flags n dst p)
    (hkeys : ∀ i < n, μ (keys+i) = (key i : ℤ))
    (hflags : ∀ i < n, μ (flags+i) = (valid i : ℤ))
    (hkeyLt : ∀ i < n, key i < p)
    (hzero : ∀ r < p, μ (dst+r)=0) (hword : (1 : ℤ) ≤ lim.word) :
    Ends lim P d markBody ⟨loc,μ⟩ (markTime n)
      (fun σ' => (∀ r < p, σ'.mem (dst+r) = (bit key valid r n : ℤ)) ∧
        SameOutside μ σ'.mem dst p) := by
  let Inv := fun i (μ' : ℕ → ℤ) =>
    (∀ r < p, μ' (dst+r) = (bit key valid r i : ℤ)) ∧ SameOutside μ μ' dst p
  unfold markBody
  apply Ends.forMem Inv n 32 (hn := by omega) (hT := by unfold markTime; light_time)
  · exact ⟨by simpa only [bit_zero,Nat.cast_zero] using hzero,SameOutside.refl⟩
  · intro i μ' hi hI
    obtain ⟨hbits,hsame⟩ := hI
    have hk := hkeyLt i hi
    have hkr : μ' (keys+i) = (key i : ℤ) := (hsame _ (by omega)).trans (hkeys i hi)
    have hfr : μ' (flags+i) = (valid i : ℤ) := (hsame _ (by omega)).trans (hflags i hi)
    refine Ends.iteLast (fun hc => ?_) (fun hc => ?_)
      (by light_side [hflagsLoc,hfr])
    · have hv : valid i=1 := by simpa [hflagsLoc,hfr] using hc
      have ha : (v 2 +' M (v 0 +' v 5)).val ⟨Function.update loc 5 (i : ℤ),μ'⟩ =
          ((dst+key i : ℕ) : ℤ) := by light_side [hkeysLoc,hdstLoc,hkr]
      refine Ends.storeLast ?_ (by light_side [hkeysLoc,hdstLoc,hkr]) (by light_time)
      change Function.update loc 5 (i : ℤ) = Function.update loc 5 (i : ℤ) ∧
        Inv (i+1) (Function.update μ' ((v 2 +' M (v 0 +' v 5)).val
          ⟨Function.update loc 5 (i : ℤ),μ'⟩).toNat 1)
      rw [ha,Int.toNat_natCast]
      refine ⟨rfl,?_,hsame.update ⟨by omega,by omega⟩ 1⟩
      intro r hr
      by_cases he : key i=r
      · subst r
        rw [bit_succ_of_hit key valid (key i) i hv rfl]
        simp
      · rw [Function.update_of_ne (by omega),hbits r hr]
        rw [bit_succ_of_not key valid r i (by tauto)]
    · have hv : valid i≠1 := by simpa [hflagsLoc,hfr] using hc
      apply Ends.skip
      refine ⟨rfl,?_,hsame⟩
      intro r hr
      rw [bit_succ_of_not key valid r i (by tauto)]
      exact hbits r hr
  · intro μ' hI
    exact hI
  · intro i μ' hi hI
    simp [hlen]

def body (pFill : ℕ) : Stmt :=
  .call pFill [v 2,v 4,k 0] 6 ;; markBody

def time (n p : ℕ) : ℕ := fillTime p+markTime n+10

theorem meets {pMain pFill : ℕ}
    (hmain : P[pMain]? = some (body pFill)) (hfill : P[pFill]? = some fillBody)
    {μ : ℕ → ℤ} {keys flags dst n p : ℕ}
    (key valid : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hK : keys+n ≤ lim.space) (hF : flags+n ≤ lim.space) (hD : dst+p ≤ lim.space)
    (hsepK : Apart keys n dst p) (hsepF : Apart flags n dst p)
    (hkeys : ∀ i < n, μ (keys+i) = (key i : ℤ))
    (hflags : ∀ i < n, μ (flags+i) = (valid i : ℤ))
    (hkeyLt : ∀ i < n, key i < p) (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P pMain d [keys,flags,dst,n,p] μ (time n p)
      (fun _ μ' => (∀ r < p, μ' (dst+r) = (bit key valid r n : ℤ)) ∧
        SameOutside μ μ' dst p) := by
  apply Meets.of_body hmain
  unfold body time
  light_call (fill_meets (d := d+1) (μ := μ) (dst := dst) (n := p) (x := 0)
    hfill hw hD) using markTime with v μ₁ ⟨hfilled,hkept⟩
  have hkr : ∀ i < n, μ₁ (keys+i) = (key i : ℤ) := by
    intro i hi
    exact (hkept _ (by omega)).trans (hkeys i hi)
  have hfr : ∀ i < n, μ₁ (flags+i) = (valid i : ℤ) := by
    intro i hi
    exact (hkept _ (by omega)).trans (hflags i hi)
  have hzero : ∀ r < p, μ₁ (dst+r)=0 := by
    intro r hr
    exact (hfilled r (by simpa using hr)).trans (List.getElem_replicate ..)
  apply Ends.pieceLast (mark_ends key valid (by simp) (by simp) (by simp) (by simp)
    hw hK hF hD hsepK hsepF hkr hfr hkeyLt hzero hword)
  · intro σ' hpost
    exact ⟨hpost.1,fun a ha => (hpost.2 a ha).trans (hkept a ha)⟩

def program : Program := [body 1,fillBody]

end ThreeSum.LightSupportMark
