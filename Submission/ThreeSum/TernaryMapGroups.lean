import Submission.ThreeSum.TernaryCanonicalTupleSemantics

noncomputable section
namespace ThreeSum.TernaryMapGroups
open TernaryCanonicalDictionaries TernaryFixedDictionaries TernaryJointType

def hash {F : ℕ} (xs : List (Fin F)) : ℤ :=
  Radix.positionalHash (F : ℤ) (fun i => (i.val : ℤ)) xs

theorem hash_injective {F : ℕ} (hF : 0<F) :
    ∀ xs ys : List (Fin F), xs.length=ys.length → hash xs=hash ys → xs=ys := by
  intro xs
  induction xs with
  | nil => intro ys hlen he; have hy : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm); exact hy.symm
  | cons x xs ih =>
    intro ys hlen he
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hx0 : (0 : ℤ)≤x.val := Nat.cast_nonneg _
      have hy0 : (0 : ℤ)≤y.val := Nat.cast_nonneg _
      have hxlt : (x.val : ℤ)<F := by exact_mod_cast x.isLt
      have hylt : (y.val : ℤ)<F := by exact_mod_cast y.isLt
      have hemod := congrArg (fun z : ℤ => z%(F : ℤ)) he
      simp only [hash,Radix.positionalHash,Int.add_emod,Int.mul_emod,Int.emod_self,
        zero_mul,Int.zero_emod,add_zero,Int.emod_emod,
        Int.emod_eq_of_lt hx0 hxlt,Int.emod_eq_of_lt hy0 hylt] at hemod
      have hxy : x=y := Fin.ext (by exact_mod_cast hemod)
      have ht : hash xs=hash ys := by
        have hFn : (F : ℤ)≠0 := by omega
        change (x.val : ℤ)+(F : ℤ)*hash xs=(y.val : ℤ)+(F : ℤ)*hash ys at he
        rw [hxy] at he
        exact mul_left_cancel₀ hFn (by omega)
      exact congrArg₂ List.cons hxy (ih ys (by simpa using hlen) ht)

variable {L : ℕ} {α : DigitType} {I : Type*} [Fintype I] [DecidableEq I]

def groupVector (rs : List (SourceRecord L α I)) : List (Fin (Fintype.card I)) :=
  rs.map fun r => Fintype.equivFin I r.1

theorem positional_map_hash (rs : List (SourceRecord L α I)) :
    Radix.positionalHash (Fintype.card I : ℤ) mapCode rs=hash (groupVector rs) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simpa only [Radix.positionalHash,groupVector,List.map_cons,hash,mapCode] using
      (congrArg (fun z : ℤ => mapCode r+(Fintype.card I : ℤ)*z) ih)

/-- Equal packed map keys mean exactly the same map occurrence at every
native block. Distinct map vectors cannot silently share an inverse bank. -/
theorem map_groups_equal (hI : 0<Fintype.card I) (rs ss : List (SourceRecord L α I))
    (hlen : rs.length=ss.length)
    (he : Radix.positionalHash (Fintype.card I : ℤ) mapCode rs=
      Radix.positionalHash (Fintype.card I : ℤ) mapCode ss) :
    rs.map Prod.fst=ss.map Prod.fst := by
  rw [positional_map_hash,positional_map_hash] at he
  have hv := hash_injective hI (groupVector rs) (groupVector ss) (by simpa [groupVector] using hlen) he
  have hd := congrArg (List.map (Fintype.equivFin I).symm) hv
  simpa only [groupVector,List.map_map,Function.comp_def,Equiv.symm_apply_apply] using hd

end ThreeSum.TernaryMapGroups
