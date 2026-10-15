import Submission.ThreeSum.LightTernarySourceHost
import Submission.ThreeSum.TernaryWeightedPhysicalSources
import Submission.ThreeSum.TernaryCodeSemantics

noncomputable section
namespace ThreeSum.TernarySourceHostModel
open Finset Light TernaryJointType
open scoped BigOperators

variable {N : ℕ}

def records (M NL NR : ℕ) (input dictionary : ℕ → ℤ) : Finset (ℕ × ℕ) :=
  ((range NL).product (range NR)).filter (fun pair => (M : ℤ)∣input pair.1-dictionary pair.2)

@[simp] theorem mem_records (M NL NR : ℕ) (input dictionary : ℕ → ℤ) (pair : ℕ × ℕ) :
    pair∈records M NL NR input dictionary ↔ pair.1<NL ∧ pair.2<NR ∧
      (M : ℤ)∣input pair.1-dictionary pair.2 := by
  rcases pair with ⟨i,j⟩
  simp only [records,mem_filter,Finset.product_eq_sprod,Finset.mem_product,mem_range,and_assoc]

def channel (S : Finset (ℕ × ℕ)) (group : ℕ → ℕ) (g : ℕ) : Finset (ℕ × ℕ) :=
  S.filter (fun pair => group pair.2=g)

def physical (S : Finset (ℕ × ℕ)) (enumeration : ℕ → TritWord N)
    (key group : ℕ → ℕ) (weight : ℕ → ℤ) (g : ℕ) (R : TritWord N) : ℤ :=
  TernaryWeightedPhysicalSources.histogram (channel S group g)
    (fun pair => enumeration (key pair.2)) (fun pair => weight pair.1) R

theorem sum_getD {A : Type*} [DecidableEq A] (ps : List A) (fallback : A)
    (hn : ps.Nodup) (f : A → ℤ) :
    (∑ i∈range ps.length, f (ps.getD i fallback))=∑ pair∈ps.toFinset, f pair := by
  have hm : (List.range ps.length).map (fun i => ps.getD i fallback)=ps := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp only [List.getD,List.getElem_map,List.getElem_range,List.getElem?_eq_getElem hi',Option.getD_some]
  calc
    _=((List.range ps.length).map (fun i => f (ps.getD i fallback))).sum := by
      simpa only [List.toFinset_range] using List.sum_toFinset _ (List.nodup_range (n := ps.length))
    _=(ps.map f).sum := by
      simpa only [List.map_map,Function.comp_def] using
        congrArg (fun ys => (ys.map f).sum) hm
    _=∑ pair∈ps.toFinset, f pair := (List.sum_toFinset f hn).symm

theorem packed_eq_iff (bank g h a b : ℕ) (ha : a<bank) (hb : b<bank) :
    g*bank+a=h*bank+b ↔ g=h ∧ a=b := by
  have hbank : 0<bank := by omega
  have hdiv (g a : ℕ) (ha : a<bank) : (g*bank+a)/bank=g := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hbank,Nat.div_eq_of_lt ha,Nat.zero_add]
  constructor
  · intro he
    have hg := congrArg (fun z => z/bank) he
    rw [hdiv g a ha,hdiv h b hb] at hg
    rw [hg] at he
    exact ⟨hg,by omega⟩
  · rintro ⟨rfl,rfl⟩; rfl

/-- Actual machine histogram sums reindex to the fixed original-record set.
No assumption about the join's enumeration order is needed. -/
theorem physical_eq_total (M NL NR bank : ℕ) (input dictionary : ℕ → ℤ)
    (enumeration : ℕ → TritWord N) (key group : ℕ → ℕ) (weight : ℕ → ℤ)
    (ps : List (ℕ × ℕ)) (hn : ps.Nodup)
    (hmem : ∀ i j, (i,j)∈ps ↔ i<NL ∧ j<NR ∧ (M : ℤ)∣input i-dictionary j)
    (hkey : ∀ j<NR, key j<bank)
    (hinj : ∀ i j, i<bank → j<bank → enumeration i=enumeration j → i=j)
    (g r : ℕ) (hr : r<bank) :
    physical (records M NL NR input dictionary) enumeration key group weight g (enumeration r)=
      LightTernaryWeightedHistogram.total
        (fun i => group (ps.getD i (0,0)).2*bank+key (ps.getD i (0,0)).2)
        (fun i => weight (ps.getD i (0,0)).1) (g*bank+r) ps.length := by
  classical
  have hset : ps.toFinset=records M NL NR input dictionary := by
    ext pair
    simpa only [List.mem_toFinset,mem_records] using hmem pair.1 pair.2
  have hsum := sum_getD ps (0,0) hn (fun pair =>
    if group pair.2*bank+key pair.2=g*bank+r then weight pair.1 else 0)
  rw [hset] at hsum
  unfold LightTernaryWeightedHistogram.total
  change _=(∑ i∈range ps.length,
    if group (ps.getD i (0,0)).2*bank+key (ps.getD i (0,0)).2=g*bank+r
      then weight (ps.getD i (0,0)).1 else 0)
  rw [hsum]
  unfold physical TernaryWeightedPhysicalSources.histogram channel
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro pair hp
  have hvalid := (mem_records M NL NR input dictionary pair).mp hp
  have hword : enumeration (key pair.2)=enumeration r ↔ key pair.2=r :=
    ⟨hinj _ _ (hkey _ hvalid.2.1) hr,fun he => by rw [he]⟩
  have hpack := packed_eq_iff bank (group pair.2) g (key pair.2) r (hkey _ hvalid.2.1) hr
  simp only [hword,hpack]
  by_cases hg : group pair.2=g <;> by_cases hk : key pair.2=r <;> simp [hg,hk]

/-- The returned physical join list may use any order. Every emitted compact
histogram cell nevertheless denotes the same fixed set of original records. -/
theorem read_physical (M NL NR bank groups valueBase factor : ℕ)
    (input dictionary : ℕ → ℤ) (enumeration : ℕ → TritWord N)
    (key group : ℕ → ℕ) (weight : ℕ → ℤ) (ν : ℕ → ℤ)
    (ps : List (ℕ × ℕ)) (hn : ps.Nodup)
    (hmem : ∀ i j, (i,j)∈ps ↔ i<NL ∧ j<NR ∧ (M : ℤ)∣input i-dictionary j)
    (hkey : ∀ j<NR, key j<bank)
    (hinj : ∀ i j, i<bank → j<bank → enumeration i=enumeration j → i=j)
    (hread : ∀ r<groups*bank, ν (valueBase+r)=(factor : ℤ)*
      LightTernaryWeightedHistogram.total
        (fun i => group (ps.getD i (0,0)).2*bank+key (ps.getD i (0,0)).2)
        (fun i => weight (ps.getD i (0,0)).1) r ps.length) :
    ∀ g<groups, ∀ r<bank, ν (valueBase+g*bank+r)=(factor : ℤ)*
      physical (records M NL NR input dictionary) enumeration key group weight g (enumeration r) := by
  intro g hg r hr
  have hm := Nat.mul_le_mul_right bank (show g+1≤groups by omega)
  rw [Nat.add_mul,Nat.one_mul] at hm
  rw [Nat.add_assoc,hread _ (by omega),
    physical_eq_total M NL NR bank input dictionary enumeration key group weight ps hn hmem hkey hinj g r hr]

theorem enumeration_injective (enumeration : ℕ → TritWord N) (bank : ℕ)
    (hsorted : ∀ i j, i<j → j<bank →
      TernaryCodeSemantics.address (enumeration i)<TernaryCodeSemantics.address (enumeration j)) :
    ∀ i j, i<bank → j<bank → enumeration i=enumeration j → i=j := by
  intro i j hi hj he
  rcases lt_trichotomy i j with hij|hij|hij
  · have hh := hsorted i j hij hj
    rw [he] at hh
    omega
  · exact hij
  · have hh := hsorted j i hij hi
    rw [he] at hh
    omega

theorem physical_homogeneous (S : Finset (ℕ × ℕ)) (enumeration : ℕ → TritWord N)
    (key group : ℕ → ℕ) (weight : ℕ → ℤ) (h : ℕ)
    (hrank : ∀ pair∈S, TernaryBank.rank (enumeration (key pair.2))=h) (g : ℕ) :
    ∀ R, physical S enumeration key group weight g R≠0 → TernaryBank.rank R=h := by
  apply TernaryWeightedPhysicalSources.histogram_homogeneous
  intro pair hp
  exact hrank pair (Finset.mem_filter.mp hp).1

/-- A source-type constant factorial is the pointwise factorial weighting
required by the exact convolution theorem. -/
theorem factor_physical (S : Finset (ℕ × ℕ)) (enumeration : ℕ → TritWord N)
    (key group : ℕ → ℕ) (weight : ℕ → ℤ) (factor : ℤ)
    (hfactor : ∀ pair∈S, factor=TernaryConvolution.factorial (enumeration (key pair.2)))
    (g : ℕ) (R : TritWord N) :
    factor*physical S enumeration key group weight g R=
      TernaryConvolution.factorial R*physical S enumeration key group weight g R := by
  classical
  unfold physical TernaryWeightedPhysicalSources.histogram
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair hp
  by_cases he : enumeration (key pair.2)=R
  · have hf := hfactor pair (Finset.mem_filter.mp hp).1
    rw [he] at hf
    rw [hf]
  · simp [he]

end ThreeSum.TernarySourceHostModel
