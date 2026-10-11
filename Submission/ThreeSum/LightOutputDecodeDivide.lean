import Submission.ThreeSumApsp.Lang.Lib.Emod

/-!
# Binary quotient for physical output indices

The existing checked doubling table is reused. During descending
subtraction this routine also accumulates the quotient bits, so its time
is logarithmic in the numerator rather than linear in the quotient.
-/

namespace ThreeSum.LightOutputDecodeDivide

open Light Light.Emod

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

abbrev Quotient : ℕ := 6

def reduceRound : Stmt :=
  .set Count (v Count -' k 1) ;;
  .set Quotient (k 2 *' v Quotient) ;;
  .ite (M (v Free +' v Count) ≤' v Rest)
    (.set Rest (v Rest -' M (v Free +' v Count)) ;;
      .set Quotient (v Quotient +' k 1)) .skip

def reduce : Stmt := .while (k 0 <' v Count) reduceRound

def body : Stmt :=
  .set Rest (v Arg) ;;
  .set Count (k 0) ;;
  .set Mult (v Modulus) ;;
  emodTable ;;
  .set Quotient (k 0) ;;
  reduce ;;
  .set Arg (v Quotient)

def time (a Mo : ℕ) : ℕ := 80*emodRounds a Mo+100
def budget (V : ℕ) : ℕ := 100*(Nat.log 2 (V+1)+2)

variable {lim : Limits} {P : Program} {d : ℕ} {μ ν : ℕ → ℤ} {a Mo V fr : ℕ}

theorem reduce_ends (F : Pre lim Mo V fr) (haV : a ≤ V) {t : ℤ}
    (tab : Table μ ν Mo fr (emodRounds a Mo)) :
    Ends lim P d reduce ⟨frame [a,Mo,fr,a,emodRounds a Mo,t,0],ν⟩
      (60*emodRounds a Mo+4)
      (fun σ => σ = ⟨frame [a,Mo,fr,(a%Mo : ℕ),0,t,(a/Mo : ℕ)],ν⟩) := by
  light_facts F
  have hK := emodRounds_le haV (M := Mo)
  have hgt : a < Mo*2^(emodRounds a Mo) := not_le.mp fun h =>
    absurd ((mul_two_pow_le_iff F.mod_pos).mp h) (lt_irrefl _)
  refine Ends.whileConst (fun i σ => ∃ r q : ℕ,
    σ = ⟨frame [a,Mo,fr,r,(emodRounds a Mo-i : ℕ),t,q],ν⟩ ∧
      r < Mo*2^(emodRounds a Mo-i) ∧ a=q*(Mo*2^(emodRounds a Mo-i))+r)
    (emodRounds a Mo) reduceRound.blockCost ?start ?round ?done
    (by simp [reduceRound]; omega)
  case start => exact ⟨a,0,by simp,by simpa using hgt,by simp⟩
  case done =>
    rintro _ ⟨r,q,rfl,hr,haq⟩
    rw [Nat.sub_self] at hr haq ⊢
    simp only [pow_zero,Nat.mul_one] at hr haq
    have hq : a/Mo=q := by
      rw [haq,Nat.add_comm,Nat.add_mul_div_right _ _ F.mod_pos,Nat.div_eq_of_lt hr,Nat.zero_add]
    have hr' : a%Mo=r := by
      have hh := Nat.div_add_mod a Mo
      rw [hq] at hh
      nlinarith
    exact ⟨by simp; omega,by simp,by rw [hq,hr']; rfl⟩
  case round =>
    rintro i _ hi ⟨r,q,rfl,hr,haq⟩
    obtain ⟨c,hc⟩ : ∃ c, emodRounds a Mo-i=c+1 := ⟨emodRounds a Mo-i-1,by omega⟩
    rw [show emodRounds a Mo-(i+1)=c by omega]
    rw [hc] at hr haq ⊢
    have hcell : ν (fr+c)=((Mo*2^c : ℕ) : ℤ) := tab.1 c (by omega)
    have hmle : Mo*2^c ≤ a := (mul_two_pow_le_iff F.mod_pos).mpr (by omega)
    have hqle : q ≤ a := by
      have hp : 0 < Mo*2^(c+1) := Nat.mul_pos F.mod_pos (Nat.two_pow_pos _)
      have hm := Nat.le_mul_of_pos_right q hp
      omega
    have hrle : r ≤ a := by omega
    have hdouble : Mo*2^(c+1)=Mo*2^c+Mo*2^c := by ring
    rw [hdouble] at hr haq
    generalize Mo*2^c=m at hr haq hcell hmle ⊢
    refine ⟨by light_side,by light_side,?_⟩
    unfold reduceRound
    light_set (c : ℕ)
    light_set (2*q : ℕ)
    refine Ends.iteLast (fun h => ?_) (fun h => ?_)
    · have hmr : m ≤ r := by simp [hcell] at h; omega
      light_set (r-m : ℕ) using hcell
      light_set (2*q+1 : ℕ)
      refine ⟨r-m,2*q+1,rfl,by omega,?_⟩
      have hs := Nat.sub_add_cancel hmr
      nlinarith
    · have hrm : r < m := by simp [hcell] at h; omega
      exact Ends.skip ⟨r,2*q,rfl,hrm,by nlinarith⟩

theorem meets {pMain : ℕ} (hmain : P[pMain]? = some body)
    (F : Pre lim Mo V fr) (haV : a ≤ V) :
    Meets lim P pMain d [a,Mo,fr] μ (time a Mo)
      (fun q ν => q = ((a/Mo : ℕ) : ℤ) ∧ Kept μ ν fr) := by
  light_facts F
  have hquot : a/Mo ≤ a := Nat.div_le_self _ _
  apply Meets.of_body hmain
  unfold body time
  light_set (a : ℕ)
  light_set (0 : ℕ)
  light_set (Mo : ℕ)
  refine Ends.next _ ((Light.Emod.table_ends (P := P) (d := d) (μ := μ)
    (x := (a : ℤ)) F haV).mono le_rfl ?_)
  rintro _ ⟨ν,rfl,tab⟩
  light_set (0 : ℕ)
  refine Ends.next _ ((reduce_ends (P := P) (d := d) F haV tab).mono le_rfl ?_)
  rintro _ rfl
  light_set (a/Mo : ℕ)
  exact ⟨rfl,tab.2⟩

theorem time_le_budget {a Mo V : ℕ} (ha : a ≤ V) : time a Mo ≤ budget V := by
  have hh := emodRounds_le ha (M := Mo)
  unfold time budget
  omega

theorem bounded_meets {pMain : ℕ} (hmain : P[pMain]? = some body)
    (F : Pre lim Mo V fr) (haV : a ≤ V) :
    Meets lim P pMain d [a,Mo,fr] μ (budget V)
      (fun q ν => q = ((a/Mo : ℕ) : ℤ) ∧ Kept μ ν fr) :=
  (meets hmain F haV).mono_time (time_le_budget haV)

def program : Program := [body]

theorem program_meets (F : Pre lim Mo V fr) (haV : a ≤ V) :
    Meets lim program 0 d [a,Mo,fr] μ (budget V)
      (fun q ν => q = ((a/Mo : ℕ) : ℤ) ∧ Kept μ ν fr) := bounded_meets rfl F haV

end ThreeSum.LightOutputDecodeDivide
