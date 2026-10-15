import Submission.ThreeSum.LightPairSearch

namespace ThreeSum.LightPairSearch
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

def body (pRow : ℕ) : Stmt :=
  .set 2 (k 0) ;;
  .for 3 (v 0) (.call pRow [v 0,v 3,v 1,v 2] 2) ;;
  .set 0 (v 2)

def time (q T : ℕ) : ℕ := q*(rowTime q T+60)+20

def Inv (I : (ℕ → ℤ) → Prop) (q ctx : ℕ)
    (good : ℕ → ℕ → Prop) [DecidableRel good] (i : ℕ) (σ : State) : Prop :=
  ∃ ν : ℕ → ℤ, σ=⟨frame [q,ctx,first (goodCode q good) (i*q),i],ν⟩ ∧ I ν

variable {lim : Limits} {P : Program}

theorem meets {pMain pRow pPred q ctx T d : ℕ}
    (hmain : P[pMain]?=some (body pRow)) (hrow : P[pRow]?=some (rowBody pPred))
    (good : ℕ → ℕ → Prop) [DecidableRel good] (I : (ℕ → ℤ) → Prop)
    (hq : 0<q) (μ : ℕ → ℤ) (hI : I μ)
    (hword : ((q*q+q+ctx+20 : ℕ) : ℤ) ≤ lim.word)
    (hd : d+1<lim.depth)
    (hpred : ∀ u<q, ∀ v<q, ∀ ν, I ν → Meets lim P pPred (d+2) [u,v,ctx] ν T
      (fun r ξ => r=(if good u v then 1 else 0) ∧ I ξ)) :
    Meets lim P pMain d [q,ctx] μ (time q T)
      (fun r ν => r=(first (goodCode q good) (q*q) : ℤ) ∧ I ν) := by
  have hqW : (q : ℤ)≤lim.word := by omega
  have hctxW : (ctx : ℤ)≤lim.word := by omega
  apply Meets.of_body hmain
  unfold body time
  light_set (0 : ℕ) using rowTime
  refine Ends.pieceThen (Ends.for (T := q*(rowTime q T+60)+10)
    (Q := Inv I q ctx good q) (Inv I q ctx good) q (rowTime q T+40)
    ?_ ?_ ?_ ?_ (hT := by light_time)) ?_ (hT := by light_time)
  · exact ⟨μ,by simp [Inv,first,update_frame_setLocal],hI⟩
  · rintro i _ hi _ ⟨ν,rfl,hν⟩
    have hcode : i*q≤q*q := Nat.mul_le_mul_right q (by omega)
    have hpref := first_le (goodCode q good) (i*q)
    have hiW : (i : ℤ)≤lim.word := by omega
    have hcall := row_meets (d := d+1) hrow good I hq hi ν hν hword (by omega)
      (fun v hv ξ hξ => hpred i hi v hv ξ hξ)
    light_call hcall with result ξ ⟨hr,hξ⟩
    refine ⟨by simp,ξ,?_,hξ⟩
    simp [setLocal,hr,update_frame_setLocal]
  · intro σ _ hshape; exact hshape
  · rintro i _ hi _ ⟨ν,rfl,hν⟩; simp
  · rintro σ ⟨ν,rfl,hν⟩
    have hpref := first_le (goodCode q good) (q*q)
    light_set (first (goodCode q good) (q*q) : ℕ)
    exact ⟨rfl,hν⟩

theorem time_bound (q T : ℕ) (hq : 0<q) : time q T≤q*q*(T+200)+100 := by
  have hsq : q≤q*q := by nlinarith
  unfold time rowTime
  nlinarith

/-- Correctness of the finite exhaustive search, including its no-hit case. -/
theorem first_pair_spec (q : ℕ) (hq : 0<q) (good : ℕ → ℕ → Prop) [DecidableRel good] :
    (first (goodCode q good) (q*q)=0 ↔ ∀ u<q, ∀ v<q, ¬good u v) ∧
    (∀ code, first (goodCode q good) (q*q)=code+1 →
      code/q<q ∧ code%q<q ∧ good (code/q) (code%q) ∧
      ∀ u<q, ∀ v<q, u*q+v<code → ¬good u v) := by
  have hs := first_spec (goodCode q good) (q*q)
  constructor
  · rw [hs.1]
    constructor
    · intro h u hu v hv
      have ht : u*q+v<q*q := by
        have hh := Nat.mul_le_mul_right q (show u+1≤q by omega)
        nlinarith
      exact fun hg => h _ ht ((goodCode_pair q u v hq hv good).mpr hg)
    · intro h code hc
      exact h _ ((Nat.div_lt_iff_lt_mul hq).mpr hc) _ (Nat.mod_lt _ hq)
  · intro code hc
    obtain ⟨hcode,hgood,hmin⟩ := hs.2 code hc
    refine ⟨(Nat.div_lt_iff_lt_mul hq).mpr hcode,Nat.mod_lt _ hq,hgood,?_⟩
    intro u hu v hv hlt hg
    exact hmin _ hlt ((goodCode_pair q u v hq hv good).mpr hg)

end ThreeSum.LightPairSearch
