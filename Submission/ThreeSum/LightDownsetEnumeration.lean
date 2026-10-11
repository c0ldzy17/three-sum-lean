import Submission.ThreeSum.LightSubsetEnumerationSetup

/-!
# Sequential enumeration of a compact downset

This routine invokes the guarded layer enumerator for the successive
cardinalities. Each layer starts immediately after the preceding layer;
the only traversal besides the emitted masks is polynomial in the bit
width. All power-table reads are shared across the layer calls.
-/

namespace ThreeSum.LightDownsetEnumeration

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def layers (L : ℕ) : ℕ → List ℕ
  | 0 => []
  | j+1 => layers L j ++ enumerateLayer L j

theorem layers_length (L j : ℕ) : (layers L j).length = layerOffset L j := by
  induction j with
  | zero => simp [layers]
  | succ j ih =>
    simp only [layers,List.length_append,ih,enumerateLayer_length,layerOffset_succ]

theorem layers_eq_through (L j : ℕ) : layers L (j+1) = enumerateThrough L j := by
  induction j with
  | zero => simp [layers,enumerateThrough]
  | succ j ih =>
    change layers L (j+1) ++ enumerateLayer L (j+1) = _
    rw [ih]
    rfl

theorem layers_eq_downset {L cut : ℕ} (hcut : cut ≤ L) :
    layers L (cut+1) = enumerateDownset L cut := by
  simp only [enumerateDownset,Nat.min_eq_left hcut,layers_eq_through]

def budget (L cut : ℕ) : ℕ := 150*((4*L+1)*downsetCap L cut+1)

theorem layer_time_le_budget {L cut j : ℕ} (hcut : cut ≤ L) (hj : j ≤ cut) :
    LightSubsetEnumeration.time L j ≤ budget L cut := by
  have ho := layerOffset_mono L (show j+1 ≤ cut+1 by omega)
  rw [layerOffset_succ] at ho
  have hcap : layerOffset L (cut+1) = downsetCap L cut := by
    simp [downsetCap,Nat.min_eq_left hcut]
  have hc : L.choose j ≤ downsetCap L cut := by omega
  have h := LightSubsetEnumeration.time_bound L j
  exact h.trans (Nat.mul_le_mul_left 150
    (Nat.add_le_add_right (Nat.mul_le_mul_left (4*L+1) hc) 1))

def roundBody (pEnum : ℕ) : Stmt :=
  .call pEnum [v 0,v 4,k 0,v 2 +' v 5,v 3] 6 ;;
  .set 5 (v 5 +' v 6)

def body (pEnum : ℕ) : Stmt :=
  .set 5 (k 0) ;;
  .for 4 (v 1 +' k 1) (roundBody pEnum) ;;
  .set 0 (v 5)

def time (L cut : ℕ) : ℕ := (cut+1)*(budget L cut+70)+40

def Inv (μ : ℕ → ℤ) (L cut dst powers j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,cut,dst,powers,j,layerOffset L j,r],μ'⟩ ∧
    SegN μ' dst (layers L j) ∧ SameOutside μ μ' dst (layerOffset L j)

theorem meets {pMain pEnum L cut dst powers d : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some (body pEnum))
    (henum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hdst : dst+downsetCap L cut ≤ powers)
    (hpowers : Powers μ powers L) (hd : d+L+1 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,dst,powers] μ (time L cut)
      (fun r μ' => r = (downsetCap L cut : ℤ) ∧
        SegN μ' dst (enumerateDownset L cut) ∧
        SameOutside μ μ' dst (downsetCap L cut)) := by
  have hcap : layerOffset L (cut+1) = downsetCap L cut := by
    simp [downsetCap,Nat.min_eq_left hcut]
  apply Meets.of_body hmain
  unfold body time
  light_set (0 : ℕ) using budget
  refine Ends.pieceThen (Ends.for
    (T := (cut+1)*(budget L cut+70)+20)
    (Q := Inv μ L cut dst powers (cut+1))
    (Inv μ L cut dst powers) (cut+1) (budget L cut+50)
    ?start ?round ?done ?bound (hT := by light_time)) ?after
  case start =>
    refine ⟨0,μ,?_,?_,SameOutside.refl⟩
    · simp [update_frame_setLocal,layerOffset_zero]
      exact (frame_append_zeros [(L : ℤ),cut,dst,powers,0,0] 1).symm
    · exact Seg.nil
  case round =>
    rintro j _ hj _ ⟨r,μ',rfl,hseg,hsame⟩
    have hjcut : j ≤ cut := by omega
    have hpart := layerOffset_mono L (show j+1 ≤ cut+1 by omega)
    rw [layerOffset_succ,hcap] at hpart
    have hpartial : dst+layerOffset L j ≤ powers := by omega
    have hnext : dst+layerOffset L j+L.choose j ≤ powers := by omega
    have hpowers' : Powers μ' powers L := by
      intro i hi
      rw [hsame (powers+i) (Or.inr (by omega))]
      exact hpowers i hi
    have hcall := (LightSubsetEnumeration.meets henum hw hspace hword
      L j 0 (dst+layerOffset L j) μ' le_rfl (by omega) (by simp) hnext hpowers'
      (d+1) (by omega)).mono_time (layer_time_le_budget hcut hjcut)
    unfold roundBody
    light_call hcall using budget with n μ₁ ⟨hn,hnew,hsame₁⟩
    have hnewN : SegN μ₁ (dst+layerOffset L j) (enumerateLayer L j) := by
      simpa [LightSubsetEnumeration.output] using hnew
    have hseg' : SegN μ₁ dst (layers L j) :=
      hseg.of_sameOutside hsame₁ (Or.inl (by rw [layers_length]))
    have hsum : layerOffset L j+L.choose j ≤ lim.space := by omega
    have hsumZ : (layerOffset L j : ℤ)+(L.choose j : ℤ) ≤ lim.word := by
      have hb : (layerOffset L j : ℤ)+(L.choose j : ℤ) ≤ (lim.space : ℤ) := by
        exact_mod_cast hsum
      exact hb.trans hw
    light_set (layerOffset L (j+1) : ℕ) using hn,layerOffset_succ,budget
    refine ⟨by simp,n,μ₁,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · change Seg μ₁ dst (((layers L j) ++ enumerateLayer L j).map _)
      rw [List.map_append,seg_append,List.length_map,layers_length]
      exact ⟨hseg',hnewN⟩
    · exact hsame.then hsame₁ (fun a ha => by
        rw [layerOffset_succ] at ha
        constructor <;> omega)
  case done =>
    intro σ _ hI
    exact hI
  case bound =>
    rintro j _ hj _ ⟨r,μ',rfl,_,_⟩
    light_side
  case after =>
    rintro _ ⟨r,μ',rfl,hseg,hsame⟩
    have hcZ : (downsetCap L cut : ℤ) ≤ lim.word := by
      have hb : (downsetCap L cut : ℤ) ≤ (lim.space : ℤ) := by exact_mod_cast (show downsetCap L cut ≤ lim.space by omega)
      exact hb.trans hw
    light_set (downsetCap L cut : ℕ) using hcap
    exact ⟨by simp, by simpa only [layers_eq_downset hcut] using hseg,
      by simpa only [hcap] using hsame⟩

theorem time_bound {L cut : ℕ} (hcut : cut ≤ L) :
    time L cut ≤ 1000*(L+1)^2*(downsetCap L cut+1) := by
  have hb : budget L cut+70 ≤ 800*(L+1)*(downsetCap L cut+1) := by
    unfold budget
    nlinarith
  have hm := Nat.mul_le_mul_left (cut+1) hb
  have hc := Nat.mul_le_mul_right (800*(L+1)*(downsetCap L cut+1))
    (Nat.succ_le_succ hcut)
  have hp : 1 ≤ (L+1)^2*(downsetCap L cut+1) :=
    Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by omega)) (by omega))
  unfold time
  calc
    _ ≤ (L+1)*(800*(L+1)*(downsetCap L cut+1))+40 := Nat.add_le_add_right (hm.trans hc) 40
    _ = 800*((L+1)^2*(downsetCap L cut+1))+40 := by ring
    _ ≤ 1000*((L+1)^2*(downsetCap L cut+1)) := by omega
    _ = _ := by ring

def program : Program := [body 1,LightSubsetEnumeration.body 1]

theorem program_meets {L cut dst powers d : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hdst : dst+downsetCap L cut ≤ powers)
    (hpowers : Powers μ powers L) (hd : d+L+1 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,dst,powers] μ (time L cut)
      (fun r μ' => r = (downsetCap L cut : ℤ) ∧
        SegN μ' dst (enumerateDownset L cut) ∧
        SameOutside μ μ' dst (downsetCap L cut)) :=
  meets rfl rfl hw hspace hword hcut hdst hpowers hd

end ThreeSum.LightDownsetEnumeration
