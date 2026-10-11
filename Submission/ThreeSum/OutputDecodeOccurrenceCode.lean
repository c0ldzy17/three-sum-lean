import Submission.ThreeSum.OutputDecodeRecords

/-! # Occurrence-only source-bank indices, with first block most significant -/

namespace ThreeSum.OutputDecodeOccurrenceCode

open OutputDecodeOrder OutputDecodeRecords GlobalEncoding

set_option maxHeartbeats 1500000

def code (T M : ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 0
  | J+1,k => (k%(T*M))/M+T*code T M J (k/(T*M))

theorem last_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (k : ℕ) :
    (k%(T*M))/M < T :=
  (Nat.div_lt_iff_lt_mul hM).mpr (Nat.mod_lt _ (Nat.mul_pos hT hM))

theorem code_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (J k : ℕ) : code T M J k < T^J := by
  induction J generalizing k with
  | zero => simp [code]
  | succ J ih =>
    have hm := Nat.mul_le_mul_left T (show code T M J (k/(T*M))+1 ≤ T^J by exact ih _)
    have hd := last_lt hT hM k
    simp only [Nat.mul_add,Nat.mul_one] at hm
    rw [code,pow_succ']
    omega

theorem code_step (T M i k : ℕ) :
    code T M (i+1) k = code T M i k+T^i*((k/(T*M)^i)%(T*M)/M) := by
  induction i generalizing k with
  | zero => simp [code]
  | succ i ih =>
    change (k%(T*M))/M+T*code T M (i+1) (k/(T*M)) =
      ((k%(T*M))/M+T*code T M i (k/(T*M)))+T^(i+1)*((k/(T*M)^(i+1))%(T*M)/M)
    rw [ih,Nat.div_div_eq_div_mul,pow_succ',pow_succ']
    ring

theorem code_indices {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (J k : ℕ) :
    indices T J (code T M J k) = (indices (T*M) J k).map (fun i => i/M) := by
  induction J generalizing k with
  | zero => rfl
  | succ J ih =>
    have hd := last_lt hT hM k
    have hdiv : code T M (J+1) k/T = code T M J (k/(T*M)) := by
      rw [code,Nat.mul_comm T (code T M J (k/(T*M))),
        Nat.add_mul_div_right _ _ hT,Nat.div_eq_of_lt hd,Nat.zero_add]
    have hmod : code T M (J+1) k%T = (k%(T*M))/M := by
      have hm := Nat.div_add_mod (code T M (J+1) k) T
      rw [hdiv] at hm
      have he : code T M (J+1) k = (k%(T*M))/M+T*code T M J (k/(T*M)) := rfl
      omega
    rw [indices,hdiv,hmod,ih]
    simp only [indices,List.map_append,List.map_cons,List.map_nil]

theorem source_code_lt (h J k : ℕ) :
    code (scheduleSize h) (layerCount h) J k < scheduleSize h^J :=
  code_lt (schedule_pos h) (layerCount_pos h) J k

theorem source_code_coordinate (h J k : ℕ) {j : ℕ} (hj : j < J) :
    (indices (scheduleSize h) J (code (scheduleSize h) (layerCount h) J k)).getD j 0 =
      occurrenceIndex h J k j := by
  rw [code_indices (schedule_pos h) (layerCount_pos h)]
  have hi : j < (indices (scheduleSize h*layerCount h) J k).length := by
    rw [indices_length]
    exact hj
  rw [List.getD_map_of_lt _ hi 0 0]
  rfl

end ThreeSum.OutputDecodeOccurrenceCode
