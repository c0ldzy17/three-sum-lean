import Submission.ThreeSum.EncodedColorCoverData

/-! # Recover the wanted-header address from the retained cover controls -/

namespace ThreeSum.LightEncodedColorWantedHeader

open Light GlobalEncoding LocalCoverBounds

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

/-- Cover header, block count, and original incidence count. -/
def body : Stmt :=
  .set 3 (M (v 0 +' k 18)) ;;
  .set 4 (M (v 0)) ;;
  .set 5 (M (v 0 +' k 10)) ;;
  .set 6 (v 5 *' v 4) ;;
  .set 7 (v 3 +' v 4 +' v 6) ;;
  .set 8 (k 1) ;;
  .for 9 (v 1) (
    .set 7 (v 7 +' k 1 +' v 8) ;;
    .set 8 (v 8 *' v 6)) ;;
  .set 7 (v 7 +' k 1 +' v 8) ;;
  .set 0 (v 7 +' k 3 *' v 2)

def time (J : ℕ) : ℕ := 100*J+1000

def program : Program := [body]

theorem program_length : program.length=1 := rfl

theorem key_controls {μ : ℕ → ℤ} {free h J : ℕ} (H : LightCoverKeyData.Stored μ free h J) :
    μ (free+18)=(LightCoverKeys.afterCover free h : ℤ) ∧
    μ free=(outputCount (512*h) h : ℤ) ∧ μ (free+10)=(scheduleSize h : ℤ) := by
  have hh (i : ℕ) (hi : i < 20) := H.header.getD (i := i)
    (by simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hi) 0
  refine ⟨?_,?_,(EncodedColorCoverData.source_controls H).2.2.2.1⟩
  · simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values,LightCoverKeys.afterCover] using hh 18 (by omega)
  · simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hh 0 (by omega)

theorem radix_space_mono (dst m : ℕ) : Monotone (LightRadixKeys.space dst m) :=
  monotone_nat_of_le_succ (LightRadixKeys.space_step dst m)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain free h J len : ℕ} {μ : ℕ → ℤ}
    (main : P[pMain]?=some body) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : LightGuardedWanted.wantedFree free h J len ≤ lim.space)
    (H : LightCoverKeyData.Stored μ free h J) :
    Meets lim P pMain d [free,J,len] μ (time J)
      (fun r ν => r=(LightGuardedWanted.wantedFree free h J len : ℤ) ∧ ν=μ) := by
  let after := LightCoverKeys.afterCover free h
  let L := outputCount (512*h) h
  let S := scheduleSize h
  let m := LightGlobalKeys.localCount h
  let scratch := LightGlobalKeys.scratch after h
  have hparts (i : ℕ) (hi : i ≤ J) : scratch+LightRadixKeys.offset m i+1+m^i ≤
      LightCoverKeyData.keyEnd free h J := radix_space_mono scratch m hi
  have hkey : LightCoverKeyData.keyEnd free h J ≤ lim.space := by
    unfold LightGuardedWanted.wantedFree at hspace
    omega
  have hheader := EncodedColorCoverData.header_end free h J
  have hstart := hparts 0 (Nat.zero_le _)
  have hlast := hparts J le_rfl
  have hJ := LightRadixKeys.le_offset m J
  have hmS : S ≤ m := by
    exact Nat.le_mul_of_pos_right _ (Nat.choose_pos (by omega))
  have hstart' : after+L+m+2 ≤ lim.space := by
    simpa [LightRadixKeys.offset,scratch,LightGlobalKeys.scratch,L,m,Nat.add_assoc]
      using hstart.trans hkey
  have hlen : 3*len ≤ lim.space := by unfold LightGuardedWanted.wantedFree at hspace; omega
  have hWantEnd : LightCoverKeyData.keyEnd free h J+3*len ≤ lim.space := hspace
  obtain ⟨readAfter,readL,readS⟩ := key_controls H
  have add10 : ((free : ℤ)+10).toNat=free+10 := by omega
  have add18 : ((free : ℤ)+18).toNat=free+18 := by omega
  have hscratch : scratch=after+L+m := rfl
  have hm : m=S*L := rfl
  apply Meets.of_body main
  unfold body time
  light_set (after : ℕ) using readAfter,add18,after
  light_set (L : ℕ) using readL,L
  light_set (S : ℕ) using readS,add10,S
  light_set (m : ℕ) using hm
  light_set (scratch : ℕ) using hscratch
  light_set (1 : ℕ)
  refine Ends.pieceThen (Ends.for (T := 60*J+6)
    (Q := fun σ => σ=⟨frame [free,J,len,after,L,S,m,scratch+LightRadixKeys.offset m J,(m^J : ℕ),J],μ⟩)
    (fun i σ => σ=⟨frame [free,J,len,after,L,S,m,scratch+LightRadixKeys.offset m i,(m^i : ℕ),i],μ⟩)
    J 40 ?start ?round ?done ?bound (hT := by light_time)) ?after
  case start => simp [update_frame_setLocal,LightRadixKeys.offset]
  case round =>
    rintro i _ hi _ rfl
    have hiPart := (hparts i (by omega)).trans hkey
    have hnPart := (hparts (i+1) (by omega)).trans hkey
    have hptr : scratch+LightRadixKeys.offset m (i+1)=scratch+LightRadixKeys.offset m i+1+m^i := by
      rw [LightRadixKeys.offset]
      omega
    have hpow : m^(i+1)=m^i*m := pow_succ _ _
    have hiZ : (scratch : ℤ)+(LightRadixKeys.offset m i : ℤ)+1+(m : ℤ)^i ≤ lim.word :=
      (by exact_mod_cast hiPart : _ ≤ (lim.space : ℤ)).trans hw
    have hnZ : (scratch : ℤ)+(LightRadixKeys.offset m (i+1) : ℤ)+1+(m : ℤ)^i*(m : ℤ) ≤ lim.word := by
      have hz : (scratch : ℤ)+(LightRadixKeys.offset m (i+1) : ℤ)+1+(m : ℤ)^(i+1) ≤ lim.word :=
        (by exact_mod_cast hnPart : _ ≤ (lim.space : ℤ)).trans hw
      simpa only [pow_succ] using hz
    have hpowNonneg : (0 : ℤ) ≤ (m : ℤ)^i := by positivity
    have hproductNonneg : (0 : ℤ) ≤ (m : ℤ)^i*(m : ℤ) := by positivity
    light_set (scratch+LightRadixKeys.offset m (i+1) : ℕ) using hptr
    light_set (m^(i+1) : ℕ) using hpow
    simp [update_frame_setLocal]
  case done =>
    intro σ _ hI
    exact hI
  case bound =>
    rintro i _ hi _ rfl
    light_side
  case after =>
    rintro _ rfl
    have hkeyEq : LightCoverKeyData.keyEnd free h J=scratch+LightRadixKeys.offset m J+1+m^J := rfl
    have hlastZ : (scratch : ℤ)+(LightRadixKeys.offset m J : ℤ)+1+(m : ℤ)^J ≤ lim.word :=
      (by exact_mod_cast hlast.trans hkey : _ ≤ (lim.space : ℤ)).trans hw
    have hpowNonneg : (0 : ℤ) ≤ (m : ℤ)^J := by positivity
    light_set (LightCoverKeyData.keyEnd free h J : ℕ) using hkeyEq
    light_set (LightGuardedWanted.wantedFree free h J len : ℕ) using LightGuardedWanted.wantedFree
    exact ⟨rfl,rfl⟩

theorem program_meets {free h J len : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : LightGuardedWanted.wantedFree free h J len ≤ lim.space)
    (H : LightCoverKeyData.Stored μ free h J) :
    Meets lim program 0 d [free,J,len] μ (time J)
      (fun r ν => r=(LightGuardedWanted.wantedFree free h J len : ℤ) ∧ ν=μ) :=
  meets rfl hw hspace H

end ThreeSum.LightEncodedColorWantedHeader
