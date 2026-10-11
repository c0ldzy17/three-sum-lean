import Submission.ThreeSum.WantedRecordOrder

/-!
# Decode an actual emitted wanted-pair cell

The host loads the two physical indices, splits the left index into its
incidence position and lift, and decodes the right index into the original
occurrence and Q-mask rows. Its four-cell header retains both source labels
and the occurrence-only bank index. Division is the verified binary routine.
-/

namespace ThreeSum.LightWantedDecode

open Light GlobalEncoding OutputDecodeRecords

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

/-- Pair array, pair slot, incidence count, block count, schedule count,
layer count, retained layer masks, destination, and scratch pointer. -/
def body (pDivide pDecode : ℕ) : Stmt :=
  .set 9 (M (v 0 +' k 2 *' v 1)) ;;
  .set 10 (M (v 0 +' k 2 *' v 1 +' k 1)) ;;
  .call pDivide [v 9,v 2,v 8] 11 ;;
  .set 12 (v 9 -' v 11 *' v 2) ;;
  .call pDecode [v 10,v 3,v 4,v 5,v 6,v 7 +' k 4,v 8] 13 ;;
  .store (v 7) (v 12) ;;
  .store (v 7 +' k 1) (v 11) ;;
  .store (v 7 +' k 2) (v 10) ;;
  .store (v 7 +' k 3) (v 13) ;;
  .set 0 (v 13)

def time (J V : ℕ) : ℕ :=
  LightOutputDecodeDivide.budget V+LightOutputDecode.time J V+250

def word (V N h J : ℕ) : ℕ :=
  LightOutputDecode.word V (scheduleSize h) (layerCount h) J (2^(512*h))+
    4*V+4*N+32

abbrev space := LightOutputDecode.space

theorem decoder_power_bound (V T M J U N : ℕ) :
    T^J ≤ LightOutputDecode.word V T M J U+4*V+4*N+32 := by
  unfold LightOutputDecode.word
  omega

structure Stored (ν : ℕ → ℤ) (dst N h J i j : ℕ) : Prop where
  position : ν dst=((i%N : ℕ) : ℤ)
  liftIndex : ν (dst+1)=((i/N : ℕ) : ℤ)
  outputIndex : ν (dst+2)=(j : ℤ)
  bankIndex : ν (dst+3)=(OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j : ℤ)
  rows : LightOutputDecodeOriginal.Rows ν (dst+4) h J j

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {pairs slot N h J masks dst work i j V : ℕ}

theorem meets {pMain pDecode : ℕ} (S : LightOutputDecode.Procs P pDecode)
    (hmain : P[pMain]?=some (body S.pDivide pDecode))
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth)
    (hN : 0 < N) (hi : i ≤ V) (hj : j ≤ V) (hkey : j < localCount h^J)
    (hpairs : pairs+2*slot+2 ≤ dst)
    (hmask : masks+layerCount h ≤ dst) (hsep : dst+4+J+J ≤ work)
    (hspace : space work V ≤ lim.space) (hword : (word V N h J : ℤ) ≤ lim.word)
    (hleft : μ (pairs+2*slot)=(i : ℤ)) (hright : μ (pairs+2*slot+1)=(j : ℤ))
    (hread : ∀ s < layerCount h,
      μ (masks+s)=(LocalMaskGraph.maskAt (512*h) (2*h) s : ℤ)) :
    Meets lim P pMain d
      [pairs,slot,N,J,scheduleSize h,layerCount h,masks,dst,work] μ (time J V)
      (fun r ν =>
        r=(OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j : ℤ) ∧
        Stored ν dst N h J i j ∧ Kept μ ν dst) := by
  have hbudget (a : ℕ) (ha : a ≤ word V N h J) : (a : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ha).trans hword
  have hVWord := hbudget V (by unfold word; omega)
  have hiWord : (i : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hi).trans hVWord
  have hjWord : (j : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hj).trans hVWord
  have hNWord := hbudget N (by unfold word; omega)
  have hwork : work ≤ lim.space := by unfold space LightOutputDecode.space at hspace; omega
  have hdecodeWord := hbudget
    (LightOutputDecode.word V (scheduleSize h) (layerCount h) J (2^(512*h)))
    (by unfold word; omega)
  have hfr : Light.Emod.Pre lim N V work := by
    refine ⟨hN,hw,?_,hspace⟩
    have hh := hbudget (4*V+4*N+16) (by unfold word; omega)
    exact_mod_cast hh
  let q := i/N
  let s := i%N
  have hqV : q ≤ V := (Nat.div_le_self _ _).trans hi
  have hsV : s ≤ V := (Nat.mod_le _ _).trans hi
  have hqWord : (q : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hqV).trans hVWord
  have hsWord : (s : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hsV).trans hVWord
  have hprod : q*N ≤ V := (Nat.div_mul_le_self _ _).trans hi
  have hprodWord : (q : ℤ)*(N : ℤ) ≤ lim.word :=
    (by exact_mod_cast hprod : (q : ℤ)*(N : ℤ) ≤ (V : ℤ)).trans hVWord
  have hprodNonneg : (0 : ℤ) ≤ (q : ℤ)*(N : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hdiff : (i : ℤ)-(q : ℤ)*(N : ℤ)=(s : ℤ) := by
    have hh : (N : ℤ)*(q : ℤ)+(s : ℤ)=(i : ℤ) := by
      exact_mod_cast Nat.div_add_mod i N
    nlinarith
  have hbank : OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j ≤
      (scheduleSize h)^J :=
    (OutputDecodeOccurrenceCode.code_lt (schedule_pos h) (layerCount_pos h) J j).le
  have hpowerWord := hbudget ((scheduleSize h)^J)
    (decoder_power_bound V (scheduleSize h) (layerCount h) J (2^(512*h)) N)
  have hbankWord : (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hbank).trans hpowerWord
  apply Meets.of_body hmain
  unfold body time
  have hleftAddr : ((pairs : ℤ)+2*(slot : ℤ)).toNat=pairs+2*slot := by omega
  have hrightAddr : ((pairs : ℤ)+2*(slot : ℤ)+1).toNat=pairs+2*slot+1 := by omega
  light_set (i : ℕ) using hleft,hleftAddr
  light_set (j : ℕ) using hright,hrightAddr
  light_call (LightOutputDecodeDivide.bounded_meets (d := d+1) S.divide hfr hi)
    with quotient μ₁ ⟨hquot,hkeep₁⟩
  have hquot' : quotient=(q : ℤ) := hquot
  light_set (s : ℕ) using hquot',hdiff
  have hread₁ : ∀ t < layerCount h,
      μ₁ (masks+t)=(LocalMaskGraph.maskAt (512*h) (2*h) t : ℤ) := by
    intro t ht
    rw [hkeep₁ _ (by omega)]
    exact hread t ht
  light_call (LightOutputDecodeOriginal.meets (d := d+1) (μ := μ₁)
    (dst := dst+4) S hw (by omega) hkey hj (by omega) hsep hspace hdecodeWord hread₁)
    with bank ν ⟨hbank',rows,kept⟩
  light_store dst (s : ℕ)
  light_store (dst+1) (q : ℕ) using hquot'
  light_store (dst+2) (j : ℕ)
  light_store (dst+3)
    (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j : ℕ) using hbank'
  light_set (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j : ℕ) using hbank'
  refine ⟨rfl,⟨?_,?_,?_,?_,?_⟩,?_⟩
  · simp [s]
  · simp [q]
  · simp
  · simp
  · constructor
    · intro t
      change Function.update (Function.update (Function.update (Function.update ν dst (s : ℤ))
        (dst+1) (q : ℤ)) (dst+2) (j : ℤ)) (dst+3)
        (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j : ℤ)
        (dst+4+t.val)=_
      simp only [Function.update_of_ne (show dst+4+t.val ≠ dst+3 by omega),
        Function.update_of_ne (show dst+4+t.val ≠ dst+2 by omega),
        Function.update_of_ne (show dst+4+t.val ≠ dst+1 by omega),
        Function.update_of_ne (show dst+4+t.val ≠ dst by omega)]
      exact rows.occurrences t
    · intro t
      change Function.update (Function.update (Function.update (Function.update ν dst (s : ℤ))
        (dst+1) (q : ℤ)) (dst+2) (j : ℤ)) (dst+3)
        (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j : ℤ)
        (dst+4+J+t.val)=_
      simp only [Function.update_of_ne (show dst+4+J+t.val ≠ dst+3 by omega),
        Function.update_of_ne (show dst+4+J+t.val ≠ dst+2 by omega),
        Function.update_of_ne (show dst+4+J+t.val ≠ dst+1 by omega),
        Function.update_of_ne (show dst+4+J+t.val ≠ dst by omega)]
      exact rows.masks t
  · intro a ha
    change Function.update (Function.update (Function.update (Function.update ν dst (s : ℤ))
      (dst+1) (q : ℤ)) (dst+2) (j : ℤ)) (dst+3)
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j : ℤ) a=μ a
    rw [Function.update_of_ne (show a ≠ dst+3 by omega),
      Function.update_of_ne (show a ≠ dst+2 by omega),
      Function.update_of_ne (show a ≠ dst+1 by omega),
      Function.update_of_ne (show a ≠ dst by omega),kept _ (by omega),hkeep₁ _ (by omega)]

def program : Program := LightOutputDecode.program ++ [body 3 0]

theorem program_length : program.length=5 := rfl

theorem program_meets
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth)
    (hN : 0 < N) (hi : i ≤ V) (hj : j ≤ V) (hkey : j < localCount h^J)
    (hpairs : pairs+2*slot+2 ≤ dst)
    (hmask : masks+layerCount h ≤ dst) (hsep : dst+4+J+J ≤ work)
    (hspace : space work V ≤ lim.space) (hword : (word V N h J : ℤ) ≤ lim.word)
    (hleft : μ (pairs+2*slot)=(i : ℤ)) (hright : μ (pairs+2*slot+1)=(j : ℤ))
    (hread : ∀ s < layerCount h,
      μ (masks+s)=(LocalMaskGraph.maskAt (512*h) (2*h) s : ℤ)) :
    Meets lim program 4 d
      [pairs,slot,N,J,scheduleSize h,layerCount h,masks,dst,work] μ (time J V)
      (fun r ν =>
        r=(OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j : ℤ) ∧
        Stored ν dst N h J i j ∧ Kept μ ν dst) :=
  meets (pDecode := 0) ⟨1,2,3,rfl,rfl,rfl,rfl⟩ rfl
    hw hd hN hi hj hkey hpairs hmask hsep hspace hword hleft hright hread

theorem time_bound (J V : ℕ) :
    time J V ≤ 800*(J+1)*(Nat.log 2 (V+1)+2) := by
  have hh := LightOutputDecode.time_bound J V
  unfold time LightOutputDecodeDivide.budget
  nlinarith

end ThreeSum.LightWantedDecode
