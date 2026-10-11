import Submission.ThreeSum.LightCoverKeyData
import Submission.ThreeSum.LightRawAKeys
import Submission.ThreeSum.LightBalancedWanted

/-!
# Actual cover construction, lifted A keys, and balanced wanted records

This closed program runs the local-cover initializer and global key product,
constructs all three lifts of the supplied A incidences, selects the common
offset, and emits precisely the matching position pairs. Every dimension and
output address is read or computed. The retained cover, layers and coefficient
tables are available to the source-bank and output-decoding phases afterwards.
-/

namespace ThreeSum.LightGuardedWanted

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

def left (P : ℕ) (xs : List ℤ) : ℕ → ℤ := fun i => (RawAKeyLists.keys P xs).getD i 0
def right (h J : ℕ) : ℕ → ℤ := fun j => (globalKeys h J).getD j 0
def totalKeys (h J : ℕ) : ℕ := LightGlobalKeys.localCount h^J
def keyBound (P h J : ℕ) : ℕ := 2*P+(512*h*localPrime h)*(localPrime h+1)^J
def wantedFree (free h J n : ℕ) : ℕ := LightCoverKeyData.keyEnd free h J+3*n

/-- h, block count, A-incidence array and length, arithmetic modulus,
guarded modulus, and first free address. -/
def body (pCover pLifts pWanted : ℕ) : Stmt :=
  .call pCover [v 0,v 1,v 6] 7 ;;
  .set 8 (M (v 7)) ;;
  .set 9 (v 7 +' k 1) ;;
  .set 10 (v 9 +' v 8) ;;
  .set 11 (k 3 *' v 3) ;;
  .set 12 (v 10 +' v 11) ;;
  .call pLifts [v 2,v 3,v 4,v 10] 13 ;;
  .call pWanted [v 10,v 9,v 11,v 8,v 5,v 12] 0

def liftProgram : Program := ReportingHostRelocation.program LightCoverKeys.program LightRawAKeys.program
def program : Program := ReportingHostRelocation.program liftProgram LightBalancedWanted.program ++
  [body 67 68 97]

theorem program_length : program.length=99 := rfl

def time (P M h J U : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  LightCoverKeys.time h J+LightRawAKeys.time xs.length U+
    LightBalancedWanted.time M (left P xs) (right h J) (3*xs.length) (totalKeys h J)
      (keyBound P h J)+300

def space (free P M h J U : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  max (LightCoverKeys.space free h J)
    (max (LightRawAKeys.space (LightCoverKeyData.keyEnd free h J) xs.length U)
      (LightBalancedWanted.space (wantedFree free h J xs.length) M (left P xs) (right h J)
        (3*xs.length) (totalKeys h J) (keyBound P h J)))

def word (P M h J U n : ℕ) : ℕ :=
  max (LightCoverKeys.word h J) (max (LightRawAKeys.word P U)
    (LightBalancedWanted.word M (3*n) (totalKeys h J) (keyBound P h J)))

theorem selected_eq (P M h J : ℕ) [NeZero M] (xs : List ℤ) :
    LightOriginalOffset.selected M (left P xs) (right h J) (3*xs.length) (totalKeys h J)=
      RawAKeyLists.selected M P xs h J := by
  unfold RawAKeyLists.selected GlobalKeyOffset.selected
  rw [RawAKeyLists.keys_length,LightCoverKeyData.global_length]
  rfl

theorem left_bound {P h J : ℕ} (hP : 0 < P) (xs : List ℤ) (i : ℕ) (hi : i < 3*xs.length) :
    |left P xs i| ≤ (keyBound P h J : ℤ) := by
  have hi' : i < (RawAKeyLists.keys P xs).length := by rwa [RawAKeyLists.keys_length]
  unfold left
  rw [List.getD_eq_getElem _ _ hi']
  have hh := RawAKeyLists.keys_bounded (by exact_mod_cast hP : (0 : ℤ) < P)
    xs _ (List.getElem_mem hi')
  have hb : 2*P ≤ keyBound P h J := by unfold keyBound; omega
  exact hh.trans (by exact_mod_cast hb)

theorem right_bound (h J P : ℕ) (j : ℕ) (hj : j < totalKeys h J) :
    |right h J j| ≤ (keyBound P h J : ℤ) := by
  have hj' : j < (globalKeys h J).length := by rwa [LightCoverKeyData.global_length]
  unfold right
  rw [List.getD_eq_getElem _ _ hj']
  have hh := globalKeys_bounded h J _ (List.getElem_mem hj')
  have hb : (512*h*localPrime h)*(localPrime h+1)^J ≤ keyBound P h J := by
    unfold keyBound
    omega
  exact hh.trans (Int.ofNat_le.mpr hb)

variable {lim : Limits}

theorem program_meets {μ : ℕ → ℤ} {a free P M h J U d : ℕ} [NeZero M] (xs : List ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hP : 0 < P) (ha : a+xs.length ≤ free)
    (hspace : space free P M h J U xs ≤ lim.space)
    (hword : (word P M h J U xs.length : ℤ) ≤ lim.word)
    (hd : d+512*h+J+Nat.clog 2 M+3*xs.length+12 ≤ lim.depth)
    (hread : Seg μ a xs) (hvalues : ∀ x ∈ xs, |x| ≤ (U : ℤ)) :
    Meets lim program 98 d [h,J,a,xs.length,P,M,free] μ (time P M h J U xs)
      (fun r ν => r=(wantedFree free h J xs.length : ℤ) ∧
        LightWantedSetup.Output ν (wantedFree free h J xs.length) M (left P xs) (right h J)
          (3*xs.length) (totalKeys h J) (RawAKeyLists.selected M P xs h J) ∧
        M*(ν (wantedFree free h J xs.length)).toNat ≤ 3*xs.length*totalKeys h J ∧
        LightCoverKeyData.Stored ν free h J ∧
        Seg ν (LightCoverKeyData.keyEnd free h J) (RawAKeyLists.keys P xs) ∧ Kept μ ν free) := by
  let keyHead := LightCoverKeys.keyHeader free h J
  let rawBase := LightCoverKeyData.keyEnd free h J
  let out := wantedFree free h J xs.length
  have hkeyEnd : rawBase=keyHead+1+totalKeys h J := rfl
  have hout : out=rawBase+3*xs.length := rfl
  have hcoverSpace : LightCoverKeys.space free h J ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hliftSpace : LightRawAKeys.space rawBase xs.length U ≤ lim.space :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hspace)
  have hwantedSpace : LightBalancedWanted.space out M (left P xs) (right h J)
      (3*xs.length) (totalKeys h J) (keyBound P h J) ≤ lim.space :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hspace)
  have hcoverWord : (LightCoverKeys.word h J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hliftWord : (LightRawAKeys.word P U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((le_max_left _ _).trans (le_max_right _ _))).trans hword
  have hwantedWord : (LightBalancedWanted.word M (3*xs.length) (totalKeys h J) (keyBound P h J) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((le_max_right _ _).trans (le_max_right _ _))).trans hword
  have hrawSpace : rawBase+3*xs.length+Nat.log 2 (U+1)+2 ≤ lim.space := hliftSpace
  have hfree : free ≤ rawBase := LightCoverKeyData.free_le_keyEnd free h J
  have htripleWord : (3*(xs.length : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show 3*xs.length ≤ lim.space by omega) :
      (3*(xs.length : ℤ)) ≤ lim.space).trans hw
  apply Meets.of_body (p := 98) (by rfl : program[98]? = some (body 67 68 97))
  unfold body time
  have hc := (((LightCoverKeyData.program_meets (d := d+1) (μ := μ) (h := h) (J := J)
    (free := free) hw (by omega) hcoverSpace hcoverWord).append
      (LightRawAKeys.program.map (ReportingHostRelocation.relocate 68))).append
      (LightBalancedWanted.program.map (ReportingHostRelocation.relocate 72))).append [body 67 68 97]
  light_call hc with header μ₁ ⟨hheader,H,hkeepC⟩
  have hcount := H.count
  light_set (totalKeys h J : ℕ) using hheader,hcount,totalKeys
  light_set (keyHead+1 : ℕ) using hheader,keyHead
  light_set (rawBase : ℕ) using hkeyEnd
  light_set (3*xs.length : ℕ)
  light_set (out : ℕ) using hout
  have hx₁ : Seg μ₁ a xs := by
    apply hread.congr
    intro i hi
    exact hkeepC _ (by omega)
  have hl := ((ReportingHostRelocation.meets
    (LightRawAKeys.program_meets (d := d+1) (μ := μ₁) (src := a) (free := rawBase)
      (p := P) (U := U) xs hw hP (by omega) hliftSpace hliftWord (by omega) hx₁ hvalues)
    LightCoverKeys.program).append
      (LightBalancedWanted.program.map (ReportingHostRelocation.relocate 72))).append [body 67 68 97]
  light_call hl with rawHead μ₂ ⟨hrawHead,hraw,hkeepL⟩
  have hleft (i : ℕ) (hi : i < 3*xs.length) : μ₂ (rawBase+i)=left P xs i := by
    have hi' : i < (RawAKeyLists.keys P xs).length := by rwa [RawAKeyLists.keys_length]
    rw [left,List.getD_eq_getElem _ _ hi']
    exact hraw i hi'
  have hright (j : ℕ) (hj : j < totalKeys h J) : μ₂ (keyHead+1+j)=right h J j := by
    have hj' : j < (globalKeys h J).length := by rwa [LightCoverKeyData.global_length]
    rw [hkeepL _ (by omega),right,List.getD_eq_getElem _ _ hj']
    exact H.keys j hj'
  have hb := (ReportingHostRelocation.meets
    (LightBalancedWanted.program_meets (d := d+1) (μ := μ₂) (a := rawBase) (b := keyHead+1)
      (NL := 3*xs.length) (NR := totalKeys h J) (M := M) (free := out) (U := keyBound P h J)
      (left P xs) (right h J) hw (by omega) (by omega) hwantedSpace hwantedWord (by omega)
      hleft hright (left_bound hP xs) (right_bound h J P)) liftProgram).append [body 67 68 97]
  light_call hb with result ν ⟨hresult,houtput,hbound,hkeepB⟩
  have hretain : Kept μ₁ ν rawBase := by
    intro i hi
    exact (hkeepB _ (by omega)).trans (hkeepL i hi)
  refine ⟨hresult,?_,hbound,H.of_kept hretain,?_,?_⟩
  · simpa only [selected_eq] using houtput
  · apply hraw.congr
    intro i hi
    rw [RawAKeyLists.keys_length] at hi
    exact hkeepB _ (by omega)
  · intro i hi
    exact (hretain i (by omega)).trans (hkeepC i hi)

end ThreeSum.LightGuardedWanted
