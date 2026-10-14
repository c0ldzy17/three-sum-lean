import Submission.ThreeSum.LightFixedRadixDictionary
import Submission.ThreeSum.LightTernaryProjectedJoin

namespace ThreeSum.LightTernaryDictionaryJoin
open Light RadixKeyLists
set_option maxHeartbeats 2000000
set_option maxRecDepth 14000
variable {lim : Limits}

def body : Stmt :=
  .call 4 [v 1,v 2,v 4,v 5] 12 ;;
  .set 13 (M (v 12)) ;;
  .set 14 (v 12 +' k 1) ;;
  .call 19 [v 0,v 14,v 3,v 13,v 6,v 7,v 8,v 9,v 10,v 11] 15 ;;
  .set 0 (v 15)

def joinedProgram (xs : List ℤ) : Program := ReportingHostRelocation.program
  (LightFixedRadixDictionary.program xs) LightTernaryProjectedJoin.program

def program (xs : List ℤ) : Program := joinedProgram xs++[body]

def dictionary (xs : List ℤ) (p J : ℕ) (i : ℕ) : ℤ := (values (p : ℤ) xs J).getD i 0

def time (xs : List ℤ) (p J q M : ℕ) (input : ℕ → ℤ) (NL U D : ℕ) (shift : ℤ) : ℕ :=
  LightFixedRadixDictionary.time xs J+
    LightTernaryProjectedJoin.time q M input (dictionary xs p J) NL (xs.length^J) U D shift+100

/-- Twenty-one actual procedures initialize the fixed signed local table,
build its runtime Cartesian radix dictionary, scan original physical input
positions and emit precisely their matching dictionary tuple IDs. -/
theorem program_meets (xs : List ℤ) {src localBase dst NL J p q M codeBase work free U V D d : ℕ}
    {shift : ℤ} (input : ℕ → ℤ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hm : 0 < xs.length)
    (hsrc : src+NL ≤ localBase) (hlocal : localBase+xs.length ≤ dst)
    (hbaseBound : ∀ x ∈ xs, |x| ≤ (V : ℤ))
    (hinitSpace : LightRadixKeys.space dst xs.length J ≤ lim.space)
    (hinitWord : (LightRadixKeys.word p V J : ℤ) ≤ lim.word)
    (hkeysEnd : LightRadixKeys.space dst xs.length J ≤ codeBase)
    (hq : 0 < q) (hM : 0 < M) (hcodes : codeBase+NL ≤ free) (hfree : free ≤ work)
    (hresidueSpace : LightSourceResidues.space work q U D ≤ lim.space)
    (hjoinSpace : LightWantedSetup.space free M (LightTernaryProjectedJoin.projected q M shift input)
      (dictionary xs p J) NL (xs.length^J) (U+M) 0 0 ≤ lim.space)
    (hresidueWord : (LightSourceResidues.word q M U D : ℤ) ≤ lim.word)
    (hjoinWord : (LightSourceResidues.word M M (U+M) 0 : ℤ) ≤ lim.word)
    (hshift : |shift| ≤ (D : ℤ)) (hd : d+NL+J+7 ≤ lim.depth)
    (hinput : ∀ i < NL, μ (src+i)=input i) (hvalues : ∀ i < NL, |input i| ≤ (U : ℤ))
    (hglobalBound : V*(p+1)^J ≤ U) :
    Meets lim (program xs) 20 d [src,localBase,dst,NL,J,p,q,M,shift,codeBase,work,free] μ
      (time xs p J q M input NL U D shift)
      (fun r ν => r=(free : ℤ) ∧
        LightWantedSetup.Output ν free M (LightTernaryProjectedJoin.projected q M shift input)
          (dictionary xs p J) NL (xs.length^J) 0 ∧ Kept μ ν localBase) := by
  have h := (LightFixedRadixDictionary.program_meets xs (base := localBase) (dst := dst)
    (p := p) (U := V) (J := J) (d := d+1) μ hw hlocal hm hbaseBound hinitSpace hinitWord (by omega)).append
      (LightTernaryProjectedJoin.program.map (ReportingHostRelocation.relocate 5))
  have hinit := h.append [body]
  apply Meets.of_body (by rfl : (program xs)[20]? = some body)
  unfold body time
  light_call hinit using LightTernaryProjectedJoin.time with head μ₁ ⟨hhead,hheader,hkeys,hkeepInit⟩
  have hNRWord : ((xs.length^J : ℕ) : ℤ) ≤ lim.word := by
    have hh : xs.length^J ≤ lim.space := by unfold LightRadixKeys.space at hinitSpace; omega
    exact (Int.ofNat_le.mpr hh).trans hw
  have hheaderZ : μ₁ head.toNat = ((xs.length^J : ℕ) : ℤ) := by rw [hhead]; simpa using hheader
  have hheaderAddr : dst+LightRadixKeys.offset xs.length J < lim.space := by
    unfold LightRadixKeys.space at hinitSpace
    omega
  have hheadWord : ((dst+LightRadixKeys.offset xs.length J : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hheaderAddr.le).trans hw
  light_set (xs.length^J : ℕ) using hheaderZ,hheader,hhead,hheadWord,hheaderAddr,hNRWord,LightTernaryProjectedJoin.time
  light_set (dst+LightRadixKeys.offset xs.length J+1 : ℕ) using hhead,LightTernaryProjectedJoin.time
  have hread (i : ℕ) (hi : i < NL) : μ₁ (src+i)=input i :=
    (hkeepInit _ (by omega)).trans (hinput i hi)
  have hdict (j : ℕ) (hj : j < xs.length^J) :
      μ₁ (dst+LightRadixKeys.offset xs.length J+1+j)=dictionary xs p J j := by
    unfold dictionary
    rw [List.getD_eq_getElem _ 0 (by simpa [values_length] using hj)]
    exact hkeys j (by simpa [values_length] using hj)
  have hb (j : ℕ) (hj : j < xs.length^J) : |dictionary xs p J j| ≤ (U : ℤ) := by
    unfold dictionary
    rw [List.getD_eq_getElem _ 0 (by simpa [values_length] using hj)]
    exact (values_bounded p V xs hbaseBound J _ (List.getElem_mem (by simpa [values_length] using hj))).trans
      (Int.ofNat_le.mpr hglobalBound)
  have hc := ReportingHostRelocation.meets
    (LightTernaryProjectedJoin.program_meets (d := d+1) (μ := μ₁)
      (src := src) (dict := dst+LightRadixKeys.offset xs.length J+1) (NL := NL) (NR := xs.length^J)
      (q := q) (M := M) (codeBase := codeBase) (work := work) (free := free)
      (U := U) (D := D) (shift := shift) input (dictionary xs p J) hw hq hM
      (by unfold LightRadixKeys.space at hkeysEnd; omega) hkeysEnd hcodes hfree
      hresidueSpace hjoinSpace hresidueWord hjoinWord hshift (by omega) hread hdict hvalues hb)
    (LightFixedRadixDictionary.program xs)
  have hjoin := hc.append [body]
  light_call hjoin using LightTernaryProjectedJoin.time with result ν ⟨hresult,hout,hkeepJoin⟩
  light_set (free : ℕ) using hresult,LightTernaryProjectedJoin.time
  refine ⟨rfl,hout,?_⟩
  intro a ha
  exact (hkeepJoin a (by unfold LightRadixKeys.space at hkeysEnd; omega)).trans (hkeepInit a ha)
end ThreeSum.LightTernaryDictionaryJoin
