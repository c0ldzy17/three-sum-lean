import Submission.ThreeSum.LightOutputDecodeDigits
import Submission.ThreeSum.LightArray
import Submission.ThreeSum.TernarySignedModes

/-! Executed original signed digit rows. Binary division is charged at log V. -/
namespace ThreeSum.LightTernarySignedRow
open Light TernarySignedDigits TernarySignedReduction

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

/-- Arguments: original value, offset, sign, J, base, destination, work,
and the two literal source tags. Digits are stored most significant first. -/
def body (pDigits : ℕ) : Stmt :=
  .set 9 (v 0 +' v 1) ;;
  .call pDigits [v 9,v 3,v 4,v 5,v 6] 10 ;;
  pass 11 (v 3) (v 5) (v 2 *' M (v 5 +' v 11)) ;;
  .store (v 5 +' v 3) (v 7) ;;
  .store (v 5 +' v 3 +' k 1) (v 8) ;;
  .set 0 (k 0)

def time (J V : ℕ) : ℕ := LightOutputDecodeDigits.time J V+30*J+150
def word (V radix J : ℕ) : ℕ := LightOutputDecodeDigits.word V radix J
def space (work V : ℕ) : ℕ := LightOutputDecodeDigits.space work V

def Row (μ : ℕ→ℤ) (dst J : ℕ) (f : Coordinate J→ℤ) : Prop :=
  (∀ j : Fin J, μ (dst+J-1-j.val)=f (.inl j)) ∧
    μ (dst+J)=f (.inr false) ∧ μ (dst+J+1)=f (.inr true)

structure Procs (P : Program) (pMain : ℕ) where
  pDigits : ℕ
  pDivide : ℕ
  main : P[pMain]?=some (body pDigits)
  digits : P[pDigits]?=some (LightOutputDecodeDigits.body pDivide)
  divide : P[pDivide]?=some LightOutputDecodeDivide.body

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ→ℤ} {J radix dst work V value offset : ℕ} {x sign tag0 tag1 : ℤ}
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+2<lim.depth)
    (hb : 1≤radix) (hval : value≤V) (hshift : x+(offset : ℤ)=(value : ℤ))
    (hx : |x|≤(V : ℤ)) (hoff : offset≤V)
    (hsign : |sign|≤1) (ht0 : |tag0|≤1) (ht1 : |tag1|≤1)
    (hsep : dst+J+2≤work) (hspace : space work V≤lim.space)
    (hword : (word V radix J : ℤ)≤lim.word) :
    Meets lim P pMain d [x,offset,sign,J,radix,dst,work,tag0,tag1] μ (time J V)
      (fun _ ν =>
        (∀ j<J, ν (dst+j)=sign*((OutputDecodeOrder.indices radix J value).getD j 0 : ℤ)) ∧
        ν (dst+J)=tag0 ∧ ν (dst+J+1)=tag1 ∧ Kept μ ν dst) := by
  have hbudget (z : ℕ) (hz : z≤word V radix J) : (z : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr hz).trans hword
  have hV := hbudget V (by unfold word LightOutputDecodeDigits.word; omega)
  have hB := hbudget radix (by unfold word LightOutputDecodeDigits.word; omega)
  have hJ := hbudget J (by unfold word LightOutputDecodeDigits.word; omega)
  have h1 := hbudget 1 (by unfold word LightOutputDecodeDigits.word; omega)
  have hOff : (offset : ℤ)≤lim.word := (Int.ofNat_le.mpr hoff).trans hV
  have hVal : (value : ℤ)≤lim.word := (Int.ofNat_le.mpr hval).trans hV
  have hwork : work≤lim.space := by unfold space LightOutputDecodeDigits.space at hspace; omega
  have hdst : dst+J≤lim.space := by omega
  have hx' := abs_le.mp hx
  have hsign' := abs_le.mp hsign
  have ht0' := abs_le.mp ht0
  have ht1' := abs_le.mp ht1
  apply Meets.of_body S.main
  unfold body time
  light_set (value : ℕ) using hshift,LightOutputDecodeDigits.time
  light_call (LightOutputDecodeDigits.meets (d := d+1) (μ := μ) (J := J)
    (m := radix) (k := value) (dst := dst) (work := work) S.digits S.divide
    hw (by omega) hb hval (by omega) hspace hword)
    using LightOutputDecodeDigits.time with q ν ⟨hq,hread,hkeep⟩
  let f : ℕ→ℤ := fun j => sign*((OutputDecodeOrder.indices radix J value).getD j 0 : ℤ)
  refine Ends.pieceThen (Ends.pass (T := 30*J+10)
    (Q := fun σ => σ=⟨Function.update
      (frame (setLocal (setLocal [x,offset,sign,J,radix,dst,work,tag0,tag1] 9 value) 10 q))
      11 (J : ℤ),wrote ν dst f J⟩) f ?round ?done hw hdst rfl rfl) ?finish
  case round =>
    intro j hj
    have hlt := OutputDecodeOrder.indices_getD_lt (k := value) (show 0<radix by omega) hj
    have hcell := hread j hj
    have hcur : wrote ν dst f j (dst+j)=ν (dst+j) := wrote_rest (by omega)
    have hcur' : wrote ν dst (fun j =>
        sign*((OutputDecodeOrder.indices radix J value).getD j 0 : ℤ)) j (dst+j)=
          ((OutputDecodeOrder.indices radix J value).getD j 0 : ℤ) := hcur.trans hcell
    have hd0 : (0 : ℤ)≤(OutputDecodeOrder.indices radix J value).getD j 0 := by positivity
    have hdB : ((OutputDecodeOrder.indices radix J value).getD j 0 : ℤ)≤radix := by exact_mod_cast hlt.le
    have hprod : |sign*((OutputDecodeOrder.indices radix J value).getD j 0 : ℤ)|≤lim.word := by
      rw [abs_mul,abs_of_nonneg hd0]
      exact (mul_le_mul hsign hdB hd0 (by norm_num : (0 : ℤ)≤1)).trans (by simpa using hB)
    have hprod' := abs_le.mp hprod
    simp only [List.getD_eq_getElem?_getD] at hcur' hprod' hcell hd0 hdB
    light_side [f,hcur',hcell]
  case done => rfl
  case finish =>
    rintro _ rfl
    rw [update_frame_setLocal]
    light_store (dst+J) tag0
    light_store (dst+J+1) tag1
    light_set (0 : ℤ)
    refine ⟨?_,?_,?_,?_⟩
    · intro j hj
      dsimp only
      rw [Function.update_of_ne (show dst+j≠dst+J+1 by omega),
        Function.update_of_ne (show dst+j≠dst+J by omega),wrote_done hj]
    · simp only [Function.update_of_ne (by omega : dst+J≠dst+J+1),Function.update_self]
    · simp
    · intro a ha
      dsimp only
      rw [Function.update_of_ne (show a≠dst+J+1 by omega),
        Function.update_of_ne (show a≠dst+J by omega),wrote_rest (by omega),hkeep a ha]

theorem Procs.left_meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ→ℤ} {J radix dst work U : ℕ} {b : ℤ}
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+2<lim.depth) (hb : 1≤radix)
    (hB : |b|≤(U : ℤ)) (hsep : dst+J+2≤work)
    (hspace : space work (3*U)≤lim.space) (hword : (word (3*U) radix J : ℤ)≤lim.word) :
    Meets lim P pMain d [b,U,-1,J,radix,dst,work,1,0] μ (time J (3*U))
      (fun _ ν => Row ν dst J (leftRaw U radix J b) ∧ Kept μ ν dst) := by
  have hs := shiftOne_cast hB
  have hU : (0 : ℤ)≤U := by positivity
  have hbounds := abs_le.mp hB
  have hv : shiftOne U b≤3*U := by exact_mod_cast (by omega : (shiftOne U b : ℤ)≤3*U)
  have hh := S.meets (μ := μ) hw hd hb hv (by omega) (hB.trans (by omega))
    (by omega : U≤3*U) (by norm_num : |(-1 : ℤ)|≤1)
    (by norm_num : |(1 : ℤ)|≤1) (by norm_num : |(0 : ℤ)|≤1) hsep hspace hword
  apply hh.mono le_rfl
  rintro r ν ⟨hread,ht0,ht1,hkeep⟩
  refine ⟨⟨?_,ht0,ht1⟩,hkeep⟩
  intro j
  have hj : J-1-j.val<J := by omega
  have he : dst+(J-1-j.val)=dst+J-1-j.val := by omega
  rw [← he,hread _ hj,OutputDecodeOrder.indices_getD_reverse radix J (shiftOne U b) j.isLt]
  simp only [leftRaw,neg_one_mul,TernarySignedDigits.digit,TernarySignedDigits.quotient]

theorem Procs.right_meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ→ℤ} {J radix dst work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+2<lim.depth) (hb : 1≤radix)
    (hC : |c|≤(U : ℤ)) (hsep : dst+J+2≤work)
    (hspace : space work (3*U)≤lim.space) (hword : (word (3*U) radix J : ℤ)≤lim.word) :
    Meets lim P pMain d [c,2*U,1,J,radix,dst,work,0,1] μ (time J (3*U))
      (fun _ ν => Row ν dst J (rightRaw U radix J c) ∧ Kept μ ν dst) := by
  have hs := shiftTwo_cast hC
  have hU : (0 : ℤ)≤U := by positivity
  have hbounds := abs_le.mp hC
  have hv : shiftTwo U c≤3*U := by exact_mod_cast (by omega : (shiftTwo U c : ℤ)≤3*U)
  have hh := S.meets (μ := μ) hw hd hb hv (by push_cast; omega) (hC.trans (by omega))
    (by omega : 2*U≤3*U) (by norm_num : |(1 : ℤ)|≤1)
    (by norm_num : |(0 : ℤ)|≤1) (by norm_num : |(1 : ℤ)|≤1) hsep hspace hword
  apply hh.mono le_rfl
  rintro r ν ⟨hread,ht0,ht1,hkeep⟩
  refine ⟨⟨?_,ht0,ht1⟩,hkeep⟩
  intro j
  have hj : J-1-j.val<J := by omega
  have he : dst+(J-1-j.val)=dst+J-1-j.val := by omega
  rw [← he,hread _ hj,OutputDecodeOrder.indices_getD_reverse radix J (shiftTwo U c) j.isLt]
  simp only [rightRaw,one_mul,TernarySignedDigits.digit,TernarySignedDigits.quotient]

def program : Program := [body 1,LightOutputDecodeDigits.body 2,LightOutputDecodeDivide.body]
def procs : Procs program 0 := ⟨1,2,rfl,rfl,rfl⟩

end ThreeSum.LightTernarySignedRow
