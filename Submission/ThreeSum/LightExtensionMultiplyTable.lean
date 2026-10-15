import Submission.ThreeSum.LightExtensionMultiplyCell

noncomputable section
namespace ThreeSum.LightExtensionMultiplyTable
noncomputable local instance (Q : Prop) : Decidable Q := Classical.propDecidable Q
open Light
set_option maxHeartbeats 3000000

/-- q,context,p,dimension,powers,left,right,table. -/
def body (pCell pDigit pDivide : ℕ) : Stmt :=
  .set 8 (v 0 *' v 0) ;;
  .for 9 (v 8) (
    .call pDivide [v 9,v 0] 10 ;;
    .call pDigit [v 9,k 1,v 0] 11 ;;
    .call pCell [v 10,v 11,v 1,v 2,v 3,v 4,v 5,v 6,v 0] 12 ;;
    .store (v 7 +' v 9) (v 12))

def time (q T : ℕ) : ℕ := q*q*(T+60*(q*q)+400)+30

def word (q ctx p dim powers a b : ℕ) : ℕ :=
  30*(q*q+q+p+dim+10)

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem meets {proc pCell pDigit pDivide q ctx p dim powers a b table T : ℕ}
    (hp : P[proc]?=some (body pCell pDigit pDivide))
    (hdigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (mul : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+1 < lim.depth)
    (hq : 0 < q) (hspace : table+q*q ≤ lim.space)
    (hctxSpace : ctx ≤ lim.space) (hpowersSpace : powers ≤ lim.space)
    (haSpace : a ≤ lim.space) (hbSpace : b ≤ lim.space)
    (hword : (word q ctx p dim powers a b : ℤ) ≤ lim.word)
    (hmul : ∀ x < q, ∀ y < q, mul x y < q)
    (hcell : ∀ x < q, ∀ y < q, ∀ ν, Kept μ ν table →
      Meets lim P pCell (depth+1) [x,y,ctx,p,dim,powers,a,b,q] ν T
        (fun z ξ => z=(mul x y : ℤ) ∧ Kept ν ξ (table+q*q))) :
    Meets lim P proc depth [q,ctx,p,dim,powers,a,b,table] μ (time q T)
      (fun _ ν => (∀ x < q, ∀ y < q, ν (table+x*q+y)=(mul x y : ℤ)) ∧
        Kept μ ν table) := by
  have hb (z : ℕ) (hz : z ≤ word q ctx p dim powers a b) : (z : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hz).trans hword
  have hctxWord := (Int.ofNat_le.mpr hctxSpace).trans hw
  have hpowersWord := (Int.ofNat_le.mpr hpowersSpace).trans hw
  have haWord := (Int.ofNat_le.mpr haSpace).trans hw
  have hbWord := (Int.ofNat_le.mpr hbSpace).trans hw
  have hqWord := hb q (by unfold word; omega)
  have hQQWord := hb (q*q) (by unfold word; omega)
  apply Meets.of_body hp
  unfold body time
  light_set (q*q : ℕ)
  refine Ends.for (fun i σ => ∃ X Y Z ν,
      σ=⟨frame [q,ctx,p,dim,powers,a,b,table,q*q,i,X,Y,Z],ν⟩ ∧
      (∀ j < i, ν (table+j)=(mul (j/q) (j%q) : ℤ)) ∧ Kept μ ν table)
    (q*q) (T+60*(q*q)+390) ?start ?round ?done ?bound
  case start =>
    refine ⟨0,0,0,μ,?_,?_,SameOn.refl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 3).symm)
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨oldX,oldY,oldZ,ν,rfl,written,kept⟩
    have hx : i/q < q := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    have hy : i%q < q := Nat.mod_lt _ hq
    have hquotient : i/q ≤ i := Nat.div_le_self i q
    have hquotientInt : (i : ℤ)/(q : ℤ) ≤ (i : ℤ) := by exact_mod_cast hquotient
    have hiWord := hb i (by unfold word; omega)
    have hdivWord := hb (i+q+2) (by unfold word; omega)
    have hdigitWord : (LightRadixDigit.word i 1 q : ℤ) ≤ lim.word := by
      apply hb; unfold LightRadixDigit.word word; omega
    have hmulWord : (mul (i/q) (i%q) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hmul _ hx _ hy).le).trans hqWord
    have haddrWord : ((table+i : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (show table+i ≤ lim.space by omega)).trans hw
    light_call (LightSmallDivide.meets (d := depth+1) (a := i) (b := q) hdivide ν hdivWord)
      using LightSmallDivide.time,LightRadixDigit.time,pow_two,Nat.mul_assoc
      with X ν₁ ⟨hX,hν₁⟩
    subst ν₁; subst X
    light_call (LightRadixDigit.meets (d := depth+1) (k := i) (b := 1) (p := q)
      hdigit hdivide ν (by omega) hdigitWord)
      using LightSmallDivide.time,LightRadixDigit.time,pow_two,Nat.mul_assoc
      with Y ν₂ ⟨hY,hν₂⟩
    subst ν₂
    have hY' : Y=((i%q : ℕ) : ℤ) := by simpa using hY
    subst Y
    light_call (hcell _ hx _ hy ν kept) using LightSmallDivide.time,LightRadixDigit.time,pow_two,Nat.mul_assoc with Z ξ ⟨hZ,hkeep⟩
    subst Z
    light_store (table+i) (mul (i/q) (i%q)) using LightSmallDivide.time,LightRadixDigit.time,pow_two,Nat.mul_assoc
    refine ⟨by simp,(i/q : ℕ),(i%q : ℕ),(mul (i/q) (i%q) : ℕ),
      Function.update ξ (table+i) (mul (i/q) (i%q)),by simp [update_frame_setLocal],?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega),hkeep _ (by omega),written j hj]
      · simp
    · intro c hc
      rw [Function.update_of_ne (by omega),hkeep c (by omega),kept c hc]
  case done =>
    rintro _ _ ⟨X,Y,Z,ν,rfl,written,kept⟩
    refine ⟨?_,kept⟩
    intro x hx y hy
    have hj : x*q+y < q*q := by nlinarith
    have hx' : (x*q+y)/q=x := by
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ hq,Nat.div_eq_of_lt hy,Nat.zero_add]
    have hy' : (x*q+y)%q=y := by rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hy]
    simpa [hx',hy',Nat.add_assoc] using written (x*q+y) hj
  case bound => rintro i _ _ _ ⟨X,Y,Z,ν,rfl,_,_⟩; light_side

/-- Every scalar multiplication is the concrete exhaustive quotient search. -/
def program : Program := LightExtensionMultiplyCell.program++[body 13 2 3]

theorem program_meets {ctx q table depth : ℕ}
    (C : LightExtensionQuotientPredicate.Layout) (μ : ℕ → ℤ)
    (f : ℕ → ℕ) (mul : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+8 < lim.depth)
    (hp : 1 < C.p) (hq : 0 < q)
    (H : Seg μ ctx (LightExtensionQuotientPredicate.header C))
    (hctx : ctx+10 ≤ table) (hpow : C.powers+(2*C.dim+1) ≤ table)
    (hmod : C.modulus+(C.dim+1) ≤ table)
    (htable : table+q*q ≤ C.a) (hab : C.a+C.dim ≤ C.b) (hbh : C.b+C.dim ≤ C.h)
    (hh : C.h+C.dim ≤ C.remainder) (hr : C.remainder+2*C.dim ≤ C.productWork)
    (hprod : C.productWork+2*C.dim ≤ C.sumWork)
    (hspace : C.sumWork+2*C.dim ≤ lim.space)
    (hpowRead : ∀ i ≤ 2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ))
    (hfRead : ∀ i < C.dim+1, μ (C.modulus+i)=(f i : ℤ))
    (hfBound : ∀ i < C.dim+1, f i < C.p)
    (hword : (word q ctx C.p C.dim C.powers C.a C.b : ℤ) ≤ lim.word)
    (hcellWord : (LightExtensionMultiplyCell.word C q ctx : ℤ) ≤ lim.word)
    (hmul : ∀ x < q, ∀ y < q, mul x y < q)
    (hspec : ∀ a < q, ∀ b < q,
      let z := LightPairSearch.first (LightPairSearch.goodCode q
        (LightExtensionQuotientSearch.good C (LightExtensionQuotientPredicate.digits C.p a)
          (LightExtensionQuotientPredicate.digits C.p b) f)) (q*q)
      0 < z ∧ z ≤ q*q ∧ (z-1)%q=mul a b) :
    Meets lim program 14 depth [q,ctx,C.p,C.dim,C.powers,C.a,C.b,table] μ
      (time q (LightExtensionMultiplyCell.time C q))
      (fun _ ν => (∀ x < q, ∀ y < q, ν (table+x*q+y)=(mul x y : ℤ)) ∧
        Kept μ ν table) := by
  apply meets rfl rfl rfl μ mul hw (by omega) hq (by omega)
    (by omega) (by omega) (by omega) (by omega) hword hmul
  intro x hx y hy ν hν
  have Hν := LightExtensionQuotientPredicate.header_kept H hctx hν
  have hpν (i : ℕ) (hi : i ≤ 2*C.dim) :=
    (hν _ (by omega)).trans (hpowRead i hi)
  have hfν (i : ℕ) (hi : i < C.dim+1) :=
    (hν _ (by omega)).trans (hfRead i hi)
  have hc := (LightExtensionMultiplyCell.program_meets C ν f mul hw (by omega) hp hq hx hy
    Hν (by omega) (by omega) (by omega) hab hbh hh hr hprod hspace hpν hfν hfBound hcellWord hspec).append
      [body 13 2 3]
  apply hc.mono (by rfl)
  rintro z ξ ⟨hz,hkeep⟩
  exact ⟨hz,fun a ha => hkeep a (by omega)⟩

end ThreeSum.LightExtensionMultiplyTable

