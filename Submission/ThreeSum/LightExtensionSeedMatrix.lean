import Submission.ThreeSum.LightExtensionSeedRow

namespace ThreeSum.LightExtensionSeedMatrix
open Light
set_option maxHeartbeats 3000000

def body (pRow pDigit pDivide : ℕ) : Stmt :=
  .set 5 (v 1 *' v 1) ;;
  .for 6 (v 5) (
    .call pDivide [v 6,v 1] 7 ;;
    .call pDigit [v 6,k 1,v 1] 8 ;;
    .call pRow [v 0,v 1,v 2,v 7,v 8,v 3 +' v 6 *' v 4,v 4] 9)

def value (mul : ℕ → ℕ → ℕ) (q p row col : ℕ) : ℕ :=
  LightExtensionSeedRow.trajectory mul (row/q) (row%q) col % p

def time (len q : ℕ) : ℕ := q*q*(LightExtensionSeedRow.time len q+60*(q*q)+400)+30

def word (len q p : ℕ) : ℕ := 30*(q*q+q+p+q*q*len+len+10)

def Inv (μ : ℕ → ℤ) (table q p dst len : ℕ) (mul : ℕ → ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (x y z : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [table,q,p,dst,len,q*q,i,x,y,z],ν⟩ ∧
    (∀ r  <  i, ∀ j < len, ν (dst+r*len+j)=(value mul q p r j : ℤ)) ∧
    SameOutside μ ν dst (q*q*len)

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem meets {proc pRow pDigit pDivide table q p dst len : ℕ}
    (hp : P[proc]?=some (body pRow pDigit pDivide))
    (hrow : P[pRow]?=some (LightExtensionSeedRow.body pDigit))
    (hdigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (mul : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+2 < lim.depth)
    (hq : 0 < q) (hmod : 0 < p)
    (htable : table+q*q ≤ dst) (hspace : dst+q*q*len ≤ lim.space)
    (hread : ∀ a < q, ∀ b < q, μ (table+a*q+b)=(mul a b : ℤ))
    (hmul : ∀ a < q, ∀ b < q, mul a b < q)
    (hword : (word len q p : ℤ) ≤ lim.word) :
    Meets lim P proc depth [table,q,p,dst,len] μ (time len q)
      (fun _ ν => (∀ i < q*q, ∀ j < len, ν (dst+i*len+j)=(value mul q p i j : ℤ)) ∧
        SameOutside μ ν dst (q*q*len)) := by
  have hb (z : ℕ) (hz : z ≤ word len q p) : (z : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hz).trans hword
  have hqWord := hb q (by unfold word; omega)
  have hpWord := hb p (by unfold word; omega)
  have hQQWord := hb (q*q) (by unfold word; omega)
  have hprod : q*q*len ≤ word len q p := by unfold word; omega
  have h1 : (1 : ℤ) ≤ lim.word := by unfold word at hword; omega
  apply Meets.of_body hp
  unfold body time
  light_set (q*q : ℕ)
  refine Ends.for (Inv μ table q p dst len mul) (q*q)
    (LightExtensionSeedRow.time len q+60*(q*q)+390) ?start ?round ?done ?bound
  case start =>
    refine ⟨0,0,0,μ,?_,?_,SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 3).symm)
    · intro r hr; omega
  case round =>
    rintro i _ hi _ ⟨oldX,oldY,oldZ,ν,rfl,written,kept⟩
    have hquotient : i/q ≤ i := Nat.div_le_self i q
    have hquotientInt : (i : ℤ)/(q : ℤ) ≤ (i : ℤ) := by exact_mod_cast hquotient
    have hx : i/q < q := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    have hy : i%q < q := Nat.mod_lt _ hq
    have hiWord := hb i (by unfold word; omega)
    have hxWord := (Int.ofNat_le.mpr hx.le).trans hqWord
    have hyWord := (Int.ofNat_le.mpr hy.le).trans hqWord
    have hdivWord := hb (i+q+2) (by unfold word; omega)
    have hdigitWord : (LightRadixDigit.word i 1 q : ℤ) ≤ lim.word := by
      apply hb; unfold LightRadixDigit.word word; omega
    have hrowWord : (LightExtensionSeedRow.word len q p : ℤ) ≤ lim.word := by
      apply hb; unfold LightExtensionSeedRow.word word; omega
    have hdivideTime : LightSmallDivide.time i q ≤ 20*(q*q)+40 :=
      (LightSmallDivide.time_bound i q).trans (by omega)
    have hdigitTime : LightRadixDigit.time i ≤ 40*(q*q)+140 := by unfold LightRadixDigit.time; omega
    have hrowEnd : i*len+len ≤ q*q*len := by
      have hm := Nat.mul_le_mul_right len (show i+1 ≤ q*q by omega)
      nlinarith
    have hoffWord := hb (i*len) (by omega)
    have haddrWord : ((dst+i*len : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (show dst+i*len ≤ lim.space by omega)).trans hw
    have hreadν (a : ℕ) (ha : a < q) (b : ℕ) (hbb : b < q) : ν (table+a*q+b)=(mul a b : ℤ) := by
      have hoff : a*q+b < q*q := by nlinarith
      rw [kept _ (Or.inl (by omega)),hread a ha b hbb]
    light_call (LightSmallDivide.meets (d := depth+1) (a := i) (b := q) hdivide ν hdivWord)
      using LightSmallDivide.time,LightRadixDigit.time,LightExtensionSeedRow.time,pow_two,Nat.mul_assoc
      with X ν₁ ⟨hX,hν₁⟩
    subst ν₁
    subst X
    light_call (LightRadixDigit.meets (d := depth+1) (k := i) (b := 1) (p := q) hdigit hdivide ν (by omega) hdigitWord)
      using LightSmallDivide.time,LightRadixDigit.time,LightExtensionSeedRow.time,pow_two,Nat.mul_assoc
      with Y ν₂ ⟨hY,hν₂⟩
    subst ν₂
    have hY' : Y=((i%q : ℕ) : ℤ) := by simpa using hY
    subst Y
    light_call (LightExtensionSeedRow.meets (depth := depth+1) (table := table) (q := q) (p := p)
      (x := i/q) (y := i%q) (dst := dst+i*len) (len := len)
      hrow hdigit hdivide ν mul hw (by omega) hx hy hmod (by omega) (by omega) hreadν hmul hrowWord)
      using LightSmallDivide.time,LightRadixDigit.time,LightExtensionSeedRow.time,pow_two,Nat.mul_assoc
      with Z ξ ⟨hZ,hvalues,hkeep⟩
    refine ⟨by simp,(i/q : ℕ),(i%q : ℕ),Z,ξ,by simp [update_frame_setLocal],?_,?_⟩
    · intro r hr j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · have hoff : r*len+j <  i*len := by
          have hm := Nat.mul_le_mul_right len (show r+1 ≤  i by omega)
          nlinarith
        rw [hkeep _ (Or.inl (by omega)),written r hr j hj]
      · simpa [value,Nat.add_assoc] using hvalues j hj
    · intro a ha
      rw [hkeep a (by omega),kept a ha]
  case done => rintro _ _ ⟨X,Y,Z,ν,rfl,written,kept⟩; exact ⟨written,kept⟩
  case bound => rintro i _ _ _ ⟨X,Y,Z,ν,rfl,_,_⟩; light_side

def program : Program := [body 1 2 3,LightExtensionSeedRow.body 2,LightRadixDigit.body 3,LightSmallDivide.body]

end ThreeSum.LightExtensionSeedMatrix
