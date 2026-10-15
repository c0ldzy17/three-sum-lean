import Submission.ThreeSum.LightTernaryCodes

/-! # Constructing the four compact ternary coordinate metadata rows in RAM -/

namespace ThreeSum.LightTernaryMetadata

open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase

set_option maxHeartbeats 3000000

variable {lim : Limits} {P : Program}

def roundBody (pZero pDigit pErase : ℕ) : Stmt :=
  .set 8 (M (v 3 +' v 7)) ;;
  .call pZero [v 0,v 1,v 2,v 8,v 5] 9 ;;
  .call pErase [v 0,v 2,v 8,v 0,v 5] 10 ;;
  .call pDigit [v 0,v 1,v 2,v 8,v 5] 11 ;;
  .store (v 6 +' v 7) (v 11) ;;
  .store (v 6 +' v 4 +' v 7) (v 9) ;;
  .store (v 6 +' k 2 *' v 4 +' v 7) (v 10) ;;
  .store (v 6 +' k 3 *' v 4 +' v 7) (v 8)

def body (pZero pDigit pErase : ℕ) : Stmt :=
  .for 7 (v 4) (roundBody pZero pDigit pErase)

def roundTime (W : ℕ) : ℕ := LightTernaryCodes.zeroTime W +
  LightMaskErase.time W + LightTernaryCodes.digitTime W + 200

def time (W n : ℕ) : ℕ := n * (roundTime W + 20) + 20

def RecordAt (μ : ℕ → ℤ) (base n j W low high : ℕ) (m : ℕ) : Prop :=
  μ (base+j) = (LightTernaryCodes.digit W low high m : ℤ) ∧
  μ (base+n+j) = (LightTernaryCodes.zeroCode W low high m : ℤ) ∧
  μ (base+2*n+j) = (LightTernaryCodes.oneCode W high m : ℤ) ∧
  μ (base+3*n+j) = (m : ℤ)

def writeRecord (μ : ℕ → ℤ) (base n j : ℕ) (q z0 z1 m : ℤ) : ℕ → ℤ :=
  Function.update (Function.update (Function.update (Function.update μ
    (base+j) q) (base+n+j) z0) (base+2*n+j) z1) (base+3*n+j) m

theorem writeRecord_current {μ : ℕ → ℤ} {base n j W low high m : ℕ} (hj : j < n) :
    RecordAt (writeRecord μ base n j (LightTernaryCodes.digit W low high m)
      (LightTernaryCodes.zeroCode W low high m) (LightTernaryCodes.oneCode W high m) m)
      base n j W low high m := by
  unfold RecordAt writeRecord
  simp only [Function.update_self, Function.update_of_ne (by omega :
      base+j ≠ base+3*n+j), Function.update_of_ne (by omega :
      base+j ≠ base+2*n+j), Function.update_of_ne (by omega :
      base+j ≠ base+n+j), Function.update_of_ne (by omega :
      base+n+j ≠ base+3*n+j), Function.update_of_ne (by omega :
      base+n+j ≠ base+2*n+j), Function.update_of_ne (by omega :
      base+2*n+j ≠ base+3*n+j), and_self]

theorem writeRecord_before {μ : ℕ → ℤ} {base n j k W low high m : ℕ}
    {q z0 z1 v : ℤ} (hk : k < j) (hj : j < n)
    (h : RecordAt μ base n k W low high m) :
    RecordAt (writeRecord μ base n j q z0 z1 v) base n k W low high m := by
  rcases h with ⟨h0,h1,h2,h3⟩
  unfold RecordAt writeRecord
  simp only [Function.update_apply]
  split_ifs <;> omega

theorem writeRecord_kept {μ : ℕ → ℤ} {base n j : ℕ} {q z0 z1 m : ℤ}
    (hj : j < n) : SameOutside μ (writeRecord μ base n j q z0 z1 m) base (4*n) := by
  intro x hx
  unfold writeRecord
  rw [Function.update_of_ne (by rcases hx with h | h <;> omega),
    Function.update_of_ne (by rcases hx with h | h <;> omega),
    Function.update_of_ne (by rcases hx with h | h <;> omega),
    Function.update_of_ne (by rcases hx with h | h <;> omega)]

def Inv (μ : ℕ → ℤ) (W low high a n powers base : ℕ) (codes : ℕ → ℕ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ (m z0 z1 q : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,low,high,a,n,powers,base,j,m,z0,z1,q],μ'⟩ ∧
    SameOutside μ μ' base (4*n) ∧
    ∀ k < j, RecordAt μ' base n k W low high (codes k)

theorem meets {pMain pZero pDigit pErase W low high a n powers base d : ℕ}
    (hmain : P[pMain]? = some (body pZero pDigit pErase))
    (hzero : P[pZero]? = some (LightTernaryCodes.zeroBody pErase))
    (hdigit : P[pDigit]? = some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (codes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ base) (hb : base+4*n ≤ powers)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (a+j) = (codes j : ℤ))
    (hpowers : Powers μ powers W)
    (hcodes : ∀ j < n, codes j < 2^W)
    (hlow : low ≤ W) (hhigh : high ≤ W) (hd : d+W+2 ≤ lim.depth) :
    Meets lim P pMain d [W,low,high,a,n,powers,base] μ (time W n)
      (fun _ μ' => (∀ j < n, RecordAt μ' base n j W low high (codes j)) ∧
        SameOutside μ μ' base (4*n)) := by
  have htwo : 2 ≤ lim.word := by
    have h : 2^1 ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast h : (2 : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ W low high a n powers base codes) n (roundTime W)
    ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,0,0,0,μ,?_,SameOn.refl,?_⟩
    · simp [update_frame_setLocal]
      change frame [(W : ℤ),low,high,a,n,powers,base,0] =
        frame ([(W : ℤ),low,high,a,n,powers,base,0] ++ [0,0,0,0])
      exact (frame_append_zeros _ 4).symm
    · intro k hk
      omega
  case round =>
    rintro j _ hj _ ⟨m,z0,z1,q,μ',rfl,hkeep,hrows⟩
    have hreadj : μ' (a+j) = (codes j : ℤ) :=
      (hkeep _ (Or.inl (by omega))).trans (hread j hj)
    have hp : Powers μ' powers W := by
      intro k hk
      rw [hkeep _ (Or.inr (by omega)),hpowers k hk]
    have hm := hcodes j hj
    have hmword : (codes j : ℤ) < lim.word := by
      have hpow : 2^W ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
      exact (Int.ofNat_lt.mpr hm).trans_le ((Int.ofNat_le.mpr hpow).trans hword)
    have hzc := LightTernaryCodes.zero_meets (d := d+1) hzero herase μ'
      hw hspace hword hp hlow hhigh hm (by omega)
    have hoc := LightMaskErase.meets herase μ' hw hspace hword hp
      W high (codes j) le_rfl hhigh hm (d+1) (by omega)
    have hdc := LightTernaryCodes.digit_meets (d := d+1) hdigit herase μ'
      hw hspace hword hp hlow hhigh hm (by omega) htwo
    have hzle := eraseMask_le (a := low) ((eraseMask_le (a := high) hm).trans_lt hm)
    have hole := eraseMask_le (a := high) hm
    have hdle := LightTernaryCodes.digit_le_two W low high (codes j)
    unfold roundBody roundTime
    light_set (codes j : ℕ) using hreadj,LightTernaryCodes.zeroTime,
      LightTernaryCodes.digitTime,LightMaskErase.time
    light_call hzc using LightTernaryCodes.zeroTime,LightTernaryCodes.digitTime,
      LightMaskErase.time with zr μ0 ⟨hzr,hm0⟩
    subst μ0
    light_call hoc using LightTernaryCodes.zeroTime,LightTernaryCodes.digitTime,
      LightMaskErase.time with one μ1 ⟨hor,hm1⟩
    subst μ1
    light_call hdc using LightTernaryCodes.zeroTime,LightTernaryCodes.digitTime,
      LightMaskErase.time with dr μ2 ⟨hdr,hm2⟩
    subst μ2
    light_store (base+j) (LightTernaryCodes.digit W low high (codes j) : ℕ)
      using hdr,LightTernaryCodes.zeroTime,LightTernaryCodes.digitTime,LightMaskErase.time
    light_store (base+n+j) (LightTernaryCodes.zeroCode W low high (codes j) : ℕ)
      using hzr,LightTernaryCodes.zeroCode,LightTernaryCodes.zeroTime,
        LightTernaryCodes.digitTime,LightMaskErase.time
    light_store (base+2*n+j) (LightTernaryCodes.oneCode W high (codes j) : ℕ)
      using hor,LightTernaryCodes.oneCode,LightTernaryCodes.zeroTime,
        LightTernaryCodes.digitTime,LightMaskErase.time
    light_store (base+3*n+j) (codes j : ℕ)
      using LightTernaryCodes.zeroTime,LightTernaryCodes.digitTime,LightMaskErase.time
    let μ'' := writeRecord μ' base n j (LightTernaryCodes.digit W low high (codes j))
      (LightTernaryCodes.zeroCode W low high (codes j))
      (LightTernaryCodes.oneCode W high (codes j)) (codes j)
    refine ⟨by simp,(codes j : ℤ),zr,one,dr,μ'',?_,?_,?_⟩
    · simp [update_frame_setLocal, μ'', writeRecord]
    · intro x hx
      exact (writeRecord_kept hj x hx).trans (hkeep x hx)
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact writeRecord_before hk hj (hrows k hk)
      · exact writeRecord_current hj
  case done =>
    rintro _ _ ⟨m,z0,z1,q,μ',rfl,hkeep,hrows⟩
    exact ⟨hrows,hkeep⟩
  case bound =>
    rintro j _ hj _ ⟨m,z0,z1,q,μ',rfl,hkeep,hrows⟩
    light_side

def program : Program := [body 1 2 3, LightTernaryCodes.zeroBody 3,
  LightTernaryCodes.digitBody 3,LightMaskErase.body 3]

theorem time_bound (W n : ℕ) : time W n ≤ 1000*(W+1)*(n+1) := by
  unfold time roundTime LightTernaryCodes.zeroTime LightTernaryCodes.digitTime
    LightMaskErase.time
  nlinarith

end ThreeSum.LightTernaryMetadata
