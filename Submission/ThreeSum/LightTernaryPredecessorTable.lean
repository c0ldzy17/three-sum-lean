import Submission.ThreeSum.LightTernaryPredecessor

/-! Actual strided Euler weight/address metadata for one coordinate. -/

namespace ThreeSum.LightTernaryPredecessorTable

open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def roundBody (pCell pDigit : ℕ) : Stmt :=
  .set 18 (M (v 3 +' v 17)) ;;
  .call pCell [v 0,v 1,v 2,v 18,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14] 19 ;;
  .call pDigit [k 2 *' v 0,v 1,v 2,v 18,v 5] 20 ;;
  .set 20 (v 14 *' v 20) ;;
  .store (v 15 +' v 16 *' v 17) (v 20) ;;
  .store (v 15 +' v 16 *' v 4 +' v 16 *' v 17) (v 19)

/-- With stride N and destination ws+i, this writes the i-th coordinate
directly into the row-major Euler rows; the address rows follow the weights. -/
def body (pCell pDigit : ℕ) : Stmt := .for 17 (v 4) (roundBody pCell pDigit)

def time (N L n : ℕ) : ℕ :=
  n*(LightTernaryPredecessor.time N L+LightTernaryCodes.digitTime (2*N)+200)+20

def RecordAt (μ : ℕ → ℤ) (dst stride n j N low high m T active bv nv bi ni : ℕ) : Prop :=
  μ (dst+stride*j)=(weight N low high m active : ℤ) ∧
  μ (dst+stride*n+stride*j)=(key N low high m T active bv nv bi ni : ℤ)

def writeRecord (μ : ℕ → ℤ) (dst stride n j : ℕ) (w k : ℤ) : ℕ → ℤ :=
  Function.update (Function.update μ (dst+stride*j) w) (dst+stride*n+stride*j) k

/-- Exact preservation of every address outside the two strided columns. -/
def KeptApart (μ ν : ℕ → ℤ) (dst stride n : ℕ) : Prop :=
  ∀ x, (∀ j<n, x≠dst+stride*j ∧ x≠dst+stride*n+stride*j) → ν x=μ x

theorem keptApart_refl (μ : ℕ → ℤ) (dst stride n : ℕ) : KeptApart μ μ dst stride n :=
  fun _ _ => rfl

theorem writeRecord_kept {μ : ℕ → ℤ} {dst stride n j : ℕ} {w k : ℤ} (hj : j<n) :
    KeptApart μ (writeRecord μ dst stride n j w k) dst stride n := by
  intro x hx
  unfold writeRecord
  rw [Function.update_of_ne (hx j hj).2,Function.update_of_ne (hx j hj).1]

theorem keptApart_outside {μ ν : ℕ → ℤ} {dst stride n : ℕ}
    (hs : 0<stride) (H : KeptApart μ ν dst stride n) : SameOutside μ ν dst (2*stride*n) := by
  intro x hx
  rw [Nat.mul_assoc] at hx
  apply H
  intro j hj
  have hjn : stride*j<stride*n := Nat.mul_lt_mul_of_pos_left hj hs
  rcases hx with h | h <;> constructor <;> omega

theorem writeRecord_current {μ : ℕ → ℤ} {dst stride n j N low high m T active bv nv bi ni : ℕ}
    (hs : 0<stride) (hj : j<n) :
    RecordAt (writeRecord μ dst stride n j (weight N low high m active)
      (key N low high m T active bv nv bi ni)) dst stride n j N low high m T active bv nv bi ni := by
  have hsn : 0<stride*n := Nat.mul_pos hs (by omega)
  simp [RecordAt,writeRecord,Function.update_of_ne (by omega : dst+stride*j≠dst+stride*n+stride*j)]

theorem writeRecord_before {μ : ℕ → ℤ} {dst stride n j k N low high m T active bv nv bi ni : ℕ}
    {w z : ℤ} (hs : 0<stride) (hk : k<j) (hj : j<n)
    (H : RecordAt μ dst stride n k N low high m T active bv nv bi ni) :
    RecordAt (writeRecord μ dst stride n j w z) dst stride n k N low high m T active bv nv bi ni := by
  have hkj : stride*k<stride*j := Nat.mul_lt_mul_of_pos_left hk hs
  have hkn : stride*k<stride*n := Nat.mul_lt_mul_of_pos_left (by omega) hs
  have hjn : stride*j<stride*n := Nat.mul_lt_mul_of_pos_left hj hs
  unfold RecordAt writeRecord at *
  simp only [Function.update_of_ne (by omega : dst+stride*k≠dst+stride*n+stride*j),
    Function.update_of_ne (by omega : dst+stride*k≠dst+stride*j),
    Function.update_of_ne (by omega : dst+stride*n+stride*k≠dst+stride*n+stride*j),
    Function.update_of_ne (by omega : dst+stride*n+stride*k≠dst+stride*j)]
  exact H

def Inv (μ : ℕ → ℤ) (N low high a n powers bank nb bv near nn nv L T active dst stride : ℕ)
    (codes bi ni : ℕ → ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ (m k q : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [N,low,high,a,n,powers,bank,nb,bv,near,nn,nv,L,T,active,dst,stride,j,m,k,q],ν⟩ ∧
    KeptApart μ ν dst stride n ∧
    ∀ l<j, RecordAt ν dst stride n l N low high (codes l) T active bv nv (bi l) (ni l)

variable {lim : Limits} {P : Program}

theorem meets {pMain pCell pDigit pZero pErase pRank pSearch N low high a n powers
    bank nb bv near nn nv L T active dst stride d : ℕ}
    (hmain : P[pMain]?=some (body pCell pDigit))
    (hcell : P[pCell]?=some (LightTernaryPredecessor.body pDigit pZero pErase pRank pSearch))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hrank : P[pRank]?=some (LightTernaryRank.body pDigit))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (codes bankCodes nearCodes bi ni : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n≤dst) (hbankSpace : bank+nb≤dst) (hnearSpace : near+nn≤dst)
    (hspace : powers+(2*N+1)≤dst) (hdst : dst+2*stride*n≤lim.space)
    (hbankVals : bv+nb≤lim.space) (hnearVals : nv+nn≤lim.space)
    (hword : ((nb+nn+2^(2*N+1)+2*N+32 : ℕ) : ℤ)≤lim.word)
    (hcontrols : ((T+active+stride+16 : ℕ) : ℤ)≤lim.word)
    (hread : ∀ j<n, μ (a+j)=(codes j : ℤ))
    (hbankRead : ∀ j<nb, μ (bank+j)=(bankCodes j : ℤ))
    (hnearRead : ∀ j<nn, μ (near+j)=(nearCodes j : ℤ))
    (hbankSorted : ∀ j k, j<k → k<nb → bankCodes j<bankCodes k)
    (hnearSorted : ∀ j k, j<k → k<nn → nearCodes j<nearCodes k)
    (hpowers : Powers μ powers (2*N)) (hcodes : ∀ j<n, codes j<2^(2*N))
    (hlow : low≤2*N) (hhigh : high≤2*N) (hL : L≤2*N)
    (hnb : nb<2^L) (hnn : nn<2^L) (hnbpos : 0<nb)
    (hactive : active≤1) (hstride : 0<stride)
    (hbi : ∀ j<n, active≠0 → digit N low high (codes j)≠0 →
      predRank N low high (codes j)≤T → bi j<nb ∧ bankCodes (bi j)=code N low high (codes j))
    (hni : ∀ j<n, active≠0 → digit N low high (codes j)≠0 →
      T<predRank N low high (codes j) → ni j<nn ∧ nearCodes (ni j)=code N low high (codes j))
    (hd : d+2*N+4≤lim.depth) :
    Meets lim P pMain d [N,low,high,a,n,powers,bank,nb,bv,near,nn,nv,L,T,active,dst,stride]
      μ (time N L n)
      (fun _ ν => (∀ j<n, RecordAt ν dst stride n j N low high (codes j) T active bv nv (bi j) (ni j)) ∧
        KeptApart μ ν dst stride n ∧ SameOutside μ ν dst (2*stride*n)) := by
  have hpowWord : ((2^(2*N+1) : ℕ) : ℤ)≤lim.word := by omega
  have htwoword : (2 : ℤ)≤lim.word := by omega
  have hspan : dst+2*(stride*n)≤lim.space := by simpa only [Nat.mul_assoc] using hdst
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ N low high a n powers bank nb bv near nn nv L T active dst stride codes bi ni)
    n (LightTernaryPredecessor.time N L+LightTernaryCodes.digitTime (2*N)+180)
    ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,0,0,μ,?_,keptApart_refl μ dst stride n,?_⟩
    · simp [update_frame_setLocal]
      change frame [(N : ℤ),low,high,a,n,powers,bank,nb,bv,near,nn,nv,L,T,active,dst,stride,0]=
        frame ([(N : ℤ),low,high,a,n,powers,bank,nb,bv,near,nn,nv,L,T,active,dst,stride,0] ++ [0,0,0])
      exact (frame_append_zeros _ 3).symm
    · intro l hl
      omega
  case round =>
    rintro j _ hj _ ⟨m,k,q,ν,rfl,H,hr⟩
    have hkeep : ∀ x<dst, ν x=μ x := by
      intro x hx
      exact (keptApart_outside hstride H) x (Or.inl hx)
    have hreadj : ν (a+j)=(codes j : ℤ) := by rw [hkeep _ (by omega),hread j hj]
    have hbRead : ∀ l<nb, ν (bank+l)=(bankCodes l : ℤ) := by
      intro l hl; rw [hkeep _ (by omega),hbankRead l hl]
    have hnRead : ∀ l<nn, ν (near+l)=(nearCodes l : ℤ) := by
      intro l hl; rw [hkeep _ (by omega),hnearRead l hl]
    have hp : Powers ν powers (2*N) := by
      intro l hl; rw [hkeep _ (by omega),hpowers l hl]
    have hm := hcodes j hj
    have hmword : (codes j : ℤ)<lim.word := by
      have hh : 2^(2*N)≤2^(2*N+1) := Nat.pow_le_pow_right (by decide) (by omega)
      exact (Int.ofNat_lt.mpr hm).trans_le ((Int.ofNat_le.mpr hh).trans hpowWord)
    have hdigitBound := LightTernaryCodes.digit_le_two (2*N) low high (codes j)
    have hweightEq : active*digit N low high (codes j)=weight N low high (codes j) active := by
      by_cases ha : active=0
      · simp [weight,ha]
      · have ha1 : active=1 := by omega
        simp [weight,ha1]
    have hweightBound : weight N low high (codes j) active≤2 := by
      unfold weight digit
      split_ifs <;> omega
    have hweightCast : (active : ℤ)*(LightTernaryCodes.digit (2*N) low high (codes j) : ℤ)=
        (weight N low high (codes j) active : ℤ) := by exact_mod_cast hweightEq
    have hkeySpace : key N low high (codes j) T active bv nv (bi j) (ni j)<lim.space := by
      unfold key
      split_ifs with h0 hb
      · omega
      · have hh := hbi j hj (by tauto) (by tauto) hb
        omega
      · have hh := hni j hj (by tauto) (by tauto) (by omega)
        omega
    have hkeyWord : (key N low high (codes j) T active bv nv (bi j) (ni j) : ℤ)≤lim.word :=
      (Int.ofNat_le.mpr (Nat.le_of_lt hkeySpace)).trans hw
    have hprod : stride*j<stride*n := Nat.mul_lt_mul_of_pos_left hj hstride
    have hprodWord : ((stride*j : ℕ) : ℤ)≤lim.word := by
      have hh : stride*j≤lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have hprodNWord : ((stride*n : ℕ) : ℤ)≤lim.word := by
      have hh : stride*n≤lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have hc := LightTernaryPredecessor.meets (d := d+1) hcell hdigit hzero herase hrank hsearch
      ν bankCodes nearCodes hw (by omega) (by omega) hbankVals hnearVals (by omega)
      hword (by omega) hbRead hnRead hbankSorted hnearSorted hp hm hlow hhigh hL hnb hnn hnbpos
      (hbi j hj) (hni j hj) (by omega)
    have hdc := LightTernaryCodes.digit_meets (d := d+1) hdigit herase ν hw
      (by omega) hpowWord hp hlow hhigh hm (by omega) htwoword
    unfold roundBody
    light_set (codes j : ℕ) using hreadj,LightTernaryPredecessor.time,LightTernaryCodes.digitTime
    light_call hc using LightTernaryPredecessor.time,LightTernaryCodes.digitTime
      with out ξ ⟨hout,hmem⟩
    subst ξ
    light_call hdc using LightTernaryPredecessor.time,LightTernaryCodes.digitTime
      with dig ξ ⟨hdig,hmem⟩
    subst ξ
    light_set (weight N low high (codes j) active : ℕ)
      using hdig,hweightCast,LightTernaryPredecessor.time,LightTernaryCodes.digitTime
    light_store (dst+stride*j) (weight N low high (codes j) active : ℕ)
      using LightTernaryPredecessor.time,LightTernaryCodes.digitTime
    light_store (dst+stride*n+stride*j) (key N low high (codes j) T active bv nv (bi j) (ni j) : ℕ)
      using hout,LightTernaryPredecessor.time,LightTernaryCodes.digitTime
    let ξ := writeRecord ν dst stride n j (weight N low high (codes j) active)
      (key N low high (codes j) T active bv nv (bi j) (ni j))
    refine ⟨by simp,(codes j : ℤ),out,(weight N low high (codes j) active : ℤ),ξ,?_,?_,?_⟩
    · simp [update_frame_setLocal,ξ,writeRecord]
    · intro x hx
      exact (writeRecord_kept hj x hx).trans (H x hx)
    · intro l hl
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
      · exact writeRecord_before hstride hl hj (hr l hl)
      · exact writeRecord_current hstride hj
  case done =>
    rintro _ _ ⟨m,k,q,ν,rfl,H,hr⟩
    exact ⟨hr,H,keptApart_outside hstride H⟩
  case bound =>
    rintro j _ hj _ ⟨m,k,q,ν,rfl,H,hr⟩
    light_side

theorem time_bound (N L n : ℕ) : time N L n≤4000*(N+L+1)^2*(n+1) := by
  have hp := LightTernaryPredecessor.time_bound N L
  have hd := LightTernaryCodes.digit_time_bound (2*N)
  have hsqr : N+L+1≤(N+L+1)^2 := le_self_pow (by omega) (by decide)
  have hsmall : 400*(2*N+1)+200≤1000*(N+L+1)^2 := by omega
  have hr : LightTernaryPredecessor.time N L+LightTernaryCodes.digitTime (2*N)+200≤
      4000*(N+L+1)^2 := by
    calc
      _ ≤ 3000*(N+L+1)^2+(400*(2*N+1)+200) := by omega
      _ ≤ 3000*(N+L+1)^2+1000*(N+L+1)^2 := Nat.add_le_add_left hsmall _
      _ = _ := by ring
  have hK : 1≤(N+L+1)^2 := by nlinarith
  have hm := Nat.mul_le_mul_left n hr
  unfold time
  nlinarith [hm,hK]

end ThreeSum.LightTernaryPredecessorTable
