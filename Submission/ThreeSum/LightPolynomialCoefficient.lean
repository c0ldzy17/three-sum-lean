import Submission.ThreeSum.LightRadixDigit

/-! A physical coefficient-array convolution loop.  Arrays store natural
coefficient representatives; a single costed remainder gives the Fp coefficient. -/
namespace ThreeSum.LightPolynomialCoefficient
open Light Finset
set_option maxHeartbeats 2000000

def term (f g : ℕ → ℕ) (m k i : ℕ) : ℕ :=
  if i≤k ∧ k-i<m then f i*g (k-i) else 0

def rawCoefficient (f g : ℕ → ℕ) (n m k : ℕ) : ℕ :=
  ∑ i ∈ range n, term f g m k i

def coefficient (p : ℕ) (f g : ℕ → ℕ) (n m k : ℕ) : ℕ :=
  rawCoefficient f g n m k % p

@[simp] theorem raw_zero (f g : ℕ → ℕ) (m k : ℕ) : rawCoefficient f g 0 m k=0 := by
  simp [rawCoefficient]

theorem raw_succ (f g : ℕ → ℕ) (j m k : ℕ) :
    rawCoefficient f g (j+1) m k=rawCoefficient f g j m k+term f g m k j :=
  sum_range_succ _ _

theorem raw_bound (f g : ℕ → ℕ) {n m k j p : ℕ}
    (hf : ∀ i<n, f i<p) (hg : ∀ i<m, g i<p) (hj : j≤n) :
    rawCoefficient f g j m k≤j*p^2 := by
  unfold rawCoefficient
  calc
    ∑ i ∈ range j, term f g m k i≤∑ _i ∈ range j, p^2 := by
      apply sum_le_sum
      intro i hi
      unfold term
      split_ifs with h
      · have hfi := hf i ((mem_range.mp hi).trans_le hj)
        have hgi := hg (k-i) h.2
        nlinarith
      · omega
    _ = _ := by simp

def loopBody : Stmt :=
  .ite (v 6 ≤' v 4)
    (.ite (v 4 -' v 6 <' v 3)
      (.set 5 (v 5 +' M (v 0 +' v 6) *' M (v 1 +' (v 4 -' v 6))))
      .skip)
    .skip

def body : Stmt := .set 5 (k 0) ;; .for 6 (v 2) loopBody ;; .set 0 (v 5)
def time (n : ℕ) : ℕ := 100*n+30

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem meets {proc srcA srcB n m k p : ℕ}
    (hp : P[proc]?=some body) (μ : ℕ → ℤ) (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word)
    (hA : srcA+n≤lim.space) (hB : srcB+m≤lim.space)
    (hreadA : ∀ i<n, μ (srcA+i)=(f i : ℤ))
    (hreadB : ∀ i<m, μ (srcB+i)=(g i : ℤ))
    (hf : ∀ i<n, f i<p) (hg : ∀ i<m, g i<p)
    (hword : (((n+1)*(p+1)^2+k+m+10 : ℕ) : ℤ)≤lim.word) :
    Meets lim P proc depth [srcA,srcB,n,m,k] μ (time n)
      (fun r ν => r=(rawCoefficient f g n m k : ℤ) ∧ ν=μ) := by
  have hb (z : ℕ) (hz : z≤(n+1)*(p+1)^2+k+m+10) : (z : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr hz).trans hword
  have hkw := hb k (by omega)
  have hmw := hb m (by omega)
  have hnp : n*p^2≤(n+1)*(p+1)^2+k+m+10 := by
    calc
      n*p^2≤(n+1)*(p+1)^2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
      _ ≤ _ := by omega
  have hfit (j : ℕ) (hj : j≤n) : (rawCoefficient f g j m k : ℤ)≤lim.word :=
    hb _ ((raw_bound f g hf hg hj).trans ((Nat.mul_le_mul_right (p^2) hj).trans hnp))
  apply Meets.of_body hp
  unfold body time
  light_set (0 : ℕ)
  refine Ends.pieceThen (Ends.for (T := 100*n+6)
    (Q := fun σ => σ=⟨frame [srcA,srcB,n,m,k,rawCoefficient f g n m k,n],μ⟩)
    (fun j σ => σ=⟨frame [srcA,srcB,n,m,k,rawCoefficient f g j m k,j],μ⟩)
    n 80 ?start ?round ?done ?bound (hT := by light_time)) ?after
  case start => simp [raw_zero,update_frame_setLocal]
  case round =>
    rintro j _ hj _ rfl
    have hsum0 := hfit j (by omega)
    have hsum1 := hfit (j+1) (by omega)
    unfold loopBody
    refine Ends.iteLast ?_ ?_ (by light_side) (by light_time)
    · intro hle
      have hjk : j≤k := by
        have hh : (j : ℤ)<(k : ℤ)+1 := by simpa using hle
        omega
      have hsub : (k : ℤ)-(j : ℤ)=((k-j : ℕ) : ℤ) := (Int.natCast_sub hjk).symm
      refine Ends.iteLast ?_ ?_ (by light_side [hsub]) (by light_time)
      · intro hlt
        have hkm : k-j<m := by
          have hh : ((k-j : ℕ) : ℤ)<(m : ℤ) := by
            simpa only [Cond.Holds,Expr.val,Op.eval,frame,List.getD_cons_zero,List.getD_cons_succ,hsub] using hlt
          exact_mod_cast hh
        have hrA := hreadA j hj
        have hrB := hreadB (k-j) hkm
        have hf' := hf j hj
        have hg' := hg (k-j) hkm
        have hprod : f j*g (k-j)≤n*p^2 := by nlinarith
        have hprodWord := hb (f j*g (k-j)) (hprod.trans hnp)
        have hsucc : rawCoefficient f g (j+1) m k=rawCoefficient f g j m k+f j*g (k-j) := by
          rw [raw_succ,term,if_pos ⟨hjk,hkm⟩]
        have hsuccZ : (rawCoefficient f g j m k : ℤ)+(f j : ℤ)*(g (k-j) : ℤ)=(rawCoefficient f g (j+1) m k : ℤ) := by exact_mod_cast hsucc.symm
        refine Ends.setLast ?_ (hs := by light_side [hrA,hrB,hsub,←hsucc]) (hT := by light_time)
        simp [hrA,hrB,hsub,hsuccZ,update_frame_setLocal]
      · intro hlt
        have hkm : ¬k-j<m := by
          have hh : ¬((k-j : ℕ) : ℤ)<(m : ℤ) := by
            simpa only [Cond.Holds,Expr.val,Op.eval,frame,List.getD_cons_zero,List.getD_cons_succ,hsub] using hlt
          exact_mod_cast hh
        have hsame : rawCoefficient f g (j+1) m k=rawCoefficient f g j m k := by
          simp [raw_succ,term,hkm]
        exact Ends.skip (by simp [hsame,update_frame_setLocal])
    · intro hle
      have hjk : ¬j≤k := by
        have hh : (k : ℤ)+1≤(j : ℤ) := by simpa using hle
        omega
      have hsame : rawCoefficient f g (j+1) m k=rawCoefficient f g j m k := by
        simp [raw_succ,term,hjk]
      exact Ends.skip (by simp [hsame,update_frame_setLocal])
  case done => intro σ hcounter hshape; exact hshape
  case bound => rintro j _ hj _ rfl; light_side
  case after =>
    intro σ hshape
    rw [hshape]
    light_set (rawCoefficient f g n m k : ℕ)
    exact ⟨rfl,rfl⟩

def reducedBody (pRaw pDigit : ℕ) : Stmt :=
  .call pRaw [v 0,v 1,v 2,v 3,v 4] 6 ;;
  .call pDigit [v 6,k 1,v 5] 0

def reducedTime (n p : ℕ) : ℕ := time n+40*(n*p^2+1)+200

theorem reduced_meets {proc pRaw pDigit pDivide srcA srcB n m k p : ℕ}
    (hp : P[proc]?=some (reducedBody pRaw pDigit))
    (hraw : P[pRaw]?=some body)
    (hdigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+1<lim.depth)
    (hA : srcA+n≤lim.space) (hB : srcB+m≤lim.space)
    (hreadA : ∀ i<n, μ (srcA+i)=(f i : ℤ))
    (hreadB : ∀ i<m, μ (srcB+i)=(g i : ℤ))
    (hf : ∀ i<n, f i<p) (hg : ∀ i<m, g i<p)
    (hword : ((20*((n+1)*(p+1)^2+k+m+10) : ℕ) : ℤ)≤lim.word) :
    Meets lim P proc depth [srcA,srcB,n,m,k,p] μ (reducedTime n p)
      (fun r ν => r=(coefficient p f g n m k : ℤ) ∧ ν=μ) := by
  have hrawBound := raw_bound f g hf hg (j := n) le_rfl (k := k)
  have hwordRaw : (((n+1)*(p+1)^2+k+m+10 : ℕ) : ℤ)≤lim.word := by omega
  have hbase : n*p^2≤(n+1)*(p+1)^2 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
  have hwordDigit : (LightRadixDigit.word (rawCoefficient f g n m k) 1 p : ℤ)≤lim.word := by
    apply le_trans (Int.ofNat_le.mpr ?_) hword
    unfold LightRadixDigit.word
    nlinarith [Nat.le_refl ((n+1)*(p+1)^2)]
  have hval : ((rawCoefficient f g n m k : ℕ) : ℤ)≤lim.word := by
    unfold LightRadixDigit.word at hwordDigit
    omega
  have hpWord : (p : ℤ)≤lim.word := by
    unfold LightRadixDigit.word at hwordDigit
    omega
  have hone : (1 : ℤ)≤lim.word := by omega
  have htimeDigit : LightRadixDigit.time (rawCoefficient f g n m k)≤40*(n*p^2+1)+100 := by
    unfold LightRadixDigit.time
    omega
  apply Meets.of_body hp
  unfold reducedBody reducedTime
  light_call (meets (depth := depth+1) hraw μ f g hw hA hB hreadA hreadB hf hg hwordRaw)
    using time with r ν ⟨hr,hν⟩
  subst ν
  subst r
  light_call (LightRadixDigit.meets (d := depth+1) hdigit hdivide μ hd hwordDigit)
    using LightRadixDigit.time with r ν ⟨hr,hν⟩
  subst ν
  subst r
  simp [coefficient]

end ThreeSum.LightPolynomialCoefficient
