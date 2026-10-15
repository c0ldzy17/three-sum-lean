import Submission.ThreeSum.LightTernaryPredecessorTable

/-! Complete physical row-major Euler metadata, with a runtime active-coordinate mask. -/

namespace ThreeSum.LightTernaryEulerMetadata

open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def lowAt (N i : ℕ) : ℕ := 2*(N-1-i)
def highAt (N i : ℕ) : ℕ := lowAt N i+1

def rowAddr (ws N i j : ℕ) : ℕ := ws+N*j+i

theorem rowAddr_ne {ws N i k j l : ℕ} (hi : i<N) (hk : k<N) (hne : i≠k) :
    rowAddr ws N i j≠rowAddr ws N k l := by
  intro he
  have hbase : N*j+i=N*l+k := by simpa only [rowAddr,Nat.add_assoc,Nat.add_left_cancel_iff] using he
  have hmod := congrArg (fun x => x%N) hbase
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod,Nat.zero_add,
    Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hk] at hmod
  exact hne hmod

theorem column_keeps {μ ν : ℕ → ℤ} {ws N rows i k : ℕ}
    (hi : i<N) (hk : k<N) (hne : i≠k)
    (H : LightTernaryPredecessorTable.KeptApart μ ν (ws+k) N rows) (j : ℕ) :
    ν (rowAddr ws N i j)=μ (rowAddr ws N i j) := by
  apply H
  intro l hl
  constructor
  · convert rowAddr_ne (j := j) (l := l) hi hk hne using 1 <;> simp [rowAddr] <;> omega
  · convert rowAddr_ne (j := j) (l := rows+l) hi hk hne using 1 <;> simp [rowAddr,Nat.mul_add] <;> omega

theorem column_outside {μ ν : ℕ → ℤ} {ws N rows k : ℕ} (hk : k<N)
    (H : LightTernaryPredecessorTable.KeptApart μ ν (ws+k) N rows) :
    SameOutside μ ν ws (2*N*rows) := by
  intro x hx
  apply H
  intro j hj
  have hm := Nat.mul_le_mul_left N (show j+1≤rows by omega)
  simp only [Nat.mul_add,Nat.mul_one] at hm
  rw [Nat.mul_assoc] at hx
  rcases hx with hx | hx <;> constructor <;> omega

def RecordAt (μ : ℕ → ℤ) (N rows ws i j m T active bv nv bi ni : ℕ) : Prop :=
  μ (rowAddr ws N i j)=(weight N (lowAt N i) (highAt N i) m active : ℤ) ∧
  μ (rowAddr ws N i (rows+j))=(key N (lowAt N i) (highAt N i) m T active bv nv bi ni : ℤ)

def roundBody (pColumn : ℕ) : Stmt :=
  .set 15 (k 2 *' (v 0 -' k 1 -' v 14)) ;;
  .set 16 (v 15 +' k 1) ;;
  .set 17 (M (v 12 +' v 14)) ;;
  .call pColumn [v 0,v 15,v 16,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,
    v 17,v 13 +' v 14,v 0] 18

/-- N, rowcodes/count, powers, bank codes/count/values, near codes/count/values,
lookup width, bank cutoff, active-mask base, row-major metadata base. -/
def body (pColumn : ℕ) : Stmt := .for 14 (v 0) (roundBody pColumn)

def time (N L rows : ℕ) : ℕ := N*(LightTernaryPredecessorTable.time N L rows+200)+20

def Inv (μ : ℕ → ℤ) (N a rows powers bank nb bv near nn nv L T activeBase ws : ℕ)
    (codes active : ℕ → ℕ) (bi ni : ℕ → ℕ → ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (lo hi act result : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [N,a,rows,powers,bank,nb,bv,near,nn,nv,L,T,activeBase,ws,i,lo,hi,act,result],ν⟩ ∧
    SameOutside μ ν ws (2*N*rows) ∧
    ∀ k < i, ∀ j<rows, RecordAt ν N rows ws k j (codes j) T (active k) bv nv (bi k j) (ni k j)

variable {lim : Limits} {P : Program}

theorem meets {pMain pColumn pCell pDigit pZero pErase pRank pSearch N a rows powers
    bank nb bv near nn nv L T activeBase ws d : ℕ}
    (hmain : P[pMain]?=some (body pColumn))
    (hcolumn : P[pColumn]?=some (LightTernaryPredecessorTable.body pCell pDigit))
    (hcell : P[pCell]?=some (LightTernaryPredecessor.body pDigit pZero pErase pRank pSearch))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hrank : P[pRank]?=some (LightTernaryRank.body pDigit))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (codes bankCodes nearCodes active : ℕ → ℕ) (bi ni : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+rows≤ws) (hbankSpace : bank+nb≤ws) (hnearSpace : near+nn≤ws)
    (hspace : powers+(2*N+1)≤ws) (hactiveSpace : activeBase+N≤ws)
    (hws : ws+2*N*rows+N≤lim.space)
    (hbankVals : bv+nb≤lim.space) (hnearVals : nv+nn≤lim.space)
    (hword : ((nb+nn+2^(2*N+1)+2*N+32 : ℕ) : ℤ)≤lim.word)
    (hcontrols : ((T+N+32 : ℕ) : ℤ)≤lim.word)
    (hread : ∀ j<rows, μ (a+j)=(codes j : ℤ))
    (hbankRead : ∀ j<nb, μ (bank+j)=(bankCodes j : ℤ))
    (hnearRead : ∀ j<nn, μ (near+j)=(nearCodes j : ℤ))
    (hactiveRead : ∀ i<N, μ (activeBase+i)=(active i : ℤ))
    (hbankSorted : ∀ j k, j<k → k<nb → bankCodes j<bankCodes k)
    (hnearSorted : ∀ j k, j<k → k<nn → nearCodes j<nearCodes k)
    (hpowers : Powers μ powers (2*N)) (hcodes : ∀ j<rows, codes j<2^(2*N))
    (hL : L≤2*N) (hnb : nb<2^L) (hnn : nn<2^L) (hnbpos : 0<nb)
    (hactive : ∀ i<N, active i≤1)
    (hbi : ∀ i<N, ∀ j<rows, active i≠0 → digit N (lowAt N i) (highAt N i) (codes j)≠0 →
      predRank N (lowAt N i) (highAt N i) (codes j)≤T →
      bi i j<nb ∧ bankCodes (bi i j)=code N (lowAt N i) (highAt N i) (codes j))
    (hni : ∀ i<N, ∀ j<rows, active i≠0 → digit N (lowAt N i) (highAt N i) (codes j)≠0 →
      T<predRank N (lowAt N i) (highAt N i) (codes j) →
      ni i j<nn ∧ nearCodes (ni i j)=code N (lowAt N i) (highAt N i) (codes j))
    (hd : d+2*N+5≤lim.depth) :
    Meets lim P pMain d [N,a,rows,powers,bank,nb,bv,near,nn,nv,L,T,activeBase,ws]
      μ (time N L rows)
      (fun _ ν => (∀ i<N, ∀ j<rows, RecordAt ν N rows ws i j (codes j) T (active i) bv nv (bi i j) (ni i j)) ∧
        SameOutside μ ν ws (2*N*rows)) := by
  have hspan : ws+2*(N*rows)+N≤lim.space := by simpa only [Nat.mul_assoc] using hws
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ N a rows powers bank nb bv near nn nv L T activeBase ws codes active bi ni)
    N (LightTernaryPredecessorTable.time N L rows+180)
    ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,0,0,0,μ,?_,SameOn.refl,?_⟩
    · simp [update_frame_setLocal]
      change frame [(N : ℤ),a,rows,powers,bank,nb,bv,near,nn,nv,L,T,activeBase,ws,0]=
        frame ([(N : ℤ),a,rows,powers,bank,nb,bv,near,nn,nv,L,T,activeBase,ws,0] ++ [0,0,0,0])
      exact (frame_append_zeros _ 4).symm
    · intro k hk
      omega
  case round =>
    rintro i _ hi _ ⟨lo,hig,act,result,ν,rfl,H,hr⟩
    have hkeep : ∀ x<ws, ν x=μ x := fun x hx => H x (Or.inl hx)
    have hRead : ∀ j<rows, ν (a+j)=(codes j : ℤ) := by
      intro j hj; rw [hkeep _ (by omega),hread j hj]
    have hbRead : ∀ j<nb, ν (bank+j)=(bankCodes j : ℤ) := by
      intro j hj; rw [hkeep _ (by omega),hbankRead j hj]
    have hnRead : ∀ j<nn, ν (near+j)=(nearCodes j : ℤ) := by
      intro j hj; rw [hkeep _ (by omega),hnearRead j hj]
    have haRead : ν (activeBase+i)=(active i : ℤ) := by
      rw [hkeep _ (by omega),hactiveRead i hi]
    have hp : Powers ν powers (2*N) := by
      intro j hj; rw [hkeep _ (by omega),hpowers j hj]
    have hlow : lowAt N i<2*N := by unfold lowAt; omega
    have hhigh : highAt N i<2*N := by unfold highAt lowAt; omega
    have hloCast : 2*((N : ℤ)-1-(i : ℤ))=(lowAt N i : ℤ) := by unfold lowAt; omega
    have hact := hactive i hi
    have hc := LightTernaryPredecessorTable.meets (d := d+1) (dst := ws+i) (stride := N) hcolumn hcell hdigit hzero herase hrank hsearch
      ν codes bankCodes nearCodes (bi i) (ni i) hw (by omega) (by omega) (by omega)
      (by omega) (by simpa only [Nat.mul_assoc] using (show ws+i+2*(N*rows)≤lim.space by omega))
      hbankVals hnearVals hword (by omega) hRead hbRead hnRead hbankSorted hnearSorted hp hcodes
      (Nat.le_of_lt hlow) (Nat.le_of_lt hhigh) hL hnb hnn hnbpos hact (by omega)
      (hbi i hi) (hni i hi) (by omega)
    unfold roundBody
    light_set (lowAt N i : ℕ) using hloCast,LightTernaryPredecessorTable.time
    light_set (highAt N i : ℕ) using highAt,LightTernaryPredecessorTable.time
    light_set (active i : ℕ) using haRead,LightTernaryPredecessorTable.time
    light_call hc using LightTernaryPredecessorTable.time
      with out ξ ⟨hrows,hapart,houtside⟩
    refine ⟨by simp,(lowAt N i : ℤ),(highAt N i : ℤ),(active i : ℤ),out,ξ,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro x hx
      exact (column_outside hi hapart x hx).trans (H x hx)
    · intro k hk j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · have hkN : k<N := by omega
        obtain ⟨hw0,hk0⟩ := hr k hk j hj
        unfold RecordAt
        rw [column_keeps hkN hi (by omega) hapart j,
          column_keeps hkN hi (by omega) hapart (rows+j)]
        exact ⟨hw0,hk0⟩
      · simpa [RecordAt,LightTernaryPredecessorTable.RecordAt,rowAddr,Nat.mul_add,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hrows j hj
  case done =>
    rintro _ _ ⟨lo,hig,act,result,ν,rfl,H,hr⟩
    exact ⟨hr,H⟩
  case bound =>
    rintro i _ hi _ ⟨lo,hig,act,result,ν,rfl,H,hr⟩
    light_side

theorem time_bound (N L rows : ℕ) :
    time N L rows≤5000*(N+L+1)^3*(rows+1) := by
  have hc := LightTernaryPredecessorTable.time_bound N L rows
  have hsqr : N+L+1≤(N+L+1)^2 := le_self_pow (by omega) (by decide)
  have hsq : 1≤(N+L+1)^2 := by omega
  have hpad : 200≤1000*(N+L+1)^2*(rows+1) := by
    have hm := Nat.mul_le_mul_left (1000*(N+L+1)^2) (show 1≤rows+1 by omega)
    omega
  have hb : LightTernaryPredecessorTable.time N L rows+200≤
      5000*(N+L+1)^2*(rows+1) := by nlinarith only [hc,hpad]
  have hm := Nat.mul_le_mul_left N hb
  have hn : N+1≤N+L+1 := by omega
  have hmul := Nat.mul_le_mul_right (5000*(N+L+1)^2*(rows+1)) hn
  have hpositive : 20≤5000*(N+L+1)^2*(rows+1) := by omega
  unfold time
  calc
    _ ≤ N*(5000*(N+L+1)^2*(rows+1))+20 := Nat.add_le_add_right hm 20
    _ ≤ (N+1)*(5000*(N+L+1)^2*(rows+1)) := by nlinarith only [hpositive]
    _ ≤ (N+L+1)*(5000*(N+L+1)^2*(rows+1)) := hmul
    _ = _ := by ring

end ThreeSum.LightTernaryEulerMetadata
