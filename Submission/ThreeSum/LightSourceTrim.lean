import Submission.ThreeSum.LightSourceRowFlag
import Submission.ThreeSum.SourceFlagProduct

/-!
# Independent endpoint trimming across all selected blocks

The loop reads each occurrence index and its exact selected-candidate index,
then calls the concrete row flag constructor on the corresponding map and
retained bucket tables. The product of the independent Boolean flags is
written in each orientation. Input Boolean rows and tables are preserved.
-/

namespace ThreeSum.LightSourceTrim

open Light SourceFlagProduct

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

def rowFlag (L h p cap : ℕ) (sel candidate bits : ℕ → ℕ)
    (w0 w1 counts : ℕ → ℕ → ℕ) (j : ℕ) : ℕ :=
  LightSourceRowFlag.flag L h p cap (fun a => bits (j*L+a))
    (w0 (sel j)) (w1 (sel j)) (counts (candidate (sel j)))

theorem rowFlag_le (L h p cap : ℕ) (sel candidate bits : ℕ → ℕ)
    (w0 w1 counts : ℕ → ℕ → ℕ) (j : ℕ) :
    rowFlag L h p cap sel candidate bits w0 w1 counts j ≤ 1 :=
  LightSourceRowFlag.flag_le ..

def roundBody (pRowFlag : ℕ) : Stmt :=
  .call pRowFlag [v 10 +' v 16 *' v 1,
    v 6 +' k 2 *' v 1 *' M (v 5 +' v 16),
    v 6 +' k 2 *' v 1 *' M (v 5 +' v 16) +' v 1,
    v 1,v 2,
    v 8 +' M (v 7 +' M (v 5 +' v 16)) *' v 3,
    v 9 +' M (v 7 +' M (v 5 +' v 16)) *' v 3,
    v 3,v 4,v 11,v 12] 17 ;;
  .set 14 (v 14 *' M (v 11)) ;;
  .set 15 (v 15 *' M (v 11 +' k 1))

/-- Arguments: block count, width, required row size, modulus, cap,
occurrence indices, selected-map coefficient rows, occurrence-to-candidate
indices, both candidate bucket tables, Boolean rows, two-cell row scratch,
remainder scratch, and two-cell final output. -/
def body (pRowFlag : ℕ) : Stmt :=
  .set 14 (k 1) ;;
  .set 15 (k 1) ;;
  .for 16 (v 0) (roundBody pRowFlag) ;;
  .store (v 13) (v 14) ;;
  .store (v 13 +' k 1) (v 15)

def time (J L U : ℕ) : ℕ := J*(LightSourceRowFlag.time L U+250)+100

structure Procs (P : Program) (pMain : ℕ) where
  pRowFlag : ℕ
  pRow : ℕ
  pEmod : ℕ
  pFlag : ℕ
  rowFlagDef : P[pRowFlag]? = some (LightSourceRowFlag.body pRow pEmod pFlag)
  row : P[pRow]? = some LightSourceRowScan.body
  emod : P[pEmod]? = some emodBody
  flag : P[pFlag]? = some LightSourceFlagTest.body
  main : P[pMain]? = some (body pRowFlag)

def Inv (μ : ℕ → ℤ) (J L h p cap occ maps candidates histL histR bitBase rowOut work dst : ℕ)
    (sel candidate bits : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [J,L,h,p,cap,occ,maps,candidates,histL,histR,bitBase,rowOut,work,dst,
      product (rowFlag L h p cap sel candidate bits w0 w1 leftCount) j,
      product (rowFlag L h p cap sel candidate bits w1 w0 rightCount) j,j,r],ν⟩ ∧
    Kept μ ν rowOut

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {J L h p cap occ maps candidates histL histR bitBase rowOut work dst U V M K : ℕ}
    (sel candidate bits : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hp : 0 < p) (hh : h ≤ L)
    (hocc : occ+J ≤ rowOut) (hmaps : maps+2*L*M ≤ rowOut)
    (hcandidates : candidates+M ≤ rowOut)
    (hleft : histL+K*p ≤ rowOut) (hright : histR+K*p ≤ rowOut)
    (hbits : bitBase+J*L ≤ rowOut) (hrowOut : rowOut+2 ≤ work) (hdst : dst+2 ≤ rowOut)
    (hspace : LightSourceRowFlag.space work L U ≤ lim.space)
    (hword : (LightSourceRowFlag.word L p U V cap : ℤ) ≤ lim.word)
    (hsel : ∀ j < J, sel j < M) (hcandidate : ∀ s < M, candidate s < K)
    (hoccRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hcandidateRead : ∀ s < M, μ (candidates+s) = (candidate s : ℤ))
    (hbitsRead : ∀ i < J*L, μ (bitBase+i) = (bits i : ℤ))
    (hbitBound : ∀ i < J*L, bits i ≤ 1)
    (hread0 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+a) = (w0 s a : ℤ))
    (hread1 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+L+a) = (w1 s a : ℤ))
    (hbound0 : ∀ s < M, ∀ a < L, w0 s a ≤ U)
    (hbound1 : ∀ s < M, ∀ a < L, w1 s a ≤ U)
    (hcountL : ∀ k < K, ∀ r < p, μ (histL+k*p+r) = (leftCount k r : ℤ))
    (hcountR : ∀ k < K, ∀ r < p, μ (histR+k*p+r) = (rightCount k r : ℤ))
    (hcountBoundL : ∀ k < K, ∀ r < p, leftCount k r ≤ V)
    (hcountBoundR : ∀ k < K, ∀ r < p, rightCount k r ≤ V) :
    Meets lim P pMain d
      [J,L,h,p,cap,occ,maps,candidates,histL,histR,bitBase,rowOut,work,dst]
      μ (time J L U) (fun _ ν =>
        ν dst = (product (rowFlag L h p cap sel candidate bits w0 w1 leftCount) J : ℤ) ∧
        ν (dst+1) = (product (rowFlag L h p cap sel candidate bits w1 w0 rightCount) J : ℤ) ∧
        KeptBut μ ν rowOut dst 2) := by
  have hspace' : work+3+(Nat.log 2 (L*U+1)+2) ≤ lim.space := hspace
  have h1 : (1 : ℤ) ≤ lim.word := by
    have hh : 1 ≤ LightSourceRowFlag.word L p U V cap := by
      unfold LightSourceRowFlag.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hleftFlag (j : ℕ) :
      rowFlag L h p cap sel candidate bits w0 w1 leftCount j ≤ 1 := rowFlag_le ..
  have hrightFlag (j : ℕ) :
      rowFlag L h p cap sel candidate bits w1 w0 rightCount j ≤ 1 := rowFlag_le ..
  have hleftPrefix (j : ℕ) :
      product (rowFlag L h p cap sel candidate bits w0 w1 leftCount) j ≤ 1 :=
    product_le _ (n := j) (fun i _ => hleftFlag i) le_rfl
  have hrightPrefix (j : ℕ) :
      product (rowFlag L h p cap sel candidate bits w1 w0 rightCount) j ≤ 1 :=
    product_le _ (n := j) (fun i _ => hrightFlag i) le_rfl
  apply Meets.of_body S.main
  unfold body time
  light_set 1
  light_set 1
  refine Ends.pieceThen (Ends.for
    (Inv μ J L h p cap occ maps candidates histL histR bitBase rowOut work dst
      sel candidate bits w0 w1 leftCount rightCount) J (LightSourceRowFlag.time L U+242)
    ?start ?round ?done ?bound
    (Q := Inv μ J L h p cap occ maps candidates histL histR bitBase rowOut work dst
      sel candidate bits w0 w1 leftCount rightCount J)
    (T := J*(LightSourceRowFlag.time L U+250)+6) (hT := by light_time)) ?finish
  case start =>
    refine ⟨0,μ,?_,fun _ _ => rfl⟩
    simp only [product_zero]
    exact congrArg (fun loc => (⟨loc,μ⟩ : State))
      ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
  case round =>
    rintro j _ hj _ ⟨r,ν,rfl,kept⟩
    have hs := hsel j hj
    have hk := hcandidate (sel j) hs
    have hocc' : ν (occ+j) = (sel j : ℤ) :=
      (kept _ (by omega)).trans (hoccRead j hj)
    have hcan' : ν (candidates+sel j) = (candidate (sel j) : ℤ) :=
      (kept _ (by omega)).trans (hcandidateRead (sel j) hs)
    have hbEnd : j*L+L ≤ J*L := by
      have hh := Nat.mul_le_mul_right L (show j+1 ≤ J by omega)
      simpa only [Nat.succ_mul] using hh
    have hmEnd : 2*L*sel j+L+L ≤ 2*L*M := by
      have hh := Nat.mul_le_mul_left (2*L) (show sel j+1 ≤ M by omega)
      nlinarith
    have htEnd : candidate (sel j)*p+p ≤ K*p := by
      have hh := Nat.mul_le_mul_right p (show candidate (sel j)+1 ≤ K by omega)
      simpa only [Nat.succ_mul] using hh
    have hdoubleNonneg : (0 : ℤ) ≤ 2*(L : ℤ) := by positivity
    have hdoubleWord : 2*(L : ℤ) ≤ lim.word := by
      have hm : 2*L ≤ 2*L*M := Nat.le_mul_of_pos_right _ (by omega)
      exact (by exact_mod_cast (show 2*L ≤ lim.space by omega) :
        2*(L : ℤ) ≤ lim.space).trans hw
    have hmapNonneg : (0 : ℤ) ≤ 2*(L : ℤ)*(sel j : ℤ) := by positivity
    have hmapWord : 2*(L : ℤ)*(sel j : ℤ) ≤ lim.word := by
      exact (by exact_mod_cast (show 2*L*sel j ≤ lim.space by omega) :
        2*(L : ℤ)*(sel j : ℤ) ≤ lim.space).trans hw
    have hmapEndZ : (maps : ℤ)+2*(L : ℤ)*(sel j : ℤ)+(L : ℤ)+(L : ℤ) ≤ rowOut := by
      exact_mod_cast (show maps+2*L*sel j+L+L ≤ rowOut by omega)
    have hbRead : ∀ a < L, ν (bitBase+j*L+a) = (bits (j*L+a) : ℤ) := by
      intro a ha
      exact (kept _ (by omega)).trans (by simpa only [Nat.add_assoc] using hbitsRead (j*L+a) (by omega))
    have hw0 : ∀ a < L, ν (maps+2*L*sel j+a) = (w0 (sel j) a : ℤ) := by
      intro a ha
      exact (kept _ (by omega)).trans (hread0 (sel j) hs a ha)
    have hw1 : ∀ a < L, ν (maps+2*L*sel j+L+a) = (w1 (sel j) a : ℤ) := by
      intro a ha
      exact (kept _ (by omega)).trans (hread1 (sel j) hs a ha)
    have hcL : ∀ r < p, ν (histL+candidate (sel j)*p+r) =
        (leftCount (candidate (sel j)) r : ℤ) := by
      intro r hr
      exact (kept _ (by omega)).trans (hcountL _ hk r hr)
    have hcR : ∀ r < p, ν (histR+candidate (sel j)*p+r) =
        (rightCount (candidate (sel j)) r : ℤ) := by
      intro r hr
      exact (kept _ (by omega)).trans (hcountR _ hk r hr)
    have hrow := LightSourceRowFlag.meets (d := d+1) (μ := ν)
      (src := bitBase+j*L) (src0 := maps+2*L*sel j) (src1 := maps+2*L*sel j+L)
      (L := L) (h := h) (histL := histL+candidate (sel j)*p)
      (histR := histR+candidate (sel j)*p) (p := p) (cap := cap)
      (dst := rowOut) (work := work) (U := U) (V := V)
      S.rowFlagDef S.row S.emod S.flag (fun a => bits (j*L+a))
      (w0 (sel j)) (w1 (sel j)) (leftCount (candidate (sel j))) (rightCount (candidate (sel j)))
      hw (by omega) hp hh (by omega) (by omega) (by omega) (by omega) (by omega) hrowOut
      hspace hword hbRead hw0 hw1 (fun a ha => hbitBound (j*L+a) (by omega))
      (hbound0 (sel j) hs) (hbound1 (sel j) hs)
      hcL hcR (hcountBoundL _ hk) (hcountBoundR _ hk)
    unfold roundBody
    light_call hrow using hocc',hcan',
      LightSourceRowFlag.time,LightSourceRowScan.time,LightResidues.residueBudget,LightSourceFlagTest.time
      with q ν₁ ⟨leftRead,rightRead,hkeep⟩
    have hlRead : ν₁ rowOut = (rowFlag L h p cap sel candidate bits w0 w1 leftCount j : ℤ) := leftRead
    have hrRead : ν₁ (rowOut+1) = (rowFlag L h p cap sel candidate bits w1 w0 rightCount j : ℤ) := rightRead
    have hlB := hleftPrefix (j+1)
    have hrB := hrightPrefix (j+1)
    have hlCast : (product (rowFlag L h p cap sel candidate bits w0 w1 leftCount) j : ℤ)*
        (rowFlag L h p cap sel candidate bits w0 w1 leftCount j : ℤ) =
        (product (rowFlag L h p cap sel candidate bits w0 w1 leftCount) (j+1) : ℤ) := by
      rw [product_succ,Nat.cast_mul]
    have hrCast : (product (rowFlag L h p cap sel candidate bits w1 w0 rightCount) j : ℤ)*
        (rowFlag L h p cap sel candidate bits w1 w0 rightCount j : ℤ) =
        (product (rowFlag L h p cap sel candidate bits w1 w0 rightCount) (j+1) : ℤ) := by
      rw [product_succ,Nat.cast_mul]
    light_set (product (rowFlag L h p cap sel candidate bits w0 w1 leftCount) (j+1) : ℕ)
      using hlRead,hlCast,LightSourceRowFlag.time,LightSourceRowScan.time,LightResidues.residueBudget,LightSourceFlagTest.time
    light_set (product (rowFlag L h p cap sel candidate bits w1 w0 rightCount) (j+1) : ℕ)
      using hrRead,hrCast,LightSourceRowFlag.time,LightSourceRowScan.time,LightResidues.residueBudget,LightSourceFlagTest.time
    refine ⟨by simp,q,ν₁,by simp [update_frame_setLocal],?_⟩
    intro a ha
    exact (hkeep a ⟨by omega,Or.inl ha⟩).trans (kept a ha)
  case done =>
    intro σ hj hshape
    exact hshape
  case bound =>
    rintro j _ hj _ ⟨r,ν,rfl,_⟩
    simp
  case finish =>
    rintro _ ⟨r,ν,rfl,kept⟩
    have hl := hleftPrefix J
    have hr := hrightPrefix J
    light_store dst (product (rowFlag L h p cap sel candidate bits w0 w1 leftCount) J : ℕ)
    light_store (dst+1) (product (rowFlag L h p cap sel candidate bits w1 w0 rightCount) J : ℕ)
    refine ⟨by simp,by simp,?_⟩
    intro a ⟨ha,hout⟩
    simp only [Function.update_of_ne (show a ≠ dst+1 by omega),
      Function.update_of_ne (show a ≠ dst by omega)]
    exact kept a ha

def program : Program :=
  [body 1,LightSourceRowFlag.body 2 3 4,LightSourceRowScan.body,emodBody,LightSourceFlagTest.body]

def programProcs : Procs program 0 := ⟨1,2,3,4,rfl,rfl,rfl,rfl,rfl⟩

theorem time_bound (J L U : ℕ) :
    time J L U ≤ J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+100 := by
  have hh := LightSourceRowFlag.time_bound L U
  unfold time
  exact Nat.add_le_add_right (Nat.mul_le_mul_left J (Nat.add_le_add_right hh 250)) 100

end ThreeSum.LightSourceTrim
