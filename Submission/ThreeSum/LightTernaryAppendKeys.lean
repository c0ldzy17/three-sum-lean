import Submission.ThreeSum.LightSignedRowHash

namespace ThreeSum.LightTernaryAppendKeys
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 6000

def body (pHash : ℕ) : Stmt :=
  .for 9 (v 4) (
    .call pHash [v 0 +' v 9 *' v 5,v 1,v 8,v 5,v 6] 10 ;;
    .store (v 3 +' v 9) (M (v 2 +' v 9) +' v 7 *' v 10))

def key (p power len : ℕ) (old : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (c : ℕ → ℕ) (i : ℕ) : ℕ :=
  old i+power*(LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len%p)

def time (n len p b : ℕ) : ℕ := n*(LightSignedRowHash.time len p b+120)+30
def word (len p b power : ℕ) : ℕ := LightSignedRowHash.word len p b+power*p+100

structure Procs (P : Program) (main : ℕ) where
  hash : ℕ
  mainBody : P[main]?=some (body hash)
  hashProcs : LightSignedRowHash.Procs P hash

def Inv (μ : ℕ → ℤ) (matrix row oldBase dst n len p power scratch : ℕ)
    (old : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (c : ℕ → ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (val : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [matrix,row,oldBase,dst,n,len,p,power,scratch,i,val],ν⟩ ∧
    (∀ j<i, ν (dst+j)=(key p power len old z c j : ℤ)) ∧ Kept μ ν dst

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem Procs.meets {main matrix row oldBase dst n len p power scratch b : ℕ}
    (S : Procs P main) (μ : ℕ → ℤ) (old : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (c : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+3<lim.depth) (hbp : b<p)
    (hmatrix : matrix+n*len≤dst) (hrow : row+len≤dst) (hold : oldBase+n≤dst)
    (hout : dst+n≤scratch) (hspace : scratch+len≤lim.space)
    (hmRead : ∀ i<n, ∀ k<len, μ (matrix+i*len+k)=z i k)
    (hcRead : ∀ k<len, μ (row+k)=(c k : ℤ))
    (hoRead : ∀ i<n, μ (oldBase+i)=(old i : ℤ))
    (hzBound : ∀ i<n, ∀ k<len, |z i k|≤(b : ℤ))
    (hcBound : ∀ k<len, c k≤p) (hoBound : ∀ i<n, old i<power)
    (hword : (word len p b power : ℤ)≤lim.word) :
    Meets lim P main depth [matrix,row,oldBase,dst,n,len,p,power,scratch] μ (time n len p b)
      (fun _ ν => (∀ i<n, ν (dst+i)=(key p power len old z c i : ℤ)) ∧ Kept μ ν dst) := by
  have hp : 0<p := by omega
  have hwHash : (LightSignedRowHash.word len p b : ℤ)≤lim.word := by unfold word at hword; omega
  have hpowerWord : (power : ℤ)≤lim.word := by
    have hh : power≤power*p := Nat.le_mul_of_pos_right _ hp
    unfold word at hword
    omega
  have hpowerPWord : ((power*p : ℕ) : ℤ)≤lim.word := by unfold word at hword; omega
  have hnWord : (n : ℤ)≤lim.word := by omega
  have hkeyBound (i : ℕ) (hi : i<n) : key p power len old z c i<power*p := by
    have hh := Nat.mod_lt (LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len) hp
    have ho := hoBound i hi
    unfold key
    nlinarith
  have hkeyWord (i : ℕ) (hi : i<n) : ((key p power len old z c i : ℕ) : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (hkeyBound i hi).le).trans hpowerPWord
  apply Meets.of_body S.mainBody
  unfold body time
  refine Ends.for (Inv μ matrix row oldBase dst n len p power scratch old z c) n
    (LightSignedRowHash.time len p b+110) ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,μ,?_,?_,SameOn.refl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro i hi; omega
  case round =>
    rintro i _ hi _ ⟨val,ν,rfl,written,kept⟩
    have hprod : i*len+len≤n*len := by nlinarith
    have hmatrixEnd : matrix+i*len+len≤scratch := by omega
    have hmValues (k : ℕ) (hk : k<len) : ν (matrix+i*len+k)=z i k :=
      (kept _ (by omega)).trans (hmRead i hi k hk)
    have hcValues (k : ℕ) (hk : k<len) : ν (row+k)=(c k : ℤ) :=
      (kept _ (by omega)).trans (hcRead k hk)
    have hoValues : ν (oldBase+i)=(old i : ℤ) :=
      (kept _ (by omega)).trans (hoRead i hi)
    have hrowEnd : row+len≤scratch := by omega
    have hrowWord : ((i*len : ℕ) : ℤ)≤lim.word := by omega
    unfold key at hkeyWord
    unfold body at *
    light_call (S.hashProcs.meets (depth := depth+1) ν (z i) c hw (by omega) hbp
      hmatrixEnd hrowEnd hspace hmValues hcValues (hzBound i hi) hcBound hwHash)
      using LightSignedRowHash.time with r ξ ⟨hr,hkeep⟩
    have hoNew : ξ (oldBase+i)=(old i : ℤ) := (hkeep _ (Or.inl (by omega))).trans hoValues
    have haddr : ((oldBase : ℤ)+(i : ℤ)).toNat=oldBase+i := by omega
    have hoWord : (old i : ℤ)≤lim.word := by have hh := hoBound i hi; omega
    have hhashBound := Nat.mod_lt (LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len) hp
    have hhashWord : (((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len)%p : ℕ) : ℤ)≤lim.word := by
      have hpWord : (p : ℤ)≤lim.word := by unfold LightSignedRowHash.word at hwHash; omega
      omega
    have hmulWord : ((power*(LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len%p) : ℕ) : ℤ)≤lim.word := by
      have hh := hkeyWord i hi
      omega
    have hmodcast : ((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len : ℕ) : ℤ)%(p : ℤ)=
        ((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len%p : ℕ) : ℤ) := by norm_cast
    have hmulNonneg : 0≤(power : ℤ)*(((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len%p : ℕ) : ℤ)) := by positivity
    have hprodIntNonneg : 0≤(power : ℤ)*(((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len : ℕ) : ℤ)%(p : ℤ)) := by rw [hmodcast]; positivity
    have hprodIntWord : (power : ℤ)*(((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len : ℕ) : ℤ)%(p : ℤ))≤lim.word := by
      rw [hmodcast]
      exact_mod_cast hmulWord
    have hoMemNonneg : 0≤ξ (oldBase+i) := by rw [hoNew]; positivity
    have hsumMemWord : ξ (oldBase+i)+(power : ℤ)*(((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len : ℕ) : ℤ)%(p : ℤ))≤lim.word := by
      rw [hoNew,hmodcast]
      exact_mod_cast hkeyWord i hi
    light_store (dst+i) (key p power len old z c i) using key,hr,hoNew,haddr,frame,LightSignedRowHash.time
    refine ⟨by simp [frame],r,Function.update ξ (dst+i) (key p power len old z c i : ℤ),
      by simp [update_frame_setLocal],?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega),hkeep _ (Or.inl (by omega))]
        exact written j hj
      · simp
    · intro j hj
      rw [Function.update_of_ne (by omega),hkeep _ (Or.inl (by omega)),kept _ hj]
  case done => rintro _ _ ⟨val,ν,rfl,written,kept⟩; exact ⟨written,kept⟩
  case bound => rintro i _ _ _ ⟨val,ν,rfl,_,_⟩; light_side


def program : Program := LightSignedRowHash.program++[body 0]

def procs : Procs program 6 where
  hash := 0
  mainBody := rfl
  hashProcs := {
    lift := 1,dot := 2,rawDot := 3,digit := 4,divide := 5,
    mainBody := rfl,liftBody := rfl,dotBody := rfl,rawBody := rfl,
    digitBody := rfl,divideBody := rfl }

theorem key_lt (p power len : ℕ) (old : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (c : ℕ → ℕ) (i : ℕ)
    (hp : 0<p) (ho : old i<power) : key p power len old z c i<power*p := by
  have hm := Nat.mod_lt (LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len) hp
  unfold key
  nlinarith

end ThreeSum.LightTernaryAppendKeys
