import Submission.ThreeSum.LightTernaryWantedCanonical

namespace ThreeSum.LightTernaryWantedBatch
open Light LightTernaryWantedCanonical
open TernaryWantedLittleEndian (wantedCodes)
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

def body : Stmt :=
  .set 7 (v 4) ;;
  .for 6 (v 3) (
    .call 0 [v 0,M (v 1 +' v 6),k 0,k 1,k 0,k 1,M (v 2 +' v 6),v 7,v 5] 7) ;;
  .set 0 (v 7)

def program (P R S : ℕ) (raws : List ℤ) (words maps : List ℕ) : Program :=
  LightTernaryWantedCanonical.program P R S raws words maps++[body]

def rows (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) (positions : ℕ → ℕ) : ℕ → List ℤ
  | 0 => []
  | n+1 => rows P R S J raws words maps targets positions n++
      rowCells (positions n) (wantedCodes (P : ℤ) raws words maps J (targets n) R S 0 1 0 1)

theorem rows_length_le (P R S J C : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) (positions : ℕ → ℕ)
    (hcap : ∀ x, (TernaryWantedRadix.localBucket (P : ℤ) raws x).length≤C) (n : ℕ) :
    (rows P R S J raws words maps targets positions n).length≤3*n*C^J := by
  induction n with
  | zero => simp [rows]
  | succ n ih =>
    have hh := TernaryWantedRadix.wantedOutputs_length_le (P : ℤ) raws C hcap J (targets n)
    simp only [rows,List.length_append,rowCells_length,TernaryWantedLittleEndian.wantedCodes_length]
    nlinarith

def time (P C V J n : ℕ) : ℕ :=
  n*((overhead P V+stepCost V+40)*(J+1)*C^J+100)+50

def Inv (μ : ℕ → ℤ) (P R S J targetBase positionBase n dst work : ℕ)
    (raws : List ℤ) (words maps : List ℕ) (targets : ℕ → ℤ) (positions : ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ ν : ℕ → ℤ,
    σ=⟨frame [J,targetBase,positionBase,n,dst,work,i,
      dst+(rows P R S J raws words maps targets positions i).length],ν⟩ ∧
    Seg ν dst (rows P R S J raws words maps targets positions i) ∧ Kept μ ν dst

variable {lim : Limits}

theorem program_meets {P R S C V work J d targetBase positionBase n dst : ℕ}
    {raws : List ℤ} {words maps : List ℕ}
    (hp : 2≤P) (hN : 1≤raws.length) (hR : 1≤R) (hS : 1≤S) (hC : 1≤C)
    (hcap : ∀ x, (TernaryWantedRadix.localBucket (P : ℤ) raws x).length≤C)
    (hraw : ∀ i<raws.length, |raws.getD i 0|≤(V : ℤ))
    (hwords : ∀ i<raws.length, words.getD i 0<R)
    (hmaps : ∀ i<raws.length, maps.getD i 0<S)
    (hRW : (R : ℤ)≤lim.word) (hSW : (S : ℤ)≤lim.word)
    (hNW : (raws.length : ℤ)≤lim.word) (F : Emod.Pre lim P (2*V) work)
    (μ : ℕ → ℤ) (targets : ℕ → ℤ) (positions : ℕ → ℕ)
    (htarget : targetBase+n≤dst) (hpositions : positionBase+n≤dst)
    (htRead : ∀ i<n, μ (targetBase+i)=targets i)
    (hpRead : ∀ i<n, μ (positionBase+i)=(positions i : ℤ))
    (htBound : ∀ i<n, |targets i|≤(V : ℤ))
    (hc : (((2*R)^J : ℕ) : ℤ)≤lim.word) (hm : (((2*S)^J : ℕ) : ℤ)≤lim.word)
    (ho : ∀ i<n, (positions i : ℤ)≤lim.word) (hJ : (J : ℤ)≤lim.word)
    (hs : dst+3*n*C^J≤work) (hd : d+J+4≤lim.depth) :
    Meets lim (program P R S raws words maps) 4 d
      [J,targetBase,positionBase,n,dst,work] μ (time P C V J n)
      (fun r ν => r=((dst+(rows P R S J raws words maps targets positions n).length : ℕ) : ℤ) ∧
        Seg ν dst (rows P R S J raws words maps targets positions n) ∧ Kept μ ν dst) := by
  have hw := F.space
  have hwork := F.free
  apply Meets.of_body (by rfl)
  unfold body time
  light_set (dst : ℕ)
  refine Ends.pieceThen (Ends.for
    (T := n*((overhead P V+stepCost V+40)*(J+1)*C^J+100)+10)
    (Q := Inv μ P R S J targetBase positionBase n dst work raws words maps targets positions n)
    (Inv μ P R S J targetBase positionBase n dst work raws words maps targets positions) n
    ((overhead P V+stepCost V+40)*(J+1)*C^J+90)
    ?start ?round ?done ?bound) ?finish
  case start =>
    refine ⟨μ,?_,?_,SameOn.refl⟩
    · simp [rows,update_frame_setLocal]
    · simp [rows,Seg]
  case round =>
    rintro i _ hi _ ⟨ν,rfl,written,kept⟩
    let outPrefix := rows P R S J raws words maps targets positions i
    have hlen := rows_length_le P R S J C raws words maps targets positions hcap i
    have hinc : 3*(i+1)*C^J≤3*n*C^J :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 (by omega : i+1≤n))
    have hcursor : dst+outPrefix.length+3*C^J≤work := by dsimp [outPrefix]; nlinarith
    have hcursorWord : ((dst+(rows P R S J raws words maps targets positions i).length : ℕ) : ℤ)≤lim.word := by
      have hh : dst+(rows P R S J raws words maps targets positions i).length≤lim.space := by
        change dst+outPrefix.length≤lim.space
        omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have htr : ν (targetBase+i)=targets i := (kept _ (by omega)).trans (htRead i hi)
    have hpr : ν (positionBase+i)=(positions i : ℤ) := (kept _ (by omega)).trans (hpRead i hi)
    have htargetaddr : ((targetBase : ℤ)+(i : ℤ)).toNat=targetBase+i := by omega
    have hpositionaddr : ((positionBase : ℤ)+(i : ℤ)).toNat=positionBase+i := by omega
    have hcall := (LightTernaryWantedCanonical.program_from_zero (d := d+1) hp hN hR hS hC
      hcap hraw hwords hmaps hRW hSW hNW F (targets i) (positions i) (dst+outPrefix.length) ν
      (htBound i hi) hc hm (ho i hi) hJ hcursor (by omega)).append [body]
    light_call hcall using htr,hpr,htargetaddr,hpositionaddr,frame,outPrefix
      with r ξ ⟨hr,hrBound,hseg,hkeep⟩
    refine ⟨by simp,ξ,?_,?_,?_⟩
    · simp [rows,outPrefix,List.length_append,hr,update_frame_setLocal,add_assoc]
    · rw [rows]
      apply (seg_append).mpr
      refine ⟨?_,hseg⟩
      intro k hk
      rw [hkeep _ (by dsimp [outPrefix]; omega)]
      exact written k hk
    · intro k hk
      exact (hkeep _ (by omega)).trans (kept _ hk)
  case done => rintro _ _ h; exact h
  case bound => rintro i _ _ _ ⟨ν,rfl,_,_⟩; light_side
  case finish =>
    rintro _ ⟨ν,rfl,written,kept⟩
    have hlen := rows_length_le P R S J C raws words maps targets positions hcap n
    light_set (dst+(rows P R S J raws words maps targets positions n).length : ℕ)
    exact ⟨rfl,written,kept⟩

end ThreeSum.LightTernaryWantedBatch
