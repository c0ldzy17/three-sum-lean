import Submission.ThreeSum.LightTernaryEulerRow

/-!
# A physical memo fill for one ascending rank layer

Rows whose stored rank equals the current rank are filled once. Every
predecessor value address must be outside this rank layer; the scan therefore
preserves all its numerator inputs while filling successive memo cells.
-/

namespace ThreeSum.LightTernaryEulerScan

open Light

set_option maxHeartbeats 1800000

def stageValue (μ : ℕ → ℤ) (f : ℕ → ℤ) (rank : ℕ → ℕ)
    (vals current j a : ℕ) : ℤ :=
  if vals ≤ a ∧ a < vals+j ∧ rank (a-vals)=current then f (a-vals) else μ a

def Stored (μ ν : ℕ → ℤ) (f : ℕ → ℤ) (rank : ℕ → ℕ)
    (vals current fr j : ℕ) : Prop :=
  ∀ a < fr, ν a=stageValue μ f rank vals current j a

theorem stageValue_below (μ : ℕ → ℤ) (f : ℕ → ℤ) (rank : ℕ → ℕ)
    {vals current j a : ℕ} (ha : a < vals) :
    stageValue μ f rank vals current j a=μ a := by
  simp [stageValue,show ¬ vals ≤ a by omega]

theorem stageValue_succ_of_ne (μ : ℕ → ℤ) (f : ℕ → ℤ) (rank : ℕ → ℕ)
    {vals current j a : ℕ} (hne : a ≠ vals+j) :
    stageValue μ f rank vals current (j+1) a=stageValue μ f rank vals current j a := by
  unfold stageValue
  have hh : (vals ≤ a ∧ a < vals+(j+1) ∧ rank (a-vals)=current) ↔
      (vals ≤ a ∧ a < vals+j ∧ rank (a-vals)=current) := by omega
  simp only [hh]

theorem Stored.next {μ ν ξ : ℕ → ℤ} {f : ℕ → ℤ} {rank : ℕ → ℕ}
    {vals current fr j : ℕ} (H : Stored μ ν f rank vals current fr j)
    (hrank : rank j=current) (hwrite : ξ (vals+j)=f j)
    (hkeep : ∀ a < fr, a ≠ vals+j → ξ a=ν a) :
    Stored μ ξ f rank vals current fr (j+1) := by
  intro a ha
  by_cases he : a=vals+j
  · subst a
    simpa [stageValue,hrank] using hwrite
  · rw [hkeep a ha he, H a ha, stageValue_succ_of_ne μ f rank he]

theorem Stored.skip {μ ν : ℕ → ℤ} {f : ℕ → ℤ} {rank : ℕ → ℕ}
    {vals current fr j : ℕ} (H : Stored μ ν f rank vals current fr j)
    (hrank : rank j≠current) : Stored μ ν f rank vals current fr (j+1) := by
  intro a ha
  rw [H a ha]
  by_cases he : a=vals+j
  · subst a
    simp [stageValue,hrank]
  · exact (stageValue_succ_of_ne μ f rank he).symm

/-- The actual row caller uses [ws,ks,0,N,pcount,current-h,fr,dst]. -/
def loopBody (pFill : ℕ) : Stmt :=
  .ite (M (v 4 +' v 10) =' v 6)
    (.call pFill [v 2 +' v 0 *' v 10,v 3 +' v 0 *' v 10,k 0,v 0,v 8,
      v 6 -' v 7,v 9,v 5 +' v 10] 11)
    .skip

def body (pFill : ℕ) : Stmt :=
  .for 10 (v 1) (loopBody pFill) ;;
  .set 0 (k 0)

def time (N rows V : ℕ) : ℕ := rows*(LightTernaryEulerRow.fillTime N V+150)+100

def Inv (μ : ℕ → ℤ) (f : ℕ → ℤ) (rank : ℕ → ℕ)
    (N rows ws ks ranks vals current h pcount fr j : ℕ) (σ : State) : Prop :=
  ∃ (rval : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [N,rows,ws,ks,ranks,vals,current,h,pcount,fr,j,rval],ν⟩ ∧
      Stored μ ν f rank vals current fr j

variable {lim : Limits} {P : Program} {d : ℕ}

/-- This contract requires physical metadata and exact Euler numerators.
The row computation is the fully specified four-procedure arithmetic kernel,
not an oracle call. Its read addresses may span bank and prior memo layers. -/
theorem meets {pMain pFill pRow pSum pDivide pNaturalDivide N rows ws ks ranks vals current h pcount fr U V : ℕ}
    (hmain : P[pMain]?=some (body pFill))
    (hfill : P[pFill]?=some (LightTernaryEulerRow.fillBody pRow))
    (hrow : P[pRow]?=some (LightTernaryEulerRow.body pSum pDivide))
    (hsum : P[pSum]?=some LightTernaryWeightedSum.body)
    (hdivide : P[pDivide]?=some (LightTernaryDivide.body pNaturalDivide))
    (hnatural : P[pNaturalDivide]?=some LightOutputDecodeDivide.body)
    (μ : ℕ → ℤ) (weights keys : ℕ → ℕ → ℕ) (g f : ℕ → ℤ) (rank : ℕ → ℕ)
    (F : Light.Emod.Pre lim (current-h) V fr) (hh : h ≤ current)
    (hws : ws+N*rows ≤ vals) (hks : ks+N*rows ≤ vals) (hranks : ranks+rows ≤ vals)
    (hvals : vals+rows ≤ fr) (hspace : pcount ≤ lim.space)
    (hrankRead : ∀ j < rows, μ (ranks+j)=(rank j : ℤ))
    (hweights : ∀ j < rows, ∀ i < N, μ (ws+N*j+i)=(weights j i : ℤ))
    (hkeys : ∀ j < rows, ∀ i < N, μ (ks+N*j+i)=(keys j i : ℤ))
    (hrange : ∀ j < rows, ∀ i < N, keys j i < pcount ∧ keys j i < fr)
    (hread : ∀ j < rows, rank j=current → ∀ i < N, μ (keys j i)=g (keys j i))
    (hweight : ∀ j < rows, ∀ i < N, weights j i ≤ 2)
    (hvalue : ∀ j < rows, rank j=current → ∀ i < N, |g (keys j i)| ≤ U)
    (hpre : ∀ j < rows, rank j=current → ∀ i < N, ∀ k < rows,
      rank k=current → keys j i ≠ vals+k)
    (hEuler : ∀ j < rows, rank j=current →
      LightTernaryWeightedSum.sum (weights j) (keys j) g N=(current-h : ℕ)*f j)
    (hV : 2*(N+1)*U ≤ V) (hd : d+4 ≤ lim.depth)
    (hcontrols : ((N+rows+current+h+pcount+fr+20 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pMain d [N,rows,ws,ks,ranks,vals,current,h,pcount,fr] μ
      (time N rows V)
      (fun r ν => r=0 ∧ Stored μ ν f rank vals current fr rows) := by
  light_facts F
  have hfr : fr ≤ lim.space := by omega
  have hwsWord : (ws : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : ws≤lim.space)).trans F.space
  have hksWord : (ks : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : ks≤lim.space)).trans F.space
  have hranksWord : (ranks : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : ranks≤lim.space)).trans F.space
  have hvalsWord : (vals : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : vals≤lim.space)).trans F.space
  have hcall {j : ℕ} (hj : j<rows) (ν : ℕ → ℤ)
      (H : Stored μ ν f rank vals current fr j) (hjrank : rank j=current) :
      Meets lim P pFill (d+1)
        [(ws+N*j : ℕ),(ks+N*j : ℕ),(0 : ℕ),N,pcount,(current-h : ℕ),fr,(vals+j : ℕ)] ν
        (LightTernaryEulerRow.fillTime N V)
        (fun r ξ => r=f j ∧ ξ (vals+j)=f j ∧
          ∀ a<fr, a≠vals+j → ξ a=ν a) := by
    have hcoef (i : ℕ) (hi : i<N) : ws+N*j+i < vals := by nlinarith
    have hkey (i : ℕ) (hi : i<N) : ks+N*j+i < vals := by nlinarith
    have hpred (i : ℕ) (hi : i<N) : ν (keys j i)=g (keys j i) := by
      rw [H _ (hrange j hj i hi).2]
      have hn : ¬ (vals ≤ keys j i ∧ keys j i < vals+j ∧ rank (keys j i-vals)=current) := by
        intro hc
        let k := keys j i-vals
        have hk : k<rows := by dsimp [k]; omega
        have he : keys j i=vals+k := by dsimp [k]; omega
        exact hpre j hj hjrank i hi k hk hc.2.2 he
      simp only [stageValue,if_neg hn]
      exact hread j hj hjrank i hi
    apply LightTernaryEulerRow.fill_meets hfill hrow hsum hdivide hnatural ν
      (weights j) (keys j) g F
    · nlinarith
    · nlinarith
    · simpa using hspace
    · intro i hi
      rw [H _ (by have hc := hcoef i hi; omega),stageValue_below μ f rank (hcoef i hi)]
      exact hweights j hj i hi
    · intro i hi
      rw [H _ (by have hc := hkey i hi; omega),stageValue_below μ f rank (hkey i hi)]
      exact hkeys j hj i hi
    · exact fun i hi => (hrange j hj i hi).1
    · simpa using hpred
    · exact hweight j hj
    · exact hvalue j hj hjrank
    · exact hV
    · exact hEuler j hj hjrank
    · omega
    · omega
  apply Meets.of_body hmain
  unfold body time
  refine Ends.pieceThen (Ends.for (T := rows*(LightTernaryEulerRow.fillTime N V+150)+20)
    (Q := Inv μ f rank N rows ws ks ranks vals current h pcount fr rows)
    (Inv μ f rank N rows ws ks ranks vals current h pcount fr)
    rows (LightTernaryEulerRow.fillTime N V+100)
    ?start ?round ?done ?bound (hT := by light_time)) ?after (hT := by light_time)
  case start =>
    refine ⟨0,μ,?_,?_⟩
    · simpa [update_frame_setLocal,setLocal] using
        congrArg (fun loc => (⟨loc,μ⟩ : State))
          (frame_append_zeros ([N,rows,ws,ks,ranks,vals,current,h,pcount,fr,0] : List ℤ) 1).symm
    · intro a ha
      unfold stageValue
      rw [if_neg (by omega)]
  case round =>
    rintro j _ hj _ ⟨rval,ν,rfl,H⟩
    have hrspace : ranks+j < vals := by omega
    have hrread : ν (ranks+j)=(rank j : ℤ) := by
      rw [H _ (by omega),stageValue_below μ f rank hrspace]
      exact hrankRead j hj
    have hwsN : ws+N*j+N ≤ vals := by nlinarith
    have hksN : ks+N*j+N ≤ vals := by nlinarith
    have hprodWord : ((N*j : ℕ) : ℤ) ≤ lim.word := by
      have hs : N*j ≤ lim.space := by nlinarith
      exact (Int.ofNat_le.mpr hs).trans F.space
    have hdstWord : ((vals+j : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (by omega : vals+j≤lim.space)).trans F.space
    have hdiff : ((current-h : ℕ) : ℤ)=(current : ℤ)-(h : ℤ) := Nat.cast_sub hh
    unfold loopBody
    light_if hy hn : rank j=current using hrread
    · have hc := hcall hj ν H hy
      light_call hc using hdiff,LightTernaryEulerRow.fillTime,LightTernaryEulerRow.time,
        LightTernaryWeightedSum.time,LightTernaryDivide.time
        with result ξ ⟨hresult,hwrite,hkeep⟩
      refine ⟨by simp,result,ξ,?_,H.next hy hwrite hkeep⟩
      simp [update_frame_setLocal]
    · apply Ends.skip
      refine ⟨by simp,rval,ν,?_,H.skip hn⟩
      simp [update_frame_setLocal]
  case done => intro σ hcounter hshape; exact hshape
  case bound => rintro j _ hj _ ⟨rval,ν,rfl,H⟩; light_side
  case after =>
    rintro _ ⟨rval,ν,rfl,H⟩
    light_set 0
    exact ⟨rfl,H⟩

end ThreeSum.LightTernaryEulerScan
