import Submission.ThreeSum.LightExtensionBackend
import Submission.ThreeSum.LightExtensionMenuBudget
import Submission.ThreeSum.LightIrreducibleBudget

/-! A concrete scalar allocation for the fully executed extension backend.
Only the base address occurs in the storage bound; all extra space and word
slack is a fixed polynomial in the true finite-field parameters. -/
namespace ThreeSum.LightExtensionBackendLayout
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

def target (base d : ℕ) := base+2*d+1
def ctx (base d : ℕ) := target base d+2*d
def table (base d : ℕ) := ctx base d+10
def logical (base d q : ℕ) := table base d+q*q
def physical (base d q J : ℕ) := logical base d q+q*q*(J+2)
def a (base d q J : ℕ) := physical base d q J+q*q*(J+2)
def b (base d q J : ℕ) := a base d q J+d
def h (base d q J : ℕ) := b base d q J+d
def r (base d q J : ℕ) := h base d q J+d
def prod (base d q J : ℕ) := r base d q J+2*d
def sum (base d q J : ℕ) := prod base d q J+2*d

def factor (base d p q J : ℕ) : LightExtensionFactorPredicate.Layout where
  p := p
  dim := d
  degree := 0
  powers := base
  target := target base d
  left := a base d q J
  right := a base d q J+2*d

def params (d p q J : ℕ) := d+p+q+J+2
def reserve (d p q J : ℕ) := 100000000*(params d p q J)^6

def args (base d p q J : ℕ) : List ℤ :=
  [p,d,q,base,target base d,ctx base d,a base d q J,a base d q J+2*d,
    ctx base d,table base d,logical base d q,physical base d q J,
    a base d q J,b base d q J,h base d q J,r base d q J,prod base d q J,sum base d q J,J]

theorem end_le (base d p q J : ℕ) : sum base d q J+2*d≤base+reserve d p q J := by
  let B := params d p q J
  have hB : 1≤B := by dsimp [B,params]; omega
  have hd : d≤B := by dsimp [B,params]; omega
  have hq : q≤B := by dsimp [B,params]; omega
  have hJ : J≤B := by dsimp [B,params]; omega
  have he : sum base d q J+2*d=base+(13*d+11+q*q+2*q*q*(J+2)) := by
    unfold sum prod r h b a physical logical table ctx target
    ring
  rw [he]
  apply Nat.add_le_add_left
  have hm : 13*d+11+q*q+2*q*q*(J+2)≤13*B+11+B*B+2*B*B*(B+2) := by gcongr
  apply hm.trans
  change 13*B+11+B*B+2*B*B*(B+2)≤100000000*B^6
  have h0 : 1≤B^6 := Nat.one_le_pow _ _ hB
  have h1 : B≤B^6 := by simpa using Nat.pow_le_pow_right hB (show 1≤6 by decide)
  have h2 : B^2≤B^6 := Nat.pow_le_pow_right hB (by decide)
  have h3 : B^3≤B^6 := Nat.pow_le_pow_right hB (by decide)
  ring_nf
  omega

theorem ctx_slack (base d p q J : ℕ) :
    ctx base d+2000000*(params d p q J)^4≤base+reserve d p q J := by
  let B := params d p q J
  have hB : 1≤B := by dsimp [B,params]; omega
  have hd : d≤B := by dsimp [B,params]; omega
  have h0 : 1≤B^6 := Nat.one_le_pow _ _ hB
  have h1 : B≤B^6 := by simpa using Nat.pow_le_pow_right hB (show 1≤6 by decide)
  have h4 : B^4≤B^6 := Nat.pow_le_pow_right hB (by decide)
  change ctx base d+2000000*B^4≤base+100000000*B^6
  unfold ctx target
  omega

variable {lim : Limits}

theorem budget (base d p q J : ℕ) (hp : 1<p) (hd : 0<d) (hq : p^d=q)
    (hw : (lim.space : ℤ)≤lim.word)
    (hspace : base+reserve d p q J≤lim.space) :
    LightExtensionBackend.Budget lim (factor base d p q J)
      q (ctx base d) (ctx base d) (table base d) (logical base d q) (physical base d q J) J
      (a base d q J) (b base d q J) (h base d q J) (r base d q J) (prod base d q J) (sum base d q J)
      (LightIrreducibleFinder.uniformFactorTime d p q) := by
  let B := params d p q J
  have hB : 1≤B := by dsimp [B,params]; omega
  have hdB : d≤B := by dsimp [B,params]; omega
  have hpB : p≤B := by dsimp [B,params]; omega
  have hqB : q≤B := by dsimp [B,params]; omega
  have hJB : J≤B := by dsimp [B,params]; omega
  have hshort : d+p+q+2≤B := by dsimp [B,params]; omega
  have hseedshort : q+p+J+2≤B := by dsimp [B,params]; omega
  have h0 : 1≤B^4 := Nat.one_le_pow _ _ hB
  have h1 : B≤B^4 := by simpa using Nat.pow_le_pow_right hB (show 1≤4 by decide)
  have h2 : B^2≤B^4 := Nat.pow_le_pow_right hB (by decide)
  have h3 : B^3≤B^4 := Nat.pow_le_pow_right hB (by decide)
  have hReserve : ((base+reserve d p q J : ℕ) : ℤ)≤lim.word := (Int.ofNat_le.mpr hspace).trans hw
  have hSlack : ctx base d+2000000*B^4≤base+reserve d p q J := ctx_slack base d p q J
  have bound (x : ℕ) (hx : x≤ctx base d+2000000*B^4) : (x : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (hx.trans hSlack)).trans hReserve
  have hEnd := (end_le base d p q J).trans hspace
  have hFactorWord : LightIrreducibleFinder.uniformFactorWord d p q≤1000000*B^4 :=
    (LightIrreducibleFinder.uniformFactorWord_polynomial d p q hq).trans (by gcongr)
  have hDecode : LightCoefficientDecode.word (2*d) p (2*q) 0 1≤1000000*B^4 := by
    apply le_trans _ hFactorWord
    unfold LightIrreducibleFinder.uniformFactorWord
    omega
  have hTableWord : LightExtensionMultiplyTable.word q (ctx base d) p d base (a base d q J) (b base d q J)≤2000000*B^4 := by
    unfold LightExtensionMultiplyTable.word
    have hm : 30*(q*q+q+p+d+10)≤30*(B*B+B+B+B+10) := by gcongr
    apply hm.trans
    ring_nf
    omega
  have hSeedWord : LightExtensionSeedMatrix.word (J+2) q p≤2000000*B^4 := by
    apply (LightExtensionMenuMatrix.seed_word_polynomial q p J).trans
    have hh : (q+p+J+2)^3≤B^3 := by gcongr
    omega
  refine {
    finder := ?_
    targetCtx := by simp [factor,ctx]
    ctxTable := by simp [table]
    tableLogical := by simp [logical]
    logicalPhysical := by simp [physical]
    physicalA := by simp [a]
    aB := by simp [factor,b]
    bH := by simp [factor,h]
    hR := by simp [factor,r]
    rProduct := by simp [factor,prod]
    productSum := by simp [factor,sum]
    space := by simpa [factor] using hEnd
    tableWord := by simpa [factor] using bound _ (by omega)
    cellWord := ?_
    seedWord := by simpa [factor] using bound _ (show LightExtensionSeedMatrix.word (J+2) q p≤ctx base d+2000000*B^4 by omega) }
  · refine {
      qpos := by rw [←hq]; exact pow_pos (by omega) _
      primeBase := hp
      dimpos := hd
      ctxLeft := ?_
      powersTarget := by simp [factor,target]; omega
      targetCtx := by simp [factor,ctx]
      leftRight := by simp [factor]
      space := ?_
      factorWord := ?_
      searchWord := ?_
      controls := ?_
      decodeWord := by simpa [factor] using bound _ (by omega)
      factorTime := ?_ }
    · simp only [factor]
      unfold a physical logical table
      omega
    · simp only [factor]
      unfold sum prod r h b at hEnd
      omega
    · intro e he hed
      apply le_trans (Int.ofNat_le.mpr (LightIrreducibleFinder.factorWord_le_uniform
        (factor base d p q J) q e (by simpa [factor] using Nat.le_of_lt hp)
        (by simpa [factor] using Nat.le_of_lt hed) (by simpa [factor] using hq)))
      exact bound _ (by simpa [factor] using show LightIrreducibleFinder.uniformFactorWord d p q≤ctx base d+2000000*B^4 by omega)
    · change ((q*q+q+ctx base d+20 : ℕ) : ℤ)≤lim.word
      apply bound
      have hh : q*q≤B^2 := by nlinarith
      omega
    · change ((p+d+q+ctx base d+32 : ℕ) : ℤ)≤lim.word
      apply bound
      omega
    · intro e he hed
      exact LightIrreducibleFinder.factorTime_le_uniform (factor base d p q J) q e
        (by simpa [factor] using Nat.le_of_lt hp) (by simpa [factor] using Nat.le_of_lt hed)
        (by simpa [factor] using hq)
  · let C := LightExtensionBackend.quotientLayout (factor base d p q J)
      (a base d q J) (b base d q J) (h base d q J) (r base d q J) (prod base d q J) (sum base d q J)
    have hh := LightExtensionMenuMatrix.cell_word_after_ctx C q (ctx base d) (by simpa [C,LightExtensionBackend.quotientLayout,factor] using hq)
    apply bound
    change LightExtensionMultiplyCell.word C q (ctx base d)≤ctx base d+2000000*B^4
    apply hh.trans
    dsimp [C,LightExtensionBackend.quotientLayout,factor]
    gcongr <;> omega

end ThreeSum.LightExtensionBackendLayout
