import Submission.ThreeSum.LightExtensionBackendLayout

noncomputable section
namespace ThreeSum.LightExtensionBackendSetup
open Light TernaryExtensionEncoding LightExtensionBackendLayout
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

/-- p,dimension,q,J,base; every physical address is computed by real instructions. -/
def body : Stmt :=
  .set 5 (k 2 *' v 1) ;;
  .set 6 (v 4 +' v 5 +' k 1) ;;
  .set 7 (v 6 +' v 5) ;;
  .set 8 (v 7 +' k 10) ;;
  .set 9 (v 2 *' v 2) ;;
  .set 10 (v 3 +' k 2) ;;
  .set 11 (v 9 *' v 10) ;;
  .set 12 (v 8 +' v 9) ;;
  .set 13 (v 12 +' v 11) ;;
  .set 14 (v 13 +' v 11) ;;
  .set 15 (v 14 +' v 1) ;;
  .set 16 (v 15 +' v 1) ;;
  .set 17 (v 16 +' v 1) ;;
  .set 18 (v 17 +' v 5) ;;
  .set 19 (v 18 +' v 5) ;;
  .set 20 (v 14 +' v 5) ;;
  .call 37 [v 0,v 1,v 2,v 4,v 6,v 7,v 14,v 20,v 7,v 8,v 12,v 13,
    v 14,v 15,v 16,v 17,v 18,v 19,v 3] 0

def program : Program := LightExtensionBackend.program++[body]

def time (base d p q J : ℕ) : ℕ :=
  LightExtensionBackend.time (factor base d p q J) q J (a base d q J) (b base d q J)
    (h base d q J) (r base d q J) (prod base d q J) (sum base d q J)
    (LightIrreducibleFinder.uniformFactorTime d p q)+500

instance factorPrime (base d p q J : ℕ) [Fact p.Prime] : Fact (factor base d p q J).p.Prime := by
  simpa only [factor] using (inferInstance : Fact p.Prime)

variable {lim : Limits} {depth : ℕ}

theorem program_meets {base d p q J : ℕ} [Fact p.Prime]
    (μ : ℕ → ℤ) (hdim : 0 < d) (hq : p^d=q)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+14 < lim.depth)
    (hspace : base+reserve d p q J ≤ lim.space) :
    Meets lim program 38 depth [p,d,q,J,base] μ (time base d p q J)
      (fun z ν => ∃ c < q, z=(c+1 : ℕ) ∧ Irreducible (monicOfCode (p := p) d c) ∧
        (∀ s < q*q, ∀ i < J+2, ν (physical base d q J+s*(J+2)+i)=
          (LightExtensionSeedMatrix.value
            (encodedMul (LightExtensionBackend.modulusMonic (factor base d p q J) c)) q p s
            (TernarySignedLayout.offset J i) : ℤ)) ∧ Kept μ ν base) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hqpos : 0 < q := by rw [←hq]; positivity
  let finish := sum base d q J+2*d
  have hEnd : finish ≤ lim.space := (end_le base d p q J).trans hspace
  have hfinishWord : (finish : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hEnd).trans hw
  have hQ : q*q ≤ q*q*(J+2) := Nat.le_mul_of_pos_right _ (by omega)
  have hLen : J+2 ≤ q*q*(J+2) := Nat.le_mul_of_pos_left _ (by nlinarith)
  have hqQQ : q ≤ q*q := by nlinarith
  have hb (n : ℕ) (hn : n ≤ finish) : (n : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hn).trans hfinishWord
  have hdWord := hb d (by dsimp [finish,sum,prod,r,h,b,a,physical,logical,table,ctx,target]; omega)
  have h2dWord := hb (2*d) (by dsimp [finish,sum,prod,r,h,b,a,physical,logical,table,ctx,target]; omega)
  have hbaseWord := hb base (by dsimp [finish,sum,prod,r,h,b,a,physical,logical,table,ctx,target]; omega)
  have htargetWord := hb (target base d) (by dsimp [finish,sum,prod,r,h,b,a,physical,logical,table,ctx]; omega)
  have hctxWord := hb (ctx base d) (by dsimp [finish,sum,prod,r,h,b,a,physical,logical,table]; omega)
  have htableWord := hb (table base d) (by dsimp [finish,sum,prod,r,h,b,a,physical,logical]; omega)
  have hQQWord := hb (q*q) (by dsimp [finish,sum,prod,r,h,b,a,physical,logical,table,ctx,target]; omega)
  have hLenWord := hb (J+2) (by dsimp [finish,sum,prod,r,h,b,a,physical,logical,table,ctx,target]; omega)
  have hProdWord := hb (q*q*(J+2)) (by dsimp [finish,sum,prod,r,h,b,a,physical,logical,table,ctx,target]; omega)
  have hlogicalWord := hb (logical base d q) (by dsimp [finish,sum,prod,r,h,b,a,physical]; omega)
  have hphysicalWord := hb (physical base d q J) (by dsimp [finish,sum,prod,r,h,b,a]; omega)
  have haWord := hb (a base d q J) (by dsimp [finish,sum,prod,r,h,b]; omega)
  have hbWord := hb (b base d q J) (by dsimp [finish,sum,prod,r,h]; omega)
  have hhWord := hb (h base d q J) (by dsimp [finish,sum,prod,r]; omega)
  have hrWord := hb (r base d q J) (by dsimp [finish,sum,prod]; omega)
  have hprodWord := hb (prod base d q J) (by dsimp [finish,sum]; omega)
  have hsumWord := hb (sum base d q J) (by dsimp [finish]; omega)
  have hrightWord := hb (a base d q J+2*d) (by dsimp [finish,sum,prod,r,h,b]; omega)
  have hQQInt : (q : ℤ)*(q : ℤ) ≤ lim.word := by exact_mod_cast hQQWord
  have hQQNonneg : 0 ≤ (q : ℤ)*(q : ℤ) := by positivity
  have hProdInt : (q : ℤ)*(q : ℤ)*((J : ℤ)+2) ≤ lim.word := by exact_mod_cast hProdWord
  have hProdNonneg : 0 ≤ (q : ℤ)*(q : ℤ)*((J : ℤ)+2) := by positivity
  have targetCalc : (base : ℤ)+2*(d : ℤ)+1 ≤ lim.word := by
    simpa only [target,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using htargetWord
  have ctxCalc : (target base d : ℤ)+2*(d : ℤ) ≤ lim.word := by
    simpa only [ctx,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hctxWord
  have tableCalc : (ctx base d : ℤ)+10 ≤ lim.word := by
    simpa only [table,Nat.cast_add,Nat.cast_ofNat] using htableWord
  have logicalCalc : (table base d : ℤ)+(q : ℤ)*(q : ℤ) ≤ lim.word := by
    simpa only [logical,Nat.cast_add,Nat.cast_mul] using hlogicalWord
  have physicalCalc : (logical base d q : ℤ)+(q : ℤ)*(q : ℤ)*((J : ℤ)+2) ≤ lim.word := by
    simpa only [physical,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hphysicalWord
  have aCalc : (physical base d q J : ℤ)+(q : ℤ)*(q : ℤ)*((J : ℤ)+2) ≤ lim.word := by
    simpa only [a,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using haWord
  have bCalc : (a base d q J : ℤ)+(d : ℤ) ≤ lim.word := by
    simpa only [b,Nat.cast_add] using hbWord
  have hCalc : (b base d q J : ℤ)+(d : ℤ) ≤ lim.word := by
    simpa only [h,Nat.cast_add] using hhWord
  have rCalc : (h base d q J : ℤ)+(d : ℤ) ≤ lim.word := by
    simpa only [r,Nat.cast_add] using hrWord
  have prodCalc : (r base d q J : ℤ)+2*(d : ℤ) ≤ lim.word := by
    simpa only [prod,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hprodWord
  have sumCalc : (prod base d q J : ℤ)+2*(d : ℤ) ≤ lim.word := by
    simpa only [sum,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hsumWord
  have hbudget := budget base d p q J hp hdim hq hw hspace
  have hc := (LightExtensionBackend.program_meets (factor base d p q J) (depth := depth+1)
    μ hw (by omega) hbudget hq.symm).append [body]
  apply Meets.of_body (show program[38]?=some body from rfl)
  unfold body time
  light_set (2*d : ℕ)
  light_set (target base d) using target
  light_set (ctx base d) using ctx
  light_set (table base d) using table
  light_set (q*q : ℕ)
  light_set (J+2 : ℕ)
  light_set (q*q*(J+2) : ℕ)
  light_set (logical base d q) using logical
  light_set (physical base d q J) using physical
  light_set (a base d q J) using a
  light_set (b base d q J) using b
  light_set (h base d q J) using h
  light_set (r base d q J) using r
  light_set (prod base d q J) using prod
  light_set (sum base d q J) using sum
  light_set (a base d q J+2*d : ℕ)
  light_call hc using args,factor
    with z ν hz
  exact hz

end ThreeSum.LightExtensionBackendSetup
