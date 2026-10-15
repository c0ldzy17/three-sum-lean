import Submission.ThreeSum.LightTernaryGlobalPreludeProof
import Submission.ThreeSum.LightTernaryDimensionsBudget
import Submission.ThreeSumApsp.Lang.Tasks

namespace ThreeSum.TernaryGlobalPreludeResources
open Light LightTernaryGlobalPrelude
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

def need (M b p K κ n _U : ℕ) : Need where
  word:=LightTernaryDimensions.word M b p K n (n^κ)+1000*(n+1)+n^κ+κ+1
  cells:=33+LightExtensionBackendLayout.reserve
    (LightTernaryDimensions.dim M b p K n (n^κ)) p
    (p^(LightTernaryDimensions.dim M b p K n (n^κ))) (LightTernaryDimensions.J M b n (n^κ))
  depth:=17

theorem need_meets {lim : Limits} {M b p K κ n U free depth : ℕ} [Fact p.Prime]
    (μ : ℕ→ℤ) (hM : 1<M) (hb : 1<b) (hn : 0<n)
    (H : (need M b p K κ n U).Ok lim free depth) :
    Meets lim (program M b p K κ) 49 depth [n,free] μ
      (LightTernaryGlobalPreludeProof.time M b p K κ n free)
      (fun z ν=>∃c<p^(LightTernaryDimensions.dim M b p K n (n^κ)), z=(free:ℤ) ∧
        Irreducible (TernaryExtensionEncoding.monicOfCode (p:=p) (LightTernaryDimensions.dim M b p K n (n^κ)) c) ∧
        Seg ν free (header n (n^κ) (LightTernaryDimensions.r M n)
          (LightTernaryDimensions.J M b n (n^κ)) (LightTernaryDimensions.dim M b p K n (n^κ)) p
          (p^(LightTernaryDimensions.dim M b p K n (n^κ))) free c) ∧
        Seg ν (params free) (LightScales.values n) ∧
        LightTernaryGlobalPreludeProof.Menu ν (backend free) (LightTernaryDimensions.dim M b p K n (n^κ)) p
          (p^(LightTernaryDimensions.dim M b p K n (n^κ))) (LightTernaryDimensions.J M b n (n^κ)) c ∧
        Kept μ ν free) :=by
  have hw:=H.word
  have hc:=H.cells
  have hd:=H.depth
  simp only [need] at hw hc hd
  have hdom (x : ℕ) (hx : x≤LightTernaryDimensions.word M b p K n (n^κ)+1000*(n+1)+n^κ+κ+1) :
      (x:ℤ)≤lim.word :=(Int.ofNat_le.mpr hx).trans hw
  apply LightTernaryGlobalPreludeProof.meets μ hM hb hn H.space
  · simpa only [finish,backend,Nat.add_assoc] using hc
  · omega
  · exact hdom _ (by omega)
  · exact hdom _ (by omega)
  · exact hdom _ (by omega)
  · exact hdom _ (by omega)

def exponent (κ : ℕ) : ℕ :=6*(κ+2)
def wordCoefficient (M b p K : ℕ) : ℕ :=2*LightTernaryDimensions.coefficient M b p K
def baseCoefficient (M b p K : ℕ) : ℕ :=3*wordCoefficient M b p K+p+2

theorem dimension_bound {M b p K : ℕ} [Fact p.Prime] (hM : 1<M) (hb : 1<b) (κ n : ℕ) :
    LightTernaryDimensions.word M b p K n (n^κ)≤wordCoefficient M b p K*(n+1)^(κ+2) :=by
  have hn : n^κ≤(n+1)^κ :=Nat.pow_le_pow_left (by omega) _
  have hpos : 1≤(n+1)^κ :=Nat.one_le_pow _ _ (by omega)
  have hh : n^κ+1≤2*(n+1)^κ :=by omega
  calc
    _≤LightTernaryDimensions.coefficient M b p K*(n+1)^2*(n^κ+1) :=
      LightTernaryDimensions.word_polynomial hM hb n (n^κ)
    _≤LightTernaryDimensions.coefficient M b p K*(n+1)^2*(2*(n+1)^κ) :=Nat.mul_le_mul_left _ hh
    _=wordCoefficient M b p K*(n+1)^(κ+2) :=by unfold wordCoefficient; rw [pow_add]; ring

theorem parameter_bound {M b p K : ℕ} [Fact p.Prime] (hM : 1<M) (hb : 1<b) (κ n : ℕ) :
    LightExtensionBackendLayout.params
      (LightTernaryDimensions.dim M b p K n (n^κ)) p
      (p^(LightTernaryDimensions.dim M b p K n (n^κ))) (LightTernaryDimensions.J M b n (n^κ))≤
        baseCoefficient M b p K*(n+1)^(κ+2) :=by
  have hh:=dimension_bound (p:=p) (K:=K) hM hb κ n
  have hj : LightTernaryDimensions.J M b n (n^κ)≤LightTernaryDimensions.word M b p K n (n^κ) :=by unfold LightTernaryDimensions.word; omega
  have hd : LightTernaryDimensions.dim M b p K n (n^κ)≤LightTernaryDimensions.word M b p K n (n^κ) :=by unfold LightTernaryDimensions.word; omega
  have hq : p^(LightTernaryDimensions.dim M b p K n (n^κ))≤LightTernaryDimensions.word M b p K n (n^κ) :=by unfold LightTernaryDimensions.word; omega
  have hp : 1≤(n+1)^(κ+2) :=Nat.one_le_pow _ _ (by omega)
  unfold LightExtensionBackendLayout.params baseCoefficient
  nlinarith

theorem reserve_bound {M b p K : ℕ} [Fact p.Prime] (hM : 1<M) (hb : 1<b) (κ n : ℕ) :
    LightExtensionBackendLayout.reserve
      (LightTernaryDimensions.dim M b p K n (n^κ)) p
      (p^(LightTernaryDimensions.dim M b p K n (n^κ))) (LightTernaryDimensions.J M b n (n^κ))≤
        100000000*(baseCoefficient M b p K)^6*(n+1)^(exponent κ) :=by
  have hh:=Nat.pow_le_pow_left (parameter_bound (p:=p) (K:=K) hM hb κ n) 6
  unfold LightExtensionBackendLayout.reserve
  apply (Nat.mul_le_mul_left 100000000 hh).trans_eq
  rw [mul_pow,←pow_mul]
  simp only [exponent,Nat.mul_comm (κ+2) 6,Nat.mul_assoc]

def coefficient (M b p K κ : ℕ) : ℕ :=
  33+100000000*(baseCoefficient M b p K)^6+wordCoefficient M b p K+1000+κ+19

theorem need_bound {M b p K : ℕ} [Fact p.Prime] (hM : 1<M) (hb : 1<b) (κ n U : ℕ) :
    (need M b p K κ n U).word≤coefficient M b p K κ*(n+1)^(exponent κ) ∧
    (need M b p K κ n U).cells≤coefficient M b p K κ*(n+1)^(exponent κ) ∧
    (need M b p K κ n U).depth≤coefficient M b p K κ*(n+1)^(exponent κ) :=by
  have hs : κ+2≤exponent κ :=by unfold exponent; omega
  have h1 : 1≤(n+1)^(exponent κ) :=Nat.one_le_pow _ _ (by omega)
  have hsmall : (n+1)^(κ+2)≤(n+1)^(exponent κ) :=Nat.pow_le_pow_right (by omega) hs
  have hn : n+1≤(n+1)^(exponent κ) :=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤n+1) (show 1≤exponent κ by unfold exponent; omega)
  have hpow : n^κ≤(n+1)^(exponent κ) :=
    (Nat.pow_le_pow_left (by omega : n≤n+1) κ).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hw:=(dimension_bound (p:=p) (K:=K) hM hb κ n).trans (Nat.mul_le_mul_left (wordCoefficient M b p K) hsmall)
  have hc:=reserve_bound (p:=p) (K:=K) hM hb κ n
  simp only [need]
  unfold coefficient
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem need_poly {M b p K : ℕ} [Fact p.Prime] (hM : 1<M) (hb : 1<b) (κ : ℕ) :
    PolyNeed (need M b p K κ) :=by
  refine ⟨Nat.size (coefficient M b p K κ),exponent κ,?_⟩
  intro n U
  have hc : coefficient M b p K κ≤2^(Nat.size (coefficient M b p K κ)) :=(Nat.lt_size_self _).le
  have hp : (n+1)^(exponent κ)≤((n+1)*(U+1))^(exponent κ) :=
    Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by omega)) _
  have hh:=Nat.mul_le_mul hc hp
  obtain ⟨hw,hs,hd⟩:=need_bound (p:=p) (K:=K) hM hb κ n U
  simpa only [polyBound,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,Nat.mul_one] using
    And.intro (hw.trans hh) (And.intro (hs.trans hh) (hd.trans hh))

end ThreeSum.TernaryGlobalPreludeResources
