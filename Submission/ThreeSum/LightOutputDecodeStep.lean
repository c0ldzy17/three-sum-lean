import Submission.ThreeSum.LightOutputDecodeDivide
import Submission.ThreeSum.OutputDecodeOccurrenceCode

/-!
# One actual output-record decoding step

A local record digit is split into its occurrence and layer indices by
the checked logarithmic quotient routine. The layer mask is read from the
existing table, both output cells are written, and the occurrence-only
source-bank code is updated. Every other cell below the scratch pointer
is preserved, so separate output rows can be filled in any order.
-/

namespace ThreeSum.LightOutputDecodeStep

open Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

def body (pDivide : ℕ) : Stmt :=
  .call pDivide [v 0,v 2,v 8] 9 ;;
  .set 10 (v 0 -' v 9 *' v 2) ;;
  .set 11 (M (v 3 +' v 10)) ;;
  .store (v 6) (v 9) ;;
  .store (v 7) (v 11) ;;
  .set 0 (v 4 +' v 5 *' v 9)

def time (V : ℕ) : ℕ := LightOutputDecodeDivide.budget V+100
def word (V T M acc power U : ℕ) : ℕ := 4*(V+T+M+acc+power*T+U+10)
def space (work V : ℕ) : ℕ := work+(Nat.log 2 (V+1)+2)

def KeptOthers (μ ν : ℕ → ℤ) (work outOcc outMask : ℕ) : Prop :=
  SameOn (fun a => a < work ∧ a ≠ outOcc ∧ a ≠ outMask) μ ν

theorem kept_prefix {μ ν : ℕ → ℤ} {work outOcc outMask fr : ℕ}
    (hs : KeptOthers μ ν work outOcc outMask)
    (hwork : fr ≤ work) (hocc : fr ≤ outOcc) (hmask : fr ≤ outMask) :
    Kept μ ν fr := fun a ha => hs a ⟨by omega,by omega,by omega⟩

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {x T M masks acc power outOcc outMask work V U : ℕ} {f : ℕ → ℕ}

theorem meets {pMain pDivide : ℕ}
    (hmain : P[pMain]?=some (body pDivide))
    (hdivide : P[pDivide]?=some LightOutputDecodeDivide.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hT : 1 ≤ T) (hM : 1 ≤ M) (hx : x < T*M) (hxV : x ≤ V)
    (hmask : masks+M ≤ work) (hocc : outOcc < work) (hout : outMask < work)
    (hne : outOcc ≠ outMask) (hspace : space work V ≤ lim.space)
    (hword : (word V T M acc power U : ℤ) ≤ lim.word)
    (hf : ∀ s < M, f s ≤ U) (hread : ∀ s < M, μ (masks+s)=(f s : ℤ)) :
    Meets lim P pMain d [x,T,M,masks,acc,power,outOcc,outMask,work] μ (time V)
      (fun r ν => r=((acc+power*(x/M) : ℕ) : ℤ) ∧
        ν outOcc=((x/M : ℕ) : ℤ) ∧ ν outMask=(f (x%M) : ℤ) ∧
        KeptOthers μ ν work outOcc outMask) := by
  have hbudget (a : ℕ) (ha : a ≤ word V T M acc power U) : (a : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ha).trans hword
  have hVWord := hbudget V (by unfold word; omega)
  have hMWord := hbudget M (by unfold word; omega)
  have hxWord : (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hxV).trans hVWord
  have haccWord := hbudget acc (by unfold word; omega)
  have hpTWord := hbudget (power*T) (by unfold word; omega)
  have hpowerLe : power ≤ power*T := Nat.le_mul_of_pos_right power hT
  have hpowerWord : (power : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hpowerLe).trans hpTWord
  have hUWord := hbudget U (by unfold word; omega)
  have hwork : work ≤ lim.space := by unfold space at hspace; omega
  have hfr : Light.Emod.Pre lim M V work := by
    refine ⟨hM,hw,?_,hspace⟩
    have hh := hbudget (4*V+4*M+16) (by unfold word; omega)
    exact_mod_cast hh
  obtain ⟨q,hq⟩ : ∃ q : ℕ, x/M=q := ⟨x/M,rfl⟩
  obtain ⟨s,hs⟩ : ∃ s : ℕ, x%M=s := ⟨x%M,rfl⟩
  have hqT : q < T := by rw [← hq]; exact (Nat.div_lt_iff_lt_mul hM).mpr hx
  have hsM : s < M := by rw [← hs]; exact Nat.mod_lt x hM
  have hqV : q ≤ V := by rw [← hq]; exact (Nat.div_le_self _ _).trans hxV
  have hsV : s ≤ V := by rw [← hs]; exact (Nat.mod_le _ _).trans hxV
  have hdecomp : M*q+s=x := by simpa only [hq,hs] using Nat.div_add_mod x M
  have hprod : q*M ≤ V := by rw [Nat.mul_comm]; omega
  have hprodWord : (q : ℤ)*(M : ℤ) ≤ lim.word :=
    (by exact_mod_cast hprod : (q : ℤ)*(M : ℤ) ≤ (V : ℤ)).trans hVWord
  have hprodNonneg : (0 : ℤ) ≤ (q : ℤ)*(M : ℤ) := by positivity
  have hdiff : (x : ℤ)-(q : ℤ)*(M : ℤ)=(s : ℤ) := by
    have hh : (M : ℤ)*(q : ℤ)+(s : ℤ)=(x : ℤ) := by exact_mod_cast hdecomp
    nlinarith
  have hcodeProd : power*q ≤ power*T := Nat.mul_le_mul_left power hqT.le
  have hcodeProdWord : (power : ℤ)*(q : ℤ) ≤ lim.word :=
    (by exact_mod_cast hcodeProd : (power : ℤ)*(q : ℤ) ≤ ((power*T : ℕ) : ℤ)).trans hpTWord
  have hcodeProdNonneg : (0 : ℤ) ≤ (power : ℤ)*(q : ℤ) := by positivity
  have hcodeWord := hbudget (acc+power*q) (by unfold word; omega)
  have hcodeWord' : (acc : ℤ)+(power : ℤ)*(q : ℤ) ≤ lim.word := by exact_mod_cast hcodeWord
  have hcodeNonneg : (0 : ℤ) ≤ (acc : ℤ)+(power : ℤ)*(q : ℤ) := by positivity
  have hfWord : (f s : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (hf s hsM)).trans hUWord
  apply Meets.of_body hmain
  unfold body time
  light_call (LightOutputDecodeDivide.bounded_meets (d := d+1) hdivide hfr hxV)
    with value ν ⟨hv,kept⟩
  have hvq : value=(q : ℤ) := by simpa only [hq] using hv
  light_set (s : ℕ) using hvq,hdiff
  have hread' : ν (masks+s)=(f s : ℤ) := by
    rw [kept _ (by omega)]
    exact hread s hsM
  light_set (f s : ℕ) using hread'
  light_store outOcc (q : ℕ) using hvq
  light_store outMask (f s : ℕ)
  light_set (acc+power*q : ℕ) using hvq
  refine ⟨by rw [hq]; rfl,?_,?_,?_⟩
  · simp [Function.update_of_ne hne,hq]
  · simp [hs]
  · intro a ha
    change Function.update (Function.update ν outOcc (q : ℤ)) outMask (f s : ℤ) a = μ a
    rw [Function.update_of_ne ha.2.2,Function.update_of_ne ha.2.1,kept a ha.1]

def program : Program := [body 1,LightOutputDecodeDivide.body]

theorem program_meets
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hT : 1 ≤ T) (hM : 1 ≤ M) (hx : x < T*M) (hxV : x ≤ V)
    (hmask : masks+M ≤ work) (hocc : outOcc < work) (hout : outMask < work)
    (hne : outOcc ≠ outMask) (hspace : space work V ≤ lim.space)
    (hword : (word V T M acc power U : ℤ) ≤ lim.word)
    (hf : ∀ s < M, f s ≤ U) (hread : ∀ s < M, μ (masks+s)=(f s : ℤ)) :
    Meets lim program 0 d [x,T,M,masks,acc,power,outOcc,outMask,work] μ (time V)
      (fun r ν => r=((acc+power*(x/M) : ℕ) : ℤ) ∧
        ν outOcc=((x/M : ℕ) : ℤ) ∧ ν outMask=(f (x%M) : ℤ) ∧
        KeptOthers μ ν work outOcc outMask) :=
  meets rfl rfl hw hd hT hM hx hxV hmask hocc hout hne hspace hword hf hread

theorem meets_code_step {pMain pDivide k i : ℕ}
    (hmain : P[pMain]?=some (body pDivide))
    (hdivide : P[pDivide]?=some LightOutputDecodeDivide.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hT : 1 ≤ T) (hM : 1 ≤ M)
    (hx : x=(k/(T*M)^i)%(T*M))
    (ha : acc=OutputDecodeOccurrenceCode.code T M i k) (hp : power=T^i)
    (hxV : x ≤ V) (hmask : masks+M ≤ work)
    (hocc : outOcc < work) (hout : outMask < work) (hne : outOcc ≠ outMask)
    (hspace : space work V ≤ lim.space)
    (hword : (word V T M acc power U : ℤ) ≤ lim.word)
    (hf : ∀ s < M, f s ≤ U) (hread : ∀ s < M, μ (masks+s)=(f s : ℤ)) :
    Meets lim P pMain d [x,T,M,masks,acc,power,outOcc,outMask,work] μ (time V)
      (fun r ν => r=(OutputDecodeOccurrenceCode.code T M (i+1) k : ℤ) ∧
        ν outOcc=((x/M : ℕ) : ℤ) ∧ ν outMask=(f (x%M) : ℤ) ∧
        KeptOthers μ ν work outOcc outMask) := by
  have hxlt : x < T*M := by rw [hx]; exact Nat.mod_lt _ (Nat.mul_pos hT hM)
  refine (meets hmain hdivide hw hd hT hM hxlt hxV hmask hocc hout hne hspace hword hf hread).mono le_rfl ?_
  rintro r ν ⟨hr,hocc',hmask',hk⟩
  refine ⟨?_,hocc',hmask',hk⟩
  rw [hr,ha,hp,hx,OutputDecodeOccurrenceCode.code_step]

end ThreeSum.LightOutputDecodeStep
