import Submission.ThreeSum.TernaryArenaLayout
import Submission.ThreeSum.LightNatPower

/-! Runtime arena pointers and the complete fixed part of both configuration
headers. Prefix-dependent dimensions are patched by the actual prefix kernel. -/
namespace ThreeSum.LightTernaryArenaTemplate
open Light TernaryArenaLayout
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

inductive Field where
  | arg (index : ℕ)
  | ptr (slot : ℕ)
  | num (value : ℕ)
  | square (index : ℕ)
  deriving DecidableEq

def value (inputs : ℕ → ℤ) (free C : ℕ) : Field → ℤ
  | .arg i => inputs i
  | .ptr s => (addr free C s : ℕ)
  | .num n => n
  | .square i => inputs i*inputs i

/-- Runtime inputs: capacityBase=n+U,free,Bmatrix,nB,Cmatrix,nC,Omatrix,nO,positions,
taggedB,taggedC,menu,J,p,localWordRadix,F,q,reserved17,reserved18,reserved19,reserved20,reserved21,reserved22.
The 23 inputs all come from the actual input/dimension/backend preludes. -/
def hostFields : List Field :=[
  .ptr 30,.ptr 31,.ptr 32,.ptr 33,.ptr 34,.ptr 35,.num 0,.arg 13,.arg 14,.arg 15,
  .ptr 16,.arg 3,.num 1,.ptr 36,.ptr 13,.num 0,.ptr 14,.num 0,.ptr 37,.ptr 38,.ptr 28,.num 1,.num 1,
  .ptr 39,.ptr 40,.ptr 41,.ptr 42,.ptr 43,.ptr 44,.num 0,.arg 13,.arg 14,.arg 15,
  .ptr 17,.arg 5,.num 1,.ptr 45,.ptr 13,.num 0,.ptr 14,.num 0,.ptr 46,.ptr 47,.ptr 29,.num 1,.num 1,
  .num 0,.ptr 13,.num 0,.ptr 49,.num 0,.ptr 48,.num 1,.ptr 38,.ptr 47,.ptr 50,.ptr 51,.ptr 52,
  .num 0,.ptr 54,.num 0,.ptr 57,.ptr 13,.num 0,.ptr 50,.num 0,.num 0,.ptr 56,.ptr 58,.ptr 59,.ptr 60,.num 0,.num 0,.ptr 61,.ptr 61,
  .num 0,.ptr 54,.num 0,.ptr 57,.ptr 13,.num 0,.ptr 51,.num 0,.num 0,.ptr 56,.ptr 62,.ptr 63,.ptr 64,.num 0,.num 0,.ptr 65,.ptr 65,
  .ptr 66,.num 0,.ptr 52,.num 0,.ptr 55,.ptr 19,.ptr 53,.ptr 50,.ptr 51,.ptr 52,.num 0,.num 0,.num 0,.ptr 53]

def seedFields : List Field :=[
  .arg 11,.num 0,.arg 12,.ptr 7,.num 1,.arg 13,.num 1,
  .arg 2,.ptr 4,.ptr 16,.arg 3,.arg 4,.ptr 5,.ptr 17,.arg 5,
  .arg 6,.ptr 6,.ptr 18,.arg 7,.arg 8,.ptr 19,.ptr 20,.ptr 21,.ptr 22,
  .ptr 1,.arg 9,.arg 10,.ptr 28,.ptr 29,.ptr 23,.ptr 53,.ptr 24,.ptr 25,.ptr 26,.ptr 27,
  .ptr 9,.ptr 10,.ptr 11,.ptr 12,.num 0,
  .square 16,.num 1,.num 1,.num 1,.num 0,.num 0,.num 0,.ptr 8]

def hostValues (inputs : ℕ → ℤ) (free C : ℕ) : List ℤ :=hostFields.map (value inputs free C)
def seedValues (inputs : ℕ → ℤ) (free C : ℕ) : List ℤ :=seedFields.map (value inputs free C)

@[simp] theorem hostFields_length : hostFields.length=106 := rfl
@[simp] theorem seedFields_length : seedFields.length=48 := rfl

def ptrExpr (slot : ℕ) : Expr :=v 1 +' k slot *' v 24
def fieldExpr : Field → Expr
  | .arg i =>v i
  | .ptr s =>ptrExpr s
  | .num n =>k n
  | .square i =>v i *' v i

def stores (dstSlot : ℕ) : ℕ → List Field → Stmt
  | _,[] =>.skip
  | offset,f::fs =>.store (ptrExpr dstSlot +' k offset) (fieldExpr f) ;; stores dstSlot (offset+1) fs

def Good : Field → Prop
  | .arg i =>i<23
  | .ptr s =>s<67
  | .num n =>n≤1
  | .square i =>i=16

instance (f : Field) : Decidable (Good f) := by cases f <;> unfold Good <;> infer_instance

theorem fields_good : ∀ f∈hostFields++seedFields, Good f := by decide

theorem pointer_gives {lim : Limits} {loc : ℕ → ℤ} {free C : ℕ}
    (hfree : loc 1=(free : ℤ)) (hC : loc 24=(C : ℤ)) (hpos : 1≤C)
    (hw : (lim.space : ℤ)≤lim.word) (hend : finish free C≤lim.space)
    (slot : ℕ) (hs : slot<67) (μ : ℕ → ℤ) :
    (ptrExpr slot).Gives lim ⟨loc,μ⟩ (addr free C slot : ℕ) := by
  have hs' : slot<slots := hs
  have ha : addr free C slot≤lim.space :=
    region_space (len := 0) hs' (by omega) hend
  have hprod : slot*C≤lim.space := by unfold addr at ha; omega
  have hslot : slot≤lim.space := by nlinarith
  have hprodInt : (slot : ℤ)*(C : ℤ)≤lim.word := (Int.ofNat_le.mpr hprod).trans hw
  have hprodNonneg : 0≤(slot : ℤ)*(C : ℤ) := by positivity
  have haddrInt : (free : ℤ)+(slot : ℤ)*(C : ℤ)≤lim.word := by
    exact_mod_cast (Int.ofNat_le.mpr ha).trans hw
  light_side [ptrExpr,hfree,hC,addr]

theorem field_gives {lim : Limits} {loc : ℕ → ℤ} {free C : ℕ}
    (hfree : loc 1=(free : ℤ)) (hC : loc 24=(C : ℤ)) (hpos : 1≤C)
    (hw : (lim.space : ℤ)≤lim.word) (hend : finish free C≤lim.space)
    (hSquare : |loc 16*loc 16|≤lim.word) (f : Field) (hg : Good f) (μ : ℕ → ℤ) :
    (fieldExpr f).Gives lim ⟨loc,μ⟩ (value loc free C f) := by
  have hOne : (1 : ℤ)≤lim.word := by
    have hfinish : C≤finish free C := by unfold finish addr slots; omega
    omega
  cases f with
  | arg i => exact ⟨trivial,rfl⟩
  | ptr s => exact pointer_gives hfree hC hpos hw hend s hg μ
  | num n => exact ⟨by change (n : ℤ)≤lim.word; dsimp [Good] at hg; omega,rfl⟩
  | square i =>
    have hi : i=16 := hg
    subst i
    exact ⟨⟨trivial,trivial,hSquare⟩,rfl⟩

theorem field_cost (f : Field) : (fieldExpr f).cost≤5 := by
  cases f <;> simp [fieldExpr,ptrExpr,Expr.cost,v,k]

theorem stores_ends {lim : Limits} {P : Program} {depth free C dstSlot : ℕ}
    (fs : List Field) (offset : ℕ) (loc μ : ℕ → ℤ)
    (hfree : loc 1=(free : ℤ)) (hC : loc 24=(C : ℤ)) (hpos : 1≤C)
    (hw : (lim.space : ℤ)≤lim.word) (hend : finish free C≤lim.space)
    (hslot : dstSlot<67) (hspace : addr free C dstSlot+offset+fs.length≤lim.space)
    (hgood : ∀ f∈fs, Good f) (hsquare : |loc 16*loc 16|≤lim.word) :
    Ends lim P depth (stores dstSlot offset fs) ⟨loc,μ⟩ (20*fs.length)
      (fun σ => σ.loc=loc ∧
        Seg σ.mem (addr free C dstSlot+offset) (fs.map (value loc free C)) ∧
        SameOutside μ σ.mem (addr free C dstSlot+offset) fs.length) := by
  induction fs generalizing offset μ with
  | nil => exact Ends.skip ⟨rfl,Seg.nil,SameOutside.refl⟩
  | cons f fs ih =>
    have haddr : addr free C dstSlot+offset<lim.space := by simp only [List.length_cons] at hspace; omega
    have hp := pointer_gives hfree hC hpos hw hend dstSlot hslot μ
    have hf := field_gives hfree hC hpos hw hend hsquare f (hgood f (by simp)) μ
    have haVal : (ptrExpr dstSlot +' k offset).val ⟨loc,μ⟩=
        ((addr free C dstSlot+offset : ℕ) : ℤ) := by
      change (ptrExpr dstSlot).val ⟨loc,μ⟩+(offset : ℤ)=_
      rw [hp.2]
      push_cast
      rfl
    have has : (ptrExpr dstSlot +' k offset).Safe lim ⟨loc,μ⟩ := by
      change (ptrExpr dstSlot).Safe lim ⟨loc,μ⟩ ∧ (offset : ℤ)≤lim.word ∧ _
      refine ⟨hp.1,by omega,?_⟩
      change |(ptrExpr dstSlot).val ⟨loc,μ⟩+(offset : ℤ)|≤lim.word
      rw [hp.2]
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast (Int.ofNat_le.mpr haddr.le).trans hw
    have haa : lim.Addr ((ptrExpr dstSlot +' k offset).val ⟨loc,μ⟩) := by
      rw [haVal]
      exact ⟨by positivity,by exact_mod_cast haddr⟩
    have hc := field_cost f
    simp only [List.length_cons,stores]
    refine Ends.seq 20 (20*fs.length) ?_ (by omega)
    refine Ends.storeLast ?_ (hs := ⟨has,hf.1,haa⟩)
      (hT := by simp only [Expr.cost,ptrExpr,v,k] at *; omega)
    have hr := ih (offset+1) (Function.update μ (addr free C dstSlot+offset) (value loc free C f))
      (by simp only [List.length_cons] at hspace; omega)
      (fun g hg => hgood g (by simp [hg]))
    rw [haVal,hf.2,Int.toNat_natCast]
    apply hr.mono le_rfl
    rintro σ ⟨hloc,hseg,hkeep⟩
    refine ⟨hloc,?_,?_⟩
    · rw [List.map_cons,seg_cons]
      constructor
      · have hh := hkeep (addr free C dstSlot+offset) (Or.inl (by omega))
        simpa using hh
      · simpa only [Nat.add_assoc] using hseg
    · intro a ha
      rw [hkeep a (by omega)]
      exact Function.update_of_ne (by omega) _ _

def body (D E : ℕ) : Stmt :=
  .call 0 [v 0 +' k 1,k E] 23 ;;
  .set 24 (k (256*(D+1)) *' v 23) ;;
  stores 0 0 hostFields ;;
  stores 2 0 seedFields ;;
  .set 0 (v 1)

def program (D E : ℕ) : Program :=LightNatPower.program++[body D E]
def time (E : ℕ) : ℕ :=LightNatPower.time E+4000

def args (U free Bmatrix nB Cmatrix nC Omatrix nO positions taggedB taggedC menu
    J p wordRadix F q dB dC dP tB tC tP : ℕ) : List ℤ :=
  [U,free,Bmatrix,nB,Cmatrix,nC,Omatrix,nO,positions,taggedB,taggedC,menu,J,p,wordRadix,F,q,dB,dC,dP,tB,tC,tP]

theorem value_congr {loc initial : ℕ → ℤ} {free C : ℕ}
    (hread : ∀ i<23, loc i=initial i) (f : Field) (hg : Good f) :
    value loc free C f=value initial free C f := by
  cases f with
  | arg i => exact hread i hg
  | ptr s => rfl
  | num n => rfl
  | square i =>
    have hi : i=16 := hg
    subst i
    simp only [value,hread 16 (by decide)]

/-- The polynomial capacity, every stored arena pointer, and both complete
template headers are computed by this finite program from actual runtime
inputs. No preinitialized address table is used. -/
theorem program_meets {lim : Limits} {D E U free q d : ℕ}
    (inputs : List ℤ) (hlen : inputs.length=23) (μ : ℕ → ℤ)
    (hU : inputs.getD 0 0=(U : ℤ)) (hFree : inputs.getD 1 0=(free : ℤ))
    (hq : inputs.getD 16 0=(q : ℤ))
    (hw : (lim.space : ℤ)≤lim.word)
    (hend : finish free (capacity D E U)≤lim.space)
    (hUW : (U : ℤ)+1≤lim.word) (hEW : (E : ℤ)≤lim.word)
    (hqC : q*q≤capacity D E U) (hd : d<lim.depth) :
    Meets lim (program D E) 1 d inputs μ (time E)
      (fun r ν => r=(free : ℤ) ∧
        Seg ν (addr free (capacity D E U) 0) (hostValues (frame inputs) free (capacity D E U)) ∧
        Seg ν (addr free (capacity D E U) 2) (seedValues (frame inputs) free (capacity D E U)) ∧
        Kept μ ν free) := by
  change inputs[0]?.getD 0=(U : ℤ) at hU
  change inputs[1]?.getD 0=(free : ℤ) at hFree
  change inputs[16]?.getD 0=(q : ℤ) at hq
  let C := capacity D E U
  have hCmin : 256≤C := capacity_pos D E U
  have hCspace : C≤lim.space := by unfold finish addr slots at hend; change free+67*C≤lim.space at hend; omega
  have hCword : (C : ℤ)≤lim.word := (Int.ofNat_le.mpr hCspace).trans hw
  have hpowpos : 1≤(U+1)^E := Nat.one_le_pow _ _ (by omega)
  have hcoeff : 256*(D+1)≤C := by dsimp [C,capacity]; nlinarith
  have hcoeffWord : ((256*(D+1) : ℕ) : ℤ)≤lim.word := (Int.ofNat_le.mpr hcoeff).trans hCword
  have hpow : ∀ i≤E, (((U+1)^i : ℕ) : ℤ)≤lim.word := by
    intro i hi
    have hh := Nat.pow_le_pow_right (by omega : 1≤U+1) hi
    have hm : (U+1)^E≤C := by dsimp [C,capacity]; nlinarith
    exact (Int.ofNat_le.mpr (hh.trans hm)).trans hCword
  have hp := (LightNatPower.program_meets (d := d+1) μ hEW hpow).append [body D E]
  apply Meets.of_body (by rfl)
  unfold body time
  light_call hp using frame,hU with pow μp ⟨hpowResult,hμp⟩
  subst μp
  have hcapProduct : (256*(D+1) : ℤ)*(((U+1)^E : ℕ) : ℤ)=(C : ℤ) := by
    dsimp [C,capacity]
  have hcapNonneg : 0≤(256*(D+1) : ℤ)*(((U+1)^E : ℕ) : ℤ) := by positivity
  have hPowLocal : (setLocal inputs 23 pow)[23]?.getD 0=(((U+1)^E : ℕ) : ℤ) := by
    change frame (setLocal inputs 23 pow) 23=_
    rw [frame_setLocal]
    simpa using hpowResult
  have hmulNonneg : 0≤(256*(D+1) : ℤ)*(setLocal inputs 23 pow)[23]?.getD 0 := by
    rw [hPowLocal]
    positivity
  have hmulWord : (256*(D+1) : ℤ)*(setLocal inputs 23 pow)[23]?.getD 0≤lim.word := by
    rw [hPowLocal,hcapProduct]
    exact hCword
  have hmulNonnegFull : 0≤256*((D : ℤ)+1)*((U : ℤ)+1)^E := by positivity
  have hmulWordFull : 256*((D : ℤ)+1)*((U : ℤ)+1)^E≤lim.word := by
    dsimp [C,capacity] at hCword
    exact_mod_cast hCword
  light_set C using hPowLocal,hcapProduct,capacity,C
  let loc := frame (setLocal (setLocal inputs 23 pow) 24 (C : ℤ))
  have hlocFree : loc 1=(free : ℤ) := by
    change frame (setLocal (setLocal inputs 23 pow) 24 (C : ℤ)) 1=_
    rw [frame_setLocal,if_neg (by decide),frame_setLocal,if_neg (by decide)]
    exact hFree
  have hlocC : loc 24=(C : ℤ) := by
    change frame (setLocal (setLocal inputs 23 pow) 24 (C : ℤ)) 24=_
    rw [frame_setLocal,if_pos rfl]
  have hlocInitial : ∀ i<23, loc i=frame inputs i := by
    intro i hi
    simp only [loc,frame_setLocal]
    rw [if_neg (by omega),if_neg (by omega)]
  have hlocQ : loc 16=(q : ℤ) := by rw [hlocInitial 16 (by decide)]; exact hq
  have hSquare : |loc 16*loc 16|≤lim.word := by
    rw [hlocQ,abs_of_nonneg (by positivity)]
    exact_mod_cast (Int.ofNat_le.mpr hqC).trans hCword
  have hgoodHost : ∀ f∈hostFields, Good f := fun f hf => fields_good f (List.mem_append_left _ hf)
  have hgoodSeed : ∀ f∈seedFields, Good f := fun f hf => fields_good f (List.mem_append_right _ hf)
  have hhostSpace : addr free C 0+0+hostFields.length≤lim.space := by
    simpa only [Nat.add_zero] using region_space (slot := 0) (by decide : 0<slots)
      (show hostFields.length≤C by rw [hostFields_length]; omega) hend
  have hseedSpace : addr free C 2+0+seedFields.length≤lim.space := by
    simpa only [Nat.add_zero] using region_space (slot := 2) (by decide : 2<slots)
      (show seedFields.length≤C by rw [seedFields_length]; omega) hend
  have hs0 := stores_ends (P := program D E) (depth := d) hostFields 0 loc μ
    hlocFree hlocC (by omega) hw hend (by decide) hhostSpace hgoodHost hSquare
  change Ends _ _ _ _ ⟨loc,μ⟩ _ _
  refine Ends.pieceThen hs0 ?_ (hT := by simp only [hostFields_length]; light_time)
  rintro ⟨loc₀,μ₀⟩ ⟨hloc₀,hhost,hkeep₀⟩
  dsimp only at hloc₀
  subst loc₀
  change Seg μ₀ (addr free C 0+0) _ at hhost
  change SameOutside μ μ₀ (addr free C 0+0) hostFields.length at hkeep₀
  simp only [Nat.add_zero] at hhost hkeep₀
  have hs1 := stores_ends (P := program D E) (depth := d) seedFields 0 loc μ₀
    hlocFree hlocC (by omega) hw hend (by decide) hseedSpace hgoodSeed hSquare
  refine Ends.pieceThen hs1 ?_ (hT := by simp only [hostFields_length,seedFields_length]; light_time)
  rintro ⟨loc₁,ν⟩ ⟨hloc₁,hseed,hkeep₁⟩
  dsimp only at hloc₁
  subst loc₁
  change Seg ν (addr free C 2+0) _ at hseed
  change SameOutside μ₀ ν (addr free C 2+0) seedFields.length at hkeep₁
  simp only [Nat.add_zero] at hseed hkeep₁
  refine Ends.setLast ?_ (hs := trivial)
    (hT := by light_time [hostFields_length,seedFields_length,Expr.cost])
  refine ⟨hlocFree,?_,?_,?_⟩
  · have hmaps : hostFields.map (value loc free C)=hostValues (frame inputs) free C := by
      apply List.map_congr_left
      intro f hf
      exact value_congr hlocInitial f (hgoodHost f hf)
    rw [← hmaps]
    intro i hi
    change ν (addr free C 0+i)=_
    rw [hkeep₁ _ (Or.inl (by
      have hb := before (free := free) (C := C) (i := 0) (j := 2) (len := 106) (by decide) (by omega)
      simp only [List.length_map,hostFields_length] at hi
      omega))]
    simpa only [Nat.add_zero] using hhost i hi
  · have hmaps : seedFields.map (value loc free C)=seedValues (frame inputs) free C := by
      apply List.map_congr_left
      intro f hf
      exact value_congr hlocInitial f (hgoodSeed f hf)
    rw [← hmaps]
    simpa only [Nat.add_zero] using hseed
  · intro x hx
    change ν x=μ x
    rw [hkeep₁ x (Or.inl (by unfold addr; omega)),hkeep₀ x (Or.inl (by unfold addr; omega))]

end ThreeSum.LightTernaryArenaTemplate
