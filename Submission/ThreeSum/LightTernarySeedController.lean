import Submission.ThreeSum.LightTernarySeedScore
import Submission.ThreeSum.LightTernaryRowSelector

/-! Exhaust the actual q² seed menu, select from the computed flags and
three score arrays, reconstruct the selected candidate's actual keys, and
extend only the physical digit-coordinate span. -/
noncomputable section
namespace ThreeSum.LightTernarySeedController
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

def seedArgs (seed : Expr) : List Expr :=
  [v 0,seed,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,
    v 16,v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28,v 29,
    v 30,v 31,v 32,v 33,v 34,v 35,v 36,v 37,v 38,v 39]

/-- First40 arguments are SeedScore's common configuration (slot1 ignored).
Slots40--47 are seedCount,dB,dC,dPaired,targetB,targetC,targetPaired,newSpan.
Zero means no seed passed the three actual integer tests; a positive result
is selectedOrdinal+1, and the new key arrays and digit span are committed. -/
def body : Stmt :=
  .for 48 (v 40) (.call LightTernarySeedScore.entry (seedArgs (v 48)) 49) ;;
  .call (LightTernarySeedScore.entry+1) [v 35,v 36,v 37,v 38,v 40,v 41,v 42,v 43,v 44,v 45,v 46] 50 ;;
  .ite (k 0 <' v 50)
    (.set 51 (v 50 -' k 1) ;;
      .call LightTernarySeedScore.entry (seedArgs (v 51)) 49 ;;
      .call 1 [v 3,v 4,v 0 +' v 51 *' (v 2 +' k 2),v 47,v 2,v 5] 52)
    .skip ;;
  .set 0 (v 50)

def program (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) : Program :=
  LightTernarySeedScore.program p R S K raws words maps xl yl zl xr yr zr++
    [LightTernaryRowSelector.body,body]

def time (seedCount seedTime spanTime : ℕ) : ℕ :=
  (seedCount+1)*(seedTime+200)+LightTernaryRowSelector.time seedCount+spanTime+1000

def entry : ℕ := LightTernarySeedScore.entry+2

@[simp] theorem program_length (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) :
    (program p R S K raws words maps xl yl zl xr yr zr).length=167 := by
  simp [program]

def args (base : List ℤ) (seedCount dB dC dP tB tC tP newSpan : ℕ) : List ℤ :=
  base++[(seedCount : ℤ),dB,dC,dP,tB,tC,tP,newSpan]

def Inv (argv : List ℤ) (I : ℕ → (ℕ → ℤ) → Prop) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame (argv++[(i : ℤ),r]),ν⟩ ∧ I i ν

/-- The seed loop calls the concrete SeedScore program for every menu entry.
Its final selection calls the actual integer RowSelector, reconstructs the
chosen seed by calling the same score program, and executes the real span
extension. The predicates are memory invariants between these checked calls. -/
theorem program_meets {lim : Limits}
    {menu J catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold Cnew nC
      Omatrix Oold Onew nO positions wanted work hashWork hist header leftTagged rightTagged
      leftWeights rightWeights tensor countOutput quadScratch quadPowers potentialColumns
      potentialPowers flags scoreB scoreC scorePaired prefixLength R S K d
      n U dB dC dP tB tC tP newSpan seedTime spanTime : ℕ}
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ)
    (μ : ℕ → ℤ) (flag fB fC fP : ℕ → ℤ)
    (I : ℕ → (ℕ → ℤ) → Prop) (Ready Final : (ℕ → ℤ) → Prop)
    (hw : (lim.space : ℤ)≤lim.word)
    (hFlags : flags+n≤lim.space) (hBs : scoreB+n≤lim.space)
    (hCs : scoreC+n≤lim.space) (hPs : scorePaired+n≤lim.space)
    (hWord : (LightTernaryRowSelector.word n U dB dC dP tB tC tP : ℤ)≤lim.word)
    (hLen : J+2≤lim.space)
    (hRow : menu+(LightTernaryRowSelector.pick
      (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n-1)*(J+2)≤lim.space)
    (hd : d<lim.depth) (hstart : I 0 μ)
    (hstep : ∀ i<n, ∀ ν, I i ν →
      Meets lim (LightTernarySeedScore.program p R S K raws words maps xl yl zl xr yr zr)
        LightTernarySeedScore.entry (d+1)
        (LightTernarySeedScore.args menu i J catalog catalogRows p power Bmatrix Bold Bnew nB
          Cmatrix Cold Cnew nC Omatrix Oold Onew nO positions wanted work hashWork hist header
          leftTagged rightTagged leftWeights rightWeights tensor countOutput quadScratch quadPowers
          potentialColumns potentialPowers flags scoreB scoreC scorePaired prefixLength)
        ν seedTime (fun _ ξ => I (i+1) ξ))
    (hread : ∀ ν, I n ν →
      (∀ i<n, ν (flags+i)=flag i ∧ |flag i|≤1) ∧
      (∀ i<n, ν (scoreB+i)=fB i ∧ |fB i|≤U) ∧
      (∀ i<n, ν (scoreC+i)=fC i ∧ |fC i|≤U) ∧
      (∀ i<n, ν (scorePaired+i)=fP i ∧ |fP i|≤U))
    (hexist : ∃ i<n, LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP i)
    (hselected : ∀ ν, I n ν →
      Meets lim (LightTernarySeedScore.program p R S K raws words maps xl yl zl xr yr zr)
        LightTernarySeedScore.entry (d+1)
        (LightTernarySeedScore.args menu (LightTernaryRowSelector.pick
          (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n-1)
          J catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold Cnew nC
          Omatrix Oold Onew nO positions wanted work hashWork hist header leftTagged rightTagged
          leftWeights rightWeights tensor countOutput quadScratch quadPowers potentialColumns
          potentialPowers flags scoreB scoreC scorePaired prefixLength)
        ν seedTime (fun _ ξ => Ready ξ))
    (hspan : ∀ ν, Ready ν → Meets lim LightStoredSpan.program 1 (d+1)
      [catalog,catalogRows,menu+(LightTernaryRowSelector.pick
        (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n-1)*(J+2),newSpan,J,p]
      ν spanTime (fun _ ξ => Final ξ)) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) entry d
      (args (LightTernarySeedScore.args menu 0 J catalog catalogRows p power Bmatrix Bold Bnew nB
        Cmatrix Cold Cnew nC Omatrix Oold Onew nO positions wanted work hashWork hist header
        leftTagged rightTagged leftWeights rightWeights tensor countOutput quadScratch quadPowers
        potentialColumns potentialPowers flags scoreB scoreC scorePaired prefixLength)
        n dB dC dP tB tC tP newSpan) μ (time n seedTime spanTime)
      (fun r ν => r=(LightTernaryRowSelector.pick
        (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n : ℤ) ∧ Final ν) := by
  let good := LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP
  let chosen := LightTernaryRowSelector.pick good n
  let argv := args (LightTernarySeedScore.args menu 0 J catalog catalogRows p power Bmatrix Bold Bnew nB
    Cmatrix Cold Cnew nC Omatrix Oold Onew nO positions wanted work hashWork hist header
    leftTagged rightTagged leftWeights rightWeights tensor countOutput quadScratch quadPowers
    potentialColumns potentialPowers flags scoreB scoreC scorePaired prefixLength)
      n dB dC dP tB tC tP newSpan
  have hcpos : 0<chosen := (LightTernaryRowSelector.pick_pos_iff good n).mpr hexist
  have hcle : chosen≤n := LightTernaryRowSelector.pick_le good n
  have hchosenExpand : LightTernaryRowSelector.pick
      (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n=chosen := rfl
  have hnWord : (n : ℤ)≤lim.word := by omega
  have hcWord : (chosen : ℤ)≤lim.word := by omega
  have hRow' : menu+(chosen-1)*(J+2)≤lim.space := hRow
  have hrowWord : ((menu+(chosen-1)*(J+2) : ℕ) : ℤ)≤lim.word := (Int.ofNat_le.mpr hRow).trans hw
  have hprodWord : ((chosen-1 : ℕ) : ℤ)*((J : ℤ)+2)≤lim.word := by
    have hprod : (chosen-1)*(J+2)≤lim.space := by omega
    exact_mod_cast (Int.ofNat_le.mpr hprod).trans hw
  have hprodNonneg : 0≤((chosen-1 : ℕ) : ℤ)*((J : ℤ)+2) := by positivity
  have hprodNonnegFull : 0≤((LightTernaryRowSelector.pick
      (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n-1 : ℕ) : ℤ)*((J : ℤ)+2) := by positivity
  have hprodWordFull : ((LightTernaryRowSelector.pick
      (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n-1 : ℕ) : ℤ)*((J : ℤ)+2)≤lim.word := by
    simpa only [chosen,good] using hprodWord
  have hrowWordFull : (menu : ℤ)+((LightTernaryRowSelector.pick
      (LightTernaryRowSelector.Good flag fB fC fP dB dC dP tB tC tP) n-1 : ℕ) : ℤ)*((J : ℤ)+2)≤lim.word := by
    exact_mod_cast (Int.ofNat_le.mpr hRow).trans hw
  have hrowIntWord : (menu : ℤ)+((chosen-1 : ℕ) : ℤ)*((J : ℤ)+2)≤lim.word := by exact_mod_cast hrowWord
  have hlenWord : ((J : ℤ)+2)≤lim.word := by exact_mod_cast (Int.ofNat_le.mpr hLen).trans hw
  have hmain : (program p R S K raws words maps xl yl zl xr yr zr)[entry]?=some body := by
    simp only [entry,LightTernarySeedScore.entry,program,Nat.reduceAdd]
    rw [List.getElem?_append_right (by simp)]
    simp
  apply Meets.of_body hmain
  change Ends _ _ _ _ ⟨frame argv,μ⟩ _ _
  unfold body time
  refine Ends.pieceThen (Ends.for (T := n*(seedTime+100)+50)
    (Q := Inv argv I n) (Inv argv I) n (seedTime+80)
    ?start ?round ?done ?bound) ?after (hT := by light_time)
  case start =>
    refine ⟨0,μ,?_,hstart⟩
    simp only [update_frame_setLocal]
    congr 1
    simp only [argv,args,LightTernarySeedScore.args,setLocal]
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro i _ hi _ ⟨ret,ν,rfl,hI⟩
    have hcall := (hstep i hi ν hI).append [LightTernaryRowSelector.body,body]
    light_call hcall using argv,args,LightTernarySeedScore.args,seedArgs,LightTernarySeedScore.entry
      with r ξ hnext
    refine ⟨by simp [argv,args,LightTernarySeedScore.args,setLocal],r,ξ,?_,hnext⟩
    simp [argv,args,LightTernarySeedScore.args,update_frame_setLocal]
  case done => intro σ _ hI; exact hI
  case bound => rintro i _ hi _ ⟨ret,ν,rfl,hI⟩; light_side [argv,args,LightTernarySeedScore.args]
  case after =>
    rintro σ ⟨ret,ν,rfl,hI⟩
    obtain ⟨hflag,hb,hc,hp⟩ := hread ν hI
    have hsel := (LightTernaryRowSelector.meets (d := d+1)
      (by rfl : (program p R S K raws words maps xl yl zl xr yr zr)[165]?=
        some LightTernaryRowSelector.body)
      ν flag fB fC fP hw hFlags hBs hCs hPs hflag hb hc hp hWord)
    light_call hsel using argv,args,LightTernarySeedScore.args,LightTernarySeedScore.entry,chosen,good
      with picked ξ ⟨hpicked,hξ⟩
    subst ξ
    have hpositive : (0 : ℤ)<picked := by rw [hpicked]; exact_mod_cast hcpos
    light_if hyes hno : (0 : ℤ)<picked using argv,args,LightTernarySeedScore.args
    · light_set (chosen-1 : ℕ) using argv,args,LightTernarySeedScore.args,chosen,good,hpicked
      have hs := (hselected ν hI).append [LightTernaryRowSelector.body,body]
      light_call hs using argv,args,LightTernarySeedScore.args,seedArgs,LightTernarySeedScore.entry,chosen,good
        with r ξ hr
      have hsp := LightTernarySeedScore.lift_span p R S K raws words maps xl yl zl xr yr zr (hspan ξ hr)
      have hsp' := hsp.append [LightTernaryRowSelector.body,body]
      light_call hsp' using argv,args,LightTernarySeedScore.args,seedArgs,chosen,good with r ζ hfinal
      light_set chosen using argv,args,LightTernarySeedScore.args,seedArgs,chosen,good,hpicked
      exact ⟨by simp [argv,args,LightTernarySeedScore.args,setLocal,chosen,good],hfinal⟩
    · exact (hno hpositive).elim

end ThreeSum.LightTernarySeedController
