import Submission.ThreeSum.LightStoredSpan
import Submission.ThreeSum.LightTernaryAppendKeys
import Submission.ThreeSum.LightTernaryWantedBatch
import Submission.ThreeSum.LightOriginalCollisionScore
import Submission.ThreeSum.LightTernaryTensorDriver

/-! One actual extension-menu candidate. The span test sees only the first J
physical digit coefficients, while the three original hash calls see all
J+2 physical coefficients, including the two tags. -/
noncomputable section
namespace ThreeSum.LightTernarySeedScore
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

/-- 40 arguments, indexed as follows.
0 physical menu; 1 seed; 2 J; 3 span catalog; 4 catalog rows; 5 p; 6 p^j;
7 B matrix; 8 old B keys; 9 new B keys; 10 nB;
11 C matrix; 12 old C keys; 13 new C keys; 14 nC;
15 requester/carry matrix; 16 old requester keys; 17 new requester keys; 18 nO;
19 original requester positions; 20 wanted rows; 21 wanted work; 22 hash work;
23 collision histogram; 24 source/count header;
25 tagged B; 26 tagged C; 27 B weights; 28 C weights;
29 fourth tensor; 30 count output; 31 four-column scratch; 32 four-column powers;
33 potential columns; 34 potential powers;
35 admissibility flags; 36 B scores; 37 C scores; 38 paired scores;
39 new prefix length j+1.
The 106-cell source/count header uses these fixed new-key/wanted-row pointers;
its wanted-count slot104 is set from the actual emitted row cursor. -/
def body : Stmt :=
  .set 40 (v 2 +' k 2) ;;
  .set 41 (v 0 +' v 1 *' v 40) ;;
  .call 6 [v 3,v 4,v 2,v 41] 42 ;;
  .call 14 [v 7,v 41,v 8,v 9,v 10,v 40,v 5,v 6,v 22] 48 ;;
  .call 14 [v 11,v 41,v 12,v 13,v 14,v 40,v 5,v 6,v 22] 48 ;;
  .call 14 [v 15,v 41,v 16,v 17,v 18,v 40,v 5,v 6,v 22] 48 ;;
  .call 19 [v 39,v 17,v 19,v 18,v 20,v 21] 43 ;;
  .call 24 [v 43 -' v 20,k 3] 44 ;;
  .call 20 [v 9,v 10,v 23,v 6 *' v 5] 45 ;;
  .call 20 [v 13,v 14,v 23,v 6 *' v 5] 46 ;;
  .store (v 24 +' k 104) (v 44) ;;
  .call (25+LightTernaryTensorDriver.entry) [v 24,v 25,v 10,v 26,v 14,v 2,v 27,v 28,v 29,v 44,v 30,
    v 31,v 32,v 33,v 34] 47 ;;
  .store (v 35 +' v 1) (v 42) ;;
  .store (v 36 +' v 1) (v 45) ;;
  .store (v 37 +' v 1) (v 46) ;;
  .store (v 38 +' v 1) (v 47) ;;
  .set 0 (v 42)

def spanAppend : Program := ReportingHostRelocation.program
  LightStoredSpan.program LightTernaryAppendKeys.program

def withWanted (p R S : ℕ) (raws : List ℤ) (words maps : List ℕ) : Program :=
  ReportingHostRelocation.program spanAppend
    (LightTernaryWantedBatch.program p R S raws words maps)

def withCollision (p R S : ℕ) (raws : List ℤ) (words maps : List ℕ) : Program :=
  ReportingHostRelocation.program (withWanted p R S raws words maps)
    LightOriginalCollisionScore.program

def withDivision (p R S : ℕ) (raws : List ℤ) (words maps : List ℕ) : Program :=
  ReportingHostRelocation.program (withCollision p R S raws words maps) LightSmallDivide.program

def libraries (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) : Program :=
  ReportingHostRelocation.program (withDivision p R S raws words maps)
    (LightTernaryTensorDriver.program xl yl zl xr yr zr K)

def program (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) : Program :=
  libraries p R S K raws words maps xl yl zl xr yr zr++[body]

def time (TS TB TC TO TW TD XB XC TP : ℕ) : ℕ :=
  TS+TB+TC+TO+TW+TD+XB+XC+TP+1000

@[simp] theorem spanAppend_length : spanAppend.length=15 := rfl
@[simp] theorem wanted_length (p R S : ℕ) (raws : List ℤ) (words maps : List ℕ) :
    (LightTernaryWantedBatch.program p R S raws words maps).length=5 := rfl
@[simp] theorem withWanted_length (p R S : ℕ) (raws : List ℤ) (words maps : List ℕ) :
    (withWanted p R S raws words maps).length=20 := by
  simp [withWanted,ReportingHostRelocation.program]
@[simp] theorem withCollision_length (p R S : ℕ) (raws : List ℤ) (words maps : List ℕ) :
    (withCollision p R S raws words maps).length=24 := by
  simp [withCollision,ReportingHostRelocation.program]
@[simp] theorem withDivision_length (p R S : ℕ) (raws : List ℤ) (words maps : List ℕ) :
    (withDivision p R S raws words maps).length=25 := by
  simp [withDivision,ReportingHostRelocation.program,LightSmallDivide.program]
@[simp] theorem libraries_length (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) :
    (libraries p R S K raws words maps xl yl zl xr yr zr).length=164 := by
  simp [libraries,ReportingHostRelocation.program]
@[simp] theorem program_length (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) :
    (program p R S K raws words maps xl yl zl xr yr zr).length=165 := by simp [program]

def args (menu seed J catalog catalogRows p power Bmatrix Bold Bnew nB
    Cmatrix Cold Cnew nC Omatrix Oold Onew nO positions wanted work hashWork hist
    header leftTagged rightTagged leftWeights rightWeights tensor countOutput quadScratch
    quadPowers potentialColumns potentialPowers flags scoreB scoreC scorePaired prefixLength : ℕ) : List ℤ :=
  [menu,seed,J,catalog,catalogRows,p,power,Bmatrix,Bold,Bnew,nB,Cmatrix,Cold,Cnew,nC,
    Omatrix,Oold,Onew,nO,positions,wanted,work,hashWork,hist,header,leftTagged,rightTagged,
    leftWeights,rightWeights,tensor,countOutput,quadScratch,quadPowers,potentialColumns,
    potentialPowers,flags,scoreB,scoreC,scorePaired,prefixLength]

section Lift
variable {lim : Limits} {entry depth T : ℕ} {vals : List ℤ} {μ : ℕ → ℤ}
  {Post : ℤ → (ℕ → ℤ) → Prop}

theorem lift_span (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ)
    (h : Meets lim LightStoredSpan.program entry depth vals μ T Post) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) entry depth vals μ T Post := by
  have hh := h.append
    (LightTernaryAppendKeys.program.map (ReportingHostRelocation.relocate 8)++
      (LightTernaryWantedBatch.program p R S raws words maps).map (ReportingHostRelocation.relocate 15)++
      LightOriginalCollisionScore.program.map (ReportingHostRelocation.relocate 20)++
      LightSmallDivide.program.map (ReportingHostRelocation.relocate 24)++
      (LightTernaryTensorDriver.program xl yl zl xr yr zr K).map (ReportingHostRelocation.relocate 25)++[body])
  simpa only [program,libraries,withDivision,withCollision,withWanted,spanAppend,
    ReportingHostRelocation.program,LightStoredSpan.program_length,
    LightTernaryAppendKeys.program,LightSignedRowHash.program,
    wanted_length,LightOriginalCollisionScore.program_length,LightSmallDivide.program,
    List.length_append,List.length_map,List.length_cons,List.length_nil,Nat.reduceAdd,
    List.append_assoc] using hh

theorem lift_append (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ)
    (h : Meets lim LightTernaryAppendKeys.program entry depth vals μ T Post) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) (8+entry) depth vals μ T Post := by
  have hh := (ReportingHostRelocation.meets h LightStoredSpan.program).append
    ((LightTernaryWantedBatch.program p R S raws words maps).map (ReportingHostRelocation.relocate 15)++
      LightOriginalCollisionScore.program.map (ReportingHostRelocation.relocate 20)++
      LightSmallDivide.program.map (ReportingHostRelocation.relocate 24)++
      (LightTernaryTensorDriver.program xl yl zl xr yr zr K).map (ReportingHostRelocation.relocate 25)++[body])
  simpa only [program,libraries,withDivision,withCollision,withWanted,spanAppend,
    ReportingHostRelocation.program,LightStoredSpan.program_length,
    LightTernaryAppendKeys.program,LightSignedRowHash.program,
    wanted_length,LightOriginalCollisionScore.program_length,LightSmallDivide.program,
    List.length_append,List.length_map,List.length_cons,List.length_nil,Nat.reduceAdd,
    List.append_assoc] using hh

theorem lift_wanted (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ)
    (h : Meets lim (LightTernaryWantedBatch.program p R S raws words maps) entry depth vals μ T Post) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) (15+entry) depth vals μ T Post := by
  have hh := (ReportingHostRelocation.meets h spanAppend).append
    (LightOriginalCollisionScore.program.map (ReportingHostRelocation.relocate 20)++
      LightSmallDivide.program.map (ReportingHostRelocation.relocate 24)++
      (LightTernaryTensorDriver.program xl yl zl xr yr zr K).map (ReportingHostRelocation.relocate 25)++[body])
  simpa only [program,libraries,withDivision,withCollision,withWanted,spanAppend_length,
    ReportingHostRelocation.program,wanted_length,LightOriginalCollisionScore.program_length,
    LightSmallDivide.program,List.length_append,List.length_map,List.length_cons,List.length_nil,
    Nat.reduceAdd,List.append_assoc] using hh

theorem lift_collision (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ)
    (h : Meets lim LightOriginalCollisionScore.program entry depth vals μ T Post) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) (20+entry) depth vals μ T Post := by
  have hh := (ReportingHostRelocation.meets h (withWanted p R S raws words maps)).append
    (LightSmallDivide.program.map (ReportingHostRelocation.relocate 24)++
      (LightTernaryTensorDriver.program xl yl zl xr yr zr K).map (ReportingHostRelocation.relocate 25)++[body])
  simpa only [program,libraries,withDivision,withCollision,withWanted_length,
    ReportingHostRelocation.program,LightOriginalCollisionScore.program_length,LightSmallDivide.program,
    List.length_append,List.length_map,List.length_cons,List.length_nil,Nat.reduceAdd,List.append_assoc] using hh

theorem lift_divide (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ)
    (h : Meets lim LightSmallDivide.program entry depth vals μ T Post) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) (24+entry) depth vals μ T Post := by
  have hh := (ReportingHostRelocation.meets h (withCollision p R S raws words maps)).append
    ((LightTernaryTensorDriver.program xl yl zl xr yr zr K).map (ReportingHostRelocation.relocate 25)++[body])
  simpa only [program,libraries,withDivision,withCollision_length,
    ReportingHostRelocation.program,LightSmallDivide.program,
    List.length_append,List.length_map,List.length_cons,List.length_nil,Nat.reduceAdd,List.append_assoc] using hh

theorem lift_tensor (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ)
    (h : Meets lim (LightTernaryTensorDriver.program xl yl zl xr yr zr K) entry depth vals μ T Post) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) (25+entry) depth vals μ T Post := by
  have hh := (ReportingHostRelocation.meets h (withDivision p R S raws words maps)).append [body]
  simpa only [program,libraries,withDivision_length] using hh
end Lift

def entry : ℕ := 164

/-- The candidate's four scalar outputs are stored only after all its actual
kernels have finished. This makes the score arrays independent of scratch
reuse. The execution receipts below name the included concrete libraries,
including the actual tensor/source/count program; there is no score oracle. -/
theorem program_meets {lim : Limits}
    {menu seed J catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold Cnew nC
      Omatrix Oold Onew nO positions wanted work hashWork hist header leftTagged rightTagged
      leftWeights rightWeights tensor countOutput quadScratch quadPowers potentialColumns
      potentialPowers flags scoreB scoreC scorePaired prefixLength R S K d
      TS TB TC TO TW TD XB XC TP H : ℕ}
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ)
    (μ : ℕ → ℤ) (flag collisionB collisionC paired : ℤ)
    (PB PC PO PW PX PY PZ : (ℕ → ℤ) → Prop)
    (hw : (lim.space : ℤ)≤lim.word) (hLen : J+2≤lim.space)
    (hRow : menu+seed*(J+2)≤lim.space)
    (hMod : power*p≤lim.space) (hHeader : header+104<lim.space)
    (hWanted : wanted+3*H≤lim.space) (hDivWord : ((3*H+5 : ℕ) : ℤ)≤lim.word)
    (hFlagAddr : flags+seed<lim.space) (hBAddr : scoreB+seed<lim.space)
    (hCAddr : scoreC+seed<lim.space) (hPAddr : scorePaired+seed<lim.space)
    (hFlagWord : |flag|≤lim.word) (hBWord : |collisionB|≤lim.word)
    (hCWord : |collisionC|≤lim.word) (hPWord : |paired|≤lim.word)
    (hd : d<lim.depth) (hTD : LightSmallDivide.time (3*H) 3≤TD)
    (hSpan : Meets lim LightStoredSpan.program 6 (d+1)
      [catalog,catalogRows,J,menu+seed*(J+2)] μ TS (fun r ν => r=flag ∧ ν=μ))
    (hB : Meets lim LightTernaryAppendKeys.program 6 (d+1)
      [Bmatrix,menu+seed*(J+2),Bold,Bnew,nB,J+2,p,power,hashWork] μ TB (fun _ ν => PB ν))
    (hC : ∀ ν, PB ν → Meets lim LightTernaryAppendKeys.program 6 (d+1)
      [Cmatrix,menu+seed*(J+2),Cold,Cnew,nC,J+2,p,power,hashWork] ν TC (fun _ ξ => PC ξ))
    (hO : ∀ ν, PC ν → Meets lim LightTernaryAppendKeys.program 6 (d+1)
      [Omatrix,menu+seed*(J+2),Oold,Onew,nO,J+2,p,power,hashWork] ν TO (fun _ ξ => PO ξ))
    (hW : ∀ ν, PO ν → Meets lim (LightTernaryWantedBatch.program p R S raws words maps) 4 (d+1)
      [prefixLength,Onew,positions,nO,wanted,work] ν TW
      (fun r ξ => r=((wanted+3*H : ℕ) : ℤ) ∧ PW ξ))
    (hXB : ∀ ν, PW ν → Meets lim LightOriginalCollisionScore.program 0 (d+1)
      [Bnew,nB,hist,power*p] ν XB (fun r ξ => r=collisionB ∧ PX ξ))
    (hXC : ∀ ν, PX ν → Meets lim LightOriginalCollisionScore.program 0 (d+1)
      [Cnew,nC,hist,power*p] ν XC (fun r ξ => r=collisionC ∧ PY ξ))
    (hTensor : ∀ ν, PY ν →
      Meets lim (LightTernaryTensorDriver.program xl yl zl xr yr zr K) LightTernaryTensorDriver.entry (d+1)
        [header,leftTagged,nB,rightTagged,nC,J,leftWeights,rightWeights,tensor,H,countOutput,
          quadScratch,quadPowers,potentialColumns,potentialPowers]
        (Function.update ν (header+104) (H : ℤ)) TP (fun r ξ => r=paired ∧ PZ ξ)) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) 164 d
      (args menu seed J catalog catalogRows p power Bmatrix Bold Bnew nB Cmatrix Cold Cnew nC
        Omatrix Oold Onew nO positions wanted work hashWork hist header leftTagged rightTagged
        leftWeights rightWeights tensor countOutput quadScratch quadPowers potentialColumns
        potentialPowers flags scoreB scoreC scorePaired prefixLength) μ
      (time TS TB TC TO TW TD XB XC TP)
      (fun r ν => r=flag ∧ ∃ ξ, PZ ξ ∧ ν=
        Function.update (Function.update (Function.update (Function.update ξ
          (flags+seed) flag) (scoreB+seed) collisionB) (scoreC+seed) collisionC)
          (scorePaired+seed) paired) := by
  have hlengthWord : ((J+2 : ℕ) : ℤ)≤lim.word := (Int.ofNat_le.mpr hLen).trans hw
  have hrowWord : ((menu+seed*(J+2) : ℕ) : ℤ)≤lim.word := (Int.ofNat_le.mpr hRow).trans hw
  have hprodWord : ((seed*(J+2) : ℕ) : ℤ)≤lim.word := by omega
  have hprodNonneg : 0≤(seed : ℤ)*((J : ℤ)+2) := by positivity
  have hprodIntWord : (seed : ℤ)*((J : ℤ)+2)≤lim.word := by exact_mod_cast hprodWord
  have hrowIntWord : (menu : ℤ)+(seed : ℤ)*((J : ℤ)+2)≤lim.word := by exact_mod_cast hrowWord
  have hmodWord : ((power*p : ℕ) : ℤ)≤lim.word := (Int.ofNat_le.mpr hMod).trans hw
  have hcountWord : (H : ℤ)≤lim.word := by omega
  have h0 := lift_span p R S K raws words maps xl yl zl xr yr zr hSpan
  have h1 := lift_append p R S K raws words maps xl yl zl xr yr zr hB
  have hmain : (program p R S K raws words maps xl yl zl xr yr zr)[164]?=some body := by
    unfold program
    rw [← libraries_length p R S K raws words maps xl yl zl xr yr zr]
    simp
  apply Meets.of_body hmain
  unfold body time
  light_set (J+2 : ℕ) using args
  light_set (menu+seed*(J+2) : ℕ) using args
  light_call h0 using args with rs μs ⟨hrs,hμs⟩
  subst μs
  light_call h1 using args with rb μb hb
  have h2 := lift_append p R S K raws words maps xl yl zl xr yr zr (hC μb hb)
  light_call h2 using args with rc μc hc
  have h3 := lift_append p R S K raws words maps xl yl zl xr yr zr (hO μc hc)
  light_call h3 using args with ro μo ho
  have h4 := lift_wanted p R S K raws words maps xl yl zl xr yr zr (hW μo ho)
  light_call h4 using args with rwanted μw ⟨hrwanted,hwanted⟩
  have hdivide := (LightSmallDivide.program_meets (d := d+1) (a := 3*H) (b := 3) μw hDivWord).mono_time hTD
  have hdivide' : Meets lim LightSmallDivide.program 0 (d+1) [((3*H : ℕ) : ℤ),3] μw TD
      (fun r ν => r=(H : ℤ) ∧ ν=μw) := by
    simpa only [Nat.mul_div_right H (by decide : 0<3),Nat.cast_ofNat] using hdivide
  have h5 := lift_divide p R S K raws words maps xl yl zl xr yr zr hdivide'
  light_call h5 using args,hrwanted with rcount μd ⟨hrcount,hμd⟩
  subst μd
  have h6 := lift_collision p R S K raws words maps xl yl zl xr yr zr (hXB μw hwanted)
  light_call h6 using args with xb μxb ⟨hrxb,hxb⟩
  have h7 := lift_collision p R S K raws words maps xl yl zl xr yr zr (hXC μxb hxb)
  light_call h7 using args with xc μxc ⟨hrxc,hxc⟩
  light_store (header+104) (H : ℕ) using args,hrcount
  have h8 := lift_tensor p R S K raws words maps xl yl zl xr yr zr (hTensor μxc hxc)
  light_call h8 using args,hrcount with xp μxp ⟨hrxp,hxp⟩
  light_store (flags+seed) flag using args,hrs
  light_store (scoreB+seed) collisionB using args,hrxb
  light_store (scoreC+seed) collisionC using args,hrxc
  light_store (scorePaired+seed) paired using args,hrxp
  light_set flag using args,hrs
  exact ⟨by simp [args,setLocal],μxp,hxp,rfl⟩

end ThreeSum.LightTernarySeedScore
