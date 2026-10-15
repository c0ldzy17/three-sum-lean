import Submission.ThreeSum.TernaryArenaSourceControls

/-! Polynomial envelopes for the actual source word/depth controls. The
capacity base is n+U; no bound on the caller's free pointer is assumed. -/
noncomputable section
namespace ThreeSum.TernaryArenaSourceControlBudget
open Light TernaryArenaSourceSetup TernaryArenaSourceControls
open TernaryArenaPairMass TernaryLocalParameters TernaryNativeCompleteFrontend
open TernaryCoverGoodMaps StageBounds
variable {p m F r : ℕ} [Fact p.Prime]

theorem bank_le (m r : ℕ) : nb m r≤4^(N m r) := by
  classical
  have hn : (bankCodes m r).Nodup := (TernaryAddresses.codes_strictly_sorted _ _).nodup
  calc
    _=((bankCodes m r).toFinset).card := (List.toFinset_card_of_nodup hn).symm
    _≤(Finset.range (4^(N m r))).card := by
      apply Finset.card_le_card
      intro a ha
      exact Finset.mem_range.mpr (TernaryAddresses.mem_codes_lt (List.mem_toFinset.mp ha))
    _=_ := Finset.card_range _

def baseWord (m p F r : ℕ) : ℕ :=
  LightRadixKeys.word p p r+LightRadixKeys.word (4^fixedLength m) (4^fixedLength m) r+
    LightRadixKeys.word F F r+LightSourceResidues.word (p^r) (p^r) (p*(p+1)^r) 0+
    (4^(N m r)+2^(2*N m r+1)+16)+(F^r*4^(N m r)+1)+2^(r*fixedAlpha m 2)
def weightCoefficient (m R r n : ℕ) : ℕ :=
  2^(r*fixedAlpha m 2)*(n*R^r)+(n*R^r+1)
def upperWord (m p F R r n w : ℕ) : ℕ :=
  baseWord m p F r+weightCoefficient m R r n*w

theorem actual_word_le (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (n : ℕ) (hn : (source (r := r) maps cap I right).NL≤n) :
    word (r := r) maps cap I right≤
      upperWord m p F (tableWidth maps cap+1) r n I.weightCap := by
  have hl : (localRecords maps cap right).length≤tableWidth maps cap+1 := by
    cases right <;> simp only [tableWidth] <;> omega
  have hrow : rowBound (r := r) maps cap I right≤n*(tableWidth maps cap+1)^r :=
    Nat.mul_le_mul hn (Nat.pow_le_pow_left hl r)
  have hb := bank_le m r
  calc
    _≤LightRadixKeys.word p p r+
        (LightRadixKeys.word (4^fixedLength m) (4^fixedLength m) r+
        (LightRadixKeys.word F F r+
        (LightSourceResidues.word (p^r) (p^r) (p*(p+1)^r) 0+
        ((4^(N m r)+2^(2*N m r+1)+16)+
        ((F^r*4^(N m r)+1)+(2^(r*fixedAlpha m 2)+
        (2^(r*fixedAlpha m 2)*(n*(tableWidth maps cap+1)^r*I.weightCap)+
        ((n*(tableWidth maps cap+1)^r+1)*I.weightCap+0)))))))) := by
      dsimp only [word,components,source]
      simp only [List.sum_cons,List.sum_nil]
      gcongr
    _=_ := by unfold upperWord baseWord weightCoefficient; ring

theorem upperWord_mono {m p F R r s n a w v : ℕ}
    (hp : 1≤p) (hF : 1≤F) (hR : 1≤R) (hr : r≤s) (hn : n≤a) (hw : w≤v) :
    upperWord m p F R r n w≤upperWord m p F R s a v := by
  have hfour : 1≤4^fixedLength m := Nat.one_le_pow _ _ (by decide)
  unfold upperWord baseWord weightCoefficient LightRadixKeys.word LightRadixRows.word
    LightSourceResidues.word N
  gcongr <;> omega

private def Poly (f : ℕ→ℕ) : Prop :=∃ a : ℝ, PowerBound f a
private theorem Poly.const (c : ℕ) : Poly (fun _ => c) :=⟨0,PowerBound.const c⟩
private theorem Poly.add {f g : ℕ→ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun n => f n+g n) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  exact ⟨max a b,(ha.mono_exponent (le_max_left _ _)).add_same (hb.mono_exponent (le_max_right _ _))⟩
private theorem Poly.mul {f g : ℕ→ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun n => f n*g n) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  exact ⟨a+b,ha.mul hb⟩
private theorem Poly.pow {f : ℕ→ℕ} (hf : Poly f) (k : ℕ) : Poly (fun n => f n^k) := by
  obtain ⟨a,ha⟩ := hf
  exact ⟨k*a,ha.pow k⟩

private theorem pow_clog_poly (M A : ℕ) (hM : 1<M) : Poly (fun n => A^(Nat.clog M (n^2))) := by
  have hplus : PowerBound (fun n => n+1) 1 := ArithmeticStageBounds.identity_powerBound.add_same
    ((PowerBound.const 1).mono_exponent (by norm_num))
  have hh := (PowerBound.const (M^A)).mul (hplus.pow (2*A))
  exact ⟨_,ArithmeticStageBounds.powerBound_mono hh
    (Filter.Eventually.of_forall (fun n => fixed_pow_clog M A n hM))⟩

private theorem native_power (A m r : ℕ) : A^(N m r)=(A^fixedLength m)^r := by
  unfold N
  rw [Nat.mul_comm r,pow_mul]
private theorem factor_power (m r : ℕ) : 2^(r*fixedAlpha m 2)=(2^fixedAlpha m 2)^r := by
  rw [Nat.mul_comm r,pow_mul]
private theorem lookup_power (m r : ℕ) : 2^(2*N m r+1)=2*(4^fixedLength m)^r := by
  rw [pow_succ,Nat.pow_mul,native_power]
  norm_num
  ring

private theorem radix_poly (M P : ℕ) (hM : 1<M) :
    Poly (fun n => LightRadixKeys.word P P (Nat.clog M (n^2))) := by
  simpa only [LightRadixKeys.word,LightRadixRows.word] using
    ((((Poly.const P).add ((Poly.const P).mul ((Poly.const P).mul
      (pow_clog_poly M (P+1) hM))))).add (Poly.const P)).add (Poly.const 1)

private theorem base_poly (M p m F : ℕ) (hM : 1<M) :
    Poly (fun n => baseWord m p F (Nat.clog M (n^2))) := by
  have hp := pow_clog_poly M p hM
  have hnext := pow_clog_poly M (p+1) hM
  have hfour := pow_clog_poly M (4^fixedLength m) hM
  have hF := pow_clog_poly M F hM
  have hfactor := pow_clog_poly M (2^fixedAlpha m 2) hM
  have hjoin : Poly (fun n => LightSourceResidues.word (p^Nat.clog M (n^2))
      (p^Nat.clog M (n^2)) (p*(p+1)^Nat.clog M (n^2)) 0) := by
    simpa only [LightSourceResidues.word,Nat.mul_zero,Nat.add_zero] using
      ((((Poly.const 4).mul ((Poly.const p).mul hnext)).add ((Poly.const 8).mul hp)).add
        ((Poly.const 4).mul hp)).add (Poly.const 32)
  have hlookup := (hfour.add ((Poly.const 2).mul hfour)).add (Poly.const 16)
  have hgroup := (hF.mul hfour).add (Poly.const 1)
  simpa only [baseWord,native_power,lookup_power,factor_power] using
    ((((((radix_poly M p hM).add (radix_poly M (4^fixedLength m) hM)).add
      (radix_poly M F hM)).add hjoin).add hlookup).add hgroup).add hfactor

def budget (m p F R M W E n U : ℕ) : Need :=
  ⟨(baseWord m p F (Nat.clog M (n^2))+
      weightCoefficient m R (Nat.clog M (n^2)) n*(W+1))*(U+1)^E,
    0,n+2*N m (Nat.clog M (n^2))+Nat.clog M (n^2)+8⟩

theorem budget_polyNeed (m p F R M W E : ℕ) (hM : 1<M) :
    PolyNeed (budget m p F R M W E) := by
  have hid : Poly (fun n : ℕ => n) :=⟨1,ArithmeticStageBounds.identity_powerBound⟩
  have hcoeff : Poly (fun n => weightCoefficient m R (Nat.clog M (n^2)) n) := by
    simpa only [weightCoefficient,factor_power] using
      ((pow_clog_poly M (2^fixedAlpha m 2) hM).mul
        (hid.mul (pow_clog_poly M R hM))).add
      ((hid.mul (pow_clog_poly M R hM)).add (Poly.const 1))
  obtain ⟨aw,hw⟩ := (base_poly M p m F hM).add (hcoeff.mul (Poly.const (W+1)))
  have hr : Poly (fun n : ℕ => Nat.clog M (n^2)) := by
    refine ⟨2,?_⟩
    apply ArithmeticStageBounds.powerBound_mono (by simpa using ArithmeticStageBounds.identity_powerBound.pow 2)
    exact Filter.Eventually.of_forall fun n => Nat.clog_le_of_le_pow (Nat.lt_pow_self hM).le
  obtain ⟨ad,hd⟩ := ((hid.add ((Poly.const 2).mul (hr.mul (Poly.const (fixedLength m))))).add hr).add (Poly.const 8)
  apply PolynomialResources.polyNeed_of_separate_envelopes hw (PowerBound.const 0) hd E 0 0
  · intro n U; exact le_rfl
  · intro n U; simp only [budget,pow_zero,mul_one,le_refl]
  · intro n U; simp only [budget,pow_zero,mul_one,N]
    exact le_rfl

theorem actual_need_le_budget (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (M n U W E : ℕ) (hM : 1<M) (hF : 1≤F) (hr : r≤Nat.clog M (n^2))
    (hn : (source (r := r) maps cap I right).NL≤n) (hweight : I.weightCap≤W*(U+1)^E) :
    (need (r := r) maps cap I right).word≤
        (budget m p F (tableWidth maps cap+1) M W E n U).word ∧
    (need (r := r) maps cap I right).depth≤
        (budget m p F (tableWidth maps cap+1) M W E n U).depth := by
  refine ⟨?_,?_⟩
  · apply (actual_word_le maps cap I right n hn).trans
    have hm := upperWord_mono (m := m) (p := p) (F := F) (R := tableWidth maps cap+1)
      (Fact.out : p.Prime).one_lt.le hF (by omega) hr (le_refl n) hweight
    apply hm.trans
    have hp : 1≤(U+1)^E := Nat.one_le_pow _ _ (by omega)
    dsimp only [upperWord,budget]
    have hb := Nat.le_mul_of_pos_right (baseWord m p F (Nat.clog M (n^2))) hp
    calc
      _≤baseWord m p F (Nat.clog M (n^2))*(U+1)^E+
          weightCoefficient m (tableWidth maps cap+1) (Nat.clog M (n^2)) n*((W+1)*(U+1)^E) :=
        Nat.add_le_add hb (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_succ W)))
      _=_ := by ring
  · dsimp only [need,depth,source,budget,N] at *
    nlinarith only [hn,hr]

theorem controls_of_budget {lim : Limits} {d fr : ℕ}
    (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (M n U W E : ℕ) (hM : 1<M) (hF : 1≤F) (hr : r≤Nat.clog M (n^2))
    (hn : (source (r := r) maps cap I right).NL≤n) (hweight : I.weightCap≤W*(U+1)^E)
    (h : (budget m p F (tableWidth maps cap+1) M W E n U).Ok lim fr d) :
    Controls (r := r) maps cap I right lim d := by
  have hb := actual_need_le_budget maps cap I right M n U W E hM hF hr hn hweight
  exact controls (fr := fr) maps cap I right
    (h.mono (fr' := fr) (d' := d) hb.1 (by simp [need,budget]) (Nat.add_le_add_left hb.2 d))

end ThreeSum.TernaryArenaSourceControlBudget
