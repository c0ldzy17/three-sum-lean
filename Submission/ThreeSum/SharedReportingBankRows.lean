import Submission.ThreeSum.SharedReportingBankLevels
import Submission.ThreeSum.SharedReportingBankSourceBounds

/-! # Exact occurrence/B-band/C-band row order and retained catalog ownership -/

namespace ThreeSum.SharedReportingBankRows

open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData

set_option maxHeartbeats 1800000

def pairs (S nb nc : ℕ) : ℕ := S*nb*nc
def rank (nb nc s i j : ℕ) : ℕ := (s*nb+i)*nc+j
def total (h J NB NC g : ℕ) : ℕ :=
  pairs (LightBlockSourceCatalog.count h J) (BandPartition.size NB g) (BandPartition.size NC g)
def rowRecord (record K q : ℕ) : ℕ := record+5*K*q
def rowBase (base h J K q : ℕ) : ℕ := base+q*offset h J K

theorem digit_injective {n a b c d : ℕ} (hb : b < n) (hd : d < n)
    (he : a*n+b=c*n+d) : a=c ∧ b=d := by
  have hmod := congrArg (fun x => x%n) he
  have hbd : b=d := by simpa [Nat.add_mod,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hd] using hmod
  have hp : a*n=c*n := by omega
  exact ⟨Nat.eq_of_mul_eq_mul_right (by omega) hp,hbd⟩

theorem rank_injective {nb nc s i j s' i' j' : ℕ}
    (hi : i < nb) (hj : j < nc) (hi' : i' < nb) (hj' : j' < nc)
    (he : rank nb nc s i j=rank nb nc s' i' j') : s=s' ∧ i=i' ∧ j=j' := by
  have hinner := digit_injective hj hj' he
  have houter := digit_injective hi hi' hinner.1
  exact ⟨houter.1,houter.2,hinner.2⟩

theorem rank_lt {S nb nc s i j : ℕ} (hs : s < S) (hi : i < nb) (hj : j < nc) :
    rank nb nc s i j < pairs S nb nc := by
  have hx : s*nb+i < S*nb := calc
    _ < s*nb+nb := Nat.add_lt_add_left hi _
    _ = (s+1)*nb := by ring
    _ ≤ S*nb := Nat.mul_le_mul_right nb (by omega)
  calc
    _ < (s*nb+i)*nc+nc := Nat.add_lt_add_left hj _
    _ = (s*nb+i+1)*nc := by ring
    _ ≤ S*nb*nc := Nat.mul_le_mul_right nc (by omega)

theorem occurrence_lt {S nb nc s i j : ℕ}
    (he : rank nb nc s i j < pairs S nb nc) : s < S := by
  by_contra h
  have hs : S ≤ s := by omega
  have hp : S*nb ≤ s*nb+i := (Nat.mul_le_mul_right nb hs).trans (Nat.le_add_right _ _)
  have hq : S*nb*nc ≤ (s*nb+i)*nc+j :=
    (Nat.mul_le_mul_right nc hp).trans (Nat.le_add_right _ _)
  exact (not_lt_of_ge hq) he

theorem rank_next_c (nb nc s i j : ℕ) : rank nb nc s i (j+1)=rank nb nc s i j+1 := by
  unfold rank
  omega

theorem rank_next_b {nb nc s i j : ℕ} (hj : j+1=nc) :
    rank nb nc s (i+1) 0=rank nb nc s i j+1 := by
  subst nc
  unfold rank
  ring

theorem rank_next_s {nb nc s i j : ℕ} (hi : i+1=nb) (hj : j+1=nc) :
    rank nb nc (s+1) 0 0=rank nb nc s i j+1 := by
  subst nb nc
  unfold rank
  ring

theorem rowRecord_zero (record K : ℕ) : rowRecord record K 0=record := by simp [rowRecord]
theorem rowBase_zero (base h J K : ℕ) : rowBase base h J K 0=base := by simp [rowBase]
theorem rowRecord_succ (record K q : ℕ) : rowRecord record K (q+1)=rowRecord record K q+5*K := by
  unfold rowRecord
  ring
theorem rowBase_next (base h J K q : ℕ) :
    baseAt (rowBase base h J K q) h J K=rowBase base h J K (q+1) := by
  unfold rowBase baseAt
  ring
theorem rowBase_mono (base h J K : ℕ) : Monotone (rowBase base h J K) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

theorem entry_of_later_block {h J k record nextRecord n low bound : ℕ} {μ ν : ℕ → ℤ}
    {D : Catalog} {hk : k ≤ J} {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Entry μ record D hk f g) (heq : KeptBut μ ν bound nextRecord n)
    (hrecord : record+5 ≤ nextRecord) (hnext : nextRecord+n ≤ low)
    (hlow : low ≤ bound) (hindexLow : low ≤ D.indexBase)
    (hptrLow : low ≤ D.ptrBase) (hboxLow : low ≤ D.boxBase)
    (hindex : D.indexBase+count h k ≤ bound) (hptr : D.ptrBase+count h k ≤ bound)
    (hbox : D.boxBase+count h k*stride ((J-k)*(512*h)) D.boxCut ≤ bound) :
    Entry ν record D hk f g := by
  refine ⟨?_,H.tables.of_window (fun a ha hb => heq a ⟨hb,Or.inr (by omega)⟩)
    hindexLow hptrLow hboxLow hindex hptr hbox⟩
  intro i hi
  have hi' : i < 5 := by
    simpa only [Catalog.record,List.length_map,List.length_cons,List.length_nil] using hi
  exact (heq _ ⟨by omega,Or.inl (by omega)⟩).trans (H.header i hi)

theorem levels_of_later_row {μ ν : ℕ → ℤ} {record base h J K nextRecord nextBase : ℕ}
    {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Built μ record base h J K f g)
    (heq : KeptBut μ ν nextBase nextRecord (5*K))
    (hrecords : record+5*K ≤ nextRecord) (hnext : nextRecord+5*K ≤ base)
    (hpayload : baseAt base h J K ≤ nextBase) : Built ν record base h J K f g := by
  intro k hk
  obtain ⟨hkJ,Hk⟩ := H k hk
  have hlow := catalog_low base h J k
  have hend := catalog_end base h J k
  have hbefore := (baseAt_mono base h J (show k+1 ≤ K by omega)).trans hpayload
  refine ⟨hkJ,entry_of_later_block Hk heq (by omega) hnext
    ((Nat.le_add_right _ _).trans hpayload) hlow.1 hlow.2.1 hlow.2.2
    (hend.1.trans hbefore) (hend.2.1.trans hbefore) (hend.2.2.trans hbefore)⟩

def Done (μ : ℕ → ℤ) (record base h J K NB NC g processed : ℕ)
    (fB fC : ℕ → ℤ) (p shift : ℤ) : Prop :=
  ∀ s < LightBlockSourceCatalog.count h J, ∀ i < BandPartition.size NB g,
    ∀ j < BandPartition.size NC g,
    rank (BandPartition.size NB g) (BandPartition.size NC g) s i j < processed →
    Built μ (rowRecord record K (rank (BandPartition.size NB g) (BandPartition.size NC g) s i j))
      (rowBase base h J K (rank (BandPartition.size NB g) (BandPartition.size NC g) s i j)) h J K
      (leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val) (representative h J s))
      (rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val) (representative h J s))

theorem Done.empty (μ : ℕ → ℤ) (record base h J K NB NC g : ℕ)
    (fB fC : ℕ → ℤ) (p shift : ℤ) : Done μ record base h J K NB NC g 0 fB fC p shift := by
  intro s hs i hi j hj hr
  omega

theorem Done.append {μ ν : ℕ → ℤ} {record base h J K NB NC g s i j q : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : Done μ record base h J K NB NC g q fB fC p shift)
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g)
    (hq : q=rank (BandPartition.size NB g) (BandPartition.size NC g) s i j)
    (Hnew : Built ν (rowRecord record K q) (rowBase base h J K q) h J K
      (leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val) (representative h J s))
      (rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val) (representative h J s)))
    (heq : KeptBut μ ν (rowBase base h J K q) (rowRecord record K q) (5*K))
    (hslab : record+5*K*total h J NB NC g ≤ base) :
    Done ν record base h J K NB NC g (q+1) fB fC p shift := by
  have hqLt : q < total h J NB NC g := by rw [hq]; exact rank_lt hs hi hj
  have hmeta := Nat.mul_le_mul_left (5*K) (show q+1 ≤ total h J NB NC g by omega)
  have hnext : rowRecord record K q+5*K ≤ base := by unfold rowRecord; nlinarith
  intro s' hs' i' hi' j' hj' hr
  rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | hr
  · have Hold := H s' hs' i' hi' j' hj' hr
    have hm := Nat.mul_le_mul_left (5*K) (show
      rank (BandPartition.size NB g) (BandPartition.size NC g) s' i' j'+1 ≤ q by omega)
    apply levels_of_later_row Hold heq
    · unfold rowRecord
      nlinarith
    · exact hnext.trans (Nat.le_add_right _ _)
    · rw [rowBase_next]
      exact rowBase_mono base h J K (by omega)
  · have hh := rank_injective hi' hj' hi hj (hr.trans hq)
    rcases hh with ⟨rfl,rfl,rfl⟩
    simpa only [← hq] using Hnew

end ThreeSum.SharedReportingBankRows
