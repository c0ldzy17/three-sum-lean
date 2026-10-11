import Submission.ThreeSum.DenseGuardWanted
import Submission.ThreeSum.BandRawAFinite

/-!
# The actual wanted array on physical owner-incidence indices

The key constructor uses the mapped A-value list. The reporter and dense
owner domains use physical positions in the incidence-label list. Their
length-preserving transport keeps every physical position, lift and full
output record, including positions holding equal integer values.
-/

namespace ThreeSum.ReportingHostWantedPhysical

open Light BandRawA BandCandidateRows RawIncidences GlobalEncoding

set_option maxHeartbeats 2100000
set_option maxRecDepth 10000

/-- The exact, value-preserving finite index transport; no sorting or
identification of equal values occurs. -/
def incidenceIndices (f : ℕ→ℤ) (n g : ℕ) (rs : List Record) :
    Fin (values f (items n g rs)).length ≃ Fin (items n g rs).length where
  toFun i := ⟨i.val,by simpa only [values_length] using i.isLt⟩
  invFun i := ⟨i.val,by simpa only [values_length] using i.isLt⟩
  left_inv i := Fin.ext rfl
  right_inv i := Fin.ext rfl

@[simp] theorem incidenceIndices_val (f : ℕ→ℤ) (n g : ℕ) (rs : List Record)
    (i : Fin (values f (items n g rs)).length) :
    (incidenceIndices f n g rs i).val=i.val := rfl

@[simp] theorem incidenceIndices_symm_val (f : ℕ→ℤ) (n g : ℕ) (rs : List Record)
    (i : Fin (items n g rs).length) :
    ((incidenceIndices f n g rs).symm i).val=i.val := rfl

def transport {α β : Type*} {h J : ℕ} (e : α≃β)
    (w : RawReporting.Wanted h J α) : RawReporting.Wanted h J β := (e w.1,w.2)

theorem transport_injective {α β : Type*} {h J : ℕ} (e : α≃β) :
    Function.Injective (transport (h := h) (J := J) e) := by
  intro w w' he
  exact Prod.ext (e.injective (congrArg (fun z : RawReporting.Wanted h J β => z.1) he))
    (congrArg (fun z : RawReporting.Wanted h J β => z.2) he)

@[simp] theorem transport_symm {α β : Type*} {h J : ℕ} (e : α≃β)
    (w : RawReporting.Wanted h J β) : transport e (transport e.symm w)=w := by
  rcases w with ⟨i,q⟩
  simp only [transport,Equiv.apply_symm_apply]

section Actual

variable {μ : ℕ→ℤ} {f : ℕ→ℤ} {n g free M P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P (values f (items n g rs)))
    (LightGuardedWanted.right h J) (3*(values f (items n g rs)).length)
    (LightGuardedWanted.totalKeys h J) shift)

def wantedAt (slot : Fin (μ free).toNat) : RawReporting.Wanted h J (Fin (items n g rs).length) :=
  transport (incidenceIndices f n g rs) (DenseGuardWanted.labelAt H slot)

theorem wantedAt_injective : Function.Injective (wantedAt H) :=
  (transport_injective (incidenceIndices f n g rs)).comp (DenseGuardWanted.labelAt_injective H)

theorem wantedAt_position (slot : Fin (μ free).toNat) :
    (wantedAt H slot).1.val=
      DenseGuardWanted.leftIndex μ free (3*(items n g rs).length)
        (LightGuardedWanted.totalKeys h J) M slot.val%(items n g rs).length := by
  simp only [wantedAt,transport,incidenceIndices,DenseGuardWanted.labelAt,
    WantedRecordOrder.label,values_length,Equiv.coe_fn_mk]

theorem wantedAt_lift (slot : Fin (μ free).toNat) :
    (wantedAt H slot).2.1.val=
      DenseGuardWanted.leftIndex μ free (3*(items n g rs).length)
        (LightGuardedWanted.totalKeys h J) M slot.val/(items n g rs).length := by
  simp only [wantedAt,transport,DenseGuardWanted.labelAt,WantedRecordOrder.label,values_length]

theorem wantedAt_output (slot : Fin (μ free).toNat) :
    (wantedAt H slot).2.2=LightOutputDecodeOriginal.output h J
      (DenseGuardWanted.rightIndex μ free (3*(items n g rs).length)
        (LightGuardedWanted.totalKeys h J) M slot.val) := by
  simp only [wantedAt,transport,DenseGuardWanted.labelAt,WantedRecordOrder.label,values_length]

include H in
theorem index_bounds (slot : Fin (μ free).toNat) :
    DenseGuardWanted.leftIndex μ free (3*(items n g rs).length)
      (LightGuardedWanted.totalKeys h J) M slot.val<3*(items n g rs).length ∧
    DenseGuardWanted.rightIndex μ free (3*(items n g rs).length)
      (LightGuardedWanted.totalKeys h J) M slot.val<LightGuardedWanted.totalKeys h J := by
  simpa only [values_length] using DenseGuardWanted.output_bounds H slot.isLt

theorem wantedAt_key (slot : Fin (μ free).toNat) :
    (M : ℤ) ∣ valueAt n g rs f (wantedAt H slot).1.val%(P : ℤ)+
      lift (wantedAt H slot).2.1*(P : ℤ)+shift-globalKey (wantedAt H slot).2.2 := by
  exact RawAKeyLists.mem_wanted.mp (DenseGuardWanted.labelAt_mem H slot)

theorem wantedAt_original_key (slot : Fin (μ free).toNat) :
    (M : ℤ) ∣ f (BandRawA.labelAt n g rs (wantedAt H slot).1.val).position%(P : ℤ)+
      lift (wantedAt H slot).2.1*(P : ℤ)+shift-globalKey (wantedAt H slot).2.2 := by
  have hh := wantedAt_key H slot
  unfold valueAt at hh
  rwa [values_getD f (wantedAt H slot).1.isLt] at hh

theorem wantedAt_owner_bounds (slot : Fin (μ free).toNat) :
    (BandRawA.labelAt n g rs (wantedAt H slot).1.val).owner<rs.length ∧
      (ownerRecord n g rs (wantedAt H slot).1.val).flag=1 :=
  ⟨(at_bounds (wantedAt H slot).1.isLt).1,(at_bounds (wantedAt H slot).1.isLt).2.1⟩

theorem wantedAt_mem_owner (slot : Fin (μ free).toNat) :
    (wantedAt H slot).1∈finiteAIndices n g rs
      (BandRawA.labelAt n g rs (wantedAt H slot).1.val).owner :=
  (finiteAIndices_owner (wantedAt_owner_bounds H slot).1).mpr rfl

/-- Every physical incidence/lift/output satisfying the key equation is an
actual emitted slot. This is the converse needed by the no-hit decision. -/
theorem wantedAt_complete (w : RawReporting.Wanted h J (Fin (items n g rs).length))
    (hk : (M : ℤ) ∣ valueAt n g rs f w.1.val%(P : ℤ)+
      lift w.2.1*(P : ℤ)+shift-globalKey w.2.2) :
    ∃ slot : Fin (μ free).toNat, wantedAt H slot=w := by
  let v := transport (incidenceIndices f n g rs).symm w
  have hv : v∈RawAKeyLists.wanted M P (values f (items n g rs)) h J shift :=
    RawAKeyLists.mem_wanted.mpr hk
  obtain ⟨slot,hs⟩ := List.mem_ofFn.mp (DenseGuardWanted.labels_complete H hv)
  refine ⟨slot,?_⟩
  change transport (incidenceIndices f n g rs) (DenseGuardWanted.labelAt H slot)=w
  rw [hs]
  exact transport_symm _ w

end Actual

end ThreeSum.ReportingHostWantedPhysical
