import Submission.ThreeSum.TernaryCanonicalTupleCodes

noncomputable section
namespace ThreeSum.TernaryCanonicalNativeCompleteness
open Finset TernaryJointType TernaryLocalParameters TernaryCoverLocal TernaryCoverGoodMaps
open TernaryNativeCoverWitness TernaryExtensionEncoding TernaryFixedDictionaries
open TernaryCanonicalDictionaries LightTernarySourceHost TernaryRepeatedWords
set_option maxHeartbeats 4000000
variable {p m F r : ℕ} [Fact p.Prime]

def outputRecord (occ : Fin r→Fin F) (e : Fin r→ActualEdge m) (i : Fin r) :
    TernaryGoodOutputCatalog.Record m (Fin F) :=
  (occ i,⟨output (e i),TernaryNativeTupleWitness.output_mem_vertices (e i)⟩)

def bankId (occ : Fin r→Fin F) : ℕ :=
  Nat.ofDigits F (List.ofFn fun i => (Fintype.equivFin (Fin F) (occ i)).val)

/-- The actual trimmed dictionary and actual wanted DFS contain a common
bank and pointwise additive pair for every original native hash pair. -/
theorem complete (maps : Fin F→Weight m p) (B τ : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ i, TernaryCoverFrequency.Covers m p B τ (maps i) (a,b))
    (a b : Fin r→ZMod p) :
    ∃ occ : Fin r→Fin F, ∃ e : Fin r→ActualEdge m, ∃ jL jR : ℕ,
      jL<(records (α := fixedAlpha m) false maps B).length^r ∧
      jR<(records (α := fixedAlpha m) true maps B).length^r ∧
      dictionary ((records (α := fixedAlpha m) false maps B).map (native false maps)) p r jL=(coefficientCode a : ℤ) ∧
      dictionary ((records (α := fixedAlpha m) true maps B).map (native true maps)) p r jR=(coefficientCode b : ℤ) ∧
      dictionary ((records (α := fixedAlpha m) false maps B).map wordCode) (4^(fixedLength m)) r jL=
        (TernaryCodeSemantics.address (canonical (fun i => left (e i))) : ℤ) ∧
      dictionary ((records (α := fixedAlpha m) true maps B).map wordCode) (4^(fixedLength m)) r jR=
        (TernaryCodeSemantics.address (canonical (fun i => right (e i))) : ℤ) ∧
      dictionary ((records (α := fixedAlpha m) false maps B).map mapCode) F r jL=(bankId occ : ℤ) ∧
      dictionary ((records (α := fixedAlpha m) true maps B).map mapCode) F r jR=(bankId occ : ℤ) ∧
      (TernaryCodeSemantics.address (canonical (fun i => output (e i))),bankId occ)∈
        TernaryWantedLittleEndian.wantedCodes (p : ℤ)
          (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
          (TernaryGoodOutputCatalog.mapCodes maps τ) r (coefficientCode (a+b) : ℤ)
          (4^(fixedLength m)) F 0 1 0 1 ∧
      TernaryConvolution.Adds (canonical (fun i => left (e i)))
        (canonical (fun i => right (e i))) (canonical (fun i => output (e i))) := by
  classical
  obtain ⟨occ,e,hL,hR,hO,ha,hb,hq⟩ := TernaryNativeTupleWitness.tuple_witness maps B τ hcover a b
  obtain ⟨jL,hjL,hl0,hl1,hl2⟩ := TernaryTupleDictionaryLookup.triple_lookup _ _ _ hL
    (native false maps) wordCode mapCode p (4^(fixedLength m)) F
  obtain ⟨jR,hjR,hr0,hr1,hr2⟩ := TernaryTupleDictionaryLookup.triple_lookup _ _ _ hR
    (native true maps) wordCode mapCode p (4^(fixedLength m)) F
  have hwordL : Radix.positionalHash ((4^(fixedLength m) : ℕ) : ℤ) wordCode
      (List.ofFn fun i => leftRecord (occ i) (e i))=
        (TernaryCodeSemantics.address (canonical (fun i => left (e i))) : ℤ) :=
    TernaryCanonicalTupleCodes.canonical_code (fun s : SourceRecord (fixedLength m) (fixedAlpha m) (Fin F) => s.2.val) _
  have hwordR : Radix.positionalHash ((4^(fixedLength m) : ℕ) : ℤ) wordCode
      (List.ofFn fun i => rightRecord (occ i) (e i))=
        (TernaryCodeSemantics.address (canonical (fun i => right (e i))) : ℤ) :=
    TernaryCanonicalTupleCodes.canonical_code (fun s : SourceRecord (fixedLength m) (fixedAlpha m) (Fin F) => s.2.val) _
  have hmapL : Radix.positionalHash (F : ℤ) mapCode
      (List.ofFn fun i => leftRecord (occ i) (e i))=(bankId occ : ℤ) := by
    unfold TernaryCanonicalDictionaries.mapCode
    simpa only [bankId,List.map_ofFn,Function.comp_def,TernaryCanonicalDictionaries.mapCode,leftRecord,Prod.fst] using
      TernaryCanonicalTupleCodes.digit_cast F
        (fun s : SourceRecord (fixedLength m) (fixedAlpha m) (Fin F) =>
          (Fintype.equivFin (Fin F) s.1).val) (List.ofFn fun i => leftRecord (occ i) (e i))
  have hmapR : Radix.positionalHash (F : ℤ) mapCode
      (List.ofFn fun i => rightRecord (occ i) (e i))=(bankId occ : ℤ) := by
    unfold TernaryCanonicalDictionaries.mapCode
    simpa only [bankId,List.map_ofFn,Function.comp_def,TernaryCanonicalDictionaries.mapCode,rightRecord,Prod.fst] using
      TernaryCanonicalTupleCodes.digit_cast F
        (fun s : SourceRecord (fixedLength m) (fixedAlpha m) (Fin F) =>
          (Fintype.equivFin (Fin F) s.1).val) (List.ofFn fun i => rightRecord (occ i) (e i))
  refine ⟨occ,e,jL,jR,hjL,hjR,hl0.trans ha,hr0.trans hb,hl1.trans hwordL,
    hr1.trans hwordR,hl2.trans hmapL,hr2.trans hmapR,?_,?_⟩
  · change (List.ofFn (outputRecord occ e))∈_ at hO
    change Radix.positionalHash (p : ℤ) (TernaryGoodOutputCatalog.key maps)
      (List.ofFn (outputRecord occ e))=(coefficientCode (a+b) : ℤ) at hq
    have hw := TernaryTupleWantedLookup.wanted_lookup _ _ r hO p ((Fact.out : p.Prime).ne_zero)
      (TernaryGoodOutputCatalog.key maps)
      (fun s => TernaryCodeSemantics.address s.2.val)
      (fun s => (Fintype.equivFin (Fin F) s.1).val)
      (4^(fixedLength m)) F (coefficientCode (a+b) : ℤ) (by rw [hq,sub_self]; exact dvd_zero _)
    have hwcode : Nat.ofDigits (4^(fixedLength m))
        ((List.ofFn (outputRecord occ e)).map fun s => TernaryCodeSemantics.address s.2.val)=
        TernaryCodeSemantics.address (canonical (fun i => output (e i))) := by
      apply Int.ofNat_inj.mp
      rw [← TernaryCanonicalTupleCodes.digit_cast]
      exact TernaryCanonicalTupleCodes.canonical_code (fun s : TernaryGoodOutputCatalog.Record m (Fin F) => s.2.val) _
    have hgcode : Nat.ofDigits F
        ((List.ofFn (outputRecord occ e)).map fun s => (Fintype.equivFin (Fin F) s.1).val)=bankId occ := by
      simp only [List.map_ofFn,Function.comp_def,outputRecord,bankId,Prod.fst]
    simpa only [TernaryGoodOutputCatalog.raws,TernaryGoodOutputCatalog.wordCodes,
      TernaryGoodOutputCatalog.mapCodes,hwcode,hgcode] using hw
  · exact canonical_adds _ _ _ (fun i => (edge_data (e i)).2.2.2)

end ThreeSum.TernaryCanonicalNativeCompleteness
