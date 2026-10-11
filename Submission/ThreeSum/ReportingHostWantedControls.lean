import Submission.ThreeSum.LightReportingWantedDecodeAccess
import Submission.ThreeSum.LightReportingWantedLayout

/-! # Typed contents of the executed wanted access and scratch records -/

namespace ThreeSum.ReportingHostWantedControls

open Light GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostWantedLayout

structure Selection where
  av : ℤ
  owner : ℕ
  bandB : ℕ
  bandC : ℕ
  catalog : ℕ
  srcL : ℕ
  srcR : ℕ
  offsetsL : ℕ
  flatL : ℕ
  offsetsR : ℕ
  flatR : ℕ
  NL : ℕ
  NR : ℕ
  baseL : ℕ
  baseR : ℕ
  occ : ℕ
  maps : ℕ
  candidates : ℕ
  histL : ℕ
  histR : ℕ

def record (S : Selection) : List ℤ :=
  [S.av,S.owner,S.bandB,S.bandC,S.catalog,S.srcL,S.srcR,S.offsetsL,S.flatL,S.offsetsR,S.flatR,
    S.NL,S.NR,S.baseL,S.baseR,S.occ,S.maps,S.candidates,S.histL,S.histR]

@[simp] theorem record_length (S : Selection) : (record S).length=20 := rfl

def ofAccess (f : ℕ→ℤ) (n g : ℕ) (rs : List BandCandidateRows.Record)
    (idx pair bank cover NB NC h J cut occ code srcB srcC report : ℕ) : Selection :=
  let X := LightReportingWantedAccess.selection n g rs idx pair bank cover NB NC h J cut occ code
  ⟨f (BandRawA.labelAt n g rs idx).position,(BandRawA.labelAt n g rs idx).owner,
    (BandRawA.ownerRecord n g rs idx).b,(BandRawA.ownerRecord n g rs idx).c,
    LightReportingWantedAccess.catalog n g rs idx report J NB NC code,
    srcB+X.startL,srcC+X.startR,X.offsetsL,X.flatL,X.offsetsR,X.flatR,X.sizeL,X.sizeR,
    X.stagesL,X.stagesR,ReportingHostSourceSelection.occurrenceRow X code J,
    X.maps,X.candidates,X.histL,X.histR⟩

theorem ofAccess_record (f : ℕ→ℤ) (n g : ℕ) (rs : List BandCandidateRows.Record)
    (idx pair bank cover NB NC h J cut occ code srcB srcC report : ℕ) :
    record (ofAccess f n g rs idx pair bank cover NB NC h J cut occ code srcB srcC report)=
      LightReportingWantedAccess.record f n g rs idx pair bank cover NB NC h J cut occ code srcB srcC report := rfl

def rawRows (layoutHeader J : ℕ) : ℕ := decoded layoutHeader+4+J

def arguments (S : Selection) (L : Layout) (layoutHeader cover counter h J K : ℕ) : List ℤ :=
  [S.av,S.srcL,S.srcR,S.offsetsL,S.flatL,S.offsetsR,S.flatR,S.NL,S.NR,
    BlockSourceEncoding.modulus h J,J,512*h,h,localPrime h,localBucketCap h,
    S.occ,S.maps,S.candidates,S.histL,S.histR,K,L.root,S.catalog,packed layoutHeader J,
    S.baseL,S.baseR,L.masks,L.childL,L.childR,L.counts,L.selected,L.maskBase,L.work,
    0,sourceCut h J,L.terminalMasks,L.masksL,L.masksR,L.base,L.bitBase,L.rowOut,
    rawRows layoutHeader J,cover,counter]

@[simp] theorem arguments_length (S : Selection) (L : Layout) (layoutHeader cover counter h J K : ℕ) :
    (arguments S L layoutHeader cover counter h J K).length=44 := rfl

theorem rawRows_end (layoutHeader J : ℕ) : rawRows layoutHeader J+J=access layoutHeader J := by
  rfl

theorem rawRows_before_packed (layoutHeader J : ℕ) : rawRows layoutHeader J+J≤packed layoutHeader J := by
  rw [rawRows_end]
  exact Nat.le_add_right _ _

theorem packed_end (layoutHeader J : ℕ) : packed layoutHeader J+J=ReportingHostWantedLayout.root layoutHeader J := rfl

end ThreeSum.ReportingHostWantedControls
