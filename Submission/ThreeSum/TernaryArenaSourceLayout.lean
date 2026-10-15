import Submission.ThreeSum.TernaryArenaLayout
import Submission.ThreeSum.TernarySourceExecutionFactory

namespace ThreeSum.TernaryArenaSourceLayout
open TernaryArenaLayout TernarySourceExecutionFactory LightTernarySourceHost

def setup (S : Setup) (free C start : ℕ) : Setup :=
  { S with
    base0 := addr free C start
    dst0 := addr free C (start+1)
    base1 := addr free C (start+2)
    dst1 := addr free C (start+3)
    base2 := addr free C (start+4)
    dst2 := addr free C (start+5)
    free := addr free C (start+6)
    keyBase := addr free C (start+7)
    valueBase := addr free C (start+8) }


theorem radix_space_translate (dst m j : ℕ) :
    LightRadixKeys.space dst m j=dst+LightRadixKeys.space 0 m j := by
  unfold LightRadixKeys.space
  omega

theorem join_space_translate (free M NL NR U : ℕ) (input dictionary : ℕ→ℤ) :
    LightWantedSetup.space free M input dictionary NL NR U 0 0=
      free+LightWantedSetup.space 0 M input dictionary NL NR U 0 0 := by
  have hp : LightWantedSetup.pairBase free NL NR M=
      free+LightWantedSetup.pairBase 0 NL NR M := by
    unfold LightWantedSetup.pairBase LightWantedSetup.bucketBase LightWantedSetup.rightCodes
      LightWantedSetup.leftCodes LightSourceBucketSetup.next
    omega
  unfold LightWantedSetup.space LightSourceResidues.space
  rw [hp]
  omega

structure Geometry (S : Setup) (space : ℕ) : Prop where
  base0 : S.base0+S.xs.length≤S.dst0
  next0 : LightRadixKeys.space S.dst0 S.xs.length S.J≤S.base1
  base1 : S.base1+S.xs.length≤S.dst1
  next1 : LightRadixKeys.space S.dst1 S.xs.length S.J≤S.base2
  base2 : S.base2+S.xs.length≤S.dst2
  initEnd : LightRadixKeys.space S.dst2 S.xs.length S.J≤S.free
  keyBase : LightWantedSetup.space S.free S.M S.input (dictionary S.xs S.p0 S.J)
    S.NL (size S.xs S.J) S.U 0 0≤S.keyBase
  keyEnd : S.keyBase+count S.xs S.p0 S.J S.M S.NL S.input≤S.valueBase
  values : S.valueBase+S.groups*S.bank≤space

/-- All three actual Cartesian dictionaries, the actual residue join and
the grouped weighted histogram fit distinct literal arena slots. -/
theorem geometry {free C start space : ℕ} (S : Setup)
    (hs : start=30 ∨ start=39) (hend : finish free C≤space)
    (hlocal : S.xs.length≤C) (hradix : LightRadixKeys.space 0 S.xs.length S.J≤C)
    (hjoin : LightWantedSetup.space 0 S.M S.input (dictionary S.xs S.p0 S.J)
      S.NL (size S.xs S.J) S.U 0 0≤C)
    (hhits : count S.xs S.p0 S.J S.M S.NL S.input≤C)
    (hvalues : S.groups*S.bank≤C) : Geometry (setup S free C start) space := by
  have hlast : start+8<slots := by rcases hs with rfl|rfl <;> decide
  constructor
  · exact before (by omega) hlocal
  · dsimp [setup]
    rw [radix_space_translate]
    exact before (by omega) hradix
  · exact before (by omega) hlocal
  · dsimp [setup]
    rw [radix_space_translate]
    exact before (by omega) hradix
  · exact before (by omega) hlocal
  · dsimp [setup]
    rw [radix_space_translate]
    exact before (by omega) hradix
  · dsimp [setup]
    rw [join_space_translate]
    exact before (by omega) hjoin
  · exact before (by omega) hhits
  · exact region_space hlast hvalues hend

end ThreeSum.TernaryArenaSourceLayout
