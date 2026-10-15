import Submission.ThreeSum.TernaryColoredLoopSetup
import Submission.ThreeSum.LightTernaryColoredInitializationProof

noncomputable section
namespace ThreeSum.TernaryColoredPreparationFields
open Light TernaryConcreteProfile TernaryColoredLoopSetup LightTernaryColorPreparation
set_option maxHeartbeats 1000000
set_option maxRecDepth 24000
variable {κ : ℕ}

def fields (P : Profile κ) (n free menu : ℕ) (A B C : List ℤ) : List ℕ :=
  let J:=J P n
  let W:=LightColorParametersCosts.width n
  [LightTernaryColorPrelude.av free n,A.length,LightTernaryColorPrelude.bv free n,B.length,
    LightTernaryColorPrelude.cv free n,C.length,bMatrix free n W,cMatrix free n W B.length J,
    oMatrix free n W A.length B.length C.length J,A.length*2^J,
    positions free n W A.length B.length C.length J,carry free n W A.length B.length C.length J,
    work free n W A.length B.length C.length J,
    arenaFree free n W A.length B.length C.length J (n^κ),n^κ,rounds P n,J,q P n,menu]

def field (P : Profile κ) (n free menu : ℕ) (A B C : List ℤ) (i : ℕ) :=
  (fields P n free menu A B C).getD i 0

theorem header_eq (P : Profile κ) (n free menu : ℕ) (A B C : List ℤ) :
    LightTernaryColorPreparationProof.header free n (n^κ) (rounds P n) (J P n) (q P n) menu A B C=
      (fields P n free menu A B C).map (fun i=>(i:ℤ)) := rfl

theorem reads {P : Profile κ} {n free menu : ℕ} {A B C : List ℤ} {μ : ℕ→ℤ}
    (H : Seg μ (headerAt free n (LightColorParametersCosts.width n))
      (LightTernaryColorPreparationProof.header free n (n^κ) (rounds P n) (J P n) (q P n) menu A B C)) :
    ∀i<19,μ (headerAt free n (LightColorParametersCosts.width n)+i)=(field P n free menu A B C i:ℤ) := by
  intro i hi
  have hh:=H.getD (by simpa using hi) 0
  rw [header_eq] at hh
  exact hh.trans (List.getD_map (fields P n free menu A B C) 0 (fun j : ℕ=>(j:ℤ)))

theorem header_before (P : Profile κ) (n free : ℕ) (A B C : List ℤ) :
    headerAt free n (LightColorParametersCosts.width n)+19≤(input P n free A B C).free := by
  change _≤arenaFree free n (LightColorParametersCosts.width n) A.length B.length C.length (J P n) (n^κ)
  unfold arenaFree work oMatrix positions carry cMatrix bMatrix
  omega

theorem runtime_values (P : Profile κ) (n free menu : ℕ) (A B C : List ℤ) :
    LightTernaryColoredInitializationProof.runtimeValues n P.p (4^TernaryLocalParameters.fixedLength P.m) P.F
      (field P n free menu A B C)=
      LightTernaryColoredInitializationProof.values n (n^κ) (input P n free A B C).free
        (arrays P n free menu A B C).Bmatrix B.length (arrays P n free menu A B C).Cmatrix C.length
        (arrays P n free menu A B C).Omatrix (A.length*2^(J P n))
        (arrays P n free menu A B C).positions menu (J P n) P.p (4^TernaryLocalParameters.fixedLength P.m) P.F (q P n) := by
  rfl

end ThreeSum.TernaryColoredPreparationFields
