/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Lower.MatrixBridge.Data
@[expose] public section
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.MatrixBridge
def literalMomentFData : List (List ℚ) := [
  [(1717 / 100000000), (1717 / 100000000), (1121 / 100000000), (-149 / 25000000), 0, (-1121 / 100000000)],
  [(-1396993 / 25000000), (-1396993 / 25000000), (5193879 / 100000000), (10781851 / 100000000), 0, (-5193879 / 100000000)],
  [(418251 / 20000000), (418251 / 20000000), (-2991 / 125000), (-896811 / 20000000), 0, (2991 / 125000)]
]

def literalMomentJData : List (List ℚ) := [
  [(2033 / 100000000), 0, (691 / 100000000), 0, 0, 0],
  [(-7095051 / 100000000), 0, (1343899 / 20000000), 0, 0, 0],
  [(1371209 / 50000000), 0, (-1531193 / 50000000), 0, 0, 0]
]

def literalMoment (b : Block) (d : Option (Fin 2)) (i : Fin 3 × Fin 2) : ℚ :=
  let data := match b with | .F => literalMomentFData | .J => literalMomentJData
  (data.getD (Computation.optionIndex d).val []).getD (coordinateRank i) 0
@[simp] theorem lookup_moment_F_0_0 : literalMoment .F none (0, 0) = (1717 / 100000000) := rfl
@[simp] theorem lookup_moment_F_0_1 : literalMoment .F none (0, 1) = (1717 / 100000000) := rfl
@[simp] theorem lookup_moment_F_0_2 : literalMoment .F none (1, 0) = (1121 / 100000000) := rfl
@[simp] theorem lookup_moment_F_0_3 : literalMoment .F none (1, 1) = (-149 / 25000000) := rfl
@[simp] theorem lookup_moment_F_0_4 : literalMoment .F none (2, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_0_5 : literalMoment .F none (2, 1) = (-1121 / 100000000) := rfl
@[simp] theorem lookup_moment_F_1_0 : literalMoment .F (some 0) (0, 0) = (-1396993 / 25000000) := rfl
@[simp] theorem lookup_moment_F_1_1 : literalMoment .F (some 0) (0, 1) = (-1396993 / 25000000) := rfl
@[simp] theorem lookup_moment_F_1_2 : literalMoment .F (some 0) (1, 0) = (5193879 / 100000000) := rfl
@[simp] theorem lookup_moment_F_1_3 : literalMoment .F (some 0) (1, 1) = (10781851 / 100000000) := rfl
@[simp] theorem lookup_moment_F_1_4 : literalMoment .F (some 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_1_5 : literalMoment .F (some 0) (2, 1) = (-5193879 / 100000000) := rfl
@[simp] theorem lookup_moment_F_2_0 : literalMoment .F (some 1) (0, 0) = (418251 / 20000000) := rfl
@[simp] theorem lookup_moment_F_2_1 : literalMoment .F (some 1) (0, 1) = (418251 / 20000000) := rfl
@[simp] theorem lookup_moment_F_2_2 : literalMoment .F (some 1) (1, 0) = (-2991 / 125000) := rfl
@[simp] theorem lookup_moment_F_2_3 : literalMoment .F (some 1) (1, 1) = (-896811 / 20000000) := rfl
@[simp] theorem lookup_moment_F_2_4 : literalMoment .F (some 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_2_5 : literalMoment .F (some 1) (2, 1) = (2991 / 125000) := rfl
@[simp] theorem lookup_moment_J_0_0 : literalMoment .J none (0, 0) = (2033 / 100000000) := rfl
@[simp] theorem lookup_moment_J_0_1 : literalMoment .J none (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_0_2 : literalMoment .J none (1, 0) = (691 / 100000000) := rfl
@[simp] theorem lookup_moment_J_0_3 : literalMoment .J none (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_0_4 : literalMoment .J none (2, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_0_5 : literalMoment .J none (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_0 : literalMoment .J (some 0) (0, 0) = (-7095051 / 100000000) := rfl
@[simp] theorem lookup_moment_J_1_1 : literalMoment .J (some 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_2 : literalMoment .J (some 0) (1, 0) = (1343899 / 20000000) := rfl
@[simp] theorem lookup_moment_J_1_3 : literalMoment .J (some 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_4 : literalMoment .J (some 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_1_5 : literalMoment .J (some 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_0 : literalMoment .J (some 1) (0, 0) = (1371209 / 50000000) := rfl
@[simp] theorem lookup_moment_J_2_1 : literalMoment .J (some 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_2 : literalMoment .J (some 1) (1, 0) = (-1531193 / 50000000) := rfl
@[simp] theorem lookup_moment_J_2_3 : literalMoment .J (some 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_4 : literalMoment .J (some 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_2_5 : literalMoment .J (some 1) (2, 1) = 0 := rfl

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.MatrixBridge
