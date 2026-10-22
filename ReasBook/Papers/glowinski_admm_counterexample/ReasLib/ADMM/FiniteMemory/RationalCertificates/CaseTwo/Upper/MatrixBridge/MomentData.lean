/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseTwo.Upper.MatrixBridge.Data
@[expose] public section
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseTwo.Upper.MatrixBridge
def literalMomentFData : List (List ℚ) := [
  [(1460443 / 100000000), (1460443 / 100000000), (668329 / 50000000), (-24757 / 20000000), (257641 / 100000000), (-1079017 / 100000000), (118427 / 50000000), (-20787 / 100000000), (127149 / 100000000), (-21941 / 20000000), (107557 / 100000000), (-2449 / 12500000), 0, (-107557 / 100000000)],
  [(-144557 / 3125000), (-144557 / 3125000), (2051439 / 100000000), (6677263 / 100000000), (469719 / 50000000), (-1112001 / 100000000), (214949 / 100000000), (-724489 / 100000000), (146383 / 100000000), (-34283 / 50000000), (106919 / 100000000), (-4933 / 12500000), 0, (-106919 / 100000000)],
  [(1240119 / 50000000), (1240119 / 50000000), (-5783051 / 100000000), (-8263289 / 100000000), (238363 / 100000000), (3010707 / 50000000), (339277 / 25000000), (223749 / 20000000), (14523 / 20000000), (-1284493 / 100000000), (165149 / 100000000), (46267 / 50000000), 0, (-165149 / 100000000)],
  [(231319 / 50000000), (231319 / 50000000), (697063 / 50000000), (29109 / 3125000), (-1346243 / 50000000), (-1021653 / 25000000), (9797 / 20000000), (2741471 / 100000000), (124047 / 50000000), (199109 / 100000000), (4611 / 20000000), (-225039 / 100000000), 0, (-4611 / 20000000)],
  [(11499 / 10000000), (11499 / 10000000), (609677 / 100000000), (494687 / 100000000), (40261 / 20000000), (-102093 / 25000000), (-1356327 / 100000000), (-12169 / 781250), (18991 / 100000000), (687659 / 50000000), (148111 / 100000000), (807 / 625000), 0, (-148111 / 100000000)],
  [(79063 / 50000000), (79063 / 50000000), (356593 / 100000000), (198467 / 100000000), (167921 / 50000000), (-20751 / 100000000), (69447 / 100000000), (-53279 / 20000000), (-552433 / 50000000), (-1174313 / 100000000), (10943 / 100000000), (1115809 / 100000000), 0, (-10943 / 100000000)],
  [(36459 / 100000000), (36459 / 100000000), (30407 / 25000000), (85169 / 100000000), (7321 / 10000000), (-24209 / 50000000), (267 / 200000), (6029 / 10000000), (3289 / 20000000), (-23411 / 20000000), (-449113 / 100000000), (-232779 / 50000000), 0, (449113 / 100000000)]
]

def literalMomentJData : List (List ℚ) := [
  [(435519 / 20000000), 0, (586061 / 50000000), 0, (33697 / 20000000), 0, (3479 / 5000000), 0, (2459 / 6250000), 0, (4929 / 25000000), 0, 0, 0],
  [(-12610581 / 50000000), 0, (5546507 / 25000000), 0, (31903 / 12500000), 0, (91667 / 100000000), 0, (23017 / 50000000), 0, (22901 / 100000000), 0, 0, 0],
  [(686059 / 50000000), 0, (-2445163 / 100000000), 0, (299843 / 100000000), 0, (163 / 160000), 0, (1289 / 2500000), 0, (2383 / 10000000), 0, 0, 0],
  [(668847 / 100000000), 0, (1435357 / 100000000), 0, (-263837 / 10000000), 0, (153361 / 100000000), 0, (51089 / 50000000), 0, (16357 / 50000000), 0, 0, 0],
  [(123919 / 50000000), 0, (464203 / 100000000), 0, (323939 / 50000000), 0, (-859183 / 50000000), 0, (27333 / 20000000), 0, (43409 / 50000000), 0, 0, 0],
  [(147529 / 100000000), 0, (14417 / 6250000), 0, (359011 / 100000000), 0, (2691 / 800000), 0, (-156687 / 12500000), 0, (77509 / 100000000), 0, 0, 0],
  [(112453 / 100000000), 0, (15829 / 12500000), 0, (6607 / 4000000), 0, (44551 / 20000000), 0, (134963 / 100000000), 0, (-840897 / 100000000), 0, 0, 0]
]

def literalMoment (b : Block) (d : Option (Fin 6)) (i : Fin 7 × Fin 2) : ℚ :=
  let data := match b with | .F => literalMomentFData | .J => literalMomentJData
  (data.getD (Computation.optionIndex d).val []).getD (coordinateRank i) 0
@[simp] theorem lookup_moment_F_0_0 : literalMoment .F none (0, 0) = (1460443 / 100000000) := rfl
@[simp] theorem lookup_moment_F_0_1 : literalMoment .F none (0, 1) = (1460443 / 100000000) := rfl
@[simp] theorem lookup_moment_F_0_2 : literalMoment .F none (1, 0) = (668329 / 50000000) := rfl
@[simp] theorem lookup_moment_F_0_3 : literalMoment .F none (1, 1) = (-24757 / 20000000) := rfl
@[simp] theorem lookup_moment_F_0_4 : literalMoment .F none (2, 0) = (257641 / 100000000) := rfl
@[simp] theorem lookup_moment_F_0_5 : literalMoment .F none (2, 1) = (-1079017 / 100000000) := rfl
@[simp] theorem lookup_moment_F_0_6 : literalMoment .F none (3, 0) = (118427 / 50000000) := rfl
@[simp] theorem lookup_moment_F_0_7 : literalMoment .F none (3, 1) = (-20787 / 100000000) := rfl
@[simp] theorem lookup_moment_F_0_8 : literalMoment .F none (4, 0) = (127149 / 100000000) := rfl
@[simp] theorem lookup_moment_F_0_9 : literalMoment .F none (4, 1) = (-21941 / 20000000) := rfl
@[simp] theorem lookup_moment_F_0_10 : literalMoment .F none (5, 0) = (107557 / 100000000) := rfl
@[simp] theorem lookup_moment_F_0_11 : literalMoment .F none (5, 1) = (-2449 / 12500000) := rfl
@[simp] theorem lookup_moment_F_0_12 : literalMoment .F none (6, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_0_13 : literalMoment .F none (6, 1) = (-107557 / 100000000) := rfl
@[simp] theorem lookup_moment_F_1_0 : literalMoment .F (some 0) (0, 0) = (-144557 / 3125000) := rfl
@[simp] theorem lookup_moment_F_1_1 : literalMoment .F (some 0) (0, 1) = (-144557 / 3125000) := rfl
@[simp] theorem lookup_moment_F_1_2 : literalMoment .F (some 0) (1, 0) = (2051439 / 100000000) := rfl
@[simp] theorem lookup_moment_F_1_3 : literalMoment .F (some 0) (1, 1) = (6677263 / 100000000) := rfl
@[simp] theorem lookup_moment_F_1_4 : literalMoment .F (some 0) (2, 0) = (469719 / 50000000) := rfl
@[simp] theorem lookup_moment_F_1_5 : literalMoment .F (some 0) (2, 1) = (-1112001 / 100000000) := rfl
@[simp] theorem lookup_moment_F_1_6 : literalMoment .F (some 0) (3, 0) = (214949 / 100000000) := rfl
@[simp] theorem lookup_moment_F_1_7 : literalMoment .F (some 0) (3, 1) = (-724489 / 100000000) := rfl
@[simp] theorem lookup_moment_F_1_8 : literalMoment .F (some 0) (4, 0) = (146383 / 100000000) := rfl
@[simp] theorem lookup_moment_F_1_9 : literalMoment .F (some 0) (4, 1) = (-34283 / 50000000) := rfl
@[simp] theorem lookup_moment_F_1_10 : literalMoment .F (some 0) (5, 0) = (106919 / 100000000) := rfl
@[simp] theorem lookup_moment_F_1_11 : literalMoment .F (some 0) (5, 1) = (-4933 / 12500000) := rfl
@[simp] theorem lookup_moment_F_1_12 : literalMoment .F (some 0) (6, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_1_13 : literalMoment .F (some 0) (6, 1) = (-106919 / 100000000) := rfl
@[simp] theorem lookup_moment_F_2_0 : literalMoment .F (some 1) (0, 0) = (1240119 / 50000000) := rfl
@[simp] theorem lookup_moment_F_2_1 : literalMoment .F (some 1) (0, 1) = (1240119 / 50000000) := rfl
@[simp] theorem lookup_moment_F_2_2 : literalMoment .F (some 1) (1, 0) = (-5783051 / 100000000) := rfl
@[simp] theorem lookup_moment_F_2_3 : literalMoment .F (some 1) (1, 1) = (-8263289 / 100000000) := rfl
@[simp] theorem lookup_moment_F_2_4 : literalMoment .F (some 1) (2, 0) = (238363 / 100000000) := rfl
@[simp] theorem lookup_moment_F_2_5 : literalMoment .F (some 1) (2, 1) = (3010707 / 50000000) := rfl
@[simp] theorem lookup_moment_F_2_6 : literalMoment .F (some 1) (3, 0) = (339277 / 25000000) := rfl
@[simp] theorem lookup_moment_F_2_7 : literalMoment .F (some 1) (3, 1) = (223749 / 20000000) := rfl
@[simp] theorem lookup_moment_F_2_8 : literalMoment .F (some 1) (4, 0) = (14523 / 20000000) := rfl
@[simp] theorem lookup_moment_F_2_9 : literalMoment .F (some 1) (4, 1) = (-1284493 / 100000000) := rfl
@[simp] theorem lookup_moment_F_2_10 : literalMoment .F (some 1) (5, 0) = (165149 / 100000000) := rfl
@[simp] theorem lookup_moment_F_2_11 : literalMoment .F (some 1) (5, 1) = (46267 / 50000000) := rfl
@[simp] theorem lookup_moment_F_2_12 : literalMoment .F (some 1) (6, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_2_13 : literalMoment .F (some 1) (6, 1) = (-165149 / 100000000) := rfl
@[simp] theorem lookup_moment_F_3_0 : literalMoment .F (some 2) (0, 0) = (231319 / 50000000) := rfl
@[simp] theorem lookup_moment_F_3_1 : literalMoment .F (some 2) (0, 1) = (231319 / 50000000) := rfl
@[simp] theorem lookup_moment_F_3_2 : literalMoment .F (some 2) (1, 0) = (697063 / 50000000) := rfl
@[simp] theorem lookup_moment_F_3_3 : literalMoment .F (some 2) (1, 1) = (29109 / 3125000) := rfl
@[simp] theorem lookup_moment_F_3_4 : literalMoment .F (some 2) (2, 0) = (-1346243 / 50000000) := rfl
@[simp] theorem lookup_moment_F_3_5 : literalMoment .F (some 2) (2, 1) = (-1021653 / 25000000) := rfl
@[simp] theorem lookup_moment_F_3_6 : literalMoment .F (some 2) (3, 0) = (9797 / 20000000) := rfl
@[simp] theorem lookup_moment_F_3_7 : literalMoment .F (some 2) (3, 1) = (2741471 / 100000000) := rfl
@[simp] theorem lookup_moment_F_3_8 : literalMoment .F (some 2) (4, 0) = (124047 / 50000000) := rfl
@[simp] theorem lookup_moment_F_3_9 : literalMoment .F (some 2) (4, 1) = (199109 / 100000000) := rfl
@[simp] theorem lookup_moment_F_3_10 : literalMoment .F (some 2) (5, 0) = (4611 / 20000000) := rfl
@[simp] theorem lookup_moment_F_3_11 : literalMoment .F (some 2) (5, 1) = (-225039 / 100000000) := rfl
@[simp] theorem lookup_moment_F_3_12 : literalMoment .F (some 2) (6, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_3_13 : literalMoment .F (some 2) (6, 1) = (-4611 / 20000000) := rfl
@[simp] theorem lookup_moment_F_4_0 : literalMoment .F (some 3) (0, 0) = (11499 / 10000000) := rfl
@[simp] theorem lookup_moment_F_4_1 : literalMoment .F (some 3) (0, 1) = (11499 / 10000000) := rfl
@[simp] theorem lookup_moment_F_4_2 : literalMoment .F (some 3) (1, 0) = (609677 / 100000000) := rfl
@[simp] theorem lookup_moment_F_4_3 : literalMoment .F (some 3) (1, 1) = (494687 / 100000000) := rfl
@[simp] theorem lookup_moment_F_4_4 : literalMoment .F (some 3) (2, 0) = (40261 / 20000000) := rfl
@[simp] theorem lookup_moment_F_4_5 : literalMoment .F (some 3) (2, 1) = (-102093 / 25000000) := rfl
@[simp] theorem lookup_moment_F_4_6 : literalMoment .F (some 3) (3, 0) = (-1356327 / 100000000) := rfl
@[simp] theorem lookup_moment_F_4_7 : literalMoment .F (some 3) (3, 1) = (-12169 / 781250) := rfl
@[simp] theorem lookup_moment_F_4_8 : literalMoment .F (some 3) (4, 0) = (18991 / 100000000) := rfl
@[simp] theorem lookup_moment_F_4_9 : literalMoment .F (some 3) (4, 1) = (687659 / 50000000) := rfl
@[simp] theorem lookup_moment_F_4_10 : literalMoment .F (some 3) (5, 0) = (148111 / 100000000) := rfl
@[simp] theorem lookup_moment_F_4_11 : literalMoment .F (some 3) (5, 1) = (807 / 625000) := rfl
@[simp] theorem lookup_moment_F_4_12 : literalMoment .F (some 3) (6, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_4_13 : literalMoment .F (some 3) (6, 1) = (-148111 / 100000000) := rfl
@[simp] theorem lookup_moment_F_5_0 : literalMoment .F (some 4) (0, 0) = (79063 / 50000000) := rfl
@[simp] theorem lookup_moment_F_5_1 : literalMoment .F (some 4) (0, 1) = (79063 / 50000000) := rfl
@[simp] theorem lookup_moment_F_5_2 : literalMoment .F (some 4) (1, 0) = (356593 / 100000000) := rfl
@[simp] theorem lookup_moment_F_5_3 : literalMoment .F (some 4) (1, 1) = (198467 / 100000000) := rfl
@[simp] theorem lookup_moment_F_5_4 : literalMoment .F (some 4) (2, 0) = (167921 / 50000000) := rfl
@[simp] theorem lookup_moment_F_5_5 : literalMoment .F (some 4) (2, 1) = (-20751 / 100000000) := rfl
@[simp] theorem lookup_moment_F_5_6 : literalMoment .F (some 4) (3, 0) = (69447 / 100000000) := rfl
@[simp] theorem lookup_moment_F_5_7 : literalMoment .F (some 4) (3, 1) = (-53279 / 20000000) := rfl
@[simp] theorem lookup_moment_F_5_8 : literalMoment .F (some 4) (4, 0) = (-552433 / 50000000) := rfl
@[simp] theorem lookup_moment_F_5_9 : literalMoment .F (some 4) (4, 1) = (-1174313 / 100000000) := rfl
@[simp] theorem lookup_moment_F_5_10 : literalMoment .F (some 4) (5, 0) = (10943 / 100000000) := rfl
@[simp] theorem lookup_moment_F_5_11 : literalMoment .F (some 4) (5, 1) = (1115809 / 100000000) := rfl
@[simp] theorem lookup_moment_F_5_12 : literalMoment .F (some 4) (6, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_5_13 : literalMoment .F (some 4) (6, 1) = (-10943 / 100000000) := rfl
@[simp] theorem lookup_moment_F_6_0 : literalMoment .F (some 5) (0, 0) = (36459 / 100000000) := rfl
@[simp] theorem lookup_moment_F_6_1 : literalMoment .F (some 5) (0, 1) = (36459 / 100000000) := rfl
@[simp] theorem lookup_moment_F_6_2 : literalMoment .F (some 5) (1, 0) = (30407 / 25000000) := rfl
@[simp] theorem lookup_moment_F_6_3 : literalMoment .F (some 5) (1, 1) = (85169 / 100000000) := rfl
@[simp] theorem lookup_moment_F_6_4 : literalMoment .F (some 5) (2, 0) = (7321 / 10000000) := rfl
@[simp] theorem lookup_moment_F_6_5 : literalMoment .F (some 5) (2, 1) = (-24209 / 50000000) := rfl
@[simp] theorem lookup_moment_F_6_6 : literalMoment .F (some 5) (3, 0) = (267 / 200000) := rfl
@[simp] theorem lookup_moment_F_6_7 : literalMoment .F (some 5) (3, 1) = (6029 / 10000000) := rfl
@[simp] theorem lookup_moment_F_6_8 : literalMoment .F (some 5) (4, 0) = (3289 / 20000000) := rfl
@[simp] theorem lookup_moment_F_6_9 : literalMoment .F (some 5) (4, 1) = (-23411 / 20000000) := rfl
@[simp] theorem lookup_moment_F_6_10 : literalMoment .F (some 5) (5, 0) = (-449113 / 100000000) := rfl
@[simp] theorem lookup_moment_F_6_11 : literalMoment .F (some 5) (5, 1) = (-232779 / 50000000) := rfl
@[simp] theorem lookup_moment_F_6_12 : literalMoment .F (some 5) (6, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_6_13 : literalMoment .F (some 5) (6, 1) = (449113 / 100000000) := rfl
@[simp] theorem lookup_moment_J_0_0 : literalMoment .J none (0, 0) = (435519 / 20000000) := rfl
@[simp] theorem lookup_moment_J_0_1 : literalMoment .J none (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_0_2 : literalMoment .J none (1, 0) = (586061 / 50000000) := rfl
@[simp] theorem lookup_moment_J_0_3 : literalMoment .J none (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_0_4 : literalMoment .J none (2, 0) = (33697 / 20000000) := rfl
@[simp] theorem lookup_moment_J_0_5 : literalMoment .J none (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_0_6 : literalMoment .J none (3, 0) = (3479 / 5000000) := rfl
@[simp] theorem lookup_moment_J_0_7 : literalMoment .J none (3, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_0_8 : literalMoment .J none (4, 0) = (2459 / 6250000) := rfl
@[simp] theorem lookup_moment_J_0_9 : literalMoment .J none (4, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_0_10 : literalMoment .J none (5, 0) = (4929 / 25000000) := rfl
@[simp] theorem lookup_moment_J_0_11 : literalMoment .J none (5, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_0_12 : literalMoment .J none (6, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_0_13 : literalMoment .J none (6, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_0 : literalMoment .J (some 0) (0, 0) = (-12610581 / 50000000) := rfl
@[simp] theorem lookup_moment_J_1_1 : literalMoment .J (some 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_2 : literalMoment .J (some 0) (1, 0) = (5546507 / 25000000) := rfl
@[simp] theorem lookup_moment_J_1_3 : literalMoment .J (some 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_4 : literalMoment .J (some 0) (2, 0) = (31903 / 12500000) := rfl
@[simp] theorem lookup_moment_J_1_5 : literalMoment .J (some 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_6 : literalMoment .J (some 0) (3, 0) = (91667 / 100000000) := rfl
@[simp] theorem lookup_moment_J_1_7 : literalMoment .J (some 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_8 : literalMoment .J (some 0) (4, 0) = (23017 / 50000000) := rfl
@[simp] theorem lookup_moment_J_1_9 : literalMoment .J (some 0) (4, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_10 : literalMoment .J (some 0) (5, 0) = (22901 / 100000000) := rfl
@[simp] theorem lookup_moment_J_1_11 : literalMoment .J (some 0) (5, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_12 : literalMoment .J (some 0) (6, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_1_13 : literalMoment .J (some 0) (6, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_0 : literalMoment .J (some 1) (0, 0) = (686059 / 50000000) := rfl
@[simp] theorem lookup_moment_J_2_1 : literalMoment .J (some 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_2 : literalMoment .J (some 1) (1, 0) = (-2445163 / 100000000) := rfl
@[simp] theorem lookup_moment_J_2_3 : literalMoment .J (some 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_4 : literalMoment .J (some 1) (2, 0) = (299843 / 100000000) := rfl
@[simp] theorem lookup_moment_J_2_5 : literalMoment .J (some 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_6 : literalMoment .J (some 1) (3, 0) = (163 / 160000) := rfl
@[simp] theorem lookup_moment_J_2_7 : literalMoment .J (some 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_8 : literalMoment .J (some 1) (4, 0) = (1289 / 2500000) := rfl
@[simp] theorem lookup_moment_J_2_9 : literalMoment .J (some 1) (4, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_10 : literalMoment .J (some 1) (5, 0) = (2383 / 10000000) := rfl
@[simp] theorem lookup_moment_J_2_11 : literalMoment .J (some 1) (5, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_12 : literalMoment .J (some 1) (6, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_2_13 : literalMoment .J (some 1) (6, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_3_0 : literalMoment .J (some 2) (0, 0) = (668847 / 100000000) := rfl
@[simp] theorem lookup_moment_J_3_1 : literalMoment .J (some 2) (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_3_2 : literalMoment .J (some 2) (1, 0) = (1435357 / 100000000) := rfl
@[simp] theorem lookup_moment_J_3_3 : literalMoment .J (some 2) (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_3_4 : literalMoment .J (some 2) (2, 0) = (-263837 / 10000000) := rfl
@[simp] theorem lookup_moment_J_3_5 : literalMoment .J (some 2) (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_3_6 : literalMoment .J (some 2) (3, 0) = (153361 / 100000000) := rfl
@[simp] theorem lookup_moment_J_3_7 : literalMoment .J (some 2) (3, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_3_8 : literalMoment .J (some 2) (4, 0) = (51089 / 50000000) := rfl
@[simp] theorem lookup_moment_J_3_9 : literalMoment .J (some 2) (4, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_3_10 : literalMoment .J (some 2) (5, 0) = (16357 / 50000000) := rfl
@[simp] theorem lookup_moment_J_3_11 : literalMoment .J (some 2) (5, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_3_12 : literalMoment .J (some 2) (6, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_3_13 : literalMoment .J (some 2) (6, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_4_0 : literalMoment .J (some 3) (0, 0) = (123919 / 50000000) := rfl
@[simp] theorem lookup_moment_J_4_1 : literalMoment .J (some 3) (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_4_2 : literalMoment .J (some 3) (1, 0) = (464203 / 100000000) := rfl
@[simp] theorem lookup_moment_J_4_3 : literalMoment .J (some 3) (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_4_4 : literalMoment .J (some 3) (2, 0) = (323939 / 50000000) := rfl
@[simp] theorem lookup_moment_J_4_5 : literalMoment .J (some 3) (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_4_6 : literalMoment .J (some 3) (3, 0) = (-859183 / 50000000) := rfl
@[simp] theorem lookup_moment_J_4_7 : literalMoment .J (some 3) (3, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_4_8 : literalMoment .J (some 3) (4, 0) = (27333 / 20000000) := rfl
@[simp] theorem lookup_moment_J_4_9 : literalMoment .J (some 3) (4, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_4_10 : literalMoment .J (some 3) (5, 0) = (43409 / 50000000) := rfl
@[simp] theorem lookup_moment_J_4_11 : literalMoment .J (some 3) (5, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_4_12 : literalMoment .J (some 3) (6, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_4_13 : literalMoment .J (some 3) (6, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_5_0 : literalMoment .J (some 4) (0, 0) = (147529 / 100000000) := rfl
@[simp] theorem lookup_moment_J_5_1 : literalMoment .J (some 4) (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_5_2 : literalMoment .J (some 4) (1, 0) = (14417 / 6250000) := rfl
@[simp] theorem lookup_moment_J_5_3 : literalMoment .J (some 4) (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_5_4 : literalMoment .J (some 4) (2, 0) = (359011 / 100000000) := rfl
@[simp] theorem lookup_moment_J_5_5 : literalMoment .J (some 4) (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_5_6 : literalMoment .J (some 4) (3, 0) = (2691 / 800000) := rfl
@[simp] theorem lookup_moment_J_5_7 : literalMoment .J (some 4) (3, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_5_8 : literalMoment .J (some 4) (4, 0) = (-156687 / 12500000) := rfl
@[simp] theorem lookup_moment_J_5_9 : literalMoment .J (some 4) (4, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_5_10 : literalMoment .J (some 4) (5, 0) = (77509 / 100000000) := rfl
@[simp] theorem lookup_moment_J_5_11 : literalMoment .J (some 4) (5, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_5_12 : literalMoment .J (some 4) (6, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_5_13 : literalMoment .J (some 4) (6, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_6_0 : literalMoment .J (some 5) (0, 0) = (112453 / 100000000) := rfl
@[simp] theorem lookup_moment_J_6_1 : literalMoment .J (some 5) (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_6_2 : literalMoment .J (some 5) (1, 0) = (15829 / 12500000) := rfl
@[simp] theorem lookup_moment_J_6_3 : literalMoment .J (some 5) (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_6_4 : literalMoment .J (some 5) (2, 0) = (6607 / 4000000) := rfl
@[simp] theorem lookup_moment_J_6_5 : literalMoment .J (some 5) (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_6_6 : literalMoment .J (some 5) (3, 0) = (44551 / 20000000) := rfl
@[simp] theorem lookup_moment_J_6_7 : literalMoment .J (some 5) (3, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_6_8 : literalMoment .J (some 5) (4, 0) = (134963 / 100000000) := rfl
@[simp] theorem lookup_moment_J_6_9 : literalMoment .J (some 5) (4, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_6_10 : literalMoment .J (some 5) (5, 0) = (-840897 / 100000000) := rfl
@[simp] theorem lookup_moment_J_6_11 : literalMoment .J (some 5) (5, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_6_12 : literalMoment .J (some 5) (6, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_6_13 : literalMoment .J (some 5) (6, 1) = 0 := rfl

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseTwo.Upper.MatrixBridge
