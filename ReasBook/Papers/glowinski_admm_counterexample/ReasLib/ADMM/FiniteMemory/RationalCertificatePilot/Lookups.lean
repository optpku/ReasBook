/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.Data

@[expose] public section

set_option maxRecDepth 4096
set_option linter.style.longLine false

namespace ADMM.FiniteMemory.Reconstruction.Pilot

-- Each lookup is a definitional equality to an exact candidate literal.
@[simp] theorem lookupK0_0 : candidateK (0, 0) (0, 0) = (1669415457 / 10000000000) := rfl
@[simp] theorem lookupK0_1 : candidateK (0, 0) (0, 1) = (-843470451 / 10000000000) := rfl
@[simp] theorem lookupK0_2 : candidateK (0, 0) (1, 0) = (-2057001257 / 20000000000) := rfl
@[simp] theorem lookupK0_3 : candidateK (0, 0) (1, 1) = (-47354649157 / 4000000000000) := rfl
@[simp] theorem lookupK0_4 : candidateK (0, 0) (2, 0) = (-519673661 / 5000000000) := rfl
@[simp] theorem lookupK0_5 : candidateK (0, 0) (2, 1) = (192086114803 / 2000000000000) := rfl
@[simp] theorem lookupK0_6 : candidateK (0, 0) (3, 0) = (811649597 / 20000000000) := rfl
@[simp] theorem lookupK0_7 : candidateK (0, 0) (3, 1) = (2554388897 / 400000000000) := rfl
@[simp] theorem lookupK0_8 : candidateK (0, 0) (4, 0) = (9512821 / 10000000000) := rfl
@[simp] theorem lookupK0_9 : candidateK (0, 0) (4, 1) = (-53155589301 / 4000000000000) := rfl
@[simp] theorem lookupK0_10 : candidateK (0, 0) (5, 0) = (-18717269 / 20000000000) := rfl
@[simp] theorem lookupK0_11 : candidateK (0, 0) (5, 1) = (6502650513 / 2000000000000) := rfl
@[simp] theorem lookupK0_12 : candidateK (0, 0) (6, 0) = (41715639 / 20000000000) := rfl
@[simp] theorem lookupK0_13 : candidateK (0, 0) (6, 1) = (-1198090091 / 800000000000) := rfl
@[simp] theorem lookupK0_14 : candidateK (0, 0) (7, 0) = (482671 / 800000000) := rfl
@[simp] theorem lookupK0_15 : candidateK (0, 0) (7, 1) = (11115808131 / 4000000000000) := rfl
@[simp] theorem lookupK0_16 : candidateK (0, 0) (8, 0) = (-4270669 / 2500000000) := rfl
@[simp] theorem lookupK0_17 : candidateK (0, 0) (8, 1) = (1893004561 / 4000000000000) := rfl
@[simp] theorem lookupK1_0 : candidateK (0, 1) (0, 0) = (-843470451 / 10000000000) := rfl
@[simp] theorem lookupK1_1 : candidateK (0, 1) (0, 1) = (67264413373 / 400000000000) := rfl
@[simp] theorem lookupK1_2 : candidateK (0, 1) (1, 0) = (12786006993 / 800000000000) := rfl
@[simp] theorem lookupK1_3 : candidateK (0, 1) (1, 1) = (-124305767617 / 4000000000000) := rfl
@[simp] theorem lookupK1_4 : candidateK (0, 1) (2, 0) = (94349967 / 4000000000) := rfl
@[simp] theorem lookupK1_5 : candidateK (0, 1) (2, 1) = (-239633139343 / 2000000000000) := rfl
@[simp] theorem lookupK1_6 : candidateK (0, 1) (3, 0) = (33717908887 / 800000000000) := rfl
@[simp] theorem lookupK1_7 : candidateK (0, 1) (3, 1) = (1303068801 / 400000000000) := rfl
@[simp] theorem lookupK1_8 : candidateK (0, 1) (4, 0) = (4287699 / 5000000000) := rfl
@[simp] theorem lookupK1_9 : candidateK (0, 1) (4, 1) = (-29721338739 / 2000000000000) := rfl
@[simp] theorem lookupK1_10 : candidateK (0, 1) (5, 0) = (-16778999 / 20000000000) := rfl
@[simp] theorem lookupK1_11 : candidateK (0, 1) (5, 1) = (13062729269 / 4000000000000) := rfl
@[simp] theorem lookupK1_12 : candidateK (0, 1) (6, 0) = (1228449 / 10000000000) := rfl
@[simp] theorem lookupK1_13 : candidateK (0, 1) (6, 1) = (-4690898521 / 2000000000000) := rfl
@[simp] theorem lookupK1_14 : candidateK (0, 1) (7, 0) = (18025339 / 20000000000) := rfl
@[simp] theorem lookupK1_15 : candidateK (0, 1) (7, 1) = (542995409 / 4000000000000) := rfl
@[simp] theorem lookupK1_16 : candidateK (0, 1) (8, 0) = (-5790263 / 10000000000) := rfl
@[simp] theorem lookupK1_17 : candidateK (0, 1) (8, 1) = (-688336753 / 400000000000) := rfl
@[simp] theorem lookupK2_0 : candidateK (1, 0) (0, 0) = (-2057001257 / 20000000000) := rfl
@[simp] theorem lookupK2_1 : candidateK (1, 0) (0, 1) = (12786006993 / 800000000000) := rfl
@[simp] theorem lookupK2_2 : candidateK (1, 0) (1, 0) = (93541343 / 500000000) := rfl
@[simp] theorem lookupK2_3 : candidateK (1, 0) (1, 1) = (8606045511 / 800000000000) := rfl
@[simp] theorem lookupK2_4 : candidateK (1, 0) (2, 0) = (-673677083 / 20000000000) := rfl
@[simp] theorem lookupK2_5 : candidateK (1, 0) (2, 1) = (-201914459159 / 4000000000000) := rfl
@[simp] theorem lookupK2_6 : candidateK (1, 0) (3, 0) = (-933563947 / 10000000000) := rfl
@[simp] theorem lookupK2_7 : candidateK (1, 0) (3, 1) = (22727345899 / 800000000000) := rfl
@[simp] theorem lookupK2_8 : candidateK (1, 0) (4, 0) = (773759821 / 20000000000) := rfl
@[simp] theorem lookupK2_9 : candidateK (1, 0) (4, 1) = (41003446569 / 4000000000000) := rfl
@[simp] theorem lookupK2_10 : candidateK (1, 0) (5, 0) = (85533743 / 20000000000) := rfl
@[simp] theorem lookupK2_11 : candidateK (1, 0) (5, 1) = (-70587638823 / 4000000000000) := rfl
@[simp] theorem lookupK2_12 : candidateK (1, 0) (6, 0) = (-44505719 / 20000000000) := rfl
@[simp] theorem lookupK2_13 : candidateK (1, 0) (6, 1) = (13369556457 / 4000000000000) := rfl
@[simp] theorem lookupK2_14 : candidateK (1, 0) (7, 0) = (10727489 / 4000000000) := rfl
@[simp] theorem lookupK2_15 : candidateK (1, 0) (7, 1) = (-6650039257 / 4000000000000) := rfl
@[simp] theorem lookupK2_16 : candidateK (1, 0) (8, 0) = (8219 / 2000000000) := rfl
@[simp] theorem lookupK2_17 : candidateK (1, 0) (8, 1) = (100356581 / 80000000000) := rfl
@[simp] theorem lookupK3_0 : candidateK (1, 1) (0, 0) = (-47354649157 / 4000000000000) := rfl
@[simp] theorem lookupK3_1 : candidateK (1, 1) (0, 1) = (-124305767617 / 4000000000000) := rfl
@[simp] theorem lookupK3_2 : candidateK (1, 1) (1, 0) = (8606045511 / 800000000000) := rfl
@[simp] theorem lookupK3_3 : candidateK (1, 1) (1, 1) = (157590631757 / 4000000000000) := rfl
@[simp] theorem lookupK3_4 : candidateK (1, 1) (2, 0) = (542121283 / 160000000000) := rfl
@[simp] theorem lookupK3_5 : candidateK (1, 1) (2, 1) = (1534265739 / 4000000000000) := rfl
@[simp] theorem lookupK3_6 : candidateK (1, 1) (3, 0) = (-24959625047 / 1000000000000) := rfl
@[simp] theorem lookupK3_7 : candidateK (1, 1) (3, 1) = (-58674465371 / 4000000000000) := rfl
@[simp] theorem lookupK3_8 : candidateK (1, 1) (4, 0) = (48402200919 / 2000000000000) := rfl
@[simp] theorem lookupK3_9 : candidateK (1, 1) (4, 1) = (13411481833 / 2000000000000) := rfl
@[simp] theorem lookupK3_10 : candidateK (1, 1) (5, 0) = (799708629 / 500000000000) := rfl
@[simp] theorem lookupK3_11 : candidateK (1, 1) (5, 1) = (-9838069681 / 2000000000000) := rfl
@[simp] theorem lookupK3_12 : candidateK (1, 1) (6, 0) = (-14697350149 / 4000000000000) := rfl
@[simp] theorem lookupK3_13 : candidateK (1, 1) (6, 1) = (8256851437 / 2000000000000) := rfl
@[simp] theorem lookupK3_14 : candidateK (1, 1) (7, 0) = (-55869139 / 200000000000) := rfl
@[simp] theorem lookupK3_15 : candidateK (1, 1) (7, 1) = (-312490441 / 400000000000) := rfl
@[simp] theorem lookupK3_16 : candidateK (1, 1) (8, 0) = (1184173 / 10000000000) := rfl
@[simp] theorem lookupK3_17 : candidateK (1, 1) (8, 1) = (87710189 / 2000000000000) := rfl
@[simp] theorem lookupK4_0 : candidateK (2, 0) (0, 0) = (-519673661 / 5000000000) := rfl
@[simp] theorem lookupK4_1 : candidateK (2, 0) (0, 1) = (94349967 / 4000000000) := rfl
@[simp] theorem lookupK4_2 : candidateK (2, 0) (1, 0) = (-673677083 / 20000000000) := rfl
@[simp] theorem lookupK4_3 : candidateK (2, 0) (1, 1) = (542121283 / 160000000000) := rfl
@[simp] theorem lookupK4_4 : candidateK (2, 0) (2, 0) = (1215980783 / 5000000000) := rfl
@[simp] theorem lookupK4_5 : candidateK (2, 0) (2, 1) = (-56569022569 / 4000000000000) := rfl
@[simp] theorem lookupK4_6 : candidateK (2, 0) (3, 0) = (-146443779 / 2500000000) := rfl
@[simp] theorem lookupK4_7 : candidateK (2, 0) (3, 1) = (-40064802991 / 1000000000000) := rfl
@[simp] theorem lookupK4_8 : candidateK (2, 0) (4, 0) = (-165279291 / 2000000000) := rfl
@[simp] theorem lookupK4_9 : candidateK (2, 0) (4, 1) = (137195975781 / 4000000000000) := rfl
@[simp] theorem lookupK4_10 : candidateK (2, 0) (5, 0) = (615627863 / 20000000000) := rfl
@[simp] theorem lookupK4_11 : candidateK (2, 0) (5, 1) = (625971843 / 125000000000) := rfl
@[simp] theorem lookupK4_12 : candidateK (2, 0) (6, 0) = (139188991 / 20000000000) := rfl
@[simp] theorem lookupK4_13 : candidateK (2, 0) (6, 1) = (-51890657491 / 4000000000000) := rfl
@[simp] theorem lookupK4_14 : candidateK (2, 0) (7, 0) = (-6605617 / 800000000) := rfl
@[simp] theorem lookupK4_15 : candidateK (2, 0) (7, 1) = (3522292603 / 4000000000000) := rfl
@[simp] theorem lookupK4_16 : candidateK (2, 0) (8, 0) = (12583783 / 2500000000) := rfl
@[simp] theorem lookupK4_17 : candidateK (2, 0) (8, 1) = (1105772187 / 2000000000000) := rfl
@[simp] theorem lookupK5_0 : candidateK (2, 1) (0, 0) = (192086114803 / 2000000000000) := rfl
@[simp] theorem lookupK5_1 : candidateK (2, 1) (0, 1) = (-239633139343 / 2000000000000) := rfl
@[simp] theorem lookupK5_2 : candidateK (2, 1) (1, 0) = (-201914459159 / 4000000000000) := rfl
@[simp] theorem lookupK5_3 : candidateK (2, 1) (1, 1) = (1534265739 / 4000000000000) := rfl
@[simp] theorem lookupK5_4 : candidateK (2, 1) (2, 0) = (-56569022569 / 4000000000000) := rfl
@[simp] theorem lookupK5_5 : candidateK (2, 1) (2, 1) = (118770154839 / 1000000000000) := rfl
@[simp] theorem lookupK5_6 : candidateK (2, 1) (3, 0) = (-26054417809 / 1000000000000) := rfl
@[simp] theorem lookupK5_7 : candidateK (2, 1) (3, 1) = (-2392287511 / 400000000000) := rfl
@[simp] theorem lookupK5_8 : candidateK (2, 1) (4, 0) = (-84081303 / 3906250000) := rfl
@[simp] theorem lookupK5_9 : candidateK (2, 1) (4, 1) = (9077629327 / 4000000000000) := rfl
@[simp] theorem lookupK5_10 : candidateK (2, 1) (5, 0) = (37320238441 / 2000000000000) := rfl
@[simp] theorem lookupK5_11 : candidateK (2, 1) (5, 1) = (3834106381 / 4000000000000) := rfl
@[simp] theorem lookupK5_12 : candidateK (2, 1) (6, 0) = (9439735649 / 4000000000000) := rfl
@[simp] theorem lookupK5_13 : candidateK (2, 1) (6, 1) = (-7516651173 / 4000000000000) := rfl
@[simp] theorem lookupK5_14 : candidateK (2, 1) (7, 0) = (-520577669 / 160000000000) := rfl
@[simp] theorem lookupK5_15 : candidateK (2, 1) (7, 1) = (11525119097 / 4000000000000) := rfl
@[simp] theorem lookupK5_16 : candidateK (2, 1) (8, 0) = (-335477 / 10000000000) := rfl
@[simp] theorem lookupK5_17 : candidateK (2, 1) (8, 1) = (-99581409 / 500000000000) := rfl
@[simp] theorem lookupK6_0 : candidateK (3, 0) (0, 0) = (811649597 / 20000000000) := rfl
@[simp] theorem lookupK6_1 : candidateK (3, 0) (0, 1) = (33717908887 / 800000000000) := rfl
@[simp] theorem lookupK6_2 : candidateK (3, 0) (1, 0) = (-933563947 / 10000000000) := rfl
@[simp] theorem lookupK6_3 : candidateK (3, 0) (1, 1) = (-24959625047 / 1000000000000) := rfl
@[simp] theorem lookupK6_4 : candidateK (3, 0) (2, 0) = (-146443779 / 2500000000) := rfl
@[simp] theorem lookupK6_5 : candidateK (3, 0) (2, 1) = (-26054417809 / 1000000000000) := rfl
@[simp] theorem lookupK6_6 : candidateK (3, 0) (3, 0) = (62882581 / 312500000) := rfl
@[simp] theorem lookupK6_7 : candidateK (3, 0) (3, 1) = (18827307679 / 1000000000000) := rfl
@[simp] theorem lookupK6_8 : candidateK (3, 0) (4, 0) = (-974830419 / 20000000000) := rfl
@[simp] theorem lookupK6_9 : candidateK (3, 0) (4, 1) = (-138637792033 / 4000000000000) := rfl
@[simp] theorem lookupK6_10 : candidateK (3, 0) (5, 0) = (-171372033 / 2500000000) := rfl
@[simp] theorem lookupK6_11 : candidateK (3, 0) (5, 1) = (63957883581 / 2000000000000) := rfl
@[simp] theorem lookupK6_12 : candidateK (3, 0) (6, 0) = (42998401 / 2000000000) := rfl
@[simp] theorem lookupK6_13 : candidateK (3, 0) (6, 1) = (1749048443 / 4000000000000) := rfl
@[simp] theorem lookupK6_14 : candidateK (3, 0) (7, 0) = (8023441 / 800000000) := rfl
@[simp] theorem lookupK6_15 : candidateK (3, 0) (7, 1) = (-38670186217 / 4000000000000) := rfl
@[simp] theorem lookupK6_16 : candidateK (3, 0) (8, 0) = (-5578073 / 1250000000) := rfl
@[simp] theorem lookupK6_17 : candidateK (3, 0) (8, 1) = (9900457589 / 4000000000000) := rfl
@[simp] theorem lookupK7_0 : candidateK (3, 1) (0, 0) = (2554388897 / 400000000000) := rfl
@[simp] theorem lookupK7_1 : candidateK (3, 1) (0, 1) = (1303068801 / 400000000000) := rfl
@[simp] theorem lookupK7_2 : candidateK (3, 1) (1, 0) = (22727345899 / 800000000000) := rfl
@[simp] theorem lookupK7_3 : candidateK (3, 1) (1, 1) = (-58674465371 / 4000000000000) := rfl
@[simp] theorem lookupK7_4 : candidateK (3, 1) (2, 0) = (-40064802991 / 1000000000000) := rfl
@[simp] theorem lookupK7_5 : candidateK (3, 1) (2, 1) = (-2392287511 / 400000000000) := rfl
@[simp] theorem lookupK7_6 : candidateK (3, 1) (3, 0) = (18827307679 / 1000000000000) := rfl
@[simp] theorem lookupK7_7 : candidateK (3, 1) (3, 1) = (2656055333 / 100000000000) := rfl
@[simp] theorem lookupK7_8 : candidateK (3, 1) (4, 0) = (-59411881 / 6250000000) := rfl
@[simp] theorem lookupK7_9 : candidateK (3, 1) (4, 1) = (-27811732409 / 4000000000000) := rfl
@[simp] theorem lookupK7_10 : candidateK (3, 1) (5, 0) = (-72372260661 / 4000000000000) := rfl
@[simp] theorem lookupK7_11 : candidateK (3, 1) (5, 1) = (-8911605481 / 4000000000000) := rfl
@[simp] theorem lookupK7_12 : candidateK (3, 1) (6, 0) = (49557570173 / 4000000000000) := rfl
@[simp] theorem lookupK7_13 : candidateK (3, 1) (6, 1) = (101495617 / 500000000000) := rfl
@[simp] theorem lookupK7_14 : candidateK (3, 1) (7, 0) = (9709414043 / 2000000000000) := rfl
@[simp] theorem lookupK7_15 : candidateK (3, 1) (7, 1) = (-117311799 / 62500000000) := rfl
@[simp] theorem lookupK7_16 : candidateK (3, 1) (8, 0) = (-5000353 / 2000000000) := rfl
@[simp] theorem lookupK7_17 : candidateK (3, 1) (8, 1) = (5778801811 / 4000000000000) := rfl
@[simp] theorem lookupK8_0 : candidateK (4, 0) (0, 0) = (9512821 / 10000000000) := rfl
@[simp] theorem lookupK8_1 : candidateK (4, 0) (0, 1) = (4287699 / 5000000000) := rfl
@[simp] theorem lookupK8_2 : candidateK (4, 0) (1, 0) = (773759821 / 20000000000) := rfl
@[simp] theorem lookupK8_3 : candidateK (4, 0) (1, 1) = (48402200919 / 2000000000000) := rfl
@[simp] theorem lookupK8_4 : candidateK (4, 0) (2, 0) = (-165279291 / 2000000000) := rfl
@[simp] theorem lookupK8_5 : candidateK (4, 0) (2, 1) = (-84081303 / 3906250000) := rfl
@[simp] theorem lookupK8_6 : candidateK (4, 0) (3, 0) = (-974830419 / 20000000000) := rfl
@[simp] theorem lookupK8_7 : candidateK (4, 0) (3, 1) = (-59411881 / 6250000000) := rfl
@[simp] theorem lookupK8_8 : candidateK (4, 0) (4, 0) = (385964893 / 2500000000) := rfl
@[simp] theorem lookupK8_9 : candidateK (4, 0) (4, 1) = (8145416637 / 800000000000) := rfl
@[simp] theorem lookupK8_10 : candidateK (4, 0) (5, 0) = (-525167829 / 20000000000) := rfl
@[simp] theorem lookupK8_11 : candidateK (4, 0) (5, 1) = (-404262093 / 16000000000) := rfl
@[simp] theorem lookupK8_12 : candidateK (4, 0) (6, 0) = (-174518717 / 4000000000) := rfl
@[simp] theorem lookupK8_13 : candidateK (4, 0) (6, 1) = (105328519603 / 4000000000000) := rfl
@[simp] theorem lookupK8_14 : candidateK (4, 0) (7, 0) = (15310593 / 20000000000) := rfl
@[simp] theorem lookupK8_15 : candidateK (4, 0) (7, 1) = (-696455297 / 4000000000000) := rfl
@[simp] theorem lookupK8_16 : candidateK (4, 0) (8, 0) = (62208091 / 10000000000) := rfl
@[simp] theorem lookupK8_17 : candidateK (4, 0) (8, 1) = (-19728927339 / 4000000000000) := rfl
@[simp] theorem lookupK9_0 : candidateK (4, 1) (0, 0) = (-53155589301 / 4000000000000) := rfl
@[simp] theorem lookupK9_1 : candidateK (4, 1) (0, 1) = (-29721338739 / 2000000000000) := rfl
@[simp] theorem lookupK9_2 : candidateK (4, 1) (1, 0) = (41003446569 / 4000000000000) := rfl
@[simp] theorem lookupK9_3 : candidateK (4, 1) (1, 1) = (13411481833 / 2000000000000) := rfl
@[simp] theorem lookupK9_4 : candidateK (4, 1) (2, 0) = (137195975781 / 4000000000000) := rfl
@[simp] theorem lookupK9_5 : candidateK (4, 1) (2, 1) = (9077629327 / 4000000000000) := rfl
@[simp] theorem lookupK9_6 : candidateK (4, 1) (3, 0) = (-138637792033 / 4000000000000) := rfl
@[simp] theorem lookupK9_7 : candidateK (4, 1) (3, 1) = (-27811732409 / 4000000000000) := rfl
@[simp] theorem lookupK9_8 : candidateK (4, 1) (4, 0) = (8145416637 / 800000000000) := rfl
@[simp] theorem lookupK9_9 : candidateK (4, 1) (4, 1) = (19362037253 / 1000000000000) := rfl
@[simp] theorem lookupK9_10 : candidateK (4, 1) (5, 0) = (-12234842163 / 4000000000000) := rfl
@[simp] theorem lookupK9_11 : candidateK (4, 1) (5, 1) = (-22133370409 / 4000000000000) := rfl
@[simp] theorem lookupK9_12 : candidateK (4, 1) (6, 0) = (-9032394429 / 1000000000000) := rfl
@[simp] theorem lookupK9_13 : candidateK (4, 1) (6, 1) = (-805454719 / 500000000000) := rfl
@[simp] theorem lookupK9_14 : candidateK (4, 1) (7, 0) = (3270282293 / 2000000000000) := rfl
@[simp] theorem lookupK9_15 : candidateK (4, 1) (7, 1) = (-659803219 / 4000000000000) := rfl
@[simp] theorem lookupK9_16 : candidateK (4, 1) (8, 0) = (40064829 / 10000000000) := rfl
@[simp] theorem lookupK9_17 : candidateK (4, 1) (8, 1) = (63126453 / 250000000000) := rfl
@[simp] theorem lookupK10_0 : candidateK (5, 0) (0, 0) = (-18717269 / 20000000000) := rfl
@[simp] theorem lookupK10_1 : candidateK (5, 0) (0, 1) = (-16778999 / 20000000000) := rfl
@[simp] theorem lookupK10_2 : candidateK (5, 0) (1, 0) = (85533743 / 20000000000) := rfl
@[simp] theorem lookupK10_3 : candidateK (5, 0) (1, 1) = (799708629 / 500000000000) := rfl
@[simp] theorem lookupK10_4 : candidateK (5, 0) (2, 0) = (615627863 / 20000000000) := rfl
@[simp] theorem lookupK10_5 : candidateK (5, 0) (2, 1) = (37320238441 / 2000000000000) := rfl
@[simp] theorem lookupK10_6 : candidateK (5, 0) (3, 0) = (-171372033 / 2500000000) := rfl
@[simp] theorem lookupK10_7 : candidateK (5, 0) (3, 1) = (-72372260661 / 4000000000000) := rfl
@[simp] theorem lookupK10_8 : candidateK (5, 0) (4, 0) = (-525167829 / 20000000000) := rfl
@[simp] theorem lookupK10_9 : candidateK (5, 0) (4, 1) = (-12234842163 / 4000000000000) := rfl
@[simp] theorem lookupK10_10 : candidateK (5, 0) (5, 0) = (504765271 / 5000000000) := rfl
@[simp] theorem lookupK10_11 : candidateK (5, 0) (5, 1) = (19097860611 / 4000000000000) := rfl
@[simp] theorem lookupK10_12 : candidateK (5, 0) (6, 0) = (-22810053 / 800000000) := rfl
@[simp] theorem lookupK10_13 : candidateK (5, 0) (6, 1) = (-17427268667 / 1000000000000) := rfl
@[simp] theorem lookupK10_14 : candidateK (5, 0) (7, 0) = (-193497917 / 20000000000) := rfl
@[simp] theorem lookupK10_15 : candidateK (5, 0) (7, 1) = (19661884631 / 1000000000000) := rfl
@[simp] theorem lookupK10_16 : candidateK (5, 0) (8, 0) = (-45510449 / 20000000000) := rfl
@[simp] theorem lookupK10_17 : candidateK (5, 0) (8, 1) = (-20382372849 / 4000000000000) := rfl
@[simp] theorem lookupK11_0 : candidateK (5, 1) (0, 0) = (6502650513 / 2000000000000) := rfl
@[simp] theorem lookupK11_1 : candidateK (5, 1) (0, 1) = (13062729269 / 4000000000000) := rfl
@[simp] theorem lookupK11_2 : candidateK (5, 1) (1, 0) = (-70587638823 / 4000000000000) := rfl
@[simp] theorem lookupK11_3 : candidateK (5, 1) (1, 1) = (-9838069681 / 2000000000000) := rfl
@[simp] theorem lookupK11_4 : candidateK (5, 1) (2, 0) = (625971843 / 125000000000) := rfl
@[simp] theorem lookupK11_5 : candidateK (5, 1) (2, 1) = (3834106381 / 4000000000000) := rfl
@[simp] theorem lookupK11_6 : candidateK (5, 1) (3, 0) = (63957883581 / 2000000000000) := rfl
@[simp] theorem lookupK11_7 : candidateK (5, 1) (3, 1) = (-8911605481 / 4000000000000) := rfl
@[simp] theorem lookupK11_8 : candidateK (5, 1) (4, 0) = (-404262093 / 16000000000) := rfl
@[simp] theorem lookupK11_9 : candidateK (5, 1) (4, 1) = (-22133370409 / 4000000000000) := rfl
@[simp] theorem lookupK11_10 : candidateK (5, 1) (5, 0) = (19097860611 / 4000000000000) := rfl
@[simp] theorem lookupK11_11 : candidateK (5, 1) (5, 1) = (13751713543 / 1000000000000) := rfl
@[simp] theorem lookupK11_12 : candidateK (5, 1) (6, 0) = (-5394333897 / 4000000000000) := rfl
@[simp] theorem lookupK11_13 : candidateK (5, 1) (6, 1) = (-21419143289 / 4000000000000) := rfl
@[simp] theorem lookupK11_14 : candidateK (5, 1) (7, 0) = (-1930323143 / 1000000000000) := rfl
@[simp] theorem lookupK11_15 : candidateK (5, 1) (7, 1) = (-3590761601 / 4000000000000) := rfl
@[simp] theorem lookupK11_16 : candidateK (5, 1) (8, 0) = (24262451 / 20000000000) := rfl
@[simp] theorem lookupK11_17 : candidateK (5, 1) (8, 1) = (727257491 / 800000000000) := rfl
@[simp] theorem lookupK12_0 : candidateK (6, 0) (0, 0) = (41715639 / 20000000000) := rfl
@[simp] theorem lookupK12_1 : candidateK (6, 0) (0, 1) = (1228449 / 10000000000) := rfl
@[simp] theorem lookupK12_2 : candidateK (6, 0) (1, 0) = (-44505719 / 20000000000) := rfl
@[simp] theorem lookupK12_3 : candidateK (6, 0) (1, 1) = (-14697350149 / 4000000000000) := rfl
@[simp] theorem lookupK12_4 : candidateK (6, 0) (2, 0) = (139188991 / 20000000000) := rfl
@[simp] theorem lookupK12_5 : candidateK (6, 0) (2, 1) = (9439735649 / 4000000000000) := rfl
@[simp] theorem lookupK12_6 : candidateK (6, 0) (3, 0) = (42998401 / 2000000000) := rfl
@[simp] theorem lookupK12_7 : candidateK (6, 0) (3, 1) = (49557570173 / 4000000000000) := rfl
@[simp] theorem lookupK12_8 : candidateK (6, 0) (4, 0) = (-174518717 / 4000000000) := rfl
@[simp] theorem lookupK12_9 : candidateK (6, 0) (4, 1) = (-9032394429 / 1000000000000) := rfl
@[simp] theorem lookupK12_10 : candidateK (6, 0) (5, 0) = (-22810053 / 800000000) := rfl
@[simp] theorem lookupK12_11 : candidateK (6, 0) (5, 1) = (-5394333897 / 4000000000000) := rfl
@[simp] theorem lookupK12_12 : candidateK (6, 0) (6, 0) = (4456457 / 78125000) := rfl
@[simp] theorem lookupK12_13 : candidateK (6, 0) (6, 1) = (3892998059 / 800000000000) := rfl
@[simp] theorem lookupK12_14 : candidateK (6, 0) (7, 0) = (-50539531 / 10000000000) := rfl
@[simp] theorem lookupK12_15 : candidateK (6, 0) (7, 1) = (-12176429087 / 1000000000000) := rfl
@[simp] theorem lookupK12_16 : candidateK (6, 0) (8, 0) = (-163843833 / 20000000000) := rfl
@[simp] theorem lookupK12_17 : candidateK (6, 0) (8, 1) = (26623488657 / 4000000000000) := rfl
@[simp] theorem lookupK13_0 : candidateK (6, 1) (0, 0) = (-1198090091 / 800000000000) := rfl
@[simp] theorem lookupK13_1 : candidateK (6, 1) (0, 1) = (-4690898521 / 2000000000000) := rfl
@[simp] theorem lookupK13_2 : candidateK (6, 1) (1, 0) = (13369556457 / 4000000000000) := rfl
@[simp] theorem lookupK13_3 : candidateK (6, 1) (1, 1) = (8256851437 / 2000000000000) := rfl
@[simp] theorem lookupK13_4 : candidateK (6, 1) (2, 0) = (-51890657491 / 4000000000000) := rfl
@[simp] theorem lookupK13_5 : candidateK (6, 1) (2, 1) = (-7516651173 / 4000000000000) := rfl
@[simp] theorem lookupK13_6 : candidateK (6, 1) (3, 0) = (1749048443 / 4000000000000) := rfl
@[simp] theorem lookupK13_7 : candidateK (6, 1) (3, 1) = (101495617 / 500000000000) := rfl
@[simp] theorem lookupK13_8 : candidateK (6, 1) (4, 0) = (105328519603 / 4000000000000) := rfl
@[simp] theorem lookupK13_9 : candidateK (6, 1) (4, 1) = (-805454719 / 500000000000) := rfl
@[simp] theorem lookupK13_10 : candidateK (6, 1) (5, 0) = (-17427268667 / 1000000000000) := rfl
@[simp] theorem lookupK13_11 : candidateK (6, 1) (5, 1) = (-21419143289 / 4000000000000) := rfl
@[simp] theorem lookupK13_12 : candidateK (6, 1) (6, 0) = (3892998059 / 800000000000) := rfl
@[simp] theorem lookupK13_13 : candidateK (6, 1) (6, 1) = (42005562023 / 4000000000000) := rfl
@[simp] theorem lookupK13_14 : candidateK (6, 1) (7, 0) = (-4668169083 / 2000000000000) := rfl
@[simp] theorem lookupK13_15 : candidateK (6, 1) (7, 1) = (-7872326449 / 2000000000000) := rfl
@[simp] theorem lookupK13_16 : candidateK (6, 1) (8, 0) = (-100277 / 125000000) := rfl
@[simp] theorem lookupK13_17 : candidateK (6, 1) (8, 1) = (988281617 / 4000000000000) := rfl
@[simp] theorem lookupK14_0 : candidateK (7, 0) (0, 0) = (482671 / 800000000) := rfl
@[simp] theorem lookupK14_1 : candidateK (7, 0) (0, 1) = (18025339 / 20000000000) := rfl
@[simp] theorem lookupK14_2 : candidateK (7, 0) (1, 0) = (10727489 / 4000000000) := rfl
@[simp] theorem lookupK14_3 : candidateK (7, 0) (1, 1) = (-55869139 / 200000000000) := rfl
@[simp] theorem lookupK14_4 : candidateK (7, 0) (2, 0) = (-6605617 / 800000000) := rfl
@[simp] theorem lookupK14_5 : candidateK (7, 0) (2, 1) = (-520577669 / 160000000000) := rfl
@[simp] theorem lookupK14_6 : candidateK (7, 0) (3, 0) = (8023441 / 800000000) := rfl
@[simp] theorem lookupK14_7 : candidateK (7, 0) (3, 1) = (9709414043 / 2000000000000) := rfl
@[simp] theorem lookupK14_8 : candidateK (7, 0) (4, 0) = (15310593 / 20000000000) := rfl
@[simp] theorem lookupK14_9 : candidateK (7, 0) (4, 1) = (3270282293 / 2000000000000) := rfl
@[simp] theorem lookupK14_10 : candidateK (7, 0) (5, 0) = (-193497917 / 20000000000) := rfl
@[simp] theorem lookupK14_11 : candidateK (7, 0) (5, 1) = (-1930323143 / 1000000000000) := rfl
@[simp] theorem lookupK14_12 : candidateK (7, 0) (6, 0) = (-50539531 / 10000000000) := rfl
@[simp] theorem lookupK14_13 : candidateK (7, 0) (6, 1) = (-4668169083 / 2000000000000) := rfl
@[simp] theorem lookupK14_14 : candidateK (7, 0) (7, 0) = (17946101 / 2000000000) := rfl
@[simp] theorem lookupK14_15 : candidateK (7, 0) (7, 1) = (4194168643 / 2000000000000) := rfl
@[simp] theorem lookupK14_16 : candidateK (7, 0) (8, 0) = (-176107 / 2000000000) := rfl
@[simp] theorem lookupK14_17 : candidateK (7, 0) (8, 1) = (-6258150451 / 4000000000000) := rfl
@[simp] theorem lookupK15_0 : candidateK (7, 1) (0, 0) = (11115808131 / 4000000000000) := rfl
@[simp] theorem lookupK15_1 : candidateK (7, 1) (0, 1) = (542995409 / 4000000000000) := rfl
@[simp] theorem lookupK15_2 : candidateK (7, 1) (1, 0) = (-6650039257 / 4000000000000) := rfl
@[simp] theorem lookupK15_3 : candidateK (7, 1) (1, 1) = (-312490441 / 400000000000) := rfl
@[simp] theorem lookupK15_4 : candidateK (7, 1) (2, 0) = (3522292603 / 4000000000000) := rfl
@[simp] theorem lookupK15_5 : candidateK (7, 1) (2, 1) = (11525119097 / 4000000000000) := rfl
@[simp] theorem lookupK15_6 : candidateK (7, 1) (3, 0) = (-38670186217 / 4000000000000) := rfl
@[simp] theorem lookupK15_7 : candidateK (7, 1) (3, 1) = (-117311799 / 62500000000) := rfl
@[simp] theorem lookupK15_8 : candidateK (7, 1) (4, 0) = (-696455297 / 4000000000000) := rfl
@[simp] theorem lookupK15_9 : candidateK (7, 1) (4, 1) = (-659803219 / 4000000000000) := rfl
@[simp] theorem lookupK15_10 : candidateK (7, 1) (5, 0) = (19661884631 / 1000000000000) := rfl
@[simp] theorem lookupK15_11 : candidateK (7, 1) (5, 1) = (-3590761601 / 4000000000000) := rfl
@[simp] theorem lookupK15_12 : candidateK (7, 1) (6, 0) = (-12176429087 / 1000000000000) := rfl
@[simp] theorem lookupK15_13 : candidateK (7, 1) (6, 1) = (-7872326449 / 2000000000000) := rfl
@[simp] theorem lookupK15_14 : candidateK (7, 1) (7, 0) = (4194168643 / 2000000000000) := rfl
@[simp] theorem lookupK15_15 : candidateK (7, 1) (7, 1) = (14634384229 / 2000000000000) := rfl
@[simp] theorem lookupK15_16 : candidateK (7, 1) (8, 0) = (-6686851 / 4000000000) := rfl
@[simp] theorem lookupK15_17 : candidateK (7, 1) (8, 1) = (-5478335191 / 2000000000000) := rfl
@[simp] theorem lookupK16_0 : candidateK (8, 0) (0, 0) = (-4270669 / 2500000000) := rfl
@[simp] theorem lookupK16_1 : candidateK (8, 0) (0, 1) = (-5790263 / 10000000000) := rfl
@[simp] theorem lookupK16_2 : candidateK (8, 0) (1, 0) = (8219 / 2000000000) := rfl
@[simp] theorem lookupK16_3 : candidateK (8, 0) (1, 1) = (1184173 / 10000000000) := rfl
@[simp] theorem lookupK16_4 : candidateK (8, 0) (2, 0) = (12583783 / 2500000000) := rfl
@[simp] theorem lookupK16_5 : candidateK (8, 0) (2, 1) = (-335477 / 10000000000) := rfl
@[simp] theorem lookupK16_6 : candidateK (8, 0) (3, 0) = (-5578073 / 1250000000) := rfl
@[simp] theorem lookupK16_7 : candidateK (8, 0) (3, 1) = (-5000353 / 2000000000) := rfl
@[simp] theorem lookupK16_8 : candidateK (8, 0) (4, 0) = (62208091 / 10000000000) := rfl
@[simp] theorem lookupK16_9 : candidateK (8, 0) (4, 1) = (40064829 / 10000000000) := rfl
@[simp] theorem lookupK16_10 : candidateK (8, 0) (5, 0) = (-45510449 / 20000000000) := rfl
@[simp] theorem lookupK16_11 : candidateK (8, 0) (5, 1) = (24262451 / 20000000000) := rfl
@[simp] theorem lookupK16_12 : candidateK (8, 0) (6, 0) = (-163843833 / 20000000000) := rfl
@[simp] theorem lookupK16_13 : candidateK (8, 0) (6, 1) = (-100277 / 125000000) := rfl
@[simp] theorem lookupK16_14 : candidateK (8, 0) (7, 0) = (-176107 / 2000000000) := rfl
@[simp] theorem lookupK16_15 : candidateK (8, 0) (7, 1) = (-6686851 / 4000000000) := rfl
@[simp] theorem lookupK16_16 : candidateK (8, 0) (8, 0) = (26761203 / 5000000000) := rfl
@[simp] theorem lookupK16_17 : candidateK (8, 0) (8, 1) = (497313 / 2000000000) := rfl
@[simp] theorem lookupK17_0 : candidateK (8, 1) (0, 0) = (1893004561 / 4000000000000) := rfl
@[simp] theorem lookupK17_1 : candidateK (8, 1) (0, 1) = (-688336753 / 400000000000) := rfl
@[simp] theorem lookupK17_2 : candidateK (8, 1) (1, 0) = (100356581 / 80000000000) := rfl
@[simp] theorem lookupK17_3 : candidateK (8, 1) (1, 1) = (87710189 / 2000000000000) := rfl
@[simp] theorem lookupK17_4 : candidateK (8, 1) (2, 0) = (1105772187 / 2000000000000) := rfl
@[simp] theorem lookupK17_5 : candidateK (8, 1) (2, 1) = (-99581409 / 500000000000) := rfl
@[simp] theorem lookupK17_6 : candidateK (8, 1) (3, 0) = (9900457589 / 4000000000000) := rfl
@[simp] theorem lookupK17_7 : candidateK (8, 1) (3, 1) = (5778801811 / 4000000000000) := rfl
@[simp] theorem lookupK17_8 : candidateK (8, 1) (4, 0) = (-19728927339 / 4000000000000) := rfl
@[simp] theorem lookupK17_9 : candidateK (8, 1) (4, 1) = (63126453 / 250000000000) := rfl
@[simp] theorem lookupK17_10 : candidateK (8, 1) (5, 0) = (-20382372849 / 4000000000000) := rfl
@[simp] theorem lookupK17_11 : candidateK (8, 1) (5, 1) = (727257491 / 800000000000) := rfl
@[simp] theorem lookupK17_12 : candidateK (8, 1) (6, 0) = (26623488657 / 4000000000000) := rfl
@[simp] theorem lookupK17_13 : candidateK (8, 1) (6, 1) = (988281617 / 4000000000000) := rfl
@[simp] theorem lookupK17_14 : candidateK (8, 1) (7, 0) = (-6258150451 / 4000000000000) := rfl
@[simp] theorem lookupK17_15 : candidateK (8, 1) (7, 1) = (-5478335191 / 2000000000000) := rfl
@[simp] theorem lookupK17_16 : candidateK (8, 1) (8, 0) = (497313 / 2000000000) := rfl
@[simp] theorem lookupK17_17 : candidateK (8, 1) (8, 1) = (1606018943 / 1000000000000) := rfl
@[simp] theorem lookupL0_0 : candidateL (0, 0) (0, 0) = 1 := rfl
@[simp] theorem lookupL0_1 : candidateL (0, 0) (0, 1) = 0 := rfl
@[simp] theorem lookupL0_2 : candidateL (0, 0) (1, 0) = 0 := rfl
@[simp] theorem lookupL0_3 : candidateL (0, 0) (1, 1) = 0 := rfl
@[simp] theorem lookupL0_4 : candidateL (0, 0) (2, 0) = 0 := rfl
@[simp] theorem lookupL0_5 : candidateL (0, 0) (2, 1) = 0 := rfl
@[simp] theorem lookupL0_6 : candidateL (0, 0) (3, 0) = 0 := rfl
@[simp] theorem lookupL0_7 : candidateL (0, 0) (3, 1) = 0 := rfl
@[simp] theorem lookupL0_8 : candidateL (0, 0) (4, 0) = 0 := rfl
@[simp] theorem lookupL0_9 : candidateL (0, 0) (4, 1) = 0 := rfl
@[simp] theorem lookupL0_10 : candidateL (0, 0) (5, 0) = 0 := rfl
@[simp] theorem lookupL0_11 : candidateL (0, 0) (5, 1) = 0 := rfl
@[simp] theorem lookupL0_12 : candidateL (0, 0) (6, 0) = 0 := rfl
@[simp] theorem lookupL0_13 : candidateL (0, 0) (6, 1) = 0 := rfl
@[simp] theorem lookupL0_14 : candidateL (0, 0) (7, 0) = 0 := rfl
@[simp] theorem lookupL0_15 : candidateL (0, 0) (7, 1) = 0 := rfl
@[simp] theorem lookupL0_16 : candidateL (0, 0) (8, 0) = 0 := rfl
@[simp] theorem lookupL0_17 : candidateL (0, 0) (8, 1) = 0 := rfl
@[simp] theorem lookupL1_0 : candidateL (0, 1) (0, 0) = (-281156817 / 556471819) := rfl
@[simp] theorem lookupL1_1 : candidateL (0, 1) (0, 1) = 1 := rfl
@[simp] theorem lookupL1_2 : candidateL (0, 1) (1, 0) = 0 := rfl
@[simp] theorem lookupL1_3 : candidateL (0, 1) (1, 1) = 0 := rfl
@[simp] theorem lookupL1_4 : candidateL (0, 1) (2, 0) = 0 := rfl
@[simp] theorem lookupL1_5 : candidateL (0, 1) (2, 1) = 0 := rfl
@[simp] theorem lookupL1_6 : candidateL (0, 1) (3, 0) = 0 := rfl
@[simp] theorem lookupL1_7 : candidateL (0, 1) (3, 1) = 0 := rfl
@[simp] theorem lookupL1_8 : candidateL (0, 1) (4, 0) = 0 := rfl
@[simp] theorem lookupL1_9 : candidateL (0, 1) (4, 1) = 0 := rfl
@[simp] theorem lookupL1_10 : candidateL (0, 1) (5, 0) = 0 := rfl
@[simp] theorem lookupL1_11 : candidateL (0, 1) (5, 1) = 0 := rfl
@[simp] theorem lookupL1_12 : candidateL (0, 1) (6, 0) = 0 := rfl
@[simp] theorem lookupL1_13 : candidateL (0, 1) (6, 1) = 0 := rfl
@[simp] theorem lookupL1_14 : candidateL (0, 1) (7, 0) = 0 := rfl
@[simp] theorem lookupL1_15 : candidateL (0, 1) (7, 1) = 0 := rfl
@[simp] theorem lookupL1_16 : candidateL (0, 1) (8, 0) = 0 := rfl
@[simp] theorem lookupL1_17 : candidateL (0, 1) (8, 1) = 0 := rfl
@[simp] theorem lookupL2_0 : candidateL (1, 0) (0, 0) = (-2057001257 / 3338830914) := rfl
@[simp] theorem lookupL2_1 : candidateL (1, 0) (0, 1) = (-16018544470183328493 / 55889703548345313614) := rfl
@[simp] theorem lookupL2_2 : candidateL (1, 0) (1, 0) = 1 := rfl
@[simp] theorem lookupL2_3 : candidateL (1, 0) (1, 1) = 0 := rfl
@[simp] theorem lookupL2_4 : candidateL (1, 0) (2, 0) = 0 := rfl
@[simp] theorem lookupL2_5 : candidateL (1, 0) (2, 1) = 0 := rfl
@[simp] theorem lookupL2_6 : candidateL (1, 0) (3, 0) = 0 := rfl
@[simp] theorem lookupL2_7 : candidateL (1, 0) (3, 1) = 0 := rfl
@[simp] theorem lookupL2_8 : candidateL (1, 0) (4, 0) = 0 := rfl
@[simp] theorem lookupL2_9 : candidateL (1, 0) (4, 1) = 0 := rfl
@[simp] theorem lookupL2_10 : candidateL (1, 0) (5, 0) = 0 := rfl
@[simp] theorem lookupL2_11 : candidateL (1, 0) (5, 1) = 0 := rfl
@[simp] theorem lookupL2_12 : candidateL (1, 0) (6, 0) = 0 := rfl
@[simp] theorem lookupL2_13 : candidateL (1, 0) (6, 1) = 0 := rfl
@[simp] theorem lookupL2_14 : candidateL (1, 0) (7, 0) = 0 := rfl
@[simp] theorem lookupL2_15 : candidateL (1, 0) (7, 1) = 0 := rfl
@[simp] theorem lookupL2_16 : candidateL (1, 0) (8, 0) = 0 := rfl
@[simp] theorem lookupL2_17 : candidateL (1, 0) (8, 1) = 0 := rfl
@[simp] theorem lookupL3_0 : candidateL (1, 1) (0, 0) = (-47354649157 / 667766182800) := rfl
@[simp] theorem lookupL3_1 : candidateL (1, 1) (0, 1) = (-41243369522578569296 / 139724258870863284035) := rfl
@[simp] theorem lookupL3_2 : candidateL (1, 1) (1, 0) = (-4800181070996780102284395939059 / 76058377708885404203689609796035) := rfl
@[simp] theorem lookupL3_3 : candidateL (1, 1) (1, 1) = 1 := rfl
@[simp] theorem lookupL3_4 : candidateL (1, 1) (2, 0) = 0 := rfl
@[simp] theorem lookupL3_5 : candidateL (1, 1) (2, 1) = 0 := rfl
@[simp] theorem lookupL3_6 : candidateL (1, 1) (3, 0) = 0 := rfl
@[simp] theorem lookupL3_7 : candidateL (1, 1) (3, 1) = 0 := rfl
@[simp] theorem lookupL3_8 : candidateL (1, 1) (4, 0) = 0 := rfl
@[simp] theorem lookupL3_9 : candidateL (1, 1) (4, 1) = 0 := rfl
@[simp] theorem lookupL3_10 : candidateL (1, 1) (5, 0) = 0 := rfl
@[simp] theorem lookupL3_11 : candidateL (1, 1) (5, 1) = 0 := rfl
@[simp] theorem lookupL3_12 : candidateL (1, 1) (6, 0) = 0 := rfl
@[simp] theorem lookupL3_13 : candidateL (1, 1) (6, 1) = 0 := rfl
@[simp] theorem lookupL3_14 : candidateL (1, 1) (7, 0) = 0 := rfl
@[simp] theorem lookupL3_15 : candidateL (1, 1) (7, 1) = 0 := rfl
@[simp] theorem lookupL3_16 : candidateL (1, 1) (8, 0) = 0 := rfl
@[simp] theorem lookupL3_17 : candidateL (1, 1) (8, 1) = 0 := rfl
@[simp] theorem lookupL4_0 : candidateL (2, 0) (0, 0) = (-1039347322 / 1669415457) := rfl
@[simp] theorem lookupL4_1 : candidateL (2, 0) (0, 1) = (-6438473616531765660 / 27944851774172656807) := rfl
@[simp] theorem lookupL4_2 : candidateL (2, 0) (1, 0) = (-14219242468206754096567256220520 / 15211675541777080840737921959207) := rfl
@[simp] theorem lookupL4_3 : candidateL (2, 0) (1, 1) = (-467562286702472496521263429486938297902379600 / 661227798504720496816165525588695508877654521) := rfl
@[simp] theorem lookupL4_4 : candidateL (2, 0) (2, 0) = 1 := rfl
@[simp] theorem lookupL4_5 : candidateL (2, 0) (2, 1) = 0 := rfl
@[simp] theorem lookupL4_6 : candidateL (2, 0) (3, 0) = 0 := rfl
@[simp] theorem lookupL4_7 : candidateL (2, 0) (3, 1) = 0 := rfl
@[simp] theorem lookupL4_8 : candidateL (2, 0) (4, 0) = 0 := rfl
@[simp] theorem lookupL4_9 : candidateL (2, 0) (4, 1) = 0 := rfl
@[simp] theorem lookupL4_10 : candidateL (2, 0) (5, 0) = 0 := rfl
@[simp] theorem lookupL4_11 : candidateL (2, 0) (5, 1) = 0 := rfl
@[simp] theorem lookupL4_12 : candidateL (2, 0) (6, 0) = 0 := rfl
@[simp] theorem lookupL4_13 : candidateL (2, 0) (6, 1) = 0 := rfl
@[simp] theorem lookupL4_14 : candidateL (2, 0) (7, 0) = 0 := rfl
@[simp] theorem lookupL4_15 : candidateL (2, 0) (7, 1) = 0 := rfl
@[simp] theorem lookupL4_16 : candidateL (2, 0) (8, 0) = 0 := rfl
@[simp] theorem lookupL4_17 : candidateL (2, 0) (8, 1) = 0 := rfl
@[simp] theorem lookupL5_0 : candidateL (2, 1) (0, 0) = (192086114803 / 333883091400) := rfl
@[simp] theorem lookupL5_1 : candidateL (2, 1) (0, 1) = (-1688144006701523678 / 2972856571720495405) := rfl
@[simp] theorem lookupL5_2 : candidateL (2, 1) (1, 0) = (-7874197927303374635005112063564 / 76058377708885404203689609796035) := rfl
@[simp] theorem lookupL5_3 : candidateL (2, 1) (1, 1) = (-355099962557351345116761693893609038219513438 / 661227798504720496816165525588695508877654521) := rfl
@[simp] theorem lookupL5_4 : candidateL (2, 1) (2, 0) = (20988905362077213440731602727039546993603557481841010321 / 156444193069134809007613356626382889146752192785042116400) := rfl
@[simp] theorem lookupL5_5 : candidateL (2, 1) (2, 1) = 1 := rfl
@[simp] theorem lookupL5_6 : candidateL (2, 1) (3, 0) = 0 := rfl
@[simp] theorem lookupL5_7 : candidateL (2, 1) (3, 1) = 0 := rfl
@[simp] theorem lookupL5_8 : candidateL (2, 1) (4, 0) = 0 := rfl
@[simp] theorem lookupL5_9 : candidateL (2, 1) (4, 1) = 0 := rfl
@[simp] theorem lookupL5_10 : candidateL (2, 1) (5, 0) = 0 := rfl
@[simp] theorem lookupL5_11 : candidateL (2, 1) (5, 1) = 0 := rfl
@[simp] theorem lookupL5_12 : candidateL (2, 1) (6, 0) = 0 := rfl
@[simp] theorem lookupL5_13 : candidateL (2, 1) (6, 1) = 0 := rfl
@[simp] theorem lookupL5_14 : candidateL (2, 1) (7, 0) = 0 := rfl
@[simp] theorem lookupL5_15 : candidateL (2, 1) (7, 1) = 0 := rfl
@[simp] theorem lookupL5_16 : candidateL (2, 1) (8, 0) = 0 := rfl
@[simp] theorem lookupL5_17 : candidateL (2, 1) (8, 1) = 0 := rfl
@[simp] theorem lookupL6_0 : candidateL (3, 0) (0, 0) = (811649597 / 3338830914) := rfl
@[simp] theorem lookupL6_1 : candidateL (3, 0) (0, 1) = (27891098779699265413 / 55889703548345313614) := rfl
@[simp] theorem lookupL6_2 : candidateL (3, 0) (1, 0) = (-6760094367308828967015184628207 / 15211675541777080840737921959207) := rfl
@[simp] theorem lookupL6_3 : candidateL (3, 0) (1, 1) = (-164750580754843674054616296915152930871224400 / 661227798504720496816165525588695508877654521) := rfl
@[simp] theorem lookupL6_4 : candidateL (3, 0) (2, 0) = (-935938641388832190900713301494950825214673160989791369 / 782220965345674045038066783131914445733760963925210582) := rfl
@[simp] theorem lookupL6_5 : candidateL (3, 0) (2, 1) = (-8249467857196854279425847929798093228587506396402227535686650653800 / 8083500003167212902569087740241432556623919119752858299163160176439) := rfl
@[simp] theorem lookupL6_6 : candidateL (3, 0) (3, 0) = 1 := rfl
@[simp] theorem lookupL6_7 : candidateL (3, 0) (3, 1) = 0 := rfl
@[simp] theorem lookupL6_8 : candidateL (3, 0) (4, 0) = 0 := rfl
@[simp] theorem lookupL6_9 : candidateL (3, 0) (4, 1) = 0 := rfl
@[simp] theorem lookupL6_10 : candidateL (3, 0) (5, 0) = 0 := rfl
@[simp] theorem lookupL6_11 : candidateL (3, 0) (5, 1) = 0 := rfl
@[simp] theorem lookupL6_12 : candidateL (3, 0) (6, 0) = 0 := rfl
@[simp] theorem lookupL6_13 : candidateL (3, 0) (6, 1) = 0 := rfl
@[simp] theorem lookupL6_14 : candidateL (3, 0) (7, 0) = 0 := rfl
@[simp] theorem lookupL6_15 : candidateL (3, 0) (7, 1) = 0 := rfl
@[simp] theorem lookupL6_16 : candidateL (3, 0) (8, 0) = 0 := rfl
@[simp] theorem lookupL6_17 : candidateL (3, 0) (8, 1) = 0 := rfl
@[simp] theorem lookupL7_0 : candidateL (3, 1) (0, 0) = (2554388897 / 66776618280) := rfl
@[simp] theorem lookupL7_1 : candidateL (3, 1) (0, 1) = (1443304917635279868 / 27944851774172656807) := rfl
@[simp] theorem lookupL7_2 : candidateL (3, 1) (1, 0) = (4587682979273912610935485512608 / 15211675541777080840737921959207) := rfl
@[simp] theorem lookupL7_3 : candidateL (3, 1) (1, 1) = (-246872877540722995002128241979919879153897010 / 661227798504720496816165525588695508877654521) := rfl
@[simp] theorem lookupL7_4 : candidateL (3, 1) (2, 0) = (-12956022893493172155516851889619314943474701007351801247 / 78222096534567404503806678313191444573376096392521058200) := rfl
@[simp] theorem lookupL7_5 : candidateL (3, 1) (2, 1) = (-4107947628106467828557692158621073347705088956949146341953209245106 / 8083500003167212902569087740241432556623919119752858299163160176439) := rfl
@[simp] theorem lookupL7_6 : candidateL (3, 1) (3, 0) = (10721506960057732725547768272160201602324843231652093208227500678498254128117 / 48987185726169720190330461879342984473838473188580974990179939566945158177200) := rfl
@[simp] theorem lookupL7_7 : candidateL (3, 1) (3, 1) = 1 := rfl
@[simp] theorem lookupL7_8 : candidateL (3, 1) (4, 0) = 0 := rfl
@[simp] theorem lookupL7_9 : candidateL (3, 1) (4, 1) = 0 := rfl
@[simp] theorem lookupL7_10 : candidateL (3, 1) (5, 0) = 0 := rfl
@[simp] theorem lookupL7_11 : candidateL (3, 1) (5, 1) = 0 := rfl
@[simp] theorem lookupL7_12 : candidateL (3, 1) (6, 0) = 0 := rfl
@[simp] theorem lookupL7_13 : candidateL (3, 1) (6, 1) = 0 := rfl
@[simp] theorem lookupL7_14 : candidateL (3, 1) (7, 0) = 0 := rfl
@[simp] theorem lookupL7_15 : candidateL (3, 1) (7, 1) = 0 := rfl
@[simp] theorem lookupL7_16 : candidateL (3, 1) (8, 0) = 0 := rfl
@[simp] theorem lookupL7_17 : candidateL (3, 1) (8, 1) = 0 := rfl
@[simp] theorem lookupL8_0 : candidateL (4, 0) (0, 0) = (9512821 / 1669415457) := rfl
@[simp] theorem lookupL8_1 : candidateL (4, 0) (0, 1) = (1897213196626680 / 177992686459698451) := rfl
@[simp] theorem lookupL8_2 : candidateL (4, 0) (1, 0) = (5319482947253262583324927764880 / 15211675541777080840737921959207) := rfl
@[simp] theorem lookupL8_3 : candidateL (4, 0) (1, 1) = (661194847787303476599217430779849159796221200 / 661227798504720496816165525588695508877654521) := rfl
@[simp] theorem lookupL8_4 : candidateL (4, 0) (2, 0) = (-168342636059882922447254212544097672663755101577665738 / 391110482672837022519033391565957222866880481962605291) := rfl
@[simp] theorem lookupL8_5 : candidateL (4, 0) (2, 1) = (499583400718186103116177784780509378121808448567832881486403644000 / 8083500003167212902569087740241432556623919119752858299163160176439) := rfl
@[simp] theorem lookupL8_6 : candidateL (4, 0) (3, 0) = (-633923864835349622233121536966318793950471909091939280791752518639991099742 / 437385586840801073127950552494133789944986367755187276698035174704867483725) := rfl
@[simp] theorem lookupL8_7 : candidateL (4, 0) (3, 1) = (-126407218889362802680530887341873302062079144696359115595407855979114340809305102625120 / 200118009343657176361393221615626481951272358086144636652518941298728670532338112203861) := rfl
@[simp] theorem lookupL8_8 : candidateL (4, 0) (4, 0) = 1 := rfl
@[simp] theorem lookupL8_9 : candidateL (4, 0) (4, 1) = 0 := rfl
@[simp] theorem lookupL8_10 : candidateL (4, 0) (5, 0) = 0 := rfl
@[simp] theorem lookupL8_11 : candidateL (4, 0) (5, 1) = 0 := rfl
@[simp] theorem lookupL8_12 : candidateL (4, 0) (6, 0) = 0 := rfl
@[simp] theorem lookupL8_13 : candidateL (4, 0) (6, 1) = 0 := rfl
@[simp] theorem lookupL8_14 : candidateL (4, 0) (7, 0) = 0 := rfl
@[simp] theorem lookupL8_15 : candidateL (4, 0) (7, 1) = 0 := rfl
@[simp] theorem lookupL8_16 : candidateL (4, 0) (8, 0) = 0 := rfl
@[simp] theorem lookupL8_17 : candidateL (4, 0) (8, 1) = 0 := rfl
@[simp] theorem lookupL9_0 : candidateL (4, 1) (0, 0) = (-17718529767 / 222588727600) := rfl
@[simp] theorem lookupL9_1 : candidateL (4, 1) (0, 1) = (-48023231156041407399 / 279448517741726568070) := rfl
@[simp] theorem lookupL9_2 : candidateL (4, 1) (1, 0) = (-2763047206723229819770260624282 / 76058377708885404203689609796035) := rfl
@[simp] theorem lookupL9_3 : candidateL (4, 1) (1, 1) = (-21054221151320538458693827375151997998230607 / 661227798504720496816165525588695508877654521) := rfl
@[simp] theorem lookupL9_4 : candidateL (4, 1) (2, 0) = (21942232982270362015272205156067116640428070069795250573 / 78222096534567404503806678313191444573376096392521058200) := rfl
@[simp] theorem lookupL9_5 : candidateL (4, 1) (2, 1) = (-3412866534802520625944574822809663125660350885249065974567003819866 / 8083500003167212902569087740241432556623919119752858299163160176439) := rfl
@[simp] theorem lookupL9_6 : candidateL (4, 1) (3, 0) = (-272312479410932769363452786087676693191731778534398445379718531873110898730819 / 1224679643154243004758261546983574611845961829714524374754498489173628954430000) := rfl
@[simp] theorem lookupL9_7 : candidateL (4, 1) (3, 1) = (-507692285323361526461016026810840330210123149877630307599766098682146876811301273668503 / 1000590046718285881806966108078132409756361790430723183262594706493643352661690561019305) := rfl
@[simp] theorem lookupL9_8 : candidateL (4, 1) (4, 0) = (128655456551476104785524734771904783559020784560700153266622835988269985973111045945945624672191107 / 414757042317679810946681367499965067516162605168537980968779866584389463553103385943912604183876800) := rfl
@[simp] theorem lookupL9_9 : candidateL (4, 1) (4, 1) = 1 := rfl
@[simp] theorem lookupL9_10 : candidateL (4, 1) (5, 0) = 0 := rfl
@[simp] theorem lookupL9_11 : candidateL (4, 1) (5, 1) = 0 := rfl
@[simp] theorem lookupL9_12 : candidateL (4, 1) (6, 0) = 0 := rfl
@[simp] theorem lookupL9_13 : candidateL (4, 1) (6, 1) = 0 := rfl
@[simp] theorem lookupL9_14 : candidateL (4, 1) (7, 0) = 0 := rfl
@[simp] theorem lookupL9_15 : candidateL (4, 1) (7, 1) = 0 := rfl
@[simp] theorem lookupL9_16 : candidateL (4, 1) (8, 0) = 0 := rfl
@[simp] theorem lookupL9_17 : candidateL (4, 1) (8, 1) = 0 := rfl
@[simp] theorem lookupL10_0 : candidateL (5, 0) (0, 0) = (-18717269 / 3338830914) := rfl
@[simp] theorem lookupL10_1 : candidateL (5, 0) (0, 1) = (-291990557390039080 / 27944851774172656807) := rfl
@[simp] theorem lookupL10_2 : candidateL (5, 0) (1, 0) = (445884905626366492838563649720 / 15211675541777080840737921959207) := rfl
@[simp] theorem lookupL10_3 : candidateL (5, 0) (1, 1) = (32994292103460426069233321871963107877253000 / 661227798504720496816165525588695508877654521) := rfl
@[simp] theorem lookupL10_4 : candidateL (5, 0) (2, 0) = (224568567563368087133928336756035131071206607381894542 / 391110482672837022519033391565957222866880481962605291) := rfl
@[simp] theorem lookupL10_5 : candidateL (5, 0) (2, 1) = (9367451357915070338621951293667925038236109441759188151321944326400 / 8083500003167212902569087740241432556623919119752858299163160176439) := rfl
@[simp] theorem lookupL10_6 : candidateL (5, 0) (3, 0) = (-267793879614198582910814596126589367094697912118569735130129842121450740423 / 1020566369295202503965217955819645509871634858095436978962082074311357462025) := rfl
@[simp] theorem lookupL10_7 : candidateL (5, 0) (3, 1) = (-120635906513170522100727181560144327136735639678875108081025224019138777331855923156800 / 200118009343657176361393221615626481951272358086144636652518941298728670532338112203861) := rfl
@[simp] theorem lookupL10_8 : candidateL (5, 0) (4, 0) = (-3143142863471309195786130251954112454933241584072214584785898967667737331059680820446296431846771 / 2073785211588399054733406837499825337580813025842689904843899332921947317765516929719563020919384) := rfl
@[simp] theorem lookupL10_9 : candidateL (5, 0) (4, 1) = (-3559738869030431860647222024953419113190000365047644029901082176969616335126031321517479723281262962615609400 / 18921170648037905597939938894582197786773172430445851828089334224273923837384746034283145051085508624051423071) := rfl
@[simp] theorem lookupL10_10 : candidateL (5, 0) (5, 0) = 1 := rfl
@[simp] theorem lookupL10_11 : candidateL (5, 0) (5, 1) = 0 := rfl
@[simp] theorem lookupL10_12 : candidateL (5, 0) (6, 0) = 0 := rfl
@[simp] theorem lookupL10_13 : candidateL (5, 0) (6, 1) = 0 := rfl
@[simp] theorem lookupL10_14 : candidateL (5, 0) (7, 0) = 0 := rfl
@[simp] theorem lookupL10_15 : candidateL (5, 0) (7, 1) = 0 := rfl
@[simp] theorem lookupL10_16 : candidateL (5, 0) (8, 0) = 0 := rfl
@[simp] theorem lookupL10_17 : candidateL (5, 0) (8, 1) = 0 := rfl
@[simp] theorem lookupL11_0 : candidateL (5, 1) (0, 0) = (2167550171 / 111294363800) := rfl
@[simp] theorem lookupL11_1 : candidateL (5, 1) (0, 1) = (10925569758021964553 / 279448517741726568070) := rfl
@[simp] theorem lookupL11_2 : candidateL (5, 1) (1, 0) = (-9548433869597889835319793409647 / 76058377708885404203689609796035) := rfl
@[simp] theorem lookupL11_3 : candidateL (5, 1) (1, 1) = (-14388129618504081572046422330115928658223054 / 94461114072102928116595075084099358411093503) := rfl
@[simp] theorem lookupL11_4 : candidateL (5, 1) (2, 0) = (-10674096148978288161821860053792215730064766907371635917 / 78222096534567404503806678313191444573376096392521058200) := rfl
@[simp] theorem lookupL11_5 : candidateL (5, 1) (2, 1) = (-461888641095998943979237079049127314725265066349487600664533850166 / 8083500003167212902569087740241432556623919119752858299163160176439) := rfl
@[simp] theorem lookupL11_6 : candidateL (5, 1) (3, 0) = (354711728419814260447821981914707894095623452377189261609880090733830992560921 / 1224679643154243004758261546983574611845961829714524374754498489173628954430000) := rfl
@[simp] theorem lookupL11_7 : candidateL (5, 1) (3, 1) = (-777917678226036981728798620597988850560951176659678552351102218231270869517257094071483 / 1000590046718285881806966108078132409756361790430723183262594706493643352661690561019305) := rfl
@[simp] theorem lookupL11_8 : candidateL (5, 1) (4, 0) = (-62608504800950414053372172134000881538328674622462475004438410948203854685248112222264586112825969 / 207378521158839905473340683749982533758081302584268990484389933292194731776551692971956302091938400) := rfl
@[simp] theorem lookupL11_9 : candidateL (5, 1) (4, 1) = (-6317758711155226290817267318014716985992797531114077877879733706167272052822302374474467392686408395477068554 / 18921170648037905597939938894582197786773172430445851828089334224273923837384746034283145051085508624051423071) := rfl
@[simp] theorem lookupL11_10 : candidateL (5, 1) (5, 0) = (3435997842970882310284964592936612701760982521916348353211066684703736454483405148614919563610276713510168806019557193 / 22262892500766805306432489927907893172896739855505916479641733029917404953782323458900794357556902167846915308602415690) := rfl
@[simp] theorem lookupL11_11 : candidateL (5, 1) (5, 1) = 1 := rfl
@[simp] theorem lookupL11_12 : candidateL (5, 1) (6, 0) = 0 := rfl
@[simp] theorem lookupL11_13 : candidateL (5, 1) (6, 1) = 0 := rfl
@[simp] theorem lookupL11_14 : candidateL (5, 1) (7, 0) = 0 := rfl
@[simp] theorem lookupL11_15 : candidateL (5, 1) (7, 1) = 0 := rfl
@[simp] theorem lookupL11_16 : candidateL (5, 1) (8, 0) = 0 := rfl
@[simp] theorem lookupL11_17 : candidateL (5, 1) (8, 1) = 0 := rfl
@[simp] theorem lookupL12_0 : candidateL (6, 0) (0, 0) = (13905213 / 1112943638) := rfl
@[simp] theorem lookupL12_1 : candidateL (6, 0) (0, 1) = (261916615590370500 / 27944851774172656807) := rfl
@[simp] theorem lookupL12_2 : candidateL (6, 0) (1, 0) = (-80886142651778412280268630160 / 15211675541777080840737921959207) := rfl
@[simp] theorem lookupL12_3 : candidateL (6, 0) (1, 1) = (-78301235097382576647139292467071052521750600 / 661227798504720496816165525588695508877654521) := rfl
@[simp] theorem lookupL12_4 : candidateL (6, 0) (2, 0) = (37627573265986793329606111938581984312477751457006347 / 391110482672837022519033391565957222866880481962605291) := rfl
@[simp] theorem lookupL12_5 : candidateL (6, 0) (2, 1) = (-453971240677370801841290362622004029847958393493571036794249316000 / 8083500003167212902569087740241432556623919119752858299163160176439) := rfl
@[simp] theorem lookupL12_6 : candidateL (6, 0) (3, 0) = (821408953056697903667807775922368479820067650245242543478290044754061120063 / 1224679643154243004758261546983574611845961829714524374754498489173628954430) := rfl
@[simp] theorem lookupL12_7 : candidateL (6, 0) (3, 1) = (244678914560334834937377908574254497119423107490725991917561542574654689065198454668040 / 200118009343657176361393221615626481951272358086144636652518941298728670532338112203861) := rfl
@[simp] theorem lookupL12_8 : candidateL (6, 0) (4, 0) = (303253434372711958717306267495404891475450204928213368888167558972519821240423172462769519014395 / 2073785211588399054733406837499825337580813025842689904843899332921947317765516929719563020919384) := rfl
@[simp] theorem lookupL12_9 : candidateL (6, 0) (4, 1) = (-23347826296245039947230992120615867704448818677108860042863778172530069155472920062183140342460172586672433800 / 18921170648037905597939938894582197786773172430445851828089334224273923837384746034283145051085508624051423071) := rfl
@[simp] theorem lookupL12_10 : candidateL (6, 0) (5, 0) = (-6146909895802613802390322270910082955675433841085795421492084971433099996446226067515698218787868373984954674386942807 / 4452578500153361061286497985581578634579347971101183295928346605983480990756464691780158871511380433569383061720483138) := rfl
@[simp] theorem lookupL12_11 : candidateL (6, 0) (5, 1) = (-28665000155309625785402660996692195767762322880911525904756270941459423878980530834908846434479578513860295058857534537244439335 / 27777843629871286532959907516035629398931480247090831275450067989880519546301686470583169005796573495281436255883859855727614727) := rfl
@[simp] theorem lookupL12_12 : candidateL (6, 0) (6, 0) = 1 := rfl
@[simp] theorem lookupL12_13 : candidateL (6, 0) (6, 1) = 0 := rfl
@[simp] theorem lookupL12_14 : candidateL (6, 0) (7, 0) = 0 := rfl
@[simp] theorem lookupL12_15 : candidateL (6, 0) (7, 1) = 0 := rfl
@[simp] theorem lookupL12_16 : candidateL (6, 0) (8, 0) = 0 := rfl
@[simp] theorem lookupL12_17 : candidateL (6, 0) (8, 1) = 0 := rfl
@[simp] theorem lookupL13_0 : candidateL (6, 1) (0, 0) = (-1198090091 / 133553236560) := rfl
@[simp] theorem lookupL13_1 : candidateL (6, 1) (0, 1) = (-6904961647774561133 / 279448517741726568070) := rfl
@[simp] theorem lookupL13_2 : candidateL (6, 1) (1, 0) = (1026561574158624377174723425486 / 76058377708885404203689609796035) := rfl
@[simp] theorem lookupL13_3 : candidateL (6, 1) (1, 1) = (11137208788684202076375611073828296558711645 / 94461114072102928116595075084099358411093503) := rfl
@[simp] theorem lookupL13_4 : candidateL (6, 1) (2, 0) = (-7223261489070836637035685915021091138116597124292375279 / 39111048267283702251903339156595722286688048196260529100) := rfl
@[simp] theorem lookupL13_5 : candidateL (6, 1) (2, 1) = (353645073165825985851269426975314041690819970681368765186830867916 / 8083500003167212902569087740241432556623919119752858299163160176439) := rfl
@[simp] theorem lookupL13_6 : candidateL (6, 1) (3, 0) = (-280216129510532452101496629761217808107604659001682859876648349048516297396531 / 1224679643154243004758261546983574611845961829714524374754498489173628954430000) := rfl
@[simp] theorem lookupL13_7 : candidateL (6, 1) (3, 1) = (299675968981828754251002113356172936419469445259006456443209894619801836149522896420713 / 1000590046718285881806966108078132409756361790430723183262594706493643352661690561019305) := rfl
@[simp] theorem lookupL13_8 : candidateL (6, 1) (4, 0) = (126157820171905260946625826162099042263131851953656345313791838461728095806444065090048048947013193 / 414757042317679810946681367499965067516162605168537980968779866584389463553103385943912604183876800) := rfl
@[simp] theorem lookupL13_9 : candidateL (6, 1) (4, 1) = (-15837341823541321038864814941218988913761439682020869546522319550368957416780158311631673931053456068498010851 / 18921170648037905597939938894582197786773172430445851828089334224273923837384746034283145051085508624051423071) := rfl
@[simp] theorem lookupL13_10 : candidateL (6, 1) (5, 0) = (-63751064909195155693921680018453827352602165728314142369639718650959868915798984533904117318925488201941367544426833163 / 178103140006134442451459919423263145383173918844047331837133864239339239630258587671206354860455217342775322468819325520) := rfl
@[simp] theorem lookupL13_11 : candidateL (6, 1) (5, 1) = (-32753161157738205354386187582163681855644311138148526042857008161097225106018898289936224952765190198786947319381138930746509945 / 111111374519485146131839630064142517595725920988363325101800271959522078185206745882332676023186293981125745023535439422910458908) := rfl
@[simp] theorem lookupL13_12 : candidateL (6, 1) (6, 0) = (95033884378232419959402715541724222181629307180574818013754641644788214834061465912113208213420124342203949999898246104091562636246140991 / 410132446332429501632535672717021675339157413624917542751719167462065638888295851459179438417839381925843833014813490615547089635216036690) := rfl
@[simp] theorem lookupL13_13 : candidateL (6, 1) (6, 1) = 1 := rfl
@[simp] theorem lookupL13_14 : candidateL (6, 1) (7, 0) = 0 := rfl
@[simp] theorem lookupL13_15 : candidateL (6, 1) (7, 1) = 0 := rfl
@[simp] theorem lookupL13_16 : candidateL (6, 1) (8, 0) = 0 := rfl
@[simp] theorem lookupL13_17 : candidateL (6, 1) (8, 1) = 0 := rfl
@[simp] theorem lookupL14_0 : candidateL (7, 0) (0, 0) = (12066775 / 3338830914) := rfl
@[simp] theorem lookupL14_1 : candidateL (7, 0) (0, 1) = (268464984637536320 / 27944851774172656807) := rfl
@[simp] theorem lookupL14_2 : candidateL (7, 0) (1, 0) = (455960847761800943929857320840 / 15211675541777080840737921959207) := rfl
@[simp] theorem lookupL14_3 : candidateL (7, 0) (1, 1) = (8128811175273754377177843199622826920977000 / 661227798504720496816165525588695508877654521) := rfl
@[simp] theorem lookupL14_4 : candidateL (7, 0) (2, 0) = (-27704478431447257686915984851010983871327125351507540 / 391110482672837022519033391565957222866880481962605291) := rfl
@[simp] theorem lookupL14_5 : candidateL (7, 0) (2, 1) = (-1140432178319054357190713063911549315300986873675971408304541438000 / 8083500003167212902569087740241432556623919119752858299163160176439) := rfl
@[simp] theorem lookupL14_6 : candidateL (7, 0) (3, 0) = (616121341612996289771802074926369898748464125305641633869664478136591526 / 5831807824544014308372674033255117199266484903402497022640468996064899783) := rfl
@[simp] theorem lookupL14_7 : candidateL (7, 0) (3, 1) = (53805624384875283214039703771567729064035233227945259367688168239778457045970786454240 / 200118009343657176361393221615626481951272358086144636652518941298728670532338112203861) := rfl
@[simp] theorem lookupL14_8 : candidateL (7, 0) (4, 0) = (420510995940322361066076287758043993516280620722100541904567980248636288576847270908100434915115 / 2073785211588399054733406837499825337580813025842689904843899332921947317765516929719563020919384) := rfl
@[simp] theorem lookupL14_9 : candidateL (7, 0) (4, 1) = (22506219039370039272426260657079947434501145240473591251678195502817577951981393464162871522150975557587246200 / 18921170648037905597939938894582197786773172430445851828089334224273923837384746034283145051085508624051423071) := rfl
@[simp] theorem lookupL14_10 : candidateL (7, 0) (5, 0) = (1324571652171875858171554798248839472242836125797399272314113232105026452853617646754414009349131562712601673219133367 / 4452578500153361061286497985581578634579347971101183295928346605983480990756464691780158871511380433569383061720483138) := rfl
@[simp] theorem lookupL14_11 : candidateL (7, 0) (5, 1) = (-14349708395984207264975670405937821562193836350246269977701865318698971660798191631874440905308425873402710648195280565671709765 / 27777843629871286532959907516035629398931480247090831275450067989880519546301686470583169005796573495281436255883859855727614727) := rfl
@[simp] theorem lookupL14_12 : candidateL (7, 0) (6, 0) = (-24184106224208960338317659668754253590711735838455091307598547324854957629523419699698812729747436820460832624569164773706933718680947989 / 41013244633242950163253567271702167533915741362491754275171916746206563888829585145917943841783938192584383301481349061554708963521603669) := rfl
@[simp] theorem lookupL14_13 : candidateL (7, 0) (6, 1) = (-182915353727221310025188191887066762407531830668155741065739643675295743924333351202189734846769883115093888459963705344571955938114332617515640400 / 2625398655755109579609881724170253949692212801167363854449402424606607962852276209306898110987869644710682823711674194378913090147084260257010314227) := rfl
@[simp] theorem lookupL14_14 : candidateL (7, 0) (7, 0) = 1 := rfl
@[simp] theorem lookupL14_15 : candidateL (7, 0) (7, 1) = 0 := rfl
@[simp] theorem lookupL14_16 : candidateL (7, 0) (8, 0) = 0 := rfl
@[simp] theorem lookupL14_17 : candidateL (7, 0) (8, 1) = 0 := rfl
@[simp] theorem lookupL15_0 : candidateL (7, 1) (0, 0) = (3705269377 / 222588727600) := rfl
@[simp] theorem lookupL15_1 : candidateL (7, 1) (0, 1) = (1713723437724778999 / 139724258870863284035) := rfl
@[simp] theorem lookupL15_2 : candidateL (7, 1) (1, 0) = (65844886745966719602895460775 / 15211675541777080840737921959207) := rfl
@[simp] theorem lookupL15_3 : candidateL (7, 1) (1, 1) = (-2401238371176876289398134613275886159672623 / 661227798504720496816165525588695508877654521) := rfl
@[simp] theorem lookupL15_4 : candidateL (7, 1) (2, 0) = (1109065434832649399822436885965390458161594116045929051 / 19555524133641851125951669578297861143344024098130264550) := rfl
@[simp] theorem lookupL15_5 : candidateL (7, 1) (2, 1) = (1066755096281825530214460988730946814682316648295155483410931687432 / 8083500003167212902569087740241432556623919119752858299163160176439) := rfl
@[simp] theorem lookupL15_6 : candidateL (7, 1) (3, 0) = (-166988177028246593665208276716843865250443391509853045537066974602726739654159 / 1224679643154243004758261546983574611845961829714524374754498489173628954430000) := rfl
@[simp] theorem lookupL15_7 : candidateL (7, 1) (3, 1) = (59674274742432181071584320424778004417564564412254046633364698048859247920810784065997 / 1000590046718285881806966108078132409756361790430723183262594706493643352661690561019305) := rfl
@[simp] theorem lookupL15_8 : candidateL (7, 1) (4, 0) = (-124745562938919919515309933740212216448037223372440029278787574296051287217889652767046750791793623 / 414757042317679810946681367499965067516162605168537980968779866584389463553103385943912604183876800) := rfl
@[simp] theorem lookupL15_9 : candidateL (7, 1) (4, 1) = (8743943836291145237888635193628670181027224512137846034190407674924810275820214082738961004016508507051497341 / 18921170648037905597939938894582197786773172430445851828089334224273923837384746034283145051085508624051423071) := rfl
@[simp] theorem lookupL15_10 : candidateL (7, 1) (5, 0) = (405765842603182958064881258156514427760959065233708519009720039318610036771206305322342430403651485806330175411414631669 / 890515700030672212257299597116315726915869594220236659185669321196696198151292938356031774302276086713876612344096627600) := rfl
@[simp] theorem lookupL15_11 : candidateL (7, 1) (5, 1) = (-92176853027474471559525490287879763442166154642698994403642420418118926343164026841381961202712182250959511151774276506878033861 / 111111374519485146131839630064142517595725920988363325101800271959522078185206745882332676023186293981125745023535439422910458908) := rfl
@[simp] theorem lookupL15_12 : candidateL (7, 1) (6, 0) = (-9162561646946278754600323696492088512713536897416647058173641086729910214258286116205987830027784004726796387618997489681890500205393738 / 41013244633242950163253567271702167533915741362491754275171916746206563888829585145917943841783938192584383301481349061554708963521603669) := rfl
@[simp] theorem lookupL15_13 : candidateL (7, 1) (6, 1) = (-166815925480062203304682597131469647644583824541980481658009617375458604109253942892717510636759333784771553730702219107154259824071188116197391761 / 2625398655755109579609881724170253949692212801167363854449402424606607962852276209306898110987869644710682823711674194378913090147084260257010314227) := rfl
@[simp] theorem lookupL15_14 : candidateL (7, 1) (7, 0) = (4138074813441799850657880520742983782583019457048882759734364571081330894701032449085067686217357608463201080933447072907158251461916173468694686615000145669 / 8079833363374375756268428212673706465541946633347913120740667821526730141352852194689555432324734722025113990985922203511397389608811220360711985794444386000) := rfl
@[simp] theorem lookupL15_15 : candidateL (7, 1) (7, 1) = 1 := rfl
@[simp] theorem lookupL15_16 : candidateL (7, 1) (8, 0) = 0 := rfl
@[simp] theorem lookupL15_17 : candidateL (7, 1) (8, 1) = 0 := rfl
@[simp] theorem lookupL16_0 : candidateL (8, 0) (0, 0) = (-17082676 / 1669415457) := rfl
@[simp] theorem lookupL16_1 : candidateL (8, 0) (0, 1) = (-321001159764027560 / 27944851774172656807) := rfl
@[simp] theorem lookupL16_2 : candidateL (8, 0) (1, 0) = (-196059539756077508927397852400 / 15211675541777080840737921959207) := rfl
@[simp] theorem lookupL16_3 : candidateL (8, 0) (1, 1) = (-12672047983064919456020023310152931636244800 / 661227798504720496816165525588695508877654521) := rfl
@[simp] theorem lookupL16_4 : candidateL (8, 0) (2, 0) = (12584860571762478473414524190717707166018776638596792 / 391110482672837022519033391565957222866880481962605291) := rfl
@[simp] theorem lookupL16_5 : candidateL (8, 0) (2, 1) = (-347904418869427751837036354732118264233393275960631925986336508800 / 8083500003167212902569087740241432556623919119752858299163160176439) := rfl
@[simp] theorem lookupL16_6 : candidateL (8, 0) (3, 0) = (-193753187960946252697862812127522248849412705140464095397572262121515340243 / 3061699107885607511895653867458936529614904574286310936886246222934072386075) := rfl
@[simp] theorem lookupL16_7 : candidateL (8, 0) (3, 1) = (-61003357422293633416597536497257959639618717355699699606453126051296774572094820005680 / 200118009343657176361393221615626481951272358086144636652518941298728670532338112203861) := rfl
@[simp] theorem lookupL16_8 : candidateL (8, 0) (4, 0) = (183810861636001560705011174666885944918189219918038436554168437365693884832714359057759497163579 / 1036892605794199527366703418749912668790406512921344952421949666460973658882758464859781510459692) := rfl
@[simp] theorem lookupL16_9 : candidateL (8, 0) (4, 1) = (2670510019439995295003765083766650985815207424956966707290758581355973800061184494160828193190221146856162800 / 18921170648037905597939938894582197786773172430445851828089334224273923837384746034283145051085508624051423071) := rfl
@[simp] theorem lookupL16_10 : candidateL (8, 0) (5, 0) = (522965188119832951496578939126205889239055160050842789501759347456279849570588866329863894405095074457735172796704515 / 4452578500153361061286497985581578634579347971101183295928346605983480990756464691780158871511380433569383061720483138) := rfl
@[simp] theorem lookupL16_11 : candidateL (8, 0) (5, 1) = (39079485145254053323443294807653660930864390743565493845086923839048689258619295362055116840044397795138450601528518661304537450 / 27777843629871286532959907516035629398931480247090831275450067989880519546301686470583169005796573495281436255883859855727614727) := rfl
@[simp] theorem lookupL16_12 : candidateL (8, 0) (6, 0) = (-1154683277114389709280923143629800520960839738335567733982599856852256326641464115800142256434778970469133849577510171625300323991241100 / 3154864971787919243327197482438628271839672412499365713474762826631274145294583472762918757060302937891106407806257620119592997193969513) := rfl
@[simp] theorem lookupL16_13 : candidateL (8, 0) (6, 1) = (-18208273445458064044624604833709593442664642888019971077496322397110070949986753760290180871675030941630449118286998393013609835880153614521945400 / 2625398655755109579609881724170253949692212801167363854449402424606607962852276209306898110987869644710682823711674194378913090147084260257010314227) := rfl
@[simp] theorem lookupL16_14 : candidateL (8, 0) (7, 0) = (-18867288120294167490357786456632879015829212705773948370129041011200237570476010068532117067668998609343128322426212885553436640003700628573562254448828402 / 20199583408435939390671070531684266163854866583369782801851669553816825353382130486723888580811836805062784977464805508778493474022028050901779964486110965) := rfl
@[simp] theorem lookupL16_15 : candidateL (8, 0) (7, 1) = (-1317441392203890413266444793329622445988063751409157094932954874661702237284871367135821286442544806195529628020494193220045713737462203774219199154274433828768682400 / 1990337992458895867294451952088980138384735017470629157526423633247869321722325668662888026226959229679172056444281864658774656915653269259780794861472993455032172597) := rfl
@[simp] theorem lookupL16_16 : candidateL (8, 0) (8, 0) = 1 := rfl
@[simp] theorem lookupL16_17 : candidateL (8, 0) (8, 1) = 0 := rfl
@[simp] theorem lookupL17_0 : candidateL (8, 1) (0, 0) = (1893004561 / 667766182800) := rfl
@[simp] theorem lookupL17_1 : candidateL (8, 1) (0, 1) = (-299833537575217703 / 25404410703793324370) := rfl
@[simp] theorem lookupL17_2 : candidateL (8, 1) (1, 0) = (752056772041088670626858551328 / 76058377708885404203689609796035) := rfl
@[simp] theorem lookupL17_3 : candidateL (8, 1) (1, 1) = (-7038443462020113109094674351464746805983053 / 661227798504720496816165525588695508877654521) := rfl
@[simp] theorem lookupL17_4 : candidateL (8, 1) (2, 0) = (3570175522134318128614969409407113298338357828898225989 / 156444193069134809007613356626382889146752192785042116400) := rfl
@[simp] theorem lookupL17_5 : candidateL (8, 1) (2, 1) = (-959404782446528736761990580864311905228480453147512991923466298429 / 8083500003167212902569087740241432556623919119752858299163160176439) := rfl
@[simp] theorem lookupL17_6 : candidateL (8, 1) (3, 0) = (38544840318680608596344222471960988288856594180151747115108409783075199354883 / 408226547718081001586087182327858203948653943238174791584832829724542984810000) := rfl
@[simp] theorem lookupL17_7 : candidateL (8, 1) (3, 1) = (-55118750512514822931122716164843675512464596241275120670099288500818835161838200347707 / 1000590046718285881806966108078132409756361790430723183262594706493643352661690561019305) := rfl
@[simp] theorem lookupL17_8 : candidateL (8, 1) (4, 0) = (13191938977594678218519497861692265368221727338269388475266987323171228934499738176626708158893503 / 414757042317679810946681367499965067516162605168537980968779866584389463553103385943912604183876800) := rfl
@[simp] theorem lookupL17_9 : candidateL (8, 1) (4, 1) = (-4237840845235985600761035371457920583525950615334422969261531932504583150165917655552903279378833726201517621 / 18921170648037905597939938894582197786773172430445851828089334224273923837384746034283145051085508624051423071) := rfl
@[simp] theorem lookupL17_10 : candidateL (8, 1) (5, 0) = (-23210612060735276931027440427856488867714944987227797960190206469159605966631860752833829305224456314563742329211887463 / 111314462503834026532162449639539465864483699277529582398208665149587024768911617294503971787784510839234576543012078450) := rfl
@[simp] theorem lookupL17_11 : candidateL (8, 1) (5, 1) = (13521841014089296228754530875272972801034635068865345485670797856679168863443486994475396978066840768851617039305735317369884085 / 55555687259742573065919815032071258797862960494181662550900135979761039092603372941166338011593146990562872511767719711455229454) := rfl
@[simp] theorem lookupL17_12 : candidateL (8, 1) (6, 0) = (62720327742467021068095539551266632784755984753101225827860866534215664388785229626922089452450959821346781556431639825184370593299041001 / 410132446332429501632535672717021675339157413624917542751719167462065638888295851459179438417839381925843833014813490615547089635216036690) := rfl
@[simp] theorem lookupL17_13 : candidateL (8, 1) (6, 1) = (-1247307248310016432833612247477529242451389183185611803221433134211454369473872613794921732650236190549760296945631452639876197913755394649455771348 / 2625398655755109579609881724170253949692212801167363854449402424606607962852276209306898110987869644710682823711674194378913090147084260257010314227) := rfl
@[simp] theorem lookupL17_14 : candidateL (8, 1) (7, 0) = (-834808114676104508206121457727760552289238108129731683372458143792070903699701375173230973908412065157274357125997217791081499268329672196994940164195280139 / 2019958340843593939067107053168426616385486658336978280185166955381682535338213048672388858081183680506278497746480550877849347402202805090177996448611096500) := rfl
@[simp] theorem lookupL17_15 : candidateL (8, 1) (7, 1) = (-565140030455754756675026479502823988093865376027672809806827293645206848936961500649745371378388195144484214788680188397075845590215510904582189402140467834705916708 / 1990337992458895867294451952088980138384735017470629157526423633247869321722325668662888026226959229679172056444281864658774656915653269259780794861472993455032172597) := rfl
@[simp] theorem lookupL17_16 : candidateL (8, 1) (8, 0) = (-9886251796206669302111004921942118609108930259438889958639486195807671154557451557479304339205709724119374554131485395865356982568740847732545183214812407200364272272178339 / 56440625889339966845174439474416232254008192089295953715041554457437236774420541814733586268242238979971415573499600283055121298766202709406402603291704898281943467024120500) := rfl
@[simp] theorem lookupL17_17 : candidateL (8, 1) (8, 1) = 1 := rfl
@[simp] theorem lookupD0 : candidateD (0, 0) = (1669415457 / 10000000000) := rfl
@[simp] theorem lookupD1 : candidateD (0, 1) = (27944851774172656807 / 222588727600000000000) := rfl
@[simp] theorem lookupD2 : candidateD (1, 0) = (15211675541777080840737921959207 / 134135288516028752673600000000000) := rfl
@[simp] theorem lookupD3 : candidateD (1, 1) = (661227798504720496816165525588695508877654521 / 24338680866843329345180675134731200000000000000) := rfl
@[simp] theorem lookupD4 : candidateD (2, 0) = (391110482672837022519033391565957222866880481962605291 / 6612277985047204968161655255886955088776545210000000000) := rfl
@[simp] theorem lookupD5 : candidateD (2, 1) = (8083500003167212902569087740241432556623919119752858299163160176439 / 625776772276539236030453426505531556587008771140168465600000000000000) := rfl
@[simp] theorem lookupD6 : candidateD (3, 0) = (122467964315424300475826154698357461184596182971452437475449848917362895443 / 3233400001266885161027635096096573022649567647901143319665264070575600000000) := rfl
@[simp] theorem lookupD7 : candidateD (3, 1) = (200118009343657176361393221615626481951272358086144636652518941298728670532338112203861 / 39189748580935776152264369503474387579070778550864779992143951653556126541760000000000000) := rfl
@[simp] theorem lookupD8 : candidateD (4, 0) = (259223151448549881841675854687478167197601628230336238105487416615243414720689616214945377614923 / 12507375583978573522587076350976655121954522380384039790782433831170541908271132012741312500000000) := rfl
@[simp] theorem lookupD9 : candidateD (4, 1) = (18921170648037905597939938894582197786773172430445851828089334224273923837384746034283145051085508624051423071 / 8295140846353596218933627349999301350323252103370759619375597331687789271062067718878252083677536000000000000000) := rfl
@[simp] theorem lookupD10 : candidateD (5, 0) = (2226289250076680530643248992790789317289673985550591647964173302991740495378232345890079435755690216784691530860241569 / 189211706480379055979399388945821977867731724304458518280893342242739238373847460342831450510855086240514230710000000000) := rfl
@[simp] theorem lookupD11 : candidateD (5, 1) = (27777843629871286532959907516035629398931480247090831275450067989880519546301686470583169005796573495281436255883859855727614727 / 22262892500766805306432489927907893172896739855505916479641733029917404953782323458900794357556902167846915308602415690000000000000) := rfl
@[simp] theorem lookupD12 : candidateD (6, 0) = (41013244633242950163253567271702167533915741362491754275171916746206563888829585145917943841783938192584383301481349061554708963521603669 / 11111137451948514613183963006414251759572592098836332510180027195952207818520674588233267602318629398112574502353543942291045890800000000000) := rfl
@[simp] theorem lookupD13 : candidateD (6, 1) = (2625398655755109579609881724170253949692212801167363854449402424606607962852276209306898110987869644710682823711674194378913090147084260257010314227 / 13124238282637744052241141526944693610853037235997361368055013358786100444425467246693742029370860221627002656474031699697506868326913174080000000000000) := rfl
@[simp] theorem lookupD14 : candidateD (7, 0) = (4039916681687187878134214106336853232770973316673956560370333910763365070676426097344777716162367361012556995492961101755698694804405610180355992897222193 / 5250797311510219159219763448340507899384425602334727708898804849213215925704552418613796221975739289421365647423348388757826180294168520514020628454000000000) := rfl
@[simp] theorem lookupD15 : candidateD (7, 1) = (1990337992458895867294451952088980138384735017470629157526423633247869321722325668662888026226959229679172056444281864658774656915653269259780794861472993455032172597 / 32319333453497503025073712850694825862167786533391652482962671286106920565411408778758221729298938888100455963943688814045589558435244881442847943177777544000000000000000) := rfl
@[simp] theorem lookupD16 : candidateD (8, 0) = (112881251778679933690348878948832464508016384178591907430083108914874473548841083629467172536484477959942831146999200566110242597532405418812805206583409796563886934048241 / 1990337992458895867294451952088980138384735017470629157526423633247869321722325668662888026226959229679172056444281864658774656915653269259780794861472993455032172597000000000) := rfl
@[simp] theorem lookupD17 : candidateD (8, 1) = (234534123787698546519185838947619433477400591778437815196821243397264919157855372792885525460585820069772761354958136828901075096067799744986136531899430902847513971692054503649021 / 14110156472334991711293609868604058063502048022323988428760388614359309193605135453683396567060559744992853893374900070763780324691550677351600650822926224570485866756030125000000000000) := rfl

-- Normalize concrete successor coordinates produced by finite-sum expansion.
@[simp] theorem lookupFinSucc1_0 : Fin.succ (0 : Fin 1) = (1 : Fin 2) := rfl
@[simp] theorem lookupFinSucc2_0 : Fin.succ (0 : Fin 2) = (1 : Fin 3) := rfl
@[simp] theorem lookupFinSucc2_1 : Fin.succ (1 : Fin 2) = (2 : Fin 3) := rfl
@[simp] theorem lookupFinSucc3_0 : Fin.succ (0 : Fin 3) = (1 : Fin 4) := rfl
@[simp] theorem lookupFinSucc3_1 : Fin.succ (1 : Fin 3) = (2 : Fin 4) := rfl
@[simp] theorem lookupFinSucc3_2 : Fin.succ (2 : Fin 3) = (3 : Fin 4) := rfl
@[simp] theorem lookupFinSucc4_0 : Fin.succ (0 : Fin 4) = (1 : Fin 5) := rfl
@[simp] theorem lookupFinSucc4_1 : Fin.succ (1 : Fin 4) = (2 : Fin 5) := rfl
@[simp] theorem lookupFinSucc4_2 : Fin.succ (2 : Fin 4) = (3 : Fin 5) := rfl
@[simp] theorem lookupFinSucc4_3 : Fin.succ (3 : Fin 4) = (4 : Fin 5) := rfl
@[simp] theorem lookupFinSucc5_0 : Fin.succ (0 : Fin 5) = (1 : Fin 6) := rfl
@[simp] theorem lookupFinSucc5_1 : Fin.succ (1 : Fin 5) = (2 : Fin 6) := rfl
@[simp] theorem lookupFinSucc5_2 : Fin.succ (2 : Fin 5) = (3 : Fin 6) := rfl
@[simp] theorem lookupFinSucc5_3 : Fin.succ (3 : Fin 5) = (4 : Fin 6) := rfl
@[simp] theorem lookupFinSucc5_4 : Fin.succ (4 : Fin 5) = (5 : Fin 6) := rfl
@[simp] theorem lookupFinSucc6_0 : Fin.succ (0 : Fin 6) = (1 : Fin 7) := rfl
@[simp] theorem lookupFinSucc6_1 : Fin.succ (1 : Fin 6) = (2 : Fin 7) := rfl
@[simp] theorem lookupFinSucc6_2 : Fin.succ (2 : Fin 6) = (3 : Fin 7) := rfl
@[simp] theorem lookupFinSucc6_3 : Fin.succ (3 : Fin 6) = (4 : Fin 7) := rfl
@[simp] theorem lookupFinSucc6_4 : Fin.succ (4 : Fin 6) = (5 : Fin 7) := rfl
@[simp] theorem lookupFinSucc6_5 : Fin.succ (5 : Fin 6) = (6 : Fin 7) := rfl
@[simp] theorem lookupFinSucc7_0 : Fin.succ (0 : Fin 7) = (1 : Fin 8) := rfl
@[simp] theorem lookupFinSucc7_1 : Fin.succ (1 : Fin 7) = (2 : Fin 8) := rfl
@[simp] theorem lookupFinSucc7_2 : Fin.succ (2 : Fin 7) = (3 : Fin 8) := rfl
@[simp] theorem lookupFinSucc7_3 : Fin.succ (3 : Fin 7) = (4 : Fin 8) := rfl
@[simp] theorem lookupFinSucc7_4 : Fin.succ (4 : Fin 7) = (5 : Fin 8) := rfl
@[simp] theorem lookupFinSucc7_5 : Fin.succ (5 : Fin 7) = (6 : Fin 8) := rfl
@[simp] theorem lookupFinSucc7_6 : Fin.succ (6 : Fin 7) = (7 : Fin 8) := rfl
@[simp] theorem lookupFinSucc8_0 : Fin.succ (0 : Fin 8) = (1 : Fin 9) := rfl
@[simp] theorem lookupFinSucc8_1 : Fin.succ (1 : Fin 8) = (2 : Fin 9) := rfl
@[simp] theorem lookupFinSucc8_2 : Fin.succ (2 : Fin 8) = (3 : Fin 9) := rfl
@[simp] theorem lookupFinSucc8_3 : Fin.succ (3 : Fin 8) = (4 : Fin 9) := rfl
@[simp] theorem lookupFinSucc8_4 : Fin.succ (4 : Fin 8) = (5 : Fin 9) := rfl
@[simp] theorem lookupFinSucc8_5 : Fin.succ (5 : Fin 8) = (6 : Fin 9) := rfl
@[simp] theorem lookupFinSucc8_6 : Fin.succ (6 : Fin 8) = (7 : Fin 9) := rfl
@[simp] theorem lookupFinSucc8_7 : Fin.succ (7 : Fin 8) = (8 : Fin 9) := rfl

-- Normalize constructor coordinates emitted by fin_cases.
@[simp] theorem lookupFinMk1_0 (h : 0 < 1) : (⟨0, h⟩ : Fin 1) = 0 := rfl
@[simp] theorem lookupFinMk2_0 (h : 0 < 2) : (⟨0, h⟩ : Fin 2) = 0 := rfl
@[simp] theorem lookupFinMk2_1 (h : 1 < 2) : (⟨1, h⟩ : Fin 2) = 1 := rfl
@[simp] theorem lookupFinMk3_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem lookupFinMk3_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem lookupFinMk3_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem lookupFinMk4_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem lookupFinMk4_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem lookupFinMk4_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem lookupFinMk4_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem lookupFinMk5_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem lookupFinMk5_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem lookupFinMk5_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem lookupFinMk5_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem lookupFinMk5_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem lookupFinMk6_0 (h : 0 < 6) : (⟨0, h⟩ : Fin 6) = 0 := rfl
@[simp] theorem lookupFinMk6_1 (h : 1 < 6) : (⟨1, h⟩ : Fin 6) = 1 := rfl
@[simp] theorem lookupFinMk6_2 (h : 2 < 6) : (⟨2, h⟩ : Fin 6) = 2 := rfl
@[simp] theorem lookupFinMk6_3 (h : 3 < 6) : (⟨3, h⟩ : Fin 6) = 3 := rfl
@[simp] theorem lookupFinMk6_4 (h : 4 < 6) : (⟨4, h⟩ : Fin 6) = 4 := rfl
@[simp] theorem lookupFinMk6_5 (h : 5 < 6) : (⟨5, h⟩ : Fin 6) = 5 := rfl
@[simp] theorem lookupFinMk7_0 (h : 0 < 7) : (⟨0, h⟩ : Fin 7) = 0 := rfl
@[simp] theorem lookupFinMk7_1 (h : 1 < 7) : (⟨1, h⟩ : Fin 7) = 1 := rfl
@[simp] theorem lookupFinMk7_2 (h : 2 < 7) : (⟨2, h⟩ : Fin 7) = 2 := rfl
@[simp] theorem lookupFinMk7_3 (h : 3 < 7) : (⟨3, h⟩ : Fin 7) = 3 := rfl
@[simp] theorem lookupFinMk7_4 (h : 4 < 7) : (⟨4, h⟩ : Fin 7) = 4 := rfl
@[simp] theorem lookupFinMk7_5 (h : 5 < 7) : (⟨5, h⟩ : Fin 7) = 5 := rfl
@[simp] theorem lookupFinMk7_6 (h : 6 < 7) : (⟨6, h⟩ : Fin 7) = 6 := rfl
@[simp] theorem lookupFinMk8_0 (h : 0 < 8) : (⟨0, h⟩ : Fin 8) = 0 := rfl
@[simp] theorem lookupFinMk8_1 (h : 1 < 8) : (⟨1, h⟩ : Fin 8) = 1 := rfl
@[simp] theorem lookupFinMk8_2 (h : 2 < 8) : (⟨2, h⟩ : Fin 8) = 2 := rfl
@[simp] theorem lookupFinMk8_3 (h : 3 < 8) : (⟨3, h⟩ : Fin 8) = 3 := rfl
@[simp] theorem lookupFinMk8_4 (h : 4 < 8) : (⟨4, h⟩ : Fin 8) = 4 := rfl
@[simp] theorem lookupFinMk8_5 (h : 5 < 8) : (⟨5, h⟩ : Fin 8) = 5 := rfl
@[simp] theorem lookupFinMk8_6 (h : 6 < 8) : (⟨6, h⟩ : Fin 8) = 6 := rfl
@[simp] theorem lookupFinMk8_7 (h : 7 < 8) : (⟨7, h⟩ : Fin 8) = 7 := rfl
@[simp] theorem lookupFinMk9_0 (h : 0 < 9) : (⟨0, h⟩ : Fin 9) = 0 := rfl
@[simp] theorem lookupFinMk9_1 (h : 1 < 9) : (⟨1, h⟩ : Fin 9) = 1 := rfl
@[simp] theorem lookupFinMk9_2 (h : 2 < 9) : (⟨2, h⟩ : Fin 9) = 2 := rfl
@[simp] theorem lookupFinMk9_3 (h : 3 < 9) : (⟨3, h⟩ : Fin 9) = 3 := rfl
@[simp] theorem lookupFinMk9_4 (h : 4 < 9) : (⟨4, h⟩ : Fin 9) = 4 := rfl
@[simp] theorem lookupFinMk9_5 (h : 5 < 9) : (⟨5, h⟩ : Fin 9) = 5 := rfl
@[simp] theorem lookupFinMk9_6 (h : 6 < 9) : (⟨6, h⟩ : Fin 9) = 6 := rfl
@[simp] theorem lookupFinMk9_7 (h : 7 < 9) : (⟨7, h⟩ : Fin 9) = 7 := rfl
@[simp] theorem lookupFinMk9_8 (h : 8 < 9) : (⟨8, h⟩ : Fin 9) = 8 := rfl

end ADMM.FiniteMemory.Reconstruction.Pilot
