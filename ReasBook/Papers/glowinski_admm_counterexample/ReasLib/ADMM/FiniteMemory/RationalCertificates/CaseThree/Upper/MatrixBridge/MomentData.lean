module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Upper.MatrixBridge.Data
@[expose] public section
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.MatrixBridge
def literalMomentFData : List (List ℚ) := [
  [(105005401 / 10000000000), (105005401 / 10000000000), (5699909 / 625000000), (-13806857 / 10000000000), (22923001 / 10000000000), (-68275543 / 10000000000), (18999147 / 10000000000), (-1961927 / 5000000000), (6181801 / 10000000000), (-6408673 / 5000000000), (5709449 / 10000000000), (-14761 / 312500000), (379209 / 1250000000), (-2675777 / 10000000000), (2199651 / 10000000000), (-834021 / 10000000000), 0, (-2199651 / 10000000000)],
  [(-403529713 / 10000000000), (-403529713 / 10000000000), (32761939 / 2000000000), (35458713 / 625000000), (59793277 / 5000000000), (-44223141 / 10000000000), (23848857 / 10000000000), (-95737697 / 10000000000), (7793377 / 10000000000), (-401387 / 250000000), (7176697 / 10000000000), (-15417 / 250000000), (580553 / 2500000000), (-970897 / 2000000000), (555927 / 2500000000), (-12313 / 1250000000), 0, (-555927 / 2500000000)],
  [(23169389 / 1000000000), (23169389 / 1000000000), (-2094067 / 40000000), (-9440133 / 125000000), (5460939 / 2500000000), (272680253 / 5000000000), (18518129 / 1250000000), (31575319 / 2500000000), (503167 / 1000000000), (-71556681 / 5000000000), (9815001 / 10000000000), (4783331 / 10000000000), (2722623 / 10000000000), (-3546189 / 5000000000), (485617 / 2500000000), (-156031 / 2000000000), 0, (-485617 / 2500000000)],
  [(242211 / 62500000), (242211 / 62500000), (88466103 / 5000000000), (69089223 / 5000000000), (-17185253 / 625000000), (-225948127 / 5000000000), (433873 / 1250000000), (34804379 / 1250000000), (102953 / 100000000), (1706079 / 2500000000), (89 / 625000), (-88713 / 100000000), (311281 / 1250000000), (133281 / 1250000000), (584671 / 5000000000), (-660453 / 5000000000), 0, (-584671 / 5000000000)],
  [(9204501 / 10000000000), (9204501 / 10000000000), (54530779 / 10000000000), (22663139 / 5000000000), (5229403 / 2500000000), (-33613167 / 10000000000), (-15078531 / 1250000000), (-7077293 / 500000000), (312651 / 2000000000), (122191503 / 10000000000), (10805409 / 10000000000), (4621077 / 5000000000), (742051 / 10000000000), (-5031679 / 5000000000), (256983 / 1250000000), (1313813 / 10000000000), 0, (-256983 / 1250000000)],
  [(7413091 / 10000000000), (7413091 / 10000000000), (2106727 / 1250000000), (377629 / 400000000), (27388417 / 10000000000), (10534601 / 10000000000), (888253 / 2500000000), (-4767081 / 2000000000), (-71548197 / 10000000000), (-75101209 / 10000000000), (345639 / 5000000000), (2889579 / 400000000), (322171 / 625000000), (2231729 / 5000000000), (196413 / 5000000000), (-476191 / 1000000000), 0, (-196413 / 5000000000)],
  [(2159969 / 10000000000), (2159969 / 10000000000), (6502209 / 10000000000), (27139 / 62500000), (4115043 / 10000000000), (-1193583 / 5000000000), (13131617 / 10000000000), (4508287 / 5000000000), (1516317 / 10000000000), (-116153 / 100000000), (-36016513 / 10000000000), (-3753283 / 1000000000), (75843 / 2000000000), (2274733 / 625000000), (2147917 / 5000000000), (3916619 / 10000000000), 0, (-2147917 / 5000000000)],
  [(573931 / 2500000000), (573931 / 2500000000), (3150297 / 10000000000), (854573 / 10000000000), (698727 / 2500000000), (-355389 / 10000000000), (1474381 / 2000000000), (4576997 / 10000000000), (213407 / 200000000), (659689 / 2000000000), (101599 / 1250000000), (-4928779 / 5000000000), (-15189519 / 5000000000), (-3119183 / 1000000000), (261363 / 10000000000), (30640401 / 10000000000), 0, (-261363 / 10000000000)],
  [(1293719 / 10000000000), (1293719 / 10000000000), (4829589 / 10000000000), (353587 / 1000000000), (842743 / 5000000000), (-3144103 / 10000000000), (2487537 / 10000000000), (802051 / 10000000000), (468387 / 2500000000), (-613989 / 10000000000), (2957297 / 10000000000), (1083749 / 10000000000), (356899 / 10000000000), (-1300199 / 5000000000), (-18504381 / 10000000000), (-117883 / 62500000), 0, (18504381 / 10000000000)]
]

def literalMomentJData : List (List ℚ) := [
  [(78495581 / 5000000000), 0, (41894129 / 5000000000), 0, (4970899 / 5000000000), 0, (1253821 / 2500000000), 0, (2049317 / 10000000000), 0, (587757 / 5000000000), 0, (74951 / 1000000000), 0, (84579 / 2000000000), 0, 0, 0],
  [(-1959398911 / 7500000000), 0, (7215811393 / 30000000000), 0, (3619507 / 2500000000), 0, (3327591 / 5000000000), 0, (2393681 / 10000000000), 0, (1347161 / 10000000000), 0, (83473 / 1000000000), 0, (58061 / 1250000000), 0, 0, 0],
  [(47102027 / 5000000000), 0, (-10315609 / 625000000), 0, (18206181 / 10000000000), 0, (7683879 / 10000000000), 0, (269183 / 1000000000), 0, (1400941 / 10000000000), 0, (87131 / 1000000000), 0, (470191 / 10000000000), 0, 0, 0],
  [(43384997 / 10000000000), 0, (57582303 / 5000000000), 0, (-99259629 / 5000000000), 0, (2873453 / 2000000000), 0, (1013963 / 2000000000), 0, (934813 / 5000000000), 0, (1095443 / 10000000000), 0, (549261 / 10000000000), 0, 0, 0],
  [(10289209 / 5000000000), 0, (35475149 / 10000000000), 0, (6585663 / 1250000000), 0, (-131676511 / 10000000000), 0, (697981 / 1000000000), 0, (421609 / 1250000000), 0, (701429 / 5000000000), 0, (174191 / 2500000000), 0, 0, 0],
  [(11032487 / 10000000000), 0, (15897243 / 10000000000), 0, (6268689 / 2000000000), 0, (11412823 / 5000000000), 0, (-48369957 / 5000000000), 0, (532317 / 1250000000), 0, (821387 / 2500000000), 0, (234883 / 2500000000), 0, 0, 0],
  [(8574799 / 10000000000), 0, (1182189 / 1250000000), 0, (7523557 / 5000000000), 0, (608621 / 400000000), 0, (15958847 / 10000000000), 0, (-19169423 / 2500000000), 0, (3794283 / 10000000000), 0, (3278167 / 10000000000), 0, 0, 0],
  [(5517779 / 10000000000), 0, (3890951 / 5000000000), 0, (1742899 / 2500000000), 0, (10055521 / 10000000000), 0, (5645671 / 5000000000), 0, (2547257 / 2000000000), 0, (-31320069 / 5000000000), 0, (4516119 / 10000000000), 0, 0, 0],
  [(130089 / 1250000000), 0, (1127977 / 10000000000), 0, (637551 / 5000000000), 0, (257699 / 2000000000), 0, (1735709 / 10000000000), 0, (975219 / 5000000000), 0, (2041181 / 10000000000), 0, (-11338327 / 10000000000), 0, 0, 0]
]

def literalMoment (b : Block) (d : Option (Fin 8)) (i : Fin 9 × Fin 2) : ℚ :=
  let data := match b with | .F => literalMomentFData | .J => literalMomentJData
  (data.getD (Computation.optionIndex d).val []).getD (coordinateRank i) 0
@[simp] theorem lookup_moment_F_0_0 : literalMoment .F none (0, 0) = (105005401 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_0_1 : literalMoment .F none (0, 1) = (105005401 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_0_2 : literalMoment .F none (1, 0) = (5699909 / 625000000) := rfl
@[simp] theorem lookup_moment_F_0_3 : literalMoment .F none (1, 1) = (-13806857 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_0_4 : literalMoment .F none (2, 0) = (22923001 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_0_5 : literalMoment .F none (2, 1) = (-68275543 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_0_6 : literalMoment .F none (3, 0) = (18999147 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_0_7 : literalMoment .F none (3, 1) = (-1961927 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_0_8 : literalMoment .F none (4, 0) = (6181801 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_0_9 : literalMoment .F none (4, 1) = (-6408673 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_0_10 : literalMoment .F none (5, 0) = (5709449 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_0_11 : literalMoment .F none (5, 1) = (-14761 / 312500000) := rfl
@[simp] theorem lookup_moment_F_0_12 : literalMoment .F none (6, 0) = (379209 / 1250000000) := rfl
@[simp] theorem lookup_moment_F_0_13 : literalMoment .F none (6, 1) = (-2675777 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_0_14 : literalMoment .F none (7, 0) = (2199651 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_0_15 : literalMoment .F none (7, 1) = (-834021 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_0_16 : literalMoment .F none (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_0_17 : literalMoment .F none (8, 1) = (-2199651 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_1_0 : literalMoment .F (some 0) (0, 0) = (-403529713 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_1_1 : literalMoment .F (some 0) (0, 1) = (-403529713 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_1_2 : literalMoment .F (some 0) (1, 0) = (32761939 / 2000000000) := rfl
@[simp] theorem lookup_moment_F_1_3 : literalMoment .F (some 0) (1, 1) = (35458713 / 625000000) := rfl
@[simp] theorem lookup_moment_F_1_4 : literalMoment .F (some 0) (2, 0) = (59793277 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_1_5 : literalMoment .F (some 0) (2, 1) = (-44223141 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_1_6 : literalMoment .F (some 0) (3, 0) = (23848857 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_1_7 : literalMoment .F (some 0) (3, 1) = (-95737697 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_1_8 : literalMoment .F (some 0) (4, 0) = (7793377 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_1_9 : literalMoment .F (some 0) (4, 1) = (-401387 / 250000000) := rfl
@[simp] theorem lookup_moment_F_1_10 : literalMoment .F (some 0) (5, 0) = (7176697 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_1_11 : literalMoment .F (some 0) (5, 1) = (-15417 / 250000000) := rfl
@[simp] theorem lookup_moment_F_1_12 : literalMoment .F (some 0) (6, 0) = (580553 / 2500000000) := rfl
@[simp] theorem lookup_moment_F_1_13 : literalMoment .F (some 0) (6, 1) = (-970897 / 2000000000) := rfl
@[simp] theorem lookup_moment_F_1_14 : literalMoment .F (some 0) (7, 0) = (555927 / 2500000000) := rfl
@[simp] theorem lookup_moment_F_1_15 : literalMoment .F (some 0) (7, 1) = (-12313 / 1250000000) := rfl
@[simp] theorem lookup_moment_F_1_16 : literalMoment .F (some 0) (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_1_17 : literalMoment .F (some 0) (8, 1) = (-555927 / 2500000000) := rfl
@[simp] theorem lookup_moment_F_2_0 : literalMoment .F (some 1) (0, 0) = (23169389 / 1000000000) := rfl
@[simp] theorem lookup_moment_F_2_1 : literalMoment .F (some 1) (0, 1) = (23169389 / 1000000000) := rfl
@[simp] theorem lookup_moment_F_2_2 : literalMoment .F (some 1) (1, 0) = (-2094067 / 40000000) := rfl
@[simp] theorem lookup_moment_F_2_3 : literalMoment .F (some 1) (1, 1) = (-9440133 / 125000000) := rfl
@[simp] theorem lookup_moment_F_2_4 : literalMoment .F (some 1) (2, 0) = (5460939 / 2500000000) := rfl
@[simp] theorem lookup_moment_F_2_5 : literalMoment .F (some 1) (2, 1) = (272680253 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_2_6 : literalMoment .F (some 1) (3, 0) = (18518129 / 1250000000) := rfl
@[simp] theorem lookup_moment_F_2_7 : literalMoment .F (some 1) (3, 1) = (31575319 / 2500000000) := rfl
@[simp] theorem lookup_moment_F_2_8 : literalMoment .F (some 1) (4, 0) = (503167 / 1000000000) := rfl
@[simp] theorem lookup_moment_F_2_9 : literalMoment .F (some 1) (4, 1) = (-71556681 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_2_10 : literalMoment .F (some 1) (5, 0) = (9815001 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_2_11 : literalMoment .F (some 1) (5, 1) = (4783331 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_2_12 : literalMoment .F (some 1) (6, 0) = (2722623 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_2_13 : literalMoment .F (some 1) (6, 1) = (-3546189 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_2_14 : literalMoment .F (some 1) (7, 0) = (485617 / 2500000000) := rfl
@[simp] theorem lookup_moment_F_2_15 : literalMoment .F (some 1) (7, 1) = (-156031 / 2000000000) := rfl
@[simp] theorem lookup_moment_F_2_16 : literalMoment .F (some 1) (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_2_17 : literalMoment .F (some 1) (8, 1) = (-485617 / 2500000000) := rfl
@[simp] theorem lookup_moment_F_3_0 : literalMoment .F (some 2) (0, 0) = (242211 / 62500000) := rfl
@[simp] theorem lookup_moment_F_3_1 : literalMoment .F (some 2) (0, 1) = (242211 / 62500000) := rfl
@[simp] theorem lookup_moment_F_3_2 : literalMoment .F (some 2) (1, 0) = (88466103 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_3_3 : literalMoment .F (some 2) (1, 1) = (69089223 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_3_4 : literalMoment .F (some 2) (2, 0) = (-17185253 / 625000000) := rfl
@[simp] theorem lookup_moment_F_3_5 : literalMoment .F (some 2) (2, 1) = (-225948127 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_3_6 : literalMoment .F (some 2) (3, 0) = (433873 / 1250000000) := rfl
@[simp] theorem lookup_moment_F_3_7 : literalMoment .F (some 2) (3, 1) = (34804379 / 1250000000) := rfl
@[simp] theorem lookup_moment_F_3_8 : literalMoment .F (some 2) (4, 0) = (102953 / 100000000) := rfl
@[simp] theorem lookup_moment_F_3_9 : literalMoment .F (some 2) (4, 1) = (1706079 / 2500000000) := rfl
@[simp] theorem lookup_moment_F_3_10 : literalMoment .F (some 2) (5, 0) = (89 / 625000) := rfl
@[simp] theorem lookup_moment_F_3_11 : literalMoment .F (some 2) (5, 1) = (-88713 / 100000000) := rfl
@[simp] theorem lookup_moment_F_3_12 : literalMoment .F (some 2) (6, 0) = (311281 / 1250000000) := rfl
@[simp] theorem lookup_moment_F_3_13 : literalMoment .F (some 2) (6, 1) = (133281 / 1250000000) := rfl
@[simp] theorem lookup_moment_F_3_14 : literalMoment .F (some 2) (7, 0) = (584671 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_3_15 : literalMoment .F (some 2) (7, 1) = (-660453 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_3_16 : literalMoment .F (some 2) (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_3_17 : literalMoment .F (some 2) (8, 1) = (-584671 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_4_0 : literalMoment .F (some 3) (0, 0) = (9204501 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_4_1 : literalMoment .F (some 3) (0, 1) = (9204501 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_4_2 : literalMoment .F (some 3) (1, 0) = (54530779 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_4_3 : literalMoment .F (some 3) (1, 1) = (22663139 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_4_4 : literalMoment .F (some 3) (2, 0) = (5229403 / 2500000000) := rfl
@[simp] theorem lookup_moment_F_4_5 : literalMoment .F (some 3) (2, 1) = (-33613167 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_4_6 : literalMoment .F (some 3) (3, 0) = (-15078531 / 1250000000) := rfl
@[simp] theorem lookup_moment_F_4_7 : literalMoment .F (some 3) (3, 1) = (-7077293 / 500000000) := rfl
@[simp] theorem lookup_moment_F_4_8 : literalMoment .F (some 3) (4, 0) = (312651 / 2000000000) := rfl
@[simp] theorem lookup_moment_F_4_9 : literalMoment .F (some 3) (4, 1) = (122191503 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_4_10 : literalMoment .F (some 3) (5, 0) = (10805409 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_4_11 : literalMoment .F (some 3) (5, 1) = (4621077 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_4_12 : literalMoment .F (some 3) (6, 0) = (742051 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_4_13 : literalMoment .F (some 3) (6, 1) = (-5031679 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_4_14 : literalMoment .F (some 3) (7, 0) = (256983 / 1250000000) := rfl
@[simp] theorem lookup_moment_F_4_15 : literalMoment .F (some 3) (7, 1) = (1313813 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_4_16 : literalMoment .F (some 3) (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_4_17 : literalMoment .F (some 3) (8, 1) = (-256983 / 1250000000) := rfl
@[simp] theorem lookup_moment_F_5_0 : literalMoment .F (some 4) (0, 0) = (7413091 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_5_1 : literalMoment .F (some 4) (0, 1) = (7413091 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_5_2 : literalMoment .F (some 4) (1, 0) = (2106727 / 1250000000) := rfl
@[simp] theorem lookup_moment_F_5_3 : literalMoment .F (some 4) (1, 1) = (377629 / 400000000) := rfl
@[simp] theorem lookup_moment_F_5_4 : literalMoment .F (some 4) (2, 0) = (27388417 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_5_5 : literalMoment .F (some 4) (2, 1) = (10534601 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_5_6 : literalMoment .F (some 4) (3, 0) = (888253 / 2500000000) := rfl
@[simp] theorem lookup_moment_F_5_7 : literalMoment .F (some 4) (3, 1) = (-4767081 / 2000000000) := rfl
@[simp] theorem lookup_moment_F_5_8 : literalMoment .F (some 4) (4, 0) = (-71548197 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_5_9 : literalMoment .F (some 4) (4, 1) = (-75101209 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_5_10 : literalMoment .F (some 4) (5, 0) = (345639 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_5_11 : literalMoment .F (some 4) (5, 1) = (2889579 / 400000000) := rfl
@[simp] theorem lookup_moment_F_5_12 : literalMoment .F (some 4) (6, 0) = (322171 / 625000000) := rfl
@[simp] theorem lookup_moment_F_5_13 : literalMoment .F (some 4) (6, 1) = (2231729 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_5_14 : literalMoment .F (some 4) (7, 0) = (196413 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_5_15 : literalMoment .F (some 4) (7, 1) = (-476191 / 1000000000) := rfl
@[simp] theorem lookup_moment_F_5_16 : literalMoment .F (some 4) (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_5_17 : literalMoment .F (some 4) (8, 1) = (-196413 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_6_0 : literalMoment .F (some 5) (0, 0) = (2159969 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_6_1 : literalMoment .F (some 5) (0, 1) = (2159969 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_6_2 : literalMoment .F (some 5) (1, 0) = (6502209 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_6_3 : literalMoment .F (some 5) (1, 1) = (27139 / 62500000) := rfl
@[simp] theorem lookup_moment_F_6_4 : literalMoment .F (some 5) (2, 0) = (4115043 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_6_5 : literalMoment .F (some 5) (2, 1) = (-1193583 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_6_6 : literalMoment .F (some 5) (3, 0) = (13131617 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_6_7 : literalMoment .F (some 5) (3, 1) = (4508287 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_6_8 : literalMoment .F (some 5) (4, 0) = (1516317 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_6_9 : literalMoment .F (some 5) (4, 1) = (-116153 / 100000000) := rfl
@[simp] theorem lookup_moment_F_6_10 : literalMoment .F (some 5) (5, 0) = (-36016513 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_6_11 : literalMoment .F (some 5) (5, 1) = (-3753283 / 1000000000) := rfl
@[simp] theorem lookup_moment_F_6_12 : literalMoment .F (some 5) (6, 0) = (75843 / 2000000000) := rfl
@[simp] theorem lookup_moment_F_6_13 : literalMoment .F (some 5) (6, 1) = (2274733 / 625000000) := rfl
@[simp] theorem lookup_moment_F_6_14 : literalMoment .F (some 5) (7, 0) = (2147917 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_6_15 : literalMoment .F (some 5) (7, 1) = (3916619 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_6_16 : literalMoment .F (some 5) (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_6_17 : literalMoment .F (some 5) (8, 1) = (-2147917 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_7_0 : literalMoment .F (some 6) (0, 0) = (573931 / 2500000000) := rfl
@[simp] theorem lookup_moment_F_7_1 : literalMoment .F (some 6) (0, 1) = (573931 / 2500000000) := rfl
@[simp] theorem lookup_moment_F_7_2 : literalMoment .F (some 6) (1, 0) = (3150297 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_7_3 : literalMoment .F (some 6) (1, 1) = (854573 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_7_4 : literalMoment .F (some 6) (2, 0) = (698727 / 2500000000) := rfl
@[simp] theorem lookup_moment_F_7_5 : literalMoment .F (some 6) (2, 1) = (-355389 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_7_6 : literalMoment .F (some 6) (3, 0) = (1474381 / 2000000000) := rfl
@[simp] theorem lookup_moment_F_7_7 : literalMoment .F (some 6) (3, 1) = (4576997 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_7_8 : literalMoment .F (some 6) (4, 0) = (213407 / 200000000) := rfl
@[simp] theorem lookup_moment_F_7_9 : literalMoment .F (some 6) (4, 1) = (659689 / 2000000000) := rfl
@[simp] theorem lookup_moment_F_7_10 : literalMoment .F (some 6) (5, 0) = (101599 / 1250000000) := rfl
@[simp] theorem lookup_moment_F_7_11 : literalMoment .F (some 6) (5, 1) = (-4928779 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_7_12 : literalMoment .F (some 6) (6, 0) = (-15189519 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_7_13 : literalMoment .F (some 6) (6, 1) = (-3119183 / 1000000000) := rfl
@[simp] theorem lookup_moment_F_7_14 : literalMoment .F (some 6) (7, 0) = (261363 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_7_15 : literalMoment .F (some 6) (7, 1) = (30640401 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_7_16 : literalMoment .F (some 6) (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_7_17 : literalMoment .F (some 6) (8, 1) = (-261363 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_8_0 : literalMoment .F (some 7) (0, 0) = (1293719 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_8_1 : literalMoment .F (some 7) (0, 1) = (1293719 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_8_2 : literalMoment .F (some 7) (1, 0) = (4829589 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_8_3 : literalMoment .F (some 7) (1, 1) = (353587 / 1000000000) := rfl
@[simp] theorem lookup_moment_F_8_4 : literalMoment .F (some 7) (2, 0) = (842743 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_8_5 : literalMoment .F (some 7) (2, 1) = (-3144103 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_8_6 : literalMoment .F (some 7) (3, 0) = (2487537 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_8_7 : literalMoment .F (some 7) (3, 1) = (802051 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_8_8 : literalMoment .F (some 7) (4, 0) = (468387 / 2500000000) := rfl
@[simp] theorem lookup_moment_F_8_9 : literalMoment .F (some 7) (4, 1) = (-613989 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_8_10 : literalMoment .F (some 7) (5, 0) = (2957297 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_8_11 : literalMoment .F (some 7) (5, 1) = (1083749 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_8_12 : literalMoment .F (some 7) (6, 0) = (356899 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_8_13 : literalMoment .F (some 7) (6, 1) = (-1300199 / 5000000000) := rfl
@[simp] theorem lookup_moment_F_8_14 : literalMoment .F (some 7) (7, 0) = (-18504381 / 10000000000) := rfl
@[simp] theorem lookup_moment_F_8_15 : literalMoment .F (some 7) (7, 1) = (-117883 / 62500000) := rfl
@[simp] theorem lookup_moment_F_8_16 : literalMoment .F (some 7) (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_F_8_17 : literalMoment .F (some 7) (8, 1) = (18504381 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_0_0 : literalMoment .J none (0, 0) = (78495581 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_0_1 : literalMoment .J none (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_0_2 : literalMoment .J none (1, 0) = (41894129 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_0_3 : literalMoment .J none (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_0_4 : literalMoment .J none (2, 0) = (4970899 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_0_5 : literalMoment .J none (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_0_6 : literalMoment .J none (3, 0) = (1253821 / 2500000000) := rfl
@[simp] theorem lookup_moment_J_0_7 : literalMoment .J none (3, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_0_8 : literalMoment .J none (4, 0) = (2049317 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_0_9 : literalMoment .J none (4, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_0_10 : literalMoment .J none (5, 0) = (587757 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_0_11 : literalMoment .J none (5, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_0_12 : literalMoment .J none (6, 0) = (74951 / 1000000000) := rfl
@[simp] theorem lookup_moment_J_0_13 : literalMoment .J none (6, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_0_14 : literalMoment .J none (7, 0) = (84579 / 2000000000) := rfl
@[simp] theorem lookup_moment_J_0_15 : literalMoment .J none (7, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_0_16 : literalMoment .J none (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_0_17 : literalMoment .J none (8, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_0 : literalMoment .J (some 0) (0, 0) = (-1959398911 / 7500000000) := rfl
@[simp] theorem lookup_moment_J_1_1 : literalMoment .J (some 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_2 : literalMoment .J (some 0) (1, 0) = (7215811393 / 30000000000) := rfl
@[simp] theorem lookup_moment_J_1_3 : literalMoment .J (some 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_4 : literalMoment .J (some 0) (2, 0) = (3619507 / 2500000000) := rfl
@[simp] theorem lookup_moment_J_1_5 : literalMoment .J (some 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_6 : literalMoment .J (some 0) (3, 0) = (3327591 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_1_7 : literalMoment .J (some 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_8 : literalMoment .J (some 0) (4, 0) = (2393681 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_1_9 : literalMoment .J (some 0) (4, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_10 : literalMoment .J (some 0) (5, 0) = (1347161 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_1_11 : literalMoment .J (some 0) (5, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_12 : literalMoment .J (some 0) (6, 0) = (83473 / 1000000000) := rfl
@[simp] theorem lookup_moment_J_1_13 : literalMoment .J (some 0) (6, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_14 : literalMoment .J (some 0) (7, 0) = (58061 / 1250000000) := rfl
@[simp] theorem lookup_moment_J_1_15 : literalMoment .J (some 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_1_16 : literalMoment .J (some 0) (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_1_17 : literalMoment .J (some 0) (8, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_0 : literalMoment .J (some 1) (0, 0) = (47102027 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_2_1 : literalMoment .J (some 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_2 : literalMoment .J (some 1) (1, 0) = (-10315609 / 625000000) := rfl
@[simp] theorem lookup_moment_J_2_3 : literalMoment .J (some 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_4 : literalMoment .J (some 1) (2, 0) = (18206181 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_2_5 : literalMoment .J (some 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_6 : literalMoment .J (some 1) (3, 0) = (7683879 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_2_7 : literalMoment .J (some 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_8 : literalMoment .J (some 1) (4, 0) = (269183 / 1000000000) := rfl
@[simp] theorem lookup_moment_J_2_9 : literalMoment .J (some 1) (4, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_10 : literalMoment .J (some 1) (5, 0) = (1400941 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_2_11 : literalMoment .J (some 1) (5, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_12 : literalMoment .J (some 1) (6, 0) = (87131 / 1000000000) := rfl
@[simp] theorem lookup_moment_J_2_13 : literalMoment .J (some 1) (6, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_14 : literalMoment .J (some 1) (7, 0) = (470191 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_2_15 : literalMoment .J (some 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_2_16 : literalMoment .J (some 1) (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_2_17 : literalMoment .J (some 1) (8, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_3_0 : literalMoment .J (some 2) (0, 0) = (43384997 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_3_1 : literalMoment .J (some 2) (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_3_2 : literalMoment .J (some 2) (1, 0) = (57582303 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_3_3 : literalMoment .J (some 2) (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_3_4 : literalMoment .J (some 2) (2, 0) = (-99259629 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_3_5 : literalMoment .J (some 2) (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_3_6 : literalMoment .J (some 2) (3, 0) = (2873453 / 2000000000) := rfl
@[simp] theorem lookup_moment_J_3_7 : literalMoment .J (some 2) (3, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_3_8 : literalMoment .J (some 2) (4, 0) = (1013963 / 2000000000) := rfl
@[simp] theorem lookup_moment_J_3_9 : literalMoment .J (some 2) (4, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_3_10 : literalMoment .J (some 2) (5, 0) = (934813 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_3_11 : literalMoment .J (some 2) (5, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_3_12 : literalMoment .J (some 2) (6, 0) = (1095443 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_3_13 : literalMoment .J (some 2) (6, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_3_14 : literalMoment .J (some 2) (7, 0) = (549261 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_3_15 : literalMoment .J (some 2) (7, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_3_16 : literalMoment .J (some 2) (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_3_17 : literalMoment .J (some 2) (8, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_4_0 : literalMoment .J (some 3) (0, 0) = (10289209 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_4_1 : literalMoment .J (some 3) (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_4_2 : literalMoment .J (some 3) (1, 0) = (35475149 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_4_3 : literalMoment .J (some 3) (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_4_4 : literalMoment .J (some 3) (2, 0) = (6585663 / 1250000000) := rfl
@[simp] theorem lookup_moment_J_4_5 : literalMoment .J (some 3) (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_4_6 : literalMoment .J (some 3) (3, 0) = (-131676511 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_4_7 : literalMoment .J (some 3) (3, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_4_8 : literalMoment .J (some 3) (4, 0) = (697981 / 1000000000) := rfl
@[simp] theorem lookup_moment_J_4_9 : literalMoment .J (some 3) (4, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_4_10 : literalMoment .J (some 3) (5, 0) = (421609 / 1250000000) := rfl
@[simp] theorem lookup_moment_J_4_11 : literalMoment .J (some 3) (5, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_4_12 : literalMoment .J (some 3) (6, 0) = (701429 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_4_13 : literalMoment .J (some 3) (6, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_4_14 : literalMoment .J (some 3) (7, 0) = (174191 / 2500000000) := rfl
@[simp] theorem lookup_moment_J_4_15 : literalMoment .J (some 3) (7, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_4_16 : literalMoment .J (some 3) (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_4_17 : literalMoment .J (some 3) (8, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_5_0 : literalMoment .J (some 4) (0, 0) = (11032487 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_5_1 : literalMoment .J (some 4) (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_5_2 : literalMoment .J (some 4) (1, 0) = (15897243 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_5_3 : literalMoment .J (some 4) (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_5_4 : literalMoment .J (some 4) (2, 0) = (6268689 / 2000000000) := rfl
@[simp] theorem lookup_moment_J_5_5 : literalMoment .J (some 4) (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_5_6 : literalMoment .J (some 4) (3, 0) = (11412823 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_5_7 : literalMoment .J (some 4) (3, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_5_8 : literalMoment .J (some 4) (4, 0) = (-48369957 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_5_9 : literalMoment .J (some 4) (4, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_5_10 : literalMoment .J (some 4) (5, 0) = (532317 / 1250000000) := rfl
@[simp] theorem lookup_moment_J_5_11 : literalMoment .J (some 4) (5, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_5_12 : literalMoment .J (some 4) (6, 0) = (821387 / 2500000000) := rfl
@[simp] theorem lookup_moment_J_5_13 : literalMoment .J (some 4) (6, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_5_14 : literalMoment .J (some 4) (7, 0) = (234883 / 2500000000) := rfl
@[simp] theorem lookup_moment_J_5_15 : literalMoment .J (some 4) (7, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_5_16 : literalMoment .J (some 4) (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_5_17 : literalMoment .J (some 4) (8, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_6_0 : literalMoment .J (some 5) (0, 0) = (8574799 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_6_1 : literalMoment .J (some 5) (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_6_2 : literalMoment .J (some 5) (1, 0) = (1182189 / 1250000000) := rfl
@[simp] theorem lookup_moment_J_6_3 : literalMoment .J (some 5) (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_6_4 : literalMoment .J (some 5) (2, 0) = (7523557 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_6_5 : literalMoment .J (some 5) (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_6_6 : literalMoment .J (some 5) (3, 0) = (608621 / 400000000) := rfl
@[simp] theorem lookup_moment_J_6_7 : literalMoment .J (some 5) (3, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_6_8 : literalMoment .J (some 5) (4, 0) = (15958847 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_6_9 : literalMoment .J (some 5) (4, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_6_10 : literalMoment .J (some 5) (5, 0) = (-19169423 / 2500000000) := rfl
@[simp] theorem lookup_moment_J_6_11 : literalMoment .J (some 5) (5, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_6_12 : literalMoment .J (some 5) (6, 0) = (3794283 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_6_13 : literalMoment .J (some 5) (6, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_6_14 : literalMoment .J (some 5) (7, 0) = (3278167 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_6_15 : literalMoment .J (some 5) (7, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_6_16 : literalMoment .J (some 5) (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_6_17 : literalMoment .J (some 5) (8, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_7_0 : literalMoment .J (some 6) (0, 0) = (5517779 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_7_1 : literalMoment .J (some 6) (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_7_2 : literalMoment .J (some 6) (1, 0) = (3890951 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_7_3 : literalMoment .J (some 6) (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_7_4 : literalMoment .J (some 6) (2, 0) = (1742899 / 2500000000) := rfl
@[simp] theorem lookup_moment_J_7_5 : literalMoment .J (some 6) (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_7_6 : literalMoment .J (some 6) (3, 0) = (10055521 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_7_7 : literalMoment .J (some 6) (3, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_7_8 : literalMoment .J (some 6) (4, 0) = (5645671 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_7_9 : literalMoment .J (some 6) (4, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_7_10 : literalMoment .J (some 6) (5, 0) = (2547257 / 2000000000) := rfl
@[simp] theorem lookup_moment_J_7_11 : literalMoment .J (some 6) (5, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_7_12 : literalMoment .J (some 6) (6, 0) = (-31320069 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_7_13 : literalMoment .J (some 6) (6, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_7_14 : literalMoment .J (some 6) (7, 0) = (4516119 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_7_15 : literalMoment .J (some 6) (7, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_7_16 : literalMoment .J (some 6) (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_7_17 : literalMoment .J (some 6) (8, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_8_0 : literalMoment .J (some 7) (0, 0) = (130089 / 1250000000) := rfl
@[simp] theorem lookup_moment_J_8_1 : literalMoment .J (some 7) (0, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_8_2 : literalMoment .J (some 7) (1, 0) = (1127977 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_8_3 : literalMoment .J (some 7) (1, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_8_4 : literalMoment .J (some 7) (2, 0) = (637551 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_8_5 : literalMoment .J (some 7) (2, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_8_6 : literalMoment .J (some 7) (3, 0) = (257699 / 2000000000) := rfl
@[simp] theorem lookup_moment_J_8_7 : literalMoment .J (some 7) (3, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_8_8 : literalMoment .J (some 7) (4, 0) = (1735709 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_8_9 : literalMoment .J (some 7) (4, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_8_10 : literalMoment .J (some 7) (5, 0) = (975219 / 5000000000) := rfl
@[simp] theorem lookup_moment_J_8_11 : literalMoment .J (some 7) (5, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_8_12 : literalMoment .J (some 7) (6, 0) = (2041181 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_8_13 : literalMoment .J (some 7) (6, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_8_14 : literalMoment .J (some 7) (7, 0) = (-11338327 / 10000000000) := rfl
@[simp] theorem lookup_moment_J_8_15 : literalMoment .J (some 7) (7, 1) = 0 := rfl
@[simp] theorem lookup_moment_J_8_16 : literalMoment .J (some 7) (8, 0) = 0 := rfl
@[simp] theorem lookup_moment_J_8_17 : literalMoment .J (some 7) (8, 1) = 0 := rfl

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.MatrixBridge
