/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Upper.MatrixBridge.Data

@[expose] public section
set_option linter.style.longLine false
set_option maxRecDepth 4096

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.MatrixBridge

@[simp] theorem lookup_literalQ_0_0 : literalQ (0, 0) (0, 0) = (-123333 / 1000000) := rfl
@[simp] theorem lookup_literalQ_0_1 : literalQ (0, 0) (0, 1) = (559 / 10000) := rfl
@[simp] theorem lookup_literalQ_0_2 : literalQ (0, 0) (1, 0) = (37261 / 400000) := rfl
@[simp] theorem lookup_literalQ_0_3 : literalQ (0, 0) (1, 1) = (-370559 / 20000000) := rfl
@[simp] theorem lookup_literalQ_0_4 : literalQ (0, 0) (2, 0) = (31909 / 500000) := rfl
@[simp] theorem lookup_literalQ_0_5 : literalQ (0, 0) (2, 1) = (-184397 / 10000000) := rfl
@[simp] theorem lookup_literalQ_0_6 : literalQ (0, 0) (3, 0) = (-81293 / 2000000) := rfl
@[simp] theorem lookup_literalQ_0_7 : literalQ (0, 0) (3, 1) = (-524099 / 20000000) := rfl
@[simp] theorem lookup_literalQ_1_0 : literalQ (0, 1) (0, 0) = (559 / 10000) := rfl
@[simp] theorem lookup_literalQ_1_1 : literalQ (0, 1) (0, 1) = (-122333 / 1000000) := rfl
@[simp] theorem lookup_literalQ_1_2 : literalQ (0, 1) (1, 0) = (-24313 / 400000) := rfl
@[simp] theorem lookup_literalQ_1_3 : literalQ (0, 1) (1, 1) = (979719 / 20000000) := rfl
@[simp] theorem lookup_literalQ_1_4 : literalQ (0, 1) (2, 0) = (45529 / 1000000) := rfl
@[simp] theorem lookup_literalQ_1_5 : literalQ (0, 1) (2, 1) = (586721 / 5000000) := rfl
@[simp] theorem lookup_literalQ_1_6 : literalQ (0, 1) (3, 0) = (-81293 / 2000000) := rfl
@[simp] theorem lookup_literalQ_1_7 : literalQ (0, 1) (3, 1) = (-524099 / 20000000) := rfl
@[simp] theorem lookup_literalQ_2_0 : literalQ (1, 0) (0, 0) = (37261 / 400000) := rfl
@[simp] theorem lookup_literalQ_2_1 : literalQ (1, 0) (0, 1) = (-24313 / 400000) := rfl
@[simp] theorem lookup_literalQ_2_2 : literalQ (1, 0) (1, 0) = (-15743 / 250000) := rfl
@[simp] theorem lookup_literalQ_2_3 : literalQ (1, 0) (1, 1) = (-34951 / 500000) := rfl
@[simp] theorem lookup_literalQ_2_4 : literalQ (1, 0) (2, 0) = (-46343 / 2000000) := rfl
@[simp] theorem lookup_literalQ_2_5 : literalQ (1, 0) (2, 1) = (452861 / 5000000) := rfl
@[simp] theorem lookup_literalQ_2_6 : literalQ (1, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_2_7 : literalQ (1, 0) (3, 1) = (21863 / 400000) := rfl
@[simp] theorem lookup_literalQ_3_0 : literalQ (1, 1) (0, 0) = (-370559 / 20000000) := rfl
@[simp] theorem lookup_literalQ_3_1 : literalQ (1, 1) (0, 1) = (979719 / 20000000) := rfl
@[simp] theorem lookup_literalQ_3_2 : literalQ (1, 1) (1, 0) = (-34951 / 500000) := rfl
@[simp] theorem lookup_literalQ_3_3 : literalQ (1, 1) (1, 1) = (-386109 / 10000000) := rfl
@[simp] theorem lookup_literalQ_3_4 : literalQ (1, 1) (2, 0) = (955669 / 20000000) := rfl
@[simp] theorem lookup_literalQ_3_5 : literalQ (1, 1) (2, 1) = (-299613 / 20000000) := rfl
@[simp] theorem lookup_literalQ_3_6 : literalQ (1, 1) (3, 0) = (81293 / 2000000) := rfl
@[simp] theorem lookup_literalQ_3_7 : literalQ (1, 1) (3, 1) = (-83391 / 1250000) := rfl
@[simp] theorem lookup_literalQ_4_0 : literalQ (2, 0) (0, 0) = (31909 / 500000) := rfl
@[simp] theorem lookup_literalQ_4_1 : literalQ (2, 0) (0, 1) = (45529 / 1000000) := rfl
@[simp] theorem lookup_literalQ_4_2 : literalQ (2, 0) (1, 0) = (-46343 / 2000000) := rfl
@[simp] theorem lookup_literalQ_4_3 : literalQ (2, 0) (1, 1) = (955669 / 20000000) := rfl
@[simp] theorem lookup_literalQ_4_4 : literalQ (2, 0) (2, 0) = (-81293 / 1000000) := rfl
@[simp] theorem lookup_literalQ_4_5 : literalQ (2, 0) (2, 1) = (-112779 / 1000000) := rfl
@[simp] theorem lookup_literalQ_4_6 : literalQ (2, 0) (3, 0) = (81293 / 2000000) := rfl
@[simp] theorem lookup_literalQ_4_7 : literalQ (2, 0) (3, 1) = (243879 / 20000000) := rfl
@[simp] theorem lookup_literalQ_5_0 : literalQ (2, 1) (0, 0) = (-184397 / 10000000) := rfl
@[simp] theorem lookup_literalQ_5_1 : literalQ (2, 1) (0, 1) = (586721 / 5000000) := rfl
@[simp] theorem lookup_literalQ_5_2 : literalQ (2, 1) (1, 0) = (452861 / 5000000) := rfl
@[simp] theorem lookup_literalQ_5_3 : literalQ (2, 1) (1, 1) = (-299613 / 20000000) := rfl
@[simp] theorem lookup_literalQ_5_4 : literalQ (2, 1) (2, 0) = (-112779 / 1000000) := rfl
@[simp] theorem lookup_literalQ_5_5 : literalQ (2, 1) (2, 1) = (-186063 / 5000000) := rfl
@[simp] theorem lookup_literalQ_5_6 : literalQ (2, 1) (3, 0) = (81293 / 2000000) := rfl
@[simp] theorem lookup_literalQ_5_7 : literalQ (2, 1) (3, 1) = (243879 / 20000000) := rfl
@[simp] theorem lookup_literalQ_6_0 : literalQ (3, 0) (0, 0) = (-81293 / 2000000) := rfl
@[simp] theorem lookup_literalQ_6_1 : literalQ (3, 0) (0, 1) = (-81293 / 2000000) := rfl
@[simp] theorem lookup_literalQ_6_2 : literalQ (3, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_6_3 : literalQ (3, 0) (1, 1) = (81293 / 2000000) := rfl
@[simp] theorem lookup_literalQ_6_4 : literalQ (3, 0) (2, 0) = (81293 / 2000000) := rfl
@[simp] theorem lookup_literalQ_6_5 : literalQ (3, 0) (2, 1) = (81293 / 2000000) := rfl
@[simp] theorem lookup_literalQ_6_6 : literalQ (3, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_6_7 : literalQ (3, 0) (3, 1) = (-81293 / 2000000) := rfl
@[simp] theorem lookup_literalQ_7_0 : literalQ (3, 1) (0, 0) = (-524099 / 20000000) := rfl
@[simp] theorem lookup_literalQ_7_1 : literalQ (3, 1) (0, 1) = (-524099 / 20000000) := rfl
@[simp] theorem lookup_literalQ_7_2 : literalQ (3, 1) (1, 0) = (21863 / 400000) := rfl
@[simp] theorem lookup_literalQ_7_3 : literalQ (3, 1) (1, 1) = (-83391 / 1250000) := rfl
@[simp] theorem lookup_literalQ_7_4 : literalQ (3, 1) (2, 0) = (243879 / 20000000) := rfl
@[simp] theorem lookup_literalQ_7_5 : literalQ (3, 1) (2, 1) = (243879 / 20000000) := rfl
@[simp] theorem lookup_literalQ_7_6 : literalQ (3, 1) (3, 0) = (-81293 / 2000000) := rfl
@[simp] theorem lookup_literalQ_7_7 : literalQ (3, 1) (3, 1) = (569051 / 10000000) := rfl
@[simp] theorem lookup_literalAction_0_0 : literalAction (0, 0) 0 = (-7009 / 1000000) := rfl
@[simp] theorem lookup_literalAction_0_1 : literalAction (0, 0) 1 = (-36363 / 5000000) := rfl
@[simp] theorem lookup_literalAction_1_0 : literalAction (0, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_1_1 : literalAction (0, 1) 1 = (88961 / 5000000) := rfl
@[simp] theorem lookup_literalAction_2_0 : literalAction (1, 0) 0 = (7009 / 1000000) := rfl
@[simp] theorem lookup_literalAction_2_1 : literalAction (1, 0) 1 = (36363 / 2500000) := rfl
@[simp] theorem lookup_literalAction_3_0 : literalAction (1, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_3_1 : literalAction (1, 1) 1 = (-22287 / 312500) := rfl
@[simp] theorem lookup_literalAction_4_0 : literalAction (2, 0) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_4_1 : literalAction (2, 0) 1 = (-36363 / 5000000) := rfl
@[simp] theorem lookup_literalAction_5_0 : literalAction (2, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_5_1 : literalAction (2, 1) 1 = (773449 / 10000000) := rfl
@[simp] theorem lookup_literalAction_6_0 : literalAction (3, 0) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_6_1 : literalAction (3, 0) 1 = 0 := rfl
@[simp] theorem lookup_literalAction_7_0 : literalAction (3, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_7_1 : literalAction (3, 1) 1 = (-238187 / 10000000) := rfl
@[simp] theorem lookup_literalPrefix_0_0 : literalPrefix (0, 0) 0 = (7009 / 1000000) := rfl
@[simp] theorem lookup_literalPrefix_0_1 : literalPrefix (0, 0) 1 = (36363 / 5000000) := rfl
@[simp] theorem lookup_literalPrefix_1_0 : literalPrefix (0, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_1_1 : literalPrefix (0, 1) 1 = (-88961 / 5000000) := rfl
@[simp] theorem lookup_literalPrefix_2_0 : literalPrefix (1, 0) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_2_1 : literalPrefix (1, 0) 1 = (-36363 / 5000000) := rfl
@[simp] theorem lookup_literalPrefix_3_0 : literalPrefix (1, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_3_1 : literalPrefix (1, 1) 1 = (267631 / 5000000) := rfl
@[simp] theorem lookup_literalPrefix_4_0 : literalPrefix (2, 0) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_4_1 : literalPrefix (2, 0) 1 = 0 := rfl
@[simp] theorem lookup_literalPrefix_5_0 : literalPrefix (2, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_5_1 : literalPrefix (2, 1) 1 = (-238187 / 10000000) := rfl
@[simp] theorem lookup_literalA_0_0 : literalA (0, 0) (0, 0) = (4596577 / 50000000) := rfl
@[simp] theorem lookup_literalA_0_1 : literalA (0, 0) (0, 1) = (-41714243 / 500000000) := rfl
@[simp] theorem lookup_literalA_0_2 : literalA (0, 0) (1, 0) = (-3543031 / 50000000) := rfl
@[simp] theorem lookup_literalA_0_3 : literalA (0, 0) (1, 1) = (113917 / 2500000) := rfl
@[simp] theorem lookup_literalA_1_0 : literalA (0, 1) (0, 0) = (-41714243 / 500000000) := rfl
@[simp] theorem lookup_literalA_1_1 : literalA (0, 1) (0, 1) = (45980937 / 500000000) := rfl
@[simp] theorem lookup_literalA_1_2 : literalA (0, 1) (1, 0) = (75378799 / 1000000000) := rfl
@[simp] theorem lookup_literalA_1_3 : literalA (0, 1) (1, 1) = (-21647613 / 1000000000) := rfl
@[simp] theorem lookup_literalA_2_0 : literalA (1, 0) (0, 0) = (-3543031 / 50000000) := rfl
@[simp] theorem lookup_literalA_2_1 : literalA (1, 0) (0, 1) = (75378799 / 1000000000) := rfl
@[simp] theorem lookup_literalA_2_2 : literalA (1, 0) (1, 0) = (12432659 / 100000000) := rfl
@[simp] theorem lookup_literalA_2_3 : literalA (1, 0) (1, 1) = (-3513713 / 100000000) := rfl
@[simp] theorem lookup_literalA_3_0 : literalA (1, 1) (0, 0) = (113917 / 2500000) := rfl
@[simp] theorem lookup_literalA_3_1 : literalA (1, 1) (0, 1) = (-21647613 / 1000000000) := rfl
@[simp] theorem lookup_literalA_3_2 : literalA (1, 1) (1, 0) = (-3513713 / 100000000) := rfl
@[simp] theorem lookup_literalA_3_3 : literalA (1, 1) (1, 1) = (49850477 / 500000000) := rfl
@[simp] theorem lookup_literalT_0_0 : literalT (0, 0) 0 = (-87887 / 6250000) := rfl
@[simp] theorem lookup_literalT_0_1 : literalT (0, 0) 1 = (22567143 / 500000000) := rfl
@[simp] theorem lookup_literalT_1_0 : literalT (0, 1) 0 = (8049687 / 1000000000) := rfl
@[simp] theorem lookup_literalT_1_1 : literalT (0, 1) 1 = (-88106461 / 1000000000) := rfl
@[simp] theorem lookup_literalT_2_0 : literalT (1, 0) 0 = (-5346597 / 100000000) := rfl
@[simp] theorem lookup_literalT_2_1 : literalT (1, 0) 1 = (-47514269 / 1000000000) := rfl
@[simp] theorem lookup_literalT_3_0 : literalT (1, 1) 0 = (-1042967 / 100000000) := rfl
@[simp] theorem lookup_literalT_3_1 : literalT (1, 1) 1 = (-24527141 / 1000000000) := rfl
@[simp] theorem lookup_literalW_0_0 : literalW 0 0 = (6752789 / 100000000) := rfl
@[simp] theorem lookup_literalW_0_1 : literalW 0 1 = (2379983 / 1000000000) := rfl
@[simp] theorem lookup_literalW_1_0 : literalW 1 0 = (2379983 / 1000000000) := rfl
@[simp] theorem lookup_literalW_1_1 : literalW 1 1 = (44407451 / 500000000) := rfl
@[simp] theorem lookup_literalP_0_0 : literalP (0, 0) (0, 0) = (4596577 / 50000000) := rfl
@[simp] theorem lookup_literalP_0_1 : literalP (0, 0) (0, 1) = (-41714243 / 500000000) := rfl
@[simp] theorem lookup_literalP_0_2 : literalP (0, 0) (1, 0) = (-3543031 / 50000000) := rfl
@[simp] theorem lookup_literalP_0_3 : literalP (0, 0) (1, 1) = (113917 / 2500000) := rfl
@[simp] theorem lookup_literalP_0_4 : literalP (0, 0) (2, 0) = (-87887 / 6250000) := rfl
@[simp] theorem lookup_literalP_0_5 : literalP (0, 0) (2, 1) = (22567143 / 500000000) := rfl
@[simp] theorem lookup_literalP_1_0 : literalP (0, 1) (0, 0) = (-41714243 / 500000000) := rfl
@[simp] theorem lookup_literalP_1_1 : literalP (0, 1) (0, 1) = (45980937 / 500000000) := rfl
@[simp] theorem lookup_literalP_1_2 : literalP (0, 1) (1, 0) = (75378799 / 1000000000) := rfl
@[simp] theorem lookup_literalP_1_3 : literalP (0, 1) (1, 1) = (-21647613 / 1000000000) := rfl
@[simp] theorem lookup_literalP_1_4 : literalP (0, 1) (2, 0) = (8049687 / 1000000000) := rfl
@[simp] theorem lookup_literalP_1_5 : literalP (0, 1) (2, 1) = (-88106461 / 1000000000) := rfl
@[simp] theorem lookup_literalP_2_0 : literalP (1, 0) (0, 0) = (-3543031 / 50000000) := rfl
@[simp] theorem lookup_literalP_2_1 : literalP (1, 0) (0, 1) = (75378799 / 1000000000) := rfl
@[simp] theorem lookup_literalP_2_2 : literalP (1, 0) (1, 0) = (12432659 / 100000000) := rfl
@[simp] theorem lookup_literalP_2_3 : literalP (1, 0) (1, 1) = (-3513713 / 100000000) := rfl
@[simp] theorem lookup_literalP_2_4 : literalP (1, 0) (2, 0) = (-5346597 / 100000000) := rfl
@[simp] theorem lookup_literalP_2_5 : literalP (1, 0) (2, 1) = (-47514269 / 1000000000) := rfl
@[simp] theorem lookup_literalP_3_0 : literalP (1, 1) (0, 0) = (113917 / 2500000) := rfl
@[simp] theorem lookup_literalP_3_1 : literalP (1, 1) (0, 1) = (-21647613 / 1000000000) := rfl
@[simp] theorem lookup_literalP_3_2 : literalP (1, 1) (1, 0) = (-3513713 / 100000000) := rfl
@[simp] theorem lookup_literalP_3_3 : literalP (1, 1) (1, 1) = (49850477 / 500000000) := rfl
@[simp] theorem lookup_literalP_3_4 : literalP (1, 1) (2, 0) = (-1042967 / 100000000) := rfl
@[simp] theorem lookup_literalP_3_5 : literalP (1, 1) (2, 1) = (-24527141 / 1000000000) := rfl
@[simp] theorem lookup_literalP_4_0 : literalP (2, 0) (0, 0) = (-87887 / 6250000) := rfl
@[simp] theorem lookup_literalP_4_1 : literalP (2, 0) (0, 1) = (8049687 / 1000000000) := rfl
@[simp] theorem lookup_literalP_4_2 : literalP (2, 0) (1, 0) = (-5346597 / 100000000) := rfl
@[simp] theorem lookup_literalP_4_3 : literalP (2, 0) (1, 1) = (-1042967 / 100000000) := rfl
@[simp] theorem lookup_literalP_4_4 : literalP (2, 0) (2, 0) = (6752789 / 100000000) := rfl
@[simp] theorem lookup_literalP_4_5 : literalP (2, 0) (2, 1) = (2379983 / 1000000000) := rfl
@[simp] theorem lookup_literalP_5_0 : literalP (2, 1) (0, 0) = (22567143 / 500000000) := rfl
@[simp] theorem lookup_literalP_5_1 : literalP (2, 1) (0, 1) = (-88106461 / 1000000000) := rfl
@[simp] theorem lookup_literalP_5_2 : literalP (2, 1) (1, 0) = (-47514269 / 1000000000) := rfl
@[simp] theorem lookup_literalP_5_3 : literalP (2, 1) (1, 1) = (-24527141 / 1000000000) := rfl
@[simp] theorem lookup_literalP_5_4 : literalP (2, 1) (2, 0) = (2379983 / 1000000000) := rfl
@[simp] theorem lookup_literalP_5_5 : literalP (2, 1) (2, 1) = (44407451 / 500000000) := rfl
@[simp] theorem lookup_literalMuF_0_0 : literalMu .F none none = 0 := rfl
@[simp] theorem lookup_literalMuF_0_1 : literalMu .F none (some 0) = (394093 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_0_2 : literalMu .F none (some 1) = (60309 / 20000000) := rfl
@[simp] theorem lookup_literalMuF_1_0 : literalMu .F (some 0) none = (1717 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_1_1 : literalMu .F (some 0) (some 0) = 0 := rfl
@[simp] theorem lookup_literalMuF_1_2 : literalMu .F (some 0) (some 1) = (418251 / 20000000) := rfl
@[simp] theorem lookup_literalMuF_2_0 : literalMu .F (some 1) none = (1121 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_2_1 : literalMu .F (some 1) (some 0) = (5193879 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_2_2 : literalMu .F (some 1) (some 1) = 0 := rfl
@[simp] theorem lookup_literalMuJ_0_0 : literalMu .J none none = 0 := rfl
@[simp] theorem lookup_literalMuJ_0_1 : literalMu .J none (some 0) = (93889 / 25000000) := rfl
@[simp] theorem lookup_literalMuJ_0_2 : literalMu .J none (some 1) = (9999 / 3125000) := rfl
@[simp] theorem lookup_literalMuJ_1_0 : literalMu .J (some 0) none = (2033 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_1_1 : literalMu .J (some 0) (some 0) = 0 := rfl
@[simp] theorem lookup_literalMuJ_1_2 : literalMu .J (some 0) (some 1) = (1371209 / 50000000) := rfl
@[simp] theorem lookup_literalMuJ_2_0 : literalMu .J (some 1) none = (691 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_2_1 : literalMu .J (some 1) (some 0) = (1343899 / 20000000) := rfl
@[simp] theorem lookup_literalMuJ_2_2 : literalMu .J (some 1) (some 1) = 0 := rfl
end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.MatrixBridge
