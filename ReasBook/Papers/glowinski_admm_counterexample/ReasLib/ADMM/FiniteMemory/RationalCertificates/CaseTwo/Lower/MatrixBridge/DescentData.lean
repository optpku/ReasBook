/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseTwo.Lower.MatrixBridge.Lookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixDescent

@[expose] public section
set_option maxRecDepth 4096
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseTwo.Lower.MatrixBridge
open MatrixAssembly

-- These candidates become certificates only through the subsequent Lean proofs.
def literalDescentData : List (List ℚ) := [
  [(120873 / 12500000), (220589 / 200000000), (-2128137 / 200000000), (-3148057 / 2000000000), (-165777 / 40000000), (229719 / 250000000), (1022519 / 200000000), (2585061 / 2000000000), (7127 / 50000000), (-1981327 / 2000000000), (-24871 / 20000000), (-218883 / 400000000), (-233787 / 200000000), (-6936549 / 2000000000), (113631 / 50000000), (1306329 / 400000000)],
  [(220589 / 200000000), (605107 / 200000000), (-5308697 / 2000000000), (-6719153 / 2000000000), (-30559 / 200000000), (-305103 / 200000000), (7495007 / 2000000000), (1611977 / 1000000000), (10283 / 20000000), (1140749 / 2000000000), (-1699 / 625000), (46531 / 250000000), (-84467 / 40000000), (-175381 / 100000000), (113631 / 50000000), (1244891 / 1000000000)],
  [(-2128137 / 200000000), (-5308697 / 2000000000), (1101651 / 50000000), (493691 / 125000000), (-228999 / 40000000), (-117661 / 100000000), (-1292589 / 100000000), (-2844159 / 2000000000), (1468321 / 200000000), (587751 / 200000000), (-10759 / 50000000), (-761049 / 200000000), (226493 / 200000000), (1047477 / 200000000), (-25009 / 25000000), (-613477 / 200000000)],
  [(-3148057 / 2000000000), (-6719153 / 2000000000), (493691 / 125000000), (3342019 / 500000000), (-1139709 / 500000000), (-127681 / 80000000), (-8968363 / 2000000000), (-6678959 / 2000000000), (1605219 / 400000000), (565911 / 500000000), (185801 / 100000000), (-1941061 / 2000000000), (338913 / 400000000), (1314307 / 400000000), (-3641 / 1562500), (-3672057 / 2000000000)],
  [(-165777 / 40000000), (-30559 / 200000000), (-228999 / 40000000), (-1139709 / 500000000), (633457 / 25000000), (7174967 / 2000000000), (-908493 / 100000000), (-3548381 / 2000000000), (-752013 / 50000000), (-1 / 1250000), (189903 / 20000000), (250881 / 50000000), (-84663 / 100000000), (-126593 / 20000000), (779 / 100000000), (7727 / 4000000)],
  [(229719 / 250000000), (-305103 / 200000000), (-117661 / 100000000), (-127681 / 80000000), (7174967 / 2000000000), (16316589 / 2000000000), (-22557 / 5000000), (-2586697 / 1000000000), (-650629 / 100000000), (-420979 / 100000000), (17667401 / 2000000000), (128819 / 50000000), (128679 / 50000000), (-6623 / 2500000), (-185967 / 50000000), (91627 / 50000000)],
  [(1022519 / 200000000), (7495007 / 2000000000), (-1292589 / 100000000), (-8968363 / 2000000000), (-908493 / 100000000), (-22557 / 5000000), (3757059 / 100000000), (13021319 / 2000000000), (-1867559 / 200000000), (-7773503 / 2000000000), (-2185323 / 100000000), (90671 / 100000000), (218549 / 25000000), (44489 / 6250000), (17767 / 10000000), (-270039 / 50000000)],
  [(2585061 / 2000000000), (1611977 / 1000000000), (-2844159 / 2000000000), (-6678959 / 2000000000), (-3548381 / 2000000000), (-2586697 / 1000000000), (13021319 / 2000000000), (2359091 / 250000000), (-794967 / 200000000), (-6788769 / 2000000000), (-155167 / 25000000), (-440347 / 100000000), (1344777 / 200000000), (318607 / 100000000), (-114929 / 100000000), (-25519 / 50000000)],
  [(7127 / 50000000), (10283 / 20000000), (1468321 / 200000000), (1605219 / 400000000), (-752013 / 50000000), (-650629 / 100000000), (-1867559 / 200000000), (-794967 / 200000000), (4358621 / 100000000), (31947 / 3125000), (-1600653 / 100000000), (-1335989 / 400000000), (-3106529 / 100000000), (-147591 / 50000000), (31843 / 1562500), (50567 / 25000000)],
  [(-1981327 / 2000000000), (1140749 / 2000000000), (587751 / 200000000), (565911 / 500000000), (-1 / 1250000), (-420979 / 100000000), (-7773503 / 2000000000), (-6788769 / 2000000000), (31947 / 3125000), (13623627 / 1000000000), (-320361 / 50000000), (-4283709 / 1000000000), (-1284553 / 100000000), (-10029 / 1250000), (1096917 / 100000000), (229263 / 50000000)],
  [(-24871 / 20000000), (-1699 / 625000), (-10759 / 50000000), (185801 / 100000000), (189903 / 20000000), (17667401 / 2000000000), (-2185323 / 100000000), (-155167 / 25000000), (-1600653 / 100000000), (-320361 / 50000000), (902747 / 20000000), (637579 / 200000000), (359113 / 50000000), (173449 / 2000000000), (-2249627 / 100000000), (136597 / 100000000)],
  [(-218883 / 400000000), (46531 / 250000000), (-761049 / 200000000), (-1941061 / 2000000000), (250881 / 50000000), (128819 / 50000000), (90671 / 100000000), (-440347 / 100000000), (-1335989 / 400000000), (-4283709 / 1000000000), (637579 / 200000000), (22144981 / 2000000000), (151933 / 100000000), (-35429 / 200000000), (-293913 / 100000000), (-200007 / 50000000)],
  [(-233787 / 200000000), (-84467 / 40000000), (226493 / 200000000), (338913 / 400000000), (-84663 / 100000000), (128679 / 50000000), (218549 / 25000000), (1344777 / 200000000), (-3106529 / 100000000), (-1284553 / 100000000), (359113 / 50000000), (151933 / 100000000), (491771 / 10000000), (185561 / 40000000), (-3315293 / 100000000), (-538359 / 400000000)],
  [(-6936549 / 2000000000), (-175381 / 100000000), (1047477 / 200000000), (1314307 / 400000000), (-126593 / 20000000), (-6623 / 2500000), (44489 / 6250000), (318607 / 100000000), (-147591 / 50000000), (-10029 / 1250000), (173449 / 2000000000), (-35429 / 200000000), (185561 / 40000000), (34664907 / 2000000000), (-433163 / 100000000), (-1400117 / 125000000)],
  [(113631 / 50000000), (113631 / 50000000), (-25009 / 25000000), (-3641 / 1562500), (779 / 100000000), (-185967 / 50000000), (17767 / 10000000), (-114929 / 100000000), (31843 / 1562500), (1096917 / 100000000), (-2249627 / 100000000), (-293913 / 100000000), (-3315293 / 100000000), (-433163 / 100000000), (3221293 / 100000000), (3837 / 3125000)],
  [(1306329 / 400000000), (1244891 / 1000000000), (-613477 / 200000000), (-3672057 / 2000000000), (7727 / 4000000), (91627 / 50000000), (-270039 / 50000000), (-25519 / 50000000), (50567 / 25000000), (229263 / 50000000), (136597 / 100000000), (-200007 / 50000000), (-538359 / 400000000), (-1400117 / 125000000), (3837 / 3125000), (19769587 / 2000000000)]
]
def literalDescent : Matrix (Fin 8 × Fin 2) (Fin 8 × Fin 2) ℚ := readFlat literalDescentData
@[simp] theorem lookup_descent_0_0 : literalDescent (0, 0) (0, 0) = (120873 / 12500000) := rfl
@[simp] theorem lookup_previous_0_0 : previousPadding literalP (0, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_0_0 : currentPadding literalP (0, 0) (0, 0) = (12726347 / 100000000) := rfl
@[simp] theorem lookup_descent_0_1 : literalDescent (0, 0) (0, 1) = (220589 / 200000000) := rfl
@[simp] theorem lookup_previous_0_1 : previousPadding literalP (0, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_0_1 : currentPadding literalP (0, 0) (0, 1) = (-17733 / 20000000) := rfl
@[simp] theorem lookup_descent_0_2 : literalDescent (0, 0) (1, 0) = (-2128137 / 200000000) := rfl
@[simp] theorem lookup_previous_0_2 : previousPadding literalP (0, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_current_0_2 : currentPadding literalP (0, 0) (1, 0) = (-5782597 / 100000000) := rfl
@[simp] theorem lookup_descent_0_3 : literalDescent (0, 0) (1, 1) = (-3148057 / 2000000000) := rfl
@[simp] theorem lookup_previous_0_3 : previousPadding literalP (0, 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_current_0_3 : currentPadding literalP (0, 0) (1, 1) = (233347933 / 2000000000) := rfl
@[simp] theorem lookup_descent_0_4 : literalDescent (0, 0) (2, 0) = (-165777 / 40000000) := rfl
@[simp] theorem lookup_previous_0_4 : previousPadding literalP (0, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_current_0_4 : currentPadding literalP (0, 0) (2, 0) = (-5169047 / 50000000) := rfl
@[simp] theorem lookup_descent_0_5 : literalDescent (0, 0) (2, 1) = (229719 / 250000000) := rfl
@[simp] theorem lookup_previous_0_5 : previousPadding literalP (0, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_current_0_5 : currentPadding literalP (0, 0) (2, 1) = (106990111 / 2000000000) := rfl
@[simp] theorem lookup_descent_0_6 : literalDescent (0, 0) (3, 0) = (1022519 / 200000000) := rfl
@[simp] theorem lookup_previous_0_6 : previousPadding literalP (0, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_current_0_6 : currentPadding literalP (0, 0) (3, 0) = (250373 / 6250000) := rfl
@[simp] theorem lookup_descent_0_7 : literalDescent (0, 0) (3, 1) = (2585061 / 2000000000) := rfl
@[simp] theorem lookup_previous_0_7 : previousPadding literalP (0, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_current_0_7 : currentPadding literalP (0, 0) (3, 1) = (559937 / 50000000) := rfl
@[simp] theorem lookup_descent_0_8 : literalDescent (0, 0) (4, 0) = (7127 / 50000000) := rfl
@[simp] theorem lookup_previous_0_8 : previousPadding literalP (0, 0) (4, 0) = 0 := rfl
@[simp] theorem lookup_current_0_8 : currentPadding literalP (0, 0) (4, 0) = (71489 / 100000000) := rfl
@[simp] theorem lookup_descent_0_9 : literalDescent (0, 0) (4, 1) = (-1981327 / 2000000000) := rfl
@[simp] theorem lookup_previous_0_9 : previousPadding literalP (0, 0) (4, 1) = 0 := rfl
@[simp] theorem lookup_current_0_9 : currentPadding literalP (0, 0) (4, 1) = (-7529 / 781250) := rfl
@[simp] theorem lookup_descent_0_10 : literalDescent (0, 0) (5, 0) = (-24871 / 20000000) := rfl
@[simp] theorem lookup_previous_0_10 : previousPadding literalP (0, 0) (5, 0) = 0 := rfl
@[simp] theorem lookup_current_0_10 : currentPadding literalP (0, 0) (5, 0) = (-169547 / 100000000) := rfl
@[simp] theorem lookup_descent_0_11 : literalDescent (0, 0) (5, 1) = (-218883 / 400000000) := rfl
@[simp] theorem lookup_previous_0_11 : previousPadding literalP (0, 0) (5, 1) = 0 := rfl
@[simp] theorem lookup_current_0_11 : currentPadding literalP (0, 0) (5, 1) = (433341 / 100000000) := rfl
@[simp] theorem lookup_descent_0_12 : literalDescent (0, 0) (6, 0) = (-233787 / 200000000) := rfl
@[simp] theorem lookup_previous_0_12 : previousPadding literalP (0, 0) (6, 0) = 0 := rfl
@[simp] theorem lookup_current_0_12 : currentPadding literalP (0, 0) (6, 0) = (-25009 / 25000000) := rfl
@[simp] theorem lookup_descent_0_13 : literalDescent (0, 0) (6, 1) = (-6936549 / 2000000000) := rfl
@[simp] theorem lookup_previous_0_13 : previousPadding literalP (0, 0) (6, 1) = 0 := rfl
@[simp] theorem lookup_current_0_13 : currentPadding literalP (0, 0) (6, 1) = (-11583 / 50000000) := rfl
@[simp] theorem lookup_descent_0_14 : literalDescent (0, 0) (7, 0) = (113631 / 50000000) := rfl
@[simp] theorem lookup_previous_0_14 : previousPadding literalP (0, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_current_0_14 : currentPadding literalP (0, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_0_15 : literalDescent (0, 0) (7, 1) = (1306329 / 400000000) := rfl
@[simp] theorem lookup_previous_0_15 : previousPadding literalP (0, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_current_0_15 : currentPadding literalP (0, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_1_0 : literalDescent (0, 1) (0, 0) = (220589 / 200000000) := rfl
@[simp] theorem lookup_previous_1_0 : previousPadding literalP (0, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_1_0 : currentPadding literalP (0, 1) (0, 0) = (-17733 / 20000000) := rfl
@[simp] theorem lookup_descent_1_1 : literalDescent (0, 1) (0, 1) = (605107 / 200000000) := rfl
@[simp] theorem lookup_previous_1_1 : previousPadding literalP (0, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_1_1 : currentPadding literalP (0, 1) (0, 1) = (5352311 / 40000000) := rfl
@[simp] theorem lookup_descent_1_2 : literalDescent (0, 1) (1, 0) = (-5308697 / 2000000000) := rfl
@[simp] theorem lookup_previous_1_2 : previousPadding literalP (0, 1) (1, 0) = 0 := rfl
@[simp] theorem lookup_current_1_2 : currentPadding literalP (0, 1) (1, 0) = (-105587253 / 2000000000) := rfl
@[simp] theorem lookup_descent_1_3 : literalDescent (0, 1) (1, 1) = (-6719153 / 2000000000) := rfl
@[simp] theorem lookup_previous_1_3 : previousPadding literalP (0, 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_current_1_3 : currentPadding literalP (0, 1) (1, 1) = (-854021 / 50000000) := rfl
@[simp] theorem lookup_descent_1_4 : literalDescent (0, 1) (2, 0) = (-30559 / 200000000) := rfl
@[simp] theorem lookup_previous_1_4 : previousPadding literalP (0, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_current_1_4 : currentPadding literalP (0, 1) (2, 0) = (609523 / 50000000) := rfl
@[simp] theorem lookup_descent_1_5 : literalDescent (0, 1) (2, 1) = (-305103 / 200000000) := rfl
@[simp] theorem lookup_previous_1_5 : previousPadding literalP (0, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_current_1_5 : currentPadding literalP (0, 1) (2, 1) = (-2119997 / 20000000) := rfl
@[simp] theorem lookup_descent_1_6 : literalDescent (0, 1) (3, 0) = (7495007 / 2000000000) := rfl
@[simp] theorem lookup_previous_1_6 : previousPadding literalP (0, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_current_1_6 : currentPadding literalP (0, 1) (3, 0) = (82849553 / 2000000000) := rfl
@[simp] theorem lookup_descent_1_7 : literalDescent (0, 1) (3, 1) = (1611977 / 1000000000) := rfl
@[simp] theorem lookup_previous_1_7 : previousPadding literalP (0, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_current_1_7 : currentPadding literalP (0, 1) (3, 1) = (135991 / 12500000) := rfl
@[simp] theorem lookup_descent_1_8 : literalDescent (0, 1) (4, 0) = (10283 / 20000000) := rfl
@[simp] theorem lookup_previous_1_8 : previousPadding literalP (0, 1) (4, 0) = 0 := rfl
@[simp] theorem lookup_current_1_8 : currentPadding literalP (0, 1) (4, 0) = (4291 / 12500000) := rfl
@[simp] theorem lookup_descent_1_9 : literalDescent (0, 1) (4, 1) = (1140749 / 2000000000) := rfl
@[simp] theorem lookup_previous_1_9 : previousPadding literalP (0, 1) (4, 1) = 0 := rfl
@[simp] theorem lookup_current_1_9 : currentPadding literalP (0, 1) (4, 1) = (-1119817 / 100000000) := rfl
@[simp] theorem lookup_descent_1_10 : literalDescent (0, 1) (5, 0) = (-1699 / 625000) := rfl
@[simp] theorem lookup_previous_1_10 : previousPadding literalP (0, 1) (5, 0) = 0 := rfl
@[simp] theorem lookup_current_1_10 : currentPadding literalP (0, 1) (5, 0) = (-11031 / 50000000) := rfl
@[simp] theorem lookup_descent_1_11 : literalDescent (0, 1) (5, 1) = (46531 / 250000000) := rfl
@[simp] theorem lookup_previous_1_11 : previousPadding literalP (0, 1) (5, 1) = 0 := rfl
@[simp] theorem lookup_current_1_11 : currentPadding literalP (0, 1) (5, 1) = (34667 / 12500000) := rfl
@[simp] theorem lookup_descent_1_12 : literalDescent (0, 1) (6, 0) = (-84467 / 40000000) := rfl
@[simp] theorem lookup_previous_1_12 : previousPadding literalP (0, 1) (6, 0) = 0 := rfl
@[simp] theorem lookup_current_1_12 : currentPadding literalP (0, 1) (6, 0) = (-2881 / 50000000) := rfl
@[simp] theorem lookup_descent_1_13 : literalDescent (0, 1) (6, 1) = (-175381 / 100000000) := rfl
@[simp] theorem lookup_previous_1_13 : previousPadding literalP (0, 1) (6, 1) = 0 := rfl
@[simp] theorem lookup_current_1_13 : currentPadding literalP (0, 1) (6, 1) = (-541187 / 100000000) := rfl
@[simp] theorem lookup_descent_1_14 : literalDescent (0, 1) (7, 0) = (113631 / 50000000) := rfl
@[simp] theorem lookup_previous_1_14 : previousPadding literalP (0, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_current_1_14 : currentPadding literalP (0, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_1_15 : literalDescent (0, 1) (7, 1) = (1244891 / 1000000000) := rfl
@[simp] theorem lookup_previous_1_15 : previousPadding literalP (0, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_current_1_15 : currentPadding literalP (0, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_2_0 : literalDescent (1, 0) (0, 0) = (-2128137 / 200000000) := rfl
@[simp] theorem lookup_previous_2_0 : previousPadding literalP (1, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_2_0 : currentPadding literalP (1, 0) (0, 0) = (-5782597 / 100000000) := rfl
@[simp] theorem lookup_descent_2_1 : literalDescent (1, 0) (0, 1) = (-5308697 / 2000000000) := rfl
@[simp] theorem lookup_previous_2_1 : previousPadding literalP (1, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_2_1 : currentPadding literalP (1, 0) (0, 1) = (-105587253 / 2000000000) := rfl
@[simp] theorem lookup_descent_2_2 : literalDescent (1, 0) (1, 0) = (1101651 / 50000000) := rfl
@[simp] theorem lookup_previous_2_2 : previousPadding literalP (1, 0) (1, 0) = (12726347 / 100000000) := rfl
@[simp] theorem lookup_current_2_2 : currentPadding literalP (1, 0) (1, 0) = (2104609 / 20000000) := rfl
@[simp] theorem lookup_descent_2_3 : literalDescent (1, 0) (1, 1) = (493691 / 125000000) := rfl
@[simp] theorem lookup_previous_2_3 : previousPadding literalP (1, 0) (1, 1) = (-17733 / 20000000) := rfl
@[simp] theorem lookup_current_2_3 : currentPadding literalP (1, 0) (1, 1) = (-39649573 / 250000000) := rfl
@[simp] theorem lookup_descent_2_4 : literalDescent (1, 0) (2, 0) = (-228999 / 40000000) := rfl
@[simp] theorem lookup_previous_2_4 : previousPadding literalP (1, 0) (2, 0) = (-5782597 / 100000000) := rfl
@[simp] theorem lookup_current_2_4 : currentPadding literalP (1, 0) (2, 0) = (43701 / 12500000) := rfl
@[simp] theorem lookup_descent_2_5 : literalDescent (1, 0) (2, 1) = (-117661 / 100000000) := rfl
@[simp] theorem lookup_previous_2_5 : previousPadding literalP (1, 0) (2, 1) = (233347933 / 2000000000) := rfl
@[simp] theorem lookup_current_2_5 : currentPadding literalP (1, 0) (2, 1) = (287709 / 25000000) := rfl
@[simp] theorem lookup_descent_2_6 : literalDescent (1, 0) (3, 0) = (-1292589 / 100000000) := rfl
@[simp] theorem lookup_previous_2_6 : previousPadding literalP (1, 0) (3, 0) = (-5169047 / 50000000) := rfl
@[simp] theorem lookup_current_2_6 : currentPadding literalP (1, 0) (3, 0) = (-1809101 / 20000000) := rfl
@[simp] theorem lookup_descent_2_7 : literalDescent (1, 0) (3, 1) = (-2844159 / 2000000000) := rfl
@[simp] theorem lookup_previous_2_7 : previousPadding literalP (1, 0) (3, 1) = (106990111 / 2000000000) := rfl
@[simp] theorem lookup_current_2_7 : currentPadding literalP (1, 0) (3, 1) = (-33997 / 50000000) := rfl
@[simp] theorem lookup_descent_2_8 : literalDescent (1, 0) (4, 0) = (1468321 / 200000000) := rfl
@[simp] theorem lookup_previous_2_8 : previousPadding literalP (1, 0) (4, 0) = (250373 / 6250000) := rfl
@[simp] theorem lookup_current_2_8 : currentPadding literalP (1, 0) (4, 0) = (3861663 / 100000000) := rfl
@[simp] theorem lookup_descent_2_9 : literalDescent (1, 0) (4, 1) = (587751 / 200000000) := rfl
@[simp] theorem lookup_previous_2_9 : previousPadding literalP (1, 0) (4, 1) = (559937 / 50000000) := rfl
@[simp] theorem lookup_current_2_9 : currentPadding literalP (1, 0) (4, 1) = (707927 / 50000000) := rfl
@[simp] theorem lookup_descent_2_10 : literalDescent (1, 0) (5, 0) = (-10759 / 50000000) := rfl
@[simp] theorem lookup_previous_2_10 : previousPadding literalP (1, 0) (5, 0) = (71489 / 100000000) := rfl
@[simp] theorem lookup_current_2_10 : currentPadding literalP (1, 0) (5, 0) = (93007 / 100000000) := rfl
@[simp] theorem lookup_descent_2_11 : literalDescent (1, 0) (5, 1) = (-761049 / 200000000) := rfl
@[simp] theorem lookup_previous_2_11 : previousPadding literalP (1, 0) (5, 1) = (-7529 / 781250) := rfl
@[simp] theorem lookup_current_2_11 : currentPadding literalP (1, 0) (5, 1) = (-1173043 / 100000000) := rfl
@[simp] theorem lookup_descent_2_12 : literalDescent (1, 0) (6, 0) = (226493 / 200000000) := rfl
@[simp] theorem lookup_previous_2_12 : previousPadding literalP (1, 0) (6, 0) = (-169547 / 100000000) := rfl
@[simp] theorem lookup_current_2_12 : currentPadding literalP (1, 0) (6, 0) = (779 / 100000000) := rfl
@[simp] theorem lookup_descent_2_13 : literalDescent (1, 0) (6, 1) = (1047477 / 200000000) := rfl
@[simp] theorem lookup_previous_2_13 : previousPadding literalP (1, 0) (6, 1) = (433341 / 100000000) := rfl
@[simp] theorem lookup_current_2_13 : currentPadding literalP (1, 0) (6, 1) = (7727 / 4000000) := rfl
@[simp] theorem lookup_descent_2_14 : literalDescent (1, 0) (7, 0) = (-25009 / 25000000) := rfl
@[simp] theorem lookup_previous_2_14 : previousPadding literalP (1, 0) (7, 0) = (-25009 / 25000000) := rfl
@[simp] theorem lookup_current_2_14 : currentPadding literalP (1, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_2_15 : literalDescent (1, 0) (7, 1) = (-613477 / 200000000) := rfl
@[simp] theorem lookup_previous_2_15 : previousPadding literalP (1, 0) (7, 1) = (-11583 / 50000000) := rfl
@[simp] theorem lookup_current_2_15 : currentPadding literalP (1, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_3_0 : literalDescent (1, 1) (0, 0) = (-3148057 / 2000000000) := rfl
@[simp] theorem lookup_previous_3_0 : previousPadding literalP (1, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_3_0 : currentPadding literalP (1, 1) (0, 0) = (233347933 / 2000000000) := rfl
@[simp] theorem lookup_descent_3_1 : literalDescent (1, 1) (0, 1) = (-6719153 / 2000000000) := rfl
@[simp] theorem lookup_previous_3_1 : previousPadding literalP (1, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_3_1 : currentPadding literalP (1, 1) (0, 1) = (-854021 / 50000000) := rfl
@[simp] theorem lookup_descent_3_2 : literalDescent (1, 1) (1, 0) = (493691 / 125000000) := rfl
@[simp] theorem lookup_previous_3_2 : previousPadding literalP (1, 1) (1, 0) = (-17733 / 20000000) := rfl
@[simp] theorem lookup_current_3_2 : currentPadding literalP (1, 1) (1, 0) = (-39649573 / 250000000) := rfl
@[simp] theorem lookup_descent_3_3 : literalDescent (1, 1) (1, 1) = (3342019 / 500000000) := rfl
@[simp] theorem lookup_previous_3_3 : previousPadding literalP (1, 1) (1, 1) = (5352311 / 40000000) := rfl
@[simp] theorem lookup_current_3_3 : currentPadding literalP (1, 1) (1, 1) = (1558521 / 50000000) := rfl
@[simp] theorem lookup_descent_3_4 : literalDescent (1, 1) (2, 0) = (-1139709 / 500000000) := rfl
@[simp] theorem lookup_previous_3_4 : previousPadding literalP (1, 1) (2, 0) = (-105587253 / 2000000000) := rfl
@[simp] theorem lookup_current_3_4 : currentPadding literalP (1, 1) (2, 0) = (184761 / 4000000) := rfl
@[simp] theorem lookup_descent_3_5 : literalDescent (1, 1) (2, 1) = (-127681 / 80000000) := rfl
@[simp] theorem lookup_previous_3_5 : previousPadding literalP (1, 1) (2, 1) = (-854021 / 50000000) := rfl
@[simp] theorem lookup_current_3_5 : currentPadding literalP (1, 1) (2, 1) = (-247407 / 100000000) := rfl
@[simp] theorem lookup_descent_3_6 : literalDescent (1, 1) (3, 0) = (-8968363 / 2000000000) := rfl
@[simp] theorem lookup_previous_3_6 : previousPadding literalP (1, 1) (3, 0) = (609523 / 50000000) := rfl
@[simp] theorem lookup_current_3_6 : currentPadding literalP (1, 1) (3, 0) = (-2849763 / 100000000) := rfl
@[simp] theorem lookup_descent_3_7 : literalDescent (1, 1) (3, 1) = (-6678959 / 2000000000) := rfl
@[simp] theorem lookup_previous_3_7 : previousPadding literalP (1, 1) (3, 1) = (-2119997 / 20000000) := rfl
@[simp] theorem lookup_current_3_7 : currentPadding literalP (1, 1) (3, 1) = (-103183 / 5000000) := rfl
@[simp] theorem lookup_descent_3_8 : literalDescent (1, 1) (4, 0) = (1605219 / 400000000) := rfl
@[simp] theorem lookup_previous_3_8 : previousPadding literalP (1, 1) (4, 0) = (82849553 / 2000000000) := rfl
@[simp] theorem lookup_current_3_8 : currentPadding literalP (1, 1) (4, 0) = (53053511 / 2000000000) := rfl
@[simp] theorem lookup_descent_3_9 : literalDescent (1, 1) (4, 1) = (565911 / 500000000) := rfl
@[simp] theorem lookup_previous_3_9 : previousPadding literalP (1, 1) (4, 1) = (135991 / 12500000) := rfl
@[simp] theorem lookup_current_3_9 : currentPadding literalP (1, 1) (4, 1) = (1034771 / 100000000) := rfl
@[simp] theorem lookup_descent_3_10 : literalDescent (1, 1) (5, 0) = (185801 / 100000000) := rfl
@[simp] theorem lookup_previous_3_10 : previousPadding literalP (1, 1) (5, 0) = (4291 / 12500000) := rfl
@[simp] theorem lookup_current_3_10 : currentPadding literalP (1, 1) (5, 0) = (142429 / 100000000) := rfl
@[simp] theorem lookup_descent_3_11 : literalDescent (1, 1) (5, 1) = (-1941061 / 2000000000) := rfl
@[simp] theorem lookup_previous_3_11 : previousPadding literalP (1, 1) (5, 1) = (-1119817 / 100000000) := rfl
@[simp] theorem lookup_current_3_11 : currentPadding literalP (1, 1) (5, 1) = (-157979 / 50000000) := rfl
@[simp] theorem lookup_descent_3_12 : literalDescent (1, 1) (6, 0) = (338913 / 400000000) := rfl
@[simp] theorem lookup_previous_3_12 : previousPadding literalP (1, 1) (6, 0) = (-11031 / 50000000) := rfl
@[simp] theorem lookup_current_3_12 : currentPadding literalP (1, 1) (6, 0) = (-185967 / 50000000) := rfl
@[simp] theorem lookup_descent_3_13 : literalDescent (1, 1) (6, 1) = (1314307 / 400000000) := rfl
@[simp] theorem lookup_previous_3_13 : previousPadding literalP (1, 1) (6, 1) = (34667 / 12500000) := rfl
@[simp] theorem lookup_current_3_13 : currentPadding literalP (1, 1) (6, 1) = (91627 / 50000000) := rfl
@[simp] theorem lookup_descent_3_14 : literalDescent (1, 1) (7, 0) = (-3641 / 1562500) := rfl
@[simp] theorem lookup_previous_3_14 : previousPadding literalP (1, 1) (7, 0) = (-2881 / 50000000) := rfl
@[simp] theorem lookup_current_3_14 : currentPadding literalP (1, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_3_15 : literalDescent (1, 1) (7, 1) = (-3672057 / 2000000000) := rfl
@[simp] theorem lookup_previous_3_15 : previousPadding literalP (1, 1) (7, 1) = (-541187 / 100000000) := rfl
@[simp] theorem lookup_current_3_15 : currentPadding literalP (1, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_4_0 : literalDescent (2, 0) (0, 0) = (-165777 / 40000000) := rfl
@[simp] theorem lookup_previous_4_0 : previousPadding literalP (2, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_4_0 : currentPadding literalP (2, 0) (0, 0) = (-5169047 / 50000000) := rfl
@[simp] theorem lookup_descent_4_1 : literalDescent (2, 0) (0, 1) = (-30559 / 200000000) := rfl
@[simp] theorem lookup_previous_4_1 : previousPadding literalP (2, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_4_1 : currentPadding literalP (2, 0) (0, 1) = (609523 / 50000000) := rfl
@[simp] theorem lookup_descent_4_2 : literalDescent (2, 0) (1, 0) = (-228999 / 40000000) := rfl
@[simp] theorem lookup_previous_4_2 : previousPadding literalP (2, 0) (1, 0) = (-5782597 / 100000000) := rfl
@[simp] theorem lookup_current_4_2 : currentPadding literalP (2, 0) (1, 0) = (43701 / 12500000) := rfl
@[simp] theorem lookup_descent_4_3 : literalDescent (2, 0) (1, 1) = (-1139709 / 500000000) := rfl
@[simp] theorem lookup_previous_4_3 : previousPadding literalP (2, 0) (1, 1) = (-105587253 / 2000000000) := rfl
@[simp] theorem lookup_current_4_3 : currentPadding literalP (2, 0) (1, 1) = (184761 / 4000000) := rfl
@[simp] theorem lookup_descent_4_4 : literalDescent (2, 0) (2, 0) = (633457 / 25000000) := rfl
@[simp] theorem lookup_previous_4_4 : previousPadding literalP (2, 0) (2, 0) = (2104609 / 20000000) := rfl
@[simp] theorem lookup_current_4_4 : currentPadding literalP (2, 0) (2, 0) = (146999 / 800000) := rfl
@[simp] theorem lookup_descent_4_5 : literalDescent (2, 0) (2, 1) = (7174967 / 2000000000) := rfl
@[simp] theorem lookup_previous_4_5 : previousPadding literalP (2, 0) (2, 1) = (-39649573 / 250000000) := rfl
@[simp] theorem lookup_current_4_5 : currentPadding literalP (2, 0) (2, 1) = (-116658401 / 2000000000) := rfl
@[simp] theorem lookup_descent_4_6 : literalDescent (2, 0) (3, 0) = (-908493 / 100000000) := rfl
@[simp] theorem lookup_previous_4_6 : previousPadding literalP (2, 0) (3, 0) = (43701 / 12500000) := rfl
@[simp] theorem lookup_current_4_6 : currentPadding literalP (2, 0) (3, 0) = (-491841 / 12500000) := rfl
@[simp] theorem lookup_descent_4_7 : literalDescent (2, 0) (3, 1) = (-3548381 / 2000000000) := rfl
@[simp] theorem lookup_previous_4_7 : previousPadding literalP (2, 0) (3, 1) = (287709 / 25000000) := rfl
@[simp] theorem lookup_current_4_7 : currentPadding literalP (2, 0) (3, 1) = (-114797 / 50000000) := rfl
@[simp] theorem lookup_descent_4_8 : literalDescent (2, 0) (4, 0) = (-752013 / 50000000) := rfl
@[simp] theorem lookup_previous_4_8 : previousPadding literalP (2, 0) (4, 0) = (-1809101 / 20000000) := rfl
@[simp] theorem lookup_current_4_8 : currentPadding literalP (2, 0) (4, 0) = (-7541479 / 100000000) := rfl
@[simp] theorem lookup_descent_4_9 : literalDescent (2, 0) (4, 1) = (-1 / 1250000) := rfl
@[simp] theorem lookup_previous_4_9 : previousPadding literalP (2, 0) (4, 1) = (-33997 / 50000000) := rfl
@[simp] theorem lookup_current_4_9 : currentPadding literalP (2, 0) (4, 1) = (-33957 / 50000000) := rfl
@[simp] theorem lookup_descent_4_10 : literalDescent (2, 0) (5, 0) = (189903 / 20000000) := rfl
@[simp] theorem lookup_previous_4_10 : previousPadding literalP (2, 0) (5, 0) = (3861663 / 100000000) := rfl
@[simp] theorem lookup_current_4_10 : currentPadding literalP (2, 0) (5, 0) = (728037 / 25000000) := rfl
@[simp] theorem lookup_descent_4_11 : literalDescent (2, 0) (5, 1) = (250881 / 50000000) := rfl
@[simp] theorem lookup_previous_4_11 : previousPadding literalP (2, 0) (5, 1) = (707927 / 50000000) := rfl
@[simp] theorem lookup_current_4_11 : currentPadding literalP (2, 0) (5, 1) = (228523 / 25000000) := rfl
@[simp] theorem lookup_descent_4_12 : literalDescent (2, 0) (6, 0) = (-84663 / 100000000) := rfl
@[simp] theorem lookup_previous_4_12 : previousPadding literalP (2, 0) (6, 0) = (93007 / 100000000) := rfl
@[simp] theorem lookup_current_4_12 : currentPadding literalP (2, 0) (6, 0) = (17767 / 10000000) := rfl
@[simp] theorem lookup_descent_4_13 : literalDescent (2, 0) (6, 1) = (-126593 / 20000000) := rfl
@[simp] theorem lookup_previous_4_13 : previousPadding literalP (2, 0) (6, 1) = (-1173043 / 100000000) := rfl
@[simp] theorem lookup_current_4_13 : currentPadding literalP (2, 0) (6, 1) = (-270039 / 50000000) := rfl
@[simp] theorem lookup_descent_4_14 : literalDescent (2, 0) (7, 0) = (779 / 100000000) := rfl
@[simp] theorem lookup_previous_4_14 : previousPadding literalP (2, 0) (7, 0) = (779 / 100000000) := rfl
@[simp] theorem lookup_current_4_14 : currentPadding literalP (2, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_4_15 : literalDescent (2, 0) (7, 1) = (7727 / 4000000) := rfl
@[simp] theorem lookup_previous_4_15 : previousPadding literalP (2, 0) (7, 1) = (7727 / 4000000) := rfl
@[simp] theorem lookup_current_4_15 : currentPadding literalP (2, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_5_0 : literalDescent (2, 1) (0, 0) = (229719 / 250000000) := rfl
@[simp] theorem lookup_previous_5_0 : previousPadding literalP (2, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_5_0 : currentPadding literalP (2, 1) (0, 0) = (106990111 / 2000000000) := rfl
@[simp] theorem lookup_descent_5_1 : literalDescent (2, 1) (0, 1) = (-305103 / 200000000) := rfl
@[simp] theorem lookup_previous_5_1 : previousPadding literalP (2, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_5_1 : currentPadding literalP (2, 1) (0, 1) = (-2119997 / 20000000) := rfl
@[simp] theorem lookup_descent_5_2 : literalDescent (2, 1) (1, 0) = (-117661 / 100000000) := rfl
@[simp] theorem lookup_previous_5_2 : previousPadding literalP (2, 1) (1, 0) = (233347933 / 2000000000) := rfl
@[simp] theorem lookup_current_5_2 : currentPadding literalP (2, 1) (1, 0) = (287709 / 25000000) := rfl
@[simp] theorem lookup_descent_5_3 : literalDescent (2, 1) (1, 1) = (-127681 / 80000000) := rfl
@[simp] theorem lookup_previous_5_3 : previousPadding literalP (2, 1) (1, 1) = (-854021 / 50000000) := rfl
@[simp] theorem lookup_current_5_3 : currentPadding literalP (2, 1) (1, 1) = (-247407 / 100000000) := rfl
@[simp] theorem lookup_descent_5_4 : literalDescent (2, 1) (2, 0) = (7174967 / 2000000000) := rfl
@[simp] theorem lookup_previous_5_4 : previousPadding literalP (2, 1) (2, 0) = (-39649573 / 250000000) := rfl
@[simp] theorem lookup_current_5_4 : currentPadding literalP (2, 1) (2, 0) = (-116658401 / 2000000000) := rfl
@[simp] theorem lookup_descent_5_5 : literalDescent (2, 1) (2, 1) = (16316589 / 2000000000) := rfl
@[simp] theorem lookup_previous_5_5 : previousPadding literalP (2, 1) (2, 1) = (1558521 / 50000000) := rfl
@[simp] theorem lookup_current_5_5 : currentPadding literalP (2, 1) (2, 1) = (253737411 / 2000000000) := rfl
@[simp] theorem lookup_descent_5_6 : literalDescent (2, 1) (3, 0) = (-22557 / 5000000) := rfl
@[simp] theorem lookup_previous_5_6 : previousPadding literalP (2, 1) (3, 0) = (184761 / 4000000) := rfl
@[simp] theorem lookup_current_5_6 : currentPadding literalP (2, 1) (3, 0) = (-15333 / 12500000) := rfl
@[simp] theorem lookup_descent_5_7 : literalDescent (2, 1) (3, 1) = (-2586697 / 1000000000) := rfl
@[simp] theorem lookup_previous_5_7 : previousPadding literalP (2, 1) (3, 1) = (-247407 / 100000000) := rfl
@[simp] theorem lookup_current_5_7 : currentPadding literalP (2, 1) (3, 1) = (-773293 / 50000000) := rfl
@[simp] theorem lookup_descent_5_8 : literalDescent (2, 1) (4, 0) = (-650629 / 100000000) := rfl
@[simp] theorem lookup_previous_5_8 : previousPadding literalP (2, 1) (4, 0) = (-2849763 / 100000000) := rfl
@[simp] theorem lookup_current_5_8 : currentPadding literalP (2, 1) (4, 0) = (-1099567 / 50000000) := rfl
@[simp] theorem lookup_descent_5_9 : literalDescent (2, 1) (4, 1) = (-420979 / 100000000) := rfl
@[simp] theorem lookup_previous_5_9 : previousPadding literalP (2, 1) (4, 1) = (-103183 / 5000000) := rfl
@[simp] theorem lookup_current_5_9 : currentPadding literalP (2, 1) (4, 1) = (-1642681 / 100000000) := rfl
@[simp] theorem lookup_descent_5_10 : literalDescent (2, 1) (5, 0) = (17667401 / 2000000000) := rfl
@[simp] theorem lookup_previous_5_10 : previousPadding literalP (2, 1) (5, 0) = (53053511 / 2000000000) := rfl
@[simp] theorem lookup_current_5_10 : currentPadding literalP (2, 1) (5, 0) = (3538611 / 200000000) := rfl
@[simp] theorem lookup_descent_5_11 : literalDescent (2, 1) (5, 1) = (128819 / 50000000) := rfl
@[simp] theorem lookup_previous_5_11 : previousPadding literalP (2, 1) (5, 1) = (1034771 / 100000000) := rfl
@[simp] theorem lookup_current_5_11 : currentPadding literalP (2, 1) (5, 1) = (777133 / 100000000) := rfl
@[simp] theorem lookup_descent_5_12 : literalDescent (2, 1) (6, 0) = (128679 / 50000000) := rfl
@[simp] theorem lookup_previous_5_12 : previousPadding literalP (2, 1) (6, 0) = (142429 / 100000000) := rfl
@[simp] theorem lookup_current_5_12 : currentPadding literalP (2, 1) (6, 0) = (-114929 / 100000000) := rfl
@[simp] theorem lookup_descent_5_13 : literalDescent (2, 1) (6, 1) = (-6623 / 2500000) := rfl
@[simp] theorem lookup_previous_5_13 : previousPadding literalP (2, 1) (6, 1) = (-157979 / 50000000) := rfl
@[simp] theorem lookup_current_5_13 : currentPadding literalP (2, 1) (6, 1) = (-25519 / 50000000) := rfl
@[simp] theorem lookup_descent_5_14 : literalDescent (2, 1) (7, 0) = (-185967 / 50000000) := rfl
@[simp] theorem lookup_previous_5_14 : previousPadding literalP (2, 1) (7, 0) = (-185967 / 50000000) := rfl
@[simp] theorem lookup_current_5_14 : currentPadding literalP (2, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_5_15 : literalDescent (2, 1) (7, 1) = (91627 / 50000000) := rfl
@[simp] theorem lookup_previous_5_15 : previousPadding literalP (2, 1) (7, 1) = (91627 / 50000000) := rfl
@[simp] theorem lookup_current_5_15 : currentPadding literalP (2, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_6_0 : literalDescent (3, 0) (0, 0) = (1022519 / 200000000) := rfl
@[simp] theorem lookup_previous_6_0 : previousPadding literalP (3, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_6_0 : currentPadding literalP (3, 0) (0, 0) = (250373 / 6250000) := rfl
@[simp] theorem lookup_descent_6_1 : literalDescent (3, 0) (0, 1) = (7495007 / 2000000000) := rfl
@[simp] theorem lookup_previous_6_1 : previousPadding literalP (3, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_6_1 : currentPadding literalP (3, 0) (0, 1) = (82849553 / 2000000000) := rfl
@[simp] theorem lookup_descent_6_2 : literalDescent (3, 0) (1, 0) = (-1292589 / 100000000) := rfl
@[simp] theorem lookup_previous_6_2 : previousPadding literalP (3, 0) (1, 0) = (-5169047 / 50000000) := rfl
@[simp] theorem lookup_current_6_2 : currentPadding literalP (3, 0) (1, 0) = (-1809101 / 20000000) := rfl
@[simp] theorem lookup_descent_6_3 : literalDescent (3, 0) (1, 1) = (-8968363 / 2000000000) := rfl
@[simp] theorem lookup_previous_6_3 : previousPadding literalP (3, 0) (1, 1) = (609523 / 50000000) := rfl
@[simp] theorem lookup_current_6_3 : currentPadding literalP (3, 0) (1, 1) = (-2849763 / 100000000) := rfl
@[simp] theorem lookup_descent_6_4 : literalDescent (3, 0) (2, 0) = (-908493 / 100000000) := rfl
@[simp] theorem lookup_previous_6_4 : previousPadding literalP (3, 0) (2, 0) = (43701 / 12500000) := rfl
@[simp] theorem lookup_current_6_4 : currentPadding literalP (3, 0) (2, 0) = (-491841 / 12500000) := rfl
@[simp] theorem lookup_descent_6_5 : literalDescent (3, 0) (2, 1) = (-22557 / 5000000) := rfl
@[simp] theorem lookup_previous_6_5 : previousPadding literalP (3, 0) (2, 1) = (184761 / 4000000) := rfl
@[simp] theorem lookup_current_6_5 : currentPadding literalP (3, 0) (2, 1) = (-15333 / 12500000) := rfl
@[simp] theorem lookup_descent_6_6 : literalDescent (3, 0) (3, 0) = (3757059 / 100000000) := rfl
@[simp] theorem lookup_previous_6_6 : previousPadding literalP (3, 0) (3, 0) = (146999 / 800000) := rfl
@[simp] theorem lookup_current_6_6 : currentPadding literalP (3, 0) (3, 0) = (15969019 / 100000000) := rfl
@[simp] theorem lookup_descent_6_7 : literalDescent (3, 0) (3, 1) = (13021319 / 2000000000) := rfl
@[simp] theorem lookup_previous_6_7 : previousPadding literalP (3, 0) (3, 1) = (-116658401 / 2000000000) := rfl
@[simp] theorem lookup_current_6_7 : currentPadding literalP (3, 0) (3, 1) = (12009 / 20000000) := rfl
@[simp] theorem lookup_descent_6_8 : literalDescent (3, 0) (4, 0) = (-1867559 / 200000000) := rfl
@[simp] theorem lookup_previous_6_8 : previousPadding literalP (3, 0) (4, 0) = (-491841 / 12500000) := rfl
@[simp] theorem lookup_current_6_8 : currentPadding literalP (3, 0) (4, 0) = (-73531 / 2000000) := rfl
@[simp] theorem lookup_descent_6_9 : literalDescent (3, 0) (4, 1) = (-7773503 / 2000000000) := rfl
@[simp] theorem lookup_previous_6_9 : previousPadding literalP (3, 0) (4, 1) = (-114797 / 50000000) := rfl
@[simp] theorem lookup_current_6_9 : currentPadding literalP (3, 0) (4, 1) = (-109 / 250000) := rfl
@[simp] theorem lookup_descent_6_10 : literalDescent (3, 0) (5, 0) = (-2185323 / 100000000) := rfl
@[simp] theorem lookup_previous_6_10 : previousPadding literalP (3, 0) (5, 0) = (-7541479 / 100000000) := rfl
@[simp] theorem lookup_current_6_10 : currentPadding literalP (3, 0) (5, 0) = (-1339039 / 25000000) := rfl
@[simp] theorem lookup_descent_6_11 : literalDescent (3, 0) (5, 1) = (90671 / 100000000) := rfl
@[simp] theorem lookup_previous_6_11 : previousPadding literalP (3, 0) (5, 1) = (-33957 / 50000000) := rfl
@[simp] theorem lookup_current_6_11 : currentPadding literalP (3, 0) (5, 1) = (-31717 / 20000000) := rfl
@[simp] theorem lookup_descent_6_12 : literalDescent (3, 0) (6, 0) = (218549 / 25000000) := rfl
@[simp] theorem lookup_previous_6_12 : previousPadding literalP (3, 0) (6, 0) = (728037 / 25000000) := rfl
@[simp] theorem lookup_current_6_12 : currentPadding literalP (3, 0) (6, 0) = (31843 / 1562500) := rfl
@[simp] theorem lookup_descent_6_13 : literalDescent (3, 0) (6, 1) = (44489 / 6250000) := rfl
@[simp] theorem lookup_previous_6_13 : previousPadding literalP (3, 0) (6, 1) = (228523 / 25000000) := rfl
@[simp] theorem lookup_current_6_13 : currentPadding literalP (3, 0) (6, 1) = (50567 / 25000000) := rfl
@[simp] theorem lookup_descent_6_14 : literalDescent (3, 0) (7, 0) = (17767 / 10000000) := rfl
@[simp] theorem lookup_previous_6_14 : previousPadding literalP (3, 0) (7, 0) = (17767 / 10000000) := rfl
@[simp] theorem lookup_current_6_14 : currentPadding literalP (3, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_6_15 : literalDescent (3, 0) (7, 1) = (-270039 / 50000000) := rfl
@[simp] theorem lookup_previous_6_15 : previousPadding literalP (3, 0) (7, 1) = (-270039 / 50000000) := rfl
@[simp] theorem lookup_current_6_15 : currentPadding literalP (3, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_7_0 : literalDescent (3, 1) (0, 0) = (2585061 / 2000000000) := rfl
@[simp] theorem lookup_previous_7_0 : previousPadding literalP (3, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_7_0 : currentPadding literalP (3, 1) (0, 0) = (559937 / 50000000) := rfl
@[simp] theorem lookup_descent_7_1 : literalDescent (3, 1) (0, 1) = (1611977 / 1000000000) := rfl
@[simp] theorem lookup_previous_7_1 : previousPadding literalP (3, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_7_1 : currentPadding literalP (3, 1) (0, 1) = (135991 / 12500000) := rfl
@[simp] theorem lookup_descent_7_2 : literalDescent (3, 1) (1, 0) = (-2844159 / 2000000000) := rfl
@[simp] theorem lookup_previous_7_2 : previousPadding literalP (3, 1) (1, 0) = (106990111 / 2000000000) := rfl
@[simp] theorem lookup_current_7_2 : currentPadding literalP (3, 1) (1, 0) = (-33997 / 50000000) := rfl
@[simp] theorem lookup_descent_7_3 : literalDescent (3, 1) (1, 1) = (-6678959 / 2000000000) := rfl
@[simp] theorem lookup_previous_7_3 : previousPadding literalP (3, 1) (1, 1) = (-2119997 / 20000000) := rfl
@[simp] theorem lookup_current_7_3 : currentPadding literalP (3, 1) (1, 1) = (-103183 / 5000000) := rfl
@[simp] theorem lookup_descent_7_4 : literalDescent (3, 1) (2, 0) = (-3548381 / 2000000000) := rfl
@[simp] theorem lookup_previous_7_4 : previousPadding literalP (3, 1) (2, 0) = (287709 / 25000000) := rfl
@[simp] theorem lookup_current_7_4 : currentPadding literalP (3, 1) (2, 0) = (-114797 / 50000000) := rfl
@[simp] theorem lookup_descent_7_5 : literalDescent (3, 1) (2, 1) = (-2586697 / 1000000000) := rfl
@[simp] theorem lookup_previous_7_5 : previousPadding literalP (3, 1) (2, 1) = (-247407 / 100000000) := rfl
@[simp] theorem lookup_current_7_5 : currentPadding literalP (3, 1) (2, 1) = (-773293 / 50000000) := rfl
@[simp] theorem lookup_descent_7_6 : literalDescent (3, 1) (3, 0) = (13021319 / 2000000000) := rfl
@[simp] theorem lookup_previous_7_6 : previousPadding literalP (3, 1) (3, 0) = (-116658401 / 2000000000) := rfl
@[simp] theorem lookup_current_7_6 : currentPadding literalP (3, 1) (3, 0) = (12009 / 20000000) := rfl
@[simp] theorem lookup_descent_7_7 : literalDescent (3, 1) (3, 1) = (2359091 / 250000000) := rfl
@[simp] theorem lookup_previous_7_7 : previousPadding literalP (3, 1) (3, 1) = (253737411 / 2000000000) := rfl
@[simp] theorem lookup_current_7_7 : currentPadding literalP (3, 1) (3, 1) = (116489531 / 2000000000) := rfl
@[simp] theorem lookup_descent_7_8 : literalDescent (3, 1) (4, 0) = (-794967 / 200000000) := rfl
@[simp] theorem lookup_previous_7_8 : previousPadding literalP (3, 1) (4, 0) = (-15333 / 12500000) := rfl
@[simp] theorem lookup_current_7_8 : currentPadding literalP (3, 1) (4, 0) = (-200391 / 50000000) := rfl
@[simp] theorem lookup_descent_7_9 : literalDescent (3, 1) (4, 1) = (-6788769 / 2000000000) := rfl
@[simp] theorem lookup_previous_7_9 : previousPadding literalP (3, 1) (4, 1) = (-773293 / 50000000) := rfl
@[simp] theorem lookup_current_7_9 : currentPadding literalP (3, 1) (4, 1) = (-352457 / 25000000) := rfl
@[simp] theorem lookup_descent_7_10 : literalDescent (3, 1) (5, 0) = (-155167 / 25000000) := rfl
@[simp] theorem lookup_previous_7_10 : previousPadding literalP (3, 1) (5, 0) = (-1099567 / 50000000) := rfl
@[simp] theorem lookup_current_7_10 : currentPadding literalP (3, 1) (5, 0) = (-789233 / 50000000) := rfl
@[simp] theorem lookup_descent_7_11 : literalDescent (3, 1) (5, 1) = (-440347 / 100000000) := rfl
@[simp] theorem lookup_previous_7_11 : previousPadding literalP (3, 1) (5, 1) = (-1642681 / 100000000) := rfl
@[simp] theorem lookup_current_7_11 : currentPadding literalP (3, 1) (5, 1) = (-601167 / 50000000) := rfl
@[simp] theorem lookup_descent_7_12 : literalDescent (3, 1) (6, 0) = (1344777 / 200000000) := rfl
@[simp] theorem lookup_previous_7_12 : previousPadding literalP (3, 1) (6, 0) = (3538611 / 200000000) := rfl
@[simp] theorem lookup_current_7_12 : currentPadding literalP (3, 1) (6, 0) = (1096917 / 100000000) := rfl
@[simp] theorem lookup_descent_7_13 : literalDescent (3, 1) (6, 1) = (318607 / 100000000) := rfl
@[simp] theorem lookup_previous_7_13 : previousPadding literalP (3, 1) (6, 1) = (777133 / 100000000) := rfl
@[simp] theorem lookup_current_7_13 : currentPadding literalP (3, 1) (6, 1) = (229263 / 50000000) := rfl
@[simp] theorem lookup_descent_7_14 : literalDescent (3, 1) (7, 0) = (-114929 / 100000000) := rfl
@[simp] theorem lookup_previous_7_14 : previousPadding literalP (3, 1) (7, 0) = (-114929 / 100000000) := rfl
@[simp] theorem lookup_current_7_14 : currentPadding literalP (3, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_7_15 : literalDescent (3, 1) (7, 1) = (-25519 / 50000000) := rfl
@[simp] theorem lookup_previous_7_15 : previousPadding literalP (3, 1) (7, 1) = (-25519 / 50000000) := rfl
@[simp] theorem lookup_current_7_15 : currentPadding literalP (3, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_8_0 : literalDescent (4, 0) (0, 0) = (7127 / 50000000) := rfl
@[simp] theorem lookup_previous_8_0 : previousPadding literalP (4, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_8_0 : currentPadding literalP (4, 0) (0, 0) = (71489 / 100000000) := rfl
@[simp] theorem lookup_descent_8_1 : literalDescent (4, 0) (0, 1) = (10283 / 20000000) := rfl
@[simp] theorem lookup_previous_8_1 : previousPadding literalP (4, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_8_1 : currentPadding literalP (4, 0) (0, 1) = (4291 / 12500000) := rfl
@[simp] theorem lookup_descent_8_2 : literalDescent (4, 0) (1, 0) = (1468321 / 200000000) := rfl
@[simp] theorem lookup_previous_8_2 : previousPadding literalP (4, 0) (1, 0) = (250373 / 6250000) := rfl
@[simp] theorem lookup_current_8_2 : currentPadding literalP (4, 0) (1, 0) = (3861663 / 100000000) := rfl
@[simp] theorem lookup_descent_8_3 : literalDescent (4, 0) (1, 1) = (1605219 / 400000000) := rfl
@[simp] theorem lookup_previous_8_3 : previousPadding literalP (4, 0) (1, 1) = (82849553 / 2000000000) := rfl
@[simp] theorem lookup_current_8_3 : currentPadding literalP (4, 0) (1, 1) = (53053511 / 2000000000) := rfl
@[simp] theorem lookup_descent_8_4 : literalDescent (4, 0) (2, 0) = (-752013 / 50000000) := rfl
@[simp] theorem lookup_previous_8_4 : previousPadding literalP (4, 0) (2, 0) = (-1809101 / 20000000) := rfl
@[simp] theorem lookup_current_8_4 : currentPadding literalP (4, 0) (2, 0) = (-7541479 / 100000000) := rfl
@[simp] theorem lookup_descent_8_5 : literalDescent (4, 0) (2, 1) = (-650629 / 100000000) := rfl
@[simp] theorem lookup_previous_8_5 : previousPadding literalP (4, 0) (2, 1) = (-2849763 / 100000000) := rfl
@[simp] theorem lookup_current_8_5 : currentPadding literalP (4, 0) (2, 1) = (-1099567 / 50000000) := rfl
@[simp] theorem lookup_descent_8_6 : literalDescent (4, 0) (3, 0) = (-1867559 / 200000000) := rfl
@[simp] theorem lookup_previous_8_6 : previousPadding literalP (4, 0) (3, 0) = (-491841 / 12500000) := rfl
@[simp] theorem lookup_current_8_6 : currentPadding literalP (4, 0) (3, 0) = (-73531 / 2000000) := rfl
@[simp] theorem lookup_descent_8_7 : literalDescent (4, 0) (3, 1) = (-794967 / 200000000) := rfl
@[simp] theorem lookup_previous_8_7 : previousPadding literalP (4, 0) (3, 1) = (-15333 / 12500000) := rfl
@[simp] theorem lookup_current_8_7 : currentPadding literalP (4, 0) (3, 1) = (-200391 / 50000000) := rfl
@[simp] theorem lookup_descent_8_8 : literalDescent (4, 0) (4, 0) = (4358621 / 100000000) := rfl
@[simp] theorem lookup_previous_8_8 : previousPadding literalP (4, 0) (4, 0) = (15969019 / 100000000) := rfl
@[simp] theorem lookup_current_8_8 : currentPadding literalP (4, 0) (4, 0) = (2902601 / 25000000) := rfl
@[simp] theorem lookup_descent_8_9 : literalDescent (4, 0) (4, 1) = (31947 / 3125000) := rfl
@[simp] theorem lookup_previous_8_9 : previousPadding literalP (4, 0) (4, 1) = (12009 / 20000000) := rfl
@[simp] theorem lookup_current_8_9 : currentPadding literalP (4, 0) (4, 1) = (-71663 / 25000000) := rfl
@[simp] theorem lookup_descent_8_10 : literalDescent (4, 0) (5, 0) = (-1600653 / 100000000) := rfl
@[simp] theorem lookup_previous_8_10 : previousPadding literalP (4, 0) (5, 0) = (-73531 / 2000000) := rfl
@[simp] theorem lookup_current_8_10 : currentPadding literalP (4, 0) (5, 0) = (-20759 / 1000000) := rfl
@[simp] theorem lookup_descent_8_11 : literalDescent (4, 0) (5, 1) = (-1335989 / 400000000) := rfl
@[simp] theorem lookup_previous_8_11 : previousPadding literalP (4, 0) (5, 1) = (-109 / 250000) := rfl
@[simp] theorem lookup_current_8_11 : currentPadding literalP (4, 0) (5, 1) = (72599 / 25000000) := rfl
@[simp] theorem lookup_descent_8_12 : literalDescent (4, 0) (6, 0) = (-3106529 / 100000000) := rfl
@[simp] theorem lookup_previous_8_12 : previousPadding literalP (4, 0) (6, 0) = (-1339039 / 25000000) := rfl
@[simp] theorem lookup_current_8_12 : currentPadding literalP (4, 0) (6, 0) = (-2249627 / 100000000) := rfl
@[simp] theorem lookup_descent_8_13 : literalDescent (4, 0) (6, 1) = (-147591 / 50000000) := rfl
@[simp] theorem lookup_previous_8_13 : previousPadding literalP (4, 0) (6, 1) = (-31717 / 20000000) := rfl
@[simp] theorem lookup_current_8_13 : currentPadding literalP (4, 0) (6, 1) = (136597 / 100000000) := rfl
@[simp] theorem lookup_descent_8_14 : literalDescent (4, 0) (7, 0) = (31843 / 1562500) := rfl
@[simp] theorem lookup_previous_8_14 : previousPadding literalP (4, 0) (7, 0) = (31843 / 1562500) := rfl
@[simp] theorem lookup_current_8_14 : currentPadding literalP (4, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_8_15 : literalDescent (4, 0) (7, 1) = (50567 / 25000000) := rfl
@[simp] theorem lookup_previous_8_15 : previousPadding literalP (4, 0) (7, 1) = (50567 / 25000000) := rfl
@[simp] theorem lookup_current_8_15 : currentPadding literalP (4, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_9_0 : literalDescent (4, 1) (0, 0) = (-1981327 / 2000000000) := rfl
@[simp] theorem lookup_previous_9_0 : previousPadding literalP (4, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_9_0 : currentPadding literalP (4, 1) (0, 0) = (-7529 / 781250) := rfl
@[simp] theorem lookup_descent_9_1 : literalDescent (4, 1) (0, 1) = (1140749 / 2000000000) := rfl
@[simp] theorem lookup_previous_9_1 : previousPadding literalP (4, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_9_1 : currentPadding literalP (4, 1) (0, 1) = (-1119817 / 100000000) := rfl
@[simp] theorem lookup_descent_9_2 : literalDescent (4, 1) (1, 0) = (587751 / 200000000) := rfl
@[simp] theorem lookup_previous_9_2 : previousPadding literalP (4, 1) (1, 0) = (559937 / 50000000) := rfl
@[simp] theorem lookup_current_9_2 : currentPadding literalP (4, 1) (1, 0) = (707927 / 50000000) := rfl
@[simp] theorem lookup_descent_9_3 : literalDescent (4, 1) (1, 1) = (565911 / 500000000) := rfl
@[simp] theorem lookup_previous_9_3 : previousPadding literalP (4, 1) (1, 1) = (135991 / 12500000) := rfl
@[simp] theorem lookup_current_9_3 : currentPadding literalP (4, 1) (1, 1) = (1034771 / 100000000) := rfl
@[simp] theorem lookup_descent_9_4 : literalDescent (4, 1) (2, 0) = (-1 / 1250000) := rfl
@[simp] theorem lookup_previous_9_4 : previousPadding literalP (4, 1) (2, 0) = (-33997 / 50000000) := rfl
@[simp] theorem lookup_current_9_4 : currentPadding literalP (4, 1) (2, 0) = (-33957 / 50000000) := rfl
@[simp] theorem lookup_descent_9_5 : literalDescent (4, 1) (2, 1) = (-420979 / 100000000) := rfl
@[simp] theorem lookup_previous_9_5 : previousPadding literalP (4, 1) (2, 1) = (-103183 / 5000000) := rfl
@[simp] theorem lookup_current_9_5 : currentPadding literalP (4, 1) (2, 1) = (-1642681 / 100000000) := rfl
@[simp] theorem lookup_descent_9_6 : literalDescent (4, 1) (3, 0) = (-7773503 / 2000000000) := rfl
@[simp] theorem lookup_previous_9_6 : previousPadding literalP (4, 1) (3, 0) = (-114797 / 50000000) := rfl
@[simp] theorem lookup_current_9_6 : currentPadding literalP (4, 1) (3, 0) = (-109 / 250000) := rfl
@[simp] theorem lookup_descent_9_7 : literalDescent (4, 1) (3, 1) = (-6788769 / 2000000000) := rfl
@[simp] theorem lookup_previous_9_7 : previousPadding literalP (4, 1) (3, 1) = (-773293 / 50000000) := rfl
@[simp] theorem lookup_current_9_7 : currentPadding literalP (4, 1) (3, 1) = (-352457 / 25000000) := rfl
@[simp] theorem lookup_descent_9_8 : literalDescent (4, 1) (4, 0) = (31947 / 3125000) := rfl
@[simp] theorem lookup_previous_9_8 : previousPadding literalP (4, 1) (4, 0) = (12009 / 20000000) := rfl
@[simp] theorem lookup_current_9_8 : currentPadding literalP (4, 1) (4, 0) = (-71663 / 25000000) := rfl
@[simp] theorem lookup_descent_9_9 : literalDescent (4, 1) (4, 1) = (13623627 / 1000000000) := rfl
@[simp] theorem lookup_previous_9_9 : previousPadding literalP (4, 1) (4, 1) = (116489531 / 2000000000) := rfl
@[simp] theorem lookup_current_9_9 : currentPadding literalP (4, 1) (4, 1) = (14065111 / 400000000) := rfl
@[simp] theorem lookup_descent_9_10 : literalDescent (4, 1) (5, 0) = (-320361 / 50000000) := rfl
@[simp] theorem lookup_previous_9_10 : previousPadding literalP (4, 1) (5, 0) = (-200391 / 50000000) := rfl
@[simp] theorem lookup_current_9_10 : currentPadding literalP (4, 1) (5, 0) = (239937 / 100000000) := rfl
@[simp] theorem lookup_descent_9_11 : literalDescent (4, 1) (5, 1) = (-4283709 / 1000000000) := rfl
@[simp] theorem lookup_previous_9_11 : previousPadding literalP (4, 1) (5, 1) = (-352457 / 25000000) := rfl
@[simp] theorem lookup_current_9_11 : currentPadding literalP (4, 1) (5, 1) = (-490729 / 50000000) := rfl
@[simp] theorem lookup_descent_9_12 : literalDescent (4, 1) (6, 0) = (-1284553 / 100000000) := rfl
@[simp] theorem lookup_previous_9_12 : previousPadding literalP (4, 1) (6, 0) = (-789233 / 50000000) := rfl
@[simp] theorem lookup_current_9_12 : currentPadding literalP (4, 1) (6, 0) = (-293913 / 100000000) := rfl
@[simp] theorem lookup_descent_9_13 : literalDescent (4, 1) (6, 1) = (-10029 / 1250000) := rfl
@[simp] theorem lookup_previous_9_13 : previousPadding literalP (4, 1) (6, 1) = (-601167 / 50000000) := rfl
@[simp] theorem lookup_current_9_13 : currentPadding literalP (4, 1) (6, 1) = (-200007 / 50000000) := rfl
@[simp] theorem lookup_descent_9_14 : literalDescent (4, 1) (7, 0) = (1096917 / 100000000) := rfl
@[simp] theorem lookup_previous_9_14 : previousPadding literalP (4, 1) (7, 0) = (1096917 / 100000000) := rfl
@[simp] theorem lookup_current_9_14 : currentPadding literalP (4, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_9_15 : literalDescent (4, 1) (7, 1) = (229263 / 50000000) := rfl
@[simp] theorem lookup_previous_9_15 : previousPadding literalP (4, 1) (7, 1) = (229263 / 50000000) := rfl
@[simp] theorem lookup_current_9_15 : currentPadding literalP (4, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_10_0 : literalDescent (5, 0) (0, 0) = (-24871 / 20000000) := rfl
@[simp] theorem lookup_previous_10_0 : previousPadding literalP (5, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_10_0 : currentPadding literalP (5, 0) (0, 0) = (-169547 / 100000000) := rfl
@[simp] theorem lookup_descent_10_1 : literalDescent (5, 0) (0, 1) = (-1699 / 625000) := rfl
@[simp] theorem lookup_previous_10_1 : previousPadding literalP (5, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_10_1 : currentPadding literalP (5, 0) (0, 1) = (-11031 / 50000000) := rfl
@[simp] theorem lookup_descent_10_2 : literalDescent (5, 0) (1, 0) = (-10759 / 50000000) := rfl
@[simp] theorem lookup_previous_10_2 : previousPadding literalP (5, 0) (1, 0) = (71489 / 100000000) := rfl
@[simp] theorem lookup_current_10_2 : currentPadding literalP (5, 0) (1, 0) = (93007 / 100000000) := rfl
@[simp] theorem lookup_descent_10_3 : literalDescent (5, 0) (1, 1) = (185801 / 100000000) := rfl
@[simp] theorem lookup_previous_10_3 : previousPadding literalP (5, 0) (1, 1) = (4291 / 12500000) := rfl
@[simp] theorem lookup_current_10_3 : currentPadding literalP (5, 0) (1, 1) = (142429 / 100000000) := rfl
@[simp] theorem lookup_descent_10_4 : literalDescent (5, 0) (2, 0) = (189903 / 20000000) := rfl
@[simp] theorem lookup_previous_10_4 : previousPadding literalP (5, 0) (2, 0) = (3861663 / 100000000) := rfl
@[simp] theorem lookup_current_10_4 : currentPadding literalP (5, 0) (2, 0) = (728037 / 25000000) := rfl
@[simp] theorem lookup_descent_10_5 : literalDescent (5, 0) (2, 1) = (17667401 / 2000000000) := rfl
@[simp] theorem lookup_previous_10_5 : previousPadding literalP (5, 0) (2, 1) = (53053511 / 2000000000) := rfl
@[simp] theorem lookup_current_10_5 : currentPadding literalP (5, 0) (2, 1) = (3538611 / 200000000) := rfl
@[simp] theorem lookup_descent_10_6 : literalDescent (5, 0) (3, 0) = (-2185323 / 100000000) := rfl
@[simp] theorem lookup_previous_10_6 : previousPadding literalP (5, 0) (3, 0) = (-7541479 / 100000000) := rfl
@[simp] theorem lookup_current_10_6 : currentPadding literalP (5, 0) (3, 0) = (-1339039 / 25000000) := rfl
@[simp] theorem lookup_descent_10_7 : literalDescent (5, 0) (3, 1) = (-155167 / 25000000) := rfl
@[simp] theorem lookup_previous_10_7 : previousPadding literalP (5, 0) (3, 1) = (-1099567 / 50000000) := rfl
@[simp] theorem lookup_current_10_7 : currentPadding literalP (5, 0) (3, 1) = (-789233 / 50000000) := rfl
@[simp] theorem lookup_descent_10_8 : literalDescent (5, 0) (4, 0) = (-1600653 / 100000000) := rfl
@[simp] theorem lookup_previous_10_8 : previousPadding literalP (5, 0) (4, 0) = (-73531 / 2000000) := rfl
@[simp] theorem lookup_current_10_8 : currentPadding literalP (5, 0) (4, 0) = (-20759 / 1000000) := rfl
@[simp] theorem lookup_descent_10_9 : literalDescent (5, 0) (4, 1) = (-320361 / 50000000) := rfl
@[simp] theorem lookup_previous_10_9 : previousPadding literalP (5, 0) (4, 1) = (-200391 / 50000000) := rfl
@[simp] theorem lookup_current_10_9 : currentPadding literalP (5, 0) (4, 1) = (239937 / 100000000) := rfl
@[simp] theorem lookup_descent_10_10 : literalDescent (5, 0) (5, 0) = (902747 / 20000000) := rfl
@[simp] theorem lookup_previous_10_10 : previousPadding literalP (5, 0) (5, 0) = (2902601 / 25000000) := rfl
@[simp] theorem lookup_current_10_10 : currentPadding literalP (5, 0) (5, 0) = (7684479 / 100000000) := rfl
@[simp] theorem lookup_descent_10_11 : literalDescent (5, 0) (5, 1) = (637579 / 200000000) := rfl
@[simp] theorem lookup_previous_10_11 : previousPadding literalP (5, 0) (5, 1) = (-71663 / 25000000) := rfl
@[simp] theorem lookup_current_10_11 : currentPadding literalP (5, 0) (5, 1) = (-1003 / 1000000) := rfl
@[simp] theorem lookup_descent_10_12 : literalDescent (5, 0) (6, 0) = (359113 / 50000000) := rfl
@[simp] theorem lookup_previous_10_12 : previousPadding literalP (5, 0) (6, 0) = (-20759 / 1000000) := rfl
@[simp] theorem lookup_current_10_12 : currentPadding literalP (5, 0) (6, 0) = (-3088031 / 100000000) := rfl
@[simp] theorem lookup_descent_10_13 : literalDescent (5, 0) (6, 1) = (173449 / 2000000000) := rfl
@[simp] theorem lookup_previous_10_13 : previousPadding literalP (5, 0) (6, 1) = (72599 / 25000000) := rfl
@[simp] theorem lookup_current_10_13 : currentPadding literalP (5, 0) (6, 1) = (67841 / 50000000) := rfl
@[simp] theorem lookup_descent_10_14 : literalDescent (5, 0) (7, 0) = (-2249627 / 100000000) := rfl
@[simp] theorem lookup_previous_10_14 : previousPadding literalP (5, 0) (7, 0) = (-2249627 / 100000000) := rfl
@[simp] theorem lookup_current_10_14 : currentPadding literalP (5, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_10_15 : literalDescent (5, 0) (7, 1) = (136597 / 100000000) := rfl
@[simp] theorem lookup_previous_10_15 : previousPadding literalP (5, 0) (7, 1) = (136597 / 100000000) := rfl
@[simp] theorem lookup_current_10_15 : currentPadding literalP (5, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_11_0 : literalDescent (5, 1) (0, 0) = (-218883 / 400000000) := rfl
@[simp] theorem lookup_previous_11_0 : previousPadding literalP (5, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_11_0 : currentPadding literalP (5, 1) (0, 0) = (433341 / 100000000) := rfl
@[simp] theorem lookup_descent_11_1 : literalDescent (5, 1) (0, 1) = (46531 / 250000000) := rfl
@[simp] theorem lookup_previous_11_1 : previousPadding literalP (5, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_11_1 : currentPadding literalP (5, 1) (0, 1) = (34667 / 12500000) := rfl
@[simp] theorem lookup_descent_11_2 : literalDescent (5, 1) (1, 0) = (-761049 / 200000000) := rfl
@[simp] theorem lookup_previous_11_2 : previousPadding literalP (5, 1) (1, 0) = (-7529 / 781250) := rfl
@[simp] theorem lookup_current_11_2 : currentPadding literalP (5, 1) (1, 0) = (-1173043 / 100000000) := rfl
@[simp] theorem lookup_descent_11_3 : literalDescent (5, 1) (1, 1) = (-1941061 / 2000000000) := rfl
@[simp] theorem lookup_previous_11_3 : previousPadding literalP (5, 1) (1, 1) = (-1119817 / 100000000) := rfl
@[simp] theorem lookup_current_11_3 : currentPadding literalP (5, 1) (1, 1) = (-157979 / 50000000) := rfl
@[simp] theorem lookup_descent_11_4 : literalDescent (5, 1) (2, 0) = (250881 / 50000000) := rfl
@[simp] theorem lookup_previous_11_4 : previousPadding literalP (5, 1) (2, 0) = (707927 / 50000000) := rfl
@[simp] theorem lookup_current_11_4 : currentPadding literalP (5, 1) (2, 0) = (228523 / 25000000) := rfl
@[simp] theorem lookup_descent_11_5 : literalDescent (5, 1) (2, 1) = (128819 / 50000000) := rfl
@[simp] theorem lookup_previous_11_5 : previousPadding literalP (5, 1) (2, 1) = (1034771 / 100000000) := rfl
@[simp] theorem lookup_current_11_5 : currentPadding literalP (5, 1) (2, 1) = (777133 / 100000000) := rfl
@[simp] theorem lookup_descent_11_6 : literalDescent (5, 1) (3, 0) = (90671 / 100000000) := rfl
@[simp] theorem lookup_previous_11_6 : previousPadding literalP (5, 1) (3, 0) = (-33957 / 50000000) := rfl
@[simp] theorem lookup_current_11_6 : currentPadding literalP (5, 1) (3, 0) = (-31717 / 20000000) := rfl
@[simp] theorem lookup_descent_11_7 : literalDescent (5, 1) (3, 1) = (-440347 / 100000000) := rfl
@[simp] theorem lookup_previous_11_7 : previousPadding literalP (5, 1) (3, 1) = (-1642681 / 100000000) := rfl
@[simp] theorem lookup_current_11_7 : currentPadding literalP (5, 1) (3, 1) = (-601167 / 50000000) := rfl
@[simp] theorem lookup_descent_11_8 : literalDescent (5, 1) (4, 0) = (-1335989 / 400000000) := rfl
@[simp] theorem lookup_previous_11_8 : previousPadding literalP (5, 1) (4, 0) = (-109 / 250000) := rfl
@[simp] theorem lookup_current_11_8 : currentPadding literalP (5, 1) (4, 0) = (72599 / 25000000) := rfl
@[simp] theorem lookup_descent_11_9 : literalDescent (5, 1) (4, 1) = (-4283709 / 1000000000) := rfl
@[simp] theorem lookup_previous_11_9 : previousPadding literalP (5, 1) (4, 1) = (-352457 / 25000000) := rfl
@[simp] theorem lookup_current_11_9 : currentPadding literalP (5, 1) (4, 1) = (-490729 / 50000000) := rfl
@[simp] theorem lookup_descent_11_10 : literalDescent (5, 1) (5, 0) = (637579 / 200000000) := rfl
@[simp] theorem lookup_previous_11_10 : previousPadding literalP (5, 1) (5, 0) = (-71663 / 25000000) := rfl
@[simp] theorem lookup_current_11_10 : currentPadding literalP (5, 1) (5, 0) = (-1003 / 1000000) := rfl
@[simp] theorem lookup_descent_11_11 : literalDescent (5, 1) (5, 1) = (22144981 / 2000000000) := rfl
@[simp] theorem lookup_previous_11_11 : previousPadding literalP (5, 1) (5, 1) = (14065111 / 400000000) := rfl
@[simp] theorem lookup_current_11_11 : currentPadding literalP (5, 1) (5, 1) = (5993669 / 200000000) := rfl
@[simp] theorem lookup_descent_11_12 : literalDescent (5, 1) (6, 0) = (151933 / 100000000) := rfl
@[simp] theorem lookup_previous_11_12 : previousPadding literalP (5, 1) (6, 0) = (239937 / 100000000) := rfl
@[simp] theorem lookup_current_11_12 : currentPadding literalP (5, 1) (6, 0) = (-205901 / 100000000) := rfl
@[simp] theorem lookup_descent_11_13 : literalDescent (5, 1) (6, 1) = (-35429 / 200000000) := rfl
@[simp] theorem lookup_previous_11_13 : previousPadding literalP (5, 1) (6, 1) = (-490729 / 50000000) := rfl
@[simp] theorem lookup_current_11_13 : currentPadding literalP (5, 1) (6, 1) = (-210383 / 20000000) := rfl
@[simp] theorem lookup_descent_11_14 : literalDescent (5, 1) (7, 0) = (-293913 / 100000000) := rfl
@[simp] theorem lookup_previous_11_14 : previousPadding literalP (5, 1) (7, 0) = (-293913 / 100000000) := rfl
@[simp] theorem lookup_current_11_14 : currentPadding literalP (5, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_11_15 : literalDescent (5, 1) (7, 1) = (-200007 / 50000000) := rfl
@[simp] theorem lookup_previous_11_15 : previousPadding literalP (5, 1) (7, 1) = (-200007 / 50000000) := rfl
@[simp] theorem lookup_current_11_15 : currentPadding literalP (5, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_12_0 : literalDescent (6, 0) (0, 0) = (-233787 / 200000000) := rfl
@[simp] theorem lookup_previous_12_0 : previousPadding literalP (6, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_12_0 : currentPadding literalP (6, 0) (0, 0) = (-25009 / 25000000) := rfl
@[simp] theorem lookup_descent_12_1 : literalDescent (6, 0) (0, 1) = (-84467 / 40000000) := rfl
@[simp] theorem lookup_previous_12_1 : previousPadding literalP (6, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_12_1 : currentPadding literalP (6, 0) (0, 1) = (-2881 / 50000000) := rfl
@[simp] theorem lookup_descent_12_2 : literalDescent (6, 0) (1, 0) = (226493 / 200000000) := rfl
@[simp] theorem lookup_previous_12_2 : previousPadding literalP (6, 0) (1, 0) = (-169547 / 100000000) := rfl
@[simp] theorem lookup_current_12_2 : currentPadding literalP (6, 0) (1, 0) = (779 / 100000000) := rfl
@[simp] theorem lookup_descent_12_3 : literalDescent (6, 0) (1, 1) = (338913 / 400000000) := rfl
@[simp] theorem lookup_previous_12_3 : previousPadding literalP (6, 0) (1, 1) = (-11031 / 50000000) := rfl
@[simp] theorem lookup_current_12_3 : currentPadding literalP (6, 0) (1, 1) = (-185967 / 50000000) := rfl
@[simp] theorem lookup_descent_12_4 : literalDescent (6, 0) (2, 0) = (-84663 / 100000000) := rfl
@[simp] theorem lookup_previous_12_4 : previousPadding literalP (6, 0) (2, 0) = (93007 / 100000000) := rfl
@[simp] theorem lookup_current_12_4 : currentPadding literalP (6, 0) (2, 0) = (17767 / 10000000) := rfl
@[simp] theorem lookup_descent_12_5 : literalDescent (6, 0) (2, 1) = (128679 / 50000000) := rfl
@[simp] theorem lookup_previous_12_5 : previousPadding literalP (6, 0) (2, 1) = (142429 / 100000000) := rfl
@[simp] theorem lookup_current_12_5 : currentPadding literalP (6, 0) (2, 1) = (-114929 / 100000000) := rfl
@[simp] theorem lookup_descent_12_6 : literalDescent (6, 0) (3, 0) = (218549 / 25000000) := rfl
@[simp] theorem lookup_previous_12_6 : previousPadding literalP (6, 0) (3, 0) = (728037 / 25000000) := rfl
@[simp] theorem lookup_current_12_6 : currentPadding literalP (6, 0) (3, 0) = (31843 / 1562500) := rfl
@[simp] theorem lookup_descent_12_7 : literalDescent (6, 0) (3, 1) = (1344777 / 200000000) := rfl
@[simp] theorem lookup_previous_12_7 : previousPadding literalP (6, 0) (3, 1) = (3538611 / 200000000) := rfl
@[simp] theorem lookup_current_12_7 : currentPadding literalP (6, 0) (3, 1) = (1096917 / 100000000) := rfl
@[simp] theorem lookup_descent_12_8 : literalDescent (6, 0) (4, 0) = (-3106529 / 100000000) := rfl
@[simp] theorem lookup_previous_12_8 : previousPadding literalP (6, 0) (4, 0) = (-1339039 / 25000000) := rfl
@[simp] theorem lookup_current_12_8 : currentPadding literalP (6, 0) (4, 0) = (-2249627 / 100000000) := rfl
@[simp] theorem lookup_descent_12_9 : literalDescent (6, 0) (4, 1) = (-1284553 / 100000000) := rfl
@[simp] theorem lookup_previous_12_9 : previousPadding literalP (6, 0) (4, 1) = (-789233 / 50000000) := rfl
@[simp] theorem lookup_current_12_9 : currentPadding literalP (6, 0) (4, 1) = (-293913 / 100000000) := rfl
@[simp] theorem lookup_descent_12_10 : literalDescent (6, 0) (5, 0) = (359113 / 50000000) := rfl
@[simp] theorem lookup_previous_12_10 : previousPadding literalP (6, 0) (5, 0) = (-20759 / 1000000) := rfl
@[simp] theorem lookup_current_12_10 : currentPadding literalP (6, 0) (5, 0) = (-3088031 / 100000000) := rfl
@[simp] theorem lookup_descent_12_11 : literalDescent (6, 0) (5, 1) = (151933 / 100000000) := rfl
@[simp] theorem lookup_previous_12_11 : previousPadding literalP (6, 0) (5, 1) = (239937 / 100000000) := rfl
@[simp] theorem lookup_current_12_11 : currentPadding literalP (6, 0) (5, 1) = (-205901 / 100000000) := rfl
@[simp] theorem lookup_descent_12_12 : literalDescent (6, 0) (6, 0) = (491771 / 10000000) := rfl
@[simp] theorem lookup_previous_12_12 : previousPadding literalP (6, 0) (6, 0) = (7684479 / 100000000) := rfl
@[simp] theorem lookup_current_12_12 : currentPadding literalP (6, 0) (6, 0) = (3221293 / 100000000) := rfl
@[simp] theorem lookup_descent_12_13 : literalDescent (6, 0) (6, 1) = (185561 / 40000000) := rfl
@[simp] theorem lookup_previous_12_13 : previousPadding literalP (6, 0) (6, 1) = (-1003 / 1000000) := rfl
@[simp] theorem lookup_current_12_13 : currentPadding literalP (6, 0) (6, 1) = (-52239 / 50000000) := rfl
@[simp] theorem lookup_descent_12_14 : literalDescent (6, 0) (7, 0) = (-3315293 / 100000000) := rfl
@[simp] theorem lookup_previous_12_14 : previousPadding literalP (6, 0) (7, 0) = (-3088031 / 100000000) := rfl
@[simp] theorem lookup_current_12_14 : currentPadding literalP (6, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_12_15 : literalDescent (6, 0) (7, 1) = (-538359 / 400000000) := rfl
@[simp] theorem lookup_previous_12_15 : previousPadding literalP (6, 0) (7, 1) = (67841 / 50000000) := rfl
@[simp] theorem lookup_current_12_15 : currentPadding literalP (6, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_13_0 : literalDescent (6, 1) (0, 0) = (-6936549 / 2000000000) := rfl
@[simp] theorem lookup_previous_13_0 : previousPadding literalP (6, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_13_0 : currentPadding literalP (6, 1) (0, 0) = (-11583 / 50000000) := rfl
@[simp] theorem lookup_descent_13_1 : literalDescent (6, 1) (0, 1) = (-175381 / 100000000) := rfl
@[simp] theorem lookup_previous_13_1 : previousPadding literalP (6, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_13_1 : currentPadding literalP (6, 1) (0, 1) = (-541187 / 100000000) := rfl
@[simp] theorem lookup_descent_13_2 : literalDescent (6, 1) (1, 0) = (1047477 / 200000000) := rfl
@[simp] theorem lookup_previous_13_2 : previousPadding literalP (6, 1) (1, 0) = (433341 / 100000000) := rfl
@[simp] theorem lookup_current_13_2 : currentPadding literalP (6, 1) (1, 0) = (7727 / 4000000) := rfl
@[simp] theorem lookup_descent_13_3 : literalDescent (6, 1) (1, 1) = (1314307 / 400000000) := rfl
@[simp] theorem lookup_previous_13_3 : previousPadding literalP (6, 1) (1, 1) = (34667 / 12500000) := rfl
@[simp] theorem lookup_current_13_3 : currentPadding literalP (6, 1) (1, 1) = (91627 / 50000000) := rfl
@[simp] theorem lookup_descent_13_4 : literalDescent (6, 1) (2, 0) = (-126593 / 20000000) := rfl
@[simp] theorem lookup_previous_13_4 : previousPadding literalP (6, 1) (2, 0) = (-1173043 / 100000000) := rfl
@[simp] theorem lookup_current_13_4 : currentPadding literalP (6, 1) (2, 0) = (-270039 / 50000000) := rfl
@[simp] theorem lookup_descent_13_5 : literalDescent (6, 1) (2, 1) = (-6623 / 2500000) := rfl
@[simp] theorem lookup_previous_13_5 : previousPadding literalP (6, 1) (2, 1) = (-157979 / 50000000) := rfl
@[simp] theorem lookup_current_13_5 : currentPadding literalP (6, 1) (2, 1) = (-25519 / 50000000) := rfl
@[simp] theorem lookup_descent_13_6 : literalDescent (6, 1) (3, 0) = (44489 / 6250000) := rfl
@[simp] theorem lookup_previous_13_6 : previousPadding literalP (6, 1) (3, 0) = (228523 / 25000000) := rfl
@[simp] theorem lookup_current_13_6 : currentPadding literalP (6, 1) (3, 0) = (50567 / 25000000) := rfl
@[simp] theorem lookup_descent_13_7 : literalDescent (6, 1) (3, 1) = (318607 / 100000000) := rfl
@[simp] theorem lookup_previous_13_7 : previousPadding literalP (6, 1) (3, 1) = (777133 / 100000000) := rfl
@[simp] theorem lookup_current_13_7 : currentPadding literalP (6, 1) (3, 1) = (229263 / 50000000) := rfl
@[simp] theorem lookup_descent_13_8 : literalDescent (6, 1) (4, 0) = (-147591 / 50000000) := rfl
@[simp] theorem lookup_previous_13_8 : previousPadding literalP (6, 1) (4, 0) = (-31717 / 20000000) := rfl
@[simp] theorem lookup_current_13_8 : currentPadding literalP (6, 1) (4, 0) = (136597 / 100000000) := rfl
@[simp] theorem lookup_descent_13_9 : literalDescent (6, 1) (4, 1) = (-10029 / 1250000) := rfl
@[simp] theorem lookup_previous_13_9 : previousPadding literalP (6, 1) (4, 1) = (-601167 / 50000000) := rfl
@[simp] theorem lookup_current_13_9 : currentPadding literalP (6, 1) (4, 1) = (-200007 / 50000000) := rfl
@[simp] theorem lookup_descent_13_10 : literalDescent (6, 1) (5, 0) = (173449 / 2000000000) := rfl
@[simp] theorem lookup_previous_13_10 : previousPadding literalP (6, 1) (5, 0) = (72599 / 25000000) := rfl
@[simp] theorem lookup_current_13_10 : currentPadding literalP (6, 1) (5, 0) = (67841 / 50000000) := rfl
@[simp] theorem lookup_descent_13_11 : literalDescent (6, 1) (5, 1) = (-35429 / 200000000) := rfl
@[simp] theorem lookup_previous_13_11 : previousPadding literalP (6, 1) (5, 1) = (-490729 / 50000000) := rfl
@[simp] theorem lookup_current_13_11 : currentPadding literalP (6, 1) (5, 1) = (-210383 / 20000000) := rfl
@[simp] theorem lookup_descent_13_12 : literalDescent (6, 1) (6, 0) = (185561 / 40000000) := rfl
@[simp] theorem lookup_previous_13_12 : previousPadding literalP (6, 1) (6, 0) = (-1003 / 1000000) := rfl
@[simp] theorem lookup_current_13_12 : currentPadding literalP (6, 1) (6, 0) = (-52239 / 50000000) := rfl
@[simp] theorem lookup_descent_13_13 : literalDescent (6, 1) (6, 1) = (34664907 / 2000000000) := rfl
@[simp] theorem lookup_previous_13_13 : previousPadding literalP (6, 1) (6, 1) = (5993669 / 200000000) := rfl
@[simp] theorem lookup_current_13_13 : currentPadding literalP (6, 1) (6, 1) = (26132923 / 2000000000) := rfl
@[simp] theorem lookup_descent_13_14 : literalDescent (6, 1) (7, 0) = (-433163 / 100000000) := rfl
@[simp] theorem lookup_previous_13_14 : previousPadding literalP (6, 1) (7, 0) = (-205901 / 100000000) := rfl
@[simp] theorem lookup_current_13_14 : currentPadding literalP (6, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_13_15 : literalDescent (6, 1) (7, 1) = (-1400117 / 125000000) := rfl
@[simp] theorem lookup_previous_13_15 : previousPadding literalP (6, 1) (7, 1) = (-210383 / 20000000) := rfl
@[simp] theorem lookup_current_13_15 : currentPadding literalP (6, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_14_0 : literalDescent (7, 0) (0, 0) = (113631 / 50000000) := rfl
@[simp] theorem lookup_previous_14_0 : previousPadding literalP (7, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_14_0 : currentPadding literalP (7, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_descent_14_1 : literalDescent (7, 0) (0, 1) = (113631 / 50000000) := rfl
@[simp] theorem lookup_previous_14_1 : previousPadding literalP (7, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_14_1 : currentPadding literalP (7, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_descent_14_2 : literalDescent (7, 0) (1, 0) = (-25009 / 25000000) := rfl
@[simp] theorem lookup_previous_14_2 : previousPadding literalP (7, 0) (1, 0) = (-25009 / 25000000) := rfl
@[simp] theorem lookup_current_14_2 : currentPadding literalP (7, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_descent_14_3 : literalDescent (7, 0) (1, 1) = (-3641 / 1562500) := rfl
@[simp] theorem lookup_previous_14_3 : previousPadding literalP (7, 0) (1, 1) = (-2881 / 50000000) := rfl
@[simp] theorem lookup_current_14_3 : currentPadding literalP (7, 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_descent_14_4 : literalDescent (7, 0) (2, 0) = (779 / 100000000) := rfl
@[simp] theorem lookup_previous_14_4 : previousPadding literalP (7, 0) (2, 0) = (779 / 100000000) := rfl
@[simp] theorem lookup_current_14_4 : currentPadding literalP (7, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_descent_14_5 : literalDescent (7, 0) (2, 1) = (-185967 / 50000000) := rfl
@[simp] theorem lookup_previous_14_5 : previousPadding literalP (7, 0) (2, 1) = (-185967 / 50000000) := rfl
@[simp] theorem lookup_current_14_5 : currentPadding literalP (7, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_descent_14_6 : literalDescent (7, 0) (3, 0) = (17767 / 10000000) := rfl
@[simp] theorem lookup_previous_14_6 : previousPadding literalP (7, 0) (3, 0) = (17767 / 10000000) := rfl
@[simp] theorem lookup_current_14_6 : currentPadding literalP (7, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_14_7 : literalDescent (7, 0) (3, 1) = (-114929 / 100000000) := rfl
@[simp] theorem lookup_previous_14_7 : previousPadding literalP (7, 0) (3, 1) = (-114929 / 100000000) := rfl
@[simp] theorem lookup_current_14_7 : currentPadding literalP (7, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_14_8 : literalDescent (7, 0) (4, 0) = (31843 / 1562500) := rfl
@[simp] theorem lookup_previous_14_8 : previousPadding literalP (7, 0) (4, 0) = (31843 / 1562500) := rfl
@[simp] theorem lookup_current_14_8 : currentPadding literalP (7, 0) (4, 0) = 0 := rfl
@[simp] theorem lookup_descent_14_9 : literalDescent (7, 0) (4, 1) = (1096917 / 100000000) := rfl
@[simp] theorem lookup_previous_14_9 : previousPadding literalP (7, 0) (4, 1) = (1096917 / 100000000) := rfl
@[simp] theorem lookup_current_14_9 : currentPadding literalP (7, 0) (4, 1) = 0 := rfl
@[simp] theorem lookup_descent_14_10 : literalDescent (7, 0) (5, 0) = (-2249627 / 100000000) := rfl
@[simp] theorem lookup_previous_14_10 : previousPadding literalP (7, 0) (5, 0) = (-2249627 / 100000000) := rfl
@[simp] theorem lookup_current_14_10 : currentPadding literalP (7, 0) (5, 0) = 0 := rfl
@[simp] theorem lookup_descent_14_11 : literalDescent (7, 0) (5, 1) = (-293913 / 100000000) := rfl
@[simp] theorem lookup_previous_14_11 : previousPadding literalP (7, 0) (5, 1) = (-293913 / 100000000) := rfl
@[simp] theorem lookup_current_14_11 : currentPadding literalP (7, 0) (5, 1) = 0 := rfl
@[simp] theorem lookup_descent_14_12 : literalDescent (7, 0) (6, 0) = (-3315293 / 100000000) := rfl
@[simp] theorem lookup_previous_14_12 : previousPadding literalP (7, 0) (6, 0) = (-3088031 / 100000000) := rfl
@[simp] theorem lookup_current_14_12 : currentPadding literalP (7, 0) (6, 0) = 0 := rfl
@[simp] theorem lookup_descent_14_13 : literalDescent (7, 0) (6, 1) = (-433163 / 100000000) := rfl
@[simp] theorem lookup_previous_14_13 : previousPadding literalP (7, 0) (6, 1) = (-205901 / 100000000) := rfl
@[simp] theorem lookup_current_14_13 : currentPadding literalP (7, 0) (6, 1) = 0 := rfl
@[simp] theorem lookup_descent_14_14 : literalDescent (7, 0) (7, 0) = (3221293 / 100000000) := rfl
@[simp] theorem lookup_previous_14_14 : previousPadding literalP (7, 0) (7, 0) = (3221293 / 100000000) := rfl
@[simp] theorem lookup_current_14_14 : currentPadding literalP (7, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_14_15 : literalDescent (7, 0) (7, 1) = (3837 / 3125000) := rfl
@[simp] theorem lookup_previous_14_15 : previousPadding literalP (7, 0) (7, 1) = (-52239 / 50000000) := rfl
@[simp] theorem lookup_current_14_15 : currentPadding literalP (7, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_15_0 : literalDescent (7, 1) (0, 0) = (1306329 / 400000000) := rfl
@[simp] theorem lookup_previous_15_0 : previousPadding literalP (7, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_15_0 : currentPadding literalP (7, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_descent_15_1 : literalDescent (7, 1) (0, 1) = (1244891 / 1000000000) := rfl
@[simp] theorem lookup_previous_15_1 : previousPadding literalP (7, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_15_1 : currentPadding literalP (7, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_descent_15_2 : literalDescent (7, 1) (1, 0) = (-613477 / 200000000) := rfl
@[simp] theorem lookup_previous_15_2 : previousPadding literalP (7, 1) (1, 0) = (-11583 / 50000000) := rfl
@[simp] theorem lookup_current_15_2 : currentPadding literalP (7, 1) (1, 0) = 0 := rfl
@[simp] theorem lookup_descent_15_3 : literalDescent (7, 1) (1, 1) = (-3672057 / 2000000000) := rfl
@[simp] theorem lookup_previous_15_3 : previousPadding literalP (7, 1) (1, 1) = (-541187 / 100000000) := rfl
@[simp] theorem lookup_current_15_3 : currentPadding literalP (7, 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_descent_15_4 : literalDescent (7, 1) (2, 0) = (7727 / 4000000) := rfl
@[simp] theorem lookup_previous_15_4 : previousPadding literalP (7, 1) (2, 0) = (7727 / 4000000) := rfl
@[simp] theorem lookup_current_15_4 : currentPadding literalP (7, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_descent_15_5 : literalDescent (7, 1) (2, 1) = (91627 / 50000000) := rfl
@[simp] theorem lookup_previous_15_5 : previousPadding literalP (7, 1) (2, 1) = (91627 / 50000000) := rfl
@[simp] theorem lookup_current_15_5 : currentPadding literalP (7, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_descent_15_6 : literalDescent (7, 1) (3, 0) = (-270039 / 50000000) := rfl
@[simp] theorem lookup_previous_15_6 : previousPadding literalP (7, 1) (3, 0) = (-270039 / 50000000) := rfl
@[simp] theorem lookup_current_15_6 : currentPadding literalP (7, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_15_7 : literalDescent (7, 1) (3, 1) = (-25519 / 50000000) := rfl
@[simp] theorem lookup_previous_15_7 : previousPadding literalP (7, 1) (3, 1) = (-25519 / 50000000) := rfl
@[simp] theorem lookup_current_15_7 : currentPadding literalP (7, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_15_8 : literalDescent (7, 1) (4, 0) = (50567 / 25000000) := rfl
@[simp] theorem lookup_previous_15_8 : previousPadding literalP (7, 1) (4, 0) = (50567 / 25000000) := rfl
@[simp] theorem lookup_current_15_8 : currentPadding literalP (7, 1) (4, 0) = 0 := rfl
@[simp] theorem lookup_descent_15_9 : literalDescent (7, 1) (4, 1) = (229263 / 50000000) := rfl
@[simp] theorem lookup_previous_15_9 : previousPadding literalP (7, 1) (4, 1) = (229263 / 50000000) := rfl
@[simp] theorem lookup_current_15_9 : currentPadding literalP (7, 1) (4, 1) = 0 := rfl
@[simp] theorem lookup_descent_15_10 : literalDescent (7, 1) (5, 0) = (136597 / 100000000) := rfl
@[simp] theorem lookup_previous_15_10 : previousPadding literalP (7, 1) (5, 0) = (136597 / 100000000) := rfl
@[simp] theorem lookup_current_15_10 : currentPadding literalP (7, 1) (5, 0) = 0 := rfl
@[simp] theorem lookup_descent_15_11 : literalDescent (7, 1) (5, 1) = (-200007 / 50000000) := rfl
@[simp] theorem lookup_previous_15_11 : previousPadding literalP (7, 1) (5, 1) = (-200007 / 50000000) := rfl
@[simp] theorem lookup_current_15_11 : currentPadding literalP (7, 1) (5, 1) = 0 := rfl
@[simp] theorem lookup_descent_15_12 : literalDescent (7, 1) (6, 0) = (-538359 / 400000000) := rfl
@[simp] theorem lookup_previous_15_12 : previousPadding literalP (7, 1) (6, 0) = (67841 / 50000000) := rfl
@[simp] theorem lookup_current_15_12 : currentPadding literalP (7, 1) (6, 0) = 0 := rfl
@[simp] theorem lookup_descent_15_13 : literalDescent (7, 1) (6, 1) = (-1400117 / 125000000) := rfl
@[simp] theorem lookup_previous_15_13 : previousPadding literalP (7, 1) (6, 1) = (-210383 / 20000000) := rfl
@[simp] theorem lookup_current_15_13 : currentPadding literalP (7, 1) (6, 1) = 0 := rfl
@[simp] theorem lookup_descent_15_14 : literalDescent (7, 1) (7, 0) = (3837 / 3125000) := rfl
@[simp] theorem lookup_previous_15_14 : previousPadding literalP (7, 1) (7, 0) = (-52239 / 50000000) := rfl
@[simp] theorem lookup_current_15_14 : currentPadding literalP (7, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_15_15 : literalDescent (7, 1) (7, 1) = (19769587 / 2000000000) := rfl
@[simp] theorem lookup_previous_15_15 : previousPadding literalP (7, 1) (7, 1) = (26132923 / 2000000000) := rfl
@[simp] theorem lookup_current_15_15 : currentPadding literalP (7, 1) (7, 1) = 0 := rfl

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseTwo.Lower.MatrixBridge
