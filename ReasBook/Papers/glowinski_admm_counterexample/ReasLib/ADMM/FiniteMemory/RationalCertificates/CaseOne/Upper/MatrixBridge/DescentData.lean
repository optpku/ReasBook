module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Upper.MatrixBridge.Lookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixDescent

@[expose] public section
set_option maxRecDepth 4096
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.MatrixBridge
open MatrixAssembly

-- These candidates become certificates only through the subsequent Lean proofs.
def literalDescentData : List (List ℚ) := [
  [(1570073 / 50000000), (13764243 / 500000000), (-557297 / 25000000), (-540777 / 20000000), (-621951 / 12500000), (-13347293 / 500000000), (81293 / 2000000), (524099 / 20000000)],
  [(13764243 / 500000000), (15185563 / 500000000), (-14596299 / 1000000000), (-27338337 / 1000000000), (-53578687 / 1000000000), (-29237739 / 1000000000), (81293 / 2000000), (524099 / 20000000)],
  [(-557297 / 25000000), (-14596299 / 1000000000), (611539 / 20000000), (5402661 / 250000000), (115537 / 20000000), (2508869 / 1000000000), (-87887 / 6250000), (-4761607 / 500000000)],
  [(-540777 / 20000000), (-27338337 / 1000000000), (5402661 / 250000000), (1543591 / 50000000), (38025019 / 1000000000), (8930089 / 500000000), (-32596813 / 1000000000), (-21393661 / 1000000000)],
  [(-621951 / 12500000), (-53578687 / 1000000000), (115537 / 20000000), (38025019 / 1000000000), (1380917 / 10000000), (75261887 / 1000000000), (-9411247 / 100000000), (-59708219 / 1000000000)],
  [(-13347293 / 500000000), (-29237739 / 1000000000), (2508869 / 1000000000), (8930089 / 500000000), (75261887 / 1000000000), (12024663 / 250000000), (-5107617 / 100000000), (-36721091 / 1000000000)],
  [(81293 / 2000000), (81293 / 2000000), (-87887 / 6250000), (-32596813 / 1000000000), (-9411247 / 100000000), (-5107617 / 100000000), (6752789 / 100000000), (43026483 / 1000000000)],
  [(524099 / 20000000), (524099 / 20000000), (-4761607 / 500000000), (-21393661 / 1000000000), (-59708219 / 1000000000), (-36721091 / 1000000000), (43026483 / 1000000000), (15954901 / 500000000)]
]
def literalDescent : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℚ := readFlat literalDescentData
@[simp] theorem lookup_descent_0_0 : literalDescent (0, 0) (0, 0) = (1570073 / 50000000) := rfl
@[simp] theorem lookup_previous_0_0 : previousPadding literalP (0, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_0_0 : currentPadding literalP (0, 0) (0, 0) = (4596577 / 50000000) := rfl
@[simp] theorem lookup_descent_0_1 : literalDescent (0, 0) (0, 1) = (13764243 / 500000000) := rfl
@[simp] theorem lookup_previous_0_1 : previousPadding literalP (0, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_0_1 : currentPadding literalP (0, 0) (0, 1) = (-41714243 / 500000000) := rfl
@[simp] theorem lookup_descent_0_2 : literalDescent (0, 0) (1, 0) = (-557297 / 25000000) := rfl
@[simp] theorem lookup_previous_0_2 : previousPadding literalP (0, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_current_0_2 : currentPadding literalP (0, 0) (1, 0) = (-3543031 / 50000000) := rfl
@[simp] theorem lookup_descent_0_3 : literalDescent (0, 0) (1, 1) = (-540777 / 20000000) := rfl
@[simp] theorem lookup_previous_0_3 : previousPadding literalP (0, 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_current_0_3 : currentPadding literalP (0, 0) (1, 1) = (113917 / 2500000) := rfl
@[simp] theorem lookup_descent_0_4 : literalDescent (0, 0) (2, 0) = (-621951 / 12500000) := rfl
@[simp] theorem lookup_previous_0_4 : previousPadding literalP (0, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_current_0_4 : currentPadding literalP (0, 0) (2, 0) = (-87887 / 6250000) := rfl
@[simp] theorem lookup_descent_0_5 : literalDescent (0, 0) (2, 1) = (-13347293 / 500000000) := rfl
@[simp] theorem lookup_previous_0_5 : previousPadding literalP (0, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_current_0_5 : currentPadding literalP (0, 0) (2, 1) = (22567143 / 500000000) := rfl
@[simp] theorem lookup_descent_0_6 : literalDescent (0, 0) (3, 0) = (81293 / 2000000) := rfl
@[simp] theorem lookup_previous_0_6 : previousPadding literalP (0, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_current_0_6 : currentPadding literalP (0, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_0_7 : literalDescent (0, 0) (3, 1) = (524099 / 20000000) := rfl
@[simp] theorem lookup_previous_0_7 : previousPadding literalP (0, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_current_0_7 : currentPadding literalP (0, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_1_0 : literalDescent (0, 1) (0, 0) = (13764243 / 500000000) := rfl
@[simp] theorem lookup_previous_1_0 : previousPadding literalP (0, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_1_0 : currentPadding literalP (0, 1) (0, 0) = (-41714243 / 500000000) := rfl
@[simp] theorem lookup_descent_1_1 : literalDescent (0, 1) (0, 1) = (15185563 / 500000000) := rfl
@[simp] theorem lookup_previous_1_1 : previousPadding literalP (0, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_1_1 : currentPadding literalP (0, 1) (0, 1) = (45980937 / 500000000) := rfl
@[simp] theorem lookup_descent_1_2 : literalDescent (0, 1) (1, 0) = (-14596299 / 1000000000) := rfl
@[simp] theorem lookup_previous_1_2 : previousPadding literalP (0, 1) (1, 0) = 0 := rfl
@[simp] theorem lookup_current_1_2 : currentPadding literalP (0, 1) (1, 0) = (75378799 / 1000000000) := rfl
@[simp] theorem lookup_descent_1_3 : literalDescent (0, 1) (1, 1) = (-27338337 / 1000000000) := rfl
@[simp] theorem lookup_previous_1_3 : previousPadding literalP (0, 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_current_1_3 : currentPadding literalP (0, 1) (1, 1) = (-21647613 / 1000000000) := rfl
@[simp] theorem lookup_descent_1_4 : literalDescent (0, 1) (2, 0) = (-53578687 / 1000000000) := rfl
@[simp] theorem lookup_previous_1_4 : previousPadding literalP (0, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_current_1_4 : currentPadding literalP (0, 1) (2, 0) = (8049687 / 1000000000) := rfl
@[simp] theorem lookup_descent_1_5 : literalDescent (0, 1) (2, 1) = (-29237739 / 1000000000) := rfl
@[simp] theorem lookup_previous_1_5 : previousPadding literalP (0, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_current_1_5 : currentPadding literalP (0, 1) (2, 1) = (-88106461 / 1000000000) := rfl
@[simp] theorem lookup_descent_1_6 : literalDescent (0, 1) (3, 0) = (81293 / 2000000) := rfl
@[simp] theorem lookup_previous_1_6 : previousPadding literalP (0, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_current_1_6 : currentPadding literalP (0, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_1_7 : literalDescent (0, 1) (3, 1) = (524099 / 20000000) := rfl
@[simp] theorem lookup_previous_1_7 : previousPadding literalP (0, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_current_1_7 : currentPadding literalP (0, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_2_0 : literalDescent (1, 0) (0, 0) = (-557297 / 25000000) := rfl
@[simp] theorem lookup_previous_2_0 : previousPadding literalP (1, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_2_0 : currentPadding literalP (1, 0) (0, 0) = (-3543031 / 50000000) := rfl
@[simp] theorem lookup_descent_2_1 : literalDescent (1, 0) (0, 1) = (-14596299 / 1000000000) := rfl
@[simp] theorem lookup_previous_2_1 : previousPadding literalP (1, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_2_1 : currentPadding literalP (1, 0) (0, 1) = (75378799 / 1000000000) := rfl
@[simp] theorem lookup_descent_2_2 : literalDescent (1, 0) (1, 0) = (611539 / 20000000) := rfl
@[simp] theorem lookup_previous_2_2 : previousPadding literalP (1, 0) (1, 0) = (4596577 / 50000000) := rfl
@[simp] theorem lookup_current_2_2 : currentPadding literalP (1, 0) (1, 0) = (12432659 / 100000000) := rfl
@[simp] theorem lookup_descent_2_3 : literalDescent (1, 0) (1, 1) = (5402661 / 250000000) := rfl
@[simp] theorem lookup_previous_2_3 : previousPadding literalP (1, 0) (1, 1) = (-41714243 / 500000000) := rfl
@[simp] theorem lookup_current_2_3 : currentPadding literalP (1, 0) (1, 1) = (-3513713 / 100000000) := rfl
@[simp] theorem lookup_descent_2_4 : literalDescent (1, 0) (2, 0) = (115537 / 20000000) := rfl
@[simp] theorem lookup_previous_2_4 : previousPadding literalP (1, 0) (2, 0) = (-3543031 / 50000000) := rfl
@[simp] theorem lookup_current_2_4 : currentPadding literalP (1, 0) (2, 0) = (-5346597 / 100000000) := rfl
@[simp] theorem lookup_descent_2_5 : literalDescent (1, 0) (2, 1) = (2508869 / 1000000000) := rfl
@[simp] theorem lookup_previous_2_5 : previousPadding literalP (1, 0) (2, 1) = (113917 / 2500000) := rfl
@[simp] theorem lookup_current_2_5 : currentPadding literalP (1, 0) (2, 1) = (-47514269 / 1000000000) := rfl
@[simp] theorem lookup_descent_2_6 : literalDescent (1, 0) (3, 0) = (-87887 / 6250000) := rfl
@[simp] theorem lookup_previous_2_6 : previousPadding literalP (1, 0) (3, 0) = (-87887 / 6250000) := rfl
@[simp] theorem lookup_current_2_6 : currentPadding literalP (1, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_2_7 : literalDescent (1, 0) (3, 1) = (-4761607 / 500000000) := rfl
@[simp] theorem lookup_previous_2_7 : previousPadding literalP (1, 0) (3, 1) = (22567143 / 500000000) := rfl
@[simp] theorem lookup_current_2_7 : currentPadding literalP (1, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_3_0 : literalDescent (1, 1) (0, 0) = (-540777 / 20000000) := rfl
@[simp] theorem lookup_previous_3_0 : previousPadding literalP (1, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_3_0 : currentPadding literalP (1, 1) (0, 0) = (113917 / 2500000) := rfl
@[simp] theorem lookup_descent_3_1 : literalDescent (1, 1) (0, 1) = (-27338337 / 1000000000) := rfl
@[simp] theorem lookup_previous_3_1 : previousPadding literalP (1, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_3_1 : currentPadding literalP (1, 1) (0, 1) = (-21647613 / 1000000000) := rfl
@[simp] theorem lookup_descent_3_2 : literalDescent (1, 1) (1, 0) = (5402661 / 250000000) := rfl
@[simp] theorem lookup_previous_3_2 : previousPadding literalP (1, 1) (1, 0) = (-41714243 / 500000000) := rfl
@[simp] theorem lookup_current_3_2 : currentPadding literalP (1, 1) (1, 0) = (-3513713 / 100000000) := rfl
@[simp] theorem lookup_descent_3_3 : literalDescent (1, 1) (1, 1) = (1543591 / 50000000) := rfl
@[simp] theorem lookup_previous_3_3 : previousPadding literalP (1, 1) (1, 1) = (45980937 / 500000000) := rfl
@[simp] theorem lookup_current_3_3 : currentPadding literalP (1, 1) (1, 1) = (49850477 / 500000000) := rfl
@[simp] theorem lookup_descent_3_4 : literalDescent (1, 1) (2, 0) = (38025019 / 1000000000) := rfl
@[simp] theorem lookup_previous_3_4 : previousPadding literalP (1, 1) (2, 0) = (75378799 / 1000000000) := rfl
@[simp] theorem lookup_current_3_4 : currentPadding literalP (1, 1) (2, 0) = (-1042967 / 100000000) := rfl
@[simp] theorem lookup_descent_3_5 : literalDescent (1, 1) (2, 1) = (8930089 / 500000000) := rfl
@[simp] theorem lookup_previous_3_5 : previousPadding literalP (1, 1) (2, 1) = (-21647613 / 1000000000) := rfl
@[simp] theorem lookup_current_3_5 : currentPadding literalP (1, 1) (2, 1) = (-24527141 / 1000000000) := rfl
@[simp] theorem lookup_descent_3_6 : literalDescent (1, 1) (3, 0) = (-32596813 / 1000000000) := rfl
@[simp] theorem lookup_previous_3_6 : previousPadding literalP (1, 1) (3, 0) = (8049687 / 1000000000) := rfl
@[simp] theorem lookup_current_3_6 : currentPadding literalP (1, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_3_7 : literalDescent (1, 1) (3, 1) = (-21393661 / 1000000000) := rfl
@[simp] theorem lookup_previous_3_7 : previousPadding literalP (1, 1) (3, 1) = (-88106461 / 1000000000) := rfl
@[simp] theorem lookup_current_3_7 : currentPadding literalP (1, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_4_0 : literalDescent (2, 0) (0, 0) = (-621951 / 12500000) := rfl
@[simp] theorem lookup_previous_4_0 : previousPadding literalP (2, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_4_0 : currentPadding literalP (2, 0) (0, 0) = (-87887 / 6250000) := rfl
@[simp] theorem lookup_descent_4_1 : literalDescent (2, 0) (0, 1) = (-53578687 / 1000000000) := rfl
@[simp] theorem lookup_previous_4_1 : previousPadding literalP (2, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_4_1 : currentPadding literalP (2, 0) (0, 1) = (8049687 / 1000000000) := rfl
@[simp] theorem lookup_descent_4_2 : literalDescent (2, 0) (1, 0) = (115537 / 20000000) := rfl
@[simp] theorem lookup_previous_4_2 : previousPadding literalP (2, 0) (1, 0) = (-3543031 / 50000000) := rfl
@[simp] theorem lookup_current_4_2 : currentPadding literalP (2, 0) (1, 0) = (-5346597 / 100000000) := rfl
@[simp] theorem lookup_descent_4_3 : literalDescent (2, 0) (1, 1) = (38025019 / 1000000000) := rfl
@[simp] theorem lookup_previous_4_3 : previousPadding literalP (2, 0) (1, 1) = (75378799 / 1000000000) := rfl
@[simp] theorem lookup_current_4_3 : currentPadding literalP (2, 0) (1, 1) = (-1042967 / 100000000) := rfl
@[simp] theorem lookup_descent_4_4 : literalDescent (2, 0) (2, 0) = (1380917 / 10000000) := rfl
@[simp] theorem lookup_previous_4_4 : previousPadding literalP (2, 0) (2, 0) = (12432659 / 100000000) := rfl
@[simp] theorem lookup_current_4_4 : currentPadding literalP (2, 0) (2, 0) = (6752789 / 100000000) := rfl
@[simp] theorem lookup_descent_4_5 : literalDescent (2, 0) (2, 1) = (75261887 / 1000000000) := rfl
@[simp] theorem lookup_previous_4_5 : previousPadding literalP (2, 0) (2, 1) = (-3513713 / 100000000) := rfl
@[simp] theorem lookup_current_4_5 : currentPadding literalP (2, 0) (2, 1) = (2379983 / 1000000000) := rfl
@[simp] theorem lookup_descent_4_6 : literalDescent (2, 0) (3, 0) = (-9411247 / 100000000) := rfl
@[simp] theorem lookup_previous_4_6 : previousPadding literalP (2, 0) (3, 0) = (-5346597 / 100000000) := rfl
@[simp] theorem lookup_current_4_6 : currentPadding literalP (2, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_4_7 : literalDescent (2, 0) (3, 1) = (-59708219 / 1000000000) := rfl
@[simp] theorem lookup_previous_4_7 : previousPadding literalP (2, 0) (3, 1) = (-47514269 / 1000000000) := rfl
@[simp] theorem lookup_current_4_7 : currentPadding literalP (2, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_5_0 : literalDescent (2, 1) (0, 0) = (-13347293 / 500000000) := rfl
@[simp] theorem lookup_previous_5_0 : previousPadding literalP (2, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_5_0 : currentPadding literalP (2, 1) (0, 0) = (22567143 / 500000000) := rfl
@[simp] theorem lookup_descent_5_1 : literalDescent (2, 1) (0, 1) = (-29237739 / 1000000000) := rfl
@[simp] theorem lookup_previous_5_1 : previousPadding literalP (2, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_5_1 : currentPadding literalP (2, 1) (0, 1) = (-88106461 / 1000000000) := rfl
@[simp] theorem lookup_descent_5_2 : literalDescent (2, 1) (1, 0) = (2508869 / 1000000000) := rfl
@[simp] theorem lookup_previous_5_2 : previousPadding literalP (2, 1) (1, 0) = (113917 / 2500000) := rfl
@[simp] theorem lookup_current_5_2 : currentPadding literalP (2, 1) (1, 0) = (-47514269 / 1000000000) := rfl
@[simp] theorem lookup_descent_5_3 : literalDescent (2, 1) (1, 1) = (8930089 / 500000000) := rfl
@[simp] theorem lookup_previous_5_3 : previousPadding literalP (2, 1) (1, 1) = (-21647613 / 1000000000) := rfl
@[simp] theorem lookup_current_5_3 : currentPadding literalP (2, 1) (1, 1) = (-24527141 / 1000000000) := rfl
@[simp] theorem lookup_descent_5_4 : literalDescent (2, 1) (2, 0) = (75261887 / 1000000000) := rfl
@[simp] theorem lookup_previous_5_4 : previousPadding literalP (2, 1) (2, 0) = (-3513713 / 100000000) := rfl
@[simp] theorem lookup_current_5_4 : currentPadding literalP (2, 1) (2, 0) = (2379983 / 1000000000) := rfl
@[simp] theorem lookup_descent_5_5 : literalDescent (2, 1) (2, 1) = (12024663 / 250000000) := rfl
@[simp] theorem lookup_previous_5_5 : previousPadding literalP (2, 1) (2, 1) = (49850477 / 500000000) := rfl
@[simp] theorem lookup_current_5_5 : currentPadding literalP (2, 1) (2, 1) = (44407451 / 500000000) := rfl
@[simp] theorem lookup_descent_5_6 : literalDescent (2, 1) (3, 0) = (-5107617 / 100000000) := rfl
@[simp] theorem lookup_previous_5_6 : previousPadding literalP (2, 1) (3, 0) = (-1042967 / 100000000) := rfl
@[simp] theorem lookup_current_5_6 : currentPadding literalP (2, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_5_7 : literalDescent (2, 1) (3, 1) = (-36721091 / 1000000000) := rfl
@[simp] theorem lookup_previous_5_7 : previousPadding literalP (2, 1) (3, 1) = (-24527141 / 1000000000) := rfl
@[simp] theorem lookup_current_5_7 : currentPadding literalP (2, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_6_0 : literalDescent (3, 0) (0, 0) = (81293 / 2000000) := rfl
@[simp] theorem lookup_previous_6_0 : previousPadding literalP (3, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_6_0 : currentPadding literalP (3, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_descent_6_1 : literalDescent (3, 0) (0, 1) = (81293 / 2000000) := rfl
@[simp] theorem lookup_previous_6_1 : previousPadding literalP (3, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_6_1 : currentPadding literalP (3, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_descent_6_2 : literalDescent (3, 0) (1, 0) = (-87887 / 6250000) := rfl
@[simp] theorem lookup_previous_6_2 : previousPadding literalP (3, 0) (1, 0) = (-87887 / 6250000) := rfl
@[simp] theorem lookup_current_6_2 : currentPadding literalP (3, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_descent_6_3 : literalDescent (3, 0) (1, 1) = (-32596813 / 1000000000) := rfl
@[simp] theorem lookup_previous_6_3 : previousPadding literalP (3, 0) (1, 1) = (8049687 / 1000000000) := rfl
@[simp] theorem lookup_current_6_3 : currentPadding literalP (3, 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_descent_6_4 : literalDescent (3, 0) (2, 0) = (-9411247 / 100000000) := rfl
@[simp] theorem lookup_previous_6_4 : previousPadding literalP (3, 0) (2, 0) = (-5346597 / 100000000) := rfl
@[simp] theorem lookup_current_6_4 : currentPadding literalP (3, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_descent_6_5 : literalDescent (3, 0) (2, 1) = (-5107617 / 100000000) := rfl
@[simp] theorem lookup_previous_6_5 : previousPadding literalP (3, 0) (2, 1) = (-1042967 / 100000000) := rfl
@[simp] theorem lookup_current_6_5 : currentPadding literalP (3, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_descent_6_6 : literalDescent (3, 0) (3, 0) = (6752789 / 100000000) := rfl
@[simp] theorem lookup_previous_6_6 : previousPadding literalP (3, 0) (3, 0) = (6752789 / 100000000) := rfl
@[simp] theorem lookup_current_6_6 : currentPadding literalP (3, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_6_7 : literalDescent (3, 0) (3, 1) = (43026483 / 1000000000) := rfl
@[simp] theorem lookup_previous_6_7 : previousPadding literalP (3, 0) (3, 1) = (2379983 / 1000000000) := rfl
@[simp] theorem lookup_current_6_7 : currentPadding literalP (3, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_7_0 : literalDescent (3, 1) (0, 0) = (524099 / 20000000) := rfl
@[simp] theorem lookup_previous_7_0 : previousPadding literalP (3, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_7_0 : currentPadding literalP (3, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_descent_7_1 : literalDescent (3, 1) (0, 1) = (524099 / 20000000) := rfl
@[simp] theorem lookup_previous_7_1 : previousPadding literalP (3, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_7_1 : currentPadding literalP (3, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_descent_7_2 : literalDescent (3, 1) (1, 0) = (-4761607 / 500000000) := rfl
@[simp] theorem lookup_previous_7_2 : previousPadding literalP (3, 1) (1, 0) = (22567143 / 500000000) := rfl
@[simp] theorem lookup_current_7_2 : currentPadding literalP (3, 1) (1, 0) = 0 := rfl
@[simp] theorem lookup_descent_7_3 : literalDescent (3, 1) (1, 1) = (-21393661 / 1000000000) := rfl
@[simp] theorem lookup_previous_7_3 : previousPadding literalP (3, 1) (1, 1) = (-88106461 / 1000000000) := rfl
@[simp] theorem lookup_current_7_3 : currentPadding literalP (3, 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_descent_7_4 : literalDescent (3, 1) (2, 0) = (-59708219 / 1000000000) := rfl
@[simp] theorem lookup_previous_7_4 : previousPadding literalP (3, 1) (2, 0) = (-47514269 / 1000000000) := rfl
@[simp] theorem lookup_current_7_4 : currentPadding literalP (3, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_descent_7_5 : literalDescent (3, 1) (2, 1) = (-36721091 / 1000000000) := rfl
@[simp] theorem lookup_previous_7_5 : previousPadding literalP (3, 1) (2, 1) = (-24527141 / 1000000000) := rfl
@[simp] theorem lookup_current_7_5 : currentPadding literalP (3, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_descent_7_6 : literalDescent (3, 1) (3, 0) = (43026483 / 1000000000) := rfl
@[simp] theorem lookup_previous_7_6 : previousPadding literalP (3, 1) (3, 0) = (2379983 / 1000000000) := rfl
@[simp] theorem lookup_current_7_6 : currentPadding literalP (3, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_7_7 : literalDescent (3, 1) (3, 1) = (15954901 / 500000000) := rfl
@[simp] theorem lookup_previous_7_7 : previousPadding literalP (3, 1) (3, 1) = (44407451 / 500000000) := rfl
@[simp] theorem lookup_current_7_7 : currentPadding literalP (3, 1) (3, 1) = 0 := rfl

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.MatrixBridge
