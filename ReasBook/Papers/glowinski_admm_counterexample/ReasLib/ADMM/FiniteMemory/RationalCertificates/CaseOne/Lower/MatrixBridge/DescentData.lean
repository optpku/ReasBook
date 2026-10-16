module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Lower.MatrixBridge.Lookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixDescent

@[expose] public section
set_option maxRecDepth 4096
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.MatrixBridge
open MatrixAssembly

-- These candidates become certificates only through the subsequent Lean proofs.
def literalDescentData : List (List ℚ) := [
  [(3982533 / 100000000), (3241839 / 100000000), (-1942941 / 50000000), (-1404877 / 50000000), (-4161301 / 100000000), (-386551 / 10000000), (81293 / 2000000), (137337 / 4000000)],
  [(3241839 / 100000000), (3810657 / 100000000), (-2391359 / 100000000), (-1851241 / 50000000), (-491513 / 10000000), (-4427 / 125000), (81293 / 2000000), (137337 / 4000000)],
  [(-1942941 / 50000000), (-2391359 / 100000000), (5558923 / 100000000), (76013 / 4000000), (273729 / 50000000), (874281 / 25000000), (-2220499 / 100000000), (-300609 / 10000000)],
  [(-1404877 / 50000000), (-1851241 / 50000000), (76013 / 4000000), (21571 / 500000), (4611849 / 100000000), (1093091 / 50000000), (-185121 / 5000000), (-27979 / 1000000)],
  [(-4161301 / 100000000), (-491513 / 10000000), (273729 / 50000000), (4611849 / 100000000), (11338169 / 100000000), (4626251 / 100000000), (-3862163 / 50000000), (-432297 / 10000000)],
  [(-386551 / 10000000), (-4427 / 125000), (874281 / 25000000), (1093091 / 50000000), (4626251 / 100000000), (6671593 / 100000000), (-851573 / 20000000), (-212647 / 4000000)],
  [(81293 / 2000000), (81293 / 2000000), (-2220499 / 100000000), (-185121 / 5000000), (-3862163 / 50000000), (-851573 / 20000000), (235207 / 4000000), (779127 / 20000000)],
  [(137337 / 4000000), (137337 / 4000000), (-300609 / 10000000), (-27979 / 1000000), (-432297 / 10000000), (-212647 / 4000000), (779127 / 20000000), (93613 / 2000000)]
]
def literalDescent : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℚ := readFlat literalDescentData
@[simp] theorem lookup_descent_0_0 : literalDescent (0, 0) (0, 0) = (3982533 / 100000000) := rfl
@[simp] theorem lookup_previous_0_0 : previousPadding literalP (0, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_0_0 : currentPadding literalP (0, 0) (0, 0) = (8350767 / 100000000) := rfl
@[simp] theorem lookup_descent_0_1 : literalDescent (0, 0) (0, 1) = (3241839 / 100000000) := rfl
@[simp] theorem lookup_previous_0_1 : previousPadding literalP (0, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_0_1 : currentPadding literalP (0, 0) (0, 1) = (-8831839 / 100000000) := rfl
@[simp] theorem lookup_descent_0_2 : literalDescent (0, 0) (1, 0) = (-1942941 / 50000000) := rfl
@[simp] theorem lookup_previous_0_2 : previousPadding literalP (0, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_current_0_2 : currentPadding literalP (0, 0) (1, 0) = (-678671 / 12500000) := rfl
@[simp] theorem lookup_descent_0_3 : literalDescent (0, 0) (1, 1) = (-1404877 / 50000000) := rfl
@[simp] theorem lookup_previous_0_3 : previousPadding literalP (0, 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_current_0_3 : currentPadding literalP (0, 0) (1, 1) = (7013879 / 100000000) := rfl
@[simp] theorem lookup_descent_0_4 : literalDescent (0, 0) (2, 0) = (-4161301 / 100000000) := rfl
@[simp] theorem lookup_previous_0_4 : previousPadding literalP (0, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_current_0_4 : currentPadding literalP (0, 0) (2, 0) = (-2220499 / 100000000) := rfl
@[simp] theorem lookup_descent_0_5 : literalDescent (0, 0) (2, 1) = (-386551 / 10000000) := rfl
@[simp] theorem lookup_previous_0_5 : previousPadding literalP (0, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_current_0_5 : currentPadding literalP (0, 0) (2, 1) = (122983 / 5000000) := rfl
@[simp] theorem lookup_descent_0_6 : literalDescent (0, 0) (3, 0) = (81293 / 2000000) := rfl
@[simp] theorem lookup_previous_0_6 : previousPadding literalP (0, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_current_0_6 : currentPadding literalP (0, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_0_7 : literalDescent (0, 0) (3, 1) = (137337 / 4000000) := rfl
@[simp] theorem lookup_previous_0_7 : previousPadding literalP (0, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_current_0_7 : currentPadding literalP (0, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_1_0 : literalDescent (0, 1) (0, 0) = (3241839 / 100000000) := rfl
@[simp] theorem lookup_previous_1_0 : previousPadding literalP (0, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_1_0 : currentPadding literalP (0, 1) (0, 0) = (-8831839 / 100000000) := rfl
@[simp] theorem lookup_descent_1_1 : literalDescent (0, 1) (0, 1) = (3810657 / 100000000) := rfl
@[simp] theorem lookup_previous_1_1 : previousPadding literalP (0, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_1_1 : currentPadding literalP (0, 1) (0, 1) = (8422643 / 100000000) := rfl
@[simp] theorem lookup_descent_1_2 : literalDescent (0, 1) (1, 0) = (-2391359 / 100000000) := rfl
@[simp] theorem lookup_previous_1_2 : previousPadding literalP (0, 1) (1, 0) = 0 := rfl
@[simp] theorem lookup_current_1_2 : currentPadding literalP (0, 1) (1, 0) = (8469609 / 100000000) := rfl
@[simp] theorem lookup_descent_1_3 : literalDescent (0, 1) (1, 1) = (-1851241 / 50000000) := rfl
@[simp] theorem lookup_previous_1_3 : previousPadding literalP (0, 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_current_1_3 : currentPadding literalP (0, 1) (1, 1) = (-2429443 / 100000000) := rfl
@[simp] theorem lookup_descent_1_4 : literalDescent (0, 1) (2, 0) = (-491513 / 10000000) := rfl
@[simp] theorem lookup_previous_1_4 : previousPadding literalP (0, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_current_1_4 : currentPadding literalP (0, 1) (2, 0) = (36223 / 10000000) := rfl
@[simp] theorem lookup_descent_1_5 : literalDescent (0, 1) (2, 1) = (-4427 / 125000) := rfl
@[simp] theorem lookup_previous_1_5 : previousPadding literalP (0, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_current_1_5 : currentPadding literalP (0, 1) (2, 1) = (-75631 / 1000000) := rfl
@[simp] theorem lookup_descent_1_6 : literalDescent (0, 1) (3, 0) = (81293 / 2000000) := rfl
@[simp] theorem lookup_previous_1_6 : previousPadding literalP (0, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_current_1_6 : currentPadding literalP (0, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_1_7 : literalDescent (0, 1) (3, 1) = (137337 / 4000000) := rfl
@[simp] theorem lookup_previous_1_7 : previousPadding literalP (0, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_current_1_7 : currentPadding literalP (0, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_2_0 : literalDescent (1, 0) (0, 0) = (-1942941 / 50000000) := rfl
@[simp] theorem lookup_previous_2_0 : previousPadding literalP (1, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_2_0 : currentPadding literalP (1, 0) (0, 0) = (-678671 / 12500000) := rfl
@[simp] theorem lookup_descent_2_1 : literalDescent (1, 0) (0, 1) = (-2391359 / 100000000) := rfl
@[simp] theorem lookup_previous_2_1 : previousPadding literalP (1, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_2_1 : currentPadding literalP (1, 0) (0, 1) = (8469609 / 100000000) := rfl
@[simp] theorem lookup_descent_2_2 : literalDescent (1, 0) (1, 0) = (5558923 / 100000000) := rfl
@[simp] theorem lookup_previous_2_2 : previousPadding literalP (1, 0) (1, 0) = (8350767 / 100000000) := rfl
@[simp] theorem lookup_current_2_2 : currentPadding literalP (1, 0) (1, 0) = (2272261 / 25000000) := rfl
@[simp] theorem lookup_descent_2_3 : literalDescent (1, 0) (1, 1) = (76013 / 4000000) := rfl
@[simp] theorem lookup_previous_2_3 : previousPadding literalP (1, 0) (1, 1) = (-8831839 / 100000000) := rfl
@[simp] theorem lookup_current_2_3 : currentPadding literalP (1, 0) (1, 1) = (-852583 / 12500000) := rfl
@[simp] theorem lookup_descent_2_4 : literalDescent (1, 0) (2, 0) = (273729 / 50000000) := rfl
@[simp] theorem lookup_previous_2_4 : previousPadding literalP (1, 0) (2, 0) = (-678671 / 12500000) := rfl
@[simp] theorem lookup_current_2_4 : currentPadding literalP (1, 0) (2, 0) = (-914919 / 25000000) := rfl
@[simp] theorem lookup_descent_2_5 : literalDescent (1, 0) (2, 1) = (874281 / 25000000) := rfl
@[simp] theorem lookup_previous_2_5 : previousPadding literalP (1, 0) (2, 1) = (7013879 / 100000000) := rfl
@[simp] theorem lookup_current_2_5 : currentPadding literalP (1, 0) (2, 1) = (-458129 / 20000000) := rfl
@[simp] theorem lookup_descent_2_6 : literalDescent (1, 0) (3, 0) = (-2220499 / 100000000) := rfl
@[simp] theorem lookup_previous_2_6 : previousPadding literalP (1, 0) (3, 0) = (-2220499 / 100000000) := rfl
@[simp] theorem lookup_current_2_6 : currentPadding literalP (1, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_2_7 : literalDescent (1, 0) (3, 1) = (-300609 / 10000000) := rfl
@[simp] theorem lookup_previous_2_7 : previousPadding literalP (1, 0) (3, 1) = (122983 / 5000000) := rfl
@[simp] theorem lookup_current_2_7 : currentPadding literalP (1, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_3_0 : literalDescent (1, 1) (0, 0) = (-1404877 / 50000000) := rfl
@[simp] theorem lookup_previous_3_0 : previousPadding literalP (1, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_3_0 : currentPadding literalP (1, 1) (0, 0) = (7013879 / 100000000) := rfl
@[simp] theorem lookup_descent_3_1 : literalDescent (1, 1) (0, 1) = (-1851241 / 50000000) := rfl
@[simp] theorem lookup_previous_3_1 : previousPadding literalP (1, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_3_1 : currentPadding literalP (1, 1) (0, 1) = (-2429443 / 100000000) := rfl
@[simp] theorem lookup_descent_3_2 : literalDescent (1, 1) (1, 0) = (76013 / 4000000) := rfl
@[simp] theorem lookup_previous_3_2 : previousPadding literalP (1, 1) (1, 0) = (-8831839 / 100000000) := rfl
@[simp] theorem lookup_current_3_2 : currentPadding literalP (1, 1) (1, 0) = (-852583 / 12500000) := rfl
@[simp] theorem lookup_descent_3_3 : literalDescent (1, 1) (1, 1) = (21571 / 500000) := rfl
@[simp] theorem lookup_previous_3_3 : previousPadding literalP (1, 1) (1, 1) = (8422643 / 100000000) := rfl
@[simp] theorem lookup_current_3_3 : currentPadding literalP (1, 1) (1, 1) = (10436193 / 100000000) := rfl
@[simp] theorem lookup_descent_3_4 : literalDescent (1, 1) (2, 0) = (4611849 / 100000000) := rfl
@[simp] theorem lookup_previous_3_4 : previousPadding literalP (1, 1) (2, 0) = (8469609 / 100000000) := rfl
@[simp] theorem lookup_current_3_4 : currentPadding literalP (1, 1) (2, 0) = (-38643 / 20000000) := rfl
@[simp] theorem lookup_descent_3_5 : literalDescent (1, 1) (2, 1) = (1093091 / 50000000) := rfl
@[simp] theorem lookup_previous_3_5 : previousPadding literalP (1, 1) (2, 1) = (-2429443 / 100000000) := rfl
@[simp] theorem lookup_current_3_5 : currentPadding literalP (1, 1) (2, 1) = (-65677 / 2000000) := rfl
@[simp] theorem lookup_descent_3_6 : literalDescent (1, 1) (3, 0) = (-185121 / 5000000) := rfl
@[simp] theorem lookup_previous_3_6 : previousPadding literalP (1, 1) (3, 0) = (36223 / 10000000) := rfl
@[simp] theorem lookup_current_3_6 : currentPadding literalP (1, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_3_7 : literalDescent (1, 1) (3, 1) = (-27979 / 1000000) := rfl
@[simp] theorem lookup_previous_3_7 : previousPadding literalP (1, 1) (3, 1) = (-75631 / 1000000) := rfl
@[simp] theorem lookup_current_3_7 : currentPadding literalP (1, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_4_0 : literalDescent (2, 0) (0, 0) = (-4161301 / 100000000) := rfl
@[simp] theorem lookup_previous_4_0 : previousPadding literalP (2, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_4_0 : currentPadding literalP (2, 0) (0, 0) = (-2220499 / 100000000) := rfl
@[simp] theorem lookup_descent_4_1 : literalDescent (2, 0) (0, 1) = (-491513 / 10000000) := rfl
@[simp] theorem lookup_previous_4_1 : previousPadding literalP (2, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_4_1 : currentPadding literalP (2, 0) (0, 1) = (36223 / 10000000) := rfl
@[simp] theorem lookup_descent_4_2 : literalDescent (2, 0) (1, 0) = (273729 / 50000000) := rfl
@[simp] theorem lookup_previous_4_2 : previousPadding literalP (2, 0) (1, 0) = (-678671 / 12500000) := rfl
@[simp] theorem lookup_current_4_2 : currentPadding literalP (2, 0) (1, 0) = (-914919 / 25000000) := rfl
@[simp] theorem lookup_descent_4_3 : literalDescent (2, 0) (1, 1) = (4611849 / 100000000) := rfl
@[simp] theorem lookup_previous_4_3 : previousPadding literalP (2, 0) (1, 1) = (8469609 / 100000000) := rfl
@[simp] theorem lookup_current_4_3 : currentPadding literalP (2, 0) (1, 1) = (-38643 / 20000000) := rfl
@[simp] theorem lookup_descent_4_4 : literalDescent (2, 0) (2, 0) = (11338169 / 100000000) := rfl
@[simp] theorem lookup_previous_4_4 : previousPadding literalP (2, 0) (2, 0) = (2272261 / 25000000) := rfl
@[simp] theorem lookup_current_4_4 : currentPadding literalP (2, 0) (2, 0) = (235207 / 4000000) := rfl
@[simp] theorem lookup_descent_4_5 : literalDescent (2, 0) (2, 1) = (4626251 / 100000000) := rfl
@[simp] theorem lookup_previous_4_5 : previousPadding literalP (2, 0) (2, 1) = (-852583 / 12500000) := rfl
@[simp] theorem lookup_current_4_5 : currentPadding literalP (2, 0) (2, 1) = (-33803 / 20000000) := rfl
@[simp] theorem lookup_descent_4_6 : literalDescent (2, 0) (3, 0) = (-3862163 / 50000000) := rfl
@[simp] theorem lookup_previous_4_6 : previousPadding literalP (2, 0) (3, 0) = (-914919 / 25000000) := rfl
@[simp] theorem lookup_current_4_6 : currentPadding literalP (2, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_4_7 : literalDescent (2, 0) (3, 1) = (-432297 / 10000000) := rfl
@[simp] theorem lookup_previous_4_7 : previousPadding literalP (2, 0) (3, 1) = (-458129 / 20000000) := rfl
@[simp] theorem lookup_current_4_7 : currentPadding literalP (2, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_5_0 : literalDescent (2, 1) (0, 0) = (-386551 / 10000000) := rfl
@[simp] theorem lookup_previous_5_0 : previousPadding literalP (2, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_5_0 : currentPadding literalP (2, 1) (0, 0) = (122983 / 5000000) := rfl
@[simp] theorem lookup_descent_5_1 : literalDescent (2, 1) (0, 1) = (-4427 / 125000) := rfl
@[simp] theorem lookup_previous_5_1 : previousPadding literalP (2, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_5_1 : currentPadding literalP (2, 1) (0, 1) = (-75631 / 1000000) := rfl
@[simp] theorem lookup_descent_5_2 : literalDescent (2, 1) (1, 0) = (874281 / 25000000) := rfl
@[simp] theorem lookup_previous_5_2 : previousPadding literalP (2, 1) (1, 0) = (7013879 / 100000000) := rfl
@[simp] theorem lookup_current_5_2 : currentPadding literalP (2, 1) (1, 0) = (-458129 / 20000000) := rfl
@[simp] theorem lookup_descent_5_3 : literalDescent (2, 1) (1, 1) = (1093091 / 50000000) := rfl
@[simp] theorem lookup_previous_5_3 : previousPadding literalP (2, 1) (1, 1) = (-2429443 / 100000000) := rfl
@[simp] theorem lookup_current_5_3 : currentPadding literalP (2, 1) (1, 1) = (-65677 / 2000000) := rfl
@[simp] theorem lookup_descent_5_4 : literalDescent (2, 1) (2, 0) = (4626251 / 100000000) := rfl
@[simp] theorem lookup_previous_5_4 : previousPadding literalP (2, 1) (2, 0) = (-852583 / 12500000) := rfl
@[simp] theorem lookup_current_5_4 : currentPadding literalP (2, 1) (2, 0) = (-33803 / 20000000) := rfl
@[simp] theorem lookup_descent_5_5 : literalDescent (2, 1) (2, 1) = (6671593 / 100000000) := rfl
@[simp] theorem lookup_previous_5_5 : previousPadding literalP (2, 1) (2, 1) = (10436193 / 100000000) := rfl
@[simp] theorem lookup_current_5_5 : currentPadding literalP (2, 1) (2, 1) = (87453 / 1000000) := rfl
@[simp] theorem lookup_descent_5_6 : literalDescent (2, 1) (3, 0) = (-851573 / 20000000) := rfl
@[simp] theorem lookup_previous_5_6 : previousPadding literalP (2, 1) (3, 0) = (-38643 / 20000000) := rfl
@[simp] theorem lookup_current_5_6 : currentPadding literalP (2, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_5_7 : literalDescent (2, 1) (3, 1) = (-212647 / 4000000) := rfl
@[simp] theorem lookup_previous_5_7 : previousPadding literalP (2, 1) (3, 1) = (-65677 / 2000000) := rfl
@[simp] theorem lookup_current_5_7 : currentPadding literalP (2, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_6_0 : literalDescent (3, 0) (0, 0) = (81293 / 2000000) := rfl
@[simp] theorem lookup_previous_6_0 : previousPadding literalP (3, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_6_0 : currentPadding literalP (3, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_descent_6_1 : literalDescent (3, 0) (0, 1) = (81293 / 2000000) := rfl
@[simp] theorem lookup_previous_6_1 : previousPadding literalP (3, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_6_1 : currentPadding literalP (3, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_descent_6_2 : literalDescent (3, 0) (1, 0) = (-2220499 / 100000000) := rfl
@[simp] theorem lookup_previous_6_2 : previousPadding literalP (3, 0) (1, 0) = (-2220499 / 100000000) := rfl
@[simp] theorem lookup_current_6_2 : currentPadding literalP (3, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_descent_6_3 : literalDescent (3, 0) (1, 1) = (-185121 / 5000000) := rfl
@[simp] theorem lookup_previous_6_3 : previousPadding literalP (3, 0) (1, 1) = (36223 / 10000000) := rfl
@[simp] theorem lookup_current_6_3 : currentPadding literalP (3, 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_descent_6_4 : literalDescent (3, 0) (2, 0) = (-3862163 / 50000000) := rfl
@[simp] theorem lookup_previous_6_4 : previousPadding literalP (3, 0) (2, 0) = (-914919 / 25000000) := rfl
@[simp] theorem lookup_current_6_4 : currentPadding literalP (3, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_descent_6_5 : literalDescent (3, 0) (2, 1) = (-851573 / 20000000) := rfl
@[simp] theorem lookup_previous_6_5 : previousPadding literalP (3, 0) (2, 1) = (-38643 / 20000000) := rfl
@[simp] theorem lookup_current_6_5 : currentPadding literalP (3, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_descent_6_6 : literalDescent (3, 0) (3, 0) = (235207 / 4000000) := rfl
@[simp] theorem lookup_previous_6_6 : previousPadding literalP (3, 0) (3, 0) = (235207 / 4000000) := rfl
@[simp] theorem lookup_current_6_6 : currentPadding literalP (3, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_6_7 : literalDescent (3, 0) (3, 1) = (779127 / 20000000) := rfl
@[simp] theorem lookup_previous_6_7 : previousPadding literalP (3, 0) (3, 1) = (-33803 / 20000000) := rfl
@[simp] theorem lookup_current_6_7 : currentPadding literalP (3, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_7_0 : literalDescent (3, 1) (0, 0) = (137337 / 4000000) := rfl
@[simp] theorem lookup_previous_7_0 : previousPadding literalP (3, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_7_0 : currentPadding literalP (3, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_descent_7_1 : literalDescent (3, 1) (0, 1) = (137337 / 4000000) := rfl
@[simp] theorem lookup_previous_7_1 : previousPadding literalP (3, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_7_1 : currentPadding literalP (3, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_descent_7_2 : literalDescent (3, 1) (1, 0) = (-300609 / 10000000) := rfl
@[simp] theorem lookup_previous_7_2 : previousPadding literalP (3, 1) (1, 0) = (122983 / 5000000) := rfl
@[simp] theorem lookup_current_7_2 : currentPadding literalP (3, 1) (1, 0) = 0 := rfl
@[simp] theorem lookup_descent_7_3 : literalDescent (3, 1) (1, 1) = (-27979 / 1000000) := rfl
@[simp] theorem lookup_previous_7_3 : previousPadding literalP (3, 1) (1, 1) = (-75631 / 1000000) := rfl
@[simp] theorem lookup_current_7_3 : currentPadding literalP (3, 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_descent_7_4 : literalDescent (3, 1) (2, 0) = (-432297 / 10000000) := rfl
@[simp] theorem lookup_previous_7_4 : previousPadding literalP (3, 1) (2, 0) = (-458129 / 20000000) := rfl
@[simp] theorem lookup_current_7_4 : currentPadding literalP (3, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_descent_7_5 : literalDescent (3, 1) (2, 1) = (-212647 / 4000000) := rfl
@[simp] theorem lookup_previous_7_5 : previousPadding literalP (3, 1) (2, 1) = (-65677 / 2000000) := rfl
@[simp] theorem lookup_current_7_5 : currentPadding literalP (3, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_descent_7_6 : literalDescent (3, 1) (3, 0) = (779127 / 20000000) := rfl
@[simp] theorem lookup_previous_7_6 : previousPadding literalP (3, 1) (3, 0) = (-33803 / 20000000) := rfl
@[simp] theorem lookup_current_7_6 : currentPadding literalP (3, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_7_7 : literalDescent (3, 1) (3, 1) = (93613 / 2000000) := rfl
@[simp] theorem lookup_previous_7_7 : previousPadding literalP (3, 1) (3, 1) = (87453 / 1000000) := rfl
@[simp] theorem lookup_current_7_7 : currentPadding literalP (3, 1) (3, 1) = 0 := rfl

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.MatrixBridge
