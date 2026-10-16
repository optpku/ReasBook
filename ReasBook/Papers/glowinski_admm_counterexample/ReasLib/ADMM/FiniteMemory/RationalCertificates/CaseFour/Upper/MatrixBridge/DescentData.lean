module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Upper.MatrixBridge.Lookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixDescent

@[expose] public section
set_option maxRecDepth 4096
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Upper.MatrixBridge
open MatrixAssembly

-- These candidates become certificates only through the subsequent Lean proofs.
def literalDescentData : List (List ℚ) := [
  [(19813857 / 10000000000), (12226239 / 20000000000), (-7429389 / 2000000000), (-1187019043 / 1000000000000), (-10139801 / 10000000000), (266407237 / 500000000000), (55285251 / 10000000000), (451277541 / 4000000000000), (-38991227 / 20000000000), (-5573931437 / 4000000000000), (8842821 / 10000000000), (347422703 / 200000000000), (-5175427 / 2500000000), (-331230321 / 2000000000000), (-23479143 / 20000000000), (16616327 / 62500000000), (233761 / 400000000), (-418016227 / 1000000000000), (1887537 / 2000000000), (-191574533 / 2000000000000)],
  [(12226239 / 20000000000), (296759187 / 400000000000), (-1642753713 / 800000000000), (-568854641 / 800000000000), (-827719 / 1000000000), (-164200599 / 500000000000), (3421284473 / 800000000000), (146583399 / 400000000000), (-6960307 / 4000000000), (-4463921009 / 4000000000000), (3403207 / 4000000000), (1928852689 / 2000000000000), (-1336127 / 20000000000), (659606701 / 4000000000000), (-28992191 / 20000000000), (1368367297 / 4000000000000), (-272417 / 500000000), (-65692707 / 200000000000), (1887537 / 2000000000), (-38345209 / 400000000000)],
  [(-7429389 / 2000000000), (-1642753713 / 800000000000), (27209513 / 2500000000), (2647678373 / 800000000000), (-2992673 / 2000000000), (-1370686603 / 1000000000000), (-312988647 / 20000000000), (-19628143 / 250000000000), (13076461 / 1250000000), (71761909 / 20000000000), (-52679853 / 20000000000), (-89791801 / 20000000000), (13989309 / 5000000000), (22425099 / 20000000000), (-2741899 / 5000000000), (-823173 / 500000000), (16742321 / 10000000000), (1995537 / 1000000000), (-17742321 / 10000000000), (-93977 / 250000000)],
  [(-1187019043 / 1000000000000), (-568854641 / 800000000000), (2647678373 / 800000000000), (6164870491 / 4000000000000), (-4418286253 / 4000000000000), (-1852734763 / 4000000000000), (-22348539507 / 4000000000000), (-2165093889 / 4000000000000), (1057717183 / 200000000000), (2739104097 / 2000000000000), (-643290559 / 500000000000), (-7471768719 / 4000000000000), (2715327169 / 4000000000000), (141054337 / 500000000000), (162672047 / 250000000000), (-1397694013 / 4000000000000), (1652724079 / 2000000000000), (1041684971 / 1000000000000), (-15887593 / 10000000000), (-301672169 / 1000000000000)],
  [(-10139801 / 10000000000), (-827719 / 1000000000), (-2992673 / 2000000000), (-4418286253 / 4000000000000), (13098373 / 1000000000), (6565610543 / 2000000000000), (-17246117 / 2500000000), (-8112878741 / 4000000000000), (-25574771 / 2000000000), (1933547277 / 1000000000000), (16593809 / 2000000000), (7471657 / 5000000000), (-27189693 / 10000000000), (-10107251 / 2500000000), (14868251 / 2500000000), (2593673 / 1250000000), (-21748521 / 10000000000), (-22340419 / 10000000000), (-631519 / 2500000000), (7259151 / 5000000000)],
  [(266407237 / 500000000000), (-164200599 / 500000000000), (-1370686603 / 1000000000000), (-1852734763 / 4000000000000), (6565610543 / 2000000000000), (1466152469 / 800000000000), (-19389617 / 10000000000), (-282242119 / 400000000000), (-23363691 / 5000000000), (-5309887 / 10000000000), (1967751863 / 400000000000), (7473609 / 10000000000), (-406347 / 2000000000), (-2554809 / 2000000000), (-251163 / 625000000), (8212547 / 10000000000), (-752433 / 10000000000), (-1253 / 16000000), (-723353 / 10000000000), (-174103 / 10000000000)],
  [(55285251 / 10000000000), (3421284473 / 800000000000), (-312988647 / 20000000000), (-22348539507 / 4000000000000), (-17246117 / 2500000000), (-19389617 / 10000000000), (81131249 / 2000000000), (3883666981 / 800000000000), (-302975579 / 20000000000), (-33717611363 / 4000000000000), (-28814781 / 2000000000), (37615679 / 5000000000), (78085347 / 10000000000), (454907 / 125000000), (-7429137 / 2500000000), (-8024187 / 2500000000), (-9437591 / 2500000000), (-17603637 / 10000000000), (9896111 / 2000000000), (394973 / 625000000)],
  [(451277541 / 4000000000000), (146583399 / 400000000000), (-19628143 / 250000000000), (-2165093889 / 4000000000000), (-8112878741 / 4000000000000), (-282242119 / 400000000000), (3883666981 / 800000000000), (56886093 / 25000000000), (-65887223 / 20000000000), (-5857435391 / 4000000000000), (-16770321 / 5000000000), (-2364193 / 5000000000), (26079286359 / 4000000000000), (3536177 / 5000000000), (-1059636997 / 500000000000), (-4663093 / 5000000000), (-938131 / 1250000000), (2569977 / 2000000000), (1377117 / 10000000000), (-5174313 / 10000000000)],
  [(-38991227 / 20000000000), (-6960307 / 4000000000), (13076461 / 1250000000), (1057717183 / 200000000000), (-25574771 / 2000000000), (-23363691 / 5000000000), (-302975579 / 20000000000), (-65887223 / 20000000000), (464555833 / 10000000000), (37244731 / 4000000000), (-111908109 / 5000000000), (-1626664973 / 200000000000), (-123185883 / 5000000000), (27544907 / 5000000000), (208576891 / 10000000000), (145087 / 10000000000), (3708419 / 1000000000), (-11915681 / 2500000000), (-143073 / 31250000), (12417573 / 5000000000)],
  [(-5573931437 / 4000000000000), (-4463921009 / 4000000000000), (71761909 / 20000000000), (2739104097 / 2000000000000), (1933547277 / 1000000000000), (-5309887 / 10000000000), (-33717611363 / 4000000000000), (-5857435391 / 4000000000000), (37244731 / 4000000000), (1247369849 / 250000000000), (-12051117 / 2000000000), (-5342176489 / 2000000000000), (-39608981 / 5000000000), (-6850957 / 10000000000), (10727180729 / 1000000000000), (278003 / 500000000), (370415297 / 500000000000), (-8777049 / 5000000000), (-6326491 / 2500000000), (13078841 / 10000000000)],
  [(8842821 / 10000000000), (3403207 / 4000000000), (-52679853 / 20000000000), (-643290559 / 500000000000), (16593809 / 2000000000), (1967751863 / 400000000000), (-28814781 / 2000000000), (-16770321 / 5000000000), (-111908109 / 5000000000), (-12051117 / 2000000000), (263696429 / 5000000000), (110995869 / 20000000000), (46071073 / 20000000000), (-14533771479 / 2000000000000), (-167889543 / 5000000000), (4184541 / 625000000), (6654663 / 2500000000), (23709477 / 5000000000), (61150223 / 10000000000), (-48240463 / 10000000000)],
  [(347422703 / 200000000000), (1928852689 / 2000000000000), (-89791801 / 20000000000), (-7471768719 / 4000000000000), (7471657 / 5000000000), (7473609 / 10000000000), (37615679 / 5000000000), (-2364193 / 5000000000), (-1626664973 / 200000000000), (-5342176489 / 2000000000000), (110995869 / 20000000000), (1008997801 / 200000000000), (-22797173 / 20000000000), (-359870501 / 4000000000000), (-13745167 / 2000000000), (-8993809 / 10000000000), (786023 / 2500000000), (-1103883 / 1250000000), (40165737 / 10000000000), (1275477 / 10000000000)],
  [(-5175427 / 2500000000), (-1336127 / 20000000000), (13989309 / 5000000000), (2715327169 / 4000000000000), (-27189693 / 10000000000), (-406347 / 2000000000), (78085347 / 10000000000), (26079286359 / 4000000000000), (-123185883 / 5000000000), (-39608981 / 5000000000), (46071073 / 20000000000), (-22797173 / 20000000000), (108284327 / 2500000000), (-99947 / 400000000), (-463440661 / 20000000000), (-2570923591 / 500000000000), (-5995921 / 5000000000), (127217863 / 10000000000), (-2426147 / 1000000000), (-51970903 / 10000000000)],
  [(-331230321 / 2000000000000), (659606701 / 4000000000000), (22425099 / 20000000000), (141054337 / 500000000000), (-10107251 / 2500000000), (-2554809 / 2000000000), (454907 / 125000000), (3536177 / 5000000000), (27544907 / 5000000000), (-6850957 / 10000000000), (-14533771479 / 2000000000000), (-359870501 / 4000000000000), (-99947 / 400000000), (12736454601 / 4000000000000), (3882707 / 4000000000), (-7103582697 / 4000000000000), (-6831851 / 10000000000), (-12614953 / 10000000000), (365089 / 312500000), (3757497 / 5000000000)],
  [(-23479143 / 20000000000), (-28992191 / 20000000000), (-2741899 / 5000000000), (162672047 / 250000000000), (14868251 / 2500000000), (-251163 / 625000000), (-7429137 / 2500000000), (-1059636997 / 500000000000), (208576891 / 10000000000), (10727180729 / 1000000000000), (-167889543 / 5000000000), (-13745167 / 2000000000), (-463440661 / 20000000000), (3882707 / 4000000000), (11965421 / 250000000), (49233621 / 20000000000), (-6261507 / 1250000000), (-10705533773 / 1000000000000), (-16427069 / 2000000000), (67386349 / 10000000000)],
  [(16616327 / 62500000000), (1368367297 / 4000000000000), (-823173 / 500000000), (-1397694013 / 4000000000000), (2593673 / 1250000000), (8212547 / 10000000000), (-8024187 / 2500000000), (-4663093 / 5000000000), (145087 / 10000000000), (278003 / 500000000), (4184541 / 625000000), (-8993809 / 10000000000), (-2570923591 / 500000000000), (-7103582697 / 4000000000000), (49233621 / 20000000000), (13784470073 / 4000000000000), (-8414527 / 10000000000), (-233612453 / 200000000000), (-6729343 / 10000000000), (-400891 / 10000000000)],
  [(233761 / 400000000), (-272417 / 500000000), (16742321 / 10000000000), (1652724079 / 2000000000000), (-21748521 / 10000000000), (-752433 / 10000000000), (-9437591 / 2500000000), (-938131 / 1250000000), (3708419 / 1000000000), (370415297 / 500000000000), (6654663 / 2500000000), (786023 / 2500000000), (-5995921 / 5000000000), (-6831851 / 10000000000), (-6261507 / 1250000000), (-8414527 / 10000000000), (9108973 / 2500000000), (10507777 / 5000000000), (-1142297 / 10000000000), (-2175874667 / 2000000000000)],
  [(-418016227 / 1000000000000), (-65692707 / 200000000000), (1995537 / 1000000000), (1041684971 / 1000000000000), (-22340419 / 10000000000), (-1253 / 16000000), (-17603637 / 10000000000), (2569977 / 2000000000), (-11915681 / 2500000000), (-8777049 / 5000000000), (23709477 / 5000000000), (-1103883 / 1250000000), (127217863 / 10000000000), (-12614953 / 10000000000), (-10705533773 / 1000000000000), (-233612453 / 200000000000), (10507777 / 5000000000), (11844657413 / 2000000000000), (-16765461 / 10000000000), (-1109660951 / 400000000000)],
  [(1887537 / 2000000000), (1887537 / 2000000000), (-17742321 / 10000000000), (-15887593 / 10000000000), (-631519 / 2500000000), (-723353 / 10000000000), (9896111 / 2000000000), (1377117 / 10000000000), (-143073 / 31250000), (-6326491 / 2500000000), (61150223 / 10000000000), (40165737 / 10000000000), (-2426147 / 1000000000), (365089 / 312500000), (-16427069 / 2000000000), (-6729343 / 10000000000), (-1142297 / 10000000000), (-16765461 / 10000000000), (26761203 / 5000000000), (2748327 / 10000000000)],
  [(-191574533 / 2000000000000), (-38345209 / 400000000000), (-93977 / 250000000), (-301672169 / 1000000000000), (7259151 / 5000000000), (-174103 / 10000000000), (394973 / 625000000), (-5174313 / 10000000000), (12417573 / 5000000000), (13078841 / 10000000000), (-48240463 / 10000000000), (1275477 / 10000000000), (-51970903 / 10000000000), (3757497 / 5000000000), (67386349 / 10000000000), (-400891 / 10000000000), (-2175874667 / 2000000000000), (-1109660951 / 400000000000), (2748327 / 10000000000), (1559687069 / 1000000000000)]
]
def literalDescent : Matrix (Fin 10 × Fin 2) (Fin 10 × Fin 2) ℚ := readFlat literalDescentData
@[simp] theorem lookup_descent_0_0 : literalDescent (0, 0) (0, 0) = (19813857 / 10000000000) := rfl
@[simp] theorem lookup_previous_0_0 : previousPadding literalP (0, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_0_0 : currentPadding literalP (0, 0) (0, 0) = (655630989 / 5000000000) := rfl
@[simp] theorem lookup_descent_0_1 : literalDescent (0, 0) (0, 1) = (12226239 / 20000000000) := rfl
@[simp] theorem lookup_previous_0_1 : previousPadding literalP (0, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_0_1 : currentPadding literalP (0, 0) (0, 1) = (1627883 / 312500000) := rfl
@[simp] theorem lookup_descent_0_2 : literalDescent (0, 0) (1, 0) = (-7429389 / 2000000000) := rfl
@[simp] theorem lookup_previous_0_2 : previousPadding literalP (0, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_current_0_2 : currentPadding literalP (0, 0) (1, 0) = (-628391041 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_3 : literalDescent (0, 0) (1, 1) = (-1187019043 / 1000000000000) := rfl
@[simp] theorem lookup_previous_0_3 : previousPadding literalP (0, 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_current_0_3 : currentPadding literalP (0, 0) (1, 1) = (29649742669 / 250000000000) := rfl
@[simp] theorem lookup_descent_0_4 : literalDescent (0, 0) (2, 0) = (-10139801 / 10000000000) := rfl
@[simp] theorem lookup_previous_0_4 : previousPadding literalP (0, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_current_0_4 : currentPadding literalP (0, 0) (2, 0) = (-552360071 / 5000000000) := rfl
@[simp] theorem lookup_descent_0_5 : literalDescent (0, 0) (2, 1) = (266407237 / 500000000000) := rfl
@[simp] theorem lookup_previous_0_5 : previousPadding literalP (0, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_current_0_5 : currentPadding literalP (0, 0) (2, 1) = (19671739871 / 200000000000) := rfl
@[simp] theorem lookup_descent_0_6 : literalDescent (0, 0) (3, 0) = (55285251 / 10000000000) := rfl
@[simp] theorem lookup_previous_0_6 : previousPadding literalP (0, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_current_0_6 : currentPadding literalP (0, 0) (3, 0) = (202901393 / 5000000000) := rfl
@[simp] theorem lookup_descent_0_7 : literalDescent (0, 0) (3, 1) = (451277541 / 4000000000000) := rfl
@[simp] theorem lookup_previous_0_7 : previousPadding literalP (0, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_current_0_7 : currentPadding literalP (0, 0) (3, 1) = (12012619 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_8 : literalDescent (0, 0) (4, 0) = (-38991227 / 20000000000) := rfl
@[simp] theorem lookup_previous_0_8 : previousPadding literalP (0, 0) (4, 0) = 0 := rfl
@[simp] theorem lookup_current_0_8 : currentPadding literalP (0, 0) (4, 0) = (3747053 / 2500000000) := rfl
@[simp] theorem lookup_descent_0_9 : literalDescent (0, 0) (4, 1) = (-5573931437 / 4000000000000) := rfl
@[simp] theorem lookup_previous_0_9 : previousPadding literalP (0, 0) (4, 1) = 0 := rfl
@[simp] theorem lookup_current_0_9 : currentPadding literalP (0, 0) (4, 1) = (-71263753 / 5000000000) := rfl
@[simp] theorem lookup_descent_0_10 : literalDescent (0, 0) (5, 0) = (8842821 / 10000000000) := rfl
@[simp] theorem lookup_previous_0_10 : previousPadding literalP (0, 0) (5, 0) = 0 := rfl
@[simp] theorem lookup_current_0_10 : currentPadding literalP (0, 0) (5, 0) = (-1486621 / 2000000000) := rfl
@[simp] theorem lookup_descent_0_11 : literalDescent (0, 0) (5, 1) = (347422703 / 200000000000) := rfl
@[simp] theorem lookup_previous_0_11 : previousPadding literalP (0, 0) (5, 1) = 0 := rfl
@[simp] theorem lookup_current_0_11 : currentPadding literalP (0, 0) (5, 1) = (27842473 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_12 : literalDescent (0, 0) (6, 0) = (-5175427 / 2500000000) := rfl
@[simp] theorem lookup_previous_0_12 : previousPadding literalP (0, 0) (6, 0) = 0 := rfl
@[simp] theorem lookup_current_0_12 : currentPadding literalP (0, 0) (6, 0) = (22248179 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_13 : literalDescent (0, 0) (6, 1) = (-331230321 / 2000000000000) := rfl
@[simp] theorem lookup_previous_0_13 : previousPadding literalP (0, 0) (6, 1) = 0 := rfl
@[simp] theorem lookup_current_0_13 : currentPadding literalP (0, 0) (6, 1) = (-4226673 / 2000000000) := rfl
@[simp] theorem lookup_descent_0_14 : literalDescent (0, 0) (7, 0) = (-23479143 / 20000000000) := rfl
@[simp] theorem lookup_previous_0_14 : previousPadding literalP (0, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_current_0_14 : currentPadding literalP (0, 0) (7, 0) = (1705631 / 2500000000) := rfl
@[simp] theorem lookup_descent_0_15 : literalDescent (0, 0) (7, 1) = (16616327 / 62500000000) := rfl
@[simp] theorem lookup_previous_0_15 : previousPadding literalP (0, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_current_0_15 : currentPadding literalP (0, 0) (7, 1) = (3385001 / 1250000000) := rfl
@[simp] theorem lookup_descent_0_16 : literalDescent (0, 0) (8, 0) = (233761 / 400000000) := rfl
@[simp] theorem lookup_previous_0_16 : previousPadding literalP (0, 0) (8, 0) = 0 := rfl
@[simp] theorem lookup_current_0_16 : currentPadding literalP (0, 0) (8, 0) = (-17742321 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_17 : literalDescent (0, 0) (8, 1) = (-418016227 / 1000000000000) := rfl
@[simp] theorem lookup_previous_0_17 : previousPadding literalP (0, 0) (8, 1) = 0 := rfl
@[simp] theorem lookup_current_0_17 : currentPadding literalP (0, 0) (8, 1) = (3634641 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_18 : literalDescent (0, 0) (9, 0) = (1887537 / 2000000000) := rfl
@[simp] theorem lookup_previous_0_18 : previousPadding literalP (0, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_current_0_18 : currentPadding literalP (0, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_0_19 : literalDescent (0, 0) (9, 1) = (-191574533 / 2000000000000) := rfl
@[simp] theorem lookup_previous_0_19 : previousPadding literalP (0, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_current_0_19 : currentPadding literalP (0, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_1_0 : literalDescent (0, 1) (0, 0) = (12226239 / 20000000000) := rfl
@[simp] theorem lookup_previous_1_0 : previousPadding literalP (0, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_1_0 : currentPadding literalP (0, 1) (0, 0) = (1627883 / 312500000) := rfl
@[simp] theorem lookup_descent_1_1 : literalDescent (0, 1) (0, 1) = (296759187 / 400000000000) := rfl
@[simp] theorem lookup_previous_1_1 : previousPadding literalP (0, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_1_1 : currentPadding literalP (0, 1) (0, 1) = (52938274213 / 400000000000) := rfl
@[simp] theorem lookup_descent_1_2 : literalDescent (0, 1) (1, 0) = (-1642753713 / 800000000000) := rfl
@[simp] theorem lookup_previous_1_2 : previousPadding literalP (0, 1) (1, 0) = 0 := rfl
@[simp] theorem lookup_current_1_2 : currentPadding literalP (0, 1) (1, 0) = (-51599758407 / 800000000000) := rfl
@[simp] theorem lookup_descent_1_3 : literalDescent (0, 1) (1, 1) = (-568854641 / 800000000000) := rfl
@[simp] theorem lookup_previous_1_3 : previousPadding literalP (0, 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_current_1_3 : currentPadding literalP (0, 1) (1, 1) = (-34613123 / 5000000000) := rfl
@[simp] theorem lookup_descent_1_4 : literalDescent (0, 1) (2, 0) = (-827719 / 1000000000) := rfl
@[simp] theorem lookup_previous_1_4 : previousPadding literalP (0, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_current_1_4 : currentPadding literalP (0, 1) (2, 0) = (40860889 / 2500000000) := rfl
@[simp] theorem lookup_descent_1_5 : literalDescent (0, 1) (2, 1) = (-164200599 / 500000000000) := rfl
@[simp] theorem lookup_previous_1_5 : previousPadding literalP (0, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_current_1_5 : currentPadding literalP (0, 1) (2, 1) = (-1111576001 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_6 : literalDescent (0, 1) (3, 0) = (3421284473 / 800000000000) := rfl
@[simp] theorem lookup_previous_1_6 : previousPadding literalP (0, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_current_1_6 : currentPadding literalP (0, 1) (3, 0) = (33465772407 / 800000000000) := rfl
@[simp] theorem lookup_descent_1_7 : literalDescent (0, 1) (3, 1) = (146583399 / 400000000000) := rfl
@[simp] theorem lookup_previous_1_7 : previousPadding literalP (0, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_current_1_7 : currentPadding literalP (0, 1) (3, 1) = (1895001 / 2000000000) := rfl
@[simp] theorem lookup_descent_1_8 : literalDescent (0, 1) (4, 0) = (-6960307 / 4000000000) := rfl
@[simp] theorem lookup_previous_1_8 : previousPadding literalP (0, 1) (4, 0) = 0 := rfl
@[simp] theorem lookup_current_1_8 : currentPadding literalP (0, 1) (4, 0) = (6446739 / 5000000000) := rfl
@[simp] theorem lookup_descent_1_9 : literalDescent (0, 1) (4, 1) = (-4463921009 / 4000000000000) := rfl
@[simp] theorem lookup_previous_1_9 : previousPadding literalP (0, 1) (4, 1) = 0 := rfl
@[simp] theorem lookup_current_1_9 : currentPadding literalP (0, 1) (4, 1) = (-72651833 / 5000000000) := rfl
@[simp] theorem lookup_descent_1_10 : literalDescent (0, 1) (5, 0) = (3403207 / 4000000000) := rfl
@[simp] theorem lookup_previous_1_10 : previousPadding literalP (0, 1) (5, 0) = 0 := rfl
@[simp] theorem lookup_current_1_10 : currentPadding literalP (0, 1) (5, 0) = (-1774559 / 2500000000) := rfl
@[simp] theorem lookup_descent_1_11 : literalDescent (0, 1) (5, 1) = (1928852689 / 2000000000000) := rfl
@[simp] theorem lookup_previous_1_11 : previousPadding literalP (0, 1) (5, 1) = 0 := rfl
@[simp] theorem lookup_current_1_11 : currentPadding literalP (0, 1) (5, 1) = (17781659 / 5000000000) := rfl
@[simp] theorem lookup_descent_1_12 : literalDescent (0, 1) (6, 0) = (-1336127 / 20000000000) := rfl
@[simp] theorem lookup_previous_1_12 : previousPadding literalP (0, 1) (6, 0) = 0 := rfl
@[simp] theorem lookup_current_1_12 : currentPadding literalP (0, 1) (6, 0) = (1107293 / 5000000000) := rfl
@[simp] theorem lookup_descent_1_13 : literalDescent (0, 1) (6, 1) = (659606701 / 4000000000000) := rfl
@[simp] theorem lookup_previous_1_13 : previousPadding literalP (0, 1) (6, 1) = 0 := rfl
@[simp] theorem lookup_current_1_13 : currentPadding literalP (0, 1) (6, 1) = (-6111159 / 2500000000) := rfl
@[simp] theorem lookup_descent_1_14 : literalDescent (0, 1) (7, 0) = (-28992191 / 20000000000) := rfl
@[simp] theorem lookup_previous_1_14 : previousPadding literalP (0, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_current_1_14 : currentPadding literalP (0, 1) (7, 0) = (9579093 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_15 : literalDescent (0, 1) (7, 1) = (1368367297 / 4000000000000) := rfl
@[simp] theorem lookup_previous_1_15 : previousPadding literalP (0, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_current_1_15 : currentPadding literalP (0, 1) (7, 1) = (745663 / 2500000000) := rfl
@[simp] theorem lookup_descent_1_16 : literalDescent (0, 1) (8, 0) = (-272417 / 500000000) := rfl
@[simp] theorem lookup_previous_1_16 : previousPadding literalP (0, 1) (8, 0) = 0 := rfl
@[simp] theorem lookup_current_1_16 : currentPadding literalP (0, 1) (8, 0) = (-1612477 / 2500000000) := rfl
@[simp] theorem lookup_descent_1_17 : literalDescent (0, 1) (8, 1) = (-65692707 / 200000000000) := rfl
@[simp] theorem lookup_previous_1_17 : previousPadding literalP (0, 1) (8, 1) = 0 := rfl
@[simp] theorem lookup_current_1_17 : currentPadding literalP (0, 1) (8, 1) = (-4478129 / 2500000000) := rfl
@[simp] theorem lookup_descent_1_18 : literalDescent (0, 1) (9, 0) = (1887537 / 2000000000) := rfl
@[simp] theorem lookup_previous_1_18 : previousPadding literalP (0, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_current_1_18 : currentPadding literalP (0, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_1_19 : literalDescent (0, 1) (9, 1) = (-38345209 / 400000000000) := rfl
@[simp] theorem lookup_previous_1_19 : previousPadding literalP (0, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_current_1_19 : currentPadding literalP (0, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_2_0 : literalDescent (1, 0) (0, 0) = (-7429389 / 2000000000) := rfl
@[simp] theorem lookup_previous_2_0 : previousPadding literalP (1, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_2_0 : currentPadding literalP (1, 0) (0, 0) = (-628391041 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_1 : literalDescent (1, 0) (0, 1) = (-1642753713 / 800000000000) := rfl
@[simp] theorem lookup_previous_2_1 : previousPadding literalP (1, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_2_1 : currentPadding literalP (1, 0) (0, 1) = (-51599758407 / 800000000000) := rfl
@[simp] theorem lookup_descent_2_2 : literalDescent (1, 0) (1, 0) = (27209513 / 2500000000) := rfl
@[simp] theorem lookup_previous_2_2 : previousPadding literalP (1, 0) (1, 0) = (655630989 / 5000000000) := rfl
@[simp] theorem lookup_current_2_2 : currentPadding literalP (1, 0) (1, 0) = (1202424063 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_3 : literalDescent (1, 0) (1, 1) = (2647678373 / 800000000000) := rfl
@[simp] theorem lookup_previous_2_3 : previousPadding literalP (1, 0) (1, 1) = (1627883 / 312500000) := rfl
@[simp] theorem lookup_current_2_3 : currentPadding literalP (1, 0) (1, 1) = (-677042653809 / 4000000000000) := rfl
@[simp] theorem lookup_descent_2_4 : literalDescent (1, 0) (2, 0) = (-2992673 / 2000000000) := rfl
@[simp] theorem lookup_previous_2_4 : previousPadding literalP (1, 0) (2, 0) = (-628391041 / 10000000000) := rfl
@[simp] theorem lookup_current_2_4 : currentPadding literalP (1, 0) (2, 0) = (-20134549 / 5000000000) := rfl
@[simp] theorem lookup_descent_2_5 : literalDescent (1, 0) (2, 1) = (-1370686603 / 1000000000000) := rfl
@[simp] theorem lookup_previous_2_5 : previousPadding literalP (1, 0) (2, 1) = (29649742669 / 250000000000) := rfl
@[simp] theorem lookup_current_2_5 : currentPadding literalP (1, 0) (2, 1) = (-330919747 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_6 : literalDescent (1, 0) (3, 0) = (-312988647 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_6 : previousPadding literalP (1, 0) (3, 0) = (-552360071 / 5000000000) := rfl
@[simp] theorem lookup_current_2_6 : currentPadding literalP (1, 0) (3, 0) = (-948225799 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_7 : literalDescent (1, 0) (3, 1) = (-19628143 / 250000000000) := rfl
@[simp] theorem lookup_previous_2_7 : previousPadding literalP (1, 0) (3, 1) = (19671739871 / 200000000000) := rfl
@[simp] theorem lookup_current_2_7 : currentPadding literalP (1, 0) (3, 1) = (41121351277 / 1000000000000) := rfl
@[simp] theorem lookup_descent_2_8 : literalDescent (1, 0) (4, 0) = (13076461 / 1250000000) := rfl
@[simp] theorem lookup_previous_2_8 : previousPadding literalP (1, 0) (4, 0) = (202901393 / 5000000000) := rfl
@[simp] theorem lookup_current_2_8 : currentPadding literalP (1, 0) (4, 0) = (74397693 / 2000000000) := rfl
@[simp] theorem lookup_descent_2_9 : literalDescent (1, 0) (4, 1) = (71761909 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_9 : previousPadding literalP (1, 0) (4, 1) = (12012619 / 10000000000) := rfl
@[simp] theorem lookup_current_2_9 : currentPadding literalP (1, 0) (4, 1) = (11732253 / 2500000000) := rfl
@[simp] theorem lookup_descent_2_10 : literalDescent (1, 0) (5, 0) = (-52679853 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_10 : previousPadding literalP (1, 0) (5, 0) = (3747053 / 2500000000) := rfl
@[simp] theorem lookup_current_2_10 : currentPadding literalP (1, 0) (5, 0) = (10332043 / 2500000000) := rfl
@[simp] theorem lookup_descent_2_11 : literalDescent (1, 0) (5, 1) = (-89791801 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_11 : previousPadding literalP (1, 0) (5, 1) = (-71263753 / 5000000000) := rfl
@[simp] theorem lookup_current_2_11 : currentPadding literalP (1, 0) (5, 1) = (-168428939 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_12 : literalDescent (1, 0) (6, 0) = (13989309 / 5000000000) := rfl
@[simp] theorem lookup_previous_2_12 : previousPadding literalP (1, 0) (6, 0) = (-1486621 / 2000000000) := rfl
@[simp] theorem lookup_current_2_12 : currentPadding literalP (1, 0) (6, 0) = (-300759 / 125000000) := rfl
@[simp] theorem lookup_descent_2_13 : literalDescent (1, 0) (6, 1) = (22425099 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_13 : previousPadding literalP (1, 0) (6, 1) = (27842473 / 10000000000) := rfl
@[simp] theorem lookup_current_2_13 : currentPadding literalP (1, 0) (6, 1) = (27980893 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_14 : literalDescent (1, 0) (7, 0) = (-2741899 / 5000000000) := rfl
@[simp] theorem lookup_previous_2_14 : previousPadding literalP (1, 0) (7, 0) = (22248179 / 10000000000) := rfl
@[simp] theorem lookup_current_2_14 : currentPadding literalP (1, 0) (7, 0) = (13866017 / 5000000000) := rfl
@[simp] theorem lookup_descent_2_15 : literalDescent (1, 0) (7, 1) = (-823173 / 500000000) := rfl
@[simp] theorem lookup_previous_2_15 : previousPadding literalP (1, 0) (7, 1) = (-4226673 / 2000000000) := rfl
@[simp] theorem lookup_current_2_15 : currentPadding literalP (1, 0) (7, 1) = (-16020851 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_16 : literalDescent (1, 0) (8, 0) = (16742321 / 10000000000) := rfl
@[simp] theorem lookup_previous_2_16 : previousPadding literalP (1, 0) (8, 0) = (1705631 / 2500000000) := rfl
@[simp] theorem lookup_current_2_16 : currentPadding literalP (1, 0) (8, 0) = (-631519 / 2500000000) := rfl
@[simp] theorem lookup_descent_2_17 : literalDescent (1, 0) (8, 1) = (1995537 / 1000000000) := rfl
@[simp] theorem lookup_previous_2_17 : previousPadding literalP (1, 0) (8, 1) = (3385001 / 1250000000) := rfl
@[simp] theorem lookup_current_2_17 : currentPadding literalP (1, 0) (8, 1) = (7259151 / 5000000000) := rfl
@[simp] theorem lookup_descent_2_18 : literalDescent (1, 0) (9, 0) = (-17742321 / 10000000000) := rfl
@[simp] theorem lookup_previous_2_18 : previousPadding literalP (1, 0) (9, 0) = (-17742321 / 10000000000) := rfl
@[simp] theorem lookup_current_2_18 : currentPadding literalP (1, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_2_19 : literalDescent (1, 0) (9, 1) = (-93977 / 250000000) := rfl
@[simp] theorem lookup_previous_2_19 : previousPadding literalP (1, 0) (9, 1) = (3634641 / 10000000000) := rfl
@[simp] theorem lookup_current_2_19 : currentPadding literalP (1, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_3_0 : literalDescent (1, 1) (0, 0) = (-1187019043 / 1000000000000) := rfl
@[simp] theorem lookup_previous_3_0 : previousPadding literalP (1, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_3_0 : currentPadding literalP (1, 1) (0, 0) = (29649742669 / 250000000000) := rfl
@[simp] theorem lookup_descent_3_1 : literalDescent (1, 1) (0, 1) = (-568854641 / 800000000000) := rfl
@[simp] theorem lookup_previous_3_1 : previousPadding literalP (1, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_3_1 : currentPadding literalP (1, 1) (0, 1) = (-34613123 / 5000000000) := rfl
@[simp] theorem lookup_descent_3_2 : literalDescent (1, 1) (1, 0) = (2647678373 / 800000000000) := rfl
@[simp] theorem lookup_previous_3_2 : previousPadding literalP (1, 1) (1, 0) = (1627883 / 312500000) := rfl
@[simp] theorem lookup_current_3_2 : currentPadding literalP (1, 1) (1, 0) = (-677042653809 / 4000000000000) := rfl
@[simp] theorem lookup_descent_3_3 : literalDescent (1, 1) (1, 1) = (6164870491 / 4000000000000) := rfl
@[simp] theorem lookup_previous_3_3 : previousPadding literalP (1, 1) (1, 1) = (52938274213 / 400000000000) := rfl
@[simp] theorem lookup_current_3_3 : currentPadding literalP (1, 1) (1, 1) = (10387417667 / 800000000000) := rfl
@[simp] theorem lookup_descent_3_4 : literalDescent (1, 1) (2, 0) = (-4418286253 / 4000000000000) := rfl
@[simp] theorem lookup_previous_3_4 : previousPadding literalP (1, 1) (2, 0) = (-51599758407 / 800000000000) := rfl
@[simp] theorem lookup_current_3_4 : currentPadding literalP (1, 1) (2, 0) = (32779869 / 625000000) := rfl
@[simp] theorem lookup_descent_3_5 : literalDescent (1, 1) (2, 1) = (-1852734763 / 4000000000000) := rfl
@[simp] theorem lookup_previous_3_5 : previousPadding literalP (1, 1) (2, 1) = (-34613123 / 5000000000) := rfl
@[simp] theorem lookup_current_3_5 : currentPadding literalP (1, 1) (2, 1) = (-30138373 / 10000000000) := rfl
@[simp] theorem lookup_descent_3_6 : literalDescent (1, 1) (3, 0) = (-22348539507 / 4000000000000) := rfl
@[simp] theorem lookup_previous_3_6 : previousPadding literalP (1, 1) (3, 0) = (40860889 / 2500000000) := rfl
@[simp] theorem lookup_current_3_6 : currentPadding literalP (1, 1) (3, 0) = (-48354603 / 2000000000) := rfl
@[simp] theorem lookup_descent_3_7 : literalDescent (1, 1) (3, 1) = (-2165093889 / 4000000000000) := rfl
@[simp] theorem lookup_previous_3_7 : previousPadding literalP (1, 1) (3, 1) = (-1111576001 / 10000000000) := rfl
@[simp] theorem lookup_current_3_7 : currentPadding literalP (1, 1) (3, 1) = (-38898883 / 10000000000) := rfl
@[simp] theorem lookup_descent_3_8 : literalDescent (1, 1) (4, 0) = (1057717183 / 200000000000) := rfl
@[simp] theorem lookup_previous_3_8 : previousPadding literalP (1, 1) (4, 0) = (33465772407 / 800000000000) := rfl
@[simp] theorem lookup_current_3_8 : currentPadding literalP (1, 1) (4, 0) = (18919260781 / 800000000000) := rfl
@[simp] theorem lookup_descent_3_9 : literalDescent (1, 1) (4, 1) = (2739104097 / 2000000000000) := rfl
@[simp] theorem lookup_previous_3_9 : previousPadding literalP (1, 1) (4, 1) = (1895001 / 2000000000) := rfl
@[simp] theorem lookup_current_3_9 : currentPadding literalP (1, 1) (4, 1) = (18789953 / 10000000000) := rfl
@[simp] theorem lookup_descent_3_10 : literalDescent (1, 1) (5, 0) = (-643290559 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_10 : previousPadding literalP (1, 1) (5, 0) = (6446739 / 5000000000) := rfl
@[simp] theorem lookup_current_3_10 : currentPadding literalP (1, 1) (5, 0) = (190231 / 78125000) := rfl
@[simp] theorem lookup_descent_3_11 : literalDescent (1, 1) (5, 1) = (-7471768719 / 4000000000000) := rfl
@[simp] theorem lookup_previous_3_11 : previousPadding literalP (1, 1) (5, 1) = (-72651833 / 5000000000) := rfl
@[simp] theorem lookup_current_3_11 : currentPadding literalP (1, 1) (5, 1) = (-9594713 / 2500000000) := rfl
@[simp] theorem lookup_descent_3_12 : literalDescent (1, 1) (6, 0) = (2715327169 / 4000000000000) := rfl
@[simp] theorem lookup_previous_3_12 : previousPadding literalP (1, 1) (6, 0) = (-1774559 / 2500000000) := rfl
@[simp] theorem lookup_current_3_12 : currentPadding literalP (1, 1) (6, 0) = (-1841481 / 500000000) := rfl
@[simp] theorem lookup_descent_3_13 : literalDescent (1, 1) (6, 1) = (141054337 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_13 : previousPadding literalP (1, 1) (6, 1) = (17781659 / 5000000000) := rfl
@[simp] theorem lookup_current_3_13 : currentPadding literalP (1, 1) (6, 1) = (34141273 / 10000000000) := rfl
@[simp] theorem lookup_descent_3_14 : literalDescent (1, 1) (7, 0) = (162672047 / 250000000000) := rfl
@[simp] theorem lookup_previous_3_14 : previousPadding literalP (1, 1) (7, 0) = (1107293 / 5000000000) := rfl
@[simp] theorem lookup_current_3_14 : currentPadding literalP (1, 1) (7, 0) = (156171 / 2500000000) := rfl
@[simp] theorem lookup_descent_3_15 : literalDescent (1, 1) (7, 1) = (-1397694013 / 4000000000000) := rfl
@[simp] theorem lookup_previous_3_15 : previousPadding literalP (1, 1) (7, 1) = (-6111159 / 2500000000) := rfl
@[simp] theorem lookup_current_3_15 : currentPadding literalP (1, 1) (7, 1) = (-2978719 / 5000000000) := rfl
@[simp] theorem lookup_descent_3_16 : literalDescent (1, 1) (8, 0) = (1652724079 / 2000000000000) := rfl
@[simp] theorem lookup_previous_3_16 : previousPadding literalP (1, 1) (8, 0) = (9579093 / 10000000000) := rfl
@[simp] theorem lookup_current_3_16 : currentPadding literalP (1, 1) (8, 0) = (-723353 / 10000000000) := rfl
@[simp] theorem lookup_descent_3_17 : literalDescent (1, 1) (8, 1) = (1041684971 / 1000000000000) := rfl
@[simp] theorem lookup_previous_3_17 : previousPadding literalP (1, 1) (8, 1) = (745663 / 2500000000) := rfl
@[simp] theorem lookup_current_3_17 : currentPadding literalP (1, 1) (8, 1) = (-174103 / 10000000000) := rfl
@[simp] theorem lookup_descent_3_18 : literalDescent (1, 1) (9, 0) = (-15887593 / 10000000000) := rfl
@[simp] theorem lookup_previous_3_18 : previousPadding literalP (1, 1) (9, 0) = (-1612477 / 2500000000) := rfl
@[simp] theorem lookup_current_3_18 : currentPadding literalP (1, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_3_19 : literalDescent (1, 1) (9, 1) = (-301672169 / 1000000000000) := rfl
@[simp] theorem lookup_previous_3_19 : previousPadding literalP (1, 1) (9, 1) = (-4478129 / 2500000000) := rfl
@[simp] theorem lookup_current_3_19 : currentPadding literalP (1, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_4_0 : literalDescent (2, 0) (0, 0) = (-10139801 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_0 : previousPadding literalP (2, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_4_0 : currentPadding literalP (2, 0) (0, 0) = (-552360071 / 5000000000) := rfl
@[simp] theorem lookup_descent_4_1 : literalDescent (2, 0) (0, 1) = (-827719 / 1000000000) := rfl
@[simp] theorem lookup_previous_4_1 : previousPadding literalP (2, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_4_1 : currentPadding literalP (2, 0) (0, 1) = (40860889 / 2500000000) := rfl
@[simp] theorem lookup_descent_4_2 : literalDescent (2, 0) (1, 0) = (-2992673 / 2000000000) := rfl
@[simp] theorem lookup_previous_4_2 : previousPadding literalP (2, 0) (1, 0) = (-628391041 / 10000000000) := rfl
@[simp] theorem lookup_current_4_2 : currentPadding literalP (2, 0) (1, 0) = (-20134549 / 5000000000) := rfl
@[simp] theorem lookup_descent_4_3 : literalDescent (2, 0) (1, 1) = (-4418286253 / 4000000000000) := rfl
@[simp] theorem lookup_previous_4_3 : previousPadding literalP (2, 0) (1, 1) = (-51599758407 / 800000000000) := rfl
@[simp] theorem lookup_current_4_3 : currentPadding literalP (2, 0) (1, 1) = (32779869 / 625000000) := rfl
@[simp] theorem lookup_descent_4_4 : literalDescent (2, 0) (2, 0) = (13098373 / 1000000000) := rfl
@[simp] theorem lookup_previous_4_4 : previousPadding literalP (2, 0) (2, 0) = (1202424063 / 10000000000) := rfl
@[simp] theorem lookup_current_4_4 : currentPadding literalP (2, 0) (2, 0) = (2154843063 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_5 : literalDescent (2, 0) (2, 1) = (6565610543 / 2000000000000) := rfl
@[simp] theorem lookup_previous_4_5 : previousPadding literalP (2, 0) (2, 1) = (-677042653809 / 4000000000000) := rfl
@[simp] theorem lookup_current_4_5 : currentPadding literalP (2, 0) (2, 1) = (-51362571259 / 800000000000) := rfl
@[simp] theorem lookup_descent_4_6 : literalDescent (2, 0) (3, 0) = (-17246117 / 2500000000) := rfl
@[simp] theorem lookup_previous_4_6 : previousPadding literalP (2, 0) (3, 0) = (-20134549 / 5000000000) := rfl
@[simp] theorem lookup_current_4_6 : currentPadding literalP (2, 0) (3, 0) = (-102597199 / 2000000000) := rfl
@[simp] theorem lookup_descent_4_7 : literalDescent (2, 0) (3, 1) = (-8112878741 / 4000000000000) := rfl
@[simp] theorem lookup_previous_4_7 : previousPadding literalP (2, 0) (3, 1) = (-330919747 / 10000000000) := rfl
@[simp] theorem lookup_current_4_7 : currentPadding literalP (2, 0) (3, 1) = (-93233353 / 2500000000) := rfl
@[simp] theorem lookup_descent_4_8 : literalDescent (2, 0) (4, 0) = (-25574771 / 2000000000) := rfl
@[simp] theorem lookup_previous_4_8 : previousPadding literalP (2, 0) (4, 0) = (-948225799 / 10000000000) := rfl
@[simp] theorem lookup_current_4_8 : currentPadding literalP (2, 0) (4, 0) = (-102543993 / 1250000000) := rfl
@[simp] theorem lookup_descent_4_9 : literalDescent (2, 0) (4, 1) = (1933547277 / 1000000000000) := rfl
@[simp] theorem lookup_previous_4_9 : previousPadding literalP (2, 0) (4, 1) = (41121351277 / 1000000000000) := rfl
@[simp] theorem lookup_current_4_9 : currentPadding literalP (2, 0) (4, 1) = (9796951 / 250000000) := rfl
@[simp] theorem lookup_descent_4_10 : literalDescent (2, 0) (5, 0) = (16593809 / 2000000000) := rfl
@[simp] theorem lookup_previous_4_10 : previousPadding literalP (2, 0) (5, 0) = (74397693 / 2000000000) := rfl
@[simp] theorem lookup_current_4_10 : currentPadding literalP (2, 0) (5, 0) = (14450971 / 500000000) := rfl
@[simp] theorem lookup_descent_4_11 : literalDescent (2, 0) (5, 1) = (7471657 / 5000000000) := rfl
@[simp] theorem lookup_previous_4_11 : previousPadding literalP (2, 0) (5, 1) = (11732253 / 2500000000) := rfl
@[simp] theorem lookup_current_4_11 : currentPadding literalP (2, 0) (5, 1) = (15992849 / 5000000000) := rfl
@[simp] theorem lookup_descent_4_12 : literalDescent (2, 0) (6, 0) = (-27189693 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_12 : previousPadding literalP (2, 0) (6, 0) = (10332043 / 2500000000) := rfl
@[simp] theorem lookup_current_4_12 : currentPadding literalP (2, 0) (6, 0) = (13703573 / 2000000000) := rfl
@[simp] theorem lookup_descent_4_13 : literalDescent (2, 0) (6, 1) = (-10107251 / 2500000000) := rfl
@[simp] theorem lookup_previous_4_13 : previousPadding literalP (2, 0) (6, 1) = (-168428939 / 10000000000) := rfl
@[simp] theorem lookup_current_4_13 : currentPadding literalP (2, 0) (6, 1) = (-25599987 / 2000000000) := rfl
@[simp] theorem lookup_descent_4_14 : literalDescent (2, 0) (7, 0) = (14868251 / 2500000000) := rfl
@[simp] theorem lookup_previous_4_14 : previousPadding literalP (2, 0) (7, 0) = (-300759 / 125000000) := rfl
@[simp] theorem lookup_current_4_14 : currentPadding literalP (2, 0) (7, 0) = (-20883431 / 2500000000) := rfl
@[simp] theorem lookup_descent_4_15 : literalDescent (2, 0) (7, 1) = (2593673 / 1250000000) := rfl
@[simp] theorem lookup_previous_4_15 : previousPadding literalP (2, 0) (7, 1) = (27980893 / 10000000000) := rfl
@[simp] theorem lookup_current_4_15 : currentPadding literalP (2, 0) (7, 1) = (7231509 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_16 : literalDescent (2, 0) (8, 0) = (-21748521 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_16 : previousPadding literalP (2, 0) (8, 0) = (13866017 / 5000000000) := rfl
@[simp] theorem lookup_current_4_16 : currentPadding literalP (2, 0) (8, 0) = (9896111 / 2000000000) := rfl
@[simp] theorem lookup_descent_4_17 : literalDescent (2, 0) (8, 1) = (-22340419 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_17 : previousPadding literalP (2, 0) (8, 1) = (-16020851 / 10000000000) := rfl
@[simp] theorem lookup_current_4_17 : currentPadding literalP (2, 0) (8, 1) = (394973 / 625000000) := rfl
@[simp] theorem lookup_descent_4_18 : literalDescent (2, 0) (9, 0) = (-631519 / 2500000000) := rfl
@[simp] theorem lookup_previous_4_18 : previousPadding literalP (2, 0) (9, 0) = (-631519 / 2500000000) := rfl
@[simp] theorem lookup_current_4_18 : currentPadding literalP (2, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_4_19 : literalDescent (2, 0) (9, 1) = (7259151 / 5000000000) := rfl
@[simp] theorem lookup_previous_4_19 : previousPadding literalP (2, 0) (9, 1) = (7259151 / 5000000000) := rfl
@[simp] theorem lookup_current_4_19 : currentPadding literalP (2, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_5_0 : literalDescent (2, 1) (0, 0) = (266407237 / 500000000000) := rfl
@[simp] theorem lookup_previous_5_0 : previousPadding literalP (2, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_5_0 : currentPadding literalP (2, 1) (0, 0) = (19671739871 / 200000000000) := rfl
@[simp] theorem lookup_descent_5_1 : literalDescent (2, 1) (0, 1) = (-164200599 / 500000000000) := rfl
@[simp] theorem lookup_previous_5_1 : previousPadding literalP (2, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_5_1 : currentPadding literalP (2, 1) (0, 1) = (-1111576001 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_2 : literalDescent (2, 1) (1, 0) = (-1370686603 / 1000000000000) := rfl
@[simp] theorem lookup_previous_5_2 : previousPadding literalP (2, 1) (1, 0) = (29649742669 / 250000000000) := rfl
@[simp] theorem lookup_current_5_2 : currentPadding literalP (2, 1) (1, 0) = (-330919747 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_3 : literalDescent (2, 1) (1, 1) = (-1852734763 / 4000000000000) := rfl
@[simp] theorem lookup_previous_5_3 : previousPadding literalP (2, 1) (1, 1) = (-34613123 / 5000000000) := rfl
@[simp] theorem lookup_current_5_3 : currentPadding literalP (2, 1) (1, 1) = (-30138373 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_4 : literalDescent (2, 1) (2, 0) = (6565610543 / 2000000000000) := rfl
@[simp] theorem lookup_previous_5_4 : previousPadding literalP (2, 1) (2, 0) = (-677042653809 / 4000000000000) := rfl
@[simp] theorem lookup_current_5_4 : currentPadding literalP (2, 1) (2, 0) = (-51362571259 / 800000000000) := rfl
@[simp] theorem lookup_descent_5_5 : literalDescent (2, 1) (2, 1) = (1466152469 / 800000000000) := rfl
@[simp] theorem lookup_previous_5_5 : previousPadding literalP (2, 1) (2, 1) = (10387417667 / 800000000000) := rfl
@[simp] theorem lookup_current_5_5 : currentPadding literalP (2, 1) (2, 1) = (238983692003 / 2000000000000) := rfl
@[simp] theorem lookup_descent_5_6 : literalDescent (2, 1) (3, 0) = (-19389617 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_6 : previousPadding literalP (2, 1) (3, 0) = (32779869 / 625000000) := rfl
@[simp] theorem lookup_current_5_6 : currentPadding literalP (2, 1) (3, 0) = (541539 / 2500000000) := rfl
@[simp] theorem lookup_descent_5_7 : literalDescent (2, 1) (3, 1) = (-282242119 / 400000000000) := rfl
@[simp] theorem lookup_previous_5_7 : previousPadding literalP (2, 1) (3, 1) = (-30138373 / 10000000000) := rfl
@[simp] theorem lookup_current_5_7 : currentPadding literalP (2, 1) (3, 1) = (-85377977 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_8 : literalDescent (2, 1) (4, 0) = (-23363691 / 5000000000) := rfl
@[simp] theorem lookup_previous_5_8 : previousPadding literalP (2, 1) (4, 0) = (-48354603 / 2000000000) := rfl
@[simp] theorem lookup_current_5_8 : currentPadding literalP (2, 1) (4, 0) = (-195045633 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_9 : literalDescent (2, 1) (4, 1) = (-5309887 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_9 : previousPadding literalP (2, 1) (4, 1) = (-38898883 / 10000000000) := rfl
@[simp] theorem lookup_current_5_9 : currentPadding literalP (2, 1) (4, 1) = (-8397249 / 2500000000) := rfl
@[simp] theorem lookup_descent_5_10 : literalDescent (2, 1) (5, 0) = (1967751863 / 400000000000) := rfl
@[simp] theorem lookup_previous_5_10 : previousPadding literalP (2, 1) (5, 0) = (18919260781 / 800000000000) := rfl
@[simp] theorem lookup_current_5_10 : currentPadding literalP (2, 1) (5, 0) = (2996751411 / 160000000000) := rfl
@[simp] theorem lookup_descent_5_11 : literalDescent (2, 1) (5, 1) = (7473609 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_11 : previousPadding literalP (2, 1) (5, 1) = (18789953 / 10000000000) := rfl
@[simp] theorem lookup_current_5_11 : currentPadding literalP (2, 1) (5, 1) = (1414543 / 1250000000) := rfl
@[simp] theorem lookup_descent_5_12 : literalDescent (2, 1) (6, 0) = (-406347 / 2000000000) := rfl
@[simp] theorem lookup_previous_5_12 : previousPadding literalP (2, 1) (6, 0) = (190231 / 78125000) := rfl
@[simp] theorem lookup_current_5_12 : currentPadding literalP (2, 1) (6, 0) = (26381303 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_13 : literalDescent (2, 1) (6, 1) = (-2554809 / 2000000000) := rfl
@[simp] theorem lookup_previous_5_13 : previousPadding literalP (2, 1) (6, 1) = (-9594713 / 2500000000) := rfl
@[simp] theorem lookup_current_5_13 : currentPadding literalP (2, 1) (6, 1) = (-25604807 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_14 : literalDescent (2, 1) (7, 0) = (-251163 / 625000000) := rfl
@[simp] theorem lookup_previous_5_14 : previousPadding literalP (2, 1) (7, 0) = (-1841481 / 500000000) := rfl
@[simp] theorem lookup_current_5_14 : currentPadding literalP (2, 1) (7, 0) = (-8202753 / 2500000000) := rfl
@[simp] theorem lookup_descent_5_15 : literalDescent (2, 1) (7, 1) = (8212547 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_15 : previousPadding literalP (2, 1) (7, 1) = (34141273 / 10000000000) := rfl
@[simp] theorem lookup_current_5_15 : currentPadding literalP (2, 1) (7, 1) = (12964363 / 5000000000) := rfl
@[simp] theorem lookup_descent_5_16 : literalDescent (2, 1) (8, 0) = (-752433 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_16 : previousPadding literalP (2, 1) (8, 0) = (156171 / 2500000000) := rfl
@[simp] theorem lookup_current_5_16 : currentPadding literalP (2, 1) (8, 0) = (1377117 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_17 : literalDescent (2, 1) (8, 1) = (-1253 / 16000000) := rfl
@[simp] theorem lookup_previous_5_17 : previousPadding literalP (2, 1) (8, 1) = (-2978719 / 5000000000) := rfl
@[simp] theorem lookup_current_5_17 : currentPadding literalP (2, 1) (8, 1) = (-5174313 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_18 : literalDescent (2, 1) (9, 0) = (-723353 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_18 : previousPadding literalP (2, 1) (9, 0) = (-723353 / 10000000000) := rfl
@[simp] theorem lookup_current_5_18 : currentPadding literalP (2, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_5_19 : literalDescent (2, 1) (9, 1) = (-174103 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_19 : previousPadding literalP (2, 1) (9, 1) = (-174103 / 10000000000) := rfl
@[simp] theorem lookup_current_5_19 : currentPadding literalP (2, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_6_0 : literalDescent (3, 0) (0, 0) = (55285251 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_0 : previousPadding literalP (3, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_6_0 : currentPadding literalP (3, 0) (0, 0) = (202901393 / 5000000000) := rfl
@[simp] theorem lookup_descent_6_1 : literalDescent (3, 0) (0, 1) = (3421284473 / 800000000000) := rfl
@[simp] theorem lookup_previous_6_1 : previousPadding literalP (3, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_6_1 : currentPadding literalP (3, 0) (0, 1) = (33465772407 / 800000000000) := rfl
@[simp] theorem lookup_descent_6_2 : literalDescent (3, 0) (1, 0) = (-312988647 / 20000000000) := rfl
@[simp] theorem lookup_previous_6_2 : previousPadding literalP (3, 0) (1, 0) = (-552360071 / 5000000000) := rfl
@[simp] theorem lookup_current_6_2 : currentPadding literalP (3, 0) (1, 0) = (-948225799 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_3 : literalDescent (3, 0) (1, 1) = (-22348539507 / 4000000000000) := rfl
@[simp] theorem lookup_previous_6_3 : previousPadding literalP (3, 0) (1, 1) = (40860889 / 2500000000) := rfl
@[simp] theorem lookup_current_6_3 : currentPadding literalP (3, 0) (1, 1) = (-48354603 / 2000000000) := rfl
@[simp] theorem lookup_descent_6_4 : literalDescent (3, 0) (2, 0) = (-17246117 / 2500000000) := rfl
@[simp] theorem lookup_previous_6_4 : previousPadding literalP (3, 0) (2, 0) = (-20134549 / 5000000000) := rfl
@[simp] theorem lookup_current_6_4 : currentPadding literalP (3, 0) (2, 0) = (-102597199 / 2000000000) := rfl
@[simp] theorem lookup_descent_6_5 : literalDescent (3, 0) (2, 1) = (-19389617 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_5 : previousPadding literalP (3, 0) (2, 1) = (32779869 / 625000000) := rfl
@[simp] theorem lookup_current_6_5 : currentPadding literalP (3, 0) (2, 1) = (541539 / 2500000000) := rfl
@[simp] theorem lookup_descent_6_6 : literalDescent (3, 0) (3, 0) = (81131249 / 2000000000) := rfl
@[simp] theorem lookup_previous_6_6 : previousPadding literalP (3, 0) (3, 0) = (2154843063 / 10000000000) := rfl
@[simp] theorem lookup_current_6_6 : currentPadding literalP (3, 0) (3, 0) = (382082687 / 2000000000) := rfl
@[simp] theorem lookup_descent_6_7 : literalDescent (3, 0) (3, 1) = (3883666981 / 800000000000) := rfl
@[simp] theorem lookup_previous_6_7 : previousPadding literalP (3, 0) (3, 1) = (-51362571259 / 800000000000) := rfl
@[simp] theorem lookup_current_6_7 : currentPadding literalP (3, 0) (3, 1) = (6174493 / 5000000000) := rfl
@[simp] theorem lookup_descent_6_8 : literalDescent (3, 0) (4, 0) = (-302975579 / 20000000000) := rfl
@[simp] theorem lookup_previous_6_8 : previousPadding literalP (3, 0) (4, 0) = (-102597199 / 2000000000) := rfl
@[simp] theorem lookup_current_6_8 : currentPadding literalP (3, 0) (4, 0) = (-221055757 / 5000000000) := rfl
@[simp] theorem lookup_descent_6_9 : literalDescent (3, 0) (4, 1) = (-33717611363 / 4000000000000) := rfl
@[simp] theorem lookup_previous_6_9 : previousPadding literalP (3, 0) (4, 1) = (-93233353 / 2500000000) := rfl
@[simp] theorem lookup_current_6_9 : currentPadding literalP (3, 0) (4, 1) = (-59582163 / 2000000000) := rfl
@[simp] theorem lookup_descent_6_10 : literalDescent (3, 0) (5, 0) = (-28814781 / 2000000000) := rfl
@[simp] theorem lookup_previous_6_10 : previousPadding literalP (3, 0) (5, 0) = (-102543993 / 1250000000) := rfl
@[simp] theorem lookup_current_6_10 : currentPadding literalP (3, 0) (5, 0) = (-676278039 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_11 : literalDescent (3, 0) (5, 1) = (37615679 / 5000000000) := rfl
@[simp] theorem lookup_previous_6_11 : previousPadding literalP (3, 0) (5, 1) = (9796951 / 250000000) := rfl
@[simp] theorem lookup_current_6_11 : currentPadding literalP (3, 0) (5, 1) = (158323341 / 5000000000) := rfl
@[simp] theorem lookup_descent_6_12 : literalDescent (3, 0) (6, 0) = (78085347 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_12 : previousPadding literalP (3, 0) (6, 0) = (14450971 / 500000000) := rfl
@[simp] theorem lookup_current_6_12 : currentPadding literalP (3, 0) (6, 0) = (210934073 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_13 : literalDescent (3, 0) (6, 1) = (454907 / 125000000) := rfl
@[simp] theorem lookup_previous_6_13 : previousPadding literalP (3, 0) (6, 1) = (15992849 / 5000000000) := rfl
@[simp] theorem lookup_current_6_13 : currentPadding literalP (3, 0) (6, 1) = (-2203431 / 5000000000) := rfl
@[simp] theorem lookup_descent_6_14 : literalDescent (3, 0) (7, 0) = (-7429137 / 2500000000) := rfl
@[simp] theorem lookup_previous_6_14 : previousPadding literalP (3, 0) (7, 0) = (13703573 / 2000000000) := rfl
@[simp] theorem lookup_current_6_14 : currentPadding literalP (3, 0) (7, 0) = (98234413 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_15 : literalDescent (3, 0) (7, 1) = (-8024187 / 2500000000) := rfl
@[simp] theorem lookup_previous_6_15 : previousPadding literalP (3, 0) (7, 1) = (-25599987 / 2000000000) := rfl
@[simp] theorem lookup_current_6_15 : currentPadding literalP (3, 0) (7, 1) = (-95903187 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_16 : literalDescent (3, 0) (8, 0) = (-9437591 / 2500000000) := rfl
@[simp] theorem lookup_previous_6_16 : previousPadding literalP (3, 0) (8, 0) = (-20883431 / 2500000000) := rfl
@[simp] theorem lookup_current_6_16 : currentPadding literalP (3, 0) (8, 0) = (-143073 / 31250000) := rfl
@[simp] theorem lookup_descent_6_17 : literalDescent (3, 0) (8, 1) = (-17603637 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_17 : previousPadding literalP (3, 0) (8, 1) = (7231509 / 10000000000) := rfl
@[simp] theorem lookup_current_6_17 : currentPadding literalP (3, 0) (8, 1) = (12417573 / 5000000000) := rfl
@[simp] theorem lookup_descent_6_18 : literalDescent (3, 0) (9, 0) = (9896111 / 2000000000) := rfl
@[simp] theorem lookup_previous_6_18 : previousPadding literalP (3, 0) (9, 0) = (9896111 / 2000000000) := rfl
@[simp] theorem lookup_current_6_18 : currentPadding literalP (3, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_6_19 : literalDescent (3, 0) (9, 1) = (394973 / 625000000) := rfl
@[simp] theorem lookup_previous_6_19 : previousPadding literalP (3, 0) (9, 1) = (394973 / 625000000) := rfl
@[simp] theorem lookup_current_6_19 : currentPadding literalP (3, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_7_0 : literalDescent (3, 1) (0, 0) = (451277541 / 4000000000000) := rfl
@[simp] theorem lookup_previous_7_0 : previousPadding literalP (3, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_7_0 : currentPadding literalP (3, 1) (0, 0) = (12012619 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_1 : literalDescent (3, 1) (0, 1) = (146583399 / 400000000000) := rfl
@[simp] theorem lookup_previous_7_1 : previousPadding literalP (3, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_7_1 : currentPadding literalP (3, 1) (0, 1) = (1895001 / 2000000000) := rfl
@[simp] theorem lookup_descent_7_2 : literalDescent (3, 1) (1, 0) = (-19628143 / 250000000000) := rfl
@[simp] theorem lookup_previous_7_2 : previousPadding literalP (3, 1) (1, 0) = (19671739871 / 200000000000) := rfl
@[simp] theorem lookup_current_7_2 : currentPadding literalP (3, 1) (1, 0) = (41121351277 / 1000000000000) := rfl
@[simp] theorem lookup_descent_7_3 : literalDescent (3, 1) (1, 1) = (-2165093889 / 4000000000000) := rfl
@[simp] theorem lookup_previous_7_3 : previousPadding literalP (3, 1) (1, 1) = (-1111576001 / 10000000000) := rfl
@[simp] theorem lookup_current_7_3 : currentPadding literalP (3, 1) (1, 1) = (-38898883 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_4 : literalDescent (3, 1) (2, 0) = (-8112878741 / 4000000000000) := rfl
@[simp] theorem lookup_previous_7_4 : previousPadding literalP (3, 1) (2, 0) = (-330919747 / 10000000000) := rfl
@[simp] theorem lookup_current_7_4 : currentPadding literalP (3, 1) (2, 0) = (-93233353 / 2500000000) := rfl
@[simp] theorem lookup_descent_7_5 : literalDescent (3, 1) (2, 1) = (-282242119 / 400000000000) := rfl
@[simp] theorem lookup_previous_7_5 : previousPadding literalP (3, 1) (2, 1) = (-30138373 / 10000000000) := rfl
@[simp] theorem lookup_current_7_5 : currentPadding literalP (3, 1) (2, 1) = (-85377977 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_6 : literalDescent (3, 1) (3, 0) = (3883666981 / 800000000000) := rfl
@[simp] theorem lookup_previous_7_6 : previousPadding literalP (3, 1) (3, 0) = (-51362571259 / 800000000000) := rfl
@[simp] theorem lookup_current_7_6 : currentPadding literalP (3, 1) (3, 0) = (6174493 / 5000000000) := rfl
@[simp] theorem lookup_descent_7_7 : literalDescent (3, 1) (3, 1) = (56886093 / 25000000000) := rfl
@[simp] theorem lookup_previous_7_7 : previousPadding literalP (3, 1) (3, 1) = (238983692003 / 2000000000000) := rfl
@[simp] theorem lookup_current_7_7 : currentPadding literalP (3, 1) (3, 1) = (74915844753 / 2000000000000) := rfl
@[simp] theorem lookup_descent_7_8 : literalDescent (3, 1) (4, 0) = (-65887223 / 20000000000) := rfl
@[simp] theorem lookup_previous_7_8 : previousPadding literalP (3, 1) (4, 0) = (541539 / 2500000000) := rfl
@[simp] theorem lookup_current_7_8 : currentPadding literalP (3, 1) (4, 0) = (-45503541 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_9 : literalDescent (3, 1) (4, 1) = (-5857435391 / 4000000000000) := rfl
@[simp] theorem lookup_previous_7_9 : previousPadding literalP (3, 1) (4, 1) = (-85377977 / 10000000000) := rfl
@[simp] theorem lookup_current_7_9 : currentPadding literalP (3, 1) (4, 1) = (-80004919 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_10 : literalDescent (3, 1) (5, 0) = (-16770321 / 5000000000) := rfl
@[simp] theorem lookup_previous_7_10 : previousPadding literalP (3, 1) (5, 0) = (-195045633 / 10000000000) := rfl
@[simp] theorem lookup_current_7_10 : currentPadding literalP (3, 1) (5, 0) = (-161504991 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_11 : literalDescent (3, 1) (5, 1) = (-2364193 / 5000000000) := rfl
@[simp] theorem lookup_previous_7_11 : previousPadding literalP (3, 1) (5, 1) = (-8397249 / 2500000000) := rfl
@[simp] theorem lookup_current_7_11 : currentPadding literalP (3, 1) (5, 1) = (-2886061 / 1000000000) := rfl
@[simp] theorem lookup_descent_7_12 : literalDescent (3, 1) (6, 0) = (26079286359 / 4000000000000) := rfl
@[simp] theorem lookup_previous_7_12 : previousPadding literalP (3, 1) (6, 0) = (2996751411 / 160000000000) := rfl
@[simp] theorem lookup_current_7_12 : currentPadding literalP (3, 1) (6, 0) = (12209874729 / 1000000000000) := rfl
@[simp] theorem lookup_descent_7_13 : literalDescent (3, 1) (6, 1) = (3536177 / 5000000000) := rfl
@[simp] theorem lookup_previous_7_13 : previousPadding literalP (3, 1) (6, 1) = (1414543 / 1250000000) := rfl
@[simp] theorem lookup_current_7_13 : currentPadding literalP (3, 1) (6, 1) = (424399 / 1000000000) := rfl
@[simp] theorem lookup_descent_7_14 : literalDescent (3, 1) (7, 0) = (-1059636997 / 500000000000) := rfl
@[simp] theorem lookup_previous_7_14 : previousPadding literalP (3, 1) (7, 0) = (26381303 / 10000000000) := rfl
@[simp] theorem lookup_current_7_14 : currentPadding literalP (3, 1) (7, 0) = (2378702147 / 500000000000) := rfl
@[simp] theorem lookup_descent_7_15 : literalDescent (3, 1) (7, 1) = (-4663093 / 5000000000) := rfl
@[simp] theorem lookup_previous_7_15 : previousPadding literalP (3, 1) (7, 1) = (-25604807 / 10000000000) := rfl
@[simp] theorem lookup_current_7_15 : currentPadding literalP (3, 1) (7, 1) = (-16278621 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_16 : literalDescent (3, 1) (8, 0) = (-938131 / 1250000000) := rfl
@[simp] theorem lookup_previous_7_16 : previousPadding literalP (3, 1) (8, 0) = (-8202753 / 2500000000) := rfl
@[simp] theorem lookup_current_7_16 : currentPadding literalP (3, 1) (8, 0) = (-6326491 / 2500000000) := rfl
@[simp] theorem lookup_descent_7_17 : literalDescent (3, 1) (8, 1) = (2569977 / 2000000000) := rfl
@[simp] theorem lookup_previous_7_17 : previousPadding literalP (3, 1) (8, 1) = (12964363 / 5000000000) := rfl
@[simp] theorem lookup_current_7_17 : currentPadding literalP (3, 1) (8, 1) = (13078841 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_18 : literalDescent (3, 1) (9, 0) = (1377117 / 10000000000) := rfl
@[simp] theorem lookup_previous_7_18 : previousPadding literalP (3, 1) (9, 0) = (1377117 / 10000000000) := rfl
@[simp] theorem lookup_current_7_18 : currentPadding literalP (3, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_7_19 : literalDescent (3, 1) (9, 1) = (-5174313 / 10000000000) := rfl
@[simp] theorem lookup_previous_7_19 : previousPadding literalP (3, 1) (9, 1) = (-5174313 / 10000000000) := rfl
@[simp] theorem lookup_current_7_19 : currentPadding literalP (3, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_8_0 : literalDescent (4, 0) (0, 0) = (-38991227 / 20000000000) := rfl
@[simp] theorem lookup_previous_8_0 : previousPadding literalP (4, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_8_0 : currentPadding literalP (4, 0) (0, 0) = (3747053 / 2500000000) := rfl
@[simp] theorem lookup_descent_8_1 : literalDescent (4, 0) (0, 1) = (-6960307 / 4000000000) := rfl
@[simp] theorem lookup_previous_8_1 : previousPadding literalP (4, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_8_1 : currentPadding literalP (4, 0) (0, 1) = (6446739 / 5000000000) := rfl
@[simp] theorem lookup_descent_8_2 : literalDescent (4, 0) (1, 0) = (13076461 / 1250000000) := rfl
@[simp] theorem lookup_previous_8_2 : previousPadding literalP (4, 0) (1, 0) = (202901393 / 5000000000) := rfl
@[simp] theorem lookup_current_8_2 : currentPadding literalP (4, 0) (1, 0) = (74397693 / 2000000000) := rfl
@[simp] theorem lookup_descent_8_3 : literalDescent (4, 0) (1, 1) = (1057717183 / 200000000000) := rfl
@[simp] theorem lookup_previous_8_3 : previousPadding literalP (4, 0) (1, 1) = (33465772407 / 800000000000) := rfl
@[simp] theorem lookup_current_8_3 : currentPadding literalP (4, 0) (1, 1) = (18919260781 / 800000000000) := rfl
@[simp] theorem lookup_descent_8_4 : literalDescent (4, 0) (2, 0) = (-25574771 / 2000000000) := rfl
@[simp] theorem lookup_previous_8_4 : previousPadding literalP (4, 0) (2, 0) = (-948225799 / 10000000000) := rfl
@[simp] theorem lookup_current_8_4 : currentPadding literalP (4, 0) (2, 0) = (-102543993 / 1250000000) := rfl
@[simp] theorem lookup_descent_8_5 : literalDescent (4, 0) (2, 1) = (-23363691 / 5000000000) := rfl
@[simp] theorem lookup_previous_8_5 : previousPadding literalP (4, 0) (2, 1) = (-48354603 / 2000000000) := rfl
@[simp] theorem lookup_current_8_5 : currentPadding literalP (4, 0) (2, 1) = (-195045633 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_6 : literalDescent (4, 0) (3, 0) = (-302975579 / 20000000000) := rfl
@[simp] theorem lookup_previous_8_6 : previousPadding literalP (4, 0) (3, 0) = (-102597199 / 2000000000) := rfl
@[simp] theorem lookup_current_8_6 : currentPadding literalP (4, 0) (3, 0) = (-221055757 / 5000000000) := rfl
@[simp] theorem lookup_descent_8_7 : literalDescent (4, 0) (3, 1) = (-65887223 / 20000000000) := rfl
@[simp] theorem lookup_previous_8_7 : previousPadding literalP (4, 0) (3, 1) = (541539 / 2500000000) := rfl
@[simp] theorem lookup_current_8_7 : currentPadding literalP (4, 0) (3, 1) = (-45503541 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_8 : literalDescent (4, 0) (4, 0) = (464555833 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_8 : previousPadding literalP (4, 0) (4, 0) = (382082687 / 2000000000) := rfl
@[simp] theorem lookup_current_8_8 : currentPadding literalP (4, 0) (4, 0) = (46078259 / 312500000) := rfl
@[simp] theorem lookup_descent_8_9 : literalDescent (4, 0) (4, 1) = (37244731 / 4000000000) := rfl
@[simp] theorem lookup_previous_8_9 : previousPadding literalP (4, 0) (4, 1) = (6174493 / 5000000000) := rfl
@[simp] theorem lookup_current_8_9 : currentPadding literalP (4, 0) (4, 1) = (712423 / 250000000) := rfl
@[simp] theorem lookup_descent_8_10 : literalDescent (4, 0) (5, 0) = (-111908109 / 5000000000) := rfl
@[simp] theorem lookup_previous_8_10 : previousPadding literalP (4, 0) (5, 0) = (-221055757 / 5000000000) := rfl
@[simp] theorem lookup_current_8_10 : currentPadding literalP (4, 0) (5, 0) = (-232618639 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_11 : literalDescent (4, 0) (5, 1) = (-1626664973 / 200000000000) := rfl
@[simp] theorem lookup_previous_8_11 : previousPadding literalP (4, 0) (5, 1) = (-59582163 / 2000000000) := rfl
@[simp] theorem lookup_current_8_11 : currentPadding literalP (4, 0) (5, 1) = (-218224957 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_12 : literalDescent (4, 0) (6, 0) = (-123185883 / 5000000000) := rfl
@[simp] theorem lookup_previous_8_12 : previousPadding literalP (4, 0) (6, 0) = (-676278039 / 10000000000) := rfl
@[simp] theorem lookup_current_8_12 : currentPadding literalP (4, 0) (6, 0) = (-429906273 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_13 : literalDescent (4, 0) (6, 1) = (27544907 / 5000000000) := rfl
@[simp] theorem lookup_previous_8_13 : previousPadding literalP (4, 0) (6, 1) = (158323341 / 5000000000) := rfl
@[simp] theorem lookup_current_8_13 : currentPadding literalP (4, 0) (6, 1) = (65389217 / 2500000000) := rfl
@[simp] theorem lookup_descent_8_14 : literalDescent (4, 0) (7, 0) = (208576891 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_14 : previousPadding literalP (4, 0) (7, 0) = (210934073 / 10000000000) := rfl
@[simp] theorem lookup_current_8_14 : currentPadding literalP (4, 0) (7, 0) = (1178591 / 5000000000) := rfl
@[simp] theorem lookup_descent_8_15 : literalDescent (4, 0) (7, 1) = (145087 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_15 : previousPadding literalP (4, 0) (7, 1) = (-2203431 / 5000000000) := rfl
@[simp] theorem lookup_current_8_15 : currentPadding literalP (4, 0) (7, 1) = (-4551949 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_16 : literalDescent (4, 0) (8, 0) = (3708419 / 1000000000) := rfl
@[simp] theorem lookup_previous_8_16 : previousPadding literalP (4, 0) (8, 0) = (98234413 / 10000000000) := rfl
@[simp] theorem lookup_current_8_16 : currentPadding literalP (4, 0) (8, 0) = (61150223 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_17 : literalDescent (4, 0) (8, 1) = (-11915681 / 2500000000) := rfl
@[simp] theorem lookup_previous_8_17 : previousPadding literalP (4, 0) (8, 1) = (-95903187 / 10000000000) := rfl
@[simp] theorem lookup_current_8_17 : currentPadding literalP (4, 0) (8, 1) = (-48240463 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_18 : literalDescent (4, 0) (9, 0) = (-143073 / 31250000) := rfl
@[simp] theorem lookup_previous_8_18 : previousPadding literalP (4, 0) (9, 0) = (-143073 / 31250000) := rfl
@[simp] theorem lookup_current_8_18 : currentPadding literalP (4, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_8_19 : literalDescent (4, 0) (9, 1) = (12417573 / 5000000000) := rfl
@[simp] theorem lookup_previous_8_19 : previousPadding literalP (4, 0) (9, 1) = (12417573 / 5000000000) := rfl
@[simp] theorem lookup_current_8_19 : currentPadding literalP (4, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_9_0 : literalDescent (4, 1) (0, 0) = (-5573931437 / 4000000000000) := rfl
@[simp] theorem lookup_previous_9_0 : previousPadding literalP (4, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_9_0 : currentPadding literalP (4, 1) (0, 0) = (-71263753 / 5000000000) := rfl
@[simp] theorem lookup_descent_9_1 : literalDescent (4, 1) (0, 1) = (-4463921009 / 4000000000000) := rfl
@[simp] theorem lookup_previous_9_1 : previousPadding literalP (4, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_9_1 : currentPadding literalP (4, 1) (0, 1) = (-72651833 / 5000000000) := rfl
@[simp] theorem lookup_descent_9_2 : literalDescent (4, 1) (1, 0) = (71761909 / 20000000000) := rfl
@[simp] theorem lookup_previous_9_2 : previousPadding literalP (4, 1) (1, 0) = (12012619 / 10000000000) := rfl
@[simp] theorem lookup_current_9_2 : currentPadding literalP (4, 1) (1, 0) = (11732253 / 2500000000) := rfl
@[simp] theorem lookup_descent_9_3 : literalDescent (4, 1) (1, 1) = (2739104097 / 2000000000000) := rfl
@[simp] theorem lookup_previous_9_3 : previousPadding literalP (4, 1) (1, 1) = (1895001 / 2000000000) := rfl
@[simp] theorem lookup_current_9_3 : currentPadding literalP (4, 1) (1, 1) = (18789953 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_4 : literalDescent (4, 1) (2, 0) = (1933547277 / 1000000000000) := rfl
@[simp] theorem lookup_previous_9_4 : previousPadding literalP (4, 1) (2, 0) = (41121351277 / 1000000000000) := rfl
@[simp] theorem lookup_current_9_4 : currentPadding literalP (4, 1) (2, 0) = (9796951 / 250000000) := rfl
@[simp] theorem lookup_descent_9_5 : literalDescent (4, 1) (2, 1) = (-5309887 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_5 : previousPadding literalP (4, 1) (2, 1) = (-38898883 / 10000000000) := rfl
@[simp] theorem lookup_current_9_5 : currentPadding literalP (4, 1) (2, 1) = (-8397249 / 2500000000) := rfl
@[simp] theorem lookup_descent_9_6 : literalDescent (4, 1) (3, 0) = (-33717611363 / 4000000000000) := rfl
@[simp] theorem lookup_previous_9_6 : previousPadding literalP (4, 1) (3, 0) = (-93233353 / 2500000000) := rfl
@[simp] theorem lookup_current_9_6 : currentPadding literalP (4, 1) (3, 0) = (-59582163 / 2000000000) := rfl
@[simp] theorem lookup_descent_9_7 : literalDescent (4, 1) (3, 1) = (-5857435391 / 4000000000000) := rfl
@[simp] theorem lookup_previous_9_7 : previousPadding literalP (4, 1) (3, 1) = (-85377977 / 10000000000) := rfl
@[simp] theorem lookup_current_9_7 : currentPadding literalP (4, 1) (3, 1) = (-80004919 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_8 : literalDescent (4, 1) (4, 0) = (37244731 / 4000000000) := rfl
@[simp] theorem lookup_previous_9_8 : previousPadding literalP (4, 1) (4, 0) = (6174493 / 5000000000) := rfl
@[simp] theorem lookup_current_9_8 : currentPadding literalP (4, 1) (4, 0) = (712423 / 250000000) := rfl
@[simp] theorem lookup_descent_9_9 : literalDescent (4, 1) (4, 1) = (1247369849 / 250000000000) := rfl
@[simp] theorem lookup_previous_9_9 : previousPadding literalP (4, 1) (4, 1) = (74915844753 / 2000000000000) := rfl
@[simp] theorem lookup_current_9_9 : currentPadding literalP (4, 1) (4, 1) = (2633069497 / 125000000000) := rfl
@[simp] theorem lookup_descent_9_10 : literalDescent (4, 1) (5, 0) = (-12051117 / 2000000000) := rfl
@[simp] theorem lookup_previous_9_10 : previousPadding literalP (4, 1) (5, 0) = (-45503541 / 10000000000) := rfl
@[simp] theorem lookup_current_9_10 : currentPadding literalP (4, 1) (5, 0) = (428701 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_11 : literalDescent (4, 1) (5, 1) = (-5342176489 / 2000000000000) := rfl
@[simp] theorem lookup_previous_9_11 : previousPadding literalP (4, 1) (5, 1) = (-80004919 / 10000000000) := rfl
@[simp] theorem lookup_current_9_11 : currentPadding literalP (4, 1) (5, 1) = (-54941221 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_12 : literalDescent (4, 1) (6, 0) = (-39608981 / 5000000000) := rfl
@[simp] theorem lookup_previous_9_12 : previousPadding literalP (4, 1) (6, 0) = (-161504991 / 10000000000) := rfl
@[simp] theorem lookup_current_9_12 : currentPadding literalP (4, 1) (6, 0) = (-82287029 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_13 : literalDescent (4, 1) (6, 1) = (-6850957 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_13 : previousPadding literalP (4, 1) (6, 1) = (-2886061 / 1000000000) := rfl
@[simp] theorem lookup_current_9_13 : currentPadding literalP (4, 1) (6, 1) = (-22009653 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_14 : literalDescent (4, 1) (7, 0) = (10727180729 / 1000000000000) := rfl
@[simp] theorem lookup_previous_9_14 : previousPadding literalP (4, 1) (7, 0) = (12209874729 / 1000000000000) := rfl
@[simp] theorem lookup_current_9_14 : currentPadding literalP (4, 1) (7, 0) = (741347 / 500000000) := rfl
@[simp] theorem lookup_descent_9_15 : literalDescent (4, 1) (7, 1) = (278003 / 500000000) := rfl
@[simp] theorem lookup_previous_9_15 : previousPadding literalP (4, 1) (7, 1) = (424399 / 1000000000) := rfl
@[simp] theorem lookup_current_9_15 : currentPadding literalP (4, 1) (7, 1) = (-131607 / 1000000000) := rfl
@[simp] theorem lookup_descent_9_16 : literalDescent (4, 1) (8, 0) = (370415297 / 500000000000) := rfl
@[simp] theorem lookup_previous_9_16 : previousPadding literalP (4, 1) (8, 0) = (2378702147 / 500000000000) := rfl
@[simp] theorem lookup_current_9_16 : currentPadding literalP (4, 1) (8, 0) = (40165737 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_17 : literalDescent (4, 1) (8, 1) = (-8777049 / 5000000000) := rfl
@[simp] theorem lookup_previous_9_17 : previousPadding literalP (4, 1) (8, 1) = (-16278621 / 10000000000) := rfl
@[simp] theorem lookup_current_9_17 : currentPadding literalP (4, 1) (8, 1) = (1275477 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_18 : literalDescent (4, 1) (9, 0) = (-6326491 / 2500000000) := rfl
@[simp] theorem lookup_previous_9_18 : previousPadding literalP (4, 1) (9, 0) = (-6326491 / 2500000000) := rfl
@[simp] theorem lookup_current_9_18 : currentPadding literalP (4, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_9_19 : literalDescent (4, 1) (9, 1) = (13078841 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_19 : previousPadding literalP (4, 1) (9, 1) = (13078841 / 10000000000) := rfl
@[simp] theorem lookup_current_9_19 : currentPadding literalP (4, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_10_0 : literalDescent (5, 0) (0, 0) = (8842821 / 10000000000) := rfl
@[simp] theorem lookup_previous_10_0 : previousPadding literalP (5, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_10_0 : currentPadding literalP (5, 0) (0, 0) = (-1486621 / 2000000000) := rfl
@[simp] theorem lookup_descent_10_1 : literalDescent (5, 0) (0, 1) = (3403207 / 4000000000) := rfl
@[simp] theorem lookup_previous_10_1 : previousPadding literalP (5, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_10_1 : currentPadding literalP (5, 0) (0, 1) = (-1774559 / 2500000000) := rfl
@[simp] theorem lookup_descent_10_2 : literalDescent (5, 0) (1, 0) = (-52679853 / 20000000000) := rfl
@[simp] theorem lookup_previous_10_2 : previousPadding literalP (5, 0) (1, 0) = (3747053 / 2500000000) := rfl
@[simp] theorem lookup_current_10_2 : currentPadding literalP (5, 0) (1, 0) = (10332043 / 2500000000) := rfl
@[simp] theorem lookup_descent_10_3 : literalDescent (5, 0) (1, 1) = (-643290559 / 500000000000) := rfl
@[simp] theorem lookup_previous_10_3 : previousPadding literalP (5, 0) (1, 1) = (6446739 / 5000000000) := rfl
@[simp] theorem lookup_current_10_3 : currentPadding literalP (5, 0) (1, 1) = (190231 / 78125000) := rfl
@[simp] theorem lookup_descent_10_4 : literalDescent (5, 0) (2, 0) = (16593809 / 2000000000) := rfl
@[simp] theorem lookup_previous_10_4 : previousPadding literalP (5, 0) (2, 0) = (74397693 / 2000000000) := rfl
@[simp] theorem lookup_current_10_4 : currentPadding literalP (5, 0) (2, 0) = (14450971 / 500000000) := rfl
@[simp] theorem lookup_descent_10_5 : literalDescent (5, 0) (2, 1) = (1967751863 / 400000000000) := rfl
@[simp] theorem lookup_previous_10_5 : previousPadding literalP (5, 0) (2, 1) = (18919260781 / 800000000000) := rfl
@[simp] theorem lookup_current_10_5 : currentPadding literalP (5, 0) (2, 1) = (2996751411 / 160000000000) := rfl
@[simp] theorem lookup_descent_10_6 : literalDescent (5, 0) (3, 0) = (-28814781 / 2000000000) := rfl
@[simp] theorem lookup_previous_10_6 : previousPadding literalP (5, 0) (3, 0) = (-102543993 / 1250000000) := rfl
@[simp] theorem lookup_current_10_6 : currentPadding literalP (5, 0) (3, 0) = (-676278039 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_7 : literalDescent (5, 0) (3, 1) = (-16770321 / 5000000000) := rfl
@[simp] theorem lookup_previous_10_7 : previousPadding literalP (5, 0) (3, 1) = (-195045633 / 10000000000) := rfl
@[simp] theorem lookup_current_10_7 : currentPadding literalP (5, 0) (3, 1) = (-161504991 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_8 : literalDescent (5, 0) (4, 0) = (-111908109 / 5000000000) := rfl
@[simp] theorem lookup_previous_10_8 : previousPadding literalP (5, 0) (4, 0) = (-221055757 / 5000000000) := rfl
@[simp] theorem lookup_current_10_8 : currentPadding literalP (5, 0) (4, 0) = (-232618639 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_9 : literalDescent (5, 0) (4, 1) = (-12051117 / 2000000000) := rfl
@[simp] theorem lookup_previous_10_9 : previousPadding literalP (5, 0) (4, 1) = (-45503541 / 10000000000) := rfl
@[simp] theorem lookup_current_10_9 : currentPadding literalP (5, 0) (4, 1) = (428701 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_10 : literalDescent (5, 0) (5, 0) = (263696429 / 5000000000) := rfl
@[simp] theorem lookup_previous_10_10 : previousPadding literalP (5, 0) (5, 0) = (46078259 / 312500000) := rfl
@[simp] theorem lookup_current_10_10 : currentPadding literalP (5, 0) (5, 0) = (972938617 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_11 : literalDescent (5, 0) (5, 1) = (110995869 / 20000000000) := rfl
@[simp] theorem lookup_previous_10_11 : previousPadding literalP (5, 0) (5, 1) = (712423 / 250000000) := rfl
@[simp] theorem lookup_current_10_11 : currentPadding literalP (5, 0) (5, 1) = (2628739 / 2000000000) := rfl
@[simp] theorem lookup_descent_10_12 : literalDescent (5, 0) (6, 0) = (46071073 / 20000000000) := rfl
@[simp] theorem lookup_previous_10_12 : previousPadding literalP (5, 0) (6, 0) = (-232618639 / 10000000000) := rfl
@[simp] theorem lookup_current_10_12 : currentPadding literalP (5, 0) (6, 0) = (-268567769 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_13 : literalDescent (5, 0) (6, 1) = (-14533771479 / 2000000000000) := rfl
@[simp] theorem lookup_previous_10_13 : previousPadding literalP (5, 0) (6, 1) = (-218224957 / 10000000000) := rfl
@[simp] theorem lookup_current_10_13 : currentPadding literalP (5, 0) (6, 1) = (-73523157 / 5000000000) := rfl
@[simp] theorem lookup_descent_10_14 : literalDescent (5, 0) (7, 0) = (-167889543 / 5000000000) := rfl
@[simp] theorem lookup_previous_10_14 : previousPadding literalP (5, 0) (7, 0) = (-429906273 / 10000000000) := rfl
@[simp] theorem lookup_current_10_14 : currentPadding literalP (5, 0) (7, 0) = (-94127187 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_15 : literalDescent (5, 0) (7, 1) = (4184541 / 625000000) := rfl
@[simp] theorem lookup_previous_10_15 : previousPadding literalP (5, 0) (7, 1) = (65389217 / 2500000000) := rfl
@[simp] theorem lookup_current_10_15 : currentPadding literalP (5, 0) (7, 1) = (48651053 / 2500000000) := rfl
@[simp] theorem lookup_descent_10_16 : literalDescent (5, 0) (8, 0) = (6654663 / 2500000000) := rfl
@[simp] theorem lookup_previous_10_16 : previousPadding literalP (5, 0) (8, 0) = (1178591 / 5000000000) := rfl
@[simp] theorem lookup_current_10_16 : currentPadding literalP (5, 0) (8, 0) = (-2426147 / 1000000000) := rfl
@[simp] theorem lookup_descent_10_17 : literalDescent (5, 0) (8, 1) = (23709477 / 5000000000) := rfl
@[simp] theorem lookup_previous_10_17 : previousPadding literalP (5, 0) (8, 1) = (-4551949 / 10000000000) := rfl
@[simp] theorem lookup_current_10_17 : currentPadding literalP (5, 0) (8, 1) = (-51970903 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_18 : literalDescent (5, 0) (9, 0) = (61150223 / 10000000000) := rfl
@[simp] theorem lookup_previous_10_18 : previousPadding literalP (5, 0) (9, 0) = (61150223 / 10000000000) := rfl
@[simp] theorem lookup_current_10_18 : currentPadding literalP (5, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_10_19 : literalDescent (5, 0) (9, 1) = (-48240463 / 10000000000) := rfl
@[simp] theorem lookup_previous_10_19 : previousPadding literalP (5, 0) (9, 1) = (-48240463 / 10000000000) := rfl
@[simp] theorem lookup_current_10_19 : currentPadding literalP (5, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_11_0 : literalDescent (5, 1) (0, 0) = (347422703 / 200000000000) := rfl
@[simp] theorem lookup_previous_11_0 : previousPadding literalP (5, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_11_0 : currentPadding literalP (5, 1) (0, 0) = (27842473 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_1 : literalDescent (5, 1) (0, 1) = (1928852689 / 2000000000000) := rfl
@[simp] theorem lookup_previous_11_1 : previousPadding literalP (5, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_11_1 : currentPadding literalP (5, 1) (0, 1) = (17781659 / 5000000000) := rfl
@[simp] theorem lookup_descent_11_2 : literalDescent (5, 1) (1, 0) = (-89791801 / 20000000000) := rfl
@[simp] theorem lookup_previous_11_2 : previousPadding literalP (5, 1) (1, 0) = (-71263753 / 5000000000) := rfl
@[simp] theorem lookup_current_11_2 : currentPadding literalP (5, 1) (1, 0) = (-168428939 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_3 : literalDescent (5, 1) (1, 1) = (-7471768719 / 4000000000000) := rfl
@[simp] theorem lookup_previous_11_3 : previousPadding literalP (5, 1) (1, 1) = (-72651833 / 5000000000) := rfl
@[simp] theorem lookup_current_11_3 : currentPadding literalP (5, 1) (1, 1) = (-9594713 / 2500000000) := rfl
@[simp] theorem lookup_descent_11_4 : literalDescent (5, 1) (2, 0) = (7471657 / 5000000000) := rfl
@[simp] theorem lookup_previous_11_4 : previousPadding literalP (5, 1) (2, 0) = (11732253 / 2500000000) := rfl
@[simp] theorem lookup_current_11_4 : currentPadding literalP (5, 1) (2, 0) = (15992849 / 5000000000) := rfl
@[simp] theorem lookup_descent_11_5 : literalDescent (5, 1) (2, 1) = (7473609 / 10000000000) := rfl
@[simp] theorem lookup_previous_11_5 : previousPadding literalP (5, 1) (2, 1) = (18789953 / 10000000000) := rfl
@[simp] theorem lookup_current_11_5 : currentPadding literalP (5, 1) (2, 1) = (1414543 / 1250000000) := rfl
@[simp] theorem lookup_descent_11_6 : literalDescent (5, 1) (3, 0) = (37615679 / 5000000000) := rfl
@[simp] theorem lookup_previous_11_6 : previousPadding literalP (5, 1) (3, 0) = (9796951 / 250000000) := rfl
@[simp] theorem lookup_current_11_6 : currentPadding literalP (5, 1) (3, 0) = (158323341 / 5000000000) := rfl
@[simp] theorem lookup_descent_11_7 : literalDescent (5, 1) (3, 1) = (-2364193 / 5000000000) := rfl
@[simp] theorem lookup_previous_11_7 : previousPadding literalP (5, 1) (3, 1) = (-8397249 / 2500000000) := rfl
@[simp] theorem lookup_current_11_7 : currentPadding literalP (5, 1) (3, 1) = (-2886061 / 1000000000) := rfl
@[simp] theorem lookup_descent_11_8 : literalDescent (5, 1) (4, 0) = (-1626664973 / 200000000000) := rfl
@[simp] theorem lookup_previous_11_8 : previousPadding literalP (5, 1) (4, 0) = (-59582163 / 2000000000) := rfl
@[simp] theorem lookup_current_11_8 : currentPadding literalP (5, 1) (4, 0) = (-218224957 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_9 : literalDescent (5, 1) (4, 1) = (-5342176489 / 2000000000000) := rfl
@[simp] theorem lookup_previous_11_9 : previousPadding literalP (5, 1) (4, 1) = (-80004919 / 10000000000) := rfl
@[simp] theorem lookup_current_11_9 : currentPadding literalP (5, 1) (4, 1) = (-54941221 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_10 : literalDescent (5, 1) (5, 0) = (110995869 / 20000000000) := rfl
@[simp] theorem lookup_previous_11_10 : previousPadding literalP (5, 1) (5, 0) = (712423 / 250000000) := rfl
@[simp] theorem lookup_current_11_10 : currentPadding literalP (5, 1) (5, 0) = (2628739 / 2000000000) := rfl
@[simp] theorem lookup_descent_11_11 : literalDescent (5, 1) (5, 1) = (1008997801 / 200000000000) := rfl
@[simp] theorem lookup_previous_11_11 : previousPadding literalP (5, 1) (5, 1) = (2633069497 / 125000000000) := rfl
@[simp] theorem lookup_current_11_11 : currentPadding literalP (5, 1) (5, 1) = (401676349 / 25000000000) := rfl
@[simp] theorem lookup_descent_11_12 : literalDescent (5, 1) (6, 0) = (-22797173 / 20000000000) := rfl
@[simp] theorem lookup_previous_11_12 : previousPadding literalP (5, 1) (6, 0) = (428701 / 10000000000) := rfl
@[simp] theorem lookup_current_11_12 : currentPadding literalP (5, 1) (6, 0) = (-543153 / 5000000000) := rfl
@[simp] theorem lookup_descent_11_13 : literalDescent (5, 1) (6, 1) = (-359870501 / 4000000000000) := rfl
@[simp] theorem lookup_previous_11_13 : previousPadding literalP (5, 1) (6, 1) = (-54941221 / 10000000000) := rfl
@[simp] theorem lookup_current_11_13 : currentPadding literalP (5, 1) (6, 1) = (-3470413 / 625000000) := rfl
@[simp] theorem lookup_descent_11_14 : literalDescent (5, 1) (7, 0) = (-13745167 / 2000000000) := rfl
@[simp] theorem lookup_previous_11_14 : previousPadding literalP (5, 1) (7, 0) = (-82287029 / 10000000000) := rfl
@[simp] theorem lookup_current_11_14 : currentPadding literalP (5, 1) (7, 0) = (-6780597 / 5000000000) := rfl
@[simp] theorem lookup_descent_11_15 : literalDescent (5, 1) (7, 1) = (-8993809 / 10000000000) := rfl
@[simp] theorem lookup_previous_11_15 : previousPadding literalP (5, 1) (7, 1) = (-22009653 / 10000000000) := rfl
@[simp] theorem lookup_current_11_15 : currentPadding literalP (5, 1) (7, 1) = (-3253961 / 2500000000) := rfl
@[simp] theorem lookup_descent_11_16 : literalDescent (5, 1) (8, 0) = (786023 / 2500000000) := rfl
@[simp] theorem lookup_previous_11_16 : previousPadding literalP (5, 1) (8, 0) = (741347 / 500000000) := rfl
@[simp] theorem lookup_current_11_16 : currentPadding literalP (5, 1) (8, 0) = (365089 / 312500000) := rfl
@[simp] theorem lookup_descent_11_17 : literalDescent (5, 1) (8, 1) = (-1103883 / 1250000000) := rfl
@[simp] theorem lookup_previous_11_17 : previousPadding literalP (5, 1) (8, 1) = (-131607 / 1000000000) := rfl
@[simp] theorem lookup_current_11_17 : currentPadding literalP (5, 1) (8, 1) = (3757497 / 5000000000) := rfl
@[simp] theorem lookup_descent_11_18 : literalDescent (5, 1) (9, 0) = (40165737 / 10000000000) := rfl
@[simp] theorem lookup_previous_11_18 : previousPadding literalP (5, 1) (9, 0) = (40165737 / 10000000000) := rfl
@[simp] theorem lookup_current_11_18 : currentPadding literalP (5, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_11_19 : literalDescent (5, 1) (9, 1) = (1275477 / 10000000000) := rfl
@[simp] theorem lookup_previous_11_19 : previousPadding literalP (5, 1) (9, 1) = (1275477 / 10000000000) := rfl
@[simp] theorem lookup_current_11_19 : currentPadding literalP (5, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_12_0 : literalDescent (6, 0) (0, 0) = (-5175427 / 2500000000) := rfl
@[simp] theorem lookup_previous_12_0 : previousPadding literalP (6, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_12_0 : currentPadding literalP (6, 0) (0, 0) = (22248179 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_1 : literalDescent (6, 0) (0, 1) = (-1336127 / 20000000000) := rfl
@[simp] theorem lookup_previous_12_1 : previousPadding literalP (6, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_12_1 : currentPadding literalP (6, 0) (0, 1) = (1107293 / 5000000000) := rfl
@[simp] theorem lookup_descent_12_2 : literalDescent (6, 0) (1, 0) = (13989309 / 5000000000) := rfl
@[simp] theorem lookup_previous_12_2 : previousPadding literalP (6, 0) (1, 0) = (-1486621 / 2000000000) := rfl
@[simp] theorem lookup_current_12_2 : currentPadding literalP (6, 0) (1, 0) = (-300759 / 125000000) := rfl
@[simp] theorem lookup_descent_12_3 : literalDescent (6, 0) (1, 1) = (2715327169 / 4000000000000) := rfl
@[simp] theorem lookup_previous_12_3 : previousPadding literalP (6, 0) (1, 1) = (-1774559 / 2500000000) := rfl
@[simp] theorem lookup_current_12_3 : currentPadding literalP (6, 0) (1, 1) = (-1841481 / 500000000) := rfl
@[simp] theorem lookup_descent_12_4 : literalDescent (6, 0) (2, 0) = (-27189693 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_4 : previousPadding literalP (6, 0) (2, 0) = (10332043 / 2500000000) := rfl
@[simp] theorem lookup_current_12_4 : currentPadding literalP (6, 0) (2, 0) = (13703573 / 2000000000) := rfl
@[simp] theorem lookup_descent_12_5 : literalDescent (6, 0) (2, 1) = (-406347 / 2000000000) := rfl
@[simp] theorem lookup_previous_12_5 : previousPadding literalP (6, 0) (2, 1) = (190231 / 78125000) := rfl
@[simp] theorem lookup_current_12_5 : currentPadding literalP (6, 0) (2, 1) = (26381303 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_6 : literalDescent (6, 0) (3, 0) = (78085347 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_6 : previousPadding literalP (6, 0) (3, 0) = (14450971 / 500000000) := rfl
@[simp] theorem lookup_current_12_6 : currentPadding literalP (6, 0) (3, 0) = (210934073 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_7 : literalDescent (6, 0) (3, 1) = (26079286359 / 4000000000000) := rfl
@[simp] theorem lookup_previous_12_7 : previousPadding literalP (6, 0) (3, 1) = (2996751411 / 160000000000) := rfl
@[simp] theorem lookup_current_12_7 : currentPadding literalP (6, 0) (3, 1) = (12209874729 / 1000000000000) := rfl
@[simp] theorem lookup_descent_12_8 : literalDescent (6, 0) (4, 0) = (-123185883 / 5000000000) := rfl
@[simp] theorem lookup_previous_12_8 : previousPadding literalP (6, 0) (4, 0) = (-676278039 / 10000000000) := rfl
@[simp] theorem lookup_current_12_8 : currentPadding literalP (6, 0) (4, 0) = (-429906273 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_9 : literalDescent (6, 0) (4, 1) = (-39608981 / 5000000000) := rfl
@[simp] theorem lookup_previous_12_9 : previousPadding literalP (6, 0) (4, 1) = (-161504991 / 10000000000) := rfl
@[simp] theorem lookup_current_12_9 : currentPadding literalP (6, 0) (4, 1) = (-82287029 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_10 : literalDescent (6, 0) (5, 0) = (46071073 / 20000000000) := rfl
@[simp] theorem lookup_previous_12_10 : previousPadding literalP (6, 0) (5, 0) = (-232618639 / 10000000000) := rfl
@[simp] theorem lookup_current_12_10 : currentPadding literalP (6, 0) (5, 0) = (-268567769 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_11 : literalDescent (6, 0) (5, 1) = (-22797173 / 20000000000) := rfl
@[simp] theorem lookup_previous_12_11 : previousPadding literalP (6, 0) (5, 1) = (428701 / 10000000000) := rfl
@[simp] theorem lookup_current_12_11 : currentPadding literalP (6, 0) (5, 1) = (-543153 / 5000000000) := rfl
@[simp] theorem lookup_descent_12_12 : literalDescent (6, 0) (6, 0) = (108284327 / 2500000000) := rfl
@[simp] theorem lookup_previous_12_12 : previousPadding literalP (6, 0) (6, 0) = (972938617 / 10000000000) := rfl
@[simp] theorem lookup_current_12_12 : currentPadding literalP (6, 0) (6, 0) = (134958387 / 2500000000) := rfl
@[simp] theorem lookup_descent_12_13 : literalDescent (6, 0) (6, 1) = (-99947 / 400000000) := rfl
@[simp] theorem lookup_previous_12_13 : previousPadding literalP (6, 0) (6, 1) = (2628739 / 2000000000) := rfl
@[simp] theorem lookup_current_12_13 : currentPadding literalP (6, 0) (6, 1) = (28587251 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_14 : literalDescent (6, 0) (7, 0) = (-463440661 / 20000000000) := rfl
@[simp] theorem lookup_previous_12_14 : previousPadding literalP (6, 0) (7, 0) = (-268567769 / 10000000000) := rfl
@[simp] theorem lookup_current_12_14 : currentPadding literalP (6, 0) (7, 0) = (-18431779 / 5000000000) := rfl
@[simp] theorem lookup_descent_12_15 : literalDescent (6, 0) (7, 1) = (-2570923591 / 500000000000) := rfl
@[simp] theorem lookup_previous_12_15 : previousPadding literalP (6, 0) (7, 1) = (-73523157 / 5000000000) := rfl
@[simp] theorem lookup_current_12_15 : currentPadding literalP (6, 0) (7, 1) = (-47815269 / 5000000000) := rfl
@[simp] theorem lookup_descent_12_16 : literalDescent (6, 0) (8, 0) = (-5995921 / 5000000000) := rfl
@[simp] theorem lookup_previous_12_16 : previousPadding literalP (6, 0) (8, 0) = (-94127187 / 10000000000) := rfl
@[simp] theorem lookup_current_12_16 : currentPadding literalP (6, 0) (8, 0) = (-16427069 / 2000000000) := rfl
@[simp] theorem lookup_descent_12_17 : literalDescent (6, 0) (8, 1) = (127217863 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_17 : previousPadding literalP (6, 0) (8, 1) = (48651053 / 2500000000) := rfl
@[simp] theorem lookup_current_12_17 : currentPadding literalP (6, 0) (8, 1) = (67386349 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_18 : literalDescent (6, 0) (9, 0) = (-2426147 / 1000000000) := rfl
@[simp] theorem lookup_previous_12_18 : previousPadding literalP (6, 0) (9, 0) = (-2426147 / 1000000000) := rfl
@[simp] theorem lookup_current_12_18 : currentPadding literalP (6, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_12_19 : literalDescent (6, 0) (9, 1) = (-51970903 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_19 : previousPadding literalP (6, 0) (9, 1) = (-51970903 / 10000000000) := rfl
@[simp] theorem lookup_current_12_19 : currentPadding literalP (6, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_13_0 : literalDescent (6, 1) (0, 0) = (-331230321 / 2000000000000) := rfl
@[simp] theorem lookup_previous_13_0 : previousPadding literalP (6, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_13_0 : currentPadding literalP (6, 1) (0, 0) = (-4226673 / 2000000000) := rfl
@[simp] theorem lookup_descent_13_1 : literalDescent (6, 1) (0, 1) = (659606701 / 4000000000000) := rfl
@[simp] theorem lookup_previous_13_1 : previousPadding literalP (6, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_13_1 : currentPadding literalP (6, 1) (0, 1) = (-6111159 / 2500000000) := rfl
@[simp] theorem lookup_descent_13_2 : literalDescent (6, 1) (1, 0) = (22425099 / 20000000000) := rfl
@[simp] theorem lookup_previous_13_2 : previousPadding literalP (6, 1) (1, 0) = (27842473 / 10000000000) := rfl
@[simp] theorem lookup_current_13_2 : currentPadding literalP (6, 1) (1, 0) = (27980893 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_3 : literalDescent (6, 1) (1, 1) = (141054337 / 500000000000) := rfl
@[simp] theorem lookup_previous_13_3 : previousPadding literalP (6, 1) (1, 1) = (17781659 / 5000000000) := rfl
@[simp] theorem lookup_current_13_3 : currentPadding literalP (6, 1) (1, 1) = (34141273 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_4 : literalDescent (6, 1) (2, 0) = (-10107251 / 2500000000) := rfl
@[simp] theorem lookup_previous_13_4 : previousPadding literalP (6, 1) (2, 0) = (-168428939 / 10000000000) := rfl
@[simp] theorem lookup_current_13_4 : currentPadding literalP (6, 1) (2, 0) = (-25599987 / 2000000000) := rfl
@[simp] theorem lookup_descent_13_5 : literalDescent (6, 1) (2, 1) = (-2554809 / 2000000000) := rfl
@[simp] theorem lookup_previous_13_5 : previousPadding literalP (6, 1) (2, 1) = (-9594713 / 2500000000) := rfl
@[simp] theorem lookup_current_13_5 : currentPadding literalP (6, 1) (2, 1) = (-25604807 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_6 : literalDescent (6, 1) (3, 0) = (454907 / 125000000) := rfl
@[simp] theorem lookup_previous_13_6 : previousPadding literalP (6, 1) (3, 0) = (15992849 / 5000000000) := rfl
@[simp] theorem lookup_current_13_6 : currentPadding literalP (6, 1) (3, 0) = (-2203431 / 5000000000) := rfl
@[simp] theorem lookup_descent_13_7 : literalDescent (6, 1) (3, 1) = (3536177 / 5000000000) := rfl
@[simp] theorem lookup_previous_13_7 : previousPadding literalP (6, 1) (3, 1) = (1414543 / 1250000000) := rfl
@[simp] theorem lookup_current_13_7 : currentPadding literalP (6, 1) (3, 1) = (424399 / 1000000000) := rfl
@[simp] theorem lookup_descent_13_8 : literalDescent (6, 1) (4, 0) = (27544907 / 5000000000) := rfl
@[simp] theorem lookup_previous_13_8 : previousPadding literalP (6, 1) (4, 0) = (158323341 / 5000000000) := rfl
@[simp] theorem lookup_current_13_8 : currentPadding literalP (6, 1) (4, 0) = (65389217 / 2500000000) := rfl
@[simp] theorem lookup_descent_13_9 : literalDescent (6, 1) (4, 1) = (-6850957 / 10000000000) := rfl
@[simp] theorem lookup_previous_13_9 : previousPadding literalP (6, 1) (4, 1) = (-2886061 / 1000000000) := rfl
@[simp] theorem lookup_current_13_9 : currentPadding literalP (6, 1) (4, 1) = (-22009653 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_10 : literalDescent (6, 1) (5, 0) = (-14533771479 / 2000000000000) := rfl
@[simp] theorem lookup_previous_13_10 : previousPadding literalP (6, 1) (5, 0) = (-218224957 / 10000000000) := rfl
@[simp] theorem lookup_current_13_10 : currentPadding literalP (6, 1) (5, 0) = (-73523157 / 5000000000) := rfl
@[simp] theorem lookup_descent_13_11 : literalDescent (6, 1) (5, 1) = (-359870501 / 4000000000000) := rfl
@[simp] theorem lookup_previous_13_11 : previousPadding literalP (6, 1) (5, 1) = (-54941221 / 10000000000) := rfl
@[simp] theorem lookup_current_13_11 : currentPadding literalP (6, 1) (5, 1) = (-3470413 / 625000000) := rfl
@[simp] theorem lookup_descent_13_12 : literalDescent (6, 1) (6, 0) = (-99947 / 400000000) := rfl
@[simp] theorem lookup_previous_13_12 : previousPadding literalP (6, 1) (6, 0) = (2628739 / 2000000000) := rfl
@[simp] theorem lookup_current_13_12 : currentPadding literalP (6, 1) (6, 0) = (28587251 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_13 : literalDescent (6, 1) (6, 1) = (12736454601 / 4000000000000) := rfl
@[simp] theorem lookup_previous_13_13 : previousPadding literalP (6, 1) (6, 1) = (401676349 / 25000000000) := rfl
@[simp] theorem lookup_current_13_13 : currentPadding literalP (6, 1) (6, 1) = (42401832641 / 4000000000000) := rfl
@[simp] theorem lookup_descent_13_14 : literalDescent (6, 1) (7, 0) = (3882707 / 4000000000) := rfl
@[simp] theorem lookup_previous_13_14 : previousPadding literalP (6, 1) (7, 0) = (-543153 / 5000000000) := rfl
@[simp] theorem lookup_current_13_14 : currentPadding literalP (6, 1) (7, 0) = (-10809193 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_15 : literalDescent (6, 1) (7, 1) = (-7103582697 / 4000000000000) := rfl
@[simp] theorem lookup_previous_13_15 : previousPadding literalP (6, 1) (7, 1) = (-3470413 / 625000000) := rfl
@[simp] theorem lookup_current_13_15 : currentPadding literalP (6, 1) (7, 1) = (-7553901 / 2000000000) := rfl
@[simp] theorem lookup_descent_13_16 : literalDescent (6, 1) (8, 0) = (-6831851 / 10000000000) := rfl
@[simp] theorem lookup_previous_13_16 : previousPadding literalP (6, 1) (8, 0) = (-6780597 / 5000000000) := rfl
@[simp] theorem lookup_current_13_16 : currentPadding literalP (6, 1) (8, 0) = (-6729343 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_17 : literalDescent (6, 1) (8, 1) = (-12614953 / 10000000000) := rfl
@[simp] theorem lookup_previous_13_17 : previousPadding literalP (6, 1) (8, 1) = (-3253961 / 2500000000) := rfl
@[simp] theorem lookup_current_13_17 : currentPadding literalP (6, 1) (8, 1) = (-400891 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_18 : literalDescent (6, 1) (9, 0) = (365089 / 312500000) := rfl
@[simp] theorem lookup_previous_13_18 : previousPadding literalP (6, 1) (9, 0) = (365089 / 312500000) := rfl
@[simp] theorem lookup_current_13_18 : currentPadding literalP (6, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_13_19 : literalDescent (6, 1) (9, 1) = (3757497 / 5000000000) := rfl
@[simp] theorem lookup_previous_13_19 : previousPadding literalP (6, 1) (9, 1) = (3757497 / 5000000000) := rfl
@[simp] theorem lookup_current_13_19 : currentPadding literalP (6, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_14_0 : literalDescent (7, 0) (0, 0) = (-23479143 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_0 : previousPadding literalP (7, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_14_0 : currentPadding literalP (7, 0) (0, 0) = (1705631 / 2500000000) := rfl
@[simp] theorem lookup_descent_14_1 : literalDescent (7, 0) (0, 1) = (-28992191 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_1 : previousPadding literalP (7, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_14_1 : currentPadding literalP (7, 0) (0, 1) = (9579093 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_2 : literalDescent (7, 0) (1, 0) = (-2741899 / 5000000000) := rfl
@[simp] theorem lookup_previous_14_2 : previousPadding literalP (7, 0) (1, 0) = (22248179 / 10000000000) := rfl
@[simp] theorem lookup_current_14_2 : currentPadding literalP (7, 0) (1, 0) = (13866017 / 5000000000) := rfl
@[simp] theorem lookup_descent_14_3 : literalDescent (7, 0) (1, 1) = (162672047 / 250000000000) := rfl
@[simp] theorem lookup_previous_14_3 : previousPadding literalP (7, 0) (1, 1) = (1107293 / 5000000000) := rfl
@[simp] theorem lookup_current_14_3 : currentPadding literalP (7, 0) (1, 1) = (156171 / 2500000000) := rfl
@[simp] theorem lookup_descent_14_4 : literalDescent (7, 0) (2, 0) = (14868251 / 2500000000) := rfl
@[simp] theorem lookup_previous_14_4 : previousPadding literalP (7, 0) (2, 0) = (-300759 / 125000000) := rfl
@[simp] theorem lookup_current_14_4 : currentPadding literalP (7, 0) (2, 0) = (-20883431 / 2500000000) := rfl
@[simp] theorem lookup_descent_14_5 : literalDescent (7, 0) (2, 1) = (-251163 / 625000000) := rfl
@[simp] theorem lookup_previous_14_5 : previousPadding literalP (7, 0) (2, 1) = (-1841481 / 500000000) := rfl
@[simp] theorem lookup_current_14_5 : currentPadding literalP (7, 0) (2, 1) = (-8202753 / 2500000000) := rfl
@[simp] theorem lookup_descent_14_6 : literalDescent (7, 0) (3, 0) = (-7429137 / 2500000000) := rfl
@[simp] theorem lookup_previous_14_6 : previousPadding literalP (7, 0) (3, 0) = (13703573 / 2000000000) := rfl
@[simp] theorem lookup_current_14_6 : currentPadding literalP (7, 0) (3, 0) = (98234413 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_7 : literalDescent (7, 0) (3, 1) = (-1059636997 / 500000000000) := rfl
@[simp] theorem lookup_previous_14_7 : previousPadding literalP (7, 0) (3, 1) = (26381303 / 10000000000) := rfl
@[simp] theorem lookup_current_14_7 : currentPadding literalP (7, 0) (3, 1) = (2378702147 / 500000000000) := rfl
@[simp] theorem lookup_descent_14_8 : literalDescent (7, 0) (4, 0) = (208576891 / 10000000000) := rfl
@[simp] theorem lookup_previous_14_8 : previousPadding literalP (7, 0) (4, 0) = (210934073 / 10000000000) := rfl
@[simp] theorem lookup_current_14_8 : currentPadding literalP (7, 0) (4, 0) = (1178591 / 5000000000) := rfl
@[simp] theorem lookup_descent_14_9 : literalDescent (7, 0) (4, 1) = (10727180729 / 1000000000000) := rfl
@[simp] theorem lookup_previous_14_9 : previousPadding literalP (7, 0) (4, 1) = (12209874729 / 1000000000000) := rfl
@[simp] theorem lookup_current_14_9 : currentPadding literalP (7, 0) (4, 1) = (741347 / 500000000) := rfl
@[simp] theorem lookup_descent_14_10 : literalDescent (7, 0) (5, 0) = (-167889543 / 5000000000) := rfl
@[simp] theorem lookup_previous_14_10 : previousPadding literalP (7, 0) (5, 0) = (-429906273 / 10000000000) := rfl
@[simp] theorem lookup_current_14_10 : currentPadding literalP (7, 0) (5, 0) = (-94127187 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_11 : literalDescent (7, 0) (5, 1) = (-13745167 / 2000000000) := rfl
@[simp] theorem lookup_previous_14_11 : previousPadding literalP (7, 0) (5, 1) = (-82287029 / 10000000000) := rfl
@[simp] theorem lookup_current_14_11 : currentPadding literalP (7, 0) (5, 1) = (-6780597 / 5000000000) := rfl
@[simp] theorem lookup_descent_14_12 : literalDescent (7, 0) (6, 0) = (-463440661 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_12 : previousPadding literalP (7, 0) (6, 0) = (-268567769 / 10000000000) := rfl
@[simp] theorem lookup_current_14_12 : currentPadding literalP (7, 0) (6, 0) = (-18431779 / 5000000000) := rfl
@[simp] theorem lookup_descent_14_13 : literalDescent (7, 0) (6, 1) = (3882707 / 4000000000) := rfl
@[simp] theorem lookup_previous_14_13 : previousPadding literalP (7, 0) (6, 1) = (-543153 / 5000000000) := rfl
@[simp] theorem lookup_current_14_13 : currentPadding literalP (7, 0) (6, 1) = (-10809193 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_14 : literalDescent (7, 0) (7, 0) = (11965421 / 250000000) := rfl
@[simp] theorem lookup_previous_14_14 : previousPadding literalP (7, 0) (7, 0) = (134958387 / 2500000000) := rfl
@[simp] theorem lookup_current_14_14 : currentPadding literalP (7, 0) (7, 0) = (4442683 / 625000000) := rfl
@[simp] theorem lookup_descent_14_15 : literalDescent (7, 0) (7, 1) = (49233621 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_15 : previousPadding literalP (7, 0) (7, 1) = (28587251 / 10000000000) := rfl
@[simp] theorem lookup_current_14_15 : currentPadding literalP (7, 0) (7, 1) = (-2370357 / 2500000000) := rfl
@[simp] theorem lookup_descent_14_16 : literalDescent (7, 0) (8, 0) = (-6261507 / 1250000000) := rfl
@[simp] theorem lookup_previous_14_16 : previousPadding literalP (7, 0) (8, 0) = (-18431779 / 5000000000) := rfl
@[simp] theorem lookup_current_14_16 : currentPadding literalP (7, 0) (8, 0) = (2073847 / 2500000000) := rfl
@[simp] theorem lookup_descent_14_17 : literalDescent (7, 0) (8, 1) = (-10705533773 / 1000000000000) := rfl
@[simp] theorem lookup_previous_14_17 : previousPadding literalP (7, 0) (8, 1) = (-47815269 / 5000000000) := rfl
@[simp] theorem lookup_current_14_17 : currentPadding literalP (7, 0) (8, 1) = (-4896641 / 5000000000) := rfl
@[simp] theorem lookup_descent_14_18 : literalDescent (7, 0) (9, 0) = (-16427069 / 2000000000) := rfl
@[simp] theorem lookup_previous_14_18 : previousPadding literalP (7, 0) (9, 0) = (-16427069 / 2000000000) := rfl
@[simp] theorem lookup_current_14_18 : currentPadding literalP (7, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_14_19 : literalDescent (7, 0) (9, 1) = (67386349 / 10000000000) := rfl
@[simp] theorem lookup_previous_14_19 : previousPadding literalP (7, 0) (9, 1) = (67386349 / 10000000000) := rfl
@[simp] theorem lookup_current_14_19 : currentPadding literalP (7, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_15_0 : literalDescent (7, 1) (0, 0) = (16616327 / 62500000000) := rfl
@[simp] theorem lookup_previous_15_0 : previousPadding literalP (7, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_15_0 : currentPadding literalP (7, 1) (0, 0) = (3385001 / 1250000000) := rfl
@[simp] theorem lookup_descent_15_1 : literalDescent (7, 1) (0, 1) = (1368367297 / 4000000000000) := rfl
@[simp] theorem lookup_previous_15_1 : previousPadding literalP (7, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_15_1 : currentPadding literalP (7, 1) (0, 1) = (745663 / 2500000000) := rfl
@[simp] theorem lookup_descent_15_2 : literalDescent (7, 1) (1, 0) = (-823173 / 500000000) := rfl
@[simp] theorem lookup_previous_15_2 : previousPadding literalP (7, 1) (1, 0) = (-4226673 / 2000000000) := rfl
@[simp] theorem lookup_current_15_2 : currentPadding literalP (7, 1) (1, 0) = (-16020851 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_3 : literalDescent (7, 1) (1, 1) = (-1397694013 / 4000000000000) := rfl
@[simp] theorem lookup_previous_15_3 : previousPadding literalP (7, 1) (1, 1) = (-6111159 / 2500000000) := rfl
@[simp] theorem lookup_current_15_3 : currentPadding literalP (7, 1) (1, 1) = (-2978719 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_4 : literalDescent (7, 1) (2, 0) = (2593673 / 1250000000) := rfl
@[simp] theorem lookup_previous_15_4 : previousPadding literalP (7, 1) (2, 0) = (27980893 / 10000000000) := rfl
@[simp] theorem lookup_current_15_4 : currentPadding literalP (7, 1) (2, 0) = (7231509 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_5 : literalDescent (7, 1) (2, 1) = (8212547 / 10000000000) := rfl
@[simp] theorem lookup_previous_15_5 : previousPadding literalP (7, 1) (2, 1) = (34141273 / 10000000000) := rfl
@[simp] theorem lookup_current_15_5 : currentPadding literalP (7, 1) (2, 1) = (12964363 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_6 : literalDescent (7, 1) (3, 0) = (-8024187 / 2500000000) := rfl
@[simp] theorem lookup_previous_15_6 : previousPadding literalP (7, 1) (3, 0) = (-25599987 / 2000000000) := rfl
@[simp] theorem lookup_current_15_6 : currentPadding literalP (7, 1) (3, 0) = (-95903187 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_7 : literalDescent (7, 1) (3, 1) = (-4663093 / 5000000000) := rfl
@[simp] theorem lookup_previous_15_7 : previousPadding literalP (7, 1) (3, 1) = (-25604807 / 10000000000) := rfl
@[simp] theorem lookup_current_15_7 : currentPadding literalP (7, 1) (3, 1) = (-16278621 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_8 : literalDescent (7, 1) (4, 0) = (145087 / 10000000000) := rfl
@[simp] theorem lookup_previous_15_8 : previousPadding literalP (7, 1) (4, 0) = (-2203431 / 5000000000) := rfl
@[simp] theorem lookup_current_15_8 : currentPadding literalP (7, 1) (4, 0) = (-4551949 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_9 : literalDescent (7, 1) (4, 1) = (278003 / 500000000) := rfl
@[simp] theorem lookup_previous_15_9 : previousPadding literalP (7, 1) (4, 1) = (424399 / 1000000000) := rfl
@[simp] theorem lookup_current_15_9 : currentPadding literalP (7, 1) (4, 1) = (-131607 / 1000000000) := rfl
@[simp] theorem lookup_descent_15_10 : literalDescent (7, 1) (5, 0) = (4184541 / 625000000) := rfl
@[simp] theorem lookup_previous_15_10 : previousPadding literalP (7, 1) (5, 0) = (65389217 / 2500000000) := rfl
@[simp] theorem lookup_current_15_10 : currentPadding literalP (7, 1) (5, 0) = (48651053 / 2500000000) := rfl
@[simp] theorem lookup_descent_15_11 : literalDescent (7, 1) (5, 1) = (-8993809 / 10000000000) := rfl
@[simp] theorem lookup_previous_15_11 : previousPadding literalP (7, 1) (5, 1) = (-22009653 / 10000000000) := rfl
@[simp] theorem lookup_current_15_11 : currentPadding literalP (7, 1) (5, 1) = (-3253961 / 2500000000) := rfl
@[simp] theorem lookup_descent_15_12 : literalDescent (7, 1) (6, 0) = (-2570923591 / 500000000000) := rfl
@[simp] theorem lookup_previous_15_12 : previousPadding literalP (7, 1) (6, 0) = (-73523157 / 5000000000) := rfl
@[simp] theorem lookup_current_15_12 : currentPadding literalP (7, 1) (6, 0) = (-47815269 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_13 : literalDescent (7, 1) (6, 1) = (-7103582697 / 4000000000000) := rfl
@[simp] theorem lookup_previous_15_13 : previousPadding literalP (7, 1) (6, 1) = (-3470413 / 625000000) := rfl
@[simp] theorem lookup_current_15_13 : currentPadding literalP (7, 1) (6, 1) = (-7553901 / 2000000000) := rfl
@[simp] theorem lookup_descent_15_14 : literalDescent (7, 1) (7, 0) = (49233621 / 20000000000) := rfl
@[simp] theorem lookup_previous_15_14 : previousPadding literalP (7, 1) (7, 0) = (28587251 / 10000000000) := rfl
@[simp] theorem lookup_current_15_14 : currentPadding literalP (7, 1) (7, 0) = (-2370357 / 2500000000) := rfl
@[simp] theorem lookup_descent_15_15 : literalDescent (7, 1) (7, 1) = (13784470073 / 4000000000000) := rfl
@[simp] theorem lookup_previous_15_15 : previousPadding literalP (7, 1) (7, 1) = (42401832641 / 4000000000000) := rfl
@[simp] theorem lookup_current_15_15 : currentPadding literalP (7, 1) (7, 1) = (16276218981 / 2000000000000) := rfl
@[simp] theorem lookup_descent_15_16 : literalDescent (7, 1) (8, 0) = (-8414527 / 10000000000) := rfl
@[simp] theorem lookup_previous_15_16 : previousPadding literalP (7, 1) (8, 0) = (-10809193 / 10000000000) := rfl
@[simp] theorem lookup_current_15_16 : currentPadding literalP (7, 1) (8, 0) = (-228993 / 312500000) := rfl
@[simp] theorem lookup_descent_15_17 : literalDescent (7, 1) (8, 1) = (-233612453 / 200000000000) := rfl
@[simp] theorem lookup_previous_15_17 : previousPadding literalP (7, 1) (8, 1) = (-7553901 / 2000000000) := rfl
@[simp] theorem lookup_current_15_17 : currentPadding literalP (7, 1) (8, 1) = (-2665619 / 1000000000) := rfl
@[simp] theorem lookup_descent_15_18 : literalDescent (7, 1) (9, 0) = (-6729343 / 10000000000) := rfl
@[simp] theorem lookup_previous_15_18 : previousPadding literalP (7, 1) (9, 0) = (-6729343 / 10000000000) := rfl
@[simp] theorem lookup_current_15_18 : currentPadding literalP (7, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_15_19 : literalDescent (7, 1) (9, 1) = (-400891 / 10000000000) := rfl
@[simp] theorem lookup_previous_15_19 : previousPadding literalP (7, 1) (9, 1) = (-400891 / 10000000000) := rfl
@[simp] theorem lookup_current_15_19 : currentPadding literalP (7, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_16_0 : literalDescent (8, 0) (0, 0) = (233761 / 400000000) := rfl
@[simp] theorem lookup_previous_16_0 : previousPadding literalP (8, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_16_0 : currentPadding literalP (8, 0) (0, 0) = (-17742321 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_1 : literalDescent (8, 0) (0, 1) = (-272417 / 500000000) := rfl
@[simp] theorem lookup_previous_16_1 : previousPadding literalP (8, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_16_1 : currentPadding literalP (8, 0) (0, 1) = (-1612477 / 2500000000) := rfl
@[simp] theorem lookup_descent_16_2 : literalDescent (8, 0) (1, 0) = (16742321 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_2 : previousPadding literalP (8, 0) (1, 0) = (1705631 / 2500000000) := rfl
@[simp] theorem lookup_current_16_2 : currentPadding literalP (8, 0) (1, 0) = (-631519 / 2500000000) := rfl
@[simp] theorem lookup_descent_16_3 : literalDescent (8, 0) (1, 1) = (1652724079 / 2000000000000) := rfl
@[simp] theorem lookup_previous_16_3 : previousPadding literalP (8, 0) (1, 1) = (9579093 / 10000000000) := rfl
@[simp] theorem lookup_current_16_3 : currentPadding literalP (8, 0) (1, 1) = (-723353 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_4 : literalDescent (8, 0) (2, 0) = (-21748521 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_4 : previousPadding literalP (8, 0) (2, 0) = (13866017 / 5000000000) := rfl
@[simp] theorem lookup_current_16_4 : currentPadding literalP (8, 0) (2, 0) = (9896111 / 2000000000) := rfl
@[simp] theorem lookup_descent_16_5 : literalDescent (8, 0) (2, 1) = (-752433 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_5 : previousPadding literalP (8, 0) (2, 1) = (156171 / 2500000000) := rfl
@[simp] theorem lookup_current_16_5 : currentPadding literalP (8, 0) (2, 1) = (1377117 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_6 : literalDescent (8, 0) (3, 0) = (-9437591 / 2500000000) := rfl
@[simp] theorem lookup_previous_16_6 : previousPadding literalP (8, 0) (3, 0) = (-20883431 / 2500000000) := rfl
@[simp] theorem lookup_current_16_6 : currentPadding literalP (8, 0) (3, 0) = (-143073 / 31250000) := rfl
@[simp] theorem lookup_descent_16_7 : literalDescent (8, 0) (3, 1) = (-938131 / 1250000000) := rfl
@[simp] theorem lookup_previous_16_7 : previousPadding literalP (8, 0) (3, 1) = (-8202753 / 2500000000) := rfl
@[simp] theorem lookup_current_16_7 : currentPadding literalP (8, 0) (3, 1) = (-6326491 / 2500000000) := rfl
@[simp] theorem lookup_descent_16_8 : literalDescent (8, 0) (4, 0) = (3708419 / 1000000000) := rfl
@[simp] theorem lookup_previous_16_8 : previousPadding literalP (8, 0) (4, 0) = (98234413 / 10000000000) := rfl
@[simp] theorem lookup_current_16_8 : currentPadding literalP (8, 0) (4, 0) = (61150223 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_9 : literalDescent (8, 0) (4, 1) = (370415297 / 500000000000) := rfl
@[simp] theorem lookup_previous_16_9 : previousPadding literalP (8, 0) (4, 1) = (2378702147 / 500000000000) := rfl
@[simp] theorem lookup_current_16_9 : currentPadding literalP (8, 0) (4, 1) = (40165737 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_10 : literalDescent (8, 0) (5, 0) = (6654663 / 2500000000) := rfl
@[simp] theorem lookup_previous_16_10 : previousPadding literalP (8, 0) (5, 0) = (1178591 / 5000000000) := rfl
@[simp] theorem lookup_current_16_10 : currentPadding literalP (8, 0) (5, 0) = (-2426147 / 1000000000) := rfl
@[simp] theorem lookup_descent_16_11 : literalDescent (8, 0) (5, 1) = (786023 / 2500000000) := rfl
@[simp] theorem lookup_previous_16_11 : previousPadding literalP (8, 0) (5, 1) = (741347 / 500000000) := rfl
@[simp] theorem lookup_current_16_11 : currentPadding literalP (8, 0) (5, 1) = (365089 / 312500000) := rfl
@[simp] theorem lookup_descent_16_12 : literalDescent (8, 0) (6, 0) = (-5995921 / 5000000000) := rfl
@[simp] theorem lookup_previous_16_12 : previousPadding literalP (8, 0) (6, 0) = (-94127187 / 10000000000) := rfl
@[simp] theorem lookup_current_16_12 : currentPadding literalP (8, 0) (6, 0) = (-16427069 / 2000000000) := rfl
@[simp] theorem lookup_descent_16_13 : literalDescent (8, 0) (6, 1) = (-6831851 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_13 : previousPadding literalP (8, 0) (6, 1) = (-6780597 / 5000000000) := rfl
@[simp] theorem lookup_current_16_13 : currentPadding literalP (8, 0) (6, 1) = (-6729343 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_14 : literalDescent (8, 0) (7, 0) = (-6261507 / 1250000000) := rfl
@[simp] theorem lookup_previous_16_14 : previousPadding literalP (8, 0) (7, 0) = (-18431779 / 5000000000) := rfl
@[simp] theorem lookup_current_16_14 : currentPadding literalP (8, 0) (7, 0) = (2073847 / 2500000000) := rfl
@[simp] theorem lookup_descent_16_15 : literalDescent (8, 0) (7, 1) = (-8414527 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_15 : previousPadding literalP (8, 0) (7, 1) = (-10809193 / 10000000000) := rfl
@[simp] theorem lookup_current_16_15 : currentPadding literalP (8, 0) (7, 1) = (-228993 / 312500000) := rfl
@[simp] theorem lookup_descent_16_16 : literalDescent (8, 0) (8, 0) = (9108973 / 2500000000) := rfl
@[simp] theorem lookup_previous_16_16 : previousPadding literalP (8, 0) (8, 0) = (4442683 / 625000000) := rfl
@[simp] theorem lookup_current_16_16 : currentPadding literalP (8, 0) (8, 0) = (26761203 / 5000000000) := rfl
@[simp] theorem lookup_descent_16_17 : literalDescent (8, 0) (8, 1) = (10507777 / 5000000000) := rfl
@[simp] theorem lookup_previous_16_17 : previousPadding literalP (8, 0) (8, 1) = (-2370357 / 2500000000) := rfl
@[simp] theorem lookup_current_16_17 : currentPadding literalP (8, 0) (8, 1) = (-3344679 / 5000000000) := rfl
@[simp] theorem lookup_descent_16_18 : literalDescent (8, 0) (9, 0) = (-1142297 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_18 : previousPadding literalP (8, 0) (9, 0) = (2073847 / 2500000000) := rfl
@[simp] theorem lookup_current_16_18 : currentPadding literalP (8, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_16_19 : literalDescent (8, 0) (9, 1) = (-2175874667 / 2000000000000) := rfl
@[simp] theorem lookup_previous_16_19 : previousPadding literalP (8, 0) (9, 1) = (-4896641 / 5000000000) := rfl
@[simp] theorem lookup_current_16_19 : currentPadding literalP (8, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_17_0 : literalDescent (8, 1) (0, 0) = (-418016227 / 1000000000000) := rfl
@[simp] theorem lookup_previous_17_0 : previousPadding literalP (8, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_17_0 : currentPadding literalP (8, 1) (0, 0) = (3634641 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_1 : literalDescent (8, 1) (0, 1) = (-65692707 / 200000000000) := rfl
@[simp] theorem lookup_previous_17_1 : previousPadding literalP (8, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_17_1 : currentPadding literalP (8, 1) (0, 1) = (-4478129 / 2500000000) := rfl
@[simp] theorem lookup_descent_17_2 : literalDescent (8, 1) (1, 0) = (1995537 / 1000000000) := rfl
@[simp] theorem lookup_previous_17_2 : previousPadding literalP (8, 1) (1, 0) = (3385001 / 1250000000) := rfl
@[simp] theorem lookup_current_17_2 : currentPadding literalP (8, 1) (1, 0) = (7259151 / 5000000000) := rfl
@[simp] theorem lookup_descent_17_3 : literalDescent (8, 1) (1, 1) = (1041684971 / 1000000000000) := rfl
@[simp] theorem lookup_previous_17_3 : previousPadding literalP (8, 1) (1, 1) = (745663 / 2500000000) := rfl
@[simp] theorem lookup_current_17_3 : currentPadding literalP (8, 1) (1, 1) = (-174103 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_4 : literalDescent (8, 1) (2, 0) = (-22340419 / 10000000000) := rfl
@[simp] theorem lookup_previous_17_4 : previousPadding literalP (8, 1) (2, 0) = (-16020851 / 10000000000) := rfl
@[simp] theorem lookup_current_17_4 : currentPadding literalP (8, 1) (2, 0) = (394973 / 625000000) := rfl
@[simp] theorem lookup_descent_17_5 : literalDescent (8, 1) (2, 1) = (-1253 / 16000000) := rfl
@[simp] theorem lookup_previous_17_5 : previousPadding literalP (8, 1) (2, 1) = (-2978719 / 5000000000) := rfl
@[simp] theorem lookup_current_17_5 : currentPadding literalP (8, 1) (2, 1) = (-5174313 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_6 : literalDescent (8, 1) (3, 0) = (-17603637 / 10000000000) := rfl
@[simp] theorem lookup_previous_17_6 : previousPadding literalP (8, 1) (3, 0) = (7231509 / 10000000000) := rfl
@[simp] theorem lookup_current_17_6 : currentPadding literalP (8, 1) (3, 0) = (12417573 / 5000000000) := rfl
@[simp] theorem lookup_descent_17_7 : literalDescent (8, 1) (3, 1) = (2569977 / 2000000000) := rfl
@[simp] theorem lookup_previous_17_7 : previousPadding literalP (8, 1) (3, 1) = (12964363 / 5000000000) := rfl
@[simp] theorem lookup_current_17_7 : currentPadding literalP (8, 1) (3, 1) = (13078841 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_8 : literalDescent (8, 1) (4, 0) = (-11915681 / 2500000000) := rfl
@[simp] theorem lookup_previous_17_8 : previousPadding literalP (8, 1) (4, 0) = (-95903187 / 10000000000) := rfl
@[simp] theorem lookup_current_17_8 : currentPadding literalP (8, 1) (4, 0) = (-48240463 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_9 : literalDescent (8, 1) (4, 1) = (-8777049 / 5000000000) := rfl
@[simp] theorem lookup_previous_17_9 : previousPadding literalP (8, 1) (4, 1) = (-16278621 / 10000000000) := rfl
@[simp] theorem lookup_current_17_9 : currentPadding literalP (8, 1) (4, 1) = (1275477 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_10 : literalDescent (8, 1) (5, 0) = (23709477 / 5000000000) := rfl
@[simp] theorem lookup_previous_17_10 : previousPadding literalP (8, 1) (5, 0) = (-4551949 / 10000000000) := rfl
@[simp] theorem lookup_current_17_10 : currentPadding literalP (8, 1) (5, 0) = (-51970903 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_11 : literalDescent (8, 1) (5, 1) = (-1103883 / 1250000000) := rfl
@[simp] theorem lookup_previous_17_11 : previousPadding literalP (8, 1) (5, 1) = (-131607 / 1000000000) := rfl
@[simp] theorem lookup_current_17_11 : currentPadding literalP (8, 1) (5, 1) = (3757497 / 5000000000) := rfl
@[simp] theorem lookup_descent_17_12 : literalDescent (8, 1) (6, 0) = (127217863 / 10000000000) := rfl
@[simp] theorem lookup_previous_17_12 : previousPadding literalP (8, 1) (6, 0) = (48651053 / 2500000000) := rfl
@[simp] theorem lookup_current_17_12 : currentPadding literalP (8, 1) (6, 0) = (67386349 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_13 : literalDescent (8, 1) (6, 1) = (-12614953 / 10000000000) := rfl
@[simp] theorem lookup_previous_17_13 : previousPadding literalP (8, 1) (6, 1) = (-3253961 / 2500000000) := rfl
@[simp] theorem lookup_current_17_13 : currentPadding literalP (8, 1) (6, 1) = (-400891 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_14 : literalDescent (8, 1) (7, 0) = (-10705533773 / 1000000000000) := rfl
@[simp] theorem lookup_previous_17_14 : previousPadding literalP (8, 1) (7, 0) = (-47815269 / 5000000000) := rfl
@[simp] theorem lookup_current_17_14 : currentPadding literalP (8, 1) (7, 0) = (-4896641 / 5000000000) := rfl
@[simp] theorem lookup_descent_17_15 : literalDescent (8, 1) (7, 1) = (-233612453 / 200000000000) := rfl
@[simp] theorem lookup_previous_17_15 : previousPadding literalP (8, 1) (7, 1) = (-7553901 / 2000000000) := rfl
@[simp] theorem lookup_current_17_15 : currentPadding literalP (8, 1) (7, 1) = (-2665619 / 1000000000) := rfl
@[simp] theorem lookup_descent_17_16 : literalDescent (8, 1) (8, 0) = (10507777 / 5000000000) := rfl
@[simp] theorem lookup_previous_17_16 : previousPadding literalP (8, 1) (8, 0) = (-2370357 / 2500000000) := rfl
@[simp] theorem lookup_current_17_16 : currentPadding literalP (8, 1) (8, 0) = (-3344679 / 5000000000) := rfl
@[simp] theorem lookup_descent_17_17 : literalDescent (8, 1) (8, 1) = (11844657413 / 2000000000000) := rfl
@[simp] theorem lookup_previous_17_17 : previousPadding literalP (8, 1) (8, 1) = (16276218981 / 2000000000000) := rfl
@[simp] theorem lookup_current_17_17 : currentPadding literalP (8, 1) (8, 1) = (1615078657 / 500000000000) := rfl
@[simp] theorem lookup_descent_17_18 : literalDescent (8, 1) (9, 0) = (-16765461 / 10000000000) := rfl
@[simp] theorem lookup_previous_17_18 : previousPadding literalP (8, 1) (9, 0) = (-228993 / 312500000) := rfl
@[simp] theorem lookup_current_17_18 : currentPadding literalP (8, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_17_19 : literalDescent (8, 1) (9, 1) = (-1109660951 / 400000000000) := rfl
@[simp] theorem lookup_previous_17_19 : previousPadding literalP (8, 1) (9, 1) = (-2665619 / 1000000000) := rfl
@[simp] theorem lookup_current_17_19 : currentPadding literalP (8, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_0 : literalDescent (9, 0) (0, 0) = (1887537 / 2000000000) := rfl
@[simp] theorem lookup_previous_18_0 : previousPadding literalP (9, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_18_0 : currentPadding literalP (9, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_1 : literalDescent (9, 0) (0, 1) = (1887537 / 2000000000) := rfl
@[simp] theorem lookup_previous_18_1 : previousPadding literalP (9, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_18_1 : currentPadding literalP (9, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_2 : literalDescent (9, 0) (1, 0) = (-17742321 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_2 : previousPadding literalP (9, 0) (1, 0) = (-17742321 / 10000000000) := rfl
@[simp] theorem lookup_current_18_2 : currentPadding literalP (9, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_3 : literalDescent (9, 0) (1, 1) = (-15887593 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_3 : previousPadding literalP (9, 0) (1, 1) = (-1612477 / 2500000000) := rfl
@[simp] theorem lookup_current_18_3 : currentPadding literalP (9, 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_4 : literalDescent (9, 0) (2, 0) = (-631519 / 2500000000) := rfl
@[simp] theorem lookup_previous_18_4 : previousPadding literalP (9, 0) (2, 0) = (-631519 / 2500000000) := rfl
@[simp] theorem lookup_current_18_4 : currentPadding literalP (9, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_5 : literalDescent (9, 0) (2, 1) = (-723353 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_5 : previousPadding literalP (9, 0) (2, 1) = (-723353 / 10000000000) := rfl
@[simp] theorem lookup_current_18_5 : currentPadding literalP (9, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_6 : literalDescent (9, 0) (3, 0) = (9896111 / 2000000000) := rfl
@[simp] theorem lookup_previous_18_6 : previousPadding literalP (9, 0) (3, 0) = (9896111 / 2000000000) := rfl
@[simp] theorem lookup_current_18_6 : currentPadding literalP (9, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_7 : literalDescent (9, 0) (3, 1) = (1377117 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_7 : previousPadding literalP (9, 0) (3, 1) = (1377117 / 10000000000) := rfl
@[simp] theorem lookup_current_18_7 : currentPadding literalP (9, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_8 : literalDescent (9, 0) (4, 0) = (-143073 / 31250000) := rfl
@[simp] theorem lookup_previous_18_8 : previousPadding literalP (9, 0) (4, 0) = (-143073 / 31250000) := rfl
@[simp] theorem lookup_current_18_8 : currentPadding literalP (9, 0) (4, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_9 : literalDescent (9, 0) (4, 1) = (-6326491 / 2500000000) := rfl
@[simp] theorem lookup_previous_18_9 : previousPadding literalP (9, 0) (4, 1) = (-6326491 / 2500000000) := rfl
@[simp] theorem lookup_current_18_9 : currentPadding literalP (9, 0) (4, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_10 : literalDescent (9, 0) (5, 0) = (61150223 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_10 : previousPadding literalP (9, 0) (5, 0) = (61150223 / 10000000000) := rfl
@[simp] theorem lookup_current_18_10 : currentPadding literalP (9, 0) (5, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_11 : literalDescent (9, 0) (5, 1) = (40165737 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_11 : previousPadding literalP (9, 0) (5, 1) = (40165737 / 10000000000) := rfl
@[simp] theorem lookup_current_18_11 : currentPadding literalP (9, 0) (5, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_12 : literalDescent (9, 0) (6, 0) = (-2426147 / 1000000000) := rfl
@[simp] theorem lookup_previous_18_12 : previousPadding literalP (9, 0) (6, 0) = (-2426147 / 1000000000) := rfl
@[simp] theorem lookup_current_18_12 : currentPadding literalP (9, 0) (6, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_13 : literalDescent (9, 0) (6, 1) = (365089 / 312500000) := rfl
@[simp] theorem lookup_previous_18_13 : previousPadding literalP (9, 0) (6, 1) = (365089 / 312500000) := rfl
@[simp] theorem lookup_current_18_13 : currentPadding literalP (9, 0) (6, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_14 : literalDescent (9, 0) (7, 0) = (-16427069 / 2000000000) := rfl
@[simp] theorem lookup_previous_18_14 : previousPadding literalP (9, 0) (7, 0) = (-16427069 / 2000000000) := rfl
@[simp] theorem lookup_current_18_14 : currentPadding literalP (9, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_15 : literalDescent (9, 0) (7, 1) = (-6729343 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_15 : previousPadding literalP (9, 0) (7, 1) = (-6729343 / 10000000000) := rfl
@[simp] theorem lookup_current_18_15 : currentPadding literalP (9, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_16 : literalDescent (9, 0) (8, 0) = (-1142297 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_16 : previousPadding literalP (9, 0) (8, 0) = (2073847 / 2500000000) := rfl
@[simp] theorem lookup_current_18_16 : currentPadding literalP (9, 0) (8, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_17 : literalDescent (9, 0) (8, 1) = (-16765461 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_17 : previousPadding literalP (9, 0) (8, 1) = (-228993 / 312500000) := rfl
@[simp] theorem lookup_current_18_17 : currentPadding literalP (9, 0) (8, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_18 : literalDescent (9, 0) (9, 0) = (26761203 / 5000000000) := rfl
@[simp] theorem lookup_previous_18_18 : previousPadding literalP (9, 0) (9, 0) = (26761203 / 5000000000) := rfl
@[simp] theorem lookup_current_18_18 : currentPadding literalP (9, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_19 : literalDescent (9, 0) (9, 1) = (2748327 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_19 : previousPadding literalP (9, 0) (9, 1) = (-3344679 / 5000000000) := rfl
@[simp] theorem lookup_current_18_19 : currentPadding literalP (9, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_0 : literalDescent (9, 1) (0, 0) = (-191574533 / 2000000000000) := rfl
@[simp] theorem lookup_previous_19_0 : previousPadding literalP (9, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_19_0 : currentPadding literalP (9, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_1 : literalDescent (9, 1) (0, 1) = (-38345209 / 400000000000) := rfl
@[simp] theorem lookup_previous_19_1 : previousPadding literalP (9, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_19_1 : currentPadding literalP (9, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_2 : literalDescent (9, 1) (1, 0) = (-93977 / 250000000) := rfl
@[simp] theorem lookup_previous_19_2 : previousPadding literalP (9, 1) (1, 0) = (3634641 / 10000000000) := rfl
@[simp] theorem lookup_current_19_2 : currentPadding literalP (9, 1) (1, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_3 : literalDescent (9, 1) (1, 1) = (-301672169 / 1000000000000) := rfl
@[simp] theorem lookup_previous_19_3 : previousPadding literalP (9, 1) (1, 1) = (-4478129 / 2500000000) := rfl
@[simp] theorem lookup_current_19_3 : currentPadding literalP (9, 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_4 : literalDescent (9, 1) (2, 0) = (7259151 / 5000000000) := rfl
@[simp] theorem lookup_previous_19_4 : previousPadding literalP (9, 1) (2, 0) = (7259151 / 5000000000) := rfl
@[simp] theorem lookup_current_19_4 : currentPadding literalP (9, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_5 : literalDescent (9, 1) (2, 1) = (-174103 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_5 : previousPadding literalP (9, 1) (2, 1) = (-174103 / 10000000000) := rfl
@[simp] theorem lookup_current_19_5 : currentPadding literalP (9, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_6 : literalDescent (9, 1) (3, 0) = (394973 / 625000000) := rfl
@[simp] theorem lookup_previous_19_6 : previousPadding literalP (9, 1) (3, 0) = (394973 / 625000000) := rfl
@[simp] theorem lookup_current_19_6 : currentPadding literalP (9, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_7 : literalDescent (9, 1) (3, 1) = (-5174313 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_7 : previousPadding literalP (9, 1) (3, 1) = (-5174313 / 10000000000) := rfl
@[simp] theorem lookup_current_19_7 : currentPadding literalP (9, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_8 : literalDescent (9, 1) (4, 0) = (12417573 / 5000000000) := rfl
@[simp] theorem lookup_previous_19_8 : previousPadding literalP (9, 1) (4, 0) = (12417573 / 5000000000) := rfl
@[simp] theorem lookup_current_19_8 : currentPadding literalP (9, 1) (4, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_9 : literalDescent (9, 1) (4, 1) = (13078841 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_9 : previousPadding literalP (9, 1) (4, 1) = (13078841 / 10000000000) := rfl
@[simp] theorem lookup_current_19_9 : currentPadding literalP (9, 1) (4, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_10 : literalDescent (9, 1) (5, 0) = (-48240463 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_10 : previousPadding literalP (9, 1) (5, 0) = (-48240463 / 10000000000) := rfl
@[simp] theorem lookup_current_19_10 : currentPadding literalP (9, 1) (5, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_11 : literalDescent (9, 1) (5, 1) = (1275477 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_11 : previousPadding literalP (9, 1) (5, 1) = (1275477 / 10000000000) := rfl
@[simp] theorem lookup_current_19_11 : currentPadding literalP (9, 1) (5, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_12 : literalDescent (9, 1) (6, 0) = (-51970903 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_12 : previousPadding literalP (9, 1) (6, 0) = (-51970903 / 10000000000) := rfl
@[simp] theorem lookup_current_19_12 : currentPadding literalP (9, 1) (6, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_13 : literalDescent (9, 1) (6, 1) = (3757497 / 5000000000) := rfl
@[simp] theorem lookup_previous_19_13 : previousPadding literalP (9, 1) (6, 1) = (3757497 / 5000000000) := rfl
@[simp] theorem lookup_current_19_13 : currentPadding literalP (9, 1) (6, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_14 : literalDescent (9, 1) (7, 0) = (67386349 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_14 : previousPadding literalP (9, 1) (7, 0) = (67386349 / 10000000000) := rfl
@[simp] theorem lookup_current_19_14 : currentPadding literalP (9, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_15 : literalDescent (9, 1) (7, 1) = (-400891 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_15 : previousPadding literalP (9, 1) (7, 1) = (-400891 / 10000000000) := rfl
@[simp] theorem lookup_current_19_15 : currentPadding literalP (9, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_16 : literalDescent (9, 1) (8, 0) = (-2175874667 / 2000000000000) := rfl
@[simp] theorem lookup_previous_19_16 : previousPadding literalP (9, 1) (8, 0) = (-4896641 / 5000000000) := rfl
@[simp] theorem lookup_current_19_16 : currentPadding literalP (9, 1) (8, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_17 : literalDescent (9, 1) (8, 1) = (-1109660951 / 400000000000) := rfl
@[simp] theorem lookup_previous_19_17 : previousPadding literalP (9, 1) (8, 1) = (-2665619 / 1000000000) := rfl
@[simp] theorem lookup_current_19_17 : currentPadding literalP (9, 1) (8, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_18 : literalDescent (9, 1) (9, 0) = (2748327 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_18 : previousPadding literalP (9, 1) (9, 0) = (-3344679 / 5000000000) := rfl
@[simp] theorem lookup_current_19_18 : currentPadding literalP (9, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_19 : literalDescent (9, 1) (9, 1) = (1559687069 / 1000000000000) := rfl
@[simp] theorem lookup_previous_19_19 : previousPadding literalP (9, 1) (9, 1) = (1615078657 / 500000000000) := rfl
@[simp] theorem lookup_current_19_19 : currentPadding literalP (9, 1) (9, 1) = 0 := rfl

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Upper.MatrixBridge
