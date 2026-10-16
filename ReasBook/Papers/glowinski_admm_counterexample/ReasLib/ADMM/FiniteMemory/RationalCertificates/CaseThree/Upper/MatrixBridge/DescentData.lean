module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Upper.MatrixBridge.Lookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixDescent

@[expose] public section
set_option maxRecDepth 4096
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.MatrixBridge
open MatrixAssembly

-- These candidates become certificates only through the subsequent Lean proofs.
def literalDescentData : List (List ℚ) := [
  [(9177683 / 5000000000), (30078329 / 60000000000), (-1638793 / 500000000), (-76579589 / 75000000000), (-20991371 / 20000000000), (789992021 / 1500000000000), (4186237 / 800000000), (19934297 / 125000000000), (-41558817 / 20000000000), (-723530193 / 500000000000), (7184263 / 20000000000), (52016533 / 31250000000), (-2531581 / 2500000000), (3130629 / 125000000000), (-14438377 / 10000000000), (-7674837 / 62500000000), (2596341 / 5000000000), (-24718453 / 125000000000), (9147513 / 10000000000), (-44174353 / 500000000000)],
  [(30078329 / 60000000000), (160215273 / 250000000000), (-486490757 / 250000000000), (-77551087 / 125000000000), (-4731163 / 12000000000), (-2464639 / 10000000000), (2020820139 / 500000000000), (87875689 / 500000000000), (-20724103 / 10000000000), (-99155713 / 100000000000), (8014933 / 10000000000), (585318937 / 500000000000), (118271 / 20000000000), (24641457 / 500000000000), (-29303481 / 20000000000), (34092427 / 250000000000), (-7745859 / 20000000000), (-113038573 / 500000000000), (9147513 / 10000000000), (-44198047 / 500000000000)],
  [(-1638793 / 500000000), (-486490757 / 250000000000), (106579047 / 10000000000), (353019351 / 125000000000), (-3645547 / 2000000000), (-508237667 / 500000000000), (-323197091 / 20000000000), (4353293 / 7812500000), (100337397 / 10000000000), (64684911 / 20000000000), (-2801751 / 4000000000), (-103318071 / 20000000000), (40168437 / 20000000000), (2142083 / 2500000000), (-3126711 / 10000000000), (-10258293 / 20000000000), (5052613 / 4000000000), (31750081 / 20000000000), (-8449483 / 5000000000), (-8374051 / 20000000000)],
  [(-76579589 / 75000000000), (-77551087 / 125000000000), (353019351 / 125000000000), (722344921 / 500000000000), (-580744139 / 375000000000), (-3118601 / 7812500000), (-1245269191 / 250000000000), (-228199803 / 500000000000), (1459960829 / 250000000000), (434951 / 400000000), (-153170061 / 125000000000), (-20319797 / 10000000000), (118622537 / 500000000000), (228280233 / 500000000000), (23829057 / 31250000000), (-5497253 / 500000000000), (405227427 / 500000000000), (45271837 / 50000000000), (-1061299 / 625000000), (-46887639 / 125000000000)],
  [(-20991371 / 20000000000), (-4731163 / 12000000000), (-3645547 / 2000000000), (-580744139 / 375000000000), (67886217 / 5000000000), (703250681 / 300000000000), (-97407771 / 20000000000), (-900115213 / 500000000000), (-132626917 / 10000000000), (279669641 / 100000000000), (57363421 / 10000000000), (5220089 / 2500000000), (-36401319 / 10000000000), (-40776583 / 10000000000), (19273403 / 2500000000), (3987261 / 2500000000), (-28141411 / 10000000000), (-30500963 / 10000000000), (2183743 / 5000000000), (20470943 / 10000000000)],
  [(789992021 / 1500000000000), (-2464639 / 10000000000), (-508237667 / 500000000000), (-3118601 / 7812500000), (703250681 / 300000000000), (716899603 / 500000000000), (-37795499 / 20000000000), (-249758189 / 500000000000), (-758293 / 250000000), (-1712479 / 5000000000), (9988391 / 2500000000), (1851903 / 5000000000), (-1721729 / 2500000000), (-9333933 / 10000000000), (-846131 / 5000000000), (8201799 / 10000000000), (-216261 / 2500000000), (-436073 / 2000000000), (88289 / 5000000000), (147271 / 10000000000)],
  [(4186237 / 800000000), (2020820139 / 500000000000), (-323197091 / 20000000000), (-1245269191 / 250000000000), (-97407771 / 20000000000), (-37795499 / 20000000000), (82850627 / 2000000000), (1595222843 / 500000000000), (-354959661 / 20000000000), (-3945616407 / 500000000000), (-73920867 / 5000000000), (618332979 / 62500000000), (354953 / 40000000), (6894833 / 2500000000), (-10816011 / 2500000000), (-10065821 / 2000000000), (-6136147 / 2500000000), (-1301519 / 2000000000), (75177 / 15625000), (5624077 / 10000000000)],
  [(19934297 / 125000000000), (87875689 / 500000000000), (4353293 / 7812500000), (-228199803 / 500000000000), (-900115213 / 500000000000), (-249758189 / 500000000000), (1595222843 / 500000000000), (520991469 / 250000000000), (-15298693 / 4000000000), (-132974287 / 100000000000), (-1025087 / 1000000000), (-286833 / 2000000000), (15623841 / 2500000000), (892851 / 5000000000), (-401709279 / 100000000000), (-1968693 / 2000000000), (149869 / 2500000000), (17539569 / 10000000000), (4504579 / 10000000000), (-311529 / 400000000)],
  [(-41558817 / 20000000000), (-20724103 / 10000000000), (100337397 / 10000000000), (1459960829 / 250000000000), (-132626917 / 10000000000), (-758293 / 250000000), (-354959661 / 20000000000), (-15298693 / 4000000000), (122558029 / 2500000000), (146882979 / 20000000000), (-51461671 / 2500000000), (-124359479 / 12500000000), (-118903137 / 5000000000), (451990619 / 62500000000), (44383001 / 2000000000), (1477499 / 1000000000), (161077 / 80000000), (-17267 / 3125000), (-58080029 / 10000000000), (25111127 / 10000000000)],
  [(-723530193 / 500000000000), (-99155713 / 100000000000), (64684911 / 20000000000), (434951 / 400000000), (279669641 / 100000000000), (-1712479 / 5000000000), (-3945616407 / 500000000000), (-132974287 / 100000000000), (146882979 / 20000000000), (567232603 / 125000000000), (-28518929 / 5000000000), (-592954781 / 250000000000), (-66965541 / 10000000000), (-1213993 / 2500000000), (106364901 / 10000000000), (555111 / 1250000000), (-10199761 / 100000000000), (-4174011 / 2000000000), (-21709503 / 10000000000), (3077781 / 2000000000)],
  [(7184263 / 20000000000), (8014933 / 10000000000), (-2801751 / 4000000000), (-153170061 / 125000000000), (57363421 / 10000000000), (9988391 / 2500000000), (-73920867 / 5000000000), (-1025087 / 1000000000), (-51461671 / 2500000000), (-28518929 / 5000000000), (254495849 / 5000000000), (51977781 / 20000000000), (4783079 / 1000000000), (-1858963859 / 250000000000), (-167163191 / 5000000000), (3845579287 / 500000000000), (13057689 / 5000000000), (29970653 / 5000000000), (51125759 / 10000000000), (-3556837 / 625000000)],
  [(52016533 / 31250000000), (585318937 / 500000000000), (-103318071 / 20000000000), (-20319797 / 10000000000), (5220089 / 2500000000), (1851903 / 5000000000), (618332979 / 62500000000), (-286833 / 2000000000), (-124359479 / 12500000000), (-592954781 / 250000000000), (51977781 / 20000000000), (2557290657 / 500000000000), (2280301 / 5000000000), (-97092041 / 250000000000), (-23064697 / 5000000000), (-12710103 / 10000000000), (-4732193 / 10000000000), (-8384667 / 10000000000), (3499979 / 1000000000), (3894607 / 10000000000)],
  [(-2531581 / 2500000000), (118271 / 20000000000), (40168437 / 20000000000), (118622537 / 500000000000), (-36401319 / 10000000000), (-1721729 / 2500000000), (354953 / 40000000), (15623841 / 2500000000), (-118903137 / 5000000000), (-66965541 / 10000000000), (4783079 / 1000000000), (2280301 / 5000000000), (76707903 / 2000000000), (-42746263 / 20000000000), (-525525547 / 20000000000), (-1273043483 / 250000000000), (25440649 / 10000000000), (6820855629 / 500000000000), (-4634183 / 2500000000), (-59757337 / 10000000000)],
  [(3130629 / 125000000000), (24641457 / 500000000000), (2142083 / 2500000000), (228280233 / 500000000000), (-40776583 / 10000000000), (-9333933 / 10000000000), (6894833 / 2500000000), (892851 / 5000000000), (451990619 / 62500000000), (-1213993 / 2500000000), (-1858963859 / 250000000000), (-97092041 / 250000000000), (-42746263 / 20000000000), (1630328721 / 500000000000), (56736899 / 20000000000), (-656519229 / 500000000000), (-3816111 / 5000000000), (-897981 / 500000000), (1763857 / 2500000000), (9712881 / 10000000000)],
  [(-14438377 / 10000000000), (-29303481 / 20000000000), (-3126711 / 10000000000), (23829057 / 31250000000), (19273403 / 2500000000), (-846131 / 5000000000), (-10816011 / 2500000000), (-401709279 / 100000000000), (44383001 / 2000000000), (106364901 / 10000000000), (-167163191 / 5000000000), (-23064697 / 5000000000), (-525525547 / 20000000000), (56736899 / 20000000000), (59469337 / 1250000000), (19317647 / 20000000000), (-116448353 / 20000000000), (-815225399 / 62500000000), (-58620849 / 10000000000), (20265729 / 2500000000)],
  [(-7674837 / 62500000000), (34092427 / 250000000000), (-10258293 / 20000000000), (-5497253 / 500000000000), (3987261 / 2500000000), (8201799 / 10000000000), (-10065821 / 2000000000), (-1968693 / 2000000000), (1477499 / 1000000000), (555111 / 1250000000), (3845579287 / 500000000000), (-12710103 / 10000000000), (-1273043483 / 250000000000), (-656519229 / 500000000000), (19317647 / 20000000000), (341356021 / 100000000000), (-11445547 / 20000000000), (-493049427 / 500000000000), (-792741 / 2000000000), (-24871 / 100000000)],
  [(2596341 / 5000000000), (-7745859 / 20000000000), (5052613 / 4000000000), (405227427 / 500000000000), (-28141411 / 10000000000), (-216261 / 2500000000), (-6136147 / 2500000000), (149869 / 2500000000), (161077 / 80000000), (-10199761 / 100000000000), (13057689 / 5000000000), (-4732193 / 10000000000), (25440649 / 10000000000), (-3816111 / 5000000000), (-116448353 / 20000000000), (-11445547 / 20000000000), (31156923 / 10000000000), (7798469 / 2500000000), (-4880807 / 5000000000), (-401319061 / 250000000000)],
  [(-24718453 / 125000000000), (-113038573 / 500000000000), (31750081 / 20000000000), (45271837 / 50000000000), (-30500963 / 10000000000), (-436073 / 2000000000), (-1301519 / 2000000000), (17539569 / 10000000000), (-17267 / 3125000), (-4174011 / 2000000000), (29970653 / 5000000000), (-8384667 / 10000000000), (6820855629 / 500000000000), (-897981 / 500000000), (-815225399 / 62500000000), (-493049427 / 500000000000), (7798469 / 2500000000), (217983863 / 31250000000), (-18750837 / 10000000000), (-870807639 / 250000000000)],
  [(9147513 / 10000000000), (9147513 / 10000000000), (-8449483 / 5000000000), (-1061299 / 625000000), (2183743 / 5000000000), (88289 / 5000000000), (75177 / 15625000), (4504579 / 10000000000), (-58080029 / 10000000000), (-21709503 / 10000000000), (51125759 / 10000000000), (3499979 / 1000000000), (-4634183 / 2500000000), (1763857 / 2500000000), (-58620849 / 10000000000), (-792741 / 2000000000), (-4880807 / 5000000000), (-18750837 / 10000000000), (6143019 / 1250000000), (5520941 / 10000000000)],
  [(-44174353 / 500000000000), (-44198047 / 500000000000), (-8374051 / 20000000000), (-46887639 / 125000000000), (20470943 / 10000000000), (147271 / 10000000000), (5624077 / 10000000000), (-311529 / 400000000), (25111127 / 10000000000), (3077781 / 2000000000), (-3556837 / 625000000), (3894607 / 10000000000), (-59757337 / 10000000000), (9712881 / 10000000000), (20265729 / 2500000000), (-24871 / 100000000), (-401319061 / 250000000000), (-870807639 / 250000000000), (5520941 / 10000000000), (1029946931 / 500000000000)]
]
def literalDescent : Matrix (Fin 10 × Fin 2) (Fin 10 × Fin 2) ℚ := readFlat literalDescentData
@[simp] theorem lookup_descent_0_0 : literalDescent (0, 0) (0, 0) = (9177683 / 5000000000) := rfl
@[simp] theorem lookup_previous_0_0 : previousPadding literalP (0, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_0_0 : currentPadding literalP (0, 0) (0, 0) = (52008611 / 400000000) := rfl
@[simp] theorem lookup_descent_0_1 : literalDescent (0, 0) (0, 1) = (30078329 / 60000000000) := rfl
@[simp] theorem lookup_previous_0_1 : previousPadding literalP (0, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_0_1 : currentPadding literalP (0, 0) (0, 1) = (1266767 / 625000000) := rfl
@[simp] theorem lookup_descent_0_2 : literalDescent (0, 0) (1, 0) = (-1638793 / 500000000) := rfl
@[simp] theorem lookup_previous_0_2 : previousPadding literalP (0, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_current_0_2 : currentPadding literalP (0, 0) (1, 0) = (-313254757 / 5000000000) := rfl
@[simp] theorem lookup_descent_0_3 : literalDescent (0, 0) (1, 1) = (-76579589 / 75000000000) := rfl
@[simp] theorem lookup_previous_0_3 : previousPadding literalP (0, 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_current_0_3 : currentPadding literalP (0, 0) (1, 1) = (177460931291 / 1500000000000) := rfl
@[simp] theorem lookup_descent_0_4 : literalDescent (0, 0) (2, 0) = (-20991371 / 20000000000) := rfl
@[simp] theorem lookup_previous_0_4 : previousPadding literalP (0, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_current_0_4 : currentPadding literalP (0, 0) (2, 0) = (-261845017 / 2500000000) := rfl
@[simp] theorem lookup_descent_0_5 : literalDescent (0, 0) (2, 1) = (789992021 / 1500000000000) := rfl
@[simp] theorem lookup_previous_0_5 : previousPadding literalP (0, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_current_0_5 : currentPadding literalP (0, 0) (2, 1) = (52006018157 / 500000000000) := rfl
@[simp] theorem lookup_descent_0_6 : literalDescent (0, 0) (3, 0) = (4186237 / 800000000) := rfl
@[simp] theorem lookup_previous_0_6 : previousPadding literalP (0, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_current_0_6 : currentPadding literalP (0, 0) (3, 0) = (387565431 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_7 : literalDescent (0, 0) (3, 1) = (19934297 / 125000000000) := rfl
@[simp] theorem lookup_previous_0_7 : previousPadding literalP (0, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_current_0_7 : currentPadding literalP (0, 0) (3, 1) = (739383 / 1000000000) := rfl
@[simp] theorem lookup_descent_0_8 : literalDescent (0, 0) (4, 0) = (-41558817 / 20000000000) := rfl
@[simp] theorem lookup_previous_0_8 : previousPadding literalP (0, 0) (4, 0) = 0 := rfl
@[simp] theorem lookup_current_0_8 : currentPadding literalP (0, 0) (4, 0) = (-1926173 / 1250000000) := rfl
@[simp] theorem lookup_descent_0_9 : literalDescent (0, 0) (4, 1) = (-723530193 / 500000000000) := rfl
@[simp] theorem lookup_previous_0_9 : previousPadding literalP (0, 0) (4, 1) = 0 := rfl
@[simp] theorem lookup_current_0_9 : currentPadding literalP (0, 0) (4, 1) = (-33312251 / 2000000000) := rfl
@[simp] theorem lookup_descent_0_10 : literalDescent (0, 0) (5, 0) = (7184263 / 20000000000) := rfl
@[simp] theorem lookup_previous_0_10 : previousPadding literalP (0, 0) (5, 0) = 0 := rfl
@[simp] theorem lookup_current_0_10 : currentPadding literalP (0, 0) (5, 0) = (392181 / 625000000) := rfl
@[simp] theorem lookup_descent_0_11 : literalDescent (0, 0) (5, 1) = (52016533 / 31250000000) := rfl
@[simp] theorem lookup_previous_0_11 : previousPadding literalP (0, 0) (5, 1) = 0 := rfl
@[simp] theorem lookup_current_0_11 : currentPadding literalP (0, 0) (5, 1) = (17421309 / 5000000000) := rfl
@[simp] theorem lookup_descent_0_12 : literalDescent (0, 0) (6, 0) = (-2531581 / 2500000000) := rfl
@[simp] theorem lookup_previous_0_12 : previousPadding literalP (0, 0) (6, 0) = 0 := rfl
@[simp] theorem lookup_current_0_12 : currentPadding literalP (0, 0) (6, 0) = (16845107 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_13 : literalDescent (0, 0) (6, 1) = (3130629 / 125000000000) := rfl
@[simp] theorem lookup_previous_0_13 : previousPadding literalP (0, 0) (6, 1) = 0 := rfl
@[simp] theorem lookup_current_0_13 : currentPadding literalP (0, 0) (6, 1) = (-10863883 / 5000000000) := rfl
@[simp] theorem lookup_descent_0_14 : literalDescent (0, 0) (7, 0) = (-14438377 / 10000000000) := rfl
@[simp] theorem lookup_previous_0_14 : previousPadding literalP (0, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_current_0_14 : currentPadding literalP (0, 0) (7, 0) = (614573 / 625000000) := rfl
@[simp] theorem lookup_descent_0_15 : literalDescent (0, 0) (7, 1) = (-7674837 / 62500000000) := rfl
@[simp] theorem lookup_previous_0_15 : previousPadding literalP (0, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_current_0_15 : currentPadding literalP (0, 0) (7, 1) = (3647523 / 1250000000) := rfl
@[simp] theorem lookup_descent_0_16 : literalDescent (0, 0) (8, 0) = (2596341 / 5000000000) := rfl
@[simp] theorem lookup_previous_0_16 : previousPadding literalP (0, 0) (8, 0) = 0 := rfl
@[simp] theorem lookup_current_0_16 : currentPadding literalP (0, 0) (8, 0) = (-8449483 / 5000000000) := rfl
@[simp] theorem lookup_descent_0_17 : literalDescent (0, 0) (8, 1) = (-24718453 / 125000000000) := rfl
@[simp] theorem lookup_previous_0_17 : previousPadding literalP (0, 0) (8, 1) = 0 := rfl
@[simp] theorem lookup_current_0_17 : currentPadding literalP (0, 0) (8, 1) = (119153 / 400000000) := rfl
@[simp] theorem lookup_descent_0_18 : literalDescent (0, 0) (9, 0) = (9147513 / 10000000000) := rfl
@[simp] theorem lookup_previous_0_18 : previousPadding literalP (0, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_current_0_18 : currentPadding literalP (0, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_0_19 : literalDescent (0, 0) (9, 1) = (-44174353 / 500000000000) := rfl
@[simp] theorem lookup_previous_0_19 : previousPadding literalP (0, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_current_0_19 : currentPadding literalP (0, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_1_0 : literalDescent (0, 1) (0, 0) = (30078329 / 60000000000) := rfl
@[simp] theorem lookup_previous_1_0 : previousPadding literalP (0, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_1_0 : currentPadding literalP (0, 1) (0, 0) = (1266767 / 625000000) := rfl
@[simp] theorem lookup_descent_1_1 : literalDescent (0, 1) (0, 1) = (160215273 / 250000000000) := rfl
@[simp] theorem lookup_previous_1_1 : previousPadding literalP (0, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_1_1 : currentPadding literalP (0, 1) (0, 1) = (511782043 / 3906250000) := rfl
@[simp] theorem lookup_descent_1_2 : literalDescent (0, 1) (1, 0) = (-486490757 / 250000000000) := rfl
@[simp] theorem lookup_previous_1_2 : previousPadding literalP (0, 1) (1, 0) = 0 := rfl
@[simp] theorem lookup_current_1_2 : currentPadding literalP (0, 1) (1, 0) = (-31990750611 / 500000000000) := rfl
@[simp] theorem lookup_descent_1_3 : literalDescent (0, 1) (1, 1) = (-77551087 / 125000000000) := rfl
@[simp] theorem lookup_previous_1_3 : previousPadding literalP (0, 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_current_1_3 : currentPadding literalP (0, 1) (1, 1) = (-14182041 / 2000000000) := rfl
@[simp] theorem lookup_descent_1_4 : literalDescent (0, 1) (2, 0) = (-4731163 / 12000000000) := rfl
@[simp] theorem lookup_previous_1_4 : previousPadding literalP (0, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_current_1_4 : currentPadding literalP (0, 1) (2, 0) = (112404541 / 5000000000) := rfl
@[simp] theorem lookup_descent_1_5 : literalDescent (0, 1) (2, 1) = (-2464639 / 10000000000) := rfl
@[simp] theorem lookup_previous_1_5 : previousPadding literalP (0, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_current_1_5 : currentPadding literalP (0, 1) (2, 1) = (-1055411169 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_6 : literalDescent (0, 1) (3, 0) = (2020820139 / 500000000000) := rfl
@[simp] theorem lookup_previous_1_6 : previousPadding literalP (0, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_current_1_6 : currentPadding literalP (0, 1) (3, 0) = (19973856411 / 500000000000) := rfl
@[simp] theorem lookup_descent_1_7 : literalDescent (0, 1) (3, 1) = (87875689 / 500000000000) := rfl
@[simp] theorem lookup_previous_1_7 : previousPadding literalP (0, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_current_1_7 : currentPadding literalP (0, 1) (3, 1) = (1807571 / 2500000000) := rfl
@[simp] theorem lookup_descent_1_8 : literalDescent (0, 1) (4, 0) = (-20724103 / 10000000000) := rfl
@[simp] theorem lookup_previous_1_8 : previousPadding literalP (0, 1) (4, 0) = 0 := rfl
@[simp] theorem lookup_current_1_8 : currentPadding literalP (0, 1) (4, 0) = (-15464601 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_9 : literalDescent (0, 1) (4, 1) = (-99155713 / 100000000000) := rfl
@[simp] theorem lookup_previous_1_9 : previousPadding literalP (0, 1) (4, 1) = 0 := rfl
@[simp] theorem lookup_current_1_9 : currentPadding literalP (0, 1) (4, 1) = (-85558501 / 5000000000) := rfl
@[simp] theorem lookup_descent_1_10 : literalDescent (0, 1) (5, 0) = (8014933 / 10000000000) := rfl
@[simp] theorem lookup_previous_1_10 : previousPadding literalP (0, 1) (5, 0) = 0 := rfl
@[simp] theorem lookup_current_1_10 : currentPadding literalP (0, 1) (5, 0) = (926073 / 5000000000) := rfl
@[simp] theorem lookup_descent_1_11 : literalDescent (0, 1) (5, 1) = (585318937 / 500000000000) := rfl
@[simp] theorem lookup_previous_1_11 : previousPadding literalP (0, 1) (5, 1) = 0 := rfl
@[simp] theorem lookup_current_1_11 : currentPadding literalP (0, 1) (5, 1) = (310779 / 78125000) := rfl
@[simp] theorem lookup_descent_1_12 : literalDescent (0, 1) (6, 0) = (118271 / 20000000000) := rfl
@[simp] theorem lookup_previous_1_12 : previousPadding literalP (0, 1) (6, 0) = 0 := rfl
@[simp] theorem lookup_current_1_12 : currentPadding literalP (0, 1) (6, 0) = (832461 / 1250000000) := rfl
@[simp] theorem lookup_descent_1_13 : literalDescent (0, 1) (6, 1) = (24641457 / 500000000000) := rfl
@[simp] theorem lookup_previous_1_13 : previousPadding literalP (0, 1) (6, 1) = 0 := rfl
@[simp] theorem lookup_current_1_13 : currentPadding literalP (0, 1) (6, 1) = (-1098609 / 500000000) := rfl
@[simp] theorem lookup_descent_1_14 : literalDescent (0, 1) (7, 0) = (-29303481 / 20000000000) := rfl
@[simp] theorem lookup_previous_1_14 : previousPadding literalP (0, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_current_1_14 : currentPadding literalP (0, 1) (7, 0) = (1255821 / 1250000000) := rfl
@[simp] theorem lookup_descent_1_15 : literalDescent (0, 1) (7, 1) = (34092427 / 250000000000) := rfl
@[simp] theorem lookup_previous_1_15 : previousPadding literalP (0, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_current_1_15 : currentPadding literalP (0, 1) (7, 1) = (2305799 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_16 : literalDescent (0, 1) (8, 0) = (-7745859 / 20000000000) := rfl
@[simp] theorem lookup_previous_1_16 : previousPadding literalP (0, 1) (8, 0) = 0 := rfl
@[simp] theorem lookup_current_1_16 : currentPadding literalP (0, 1) (8, 0) = (-7833271 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_17 : literalDescent (0, 1) (8, 1) = (-113038573 / 500000000000) := rfl
@[simp] theorem lookup_previous_1_17 : previousPadding literalP (0, 1) (8, 1) = 0 := rfl
@[simp] theorem lookup_current_1_17 : currentPadding literalP (0, 1) (8, 1) = (-18106771 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_18 : literalDescent (0, 1) (9, 0) = (9147513 / 10000000000) := rfl
@[simp] theorem lookup_previous_1_18 : previousPadding literalP (0, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_current_1_18 : currentPadding literalP (0, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_1_19 : literalDescent (0, 1) (9, 1) = (-44198047 / 500000000000) := rfl
@[simp] theorem lookup_previous_1_19 : previousPadding literalP (0, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_current_1_19 : currentPadding literalP (0, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_2_0 : literalDescent (1, 0) (0, 0) = (-1638793 / 500000000) := rfl
@[simp] theorem lookup_previous_2_0 : previousPadding literalP (1, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_2_0 : currentPadding literalP (1, 0) (0, 0) = (-313254757 / 5000000000) := rfl
@[simp] theorem lookup_descent_2_1 : literalDescent (1, 0) (0, 1) = (-486490757 / 250000000000) := rfl
@[simp] theorem lookup_previous_2_1 : previousPadding literalP (1, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_2_1 : currentPadding literalP (1, 0) (0, 1) = (-31990750611 / 500000000000) := rfl
@[simp] theorem lookup_descent_2_2 : literalDescent (1, 0) (1, 0) = (106579047 / 10000000000) := rfl
@[simp] theorem lookup_previous_2_2 : previousPadding literalP (1, 0) (1, 0) = (52008611 / 400000000) := rfl
@[simp] theorem lookup_current_2_2 : currentPadding literalP (1, 0) (1, 0) = (238727267 / 2000000000) := rfl
@[simp] theorem lookup_descent_2_3 : literalDescent (1, 0) (1, 1) = (353019351 / 125000000000) := rfl
@[simp] theorem lookup_previous_2_3 : previousPadding literalP (1, 0) (1, 1) = (1266767 / 625000000) := rfl
@[simp] theorem lookup_current_2_3 : currentPadding literalP (1, 0) (1, 1) = (-260812432391 / 1500000000000) := rfl
@[simp] theorem lookup_descent_2_4 : literalDescent (1, 0) (2, 0) = (-3645547 / 2000000000) := rfl
@[simp] theorem lookup_previous_2_4 : previousPadding literalP (1, 0) (2, 0) = (-313254757 / 5000000000) := rfl
@[simp] theorem lookup_current_2_4 : currentPadding literalP (1, 0) (2, 0) = (-67344007 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_5 : literalDescent (1, 0) (2, 1) = (-508237667 / 500000000000) := rfl
@[simp] theorem lookup_previous_2_5 : previousPadding literalP (1, 0) (2, 1) = (177460931291 / 1500000000000) := rfl
@[simp] theorem lookup_current_2_5 : currentPadding literalP (1, 0) (2, 1) = (-92271799 / 2500000000) := rfl
@[simp] theorem lookup_descent_2_6 : literalDescent (1, 0) (3, 0) = (-323197091 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_6 : previousPadding literalP (1, 0) (3, 0) = (-261845017 / 2500000000) := rfl
@[simp] theorem lookup_current_2_6 : currentPadding literalP (1, 0) (3, 0) = (-885781507 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_7 : literalDescent (1, 0) (3, 1) = (4353293 / 7812500000) := rfl
@[simp] theorem lookup_previous_2_7 : previousPadding literalP (1, 0) (3, 1) = (52006018157 / 500000000000) := rfl
@[simp] theorem lookup_current_2_7 : currentPadding literalP (1, 0) (3, 1) = (4936103541 / 100000000000) := rfl
@[simp] theorem lookup_descent_2_8 : literalDescent (1, 0) (4, 0) = (100337397 / 10000000000) := rfl
@[simp] theorem lookup_previous_2_8 : previousPadding literalP (1, 0) (4, 0) = (387565431 / 10000000000) := rfl
@[simp] theorem lookup_current_2_8 : currentPadding literalP (1, 0) (4, 0) = (187797661 / 5000000000) := rfl
@[simp] theorem lookup_descent_2_9 : literalDescent (1, 0) (4, 1) = (64684911 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_9 : previousPadding literalP (1, 0) (4, 1) = (739383 / 1000000000) := rfl
@[simp] theorem lookup_current_2_9 : currentPadding literalP (1, 0) (4, 1) = (63418647 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_10 : literalDescent (1, 0) (5, 0) = (-2801751 / 4000000000) := rfl
@[simp] theorem lookup_previous_2_10 : previousPadding literalP (1, 0) (5, 0) = (-1926173 / 1250000000) := rfl
@[simp] theorem lookup_current_2_10 : currentPadding literalP (1, 0) (5, 0) = (-8404979 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_11 : literalDescent (1, 0) (5, 1) = (-103318071 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_11 : previousPadding literalP (1, 0) (5, 1) = (-33312251 / 2000000000) := rfl
@[simp] theorem lookup_current_2_11 : currentPadding literalP (1, 0) (5, 1) = (-5081737 / 250000000) := rfl
@[simp] theorem lookup_descent_2_12 : literalDescent (1, 0) (6, 0) = (40168437 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_12 : previousPadding literalP (1, 0) (6, 0) = (392181 / 625000000) := rfl
@[simp] theorem lookup_current_2_12 : currentPadding literalP (1, 0) (6, 0) = (-1106201 / 2000000000) := rfl
@[simp] theorem lookup_descent_2_13 : literalDescent (1, 0) (6, 1) = (2142083 / 2500000000) := rfl
@[simp] theorem lookup_previous_2_13 : previousPadding literalP (1, 0) (6, 1) = (17421309 / 5000000000) := rfl
@[simp] theorem lookup_current_2_13 : currentPadding literalP (1, 0) (6, 1) = (134971 / 39062500) := rfl
@[simp] theorem lookup_descent_2_14 : literalDescent (1, 0) (7, 0) = (-3126711 / 10000000000) := rfl
@[simp] theorem lookup_previous_2_14 : previousPadding literalP (1, 0) (7, 0) = (16845107 / 10000000000) := rfl
@[simp] theorem lookup_current_2_14 : currentPadding literalP (1, 0) (7, 0) = (19971869 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_15 : literalDescent (1, 0) (7, 1) = (-10258293 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_15 : previousPadding literalP (1, 0) (7, 1) = (-10863883 / 5000000000) := rfl
@[simp] theorem lookup_current_2_15 : currentPadding literalP (1, 0) (7, 1) = (-12438443 / 5000000000) := rfl
@[simp] theorem lookup_descent_2_16 : literalDescent (1, 0) (8, 0) = (5052613 / 4000000000) := rfl
@[simp] theorem lookup_previous_2_16 : previousPadding literalP (1, 0) (8, 0) = (614573 / 625000000) := rfl
@[simp] theorem lookup_current_2_16 : currentPadding literalP (1, 0) (8, 0) = (2183743 / 5000000000) := rfl
@[simp] theorem lookup_descent_2_17 : literalDescent (1, 0) (8, 1) = (31750081 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_17 : previousPadding literalP (1, 0) (8, 1) = (3647523 / 1250000000) := rfl
@[simp] theorem lookup_current_2_17 : currentPadding literalP (1, 0) (8, 1) = (20470943 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_18 : literalDescent (1, 0) (9, 0) = (-8449483 / 5000000000) := rfl
@[simp] theorem lookup_previous_2_18 : previousPadding literalP (1, 0) (9, 0) = (-8449483 / 5000000000) := rfl
@[simp] theorem lookup_current_2_18 : currentPadding literalP (1, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_2_19 : literalDescent (1, 0) (9, 1) = (-8374051 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_19 : previousPadding literalP (1, 0) (9, 1) = (119153 / 400000000) := rfl
@[simp] theorem lookup_current_2_19 : currentPadding literalP (1, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_3_0 : literalDescent (1, 1) (0, 0) = (-76579589 / 75000000000) := rfl
@[simp] theorem lookup_previous_3_0 : previousPadding literalP (1, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_3_0 : currentPadding literalP (1, 1) (0, 0) = (177460931291 / 1500000000000) := rfl
@[simp] theorem lookup_descent_3_1 : literalDescent (1, 1) (0, 1) = (-77551087 / 125000000000) := rfl
@[simp] theorem lookup_previous_3_1 : previousPadding literalP (1, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_3_1 : currentPadding literalP (1, 1) (0, 1) = (-14182041 / 2000000000) := rfl
@[simp] theorem lookup_descent_3_2 : literalDescent (1, 1) (1, 0) = (353019351 / 125000000000) := rfl
@[simp] theorem lookup_previous_3_2 : previousPadding literalP (1, 1) (1, 0) = (1266767 / 625000000) := rfl
@[simp] theorem lookup_current_3_2 : currentPadding literalP (1, 1) (1, 0) = (-260812432391 / 1500000000000) := rfl
@[simp] theorem lookup_descent_3_3 : literalDescent (1, 1) (1, 1) = (722344921 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_3 : previousPadding literalP (1, 1) (1, 1) = (511782043 / 3906250000) := rfl
@[simp] theorem lookup_current_3_3 : currentPadding literalP (1, 1) (1, 1) = (6668654471 / 500000000000) := rfl
@[simp] theorem lookup_descent_3_4 : literalDescent (1, 1) (2, 0) = (-580744139 / 375000000000) := rfl
@[simp] theorem lookup_previous_3_4 : previousPadding literalP (1, 1) (2, 0) = (-31990750611 / 500000000000) := rfl
@[simp] theorem lookup_current_3_4 : currentPadding literalP (1, 1) (2, 0) = (135469317 / 2500000000) := rfl
@[simp] theorem lookup_descent_3_5 : literalDescent (1, 1) (2, 1) = (-3118601 / 7812500000) := rfl
@[simp] theorem lookup_previous_3_5 : previousPadding literalP (1, 1) (2, 1) = (-14182041 / 2000000000) := rfl
@[simp] theorem lookup_current_3_5 : currentPadding literalP (1, 1) (2, 1) = (-6501411 / 2500000000) := rfl
@[simp] theorem lookup_descent_3_6 : literalDescent (1, 1) (3, 0) = (-1245269191 / 250000000000) := rfl
@[simp] theorem lookup_previous_3_6 : previousPadding literalP (1, 1) (3, 0) = (112404541 / 5000000000) := rfl
@[simp] theorem lookup_current_3_6 : currentPadding literalP (1, 1) (3, 0) = (-41318363 / 2500000000) := rfl
@[simp] theorem lookup_descent_3_7 : literalDescent (1, 1) (3, 1) = (-228199803 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_7 : previousPadding literalP (1, 1) (3, 1) = (-1055411169 / 10000000000) := rfl
@[simp] theorem lookup_current_3_7 : currentPadding literalP (1, 1) (3, 1) = (-21435959 / 5000000000) := rfl
@[simp] theorem lookup_descent_3_8 : literalDescent (1, 1) (4, 0) = (1459960829 / 250000000000) := rfl
@[simp] theorem lookup_previous_3_8 : previousPadding literalP (1, 1) (4, 0) = (19973856411 / 500000000000) := rfl
@[simp] theorem lookup_current_3_8 : currentPadding literalP (1, 1) (4, 0) = (26392133 / 1250000000) := rfl
@[simp] theorem lookup_descent_3_9 : literalDescent (1, 1) (4, 1) = (434951 / 400000000) := rfl
@[simp] theorem lookup_previous_3_9 : previousPadding literalP (1, 1) (4, 1) = (1807571 / 2500000000) := rfl
@[simp] theorem lookup_current_3_9 : currentPadding literalP (1, 1) (4, 1) = (1125861 / 1000000000) := rfl
@[simp] theorem lookup_descent_3_10 : literalDescent (1, 1) (5, 0) = (-153170061 / 125000000000) := rfl
@[simp] theorem lookup_previous_3_10 : previousPadding literalP (1, 1) (5, 0) = (-15464601 / 10000000000) := rfl
@[simp] theorem lookup_current_3_10 : currentPadding literalP (1, 1) (5, 0) = (-1307803 / 1000000000) := rfl
@[simp] theorem lookup_descent_3_11 : literalDescent (1, 1) (5, 1) = (-20319797 / 10000000000) := rfl
@[simp] theorem lookup_previous_3_11 : previousPadding literalP (1, 1) (5, 1) = (-85558501 / 5000000000) := rfl
@[simp] theorem lookup_current_3_11 : currentPadding literalP (1, 1) (5, 1) = (-18076423 / 5000000000) := rfl
@[simp] theorem lookup_descent_3_12 : literalDescent (1, 1) (6, 0) = (118622537 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_12 : previousPadding literalP (1, 1) (6, 0) = (926073 / 5000000000) := rfl
@[simp] theorem lookup_current_3_12 : currentPadding literalP (1, 1) (6, 0) = (-22802289 / 10000000000) := rfl
@[simp] theorem lookup_descent_3_13 : literalDescent (1, 1) (6, 1) = (228280233 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_13 : previousPadding literalP (1, 1) (6, 1) = (310779 / 78125000) := rfl
@[simp] theorem lookup_current_3_13 : currentPadding literalP (1, 1) (6, 1) = (41130273 / 10000000000) := rfl
@[simp] theorem lookup_descent_3_14 : literalDescent (1, 1) (7, 0) = (23829057 / 31250000000) := rfl
@[simp] theorem lookup_previous_3_14 : previousPadding literalP (1, 1) (7, 0) = (832461 / 1250000000) := rfl
@[simp] theorem lookup_current_3_14 : currentPadding literalP (1, 1) (7, 0) = (727907 / 2000000000) := rfl
@[simp] theorem lookup_descent_3_15 : literalDescent (1, 1) (7, 1) = (-5497253 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_15 : previousPadding literalP (1, 1) (7, 1) = (-1098609 / 500000000) := rfl
@[simp] theorem lookup_current_3_15 : currentPadding literalP (1, 1) (7, 1) = (-996859 / 1000000000) := rfl
@[simp] theorem lookup_descent_3_16 : literalDescent (1, 1) (8, 0) = (405227427 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_16 : previousPadding literalP (1, 1) (8, 0) = (1255821 / 1250000000) := rfl
@[simp] theorem lookup_current_3_16 : currentPadding literalP (1, 1) (8, 0) = (88289 / 5000000000) := rfl
@[simp] theorem lookup_descent_3_17 : literalDescent (1, 1) (8, 1) = (45271837 / 50000000000) := rfl
@[simp] theorem lookup_previous_3_17 : previousPadding literalP (1, 1) (8, 1) = (2305799 / 10000000000) := rfl
@[simp] theorem lookup_current_3_17 : currentPadding literalP (1, 1) (8, 1) = (147271 / 10000000000) := rfl
@[simp] theorem lookup_descent_3_18 : literalDescent (1, 1) (9, 0) = (-1061299 / 625000000) := rfl
@[simp] theorem lookup_previous_3_18 : previousPadding literalP (1, 1) (9, 0) = (-7833271 / 10000000000) := rfl
@[simp] theorem lookup_current_3_18 : currentPadding literalP (1, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_3_19 : literalDescent (1, 1) (9, 1) = (-46887639 / 125000000000) := rfl
@[simp] theorem lookup_previous_3_19 : previousPadding literalP (1, 1) (9, 1) = (-18106771 / 10000000000) := rfl
@[simp] theorem lookup_current_3_19 : currentPadding literalP (1, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_4_0 : literalDescent (2, 0) (0, 0) = (-20991371 / 20000000000) := rfl
@[simp] theorem lookup_previous_4_0 : previousPadding literalP (2, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_4_0 : currentPadding literalP (2, 0) (0, 0) = (-261845017 / 2500000000) := rfl
@[simp] theorem lookup_descent_4_1 : literalDescent (2, 0) (0, 1) = (-4731163 / 12000000000) := rfl
@[simp] theorem lookup_previous_4_1 : previousPadding literalP (2, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_4_1 : currentPadding literalP (2, 0) (0, 1) = (112404541 / 5000000000) := rfl
@[simp] theorem lookup_descent_4_2 : literalDescent (2, 0) (1, 0) = (-3645547 / 2000000000) := rfl
@[simp] theorem lookup_previous_4_2 : previousPadding literalP (2, 0) (1, 0) = (-313254757 / 5000000000) := rfl
@[simp] theorem lookup_current_4_2 : currentPadding literalP (2, 0) (1, 0) = (-67344007 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_3 : literalDescent (2, 0) (1, 1) = (-580744139 / 375000000000) := rfl
@[simp] theorem lookup_previous_4_3 : previousPadding literalP (2, 0) (1, 1) = (-31990750611 / 500000000000) := rfl
@[simp] theorem lookup_current_4_3 : currentPadding literalP (2, 0) (1, 1) = (135469317 / 2500000000) := rfl
@[simp] theorem lookup_descent_4_4 : literalDescent (2, 0) (2, 0) = (67886217 / 5000000000) := rfl
@[simp] theorem lookup_previous_4_4 : previousPadding literalP (2, 0) (2, 0) = (238727267 / 2000000000) := rfl
@[simp] theorem lookup_current_4_4 : currentPadding literalP (2, 0) (2, 0) = (261467483 / 1250000000) := rfl
@[simp] theorem lookup_descent_4_5 : literalDescent (2, 0) (2, 1) = (703250681 / 300000000000) := rfl
@[simp] theorem lookup_previous_4_5 : previousPadding literalP (2, 0) (2, 1) = (-260812432391 / 1500000000000) := rfl
@[simp] theorem lookup_current_4_5 : currentPadding literalP (2, 0) (2, 1) = (-36415770457 / 500000000000) := rfl
@[simp] theorem lookup_descent_4_6 : literalDescent (2, 0) (3, 0) = (-97407771 / 20000000000) := rfl
@[simp] theorem lookup_previous_4_6 : previousPadding literalP (2, 0) (3, 0) = (-67344007 / 10000000000) := rfl
@[simp] theorem lookup_current_4_6 : currentPadding literalP (2, 0) (3, 0) = (-535578103 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_7 : literalDescent (2, 0) (3, 1) = (-900115213 / 500000000000) := rfl
@[simp] theorem lookup_previous_4_7 : previousPadding literalP (2, 0) (3, 1) = (-92271799 / 2500000000) := rfl
@[simp] theorem lookup_current_4_7 : currentPadding literalP (2, 0) (3, 1) = (-516397 / 12500000) := rfl
@[simp] theorem lookup_descent_4_8 : literalDescent (2, 0) (4, 0) = (-132626917 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_8 : previousPadding literalP (2, 0) (4, 0) = (-885781507 / 10000000000) := rfl
@[simp] theorem lookup_current_4_8 : currentPadding literalP (2, 0) (4, 0) = (-75315459 / 1000000000) := rfl
@[simp] theorem lookup_descent_4_9 : literalDescent (2, 0) (4, 1) = (279669641 / 100000000000) := rfl
@[simp] theorem lookup_previous_4_9 : previousPadding literalP (2, 0) (4, 1) = (4936103541 / 100000000000) := rfl
@[simp] theorem lookup_current_4_9 : currentPadding literalP (2, 0) (4, 1) = (46564339 / 1000000000) := rfl
@[simp] theorem lookup_descent_4_10 : literalDescent (2, 0) (5, 0) = (57363421 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_10 : previousPadding literalP (2, 0) (5, 0) = (187797661 / 5000000000) := rfl
@[simp] theorem lookup_current_4_10 : currentPadding literalP (2, 0) (5, 0) = (318231901 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_11 : literalDescent (2, 0) (5, 1) = (5220089 / 2500000000) := rfl
@[simp] theorem lookup_previous_4_11 : previousPadding literalP (2, 0) (5, 1) = (63418647 / 10000000000) := rfl
@[simp] theorem lookup_current_4_11 : currentPadding literalP (2, 0) (5, 1) = (42538291 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_12 : literalDescent (2, 0) (6, 0) = (-36401319 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_12 : previousPadding literalP (2, 0) (6, 0) = (-8404979 / 10000000000) := rfl
@[simp] theorem lookup_current_4_12 : currentPadding literalP (2, 0) (6, 0) = (1399817 / 500000000) := rfl
@[simp] theorem lookup_descent_4_13 : literalDescent (2, 0) (6, 1) = (-40776583 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_13 : previousPadding literalP (2, 0) (6, 1) = (-5081737 / 250000000) := rfl
@[simp] theorem lookup_current_4_13 : currentPadding literalP (2, 0) (6, 1) = (-162492897 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_14 : literalDescent (2, 0) (7, 0) = (19273403 / 2500000000) := rfl
@[simp] theorem lookup_previous_4_14 : previousPadding literalP (2, 0) (7, 0) = (-1106201 / 2000000000) := rfl
@[simp] theorem lookup_current_4_14 : currentPadding literalP (2, 0) (7, 0) = (-82624617 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_15 : literalDescent (2, 0) (7, 1) = (3987261 / 2500000000) := rfl
@[simp] theorem lookup_previous_4_15 : previousPadding literalP (2, 0) (7, 1) = (134971 / 39062500) := rfl
@[simp] theorem lookup_current_4_15 : currentPadding literalP (2, 0) (7, 1) = (4650883 / 2500000000) := rfl
@[simp] theorem lookup_descent_4_16 : literalDescent (2, 0) (8, 0) = (-28141411 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_16 : previousPadding literalP (2, 0) (8, 0) = (19971869 / 10000000000) := rfl
@[simp] theorem lookup_current_4_16 : currentPadding literalP (2, 0) (8, 0) = (75177 / 15625000) := rfl
@[simp] theorem lookup_descent_4_17 : literalDescent (2, 0) (8, 1) = (-30500963 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_17 : previousPadding literalP (2, 0) (8, 1) = (-12438443 / 5000000000) := rfl
@[simp] theorem lookup_current_4_17 : currentPadding literalP (2, 0) (8, 1) = (5624077 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_18 : literalDescent (2, 0) (9, 0) = (2183743 / 5000000000) := rfl
@[simp] theorem lookup_previous_4_18 : previousPadding literalP (2, 0) (9, 0) = (2183743 / 5000000000) := rfl
@[simp] theorem lookup_current_4_18 : currentPadding literalP (2, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_4_19 : literalDescent (2, 0) (9, 1) = (20470943 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_19 : previousPadding literalP (2, 0) (9, 1) = (20470943 / 10000000000) := rfl
@[simp] theorem lookup_current_4_19 : currentPadding literalP (2, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_5_0 : literalDescent (2, 1) (0, 0) = (789992021 / 1500000000000) := rfl
@[simp] theorem lookup_previous_5_0 : previousPadding literalP (2, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_5_0 : currentPadding literalP (2, 1) (0, 0) = (52006018157 / 500000000000) := rfl
@[simp] theorem lookup_descent_5_1 : literalDescent (2, 1) (0, 1) = (-2464639 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_1 : previousPadding literalP (2, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_5_1 : currentPadding literalP (2, 1) (0, 1) = (-1055411169 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_2 : literalDescent (2, 1) (1, 0) = (-508237667 / 500000000000) := rfl
@[simp] theorem lookup_previous_5_2 : previousPadding literalP (2, 1) (1, 0) = (177460931291 / 1500000000000) := rfl
@[simp] theorem lookup_current_5_2 : currentPadding literalP (2, 1) (1, 0) = (-92271799 / 2500000000) := rfl
@[simp] theorem lookup_descent_5_3 : literalDescent (2, 1) (1, 1) = (-3118601 / 7812500000) := rfl
@[simp] theorem lookup_previous_5_3 : previousPadding literalP (2, 1) (1, 1) = (-14182041 / 2000000000) := rfl
@[simp] theorem lookup_current_5_3 : currentPadding literalP (2, 1) (1, 1) = (-6501411 / 2500000000) := rfl
@[simp] theorem lookup_descent_5_4 : literalDescent (2, 1) (2, 0) = (703250681 / 300000000000) := rfl
@[simp] theorem lookup_previous_5_4 : previousPadding literalP (2, 1) (2, 0) = (-260812432391 / 1500000000000) := rfl
@[simp] theorem lookup_current_5_4 : currentPadding literalP (2, 1) (2, 0) = (-36415770457 / 500000000000) := rfl
@[simp] theorem lookup_descent_5_5 : literalDescent (2, 1) (2, 1) = (716899603 / 500000000000) := rfl
@[simp] theorem lookup_previous_5_5 : previousPadding literalP (2, 1) (2, 1) = (6668654471 / 500000000000) := rfl
@[simp] theorem lookup_current_5_5 : currentPadding literalP (2, 1) (2, 1) = (28822774859 / 250000000000) := rfl
@[simp] theorem lookup_descent_5_6 : literalDescent (2, 1) (3, 0) = (-37795499 / 20000000000) := rfl
@[simp] theorem lookup_previous_5_6 : previousPadding literalP (2, 1) (3, 0) = (135469317 / 2500000000) := rfl
@[simp] theorem lookup_current_5_6 : currentPadding literalP (2, 1) (3, 0) = (10959259 / 2500000000) := rfl
@[simp] theorem lookup_descent_5_7 : literalDescent (2, 1) (3, 1) = (-249758189 / 500000000000) := rfl
@[simp] theorem lookup_previous_5_7 : previousPadding literalP (2, 1) (3, 1) = (-6501411 / 2500000000) := rfl
@[simp] theorem lookup_current_5_7 : currentPadding literalP (2, 1) (3, 1) = (-41521519 / 5000000000) := rfl
@[simp] theorem lookup_descent_5_8 : literalDescent (2, 1) (4, 0) = (-758293 / 250000000) := rfl
@[simp] theorem lookup_previous_5_8 : previousPadding literalP (2, 1) (4, 0) = (-41318363 / 2500000000) := rfl
@[simp] theorem lookup_current_5_8 : currentPadding literalP (2, 1) (4, 0) = (-33735433 / 2500000000) := rfl
@[simp] theorem lookup_descent_5_9 : literalDescent (2, 1) (4, 1) = (-1712479 / 5000000000) := rfl
@[simp] theorem lookup_previous_5_9 : previousPadding literalP (2, 1) (4, 1) = (-21435959 / 5000000000) := rfl
@[simp] theorem lookup_current_5_9 : currentPadding literalP (2, 1) (4, 1) = (-493087 / 125000000) := rfl
@[simp] theorem lookup_descent_5_10 : literalDescent (2, 1) (5, 0) = (9988391 / 2500000000) := rfl
@[simp] theorem lookup_previous_5_10 : previousPadding literalP (2, 1) (5, 0) = (26392133 / 1250000000) := rfl
@[simp] theorem lookup_current_5_10 : currentPadding literalP (2, 1) (5, 0) = (342367 / 20000000) := rfl
@[simp] theorem lookup_descent_5_11 : literalDescent (2, 1) (5, 1) = (1851903 / 5000000000) := rfl
@[simp] theorem lookup_previous_5_11 : previousPadding literalP (2, 1) (5, 1) = (1125861 / 1000000000) := rfl
@[simp] theorem lookup_current_5_11 : currentPadding literalP (2, 1) (5, 1) = (1888701 / 2500000000) := rfl
@[simp] theorem lookup_descent_5_12 : literalDescent (2, 1) (6, 0) = (-1721729 / 2500000000) := rfl
@[simp] theorem lookup_previous_5_12 : previousPadding literalP (2, 1) (6, 0) = (-1307803 / 1000000000) := rfl
@[simp] theorem lookup_current_5_12 : currentPadding literalP (2, 1) (6, 0) = (-3095557 / 5000000000) := rfl
@[simp] theorem lookup_descent_5_13 : literalDescent (2, 1) (6, 1) = (-9333933 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_13 : previousPadding literalP (2, 1) (6, 1) = (-18076423 / 5000000000) := rfl
@[simp] theorem lookup_current_5_13 : currentPadding literalP (2, 1) (6, 1) = (-26818913 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_14 : literalDescent (2, 1) (7, 0) = (-846131 / 5000000000) := rfl
@[simp] theorem lookup_previous_5_14 : previousPadding literalP (2, 1) (7, 0) = (-22802289 / 10000000000) := rfl
@[simp] theorem lookup_current_5_14 : currentPadding literalP (2, 1) (7, 0) = (-21110027 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_15 : literalDescent (2, 1) (7, 1) = (8201799 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_15 : previousPadding literalP (2, 1) (7, 1) = (41130273 / 10000000000) := rfl
@[simp] theorem lookup_current_5_15 : currentPadding literalP (2, 1) (7, 1) = (16464237 / 5000000000) := rfl
@[simp] theorem lookup_descent_5_16 : literalDescent (2, 1) (8, 0) = (-216261 / 2500000000) := rfl
@[simp] theorem lookup_previous_5_16 : previousPadding literalP (2, 1) (8, 0) = (727907 / 2000000000) := rfl
@[simp] theorem lookup_current_5_16 : currentPadding literalP (2, 1) (8, 0) = (4504579 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_17 : literalDescent (2, 1) (8, 1) = (-436073 / 2000000000) := rfl
@[simp] theorem lookup_previous_5_17 : previousPadding literalP (2, 1) (8, 1) = (-996859 / 1000000000) := rfl
@[simp] theorem lookup_current_5_17 : currentPadding literalP (2, 1) (8, 1) = (-311529 / 400000000) := rfl
@[simp] theorem lookup_descent_5_18 : literalDescent (2, 1) (9, 0) = (88289 / 5000000000) := rfl
@[simp] theorem lookup_previous_5_18 : previousPadding literalP (2, 1) (9, 0) = (88289 / 5000000000) := rfl
@[simp] theorem lookup_current_5_18 : currentPadding literalP (2, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_5_19 : literalDescent (2, 1) (9, 1) = (147271 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_19 : previousPadding literalP (2, 1) (9, 1) = (147271 / 10000000000) := rfl
@[simp] theorem lookup_current_5_19 : currentPadding literalP (2, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_6_0 : literalDescent (3, 0) (0, 0) = (4186237 / 800000000) := rfl
@[simp] theorem lookup_previous_6_0 : previousPadding literalP (3, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_6_0 : currentPadding literalP (3, 0) (0, 0) = (387565431 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_1 : literalDescent (3, 0) (0, 1) = (2020820139 / 500000000000) := rfl
@[simp] theorem lookup_previous_6_1 : previousPadding literalP (3, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_6_1 : currentPadding literalP (3, 0) (0, 1) = (19973856411 / 500000000000) := rfl
@[simp] theorem lookup_descent_6_2 : literalDescent (3, 0) (1, 0) = (-323197091 / 20000000000) := rfl
@[simp] theorem lookup_previous_6_2 : previousPadding literalP (3, 0) (1, 0) = (-261845017 / 2500000000) := rfl
@[simp] theorem lookup_current_6_2 : currentPadding literalP (3, 0) (1, 0) = (-885781507 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_3 : literalDescent (3, 0) (1, 1) = (-1245269191 / 250000000000) := rfl
@[simp] theorem lookup_previous_6_3 : previousPadding literalP (3, 0) (1, 1) = (112404541 / 5000000000) := rfl
@[simp] theorem lookup_current_6_3 : currentPadding literalP (3, 0) (1, 1) = (-41318363 / 2500000000) := rfl
@[simp] theorem lookup_descent_6_4 : literalDescent (3, 0) (2, 0) = (-97407771 / 20000000000) := rfl
@[simp] theorem lookup_previous_6_4 : previousPadding literalP (3, 0) (2, 0) = (-67344007 / 10000000000) := rfl
@[simp] theorem lookup_current_6_4 : currentPadding literalP (3, 0) (2, 0) = (-535578103 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_5 : literalDescent (3, 0) (2, 1) = (-37795499 / 20000000000) := rfl
@[simp] theorem lookup_previous_6_5 : previousPadding literalP (3, 0) (2, 1) = (135469317 / 2500000000) := rfl
@[simp] theorem lookup_current_6_5 : currentPadding literalP (3, 0) (2, 1) = (10959259 / 2500000000) := rfl
@[simp] theorem lookup_descent_6_6 : literalDescent (3, 0) (3, 0) = (82850627 / 2000000000) := rfl
@[simp] theorem lookup_previous_6_6 : previousPadding literalP (3, 0) (3, 0) = (261467483 / 1250000000) := rfl
@[simp] theorem lookup_current_6_6 : currentPadding literalP (3, 0) (3, 0) = (915787937 / 5000000000) := rfl
@[simp] theorem lookup_descent_6_7 : literalDescent (3, 0) (3, 1) = (1595222843 / 500000000000) := rfl
@[simp] theorem lookup_previous_6_7 : previousPadding literalP (3, 0) (3, 1) = (-36415770457 / 500000000000) := rfl
@[simp] theorem lookup_current_6_7 : currentPadding literalP (3, 0) (3, 1) = (-17838673 / 2000000000) := rfl
@[simp] theorem lookup_descent_6_8 : literalDescent (3, 0) (4, 0) = (-354959661 / 20000000000) := rfl
@[simp] theorem lookup_previous_6_8 : previousPadding literalP (3, 0) (4, 0) = (-535578103 / 10000000000) := rfl
@[simp] theorem lookup_current_6_8 : currentPadding literalP (3, 0) (4, 0) = (-87028569 / 2000000000) := rfl
@[simp] theorem lookup_descent_6_9 : literalDescent (3, 0) (4, 1) = (-3945616407 / 500000000000) := rfl
@[simp] theorem lookup_previous_6_9 : previousPadding literalP (3, 0) (4, 1) = (-516397 / 12500000) := rfl
@[simp] theorem lookup_current_6_9 : currentPadding literalP (3, 0) (4, 1) = (-343451171 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_10 : literalDescent (3, 0) (5, 0) = (-73920867 / 5000000000) := rfl
@[simp] theorem lookup_previous_6_10 : previousPadding literalP (3, 0) (5, 0) = (-75315459 / 1000000000) := rfl
@[simp] theorem lookup_current_6_10 : currentPadding literalP (3, 0) (5, 0) = (-75664107 / 1250000000) := rfl
@[simp] theorem lookup_descent_6_11 : literalDescent (3, 0) (5, 1) = (618332979 / 62500000000) := rfl
@[simp] theorem lookup_previous_6_11 : previousPadding literalP (3, 0) (5, 1) = (46564339 / 1000000000) := rfl
@[simp] theorem lookup_current_6_11 : currentPadding literalP (3, 0) (5, 1) = (4583876417 / 125000000000) := rfl
@[simp] theorem lookup_descent_6_12 : literalDescent (3, 0) (6, 0) = (354953 / 40000000) := rfl
@[simp] theorem lookup_previous_6_12 : previousPadding literalP (3, 0) (6, 0) = (318231901 / 10000000000) := rfl
@[simp] theorem lookup_current_6_12 : currentPadding literalP (3, 0) (6, 0) = (229493651 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_13 : literalDescent (3, 0) (6, 1) = (6894833 / 2500000000) := rfl
@[simp] theorem lookup_previous_6_13 : previousPadding literalP (3, 0) (6, 1) = (42538291 / 10000000000) := rfl
@[simp] theorem lookup_current_6_13 : currentPadding literalP (3, 0) (6, 1) = (14958959 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_14 : literalDescent (3, 0) (7, 0) = (-10816011 / 2500000000) := rfl
@[simp] theorem lookup_previous_6_14 : previousPadding literalP (3, 0) (7, 0) = (1399817 / 500000000) := rfl
@[simp] theorem lookup_current_6_14 : currentPadding literalP (3, 0) (7, 0) = (2226887 / 312500000) := rfl
@[simp] theorem lookup_descent_6_15 : literalDescent (3, 0) (7, 1) = (-10065821 / 2000000000) := rfl
@[simp] theorem lookup_previous_6_15 : previousPadding literalP (3, 0) (7, 1) = (-162492897 / 10000000000) := rfl
@[simp] theorem lookup_current_6_15 : currentPadding literalP (3, 0) (7, 1) = (-7010237 / 625000000) := rfl
@[simp] theorem lookup_descent_6_16 : literalDescent (3, 0) (8, 0) = (-6136147 / 2500000000) := rfl
@[simp] theorem lookup_previous_6_16 : previousPadding literalP (3, 0) (8, 0) = (-82624617 / 10000000000) := rfl
@[simp] theorem lookup_current_6_16 : currentPadding literalP (3, 0) (8, 0) = (-58080029 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_17 : literalDescent (3, 0) (8, 1) = (-1301519 / 2000000000) := rfl
@[simp] theorem lookup_previous_6_17 : previousPadding literalP (3, 0) (8, 1) = (4650883 / 2500000000) := rfl
@[simp] theorem lookup_current_6_17 : currentPadding literalP (3, 0) (8, 1) = (25111127 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_18 : literalDescent (3, 0) (9, 0) = (75177 / 15625000) := rfl
@[simp] theorem lookup_previous_6_18 : previousPadding literalP (3, 0) (9, 0) = (75177 / 15625000) := rfl
@[simp] theorem lookup_current_6_18 : currentPadding literalP (3, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_6_19 : literalDescent (3, 0) (9, 1) = (5624077 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_19 : previousPadding literalP (3, 0) (9, 1) = (5624077 / 10000000000) := rfl
@[simp] theorem lookup_current_6_19 : currentPadding literalP (3, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_7_0 : literalDescent (3, 1) (0, 0) = (19934297 / 125000000000) := rfl
@[simp] theorem lookup_previous_7_0 : previousPadding literalP (3, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_7_0 : currentPadding literalP (3, 1) (0, 0) = (739383 / 1000000000) := rfl
@[simp] theorem lookup_descent_7_1 : literalDescent (3, 1) (0, 1) = (87875689 / 500000000000) := rfl
@[simp] theorem lookup_previous_7_1 : previousPadding literalP (3, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_7_1 : currentPadding literalP (3, 1) (0, 1) = (1807571 / 2500000000) := rfl
@[simp] theorem lookup_descent_7_2 : literalDescent (3, 1) (1, 0) = (4353293 / 7812500000) := rfl
@[simp] theorem lookup_previous_7_2 : previousPadding literalP (3, 1) (1, 0) = (52006018157 / 500000000000) := rfl
@[simp] theorem lookup_current_7_2 : currentPadding literalP (3, 1) (1, 0) = (4936103541 / 100000000000) := rfl
@[simp] theorem lookup_descent_7_3 : literalDescent (3, 1) (1, 1) = (-228199803 / 500000000000) := rfl
@[simp] theorem lookup_previous_7_3 : previousPadding literalP (3, 1) (1, 1) = (-1055411169 / 10000000000) := rfl
@[simp] theorem lookup_current_7_3 : currentPadding literalP (3, 1) (1, 1) = (-21435959 / 5000000000) := rfl
@[simp] theorem lookup_descent_7_4 : literalDescent (3, 1) (2, 0) = (-900115213 / 500000000000) := rfl
@[simp] theorem lookup_previous_7_4 : previousPadding literalP (3, 1) (2, 0) = (-92271799 / 2500000000) := rfl
@[simp] theorem lookup_current_7_4 : currentPadding literalP (3, 1) (2, 0) = (-516397 / 12500000) := rfl
@[simp] theorem lookup_descent_7_5 : literalDescent (3, 1) (2, 1) = (-249758189 / 500000000000) := rfl
@[simp] theorem lookup_previous_7_5 : previousPadding literalP (3, 1) (2, 1) = (-6501411 / 2500000000) := rfl
@[simp] theorem lookup_current_7_5 : currentPadding literalP (3, 1) (2, 1) = (-41521519 / 5000000000) := rfl
@[simp] theorem lookup_descent_7_6 : literalDescent (3, 1) (3, 0) = (1595222843 / 500000000000) := rfl
@[simp] theorem lookup_previous_7_6 : previousPadding literalP (3, 1) (3, 0) = (-36415770457 / 500000000000) := rfl
@[simp] theorem lookup_current_7_6 : currentPadding literalP (3, 1) (3, 0) = (-17838673 / 2000000000) := rfl
@[simp] theorem lookup_descent_7_7 : literalDescent (3, 1) (3, 1) = (520991469 / 250000000000) := rfl
@[simp] theorem lookup_previous_7_7 : previousPadding literalP (3, 1) (3, 1) = (28822774859 / 250000000000) := rfl
@[simp] theorem lookup_current_7_7 : currentPadding literalP (3, 1) (3, 1) = (9408740829 / 250000000000) := rfl
@[simp] theorem lookup_descent_7_8 : literalDescent (3, 1) (4, 0) = (-15298693 / 4000000000) := rfl
@[simp] theorem lookup_previous_7_8 : previousPadding literalP (3, 1) (4, 0) = (10959259 / 2500000000) := rfl
@[simp] theorem lookup_current_7_8 : currentPadding literalP (3, 1) (4, 0) = (1259799 / 2500000000) := rfl
@[simp] theorem lookup_descent_7_9 : literalDescent (3, 1) (4, 1) = (-132974287 / 100000000000) := rfl
@[simp] theorem lookup_previous_7_9 : previousPadding literalP (3, 1) (4, 1) = (-41521519 / 5000000000) := rfl
@[simp] theorem lookup_current_7_9 : currentPadding literalP (3, 1) (4, 1) = (-39495479 / 5000000000) := rfl
@[simp] theorem lookup_descent_7_10 : literalDescent (3, 1) (5, 0) = (-1025087 / 1000000000) := rfl
@[simp] theorem lookup_previous_7_10 : previousPadding literalP (3, 1) (5, 0) = (-33735433 / 2500000000) := rfl
@[simp] theorem lookup_current_7_10 : currentPadding literalP (3, 1) (5, 0) = (-62345431 / 5000000000) := rfl
@[simp] theorem lookup_descent_7_11 : literalDescent (3, 1) (5, 1) = (-286833 / 2000000000) := rfl
@[simp] theorem lookup_previous_7_11 : previousPadding literalP (3, 1) (5, 1) = (-493087 / 125000000) := rfl
@[simp] theorem lookup_current_7_11 : currentPadding literalP (3, 1) (5, 1) = (-7602559 / 2000000000) := rfl
@[simp] theorem lookup_descent_7_12 : literalDescent (3, 1) (6, 0) = (15623841 / 2500000000) := rfl
@[simp] theorem lookup_previous_7_12 : previousPadding literalP (3, 1) (6, 0) = (342367 / 20000000) := rfl
@[simp] theorem lookup_current_7_12 : currentPadding literalP (3, 1) (6, 0) = (13586017 / 1250000000) := rfl
@[simp] theorem lookup_descent_7_13 : literalDescent (3, 1) (6, 1) = (892851 / 5000000000) := rfl
@[simp] theorem lookup_previous_7_13 : previousPadding literalP (3, 1) (6, 1) = (1888701 / 2500000000) := rfl
@[simp] theorem lookup_current_7_13 : currentPadding literalP (3, 1) (6, 1) = (2884551 / 5000000000) := rfl
@[simp] theorem lookup_descent_7_14 : literalDescent (3, 1) (7, 0) = (-401709279 / 100000000000) := rfl
@[simp] theorem lookup_previous_7_14 : previousPadding literalP (3, 1) (7, 0) = (-3095557 / 5000000000) := rfl
@[simp] theorem lookup_current_7_14 : currentPadding literalP (3, 1) (7, 0) = (339798139 / 100000000000) := rfl
@[simp] theorem lookup_descent_7_15 : literalDescent (3, 1) (7, 1) = (-1968693 / 2000000000) := rfl
@[simp] theorem lookup_previous_7_15 : previousPadding literalP (3, 1) (7, 1) = (-26818913 / 10000000000) := rfl
@[simp] theorem lookup_current_7_15 : currentPadding literalP (3, 1) (7, 1) = (-2121931 / 1250000000) := rfl
@[simp] theorem lookup_descent_7_16 : literalDescent (3, 1) (8, 0) = (149869 / 2500000000) := rfl
@[simp] theorem lookup_previous_7_16 : previousPadding literalP (3, 1) (8, 0) = (-21110027 / 10000000000) := rfl
@[simp] theorem lookup_current_7_16 : currentPadding literalP (3, 1) (8, 0) = (-21709503 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_17 : literalDescent (3, 1) (8, 1) = (17539569 / 10000000000) := rfl
@[simp] theorem lookup_previous_7_17 : previousPadding literalP (3, 1) (8, 1) = (16464237 / 5000000000) := rfl
@[simp] theorem lookup_current_7_17 : currentPadding literalP (3, 1) (8, 1) = (3077781 / 2000000000) := rfl
@[simp] theorem lookup_descent_7_18 : literalDescent (3, 1) (9, 0) = (4504579 / 10000000000) := rfl
@[simp] theorem lookup_previous_7_18 : previousPadding literalP (3, 1) (9, 0) = (4504579 / 10000000000) := rfl
@[simp] theorem lookup_current_7_18 : currentPadding literalP (3, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_7_19 : literalDescent (3, 1) (9, 1) = (-311529 / 400000000) := rfl
@[simp] theorem lookup_previous_7_19 : previousPadding literalP (3, 1) (9, 1) = (-311529 / 400000000) := rfl
@[simp] theorem lookup_current_7_19 : currentPadding literalP (3, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_8_0 : literalDescent (4, 0) (0, 0) = (-41558817 / 20000000000) := rfl
@[simp] theorem lookup_previous_8_0 : previousPadding literalP (4, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_8_0 : currentPadding literalP (4, 0) (0, 0) = (-1926173 / 1250000000) := rfl
@[simp] theorem lookup_descent_8_1 : literalDescent (4, 0) (0, 1) = (-20724103 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_1 : previousPadding literalP (4, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_8_1 : currentPadding literalP (4, 0) (0, 1) = (-15464601 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_2 : literalDescent (4, 0) (1, 0) = (100337397 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_2 : previousPadding literalP (4, 0) (1, 0) = (387565431 / 10000000000) := rfl
@[simp] theorem lookup_current_8_2 : currentPadding literalP (4, 0) (1, 0) = (187797661 / 5000000000) := rfl
@[simp] theorem lookup_descent_8_3 : literalDescent (4, 0) (1, 1) = (1459960829 / 250000000000) := rfl
@[simp] theorem lookup_previous_8_3 : previousPadding literalP (4, 0) (1, 1) = (19973856411 / 500000000000) := rfl
@[simp] theorem lookup_current_8_3 : currentPadding literalP (4, 0) (1, 1) = (26392133 / 1250000000) := rfl
@[simp] theorem lookup_descent_8_4 : literalDescent (4, 0) (2, 0) = (-132626917 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_4 : previousPadding literalP (4, 0) (2, 0) = (-885781507 / 10000000000) := rfl
@[simp] theorem lookup_current_8_4 : currentPadding literalP (4, 0) (2, 0) = (-75315459 / 1000000000) := rfl
@[simp] theorem lookup_descent_8_5 : literalDescent (4, 0) (2, 1) = (-758293 / 250000000) := rfl
@[simp] theorem lookup_previous_8_5 : previousPadding literalP (4, 0) (2, 1) = (-41318363 / 2500000000) := rfl
@[simp] theorem lookup_current_8_5 : currentPadding literalP (4, 0) (2, 1) = (-33735433 / 2500000000) := rfl
@[simp] theorem lookup_descent_8_6 : literalDescent (4, 0) (3, 0) = (-354959661 / 20000000000) := rfl
@[simp] theorem lookup_previous_8_6 : previousPadding literalP (4, 0) (3, 0) = (-535578103 / 10000000000) := rfl
@[simp] theorem lookup_current_8_6 : currentPadding literalP (4, 0) (3, 0) = (-87028569 / 2000000000) := rfl
@[simp] theorem lookup_descent_8_7 : literalDescent (4, 0) (3, 1) = (-15298693 / 4000000000) := rfl
@[simp] theorem lookup_previous_8_7 : previousPadding literalP (4, 0) (3, 1) = (10959259 / 2500000000) := rfl
@[simp] theorem lookup_current_8_7 : currentPadding literalP (4, 0) (3, 1) = (1259799 / 2500000000) := rfl
@[simp] theorem lookup_descent_8_8 : literalDescent (4, 0) (4, 0) = (122558029 / 2500000000) := rfl
@[simp] theorem lookup_previous_8_8 : previousPadding literalP (4, 0) (4, 0) = (915787937 / 5000000000) := rfl
@[simp] theorem lookup_current_8_8 : currentPadding literalP (4, 0) (4, 0) = (173884489 / 1250000000) := rfl
@[simp] theorem lookup_descent_8_9 : literalDescent (4, 0) (4, 1) = (146882979 / 20000000000) := rfl
@[simp] theorem lookup_previous_8_9 : previousPadding literalP (4, 0) (4, 1) = (-17838673 / 2000000000) := rfl
@[simp] theorem lookup_current_8_9 : currentPadding literalP (4, 0) (4, 1) = (-8964573 / 2500000000) := rfl
@[simp] theorem lookup_descent_8_10 : literalDescent (4, 0) (5, 0) = (-51461671 / 2500000000) := rfl
@[simp] theorem lookup_previous_8_10 : previousPadding literalP (4, 0) (5, 0) = (-87028569 / 2000000000) := rfl
@[simp] theorem lookup_current_8_10 : currentPadding literalP (4, 0) (5, 0) = (-127081119 / 5000000000) := rfl
@[simp] theorem lookup_descent_8_11 : literalDescent (4, 0) (5, 1) = (-124359479 / 12500000000) := rfl
@[simp] theorem lookup_previous_8_11 : previousPadding literalP (4, 0) (5, 1) = (-343451171 / 10000000000) := rfl
@[simp] theorem lookup_current_8_11 : currentPadding literalP (4, 0) (5, 1) = (-3086845767 / 125000000000) := rfl
@[simp] theorem lookup_descent_8_12 : literalDescent (4, 0) (6, 0) = (-118903137 / 5000000000) := rfl
@[simp] theorem lookup_previous_8_12 : previousPadding literalP (4, 0) (6, 0) = (-75664107 / 1250000000) := rfl
@[simp] theorem lookup_current_8_12 : currentPadding literalP (4, 0) (6, 0) = (-183753291 / 5000000000) := rfl
@[simp] theorem lookup_descent_8_13 : literalDescent (4, 0) (6, 1) = (451990619 / 62500000000) := rfl
@[simp] theorem lookup_previous_8_13 : previousPadding literalP (4, 0) (6, 1) = (4583876417 / 125000000000) := rfl
@[simp] theorem lookup_current_8_13 : currentPadding literalP (4, 0) (6, 1) = (3679895179 / 125000000000) := rfl
@[simp] theorem lookup_descent_8_14 : literalDescent (4, 0) (7, 0) = (44383001 / 2000000000) := rfl
@[simp] theorem lookup_previous_8_14 : previousPadding literalP (4, 0) (7, 0) = (229493651 / 10000000000) := rfl
@[simp] theorem lookup_current_8_14 : currentPadding literalP (4, 0) (7, 0) = (3789323 / 5000000000) := rfl
@[simp] theorem lookup_descent_8_15 : literalDescent (4, 0) (7, 1) = (1477499 / 1000000000) := rfl
@[simp] theorem lookup_previous_8_15 : previousPadding literalP (4, 0) (7, 1) = (14958959 / 10000000000) := rfl
@[simp] theorem lookup_current_8_15 : currentPadding literalP (4, 0) (7, 1) = (183969 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_16 : literalDescent (4, 0) (8, 0) = (161077 / 80000000) := rfl
@[simp] theorem lookup_previous_8_16 : previousPadding literalP (4, 0) (8, 0) = (2226887 / 312500000) := rfl
@[simp] theorem lookup_current_8_16 : currentPadding literalP (4, 0) (8, 0) = (51125759 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_17 : literalDescent (4, 0) (8, 1) = (-17267 / 3125000) := rfl
@[simp] theorem lookup_previous_8_17 : previousPadding literalP (4, 0) (8, 1) = (-7010237 / 625000000) := rfl
@[simp] theorem lookup_current_8_17 : currentPadding literalP (4, 0) (8, 1) = (-3556837 / 625000000) := rfl
@[simp] theorem lookup_descent_8_18 : literalDescent (4, 0) (9, 0) = (-58080029 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_18 : previousPadding literalP (4, 0) (9, 0) = (-58080029 / 10000000000) := rfl
@[simp] theorem lookup_current_8_18 : currentPadding literalP (4, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_8_19 : literalDescent (4, 0) (9, 1) = (25111127 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_19 : previousPadding literalP (4, 0) (9, 1) = (25111127 / 10000000000) := rfl
@[simp] theorem lookup_current_8_19 : currentPadding literalP (4, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_9_0 : literalDescent (4, 1) (0, 0) = (-723530193 / 500000000000) := rfl
@[simp] theorem lookup_previous_9_0 : previousPadding literalP (4, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_9_0 : currentPadding literalP (4, 1) (0, 0) = (-33312251 / 2000000000) := rfl
@[simp] theorem lookup_descent_9_1 : literalDescent (4, 1) (0, 1) = (-99155713 / 100000000000) := rfl
@[simp] theorem lookup_previous_9_1 : previousPadding literalP (4, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_9_1 : currentPadding literalP (4, 1) (0, 1) = (-85558501 / 5000000000) := rfl
@[simp] theorem lookup_descent_9_2 : literalDescent (4, 1) (1, 0) = (64684911 / 20000000000) := rfl
@[simp] theorem lookup_previous_9_2 : previousPadding literalP (4, 1) (1, 0) = (739383 / 1000000000) := rfl
@[simp] theorem lookup_current_9_2 : currentPadding literalP (4, 1) (1, 0) = (63418647 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_3 : literalDescent (4, 1) (1, 1) = (434951 / 400000000) := rfl
@[simp] theorem lookup_previous_9_3 : previousPadding literalP (4, 1) (1, 1) = (1807571 / 2500000000) := rfl
@[simp] theorem lookup_current_9_3 : currentPadding literalP (4, 1) (1, 1) = (1125861 / 1000000000) := rfl
@[simp] theorem lookup_descent_9_4 : literalDescent (4, 1) (2, 0) = (279669641 / 100000000000) := rfl
@[simp] theorem lookup_previous_9_4 : previousPadding literalP (4, 1) (2, 0) = (4936103541 / 100000000000) := rfl
@[simp] theorem lookup_current_9_4 : currentPadding literalP (4, 1) (2, 0) = (46564339 / 1000000000) := rfl
@[simp] theorem lookup_descent_9_5 : literalDescent (4, 1) (2, 1) = (-1712479 / 5000000000) := rfl
@[simp] theorem lookup_previous_9_5 : previousPadding literalP (4, 1) (2, 1) = (-21435959 / 5000000000) := rfl
@[simp] theorem lookup_current_9_5 : currentPadding literalP (4, 1) (2, 1) = (-493087 / 125000000) := rfl
@[simp] theorem lookup_descent_9_6 : literalDescent (4, 1) (3, 0) = (-3945616407 / 500000000000) := rfl
@[simp] theorem lookup_previous_9_6 : previousPadding literalP (4, 1) (3, 0) = (-516397 / 12500000) := rfl
@[simp] theorem lookup_current_9_6 : currentPadding literalP (4, 1) (3, 0) = (-343451171 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_7 : literalDescent (4, 1) (3, 1) = (-132974287 / 100000000000) := rfl
@[simp] theorem lookup_previous_9_7 : previousPadding literalP (4, 1) (3, 1) = (-41521519 / 5000000000) := rfl
@[simp] theorem lookup_current_9_7 : currentPadding literalP (4, 1) (3, 1) = (-39495479 / 5000000000) := rfl
@[simp] theorem lookup_descent_9_8 : literalDescent (4, 1) (4, 0) = (146882979 / 20000000000) := rfl
@[simp] theorem lookup_previous_9_8 : previousPadding literalP (4, 1) (4, 0) = (-17838673 / 2000000000) := rfl
@[simp] theorem lookup_current_9_8 : currentPadding literalP (4, 1) (4, 0) = (-8964573 / 2500000000) := rfl
@[simp] theorem lookup_descent_9_9 : literalDescent (4, 1) (4, 1) = (567232603 / 125000000000) := rfl
@[simp] theorem lookup_previous_9_9 : previousPadding literalP (4, 1) (4, 1) = (9408740829 / 250000000000) := rfl
@[simp] theorem lookup_current_9_9 : currentPadding literalP (4, 1) (4, 1) = (6127618283 / 250000000000) := rfl
@[simp] theorem lookup_descent_9_10 : literalDescent (4, 1) (5, 0) = (-28518929 / 5000000000) := rfl
@[simp] theorem lookup_previous_9_10 : previousPadding literalP (4, 1) (5, 0) = (1259799 / 2500000000) := rfl
@[simp] theorem lookup_current_9_10 : currentPadding literalP (4, 1) (5, 0) = (37210977 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_11 : literalDescent (4, 1) (5, 1) = (-592954781 / 250000000000) := rfl
@[simp] theorem lookup_previous_9_11 : previousPadding literalP (4, 1) (5, 1) = (-39495479 / 5000000000) := rfl
@[simp] theorem lookup_current_9_11 : currentPadding literalP (4, 1) (5, 1) = (-7282087 / 1250000000) := rfl
@[simp] theorem lookup_descent_9_12 : literalDescent (4, 1) (6, 0) = (-66965541 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_12 : previousPadding literalP (4, 1) (6, 0) = (-62345431 / 5000000000) := rfl
@[simp] theorem lookup_current_9_12 : currentPadding literalP (4, 1) (6, 0) = (-57725321 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_13 : literalDescent (4, 1) (6, 1) = (-1213993 / 2500000000) := rfl
@[simp] theorem lookup_previous_9_13 : previousPadding literalP (4, 1) (6, 1) = (-7602559 / 2000000000) := rfl
@[simp] theorem lookup_current_9_13 : currentPadding literalP (4, 1) (6, 1) = (-33156823 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_14 : literalDescent (4, 1) (7, 0) = (106364901 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_14 : previousPadding literalP (4, 1) (7, 0) = (13586017 / 1250000000) := rfl
@[simp] theorem lookup_current_9_14 : currentPadding literalP (4, 1) (7, 0) = (464647 / 2000000000) := rfl
@[simp] theorem lookup_descent_9_15 : literalDescent (4, 1) (7, 1) = (555111 / 1250000000) := rfl
@[simp] theorem lookup_previous_9_15 : previousPadding literalP (4, 1) (7, 1) = (2884551 / 5000000000) := rfl
@[simp] theorem lookup_current_9_15 : currentPadding literalP (4, 1) (7, 1) = (664107 / 5000000000) := rfl
@[simp] theorem lookup_descent_9_16 : literalDescent (4, 1) (8, 0) = (-10199761 / 100000000000) := rfl
@[simp] theorem lookup_previous_9_16 : previousPadding literalP (4, 1) (8, 0) = (339798139 / 100000000000) := rfl
@[simp] theorem lookup_current_9_16 : currentPadding literalP (4, 1) (8, 0) = (3499979 / 1000000000) := rfl
@[simp] theorem lookup_descent_9_17 : literalDescent (4, 1) (8, 1) = (-4174011 / 2000000000) := rfl
@[simp] theorem lookup_previous_9_17 : previousPadding literalP (4, 1) (8, 1) = (-2121931 / 1250000000) := rfl
@[simp] theorem lookup_current_9_17 : currentPadding literalP (4, 1) (8, 1) = (3894607 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_18 : literalDescent (4, 1) (9, 0) = (-21709503 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_18 : previousPadding literalP (4, 1) (9, 0) = (-21709503 / 10000000000) := rfl
@[simp] theorem lookup_current_9_18 : currentPadding literalP (4, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_9_19 : literalDescent (4, 1) (9, 1) = (3077781 / 2000000000) := rfl
@[simp] theorem lookup_previous_9_19 : previousPadding literalP (4, 1) (9, 1) = (3077781 / 2000000000) := rfl
@[simp] theorem lookup_current_9_19 : currentPadding literalP (4, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_10_0 : literalDescent (5, 0) (0, 0) = (7184263 / 20000000000) := rfl
@[simp] theorem lookup_previous_10_0 : previousPadding literalP (5, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_10_0 : currentPadding literalP (5, 0) (0, 0) = (392181 / 625000000) := rfl
@[simp] theorem lookup_descent_10_1 : literalDescent (5, 0) (0, 1) = (8014933 / 10000000000) := rfl
@[simp] theorem lookup_previous_10_1 : previousPadding literalP (5, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_10_1 : currentPadding literalP (5, 0) (0, 1) = (926073 / 5000000000) := rfl
@[simp] theorem lookup_descent_10_2 : literalDescent (5, 0) (1, 0) = (-2801751 / 4000000000) := rfl
@[simp] theorem lookup_previous_10_2 : previousPadding literalP (5, 0) (1, 0) = (-1926173 / 1250000000) := rfl
@[simp] theorem lookup_current_10_2 : currentPadding literalP (5, 0) (1, 0) = (-8404979 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_3 : literalDescent (5, 0) (1, 1) = (-153170061 / 125000000000) := rfl
@[simp] theorem lookup_previous_10_3 : previousPadding literalP (5, 0) (1, 1) = (-15464601 / 10000000000) := rfl
@[simp] theorem lookup_current_10_3 : currentPadding literalP (5, 0) (1, 1) = (-1307803 / 1000000000) := rfl
@[simp] theorem lookup_descent_10_4 : literalDescent (5, 0) (2, 0) = (57363421 / 10000000000) := rfl
@[simp] theorem lookup_previous_10_4 : previousPadding literalP (5, 0) (2, 0) = (187797661 / 5000000000) := rfl
@[simp] theorem lookup_current_10_4 : currentPadding literalP (5, 0) (2, 0) = (318231901 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_5 : literalDescent (5, 0) (2, 1) = (9988391 / 2500000000) := rfl
@[simp] theorem lookup_previous_10_5 : previousPadding literalP (5, 0) (2, 1) = (26392133 / 1250000000) := rfl
@[simp] theorem lookup_current_10_5 : currentPadding literalP (5, 0) (2, 1) = (342367 / 20000000) := rfl
@[simp] theorem lookup_descent_10_6 : literalDescent (5, 0) (3, 0) = (-73920867 / 5000000000) := rfl
@[simp] theorem lookup_previous_10_6 : previousPadding literalP (5, 0) (3, 0) = (-75315459 / 1000000000) := rfl
@[simp] theorem lookup_current_10_6 : currentPadding literalP (5, 0) (3, 0) = (-75664107 / 1250000000) := rfl
@[simp] theorem lookup_descent_10_7 : literalDescent (5, 0) (3, 1) = (-1025087 / 1000000000) := rfl
@[simp] theorem lookup_previous_10_7 : previousPadding literalP (5, 0) (3, 1) = (-33735433 / 2500000000) := rfl
@[simp] theorem lookup_current_10_7 : currentPadding literalP (5, 0) (3, 1) = (-62345431 / 5000000000) := rfl
@[simp] theorem lookup_descent_10_8 : literalDescent (5, 0) (4, 0) = (-51461671 / 2500000000) := rfl
@[simp] theorem lookup_previous_10_8 : previousPadding literalP (5, 0) (4, 0) = (-87028569 / 2000000000) := rfl
@[simp] theorem lookup_current_10_8 : currentPadding literalP (5, 0) (4, 0) = (-127081119 / 5000000000) := rfl
@[simp] theorem lookup_descent_10_9 : literalDescent (5, 0) (4, 1) = (-28518929 / 5000000000) := rfl
@[simp] theorem lookup_previous_10_9 : previousPadding literalP (5, 0) (4, 1) = (1259799 / 2500000000) := rfl
@[simp] theorem lookup_current_10_9 : currentPadding literalP (5, 0) (4, 1) = (37210977 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_10 : literalDescent (5, 0) (5, 0) = (254495849 / 5000000000) := rfl
@[simp] theorem lookup_previous_10_10 : previousPadding literalP (5, 0) (5, 0) = (173884489 / 1250000000) := rfl
@[simp] theorem lookup_current_10_10 : currentPadding literalP (5, 0) (5, 0) = (456041129 / 5000000000) := rfl
@[simp] theorem lookup_descent_10_11 : literalDescent (5, 0) (5, 1) = (51977781 / 20000000000) := rfl
@[simp] theorem lookup_previous_10_11 : previousPadding literalP (5, 0) (5, 1) = (-8964573 / 2500000000) := rfl
@[simp] theorem lookup_current_10_11 : currentPadding literalP (5, 0) (5, 1) = (-1396947 / 2000000000) := rfl
@[simp] theorem lookup_descent_10_12 : literalDescent (5, 0) (6, 0) = (4783079 / 1000000000) := rfl
@[simp] theorem lookup_previous_10_12 : previousPadding literalP (5, 0) (6, 0) = (-127081119 / 5000000000) := rfl
@[simp] theorem lookup_current_10_12 : currentPadding literalP (5, 0) (6, 0) = (-6339841 / 200000000) := rfl
@[simp] theorem lookup_descent_10_13 : literalDescent (5, 0) (6, 1) = (-1858963859 / 250000000000) := rfl
@[simp] theorem lookup_previous_10_13 : previousPadding literalP (5, 0) (6, 1) = (-3086845767 / 125000000000) := rfl
@[simp] theorem lookup_current_10_13 : currentPadding literalP (5, 0) (6, 1) = (-2179880779 / 125000000000) := rfl
@[simp] theorem lookup_descent_10_14 : literalDescent (5, 0) (7, 0) = (-167163191 / 5000000000) := rfl
@[simp] theorem lookup_previous_10_14 : previousPadding literalP (5, 0) (7, 0) = (-183753291 / 5000000000) := rfl
@[simp] theorem lookup_current_10_14 : currentPadding literalP (5, 0) (7, 0) = (-165901 / 50000000) := rfl
@[simp] theorem lookup_descent_10_15 : literalDescent (5, 0) (7, 1) = (3845579287 / 500000000000) := rfl
@[simp] theorem lookup_previous_10_15 : previousPadding literalP (5, 0) (7, 1) = (3679895179 / 125000000000) := rfl
@[simp] theorem lookup_current_10_15 : currentPadding literalP (5, 0) (7, 1) = (10874001429 / 500000000000) := rfl
@[simp] theorem lookup_descent_10_16 : literalDescent (5, 0) (8, 0) = (13057689 / 5000000000) := rfl
@[simp] theorem lookup_previous_10_16 : previousPadding literalP (5, 0) (8, 0) = (3789323 / 5000000000) := rfl
@[simp] theorem lookup_current_10_16 : currentPadding literalP (5, 0) (8, 0) = (-4634183 / 2500000000) := rfl
@[simp] theorem lookup_descent_10_17 : literalDescent (5, 0) (8, 1) = (29970653 / 5000000000) := rfl
@[simp] theorem lookup_previous_10_17 : previousPadding literalP (5, 0) (8, 1) = (183969 / 10000000000) := rfl
@[simp] theorem lookup_current_10_17 : currentPadding literalP (5, 0) (8, 1) = (-59757337 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_18 : literalDescent (5, 0) (9, 0) = (51125759 / 10000000000) := rfl
@[simp] theorem lookup_previous_10_18 : previousPadding literalP (5, 0) (9, 0) = (51125759 / 10000000000) := rfl
@[simp] theorem lookup_current_10_18 : currentPadding literalP (5, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_10_19 : literalDescent (5, 0) (9, 1) = (-3556837 / 625000000) := rfl
@[simp] theorem lookup_previous_10_19 : previousPadding literalP (5, 0) (9, 1) = (-3556837 / 625000000) := rfl
@[simp] theorem lookup_current_10_19 : currentPadding literalP (5, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_11_0 : literalDescent (5, 1) (0, 0) = (52016533 / 31250000000) := rfl
@[simp] theorem lookup_previous_11_0 : previousPadding literalP (5, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_11_0 : currentPadding literalP (5, 1) (0, 0) = (17421309 / 5000000000) := rfl
@[simp] theorem lookup_descent_11_1 : literalDescent (5, 1) (0, 1) = (585318937 / 500000000000) := rfl
@[simp] theorem lookup_previous_11_1 : previousPadding literalP (5, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_11_1 : currentPadding literalP (5, 1) (0, 1) = (310779 / 78125000) := rfl
@[simp] theorem lookup_descent_11_2 : literalDescent (5, 1) (1, 0) = (-103318071 / 20000000000) := rfl
@[simp] theorem lookup_previous_11_2 : previousPadding literalP (5, 1) (1, 0) = (-33312251 / 2000000000) := rfl
@[simp] theorem lookup_current_11_2 : currentPadding literalP (5, 1) (1, 0) = (-5081737 / 250000000) := rfl
@[simp] theorem lookup_descent_11_3 : literalDescent (5, 1) (1, 1) = (-20319797 / 10000000000) := rfl
@[simp] theorem lookup_previous_11_3 : previousPadding literalP (5, 1) (1, 1) = (-85558501 / 5000000000) := rfl
@[simp] theorem lookup_current_11_3 : currentPadding literalP (5, 1) (1, 1) = (-18076423 / 5000000000) := rfl
@[simp] theorem lookup_descent_11_4 : literalDescent (5, 1) (2, 0) = (5220089 / 2500000000) := rfl
@[simp] theorem lookup_previous_11_4 : previousPadding literalP (5, 1) (2, 0) = (63418647 / 10000000000) := rfl
@[simp] theorem lookup_current_11_4 : currentPadding literalP (5, 1) (2, 0) = (42538291 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_5 : literalDescent (5, 1) (2, 1) = (1851903 / 5000000000) := rfl
@[simp] theorem lookup_previous_11_5 : previousPadding literalP (5, 1) (2, 1) = (1125861 / 1000000000) := rfl
@[simp] theorem lookup_current_11_5 : currentPadding literalP (5, 1) (2, 1) = (1888701 / 2500000000) := rfl
@[simp] theorem lookup_descent_11_6 : literalDescent (5, 1) (3, 0) = (618332979 / 62500000000) := rfl
@[simp] theorem lookup_previous_11_6 : previousPadding literalP (5, 1) (3, 0) = (46564339 / 1000000000) := rfl
@[simp] theorem lookup_current_11_6 : currentPadding literalP (5, 1) (3, 0) = (4583876417 / 125000000000) := rfl
@[simp] theorem lookup_descent_11_7 : literalDescent (5, 1) (3, 1) = (-286833 / 2000000000) := rfl
@[simp] theorem lookup_previous_11_7 : previousPadding literalP (5, 1) (3, 1) = (-493087 / 125000000) := rfl
@[simp] theorem lookup_current_11_7 : currentPadding literalP (5, 1) (3, 1) = (-7602559 / 2000000000) := rfl
@[simp] theorem lookup_descent_11_8 : literalDescent (5, 1) (4, 0) = (-124359479 / 12500000000) := rfl
@[simp] theorem lookup_previous_11_8 : previousPadding literalP (5, 1) (4, 0) = (-343451171 / 10000000000) := rfl
@[simp] theorem lookup_current_11_8 : currentPadding literalP (5, 1) (4, 0) = (-3086845767 / 125000000000) := rfl
@[simp] theorem lookup_descent_11_9 : literalDescent (5, 1) (4, 1) = (-592954781 / 250000000000) := rfl
@[simp] theorem lookup_previous_11_9 : previousPadding literalP (5, 1) (4, 1) = (-39495479 / 5000000000) := rfl
@[simp] theorem lookup_current_11_9 : currentPadding literalP (5, 1) (4, 1) = (-7282087 / 1250000000) := rfl
@[simp] theorem lookup_descent_11_10 : literalDescent (5, 1) (5, 0) = (51977781 / 20000000000) := rfl
@[simp] theorem lookup_previous_11_10 : previousPadding literalP (5, 1) (5, 0) = (-8964573 / 2500000000) := rfl
@[simp] theorem lookup_current_11_10 : currentPadding literalP (5, 1) (5, 0) = (-1396947 / 2000000000) := rfl
@[simp] theorem lookup_descent_11_11 : literalDescent (5, 1) (5, 1) = (2557290657 / 500000000000) := rfl
@[simp] theorem lookup_previous_11_11 : previousPadding literalP (5, 1) (5, 1) = (6127618283 / 250000000000) := rfl
@[simp] theorem lookup_current_11_11 : currentPadding literalP (5, 1) (5, 1) = (9009633333 / 500000000000) := rfl
@[simp] theorem lookup_descent_11_12 : literalDescent (5, 1) (6, 0) = (2280301 / 5000000000) := rfl
@[simp] theorem lookup_previous_11_12 : previousPadding literalP (5, 1) (6, 0) = (37210977 / 10000000000) := rfl
@[simp] theorem lookup_current_11_12 : currentPadding literalP (5, 1) (6, 0) = (17651353 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_13 : literalDescent (5, 1) (6, 1) = (-97092041 / 250000000000) := rfl
@[simp] theorem lookup_previous_11_13 : previousPadding literalP (5, 1) (6, 1) = (-7282087 / 1250000000) := rfl
@[simp] theorem lookup_current_11_13 : currentPadding literalP (5, 1) (6, 1) = (-56172897 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_14 : literalDescent (5, 1) (7, 0) = (-23064697 / 5000000000) := rfl
@[simp] theorem lookup_previous_11_14 : previousPadding literalP (5, 1) (7, 0) = (-57725321 / 10000000000) := rfl
@[simp] theorem lookup_current_11_14 : currentPadding literalP (5, 1) (7, 0) = (-11595927 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_15 : literalDescent (5, 1) (7, 1) = (-12710103 / 10000000000) := rfl
@[simp] theorem lookup_previous_11_15 : previousPadding literalP (5, 1) (7, 1) = (-33156823 / 10000000000) := rfl
@[simp] theorem lookup_current_11_15 : currentPadding literalP (5, 1) (7, 1) = (-7987 / 3906250) := rfl
@[simp] theorem lookup_descent_11_16 : literalDescent (5, 1) (8, 0) = (-4732193 / 10000000000) := rfl
@[simp] theorem lookup_previous_11_16 : previousPadding literalP (5, 1) (8, 0) = (464647 / 2000000000) := rfl
@[simp] theorem lookup_current_11_16 : currentPadding literalP (5, 1) (8, 0) = (1763857 / 2500000000) := rfl
@[simp] theorem lookup_descent_11_17 : literalDescent (5, 1) (8, 1) = (-8384667 / 10000000000) := rfl
@[simp] theorem lookup_previous_11_17 : previousPadding literalP (5, 1) (8, 1) = (664107 / 5000000000) := rfl
@[simp] theorem lookup_current_11_17 : currentPadding literalP (5, 1) (8, 1) = (9712881 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_18 : literalDescent (5, 1) (9, 0) = (3499979 / 1000000000) := rfl
@[simp] theorem lookup_previous_11_18 : previousPadding literalP (5, 1) (9, 0) = (3499979 / 1000000000) := rfl
@[simp] theorem lookup_current_11_18 : currentPadding literalP (5, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_11_19 : literalDescent (5, 1) (9, 1) = (3894607 / 10000000000) := rfl
@[simp] theorem lookup_previous_11_19 : previousPadding literalP (5, 1) (9, 1) = (3894607 / 10000000000) := rfl
@[simp] theorem lookup_current_11_19 : currentPadding literalP (5, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_12_0 : literalDescent (6, 0) (0, 0) = (-2531581 / 2500000000) := rfl
@[simp] theorem lookup_previous_12_0 : previousPadding literalP (6, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_12_0 : currentPadding literalP (6, 0) (0, 0) = (16845107 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_1 : literalDescent (6, 0) (0, 1) = (118271 / 20000000000) := rfl
@[simp] theorem lookup_previous_12_1 : previousPadding literalP (6, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_12_1 : currentPadding literalP (6, 0) (0, 1) = (832461 / 1250000000) := rfl
@[simp] theorem lookup_descent_12_2 : literalDescent (6, 0) (1, 0) = (40168437 / 20000000000) := rfl
@[simp] theorem lookup_previous_12_2 : previousPadding literalP (6, 0) (1, 0) = (392181 / 625000000) := rfl
@[simp] theorem lookup_current_12_2 : currentPadding literalP (6, 0) (1, 0) = (-1106201 / 2000000000) := rfl
@[simp] theorem lookup_descent_12_3 : literalDescent (6, 0) (1, 1) = (118622537 / 500000000000) := rfl
@[simp] theorem lookup_previous_12_3 : previousPadding literalP (6, 0) (1, 1) = (926073 / 5000000000) := rfl
@[simp] theorem lookup_current_12_3 : currentPadding literalP (6, 0) (1, 1) = (-22802289 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_4 : literalDescent (6, 0) (2, 0) = (-36401319 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_4 : previousPadding literalP (6, 0) (2, 0) = (-8404979 / 10000000000) := rfl
@[simp] theorem lookup_current_12_4 : currentPadding literalP (6, 0) (2, 0) = (1399817 / 500000000) := rfl
@[simp] theorem lookup_descent_12_5 : literalDescent (6, 0) (2, 1) = (-1721729 / 2500000000) := rfl
@[simp] theorem lookup_previous_12_5 : previousPadding literalP (6, 0) (2, 1) = (-1307803 / 1000000000) := rfl
@[simp] theorem lookup_current_12_5 : currentPadding literalP (6, 0) (2, 1) = (-3095557 / 5000000000) := rfl
@[simp] theorem lookup_descent_12_6 : literalDescent (6, 0) (3, 0) = (354953 / 40000000) := rfl
@[simp] theorem lookup_previous_12_6 : previousPadding literalP (6, 0) (3, 0) = (318231901 / 10000000000) := rfl
@[simp] theorem lookup_current_12_6 : currentPadding literalP (6, 0) (3, 0) = (229493651 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_7 : literalDescent (6, 0) (3, 1) = (15623841 / 2500000000) := rfl
@[simp] theorem lookup_previous_12_7 : previousPadding literalP (6, 0) (3, 1) = (342367 / 20000000) := rfl
@[simp] theorem lookup_current_12_7 : currentPadding literalP (6, 0) (3, 1) = (13586017 / 1250000000) := rfl
@[simp] theorem lookup_descent_12_8 : literalDescent (6, 0) (4, 0) = (-118903137 / 5000000000) := rfl
@[simp] theorem lookup_previous_12_8 : previousPadding literalP (6, 0) (4, 0) = (-75664107 / 1250000000) := rfl
@[simp] theorem lookup_current_12_8 : currentPadding literalP (6, 0) (4, 0) = (-183753291 / 5000000000) := rfl
@[simp] theorem lookup_descent_12_9 : literalDescent (6, 0) (4, 1) = (-66965541 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_9 : previousPadding literalP (6, 0) (4, 1) = (-62345431 / 5000000000) := rfl
@[simp] theorem lookup_current_12_9 : currentPadding literalP (6, 0) (4, 1) = (-57725321 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_10 : literalDescent (6, 0) (5, 0) = (4783079 / 1000000000) := rfl
@[simp] theorem lookup_previous_12_10 : previousPadding literalP (6, 0) (5, 0) = (-127081119 / 5000000000) := rfl
@[simp] theorem lookup_current_12_10 : currentPadding literalP (6, 0) (5, 0) = (-6339841 / 200000000) := rfl
@[simp] theorem lookup_descent_12_11 : literalDescent (6, 0) (5, 1) = (2280301 / 5000000000) := rfl
@[simp] theorem lookup_previous_12_11 : previousPadding literalP (6, 0) (5, 1) = (37210977 / 10000000000) := rfl
@[simp] theorem lookup_current_12_11 : currentPadding literalP (6, 0) (5, 1) = (17651353 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_12 : literalDescent (6, 0) (6, 0) = (76707903 / 2000000000) := rfl
@[simp] theorem lookup_previous_12_12 : previousPadding literalP (6, 0) (6, 0) = (456041129 / 5000000000) := rfl
@[simp] theorem lookup_current_12_12 : currentPadding literalP (6, 0) (6, 0) = (264273293 / 5000000000) := rfl
@[simp] theorem lookup_descent_12_13 : literalDescent (6, 0) (6, 1) = (-42746263 / 20000000000) := rfl
@[simp] theorem lookup_previous_12_13 : previousPadding literalP (6, 0) (6, 1) = (-1396947 / 2000000000) := rfl
@[simp] theorem lookup_current_12_13 : currentPadding literalP (6, 0) (6, 1) = (29390699 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_14 : literalDescent (6, 0) (7, 0) = (-525525547 / 20000000000) := rfl
@[simp] theorem lookup_previous_12_14 : previousPadding literalP (6, 0) (7, 0) = (-6339841 / 200000000) := rfl
@[simp] theorem lookup_current_12_14 : currentPadding literalP (6, 0) (7, 0) = (-27115599 / 5000000000) := rfl
@[simp] theorem lookup_descent_12_15 : literalDescent (6, 0) (7, 1) = (-1273043483 / 250000000000) := rfl
@[simp] theorem lookup_previous_12_15 : previousPadding literalP (6, 0) (7, 1) = (-2179880779 / 125000000000) := rfl
@[simp] theorem lookup_current_12_15 : currentPadding literalP (6, 0) (7, 1) = (-6173472429 / 500000000000) := rfl
@[simp] theorem lookup_descent_12_16 : literalDescent (6, 0) (8, 0) = (25440649 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_16 : previousPadding literalP (6, 0) (8, 0) = (-165901 / 50000000) := rfl
@[simp] theorem lookup_current_12_16 : currentPadding literalP (6, 0) (8, 0) = (-58620849 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_17 : literalDescent (6, 0) (8, 1) = (6820855629 / 500000000000) := rfl
@[simp] theorem lookup_previous_12_17 : previousPadding literalP (6, 0) (8, 1) = (10874001429 / 500000000000) := rfl
@[simp] theorem lookup_current_12_17 : currentPadding literalP (6, 0) (8, 1) = (20265729 / 2500000000) := rfl
@[simp] theorem lookup_descent_12_18 : literalDescent (6, 0) (9, 0) = (-4634183 / 2500000000) := rfl
@[simp] theorem lookup_previous_12_18 : previousPadding literalP (6, 0) (9, 0) = (-4634183 / 2500000000) := rfl
@[simp] theorem lookup_current_12_18 : currentPadding literalP (6, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_12_19 : literalDescent (6, 0) (9, 1) = (-59757337 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_19 : previousPadding literalP (6, 0) (9, 1) = (-59757337 / 10000000000) := rfl
@[simp] theorem lookup_current_12_19 : currentPadding literalP (6, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_13_0 : literalDescent (6, 1) (0, 0) = (3130629 / 125000000000) := rfl
@[simp] theorem lookup_previous_13_0 : previousPadding literalP (6, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_13_0 : currentPadding literalP (6, 1) (0, 0) = (-10863883 / 5000000000) := rfl
@[simp] theorem lookup_descent_13_1 : literalDescent (6, 1) (0, 1) = (24641457 / 500000000000) := rfl
@[simp] theorem lookup_previous_13_1 : previousPadding literalP (6, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_13_1 : currentPadding literalP (6, 1) (0, 1) = (-1098609 / 500000000) := rfl
@[simp] theorem lookup_descent_13_2 : literalDescent (6, 1) (1, 0) = (2142083 / 2500000000) := rfl
@[simp] theorem lookup_previous_13_2 : previousPadding literalP (6, 1) (1, 0) = (17421309 / 5000000000) := rfl
@[simp] theorem lookup_current_13_2 : currentPadding literalP (6, 1) (1, 0) = (134971 / 39062500) := rfl
@[simp] theorem lookup_descent_13_3 : literalDescent (6, 1) (1, 1) = (228280233 / 500000000000) := rfl
@[simp] theorem lookup_previous_13_3 : previousPadding literalP (6, 1) (1, 1) = (310779 / 78125000) := rfl
@[simp] theorem lookup_current_13_3 : currentPadding literalP (6, 1) (1, 1) = (41130273 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_4 : literalDescent (6, 1) (2, 0) = (-40776583 / 10000000000) := rfl
@[simp] theorem lookup_previous_13_4 : previousPadding literalP (6, 1) (2, 0) = (-5081737 / 250000000) := rfl
@[simp] theorem lookup_current_13_4 : currentPadding literalP (6, 1) (2, 0) = (-162492897 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_5 : literalDescent (6, 1) (2, 1) = (-9333933 / 10000000000) := rfl
@[simp] theorem lookup_previous_13_5 : previousPadding literalP (6, 1) (2, 1) = (-18076423 / 5000000000) := rfl
@[simp] theorem lookup_current_13_5 : currentPadding literalP (6, 1) (2, 1) = (-26818913 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_6 : literalDescent (6, 1) (3, 0) = (6894833 / 2500000000) := rfl
@[simp] theorem lookup_previous_13_6 : previousPadding literalP (6, 1) (3, 0) = (42538291 / 10000000000) := rfl
@[simp] theorem lookup_current_13_6 : currentPadding literalP (6, 1) (3, 0) = (14958959 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_7 : literalDescent (6, 1) (3, 1) = (892851 / 5000000000) := rfl
@[simp] theorem lookup_previous_13_7 : previousPadding literalP (6, 1) (3, 1) = (1888701 / 2500000000) := rfl
@[simp] theorem lookup_current_13_7 : currentPadding literalP (6, 1) (3, 1) = (2884551 / 5000000000) := rfl
@[simp] theorem lookup_descent_13_8 : literalDescent (6, 1) (4, 0) = (451990619 / 62500000000) := rfl
@[simp] theorem lookup_previous_13_8 : previousPadding literalP (6, 1) (4, 0) = (4583876417 / 125000000000) := rfl
@[simp] theorem lookup_current_13_8 : currentPadding literalP (6, 1) (4, 0) = (3679895179 / 125000000000) := rfl
@[simp] theorem lookup_descent_13_9 : literalDescent (6, 1) (4, 1) = (-1213993 / 2500000000) := rfl
@[simp] theorem lookup_previous_13_9 : previousPadding literalP (6, 1) (4, 1) = (-7602559 / 2000000000) := rfl
@[simp] theorem lookup_current_13_9 : currentPadding literalP (6, 1) (4, 1) = (-33156823 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_10 : literalDescent (6, 1) (5, 0) = (-1858963859 / 250000000000) := rfl
@[simp] theorem lookup_previous_13_10 : previousPadding literalP (6, 1) (5, 0) = (-3086845767 / 125000000000) := rfl
@[simp] theorem lookup_current_13_10 : currentPadding literalP (6, 1) (5, 0) = (-2179880779 / 125000000000) := rfl
@[simp] theorem lookup_descent_13_11 : literalDescent (6, 1) (5, 1) = (-97092041 / 250000000000) := rfl
@[simp] theorem lookup_previous_13_11 : previousPadding literalP (6, 1) (5, 1) = (-7282087 / 1250000000) := rfl
@[simp] theorem lookup_current_13_11 : currentPadding literalP (6, 1) (5, 1) = (-56172897 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_12 : literalDescent (6, 1) (6, 0) = (-42746263 / 20000000000) := rfl
@[simp] theorem lookup_previous_13_12 : previousPadding literalP (6, 1) (6, 0) = (-1396947 / 2000000000) := rfl
@[simp] theorem lookup_current_13_12 : currentPadding literalP (6, 1) (6, 0) = (29390699 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_13 : literalDescent (6, 1) (6, 1) = (1630328721 / 500000000000) := rfl
@[simp] theorem lookup_previous_13_13 : previousPadding literalP (6, 1) (6, 1) = (9009633333 / 500000000000) := rfl
@[simp] theorem lookup_current_13_13 : currentPadding literalP (6, 1) (6, 1) = (3029791413 / 250000000000) := rfl
@[simp] theorem lookup_descent_13_14 : literalDescent (6, 1) (7, 0) = (56736899 / 20000000000) := rfl
@[simp] theorem lookup_previous_13_14 : previousPadding literalP (6, 1) (7, 0) = (17651353 / 10000000000) := rfl
@[simp] theorem lookup_current_13_14 : currentPadding literalP (6, 1) (7, 0) = (-5359509 / 5000000000) := rfl
@[simp] theorem lookup_descent_13_15 : literalDescent (6, 1) (7, 1) = (-656519229 / 500000000000) := rfl
@[simp] theorem lookup_previous_13_15 : previousPadding literalP (6, 1) (7, 1) = (-56172897 / 10000000000) := rfl
@[simp] theorem lookup_current_13_15 : currentPadding literalP (6, 1) (7, 1) = (-43042743 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_16 : literalDescent (6, 1) (8, 0) = (-3816111 / 5000000000) := rfl
@[simp] theorem lookup_previous_13_16 : previousPadding literalP (6, 1) (8, 0) = (-11595927 / 10000000000) := rfl
@[simp] theorem lookup_current_13_16 : currentPadding literalP (6, 1) (8, 0) = (-792741 / 2000000000) := rfl
@[simp] theorem lookup_descent_13_17 : literalDescent (6, 1) (8, 1) = (-897981 / 500000000) := rfl
@[simp] theorem lookup_previous_13_17 : previousPadding literalP (6, 1) (8, 1) = (-7987 / 3906250) := rfl
@[simp] theorem lookup_current_13_17 : currentPadding literalP (6, 1) (8, 1) = (-24871 / 100000000) := rfl
@[simp] theorem lookup_descent_13_18 : literalDescent (6, 1) (9, 0) = (1763857 / 2500000000) := rfl
@[simp] theorem lookup_previous_13_18 : previousPadding literalP (6, 1) (9, 0) = (1763857 / 2500000000) := rfl
@[simp] theorem lookup_current_13_18 : currentPadding literalP (6, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_13_19 : literalDescent (6, 1) (9, 1) = (9712881 / 10000000000) := rfl
@[simp] theorem lookup_previous_13_19 : previousPadding literalP (6, 1) (9, 1) = (9712881 / 10000000000) := rfl
@[simp] theorem lookup_current_13_19 : currentPadding literalP (6, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_14_0 : literalDescent (7, 0) (0, 0) = (-14438377 / 10000000000) := rfl
@[simp] theorem lookup_previous_14_0 : previousPadding literalP (7, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_14_0 : currentPadding literalP (7, 0) (0, 0) = (614573 / 625000000) := rfl
@[simp] theorem lookup_descent_14_1 : literalDescent (7, 0) (0, 1) = (-29303481 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_1 : previousPadding literalP (7, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_14_1 : currentPadding literalP (7, 0) (0, 1) = (1255821 / 1250000000) := rfl
@[simp] theorem lookup_descent_14_2 : literalDescent (7, 0) (1, 0) = (-3126711 / 10000000000) := rfl
@[simp] theorem lookup_previous_14_2 : previousPadding literalP (7, 0) (1, 0) = (16845107 / 10000000000) := rfl
@[simp] theorem lookup_current_14_2 : currentPadding literalP (7, 0) (1, 0) = (19971869 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_3 : literalDescent (7, 0) (1, 1) = (23829057 / 31250000000) := rfl
@[simp] theorem lookup_previous_14_3 : previousPadding literalP (7, 0) (1, 1) = (832461 / 1250000000) := rfl
@[simp] theorem lookup_current_14_3 : currentPadding literalP (7, 0) (1, 1) = (727907 / 2000000000) := rfl
@[simp] theorem lookup_descent_14_4 : literalDescent (7, 0) (2, 0) = (19273403 / 2500000000) := rfl
@[simp] theorem lookup_previous_14_4 : previousPadding literalP (7, 0) (2, 0) = (-1106201 / 2000000000) := rfl
@[simp] theorem lookup_current_14_4 : currentPadding literalP (7, 0) (2, 0) = (-82624617 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_5 : literalDescent (7, 0) (2, 1) = (-846131 / 5000000000) := rfl
@[simp] theorem lookup_previous_14_5 : previousPadding literalP (7, 0) (2, 1) = (-22802289 / 10000000000) := rfl
@[simp] theorem lookup_current_14_5 : currentPadding literalP (7, 0) (2, 1) = (-21110027 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_6 : literalDescent (7, 0) (3, 0) = (-10816011 / 2500000000) := rfl
@[simp] theorem lookup_previous_14_6 : previousPadding literalP (7, 0) (3, 0) = (1399817 / 500000000) := rfl
@[simp] theorem lookup_current_14_6 : currentPadding literalP (7, 0) (3, 0) = (2226887 / 312500000) := rfl
@[simp] theorem lookup_descent_14_7 : literalDescent (7, 0) (3, 1) = (-401709279 / 100000000000) := rfl
@[simp] theorem lookup_previous_14_7 : previousPadding literalP (7, 0) (3, 1) = (-3095557 / 5000000000) := rfl
@[simp] theorem lookup_current_14_7 : currentPadding literalP (7, 0) (3, 1) = (339798139 / 100000000000) := rfl
@[simp] theorem lookup_descent_14_8 : literalDescent (7, 0) (4, 0) = (44383001 / 2000000000) := rfl
@[simp] theorem lookup_previous_14_8 : previousPadding literalP (7, 0) (4, 0) = (229493651 / 10000000000) := rfl
@[simp] theorem lookup_current_14_8 : currentPadding literalP (7, 0) (4, 0) = (3789323 / 5000000000) := rfl
@[simp] theorem lookup_descent_14_9 : literalDescent (7, 0) (4, 1) = (106364901 / 10000000000) := rfl
@[simp] theorem lookup_previous_14_9 : previousPadding literalP (7, 0) (4, 1) = (13586017 / 1250000000) := rfl
@[simp] theorem lookup_current_14_9 : currentPadding literalP (7, 0) (4, 1) = (464647 / 2000000000) := rfl
@[simp] theorem lookup_descent_14_10 : literalDescent (7, 0) (5, 0) = (-167163191 / 5000000000) := rfl
@[simp] theorem lookup_previous_14_10 : previousPadding literalP (7, 0) (5, 0) = (-183753291 / 5000000000) := rfl
@[simp] theorem lookup_current_14_10 : currentPadding literalP (7, 0) (5, 0) = (-165901 / 50000000) := rfl
@[simp] theorem lookup_descent_14_11 : literalDescent (7, 0) (5, 1) = (-23064697 / 5000000000) := rfl
@[simp] theorem lookup_previous_14_11 : previousPadding literalP (7, 0) (5, 1) = (-57725321 / 10000000000) := rfl
@[simp] theorem lookup_current_14_11 : currentPadding literalP (7, 0) (5, 1) = (-11595927 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_12 : literalDescent (7, 0) (6, 0) = (-525525547 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_12 : previousPadding literalP (7, 0) (6, 0) = (-6339841 / 200000000) := rfl
@[simp] theorem lookup_current_14_12 : currentPadding literalP (7, 0) (6, 0) = (-27115599 / 5000000000) := rfl
@[simp] theorem lookup_descent_14_13 : literalDescent (7, 0) (6, 1) = (56736899 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_13 : previousPadding literalP (7, 0) (6, 1) = (17651353 / 10000000000) := rfl
@[simp] theorem lookup_current_14_13 : currentPadding literalP (7, 0) (6, 1) = (-5359509 / 5000000000) := rfl
@[simp] theorem lookup_descent_14_14 : literalDescent (7, 0) (7, 0) = (59469337 / 1250000000) := rfl
@[simp] theorem lookup_previous_14_14 : previousPadding literalP (7, 0) (7, 0) = (264273293 / 5000000000) := rfl
@[simp] theorem lookup_current_14_14 : currentPadding literalP (7, 0) (7, 0) = (62006049 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_15 : literalDescent (7, 0) (7, 1) = (19317647 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_15 : previousPadding literalP (7, 0) (7, 1) = (29390699 / 10000000000) := rfl
@[simp] theorem lookup_current_14_15 : currentPadding literalP (7, 0) (7, 1) = (4665737 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_16 : literalDescent (7, 0) (8, 0) = (-116448353 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_16 : previousPadding literalP (7, 0) (8, 0) = (-27115599 / 5000000000) := rfl
@[simp] theorem lookup_current_14_16 : currentPadding literalP (7, 0) (8, 0) = (-614101 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_17 : literalDescent (7, 0) (8, 1) = (-815225399 / 62500000000) := rfl
@[simp] theorem lookup_previous_14_17 : previousPadding literalP (7, 0) (8, 1) = (-6173472429 / 500000000000) := rfl
@[simp] theorem lookup_current_14_17 : currentPadding literalP (7, 0) (8, 1) = (-14954587 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_18 : literalDescent (7, 0) (9, 0) = (-58620849 / 10000000000) := rfl
@[simp] theorem lookup_previous_14_18 : previousPadding literalP (7, 0) (9, 0) = (-58620849 / 10000000000) := rfl
@[simp] theorem lookup_current_14_18 : currentPadding literalP (7, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_14_19 : literalDescent (7, 0) (9, 1) = (20265729 / 2500000000) := rfl
@[simp] theorem lookup_previous_14_19 : previousPadding literalP (7, 0) (9, 1) = (20265729 / 2500000000) := rfl
@[simp] theorem lookup_current_14_19 : currentPadding literalP (7, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_15_0 : literalDescent (7, 1) (0, 0) = (-7674837 / 62500000000) := rfl
@[simp] theorem lookup_previous_15_0 : previousPadding literalP (7, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_15_0 : currentPadding literalP (7, 1) (0, 0) = (3647523 / 1250000000) := rfl
@[simp] theorem lookup_descent_15_1 : literalDescent (7, 1) (0, 1) = (34092427 / 250000000000) := rfl
@[simp] theorem lookup_previous_15_1 : previousPadding literalP (7, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_15_1 : currentPadding literalP (7, 1) (0, 1) = (2305799 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_2 : literalDescent (7, 1) (1, 0) = (-10258293 / 20000000000) := rfl
@[simp] theorem lookup_previous_15_2 : previousPadding literalP (7, 1) (1, 0) = (-10863883 / 5000000000) := rfl
@[simp] theorem lookup_current_15_2 : currentPadding literalP (7, 1) (1, 0) = (-12438443 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_3 : literalDescent (7, 1) (1, 1) = (-5497253 / 500000000000) := rfl
@[simp] theorem lookup_previous_15_3 : previousPadding literalP (7, 1) (1, 1) = (-1098609 / 500000000) := rfl
@[simp] theorem lookup_current_15_3 : currentPadding literalP (7, 1) (1, 1) = (-996859 / 1000000000) := rfl
@[simp] theorem lookup_descent_15_4 : literalDescent (7, 1) (2, 0) = (3987261 / 2500000000) := rfl
@[simp] theorem lookup_previous_15_4 : previousPadding literalP (7, 1) (2, 0) = (134971 / 39062500) := rfl
@[simp] theorem lookup_current_15_4 : currentPadding literalP (7, 1) (2, 0) = (4650883 / 2500000000) := rfl
@[simp] theorem lookup_descent_15_5 : literalDescent (7, 1) (2, 1) = (8201799 / 10000000000) := rfl
@[simp] theorem lookup_previous_15_5 : previousPadding literalP (7, 1) (2, 1) = (41130273 / 10000000000) := rfl
@[simp] theorem lookup_current_15_5 : currentPadding literalP (7, 1) (2, 1) = (16464237 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_6 : literalDescent (7, 1) (3, 0) = (-10065821 / 2000000000) := rfl
@[simp] theorem lookup_previous_15_6 : previousPadding literalP (7, 1) (3, 0) = (-162492897 / 10000000000) := rfl
@[simp] theorem lookup_current_15_6 : currentPadding literalP (7, 1) (3, 0) = (-7010237 / 625000000) := rfl
@[simp] theorem lookup_descent_15_7 : literalDescent (7, 1) (3, 1) = (-1968693 / 2000000000) := rfl
@[simp] theorem lookup_previous_15_7 : previousPadding literalP (7, 1) (3, 1) = (-26818913 / 10000000000) := rfl
@[simp] theorem lookup_current_15_7 : currentPadding literalP (7, 1) (3, 1) = (-2121931 / 1250000000) := rfl
@[simp] theorem lookup_descent_15_8 : literalDescent (7, 1) (4, 0) = (1477499 / 1000000000) := rfl
@[simp] theorem lookup_previous_15_8 : previousPadding literalP (7, 1) (4, 0) = (14958959 / 10000000000) := rfl
@[simp] theorem lookup_current_15_8 : currentPadding literalP (7, 1) (4, 0) = (183969 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_9 : literalDescent (7, 1) (4, 1) = (555111 / 1250000000) := rfl
@[simp] theorem lookup_previous_15_9 : previousPadding literalP (7, 1) (4, 1) = (2884551 / 5000000000) := rfl
@[simp] theorem lookup_current_15_9 : currentPadding literalP (7, 1) (4, 1) = (664107 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_10 : literalDescent (7, 1) (5, 0) = (3845579287 / 500000000000) := rfl
@[simp] theorem lookup_previous_15_10 : previousPadding literalP (7, 1) (5, 0) = (3679895179 / 125000000000) := rfl
@[simp] theorem lookup_current_15_10 : currentPadding literalP (7, 1) (5, 0) = (10874001429 / 500000000000) := rfl
@[simp] theorem lookup_descent_15_11 : literalDescent (7, 1) (5, 1) = (-12710103 / 10000000000) := rfl
@[simp] theorem lookup_previous_15_11 : previousPadding literalP (7, 1) (5, 1) = (-33156823 / 10000000000) := rfl
@[simp] theorem lookup_current_15_11 : currentPadding literalP (7, 1) (5, 1) = (-7987 / 3906250) := rfl
@[simp] theorem lookup_descent_15_12 : literalDescent (7, 1) (6, 0) = (-1273043483 / 250000000000) := rfl
@[simp] theorem lookup_previous_15_12 : previousPadding literalP (7, 1) (6, 0) = (-2179880779 / 125000000000) := rfl
@[simp] theorem lookup_current_15_12 : currentPadding literalP (7, 1) (6, 0) = (-6173472429 / 500000000000) := rfl
@[simp] theorem lookup_descent_15_13 : literalDescent (7, 1) (6, 1) = (-656519229 / 500000000000) := rfl
@[simp] theorem lookup_previous_15_13 : previousPadding literalP (7, 1) (6, 1) = (-56172897 / 10000000000) := rfl
@[simp] theorem lookup_current_15_13 : currentPadding literalP (7, 1) (6, 1) = (-43042743 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_14 : literalDescent (7, 1) (7, 0) = (19317647 / 20000000000) := rfl
@[simp] theorem lookup_previous_15_14 : previousPadding literalP (7, 1) (7, 0) = (29390699 / 10000000000) := rfl
@[simp] theorem lookup_current_15_14 : currentPadding literalP (7, 1) (7, 0) = (4665737 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_15 : literalDescent (7, 1) (7, 1) = (341356021 / 100000000000) := rfl
@[simp] theorem lookup_previous_15_15 : previousPadding literalP (7, 1) (7, 1) = (3029791413 / 250000000000) := rfl
@[simp] theorem lookup_current_15_15 : currentPadding literalP (7, 1) (7, 1) = (4813341579 / 500000000000) := rfl
@[simp] theorem lookup_descent_15_16 : literalDescent (7, 1) (8, 0) = (-11445547 / 20000000000) := rfl
@[simp] theorem lookup_previous_15_16 : previousPadding literalP (7, 1) (8, 0) = (-5359509 / 5000000000) := rfl
@[simp] theorem lookup_current_15_16 : currentPadding literalP (7, 1) (8, 0) = (-2400831 / 2500000000) := rfl
@[simp] theorem lookup_descent_15_17 : literalDescent (7, 1) (8, 1) = (-493049427 / 500000000000) := rfl
@[simp] theorem lookup_previous_15_17 : previousPadding literalP (7, 1) (8, 1) = (-43042743 / 10000000000) := rfl
@[simp] theorem lookup_current_15_17 : currentPadding literalP (7, 1) (8, 1) = (-8433651 / 2500000000) := rfl
@[simp] theorem lookup_descent_15_18 : literalDescent (7, 1) (9, 0) = (-792741 / 2000000000) := rfl
@[simp] theorem lookup_previous_15_18 : previousPadding literalP (7, 1) (9, 0) = (-792741 / 2000000000) := rfl
@[simp] theorem lookup_current_15_18 : currentPadding literalP (7, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_15_19 : literalDescent (7, 1) (9, 1) = (-24871 / 100000000) := rfl
@[simp] theorem lookup_previous_15_19 : previousPadding literalP (7, 1) (9, 1) = (-24871 / 100000000) := rfl
@[simp] theorem lookup_current_15_19 : currentPadding literalP (7, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_16_0 : literalDescent (8, 0) (0, 0) = (2596341 / 5000000000) := rfl
@[simp] theorem lookup_previous_16_0 : previousPadding literalP (8, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_16_0 : currentPadding literalP (8, 0) (0, 0) = (-8449483 / 5000000000) := rfl
@[simp] theorem lookup_descent_16_1 : literalDescent (8, 0) (0, 1) = (-7745859 / 20000000000) := rfl
@[simp] theorem lookup_previous_16_1 : previousPadding literalP (8, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_16_1 : currentPadding literalP (8, 0) (0, 1) = (-7833271 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_2 : literalDescent (8, 0) (1, 0) = (5052613 / 4000000000) := rfl
@[simp] theorem lookup_previous_16_2 : previousPadding literalP (8, 0) (1, 0) = (614573 / 625000000) := rfl
@[simp] theorem lookup_current_16_2 : currentPadding literalP (8, 0) (1, 0) = (2183743 / 5000000000) := rfl
@[simp] theorem lookup_descent_16_3 : literalDescent (8, 0) (1, 1) = (405227427 / 500000000000) := rfl
@[simp] theorem lookup_previous_16_3 : previousPadding literalP (8, 0) (1, 1) = (1255821 / 1250000000) := rfl
@[simp] theorem lookup_current_16_3 : currentPadding literalP (8, 0) (1, 1) = (88289 / 5000000000) := rfl
@[simp] theorem lookup_descent_16_4 : literalDescent (8, 0) (2, 0) = (-28141411 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_4 : previousPadding literalP (8, 0) (2, 0) = (19971869 / 10000000000) := rfl
@[simp] theorem lookup_current_16_4 : currentPadding literalP (8, 0) (2, 0) = (75177 / 15625000) := rfl
@[simp] theorem lookup_descent_16_5 : literalDescent (8, 0) (2, 1) = (-216261 / 2500000000) := rfl
@[simp] theorem lookup_previous_16_5 : previousPadding literalP (8, 0) (2, 1) = (727907 / 2000000000) := rfl
@[simp] theorem lookup_current_16_5 : currentPadding literalP (8, 0) (2, 1) = (4504579 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_6 : literalDescent (8, 0) (3, 0) = (-6136147 / 2500000000) := rfl
@[simp] theorem lookup_previous_16_6 : previousPadding literalP (8, 0) (3, 0) = (-82624617 / 10000000000) := rfl
@[simp] theorem lookup_current_16_6 : currentPadding literalP (8, 0) (3, 0) = (-58080029 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_7 : literalDescent (8, 0) (3, 1) = (149869 / 2500000000) := rfl
@[simp] theorem lookup_previous_16_7 : previousPadding literalP (8, 0) (3, 1) = (-21110027 / 10000000000) := rfl
@[simp] theorem lookup_current_16_7 : currentPadding literalP (8, 0) (3, 1) = (-21709503 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_8 : literalDescent (8, 0) (4, 0) = (161077 / 80000000) := rfl
@[simp] theorem lookup_previous_16_8 : previousPadding literalP (8, 0) (4, 0) = (2226887 / 312500000) := rfl
@[simp] theorem lookup_current_16_8 : currentPadding literalP (8, 0) (4, 0) = (51125759 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_9 : literalDescent (8, 0) (4, 1) = (-10199761 / 100000000000) := rfl
@[simp] theorem lookup_previous_16_9 : previousPadding literalP (8, 0) (4, 1) = (339798139 / 100000000000) := rfl
@[simp] theorem lookup_current_16_9 : currentPadding literalP (8, 0) (4, 1) = (3499979 / 1000000000) := rfl
@[simp] theorem lookup_descent_16_10 : literalDescent (8, 0) (5, 0) = (13057689 / 5000000000) := rfl
@[simp] theorem lookup_previous_16_10 : previousPadding literalP (8, 0) (5, 0) = (3789323 / 5000000000) := rfl
@[simp] theorem lookup_current_16_10 : currentPadding literalP (8, 0) (5, 0) = (-4634183 / 2500000000) := rfl
@[simp] theorem lookup_descent_16_11 : literalDescent (8, 0) (5, 1) = (-4732193 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_11 : previousPadding literalP (8, 0) (5, 1) = (464647 / 2000000000) := rfl
@[simp] theorem lookup_current_16_11 : currentPadding literalP (8, 0) (5, 1) = (1763857 / 2500000000) := rfl
@[simp] theorem lookup_descent_16_12 : literalDescent (8, 0) (6, 0) = (25440649 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_12 : previousPadding literalP (8, 0) (6, 0) = (-165901 / 50000000) := rfl
@[simp] theorem lookup_current_16_12 : currentPadding literalP (8, 0) (6, 0) = (-58620849 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_13 : literalDescent (8, 0) (6, 1) = (-3816111 / 5000000000) := rfl
@[simp] theorem lookup_previous_16_13 : previousPadding literalP (8, 0) (6, 1) = (-11595927 / 10000000000) := rfl
@[simp] theorem lookup_current_16_13 : currentPadding literalP (8, 0) (6, 1) = (-792741 / 2000000000) := rfl
@[simp] theorem lookup_descent_16_14 : literalDescent (8, 0) (7, 0) = (-116448353 / 20000000000) := rfl
@[simp] theorem lookup_previous_16_14 : previousPadding literalP (8, 0) (7, 0) = (-27115599 / 5000000000) := rfl
@[simp] theorem lookup_current_16_14 : currentPadding literalP (8, 0) (7, 0) = (-614101 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_15 : literalDescent (8, 0) (7, 1) = (-11445547 / 20000000000) := rfl
@[simp] theorem lookup_previous_16_15 : previousPadding literalP (8, 0) (7, 1) = (-5359509 / 5000000000) := rfl
@[simp] theorem lookup_current_16_15 : currentPadding literalP (8, 0) (7, 1) = (-2400831 / 2500000000) := rfl
@[simp] theorem lookup_descent_16_16 : literalDescent (8, 0) (8, 0) = (31156923 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_16 : previousPadding literalP (8, 0) (8, 0) = (62006049 / 10000000000) := rfl
@[simp] theorem lookup_current_16_16 : currentPadding literalP (8, 0) (8, 0) = (6143019 / 1250000000) := rfl
@[simp] theorem lookup_descent_16_17 : literalDescent (8, 0) (8, 1) = (7798469 / 2500000000) := rfl
@[simp] theorem lookup_previous_16_17 : previousPadding literalP (8, 0) (8, 1) = (4665737 / 10000000000) := rfl
@[simp] theorem lookup_current_16_17 : currentPadding literalP (8, 0) (8, 1) = (-906643 / 2500000000) := rfl
@[simp] theorem lookup_descent_16_18 : literalDescent (8, 0) (9, 0) = (-4880807 / 5000000000) := rfl
@[simp] theorem lookup_previous_16_18 : previousPadding literalP (8, 0) (9, 0) = (-614101 / 10000000000) := rfl
@[simp] theorem lookup_current_16_18 : currentPadding literalP (8, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_16_19 : literalDescent (8, 0) (9, 1) = (-401319061 / 250000000000) := rfl
@[simp] theorem lookup_previous_16_19 : previousPadding literalP (8, 0) (9, 1) = (-14954587 / 10000000000) := rfl
@[simp] theorem lookup_current_16_19 : currentPadding literalP (8, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_17_0 : literalDescent (8, 1) (0, 0) = (-24718453 / 125000000000) := rfl
@[simp] theorem lookup_previous_17_0 : previousPadding literalP (8, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_17_0 : currentPadding literalP (8, 1) (0, 0) = (119153 / 400000000) := rfl
@[simp] theorem lookup_descent_17_1 : literalDescent (8, 1) (0, 1) = (-113038573 / 500000000000) := rfl
@[simp] theorem lookup_previous_17_1 : previousPadding literalP (8, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_17_1 : currentPadding literalP (8, 1) (0, 1) = (-18106771 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_2 : literalDescent (8, 1) (1, 0) = (31750081 / 20000000000) := rfl
@[simp] theorem lookup_previous_17_2 : previousPadding literalP (8, 1) (1, 0) = (3647523 / 1250000000) := rfl
@[simp] theorem lookup_current_17_2 : currentPadding literalP (8, 1) (1, 0) = (20470943 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_3 : literalDescent (8, 1) (1, 1) = (45271837 / 50000000000) := rfl
@[simp] theorem lookup_previous_17_3 : previousPadding literalP (8, 1) (1, 1) = (2305799 / 10000000000) := rfl
@[simp] theorem lookup_current_17_3 : currentPadding literalP (8, 1) (1, 1) = (147271 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_4 : literalDescent (8, 1) (2, 0) = (-30500963 / 10000000000) := rfl
@[simp] theorem lookup_previous_17_4 : previousPadding literalP (8, 1) (2, 0) = (-12438443 / 5000000000) := rfl
@[simp] theorem lookup_current_17_4 : currentPadding literalP (8, 1) (2, 0) = (5624077 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_5 : literalDescent (8, 1) (2, 1) = (-436073 / 2000000000) := rfl
@[simp] theorem lookup_previous_17_5 : previousPadding literalP (8, 1) (2, 1) = (-996859 / 1000000000) := rfl
@[simp] theorem lookup_current_17_5 : currentPadding literalP (8, 1) (2, 1) = (-311529 / 400000000) := rfl
@[simp] theorem lookup_descent_17_6 : literalDescent (8, 1) (3, 0) = (-1301519 / 2000000000) := rfl
@[simp] theorem lookup_previous_17_6 : previousPadding literalP (8, 1) (3, 0) = (4650883 / 2500000000) := rfl
@[simp] theorem lookup_current_17_6 : currentPadding literalP (8, 1) (3, 0) = (25111127 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_7 : literalDescent (8, 1) (3, 1) = (17539569 / 10000000000) := rfl
@[simp] theorem lookup_previous_17_7 : previousPadding literalP (8, 1) (3, 1) = (16464237 / 5000000000) := rfl
@[simp] theorem lookup_current_17_7 : currentPadding literalP (8, 1) (3, 1) = (3077781 / 2000000000) := rfl
@[simp] theorem lookup_descent_17_8 : literalDescent (8, 1) (4, 0) = (-17267 / 3125000) := rfl
@[simp] theorem lookup_previous_17_8 : previousPadding literalP (8, 1) (4, 0) = (-7010237 / 625000000) := rfl
@[simp] theorem lookup_current_17_8 : currentPadding literalP (8, 1) (4, 0) = (-3556837 / 625000000) := rfl
@[simp] theorem lookup_descent_17_9 : literalDescent (8, 1) (4, 1) = (-4174011 / 2000000000) := rfl
@[simp] theorem lookup_previous_17_9 : previousPadding literalP (8, 1) (4, 1) = (-2121931 / 1250000000) := rfl
@[simp] theorem lookup_current_17_9 : currentPadding literalP (8, 1) (4, 1) = (3894607 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_10 : literalDescent (8, 1) (5, 0) = (29970653 / 5000000000) := rfl
@[simp] theorem lookup_previous_17_10 : previousPadding literalP (8, 1) (5, 0) = (183969 / 10000000000) := rfl
@[simp] theorem lookup_current_17_10 : currentPadding literalP (8, 1) (5, 0) = (-59757337 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_11 : literalDescent (8, 1) (5, 1) = (-8384667 / 10000000000) := rfl
@[simp] theorem lookup_previous_17_11 : previousPadding literalP (8, 1) (5, 1) = (664107 / 5000000000) := rfl
@[simp] theorem lookup_current_17_11 : currentPadding literalP (8, 1) (5, 1) = (9712881 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_12 : literalDescent (8, 1) (6, 0) = (6820855629 / 500000000000) := rfl
@[simp] theorem lookup_previous_17_12 : previousPadding literalP (8, 1) (6, 0) = (10874001429 / 500000000000) := rfl
@[simp] theorem lookup_current_17_12 : currentPadding literalP (8, 1) (6, 0) = (20265729 / 2500000000) := rfl
@[simp] theorem lookup_descent_17_13 : literalDescent (8, 1) (6, 1) = (-897981 / 500000000) := rfl
@[simp] theorem lookup_previous_17_13 : previousPadding literalP (8, 1) (6, 1) = (-7987 / 3906250) := rfl
@[simp] theorem lookup_current_17_13 : currentPadding literalP (8, 1) (6, 1) = (-24871 / 100000000) := rfl
@[simp] theorem lookup_descent_17_14 : literalDescent (8, 1) (7, 0) = (-815225399 / 62500000000) := rfl
@[simp] theorem lookup_previous_17_14 : previousPadding literalP (8, 1) (7, 0) = (-6173472429 / 500000000000) := rfl
@[simp] theorem lookup_current_17_14 : currentPadding literalP (8, 1) (7, 0) = (-14954587 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_15 : literalDescent (8, 1) (7, 1) = (-493049427 / 500000000000) := rfl
@[simp] theorem lookup_previous_17_15 : previousPadding literalP (8, 1) (7, 1) = (-43042743 / 10000000000) := rfl
@[simp] theorem lookup_current_17_15 : currentPadding literalP (8, 1) (7, 1) = (-8433651 / 2500000000) := rfl
@[simp] theorem lookup_descent_17_16 : literalDescent (8, 1) (8, 0) = (7798469 / 2500000000) := rfl
@[simp] theorem lookup_previous_17_16 : previousPadding literalP (8, 1) (8, 0) = (4665737 / 10000000000) := rfl
@[simp] theorem lookup_current_17_16 : currentPadding literalP (8, 1) (8, 0) = (-906643 / 2500000000) := rfl
@[simp] theorem lookup_descent_17_17 : literalDescent (8, 1) (8, 1) = (217983863 / 31250000000) := rfl
@[simp] theorem lookup_previous_17_17 : previousPadding literalP (8, 1) (8, 1) = (4813341579 / 500000000000) := rfl
@[simp] theorem lookup_current_17_17 : currentPadding literalP (8, 1) (8, 1) = (73397123 / 20000000000) := rfl
@[simp] theorem lookup_descent_17_18 : literalDescent (8, 1) (9, 0) = (-18750837 / 10000000000) := rfl
@[simp] theorem lookup_previous_17_18 : previousPadding literalP (8, 1) (9, 0) = (-2400831 / 2500000000) := rfl
@[simp] theorem lookup_current_17_18 : currentPadding literalP (8, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_17_19 : literalDescent (8, 1) (9, 1) = (-870807639 / 250000000000) := rfl
@[simp] theorem lookup_previous_17_19 : previousPadding literalP (8, 1) (9, 1) = (-8433651 / 2500000000) := rfl
@[simp] theorem lookup_current_17_19 : currentPadding literalP (8, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_0 : literalDescent (9, 0) (0, 0) = (9147513 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_0 : previousPadding literalP (9, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_18_0 : currentPadding literalP (9, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_1 : literalDescent (9, 0) (0, 1) = (9147513 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_1 : previousPadding literalP (9, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_18_1 : currentPadding literalP (9, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_2 : literalDescent (9, 0) (1, 0) = (-8449483 / 5000000000) := rfl
@[simp] theorem lookup_previous_18_2 : previousPadding literalP (9, 0) (1, 0) = (-8449483 / 5000000000) := rfl
@[simp] theorem lookup_current_18_2 : currentPadding literalP (9, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_3 : literalDescent (9, 0) (1, 1) = (-1061299 / 625000000) := rfl
@[simp] theorem lookup_previous_18_3 : previousPadding literalP (9, 0) (1, 1) = (-7833271 / 10000000000) := rfl
@[simp] theorem lookup_current_18_3 : currentPadding literalP (9, 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_4 : literalDescent (9, 0) (2, 0) = (2183743 / 5000000000) := rfl
@[simp] theorem lookup_previous_18_4 : previousPadding literalP (9, 0) (2, 0) = (2183743 / 5000000000) := rfl
@[simp] theorem lookup_current_18_4 : currentPadding literalP (9, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_5 : literalDescent (9, 0) (2, 1) = (88289 / 5000000000) := rfl
@[simp] theorem lookup_previous_18_5 : previousPadding literalP (9, 0) (2, 1) = (88289 / 5000000000) := rfl
@[simp] theorem lookup_current_18_5 : currentPadding literalP (9, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_6 : literalDescent (9, 0) (3, 0) = (75177 / 15625000) := rfl
@[simp] theorem lookup_previous_18_6 : previousPadding literalP (9, 0) (3, 0) = (75177 / 15625000) := rfl
@[simp] theorem lookup_current_18_6 : currentPadding literalP (9, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_7 : literalDescent (9, 0) (3, 1) = (4504579 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_7 : previousPadding literalP (9, 0) (3, 1) = (4504579 / 10000000000) := rfl
@[simp] theorem lookup_current_18_7 : currentPadding literalP (9, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_8 : literalDescent (9, 0) (4, 0) = (-58080029 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_8 : previousPadding literalP (9, 0) (4, 0) = (-58080029 / 10000000000) := rfl
@[simp] theorem lookup_current_18_8 : currentPadding literalP (9, 0) (4, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_9 : literalDescent (9, 0) (4, 1) = (-21709503 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_9 : previousPadding literalP (9, 0) (4, 1) = (-21709503 / 10000000000) := rfl
@[simp] theorem lookup_current_18_9 : currentPadding literalP (9, 0) (4, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_10 : literalDescent (9, 0) (5, 0) = (51125759 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_10 : previousPadding literalP (9, 0) (5, 0) = (51125759 / 10000000000) := rfl
@[simp] theorem lookup_current_18_10 : currentPadding literalP (9, 0) (5, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_11 : literalDescent (9, 0) (5, 1) = (3499979 / 1000000000) := rfl
@[simp] theorem lookup_previous_18_11 : previousPadding literalP (9, 0) (5, 1) = (3499979 / 1000000000) := rfl
@[simp] theorem lookup_current_18_11 : currentPadding literalP (9, 0) (5, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_12 : literalDescent (9, 0) (6, 0) = (-4634183 / 2500000000) := rfl
@[simp] theorem lookup_previous_18_12 : previousPadding literalP (9, 0) (6, 0) = (-4634183 / 2500000000) := rfl
@[simp] theorem lookup_current_18_12 : currentPadding literalP (9, 0) (6, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_13 : literalDescent (9, 0) (6, 1) = (1763857 / 2500000000) := rfl
@[simp] theorem lookup_previous_18_13 : previousPadding literalP (9, 0) (6, 1) = (1763857 / 2500000000) := rfl
@[simp] theorem lookup_current_18_13 : currentPadding literalP (9, 0) (6, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_14 : literalDescent (9, 0) (7, 0) = (-58620849 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_14 : previousPadding literalP (9, 0) (7, 0) = (-58620849 / 10000000000) := rfl
@[simp] theorem lookup_current_18_14 : currentPadding literalP (9, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_15 : literalDescent (9, 0) (7, 1) = (-792741 / 2000000000) := rfl
@[simp] theorem lookup_previous_18_15 : previousPadding literalP (9, 0) (7, 1) = (-792741 / 2000000000) := rfl
@[simp] theorem lookup_current_18_15 : currentPadding literalP (9, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_16 : literalDescent (9, 0) (8, 0) = (-4880807 / 5000000000) := rfl
@[simp] theorem lookup_previous_18_16 : previousPadding literalP (9, 0) (8, 0) = (-614101 / 10000000000) := rfl
@[simp] theorem lookup_current_18_16 : currentPadding literalP (9, 0) (8, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_17 : literalDescent (9, 0) (8, 1) = (-18750837 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_17 : previousPadding literalP (9, 0) (8, 1) = (-2400831 / 2500000000) := rfl
@[simp] theorem lookup_current_18_17 : currentPadding literalP (9, 0) (8, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_18 : literalDescent (9, 0) (9, 0) = (6143019 / 1250000000) := rfl
@[simp] theorem lookup_previous_18_18 : previousPadding literalP (9, 0) (9, 0) = (6143019 / 1250000000) := rfl
@[simp] theorem lookup_current_18_18 : currentPadding literalP (9, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_19 : literalDescent (9, 0) (9, 1) = (5520941 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_19 : previousPadding literalP (9, 0) (9, 1) = (-906643 / 2500000000) := rfl
@[simp] theorem lookup_current_18_19 : currentPadding literalP (9, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_0 : literalDescent (9, 1) (0, 0) = (-44174353 / 500000000000) := rfl
@[simp] theorem lookup_previous_19_0 : previousPadding literalP (9, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_19_0 : currentPadding literalP (9, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_1 : literalDescent (9, 1) (0, 1) = (-44198047 / 500000000000) := rfl
@[simp] theorem lookup_previous_19_1 : previousPadding literalP (9, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_19_1 : currentPadding literalP (9, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_2 : literalDescent (9, 1) (1, 0) = (-8374051 / 20000000000) := rfl
@[simp] theorem lookup_previous_19_2 : previousPadding literalP (9, 1) (1, 0) = (119153 / 400000000) := rfl
@[simp] theorem lookup_current_19_2 : currentPadding literalP (9, 1) (1, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_3 : literalDescent (9, 1) (1, 1) = (-46887639 / 125000000000) := rfl
@[simp] theorem lookup_previous_19_3 : previousPadding literalP (9, 1) (1, 1) = (-18106771 / 10000000000) := rfl
@[simp] theorem lookup_current_19_3 : currentPadding literalP (9, 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_4 : literalDescent (9, 1) (2, 0) = (20470943 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_4 : previousPadding literalP (9, 1) (2, 0) = (20470943 / 10000000000) := rfl
@[simp] theorem lookup_current_19_4 : currentPadding literalP (9, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_5 : literalDescent (9, 1) (2, 1) = (147271 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_5 : previousPadding literalP (9, 1) (2, 1) = (147271 / 10000000000) := rfl
@[simp] theorem lookup_current_19_5 : currentPadding literalP (9, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_6 : literalDescent (9, 1) (3, 0) = (5624077 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_6 : previousPadding literalP (9, 1) (3, 0) = (5624077 / 10000000000) := rfl
@[simp] theorem lookup_current_19_6 : currentPadding literalP (9, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_7 : literalDescent (9, 1) (3, 1) = (-311529 / 400000000) := rfl
@[simp] theorem lookup_previous_19_7 : previousPadding literalP (9, 1) (3, 1) = (-311529 / 400000000) := rfl
@[simp] theorem lookup_current_19_7 : currentPadding literalP (9, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_8 : literalDescent (9, 1) (4, 0) = (25111127 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_8 : previousPadding literalP (9, 1) (4, 0) = (25111127 / 10000000000) := rfl
@[simp] theorem lookup_current_19_8 : currentPadding literalP (9, 1) (4, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_9 : literalDescent (9, 1) (4, 1) = (3077781 / 2000000000) := rfl
@[simp] theorem lookup_previous_19_9 : previousPadding literalP (9, 1) (4, 1) = (3077781 / 2000000000) := rfl
@[simp] theorem lookup_current_19_9 : currentPadding literalP (9, 1) (4, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_10 : literalDescent (9, 1) (5, 0) = (-3556837 / 625000000) := rfl
@[simp] theorem lookup_previous_19_10 : previousPadding literalP (9, 1) (5, 0) = (-3556837 / 625000000) := rfl
@[simp] theorem lookup_current_19_10 : currentPadding literalP (9, 1) (5, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_11 : literalDescent (9, 1) (5, 1) = (3894607 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_11 : previousPadding literalP (9, 1) (5, 1) = (3894607 / 10000000000) := rfl
@[simp] theorem lookup_current_19_11 : currentPadding literalP (9, 1) (5, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_12 : literalDescent (9, 1) (6, 0) = (-59757337 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_12 : previousPadding literalP (9, 1) (6, 0) = (-59757337 / 10000000000) := rfl
@[simp] theorem lookup_current_19_12 : currentPadding literalP (9, 1) (6, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_13 : literalDescent (9, 1) (6, 1) = (9712881 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_13 : previousPadding literalP (9, 1) (6, 1) = (9712881 / 10000000000) := rfl
@[simp] theorem lookup_current_19_13 : currentPadding literalP (9, 1) (6, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_14 : literalDescent (9, 1) (7, 0) = (20265729 / 2500000000) := rfl
@[simp] theorem lookup_previous_19_14 : previousPadding literalP (9, 1) (7, 0) = (20265729 / 2500000000) := rfl
@[simp] theorem lookup_current_19_14 : currentPadding literalP (9, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_15 : literalDescent (9, 1) (7, 1) = (-24871 / 100000000) := rfl
@[simp] theorem lookup_previous_19_15 : previousPadding literalP (9, 1) (7, 1) = (-24871 / 100000000) := rfl
@[simp] theorem lookup_current_19_15 : currentPadding literalP (9, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_16 : literalDescent (9, 1) (8, 0) = (-401319061 / 250000000000) := rfl
@[simp] theorem lookup_previous_19_16 : previousPadding literalP (9, 1) (8, 0) = (-14954587 / 10000000000) := rfl
@[simp] theorem lookup_current_19_16 : currentPadding literalP (9, 1) (8, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_17 : literalDescent (9, 1) (8, 1) = (-870807639 / 250000000000) := rfl
@[simp] theorem lookup_previous_19_17 : previousPadding literalP (9, 1) (8, 1) = (-8433651 / 2500000000) := rfl
@[simp] theorem lookup_current_19_17 : currentPadding literalP (9, 1) (8, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_18 : literalDescent (9, 1) (9, 0) = (5520941 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_18 : previousPadding literalP (9, 1) (9, 0) = (-906643 / 2500000000) := rfl
@[simp] theorem lookup_current_19_18 : currentPadding literalP (9, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_19 : literalDescent (9, 1) (9, 1) = (1029946931 / 500000000000) := rfl
@[simp] theorem lookup_previous_19_19 : previousPadding literalP (9, 1) (9, 1) = (73397123 / 20000000000) := rfl
@[simp] theorem lookup_current_19_19 : currentPadding literalP (9, 1) (9, 1) = 0 := rfl

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.MatrixBridge
