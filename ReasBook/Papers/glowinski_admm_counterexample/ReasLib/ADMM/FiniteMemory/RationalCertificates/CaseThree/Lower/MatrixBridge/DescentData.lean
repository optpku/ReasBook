module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Lower.MatrixBridge.Lookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixDescent

@[expose] public section
set_option maxRecDepth 4096
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Lower.MatrixBridge
open MatrixAssembly

-- These candidates become certificates only through the subsequent Lean proofs.
def literalDescentData : List (List ℚ) := [
  [(3926439 / 1250000000), (989663 / 2400000000), (-10855219 / 2000000000), (-7054425209 / 6000000000000), (-3795193 / 20000000000), (542438513 / 400000000000), (92536843 / 20000000000), (-1116259227 / 2000000000000), (-26536701 / 20000000000), (-1211312239 / 1000000000000), (175693 / 800000000), (1339159969 / 1000000000000), (-12650727 / 10000000000), (150821561 / 2000000000000), (-2502637 / 2500000000), (200012567 / 1000000000000), (769927 / 2500000000), (-717316127 / 2000000000000), (9147513 / 10000000000), (-158403463 / 2000000000000)],
  [(989663 / 2400000000), (181933127 / 250000000000), (-4338513333 / 2000000000000), (-1318771633 / 2000000000000), (15563653 / 60000000000), (-20618837 / 80000000000), (6472026433 / 2000000000000), (-250996881 / 2000000000000), (-2587887 / 2500000000), (-198640463 / 400000000000), (-46089 / 2000000000), (774265751 / 1000000000000), (2078807 / 20000000000), (25877267 / 125000000000), (-18622063 / 20000000000), (348008459 / 2000000000000), (-15357991 / 20000000000), (-529102333 / 2000000000000), (9147513 / 10000000000), (-79248581 / 1000000000000)],
  [(-10855219 / 2000000000), (-4338513333 / 2000000000000), (159499529 / 10000000000), (10400633803 / 3000000000000), (-59184843 / 10000000000), (-15623772467 / 6000000000000), (-55597171 / 4000000000), (133225913 / 50000000000), (82427149 / 10000000000), (39839541 / 20000000000), (-423479 / 800000000), (-728569 / 160000000), (327849 / 160000000), (8410359 / 10000000000), (-327987 / 2000000000), (-720677 / 800000000), (23512079 / 20000000000), (30813587 / 20000000000), (-1848249 / 1250000000), (-1109869 / 4000000000)],
  [(-7054425209 / 6000000000000), (-1318771633 / 2000000000000), (10400633803 / 3000000000000), (3139212641 / 2000000000000), (-2505824989 / 1000000000000), (-1518912019 / 2000000000000), (-1711904193 / 500000000000), (115896837 / 2000000000000), (4172755977 / 1000000000000), (3517497 / 10000000000), (-87087103 / 250000000000), (-104732131 / 80000000000), (159508751 / 1000000000000), (220195267 / 500000000000), (14165477 / 2000000000000), (-66169397 / 500000000000), (964965721 / 1000000000000), (39448533 / 50000000000), (-6587359 / 5000000000), (-696666751 / 2000000000000)],
  [(-3795193 / 20000000000), (15563653 / 60000000000), (-59184843 / 10000000000), (-2505824989 / 1000000000000), (172515093 / 10000000000), (18866212241 / 6000000000000), (-99130827 / 20000000000), (-5868336873 / 2000000000000), (-13748689 / 1000000000), (1720134901 / 500000000000), (15288967 / 2500000000), (22425197 / 10000000000), (-21767951 / 10000000000), (-8698681 / 2000000000), (26578337 / 5000000000), (6125423 / 5000000000), (-17740091 / 10000000000), (-4586827 / 2000000000), (16303 / 200000000), (17296 / 9765625)],
  [(542438513 / 400000000000), (-20618837 / 80000000000), (-15623772467 / 6000000000000), (-1518912019 / 2000000000000), (18866212241 / 6000000000000), (4683271663 / 2000000000000), (-41833657 / 20000000000), (-2223985719 / 2000000000000), (-29068501 / 10000000000), (-2616127 / 10000000000), (8871209677 / 2000000000000), (2631679 / 5000000000), (-1245337 / 625000000), (-13300741 / 10000000000), (1533097 / 2500000000), (354779 / 312500000), (3547419 / 5000000000), (-1892563 / 5000000000), (-3318791 / 5000000000), (961193 / 10000000000)],
  [(92536843 / 20000000000), (6472026433 / 2000000000000), (-55597171 / 4000000000), (-1711904193 / 500000000000), (-99130827 / 20000000000), (-41833657 / 20000000000), (170682071 / 5000000000), (1113087187 / 500000000000), (-219171183 / 20000000000), (-5553811961 / 1000000000000), (-6814203 / 400000000), (13599221613 / 2000000000000), (104202629 / 10000000000), (3210901 / 1000000000), (-26563309 / 10000000000), (-49239659 / 10000000000), (-35522463 / 10000000000), (113213 / 312500000), (38749587 / 10000000000), (1582881 / 10000000000)],
  [(-1116259227 / 2000000000000), (-250996881 / 2000000000000), (133225913 / 50000000000), (115896837 / 2000000000000), (-5868336873 / 2000000000000), (-2223985719 / 2000000000000), (1113087187 / 500000000000), (331315003 / 125000000000), (-43014771 / 20000000000), (-419044057 / 400000000000), (-27690857 / 10000000000), (-880241 / 1250000000), (3029583733 / 500000000000), (1032661 / 2000000000), (-13040791 / 5000000000), (-6695353 / 5000000000), (-301837 / 1250000000), (4378961 / 2500000000), (31189 / 100000000), (-1296037 / 2000000000)],
  [(-26536701 / 20000000000), (-2587887 / 2500000000), (82427149 / 10000000000), (4172755977 / 1000000000000), (-13748689 / 1000000000), (-29068501 / 10000000000), (-219171183 / 20000000000), (-43014771 / 20000000000), (37540709 / 1000000000), (70453329 / 20000000000), (-116427657 / 10000000000), (-6846210273 / 1000000000000), (-51368313 / 2500000000), (855749037 / 125000000000), (5544039 / 400000000), (4515853 / 2000000000), (3991059 / 5000000000), (-7617889 / 1250000000), (-22175591 / 10000000000), (22339237 / 10000000000)],
  [(-1211312239 / 1000000000000), (-198640463 / 400000000000), (39839541 / 20000000000), (3517497 / 10000000000), (1720134901 / 500000000000), (-2616127 / 10000000000), (-5553811961 / 1000000000000), (-419044057 / 400000000000), (70453329 / 20000000000), (3875731201 / 1000000000000), (-34440669 / 10000000000), (-1327019601 / 1000000000000), (-28279929 / 5000000000), (-9500077 / 10000000000), (4338496799 / 500000000000), (3489649 / 10000000000), (-252843 / 10000000000), (-67201 / 31250000), (-17414457 / 10000000000), (132547 / 80000000)],
  [(175693 / 800000000), (-46089 / 2000000000), (-423479 / 800000000), (-87087103 / 250000000000), (15288967 / 2500000000), (8871209677 / 2000000000000), (-6814203 / 400000000), (-27690857 / 10000000000), (-116427657 / 10000000000), (-34440669 / 10000000000), (218262301 / 5000000000), (29346099 / 20000000000), (-7252517 / 2500000000), (-14595691353 / 2000000000000), (-51686991 / 2000000000), (16292303 / 2000000000), (11384479 / 2000000000), (27818559 / 5000000000), (4544443 / 2000000000), (-57303819 / 10000000000)],
  [(1339159969 / 1000000000000), (774265751 / 1000000000000), (-728569 / 160000000), (-104732131 / 80000000000), (22425197 / 10000000000), (2631679 / 5000000000), (13599221613 / 2000000000000), (-880241 / 1250000000), (-6846210273 / 1000000000000), (-1327019601 / 1000000000000), (29346099 / 20000000000), (7818813547 / 2000000000000), (7311217 / 10000000000), (-472229993 / 500000000000), (-16816941 / 5000000000), (-12269171 / 10000000000), (311810599 / 400000000000), (702827 / 2000000000), (14039111 / 10000000000), (-496807 / 10000000000)],
  [(-12650727 / 10000000000), (2078807 / 20000000000), (327849 / 160000000), (159508751 / 1000000000000), (-21767951 / 10000000000), (-1245337 / 625000000), (104202629 / 10000000000), (3029583733 / 500000000000), (-51368313 / 2500000000), (-28279929 / 5000000000), (-7252517 / 2500000000), (7311217 / 10000000000), (371485861 / 10000000000), (20979931 / 20000000000), (-455743847 / 20000000000), (-6405985717 / 1000000000000), (-304707 / 80000000), (104081599 / 10000000000), (9670811 / 2500000000), (-69631 / 15625000)],
  [(150821561 / 2000000000000), (25877267 / 125000000000), (8410359 / 10000000000), (220195267 / 500000000000), (-8698681 / 2000000000), (-13300741 / 10000000000), (3210901 / 1000000000), (1032661 / 2000000000), (855749037 / 125000000000), (-9500077 / 10000000000), (-14595691353 / 2000000000000), (-472229993 / 500000000000), (20979931 / 20000000000), (9715388591 / 2000000000000), (-6211379 / 20000000000), (-2913642159 / 2000000000000), (-3788077 / 1000000000), (-5720063 / 2500000000), (9308739 / 2500000000), (4739773 / 5000000000)],
  [(-2502637 / 2500000000), (-18622063 / 20000000000), (-327987 / 2000000000), (14165477 / 2000000000000), (26578337 / 5000000000), (1533097 / 2500000000), (-26563309 / 10000000000), (-13040791 / 5000000000), (5544039 / 400000000), (4338496799 / 500000000000), (-51686991 / 2000000000), (-16816941 / 5000000000), (-455743847 / 20000000000), (-6211379 / 20000000000), (474598673 / 10000000000), (21332463 / 20000000000), (-69377969 / 20000000000), (-23089536173 / 2000000000000), (-107146667 / 10000000000), (83940483 / 10000000000)],
  [(200012567 / 1000000000000), (348008459 / 2000000000000), (-720677 / 800000000), (-66169397 / 500000000000), (6125423 / 5000000000), (354779 / 312500000), (-49239659 / 10000000000), (-6695353 / 5000000000), (4515853 / 2000000000), (3489649 / 10000000000), (16292303 / 2000000000), (-12269171 / 10000000000), (-6405985717 / 1000000000000), (-2913642159 / 2000000000000), (21332463 / 20000000000), (1686428671 / 400000000000), (-1640463 / 4000000000), (-2603595067 / 2000000000000), (-2548847 / 10000000000), (-834777 / 2000000000)],
  [(769927 / 2500000000), (-15357991 / 20000000000), (23512079 / 20000000000), (964965721 / 1000000000000), (-17740091 / 10000000000), (3547419 / 5000000000), (-35522463 / 10000000000), (-301837 / 1250000000), (3991059 / 5000000000), (-252843 / 10000000000), (11384479 / 2000000000), (311810599 / 400000000000), (-304707 / 80000000), (-3788077 / 1000000000), (-69377969 / 20000000000), (-1640463 / 4000000000), (65820423 / 5000000000), (6087867 / 1250000000), (-85341193 / 10000000000), (-4182846837 / 2000000000000)],
  [(-717316127 / 2000000000000), (-529102333 / 2000000000000), (30813587 / 20000000000), (39448533 / 50000000000), (-4586827 / 2000000000), (-1892563 / 5000000000), (113213 / 312500000), (4378961 / 2500000000), (-7617889 / 1250000000), (-67201 / 31250000), (27818559 / 5000000000), (702827 / 2000000000), (104081599 / 10000000000), (-5720063 / 2500000000), (-23089536173 / 2000000000000), (-2603595067 / 2000000000000), (6087867 / 1250000000), (7040162709 / 1000000000000), (-12269877 / 5000000000), (-3548812769 / 1000000000000)],
  [(9147513 / 10000000000), (9147513 / 10000000000), (-1848249 / 1250000000), (-6587359 / 5000000000), (16303 / 200000000), (-3318791 / 5000000000), (38749587 / 10000000000), (31189 / 100000000), (-22175591 / 10000000000), (-17414457 / 10000000000), (4544443 / 2000000000), (14039111 / 10000000000), (9670811 / 2500000000), (9308739 / 2500000000), (-107146667 / 10000000000), (-2548847 / 10000000000), (-85341193 / 10000000000), (-12269877 / 5000000000), (59665867 / 5000000000), (387439 / 5000000000)],
  [(-158403463 / 2000000000000), (-79248581 / 1000000000000), (-1109869 / 4000000000), (-696666751 / 2000000000000), (17296 / 9765625), (961193 / 10000000000), (1582881 / 10000000000), (-1296037 / 2000000000), (22339237 / 10000000000), (132547 / 80000000), (-57303819 / 10000000000), (-496807 / 10000000000), (-69631 / 15625000), (4739773 / 5000000000), (83940483 / 10000000000), (-834777 / 2000000000), (-4182846837 / 2000000000000), (-3548812769 / 1000000000000), (387439 / 5000000000), (4781142051 / 2000000000000)]
]
def literalDescent : Matrix (Fin 10 × Fin 2) (Fin 10 × Fin 2) ℚ := readFlat literalDescentData
@[simp] theorem lookup_descent_0_0 : literalDescent (0, 0) (0, 0) = (3926439 / 1250000000) := rfl
@[simp] theorem lookup_previous_0_0 : previousPadding literalP (0, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_0_0 : currentPadding literalP (0, 0) (0, 0) = (1287159129 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_1 : literalDescent (0, 0) (0, 1) = (989663 / 2400000000) := rfl
@[simp] theorem lookup_previous_0_1 : previousPadding literalP (0, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_0_1 : currentPadding literalP (0, 0) (0, 1) = (21157731 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_2 : literalDescent (0, 0) (1, 0) = (-10855219 / 2000000000) := rfl
@[simp] theorem lookup_previous_0_2 : previousPadding literalP (0, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_current_0_2 : currentPadding literalP (0, 0) (1, 0) = (-605009279 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_3 : literalDescent (0, 0) (1, 1) = (-7054425209 / 6000000000000) := rfl
@[simp] theorem lookup_previous_0_3 : previousPadding literalP (0, 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_current_0_3 : currentPadding literalP (0, 0) (1, 1) = (142915161443 / 1200000000000) := rfl
@[simp] theorem lookup_descent_0_4 : literalDescent (0, 0) (2, 0) = (-3795193 / 20000000000) := rfl
@[simp] theorem lookup_previous_0_4 : previousPadding literalP (0, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_current_0_4 : currentPadding literalP (0, 0) (2, 0) = (-1055978157 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_5 : literalDescent (0, 0) (2, 1) = (542438513 / 400000000000) := rfl
@[simp] theorem lookup_previous_0_5 : previousPadding literalP (0, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_current_0_5 : currentPadding literalP (0, 0) (2, 1) = (201585060529 / 2000000000000) := rfl
@[simp] theorem lookup_descent_0_6 : literalDescent (0, 0) (3, 0) = (92536843 / 20000000000) := rfl
@[simp] theorem lookup_previous_0_6 : previousPadding literalP (0, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_current_0_6 : currentPadding literalP (0, 0) (3, 0) = (98406243 / 2500000000) := rfl
@[simp] theorem lookup_descent_0_7 : literalDescent (0, 0) (3, 1) = (-1116259227 / 2000000000000) := rfl
@[simp] theorem lookup_previous_0_7 : previousPadding literalP (0, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_current_0_7 : currentPadding literalP (0, 0) (3, 1) = (1233703 / 625000000) := rfl
@[simp] theorem lookup_descent_0_8 : literalDescent (0, 0) (4, 0) = (-26536701 / 20000000000) := rfl
@[simp] theorem lookup_previous_0_8 : previousPadding literalP (0, 0) (4, 0) = 0 := rfl
@[simp] theorem lookup_current_0_8 : currentPadding literalP (0, 0) (4, 0) = (-11460221 / 5000000000) := rfl
@[simp] theorem lookup_descent_0_9 : literalDescent (0, 0) (4, 1) = (-1211312239 / 1000000000000) := rfl
@[simp] theorem lookup_previous_0_9 : previousPadding literalP (0, 0) (4, 1) = 0 := rfl
@[simp] theorem lookup_current_0_9 : currentPadding literalP (0, 0) (4, 1) = (-168148297 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_10 : literalDescent (0, 0) (5, 0) = (175693 / 800000000) := rfl
@[simp] theorem lookup_previous_0_10 : previousPadding literalP (0, 0) (5, 0) = 0 := rfl
@[simp] theorem lookup_current_0_10 : currentPadding literalP (0, 0) (5, 0) = (1534173 / 2000000000) := rfl
@[simp] theorem lookup_descent_0_11 : literalDescent (0, 0) (5, 1) = (1339159969 / 1000000000000) := rfl
@[simp] theorem lookup_previous_0_11 : previousPadding literalP (0, 0) (5, 1) = 0 := rfl
@[simp] theorem lookup_current_0_11 : currentPadding literalP (0, 0) (5, 1) = (4793121 / 1250000000) := rfl
@[simp] theorem lookup_descent_0_12 : literalDescent (0, 0) (6, 0) = (-12650727 / 10000000000) := rfl
@[simp] theorem lookup_previous_0_12 : previousPadding literalP (0, 0) (6, 0) = 0 := rfl
@[simp] theorem lookup_current_0_12 : currentPadding literalP (0, 0) (6, 0) = (1936951 / 1000000000) := rfl
@[simp] theorem lookup_descent_0_13 : literalDescent (0, 0) (6, 1) = (150821561 / 2000000000000) := rfl
@[simp] theorem lookup_previous_0_13 : previousPadding literalP (0, 0) (6, 1) = 0 := rfl
@[simp] theorem lookup_current_0_13 : currentPadding literalP (0, 0) (6, 1) = (-441629 / 200000000) := rfl
@[simp] theorem lookup_descent_0_14 : literalDescent (0, 0) (7, 0) = (-2502637 / 2500000000) := rfl
@[simp] theorem lookup_previous_0_14 : previousPadding literalP (0, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_current_0_14 : currentPadding literalP (0, 0) (7, 0) = (5405339 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_15 : literalDescent (0, 0) (7, 1) = (200012567 / 1000000000000) := rfl
@[simp] theorem lookup_previous_0_15 : previousPadding literalP (0, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_current_0_15 : currentPadding literalP (0, 0) (7, 1) = (12976049 / 5000000000) := rfl
@[simp] theorem lookup_descent_0_16 : literalDescent (0, 0) (8, 0) = (769927 / 2500000000) := rfl
@[simp] theorem lookup_previous_0_16 : previousPadding literalP (0, 0) (8, 0) = 0 := rfl
@[simp] theorem lookup_current_0_16 : currentPadding literalP (0, 0) (8, 0) = (-1848249 / 1250000000) := rfl
@[simp] theorem lookup_descent_0_17 : literalDescent (0, 0) (8, 1) = (-717316127 / 2000000000000) := rfl
@[simp] theorem lookup_previous_0_17 : previousPadding literalP (0, 0) (8, 1) = 0 := rfl
@[simp] theorem lookup_current_0_17 : currentPadding literalP (0, 0) (8, 1) = (2195589 / 5000000000) := rfl
@[simp] theorem lookup_descent_0_18 : literalDescent (0, 0) (9, 0) = (9147513 / 10000000000) := rfl
@[simp] theorem lookup_previous_0_18 : previousPadding literalP (0, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_current_0_18 : currentPadding literalP (0, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_0_19 : literalDescent (0, 0) (9, 1) = (-158403463 / 2000000000000) := rfl
@[simp] theorem lookup_previous_0_19 : previousPadding literalP (0, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_current_0_19 : currentPadding literalP (0, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_1_0 : literalDescent (0, 1) (0, 0) = (989663 / 2400000000) := rfl
@[simp] theorem lookup_previous_1_0 : previousPadding literalP (0, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_1_0 : currentPadding literalP (0, 1) (0, 0) = (21157731 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_1 : literalDescent (0, 1) (0, 1) = (181933127 / 250000000000) := rfl
@[simp] theorem lookup_previous_1_1 : previousPadding literalP (0, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_1_1 : currentPadding literalP (0, 1) (0, 1) = (16366166449 / 125000000000) := rfl
@[simp] theorem lookup_descent_1_2 : literalDescent (0, 1) (1, 0) = (-4338513333 / 2000000000000) := rfl
@[simp] theorem lookup_previous_1_2 : previousPadding literalP (0, 1) (1, 0) = 0 := rfl
@[simp] theorem lookup_current_1_2 : currentPadding literalP (0, 1) (1, 0) = (-127516415167 / 2000000000000) := rfl
@[simp] theorem lookup_descent_1_3 : literalDescent (0, 1) (1, 1) = (-1318771633 / 2000000000000) := rfl
@[simp] theorem lookup_previous_1_3 : previousPadding literalP (0, 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_current_1_3 : currentPadding literalP (0, 1) (1, 1) = (-77113287 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_4 : literalDescent (0, 1) (2, 0) = (15563653 / 60000000000) := rfl
@[simp] theorem lookup_previous_1_4 : previousPadding literalP (0, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_current_1_4 : currentPadding literalP (0, 1) (2, 0) = (27284063 / 1250000000) := rfl
@[simp] theorem lookup_descent_1_5 : literalDescent (0, 1) (2, 1) = (-20618837 / 80000000000) := rfl
@[simp] theorem lookup_previous_1_5 : previousPadding literalP (0, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_current_1_5 : currentPadding literalP (0, 1) (2, 1) = (-1055298453 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_6 : literalDescent (0, 1) (3, 0) = (6472026433 / 2000000000000) := rfl
@[simp] theorem lookup_previous_1_6 : previousPadding literalP (0, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_current_1_6 : currentPadding literalP (0, 1) (3, 0) = (81506679767 / 2000000000000) := rfl
@[simp] theorem lookup_descent_1_7 : literalDescent (0, 1) (3, 1) = (-250996881 / 2000000000000) := rfl
@[simp] theorem lookup_previous_1_7 : previousPadding literalP (0, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_current_1_7 : currentPadding literalP (0, 1) (3, 1) = (7706081 / 5000000000) := rfl
@[simp] theorem lookup_descent_1_8 : literalDescent (0, 1) (4, 0) = (-2587887 / 2500000000) := rfl
@[simp] theorem lookup_previous_1_8 : previousPadding literalP (0, 1) (4, 0) = 0 := rfl
@[simp] theorem lookup_current_1_8 : currentPadding literalP (0, 1) (4, 0) = (-6459289 / 2500000000) := rfl
@[simp] theorem lookup_descent_1_9 : literalDescent (0, 1) (4, 1) = (-198640463 / 400000000000) := rfl
@[simp] theorem lookup_previous_1_9 : previousPadding literalP (0, 1) (4, 1) = 0 := rfl
@[simp] theorem lookup_current_1_9 : currentPadding literalP (0, 1) (4, 1) = (-43824029 / 2500000000) := rfl
@[simp] theorem lookup_descent_1_10 : literalDescent (0, 1) (5, 0) = (-46089 / 2000000000) := rfl
@[simp] theorem lookup_previous_1_10 : previousPadding literalP (0, 1) (5, 0) = 0 := rfl
@[simp] theorem lookup_current_1_10 : currentPadding literalP (0, 1) (5, 0) = (2524381 / 2500000000) := rfl
@[simp] theorem lookup_descent_1_11 : literalDescent (0, 1) (5, 1) = (774265751 / 1000000000000) := rfl
@[simp] theorem lookup_previous_1_11 : previousPadding literalP (0, 1) (5, 1) = 0 := rfl
@[simp] theorem lookup_current_1_11 : currentPadding literalP (0, 1) (5, 1) = (21996047 / 5000000000) := rfl
@[simp] theorem lookup_descent_1_12 : literalDescent (0, 1) (6, 0) = (2078807 / 20000000000) := rfl
@[simp] theorem lookup_previous_1_12 : previousPadding literalP (0, 1) (6, 0) = 0 := rfl
@[simp] theorem lookup_current_1_12 : currentPadding literalP (0, 1) (6, 0) = (283971 / 500000000) := rfl
@[simp] theorem lookup_descent_1_13 : literalDescent (0, 1) (6, 1) = (25877267 / 125000000000) := rfl
@[simp] theorem lookup_previous_1_13 : previousPadding literalP (0, 1) (6, 1) = 0 := rfl
@[simp] theorem lookup_current_1_13 : currentPadding literalP (0, 1) (6, 1) = (-11699771 / 5000000000) := rfl
@[simp] theorem lookup_descent_1_14 : literalDescent (0, 1) (7, 0) = (-18622063 / 20000000000) := rfl
@[simp] theorem lookup_previous_1_14 : previousPadding literalP (0, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_current_1_14 : currentPadding literalP (0, 1) (7, 0) = (4705859 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_15 : literalDescent (0, 1) (7, 1) = (348008459 / 2000000000000) := rfl
@[simp] theorem lookup_previous_1_15 : previousPadding literalP (0, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_current_1_15 : currentPadding literalP (0, 1) (7, 1) = (1929473 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_16 : literalDescent (0, 1) (8, 0) = (-15357991 / 20000000000) := rfl
@[simp] theorem lookup_previous_1_16 : previousPadding literalP (0, 1) (8, 0) = 0 := rfl
@[simp] theorem lookup_current_1_16 : currentPadding literalP (0, 1) (8, 0) = (-805441 / 2000000000) := rfl
@[simp] theorem lookup_descent_1_17 : literalDescent (0, 1) (8, 1) = (-529102333 / 2000000000000) := rfl
@[simp] theorem lookup_previous_1_17 : previousPadding literalP (0, 1) (8, 1) = 0 := rfl
@[simp] theorem lookup_current_1_17 : currentPadding literalP (0, 1) (8, 1) = (-441899 / 250000000) := rfl
@[simp] theorem lookup_descent_1_18 : literalDescent (0, 1) (9, 0) = (9147513 / 10000000000) := rfl
@[simp] theorem lookup_previous_1_18 : previousPadding literalP (0, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_current_1_18 : currentPadding literalP (0, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_1_19 : literalDescent (0, 1) (9, 1) = (-79248581 / 1000000000000) := rfl
@[simp] theorem lookup_previous_1_19 : previousPadding literalP (0, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_current_1_19 : currentPadding literalP (0, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_2_0 : literalDescent (1, 0) (0, 0) = (-10855219 / 2000000000) := rfl
@[simp] theorem lookup_previous_2_0 : previousPadding literalP (1, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_2_0 : currentPadding literalP (1, 0) (0, 0) = (-605009279 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_1 : literalDescent (1, 0) (0, 1) = (-4338513333 / 2000000000000) := rfl
@[simp] theorem lookup_previous_2_1 : previousPadding literalP (1, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_2_1 : currentPadding literalP (1, 0) (0, 1) = (-127516415167 / 2000000000000) := rfl
@[simp] theorem lookup_descent_2_2 : literalDescent (1, 0) (1, 0) = (159499529 / 10000000000) := rfl
@[simp] theorem lookup_previous_2_2 : previousPadding literalP (1, 0) (1, 0) = (1287159129 / 10000000000) := rfl
@[simp] theorem lookup_current_2_2 : currentPadding literalP (1, 0) (1, 0) = (1127659707 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_3 : literalDescent (1, 0) (1, 1) = (10400633803 / 3000000000000) := rfl
@[simp] theorem lookup_previous_2_3 : previousPadding literalP (1, 0) (1, 1) = (21157731 / 10000000000) := rfl
@[simp] theorem lookup_current_2_3 : currentPadding literalP (1, 0) (1, 1) = (-209314491443 / 1200000000000) := rfl
@[simp] theorem lookup_descent_2_4 : literalDescent (1, 0) (2, 0) = (-59184843 / 10000000000) := rfl
@[simp] theorem lookup_previous_2_4 : previousPadding literalP (1, 0) (2, 0) = (-605009279 / 10000000000) := rfl
@[simp] theorem lookup_current_2_4 : currentPadding literalP (1, 0) (2, 0) = (-610833 / 1250000000) := rfl
@[simp] theorem lookup_descent_2_5 : literalDescent (1, 0) (2, 1) = (-15623772467 / 6000000000000) := rfl
@[simp] theorem lookup_previous_2_5 : previousPadding literalP (1, 0) (2, 1) = (142915161443 / 1200000000000) := rfl
@[simp] theorem lookup_current_2_5 : currentPadding literalP (1, 0) (2, 1) = (-160712407 / 5000000000) := rfl
@[simp] theorem lookup_descent_2_6 : literalDescent (1, 0) (3, 0) = (-55597171 / 4000000000) := rfl
@[simp] theorem lookup_previous_2_6 : previousPadding literalP (1, 0) (3, 0) = (-1055978157 / 10000000000) := rfl
@[simp] theorem lookup_current_2_6 : currentPadding literalP (1, 0) (3, 0) = (-458492607 / 5000000000) := rfl
@[simp] theorem lookup_descent_2_7 : literalDescent (1, 0) (3, 1) = (133225913 / 50000000000) := rfl
@[simp] theorem lookup_previous_2_7 : previousPadding literalP (1, 0) (3, 1) = (201585060529 / 2000000000000) := rfl
@[simp] theorem lookup_current_2_7 : currentPadding literalP (1, 0) (3, 1) = (88068465209 / 2000000000000) := rfl
@[simp] theorem lookup_descent_2_8 : literalDescent (1, 0) (4, 0) = (82427149 / 10000000000) := rfl
@[simp] theorem lookup_previous_2_8 : previousPadding literalP (1, 0) (4, 0) = (98406243 / 2500000000) := rfl
@[simp] theorem lookup_current_2_8 : currentPadding literalP (1, 0) (4, 0) = (399565111 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_9 : literalDescent (1, 0) (4, 1) = (39839541 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_9 : previousPadding literalP (1, 0) (4, 1) = (1233703 / 625000000) := rfl
@[simp] theorem lookup_current_2_9 : currentPadding literalP (1, 0) (4, 1) = (352747 / 40000000) := rfl
@[simp] theorem lookup_descent_2_10 : literalDescent (1, 0) (5, 0) = (-423479 / 800000000) := rfl
@[simp] theorem lookup_previous_2_10 : previousPadding literalP (1, 0) (5, 0) = (-11460221 / 5000000000) := rfl
@[simp] theorem lookup_current_2_10 : currentPadding literalP (1, 0) (5, 0) = (-17626927 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_11 : literalDescent (1, 0) (5, 1) = (-728569 / 160000000) := rfl
@[simp] theorem lookup_previous_2_11 : previousPadding literalP (1, 0) (5, 1) = (-168148297 / 10000000000) := rfl
@[simp] theorem lookup_current_2_11 : currentPadding literalP (1, 0) (5, 1) = (-42195999 / 2000000000) := rfl
@[simp] theorem lookup_descent_2_12 : literalDescent (1, 0) (6, 0) = (327849 / 160000000) := rfl
@[simp] theorem lookup_previous_2_12 : previousPadding literalP (1, 0) (6, 0) = (1534173 / 2000000000) := rfl
@[simp] theorem lookup_current_2_12 : currentPadding literalP (1, 0) (6, 0) = (-227069 / 500000000) := rfl
@[simp] theorem lookup_descent_2_13 : literalDescent (1, 0) (6, 1) = (8410359 / 10000000000) := rfl
@[simp] theorem lookup_previous_2_13 : previousPadding literalP (1, 0) (6, 1) = (4793121 / 1250000000) := rfl
@[simp] theorem lookup_current_2_13 : currentPadding literalP (1, 0) (6, 1) = (38212899 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_14 : literalDescent (1, 0) (7, 0) = (-327987 / 2000000000) := rfl
@[simp] theorem lookup_previous_2_14 : previousPadding literalP (1, 0) (7, 0) = (1936951 / 1000000000) := rfl
@[simp] theorem lookup_current_2_14 : currentPadding literalP (1, 0) (7, 0) = (2626187 / 1250000000) := rfl
@[simp] theorem lookup_descent_2_15 : literalDescent (1, 0) (7, 1) = (-720677 / 800000000) := rfl
@[simp] theorem lookup_previous_2_15 : previousPadding literalP (1, 0) (7, 1) = (-441629 / 200000000) := rfl
@[simp] theorem lookup_current_2_15 : currentPadding literalP (1, 0) (7, 1) = (-10675627 / 5000000000) := rfl
@[simp] theorem lookup_descent_2_16 : literalDescent (1, 0) (8, 0) = (23512079 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_16 : previousPadding literalP (1, 0) (8, 0) = (5405339 / 10000000000) := rfl
@[simp] theorem lookup_current_2_16 : currentPadding literalP (1, 0) (8, 0) = (16303 / 200000000) := rfl
@[simp] theorem lookup_descent_2_17 : literalDescent (1, 0) (8, 1) = (30813587 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_17 : previousPadding literalP (1, 0) (8, 1) = (12976049 / 5000000000) := rfl
@[simp] theorem lookup_current_2_17 : currentPadding literalP (1, 0) (8, 1) = (17296 / 9765625) := rfl
@[simp] theorem lookup_descent_2_18 : literalDescent (1, 0) (9, 0) = (-1848249 / 1250000000) := rfl
@[simp] theorem lookup_previous_2_18 : previousPadding literalP (1, 0) (9, 0) = (-1848249 / 1250000000) := rfl
@[simp] theorem lookup_current_2_18 : currentPadding literalP (1, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_2_19 : literalDescent (1, 0) (9, 1) = (-1109869 / 4000000000) := rfl
@[simp] theorem lookup_previous_2_19 : previousPadding literalP (1, 0) (9, 1) = (2195589 / 5000000000) := rfl
@[simp] theorem lookup_current_2_19 : currentPadding literalP (1, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_3_0 : literalDescent (1, 1) (0, 0) = (-7054425209 / 6000000000000) := rfl
@[simp] theorem lookup_previous_3_0 : previousPadding literalP (1, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_3_0 : currentPadding literalP (1, 1) (0, 0) = (142915161443 / 1200000000000) := rfl
@[simp] theorem lookup_descent_3_1 : literalDescent (1, 1) (0, 1) = (-1318771633 / 2000000000000) := rfl
@[simp] theorem lookup_previous_3_1 : previousPadding literalP (1, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_3_1 : currentPadding literalP (1, 1) (0, 1) = (-77113287 / 10000000000) := rfl
@[simp] theorem lookup_descent_3_2 : literalDescent (1, 1) (1, 0) = (10400633803 / 3000000000000) := rfl
@[simp] theorem lookup_previous_3_2 : previousPadding literalP (1, 1) (1, 0) = (21157731 / 10000000000) := rfl
@[simp] theorem lookup_current_3_2 : currentPadding literalP (1, 1) (1, 0) = (-209314491443 / 1200000000000) := rfl
@[simp] theorem lookup_descent_3_3 : literalDescent (1, 1) (1, 1) = (3139212641 / 2000000000000) := rfl
@[simp] theorem lookup_previous_3_3 : previousPadding literalP (1, 1) (1, 1) = (16366166449 / 125000000000) := rfl
@[simp] theorem lookup_current_3_3 : currentPadding literalP (1, 1) (1, 1) = (28888183441 / 2000000000000) := rfl
@[simp] theorem lookup_descent_3_4 : literalDescent (1, 1) (2, 0) = (-2505824989 / 1000000000000) := rfl
@[simp] theorem lookup_previous_3_4 : previousPadding literalP (1, 1) (2, 0) = (-127516415167 / 2000000000000) := rfl
@[simp] theorem lookup_current_3_4 : currentPadding literalP (1, 1) (2, 0) = (5463039 / 100000000) := rfl
@[simp] theorem lookup_descent_3_5 : literalDescent (1, 1) (2, 1) = (-1518912019 / 2000000000000) := rfl
@[simp] theorem lookup_previous_3_5 : previousPadding literalP (1, 1) (2, 1) = (-77113287 / 10000000000) := rfl
@[simp] theorem lookup_current_3_5 : currentPadding literalP (1, 1) (2, 1) = (-11598299 / 5000000000) := rfl
@[simp] theorem lookup_descent_3_6 : literalDescent (1, 1) (3, 0) = (-1711904193 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_6 : previousPadding literalP (1, 1) (3, 0) = (27284063 / 1250000000) := rfl
@[simp] theorem lookup_current_3_6 : currentPadding literalP (1, 1) (3, 0) = (-37476543 / 2000000000) := rfl
@[simp] theorem lookup_descent_3_7 : literalDescent (1, 1) (3, 1) = (115896837 / 2000000000000) := rfl
@[simp] theorem lookup_previous_3_7 : previousPadding literalP (1, 1) (3, 1) = (-1055298453 / 10000000000) := rfl
@[simp] theorem lookup_current_3_7 : currentPadding literalP (1, 1) (3, 1) = (-365509 / 62500000) := rfl
@[simp] theorem lookup_descent_3_8 : literalDescent (1, 1) (4, 0) = (4172755977 / 1000000000000) := rfl
@[simp] theorem lookup_previous_3_8 : previousPadding literalP (1, 1) (4, 0) = (81506679767 / 2000000000000) := rfl
@[simp] theorem lookup_current_3_8 : currentPadding literalP (1, 1) (4, 0) = (5918697 / 250000000) := rfl
@[simp] theorem lookup_descent_3_9 : literalDescent (1, 1) (4, 1) = (3517497 / 10000000000) := rfl
@[simp] theorem lookup_previous_3_9 : previousPadding literalP (1, 1) (4, 1) = (7706081 / 5000000000) := rfl
@[simp] theorem lookup_current_3_9 : currentPadding literalP (1, 1) (4, 1) = (26909993 / 10000000000) := rfl
@[simp] theorem lookup_descent_3_10 : literalDescent (1, 1) (5, 0) = (-87087103 / 250000000000) := rfl
@[simp] theorem lookup_previous_3_10 : previousPadding literalP (1, 1) (5, 0) = (-6459289 / 2500000000) := rfl
@[simp] theorem lookup_current_3_10 : currentPadding literalP (1, 1) (5, 0) = (-16110353 / 5000000000) := rfl
@[simp] theorem lookup_descent_3_11 : literalDescent (1, 1) (5, 1) = (-104732131 / 80000000000) := rfl
@[simp] theorem lookup_previous_3_11 : previousPadding literalP (1, 1) (5, 1) = (-43824029 / 2500000000) := rfl
@[simp] theorem lookup_current_3_11 : currentPadding literalP (1, 1) (5, 1) = (-24346287 / 5000000000) := rfl
@[simp] theorem lookup_descent_3_12 : literalDescent (1, 1) (6, 0) = (159508751 / 1000000000000) := rfl
@[simp] theorem lookup_previous_3_12 : previousPadding literalP (1, 1) (6, 0) = (2524381 / 2500000000) := rfl
@[simp] theorem lookup_current_3_12 : currentPadding literalP (1, 1) (6, 0) = (-2739353 / 2000000000) := rfl
@[simp] theorem lookup_descent_3_13 : literalDescent (1, 1) (6, 1) = (220195267 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_13 : previousPadding literalP (1, 1) (6, 1) = (21996047 / 5000000000) := rfl
@[simp] theorem lookup_current_3_13 : currentPadding literalP (1, 1) (6, 1) = (45437147 / 10000000000) := rfl
@[simp] theorem lookup_descent_3_14 : literalDescent (1, 1) (7, 0) = (14165477 / 2000000000000) := rfl
@[simp] theorem lookup_previous_3_14 : previousPadding literalP (1, 1) (7, 0) = (283971 / 500000000) := rfl
@[simp] theorem lookup_current_3_14 : currentPadding literalP (1, 1) (7, 0) = (5106869 / 5000000000) := rfl
@[simp] theorem lookup_descent_3_15 : literalDescent (1, 1) (7, 1) = (-66169397 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_15 : previousPadding literalP (1, 1) (7, 1) = (-11699771 / 5000000000) := rfl
@[simp] theorem lookup_current_3_15 : currentPadding literalP (1, 1) (7, 1) = (-10265311 / 10000000000) := rfl
@[simp] theorem lookup_descent_3_16 : literalDescent (1, 1) (8, 0) = (964965721 / 1000000000000) := rfl
@[simp] theorem lookup_previous_3_16 : previousPadding literalP (1, 1) (8, 0) = (4705859 / 10000000000) := rfl
@[simp] theorem lookup_current_3_16 : currentPadding literalP (1, 1) (8, 0) = (-3318791 / 5000000000) := rfl
@[simp] theorem lookup_descent_3_17 : literalDescent (1, 1) (8, 1) = (39448533 / 50000000000) := rfl
@[simp] theorem lookup_previous_3_17 : previousPadding literalP (1, 1) (8, 1) = (1929473 / 10000000000) := rfl
@[simp] theorem lookup_current_3_17 : currentPadding literalP (1, 1) (8, 1) = (961193 / 10000000000) := rfl
@[simp] theorem lookup_descent_3_18 : literalDescent (1, 1) (9, 0) = (-6587359 / 5000000000) := rfl
@[simp] theorem lookup_previous_3_18 : previousPadding literalP (1, 1) (9, 0) = (-805441 / 2000000000) := rfl
@[simp] theorem lookup_current_3_18 : currentPadding literalP (1, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_3_19 : literalDescent (1, 1) (9, 1) = (-696666751 / 2000000000000) := rfl
@[simp] theorem lookup_previous_3_19 : previousPadding literalP (1, 1) (9, 1) = (-441899 / 250000000) := rfl
@[simp] theorem lookup_current_3_19 : currentPadding literalP (1, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_4_0 : literalDescent (2, 0) (0, 0) = (-3795193 / 20000000000) := rfl
@[simp] theorem lookup_previous_4_0 : previousPadding literalP (2, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_4_0 : currentPadding literalP (2, 0) (0, 0) = (-1055978157 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_1 : literalDescent (2, 0) (0, 1) = (15563653 / 60000000000) := rfl
@[simp] theorem lookup_previous_4_1 : previousPadding literalP (2, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_4_1 : currentPadding literalP (2, 0) (0, 1) = (27284063 / 1250000000) := rfl
@[simp] theorem lookup_descent_4_2 : literalDescent (2, 0) (1, 0) = (-59184843 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_2 : previousPadding literalP (2, 0) (1, 0) = (-605009279 / 10000000000) := rfl
@[simp] theorem lookup_current_4_2 : currentPadding literalP (2, 0) (1, 0) = (-610833 / 1250000000) := rfl
@[simp] theorem lookup_descent_4_3 : literalDescent (2, 0) (1, 1) = (-2505824989 / 1000000000000) := rfl
@[simp] theorem lookup_previous_4_3 : previousPadding literalP (2, 0) (1, 1) = (-127516415167 / 2000000000000) := rfl
@[simp] theorem lookup_current_4_3 : currentPadding literalP (2, 0) (1, 1) = (5463039 / 100000000) := rfl
@[simp] theorem lookup_descent_4_4 : literalDescent (2, 0) (2, 0) = (172515093 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_4 : previousPadding literalP (2, 0) (2, 0) = (1127659707 / 10000000000) := rfl
@[simp] theorem lookup_current_4_4 : currentPadding literalP (2, 0) (2, 0) = (1989020577 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_5 : literalDescent (2, 0) (2, 1) = (18866212241 / 6000000000000) := rfl
@[simp] theorem lookup_previous_4_5 : previousPadding literalP (2, 0) (2, 1) = (-209314491443 / 1200000000000) := rfl
@[simp] theorem lookup_current_4_5 : currentPadding literalP (2, 0) (2, 1) = (-37092764313 / 500000000000) := rfl
@[simp] theorem lookup_descent_4_6 : literalDescent (2, 0) (3, 0) = (-99130827 / 20000000000) := rfl
@[simp] theorem lookup_previous_4_6 : previousPadding literalP (2, 0) (3, 0) = (-610833 / 1250000000) := rfl
@[simp] theorem lookup_current_4_6 : currentPadding literalP (2, 0) (3, 0) = (-14758101 / 312500000) := rfl
@[simp] theorem lookup_descent_4_7 : literalDescent (2, 0) (3, 1) = (-5868336873 / 2000000000000) := rfl
@[simp] theorem lookup_previous_4_7 : previousPadding literalP (2, 0) (3, 1) = (-160712407 / 5000000000) := rfl
@[simp] theorem lookup_current_4_7 : currentPadding literalP (2, 0) (3, 1) = (-11227663 / 312500000) := rfl
@[simp] theorem lookup_descent_4_8 : literalDescent (2, 0) (4, 0) = (-13748689 / 1000000000) := rfl
@[simp] theorem lookup_previous_4_8 : previousPadding literalP (2, 0) (4, 0) = (-458492607 / 5000000000) := rfl
@[simp] theorem lookup_current_4_8 : currentPadding literalP (2, 0) (4, 0) = (-194874581 / 2500000000) := rfl
@[simp] theorem lookup_descent_4_9 : literalDescent (2, 0) (4, 1) = (1720134901 / 500000000000) := rfl
@[simp] theorem lookup_previous_4_9 : previousPadding literalP (2, 0) (4, 1) = (88068465209 / 2000000000000) := rfl
@[simp] theorem lookup_current_4_9 : currentPadding literalP (2, 0) (4, 1) = (16237585121 / 400000000000) := rfl
@[simp] theorem lookup_descent_4_10 : literalDescent (2, 0) (5, 0) = (15288967 / 2500000000) := rfl
@[simp] theorem lookup_previous_4_10 : previousPadding literalP (2, 0) (5, 0) = (399565111 / 10000000000) := rfl
@[simp] theorem lookup_current_4_10 : currentPadding literalP (2, 0) (5, 0) = (338409243 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_11 : literalDescent (2, 0) (5, 1) = (22425197 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_11 : previousPadding literalP (2, 0) (5, 1) = (352747 / 40000000) := rfl
@[simp] theorem lookup_current_4_11 : currentPadding literalP (2, 0) (5, 1) = (65761553 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_12 : literalDescent (2, 0) (6, 0) = (-21767951 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_12 : previousPadding literalP (2, 0) (6, 0) = (-17626927 / 10000000000) := rfl
@[simp] theorem lookup_current_4_12 : currentPadding literalP (2, 0) (6, 0) = (129407 / 312500000) := rfl
@[simp] theorem lookup_descent_4_13 : literalDescent (2, 0) (6, 1) = (-8698681 / 2000000000) := rfl
@[simp] theorem lookup_previous_4_13 : previousPadding literalP (2, 0) (6, 1) = (-42195999 / 2000000000) := rfl
@[simp] theorem lookup_current_4_13 : currentPadding literalP (2, 0) (6, 1) = (-16748659 / 1000000000) := rfl
@[simp] theorem lookup_descent_4_14 : literalDescent (2, 0) (7, 0) = (26578337 / 5000000000) := rfl
@[simp] theorem lookup_previous_4_14 : previousPadding literalP (2, 0) (7, 0) = (-227069 / 500000000) := rfl
@[simp] theorem lookup_current_4_14 : currentPadding literalP (2, 0) (7, 0) = (-28849027 / 5000000000) := rfl
@[simp] theorem lookup_descent_4_15 : literalDescent (2, 0) (7, 1) = (6125423 / 5000000000) := rfl
@[simp] theorem lookup_previous_4_15 : previousPadding literalP (2, 0) (7, 1) = (38212899 / 10000000000) := rfl
@[simp] theorem lookup_current_4_15 : currentPadding literalP (2, 0) (7, 1) = (25962053 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_16 : literalDescent (2, 0) (8, 0) = (-17740091 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_16 : previousPadding literalP (2, 0) (8, 0) = (2626187 / 1250000000) := rfl
@[simp] theorem lookup_current_4_16 : currentPadding literalP (2, 0) (8, 0) = (38749587 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_17 : literalDescent (2, 0) (8, 1) = (-4586827 / 2000000000) := rfl
@[simp] theorem lookup_previous_4_17 : previousPadding literalP (2, 0) (8, 1) = (-10675627 / 5000000000) := rfl
@[simp] theorem lookup_current_4_17 : currentPadding literalP (2, 0) (8, 1) = (1582881 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_18 : literalDescent (2, 0) (9, 0) = (16303 / 200000000) := rfl
@[simp] theorem lookup_previous_4_18 : previousPadding literalP (2, 0) (9, 0) = (16303 / 200000000) := rfl
@[simp] theorem lookup_current_4_18 : currentPadding literalP (2, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_4_19 : literalDescent (2, 0) (9, 1) = (17296 / 9765625) := rfl
@[simp] theorem lookup_previous_4_19 : previousPadding literalP (2, 0) (9, 1) = (17296 / 9765625) := rfl
@[simp] theorem lookup_current_4_19 : currentPadding literalP (2, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_5_0 : literalDescent (2, 1) (0, 0) = (542438513 / 400000000000) := rfl
@[simp] theorem lookup_previous_5_0 : previousPadding literalP (2, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_5_0 : currentPadding literalP (2, 1) (0, 0) = (201585060529 / 2000000000000) := rfl
@[simp] theorem lookup_descent_5_1 : literalDescent (2, 1) (0, 1) = (-20618837 / 80000000000) := rfl
@[simp] theorem lookup_previous_5_1 : previousPadding literalP (2, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_5_1 : currentPadding literalP (2, 1) (0, 1) = (-1055298453 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_2 : literalDescent (2, 1) (1, 0) = (-15623772467 / 6000000000000) := rfl
@[simp] theorem lookup_previous_5_2 : previousPadding literalP (2, 1) (1, 0) = (142915161443 / 1200000000000) := rfl
@[simp] theorem lookup_current_5_2 : currentPadding literalP (2, 1) (1, 0) = (-160712407 / 5000000000) := rfl
@[simp] theorem lookup_descent_5_3 : literalDescent (2, 1) (1, 1) = (-1518912019 / 2000000000000) := rfl
@[simp] theorem lookup_previous_5_3 : previousPadding literalP (2, 1) (1, 1) = (-77113287 / 10000000000) := rfl
@[simp] theorem lookup_current_5_3 : currentPadding literalP (2, 1) (1, 1) = (-11598299 / 5000000000) := rfl
@[simp] theorem lookup_descent_5_4 : literalDescent (2, 1) (2, 0) = (18866212241 / 6000000000000) := rfl
@[simp] theorem lookup_previous_5_4 : previousPadding literalP (2, 1) (2, 0) = (-209314491443 / 1200000000000) := rfl
@[simp] theorem lookup_current_5_4 : currentPadding literalP (2, 1) (2, 0) = (-37092764313 / 500000000000) := rfl
@[simp] theorem lookup_descent_5_5 : literalDescent (2, 1) (2, 1) = (4683271663 / 2000000000000) := rfl
@[simp] theorem lookup_previous_5_5 : previousPadding literalP (2, 1) (2, 1) = (28888183441 / 2000000000000) := rfl
@[simp] theorem lookup_current_5_5 : currentPadding literalP (2, 1) (2, 1) = (3609063927 / 31250000000) := rfl
@[simp] theorem lookup_descent_5_6 : literalDescent (2, 1) (3, 0) = (-41833657 / 20000000000) := rfl
@[simp] theorem lookup_previous_5_6 : previousPadding literalP (2, 1) (3, 0) = (5463039 / 100000000) := rfl
@[simp] theorem lookup_current_5_6 : currentPadding literalP (2, 1) (3, 0) = (50282747 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_7 : literalDescent (2, 1) (3, 1) = (-2223985719 / 2000000000000) := rfl
@[simp] theorem lookup_previous_5_7 : previousPadding literalP (2, 1) (3, 1) = (-11598299 / 5000000000) := rfl
@[simp] theorem lookup_current_5_7 : currentPadding literalP (2, 1) (3, 1) = (-79278607 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_8 : literalDescent (2, 1) (4, 0) = (-29068501 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_8 : previousPadding literalP (2, 1) (4, 0) = (-37476543 / 2000000000) := rfl
@[simp] theorem lookup_current_5_8 : currentPadding literalP (2, 1) (4, 0) = (-79157107 / 5000000000) := rfl
@[simp] theorem lookup_descent_5_9 : literalDescent (2, 1) (4, 1) = (-2616127 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_9 : previousPadding literalP (2, 1) (4, 1) = (-365509 / 62500000) := rfl
@[simp] theorem lookup_current_5_9 : currentPadding literalP (2, 1) (4, 1) = (-55865313 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_10 : literalDescent (2, 1) (5, 0) = (8871209677 / 2000000000000) := rfl
@[simp] theorem lookup_previous_5_10 : previousPadding literalP (2, 1) (5, 0) = (5918697 / 250000000) := rfl
@[simp] theorem lookup_current_5_10 : currentPadding literalP (2, 1) (5, 0) = (38478366323 / 2000000000000) := rfl
@[simp] theorem lookup_descent_5_11 : literalDescent (2, 1) (5, 1) = (2631679 / 5000000000) := rfl
@[simp] theorem lookup_previous_5_11 : previousPadding literalP (2, 1) (5, 1) = (26909993 / 10000000000) := rfl
@[simp] theorem lookup_current_5_11 : currentPadding literalP (2, 1) (5, 1) = (4329327 / 2000000000) := rfl
@[simp] theorem lookup_descent_5_12 : literalDescent (2, 1) (6, 0) = (-1245337 / 625000000) := rfl
@[simp] theorem lookup_previous_5_12 : previousPadding literalP (2, 1) (6, 0) = (-16110353 / 5000000000) := rfl
@[simp] theorem lookup_current_5_12 : currentPadding literalP (2, 1) (6, 0) = (-6147657 / 5000000000) := rfl
@[simp] theorem lookup_descent_5_13 : literalDescent (2, 1) (6, 1) = (-13300741 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_13 : previousPadding literalP (2, 1) (6, 1) = (-24346287 / 5000000000) := rfl
@[simp] theorem lookup_current_5_13 : currentPadding literalP (2, 1) (6, 1) = (-35391833 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_14 : literalDescent (2, 1) (7, 0) = (1533097 / 2500000000) := rfl
@[simp] theorem lookup_previous_5_14 : previousPadding literalP (2, 1) (7, 0) = (-2739353 / 2000000000) := rfl
@[simp] theorem lookup_current_5_14 : currentPadding literalP (2, 1) (7, 0) = (-19829153 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_15 : literalDescent (2, 1) (7, 1) = (354779 / 312500000) := rfl
@[simp] theorem lookup_previous_5_15 : previousPadding literalP (2, 1) (7, 1) = (45437147 / 10000000000) := rfl
@[simp] theorem lookup_current_5_15 : currentPadding literalP (2, 1) (7, 1) = (34084219 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_16 : literalDescent (2, 1) (8, 0) = (3547419 / 5000000000) := rfl
@[simp] theorem lookup_previous_5_16 : previousPadding literalP (2, 1) (8, 0) = (5106869 / 5000000000) := rfl
@[simp] theorem lookup_current_5_16 : currentPadding literalP (2, 1) (8, 0) = (31189 / 100000000) := rfl
@[simp] theorem lookup_descent_5_17 : literalDescent (2, 1) (8, 1) = (-1892563 / 5000000000) := rfl
@[simp] theorem lookup_previous_5_17 : previousPadding literalP (2, 1) (8, 1) = (-10265311 / 10000000000) := rfl
@[simp] theorem lookup_current_5_17 : currentPadding literalP (2, 1) (8, 1) = (-1296037 / 2000000000) := rfl
@[simp] theorem lookup_descent_5_18 : literalDescent (2, 1) (9, 0) = (-3318791 / 5000000000) := rfl
@[simp] theorem lookup_previous_5_18 : previousPadding literalP (2, 1) (9, 0) = (-3318791 / 5000000000) := rfl
@[simp] theorem lookup_current_5_18 : currentPadding literalP (2, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_5_19 : literalDescent (2, 1) (9, 1) = (961193 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_19 : previousPadding literalP (2, 1) (9, 1) = (961193 / 10000000000) := rfl
@[simp] theorem lookup_current_5_19 : currentPadding literalP (2, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_6_0 : literalDescent (3, 0) (0, 0) = (92536843 / 20000000000) := rfl
@[simp] theorem lookup_previous_6_0 : previousPadding literalP (3, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_6_0 : currentPadding literalP (3, 0) (0, 0) = (98406243 / 2500000000) := rfl
@[simp] theorem lookup_descent_6_1 : literalDescent (3, 0) (0, 1) = (6472026433 / 2000000000000) := rfl
@[simp] theorem lookup_previous_6_1 : previousPadding literalP (3, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_6_1 : currentPadding literalP (3, 0) (0, 1) = (81506679767 / 2000000000000) := rfl
@[simp] theorem lookup_descent_6_2 : literalDescent (3, 0) (1, 0) = (-55597171 / 4000000000) := rfl
@[simp] theorem lookup_previous_6_2 : previousPadding literalP (3, 0) (1, 0) = (-1055978157 / 10000000000) := rfl
@[simp] theorem lookup_current_6_2 : currentPadding literalP (3, 0) (1, 0) = (-458492607 / 5000000000) := rfl
@[simp] theorem lookup_descent_6_3 : literalDescent (3, 0) (1, 1) = (-1711904193 / 500000000000) := rfl
@[simp] theorem lookup_previous_6_3 : previousPadding literalP (3, 0) (1, 1) = (27284063 / 1250000000) := rfl
@[simp] theorem lookup_current_6_3 : currentPadding literalP (3, 0) (1, 1) = (-37476543 / 2000000000) := rfl
@[simp] theorem lookup_descent_6_4 : literalDescent (3, 0) (2, 0) = (-99130827 / 20000000000) := rfl
@[simp] theorem lookup_previous_6_4 : previousPadding literalP (3, 0) (2, 0) = (-610833 / 1250000000) := rfl
@[simp] theorem lookup_current_6_4 : currentPadding literalP (3, 0) (2, 0) = (-14758101 / 312500000) := rfl
@[simp] theorem lookup_descent_6_5 : literalDescent (3, 0) (2, 1) = (-41833657 / 20000000000) := rfl
@[simp] theorem lookup_previous_6_5 : previousPadding literalP (3, 0) (2, 1) = (5463039 / 100000000) := rfl
@[simp] theorem lookup_current_6_5 : currentPadding literalP (3, 0) (2, 1) = (50282747 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_6 : literalDescent (3, 0) (3, 0) = (170682071 / 5000000000) := rfl
@[simp] theorem lookup_previous_6_6 : previousPadding literalP (3, 0) (3, 0) = (1989020577 / 10000000000) := rfl
@[simp] theorem lookup_current_6_6 : currentPadding literalP (3, 0) (3, 0) = (90087279 / 500000000) := rfl
@[simp] theorem lookup_descent_6_7 : literalDescent (3, 0) (3, 1) = (1113087187 / 500000000000) := rfl
@[simp] theorem lookup_previous_6_7 : previousPadding literalP (3, 0) (3, 1) = (-37092764313 / 500000000000) := rfl
@[simp] theorem lookup_current_6_7 : currentPadding literalP (3, 0) (3, 1) = (-93090529 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_8 : literalDescent (3, 0) (4, 0) = (-219171183 / 20000000000) := rfl
@[simp] theorem lookup_previous_6_8 : previousPadding literalP (3, 0) (4, 0) = (-14758101 / 312500000) := rfl
@[simp] theorem lookup_current_6_8 : currentPadding literalP (3, 0) (4, 0) = (-439718213 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_9 : literalDescent (3, 0) (4, 1) = (-5553811961 / 1000000000000) := rfl
@[simp] theorem lookup_previous_6_9 : previousPadding literalP (3, 0) (4, 1) = (-11227663 / 312500000) := rfl
@[simp] theorem lookup_current_6_9 : currentPadding literalP (3, 0) (4, 1) = (-62752687 / 2000000000) := rfl
@[simp] theorem lookup_descent_6_10 : literalDescent (3, 0) (5, 0) = (-6814203 / 400000000) := rfl
@[simp] theorem lookup_previous_6_10 : previousPadding literalP (3, 0) (5, 0) = (-194874581 / 2500000000) := rfl
@[simp] theorem lookup_current_6_10 : currentPadding literalP (3, 0) (5, 0) = (-609143249 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_11 : literalDescent (3, 0) (5, 1) = (13599221613 / 2000000000000) := rfl
@[simp] theorem lookup_previous_6_11 : previousPadding literalP (3, 0) (5, 1) = (16237585121 / 400000000000) := rfl
@[simp] theorem lookup_current_6_11 : currentPadding literalP (3, 0) (5, 1) = (8448587999 / 250000000000) := rfl
@[simp] theorem lookup_descent_6_12 : literalDescent (3, 0) (6, 0) = (104202629 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_12 : previousPadding literalP (3, 0) (6, 0) = (338409243 / 10000000000) := rfl
@[simp] theorem lookup_current_6_12 : currentPadding literalP (3, 0) (6, 0) = (117103307 / 5000000000) := rfl
@[simp] theorem lookup_descent_6_13 : literalDescent (3, 0) (6, 1) = (3210901 / 1000000000) := rfl
@[simp] theorem lookup_previous_6_13 : previousPadding literalP (3, 0) (6, 1) = (65761553 / 10000000000) := rfl
@[simp] theorem lookup_current_6_13 : currentPadding literalP (3, 0) (6, 1) = (33652543 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_14 : literalDescent (3, 0) (7, 0) = (-26563309 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_14 : previousPadding literalP (3, 0) (7, 0) = (129407 / 312500000) := rfl
@[simp] theorem lookup_current_6_14 : currentPadding literalP (3, 0) (7, 0) = (30704333 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_15 : literalDescent (3, 0) (7, 1) = (-49239659 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_15 : previousPadding literalP (3, 0) (7, 1) = (-16748659 / 1000000000) := rfl
@[simp] theorem lookup_current_6_15 : currentPadding literalP (3, 0) (7, 1) = (-118246931 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_16 : literalDescent (3, 0) (8, 0) = (-35522463 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_16 : previousPadding literalP (3, 0) (8, 0) = (-28849027 / 5000000000) := rfl
@[simp] theorem lookup_current_6_16 : currentPadding literalP (3, 0) (8, 0) = (-22175591 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_17 : literalDescent (3, 0) (8, 1) = (113213 / 312500000) := rfl
@[simp] theorem lookup_previous_6_17 : previousPadding literalP (3, 0) (8, 1) = (25962053 / 10000000000) := rfl
@[simp] theorem lookup_current_6_17 : currentPadding literalP (3, 0) (8, 1) = (22339237 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_18 : literalDescent (3, 0) (9, 0) = (38749587 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_18 : previousPadding literalP (3, 0) (9, 0) = (38749587 / 10000000000) := rfl
@[simp] theorem lookup_current_6_18 : currentPadding literalP (3, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_6_19 : literalDescent (3, 0) (9, 1) = (1582881 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_19 : previousPadding literalP (3, 0) (9, 1) = (1582881 / 10000000000) := rfl
@[simp] theorem lookup_current_6_19 : currentPadding literalP (3, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_7_0 : literalDescent (3, 1) (0, 0) = (-1116259227 / 2000000000000) := rfl
@[simp] theorem lookup_previous_7_0 : previousPadding literalP (3, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_7_0 : currentPadding literalP (3, 1) (0, 0) = (1233703 / 625000000) := rfl
@[simp] theorem lookup_descent_7_1 : literalDescent (3, 1) (0, 1) = (-250996881 / 2000000000000) := rfl
@[simp] theorem lookup_previous_7_1 : previousPadding literalP (3, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_7_1 : currentPadding literalP (3, 1) (0, 1) = (7706081 / 5000000000) := rfl
@[simp] theorem lookup_descent_7_2 : literalDescent (3, 1) (1, 0) = (133225913 / 50000000000) := rfl
@[simp] theorem lookup_previous_7_2 : previousPadding literalP (3, 1) (1, 0) = (201585060529 / 2000000000000) := rfl
@[simp] theorem lookup_current_7_2 : currentPadding literalP (3, 1) (1, 0) = (88068465209 / 2000000000000) := rfl
@[simp] theorem lookup_descent_7_3 : literalDescent (3, 1) (1, 1) = (115896837 / 2000000000000) := rfl
@[simp] theorem lookup_previous_7_3 : previousPadding literalP (3, 1) (1, 1) = (-1055298453 / 10000000000) := rfl
@[simp] theorem lookup_current_7_3 : currentPadding literalP (3, 1) (1, 1) = (-365509 / 62500000) := rfl
@[simp] theorem lookup_descent_7_4 : literalDescent (3, 1) (2, 0) = (-5868336873 / 2000000000000) := rfl
@[simp] theorem lookup_previous_7_4 : previousPadding literalP (3, 1) (2, 0) = (-160712407 / 5000000000) := rfl
@[simp] theorem lookup_current_7_4 : currentPadding literalP (3, 1) (2, 0) = (-11227663 / 312500000) := rfl
@[simp] theorem lookup_descent_7_5 : literalDescent (3, 1) (2, 1) = (-2223985719 / 2000000000000) := rfl
@[simp] theorem lookup_previous_7_5 : previousPadding literalP (3, 1) (2, 1) = (-11598299 / 5000000000) := rfl
@[simp] theorem lookup_current_7_5 : currentPadding literalP (3, 1) (2, 1) = (-79278607 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_6 : literalDescent (3, 1) (3, 0) = (1113087187 / 500000000000) := rfl
@[simp] theorem lookup_previous_7_6 : previousPadding literalP (3, 1) (3, 0) = (-37092764313 / 500000000000) := rfl
@[simp] theorem lookup_current_7_6 : currentPadding literalP (3, 1) (3, 0) = (-93090529 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_7 : literalDescent (3, 1) (3, 1) = (331315003 / 125000000000) := rfl
@[simp] theorem lookup_previous_7_7 : previousPadding literalP (3, 1) (3, 1) = (3609063927 / 31250000000) := rfl
@[simp] theorem lookup_current_7_7 : currentPadding literalP (3, 1) (3, 1) = (38301231359 / 1000000000000) := rfl
@[simp] theorem lookup_descent_7_8 : literalDescent (3, 1) (4, 0) = (-43014771 / 20000000000) := rfl
@[simp] theorem lookup_previous_7_8 : previousPadding literalP (3, 1) (4, 0) = (50282747 / 10000000000) := rfl
@[simp] theorem lookup_current_7_8 : currentPadding literalP (3, 1) (4, 0) = (-131361 / 250000000) := rfl
@[simp] theorem lookup_descent_7_9 : literalDescent (3, 1) (4, 1) = (-419044057 / 400000000000) := rfl
@[simp] theorem lookup_previous_7_9 : previousPadding literalP (3, 1) (4, 1) = (-79278607 / 10000000000) := rfl
@[simp] theorem lookup_current_7_9 : currentPadding literalP (3, 1) (4, 1) = (-788183 / 100000000) := rfl
@[simp] theorem lookup_descent_7_10 : literalDescent (3, 1) (5, 0) = (-27690857 / 10000000000) := rfl
@[simp] theorem lookup_previous_7_10 : previousPadding literalP (3, 1) (5, 0) = (-79157107 / 5000000000) := rfl
@[simp] theorem lookup_current_7_10 : currentPadding literalP (3, 1) (5, 0) = (-130623357 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_11 : literalDescent (3, 1) (5, 1) = (-880241 / 1250000000) := rfl
@[simp] theorem lookup_previous_7_11 : previousPadding literalP (3, 1) (5, 1) = (-55865313 / 10000000000) := rfl
@[simp] theorem lookup_current_7_11 : currentPadding literalP (3, 1) (5, 1) = (-9764677 / 2000000000) := rfl
@[simp] theorem lookup_descent_7_12 : literalDescent (3, 1) (6, 0) = (3029583733 / 500000000000) := rfl
@[simp] theorem lookup_previous_7_12 : previousPadding literalP (3, 1) (6, 0) = (38478366323 / 2000000000000) := rfl
@[simp] theorem lookup_current_7_12 : currentPadding literalP (3, 1) (6, 0) = (26360031391 / 2000000000000) := rfl
@[simp] theorem lookup_descent_7_13 : literalDescent (3, 1) (6, 1) = (1032661 / 2000000000) := rfl
@[simp] theorem lookup_previous_7_13 : previousPadding literalP (3, 1) (6, 1) = (4329327 / 2000000000) := rfl
@[simp] theorem lookup_current_7_13 : currentPadding literalP (3, 1) (6, 1) = (1648333 / 1000000000) := rfl
@[simp] theorem lookup_descent_7_14 : literalDescent (3, 1) (7, 0) = (-13040791 / 5000000000) := rfl
@[simp] theorem lookup_previous_7_14 : previousPadding literalP (3, 1) (7, 0) = (-6147657 / 5000000000) := rfl
@[simp] theorem lookup_current_7_14 : currentPadding literalP (3, 1) (7, 0) = (3446567 / 2500000000) := rfl
@[simp] theorem lookup_descent_7_15 : literalDescent (3, 1) (7, 1) = (-6695353 / 5000000000) := rfl
@[simp] theorem lookup_previous_7_15 : previousPadding literalP (3, 1) (7, 1) = (-35391833 / 10000000000) := rfl
@[simp] theorem lookup_current_7_15 : currentPadding literalP (3, 1) (7, 1) = (-22001127 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_16 : literalDescent (3, 1) (8, 0) = (-301837 / 1250000000) := rfl
@[simp] theorem lookup_previous_7_16 : previousPadding literalP (3, 1) (8, 0) = (-19829153 / 10000000000) := rfl
@[simp] theorem lookup_current_7_16 : currentPadding literalP (3, 1) (8, 0) = (-17414457 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_17 : literalDescent (3, 1) (8, 1) = (4378961 / 2500000000) := rfl
@[simp] theorem lookup_previous_7_17 : previousPadding literalP (3, 1) (8, 1) = (34084219 / 10000000000) := rfl
@[simp] theorem lookup_current_7_17 : currentPadding literalP (3, 1) (8, 1) = (132547 / 80000000) := rfl
@[simp] theorem lookup_descent_7_18 : literalDescent (3, 1) (9, 0) = (31189 / 100000000) := rfl
@[simp] theorem lookup_previous_7_18 : previousPadding literalP (3, 1) (9, 0) = (31189 / 100000000) := rfl
@[simp] theorem lookup_current_7_18 : currentPadding literalP (3, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_7_19 : literalDescent (3, 1) (9, 1) = (-1296037 / 2000000000) := rfl
@[simp] theorem lookup_previous_7_19 : previousPadding literalP (3, 1) (9, 1) = (-1296037 / 2000000000) := rfl
@[simp] theorem lookup_current_7_19 : currentPadding literalP (3, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_8_0 : literalDescent (4, 0) (0, 0) = (-26536701 / 20000000000) := rfl
@[simp] theorem lookup_previous_8_0 : previousPadding literalP (4, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_8_0 : currentPadding literalP (4, 0) (0, 0) = (-11460221 / 5000000000) := rfl
@[simp] theorem lookup_descent_8_1 : literalDescent (4, 0) (0, 1) = (-2587887 / 2500000000) := rfl
@[simp] theorem lookup_previous_8_1 : previousPadding literalP (4, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_8_1 : currentPadding literalP (4, 0) (0, 1) = (-6459289 / 2500000000) := rfl
@[simp] theorem lookup_descent_8_2 : literalDescent (4, 0) (1, 0) = (82427149 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_2 : previousPadding literalP (4, 0) (1, 0) = (98406243 / 2500000000) := rfl
@[simp] theorem lookup_current_8_2 : currentPadding literalP (4, 0) (1, 0) = (399565111 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_3 : literalDescent (4, 0) (1, 1) = (4172755977 / 1000000000000) := rfl
@[simp] theorem lookup_previous_8_3 : previousPadding literalP (4, 0) (1, 1) = (81506679767 / 2000000000000) := rfl
@[simp] theorem lookup_current_8_3 : currentPadding literalP (4, 0) (1, 1) = (5918697 / 250000000) := rfl
@[simp] theorem lookup_descent_8_4 : literalDescent (4, 0) (2, 0) = (-13748689 / 1000000000) := rfl
@[simp] theorem lookup_previous_8_4 : previousPadding literalP (4, 0) (2, 0) = (-458492607 / 5000000000) := rfl
@[simp] theorem lookup_current_8_4 : currentPadding literalP (4, 0) (2, 0) = (-194874581 / 2500000000) := rfl
@[simp] theorem lookup_descent_8_5 : literalDescent (4, 0) (2, 1) = (-29068501 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_5 : previousPadding literalP (4, 0) (2, 1) = (-37476543 / 2000000000) := rfl
@[simp] theorem lookup_current_8_5 : currentPadding literalP (4, 0) (2, 1) = (-79157107 / 5000000000) := rfl
@[simp] theorem lookup_descent_8_6 : literalDescent (4, 0) (3, 0) = (-219171183 / 20000000000) := rfl
@[simp] theorem lookup_previous_8_6 : previousPadding literalP (4, 0) (3, 0) = (-14758101 / 312500000) := rfl
@[simp] theorem lookup_current_8_6 : currentPadding literalP (4, 0) (3, 0) = (-439718213 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_7 : literalDescent (4, 0) (3, 1) = (-43014771 / 20000000000) := rfl
@[simp] theorem lookup_previous_8_7 : previousPadding literalP (4, 0) (3, 1) = (50282747 / 10000000000) := rfl
@[simp] theorem lookup_current_8_7 : currentPadding literalP (4, 0) (3, 1) = (-131361 / 250000000) := rfl
@[simp] theorem lookup_descent_8_8 : literalDescent (4, 0) (4, 0) = (37540709 / 1000000000) := rfl
@[simp] theorem lookup_previous_8_8 : previousPadding literalP (4, 0) (4, 0) = (90087279 / 500000000) := rfl
@[simp] theorem lookup_current_8_8 : currentPadding literalP (4, 0) (4, 0) = (369017661 / 2500000000) := rfl
@[simp] theorem lookup_descent_8_9 : literalDescent (4, 0) (4, 1) = (70453329 / 20000000000) := rfl
@[simp] theorem lookup_previous_8_9 : previousPadding literalP (4, 0) (4, 1) = (-93090529 / 10000000000) := rfl
@[simp] theorem lookup_current_8_9 : currentPadding literalP (4, 0) (4, 1) = (-1540631 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_10 : literalDescent (4, 0) (5, 0) = (-116427657 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_10 : previousPadding literalP (4, 0) (5, 0) = (-439718213 / 10000000000) := rfl
@[simp] theorem lookup_current_8_10 : currentPadding literalP (4, 0) (5, 0) = (-348156633 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_11 : literalDescent (4, 0) (5, 1) = (-6846210273 / 1000000000000) := rfl
@[simp] theorem lookup_previous_8_11 : previousPadding literalP (4, 0) (5, 1) = (-62752687 / 2000000000) := rfl
@[simp] theorem lookup_current_8_11 : currentPadding literalP (4, 0) (5, 1) = (-776668953 / 31250000000) := rfl
@[simp] theorem lookup_descent_8_12 : literalDescent (4, 0) (6, 0) = (-51368313 / 2500000000) := rfl
@[simp] theorem lookup_previous_8_12 : previousPadding literalP (4, 0) (6, 0) = (-609143249 / 10000000000) := rfl
@[simp] theorem lookup_current_8_12 : currentPadding literalP (4, 0) (6, 0) = (-403669997 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_13 : literalDescent (4, 0) (6, 1) = (855749037 / 125000000000) := rfl
@[simp] theorem lookup_previous_8_13 : previousPadding literalP (4, 0) (6, 1) = (8448587999 / 250000000000) := rfl
@[simp] theorem lookup_current_8_13 : currentPadding literalP (4, 0) (6, 1) = (269483597 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_14 : literalDescent (4, 0) (7, 0) = (5544039 / 400000000) := rfl
@[simp] theorem lookup_previous_8_14 : previousPadding literalP (4, 0) (7, 0) = (117103307 / 5000000000) := rfl
@[simp] theorem lookup_current_8_14 : currentPadding literalP (4, 0) (7, 0) = (95605639 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_15 : literalDescent (4, 0) (7, 1) = (4515853 / 2000000000) := rfl
@[simp] theorem lookup_previous_8_15 : previousPadding literalP (4, 0) (7, 1) = (33652543 / 10000000000) := rfl
@[simp] theorem lookup_current_8_15 : currentPadding literalP (4, 0) (7, 1) = (5536639 / 5000000000) := rfl
@[simp] theorem lookup_descent_8_16 : literalDescent (4, 0) (8, 0) = (3991059 / 5000000000) := rfl
@[simp] theorem lookup_previous_8_16 : previousPadding literalP (4, 0) (8, 0) = (30704333 / 10000000000) := rfl
@[simp] theorem lookup_current_8_16 : currentPadding literalP (4, 0) (8, 0) = (4544443 / 2000000000) := rfl
@[simp] theorem lookup_descent_8_17 : literalDescent (4, 0) (8, 1) = (-7617889 / 1250000000) := rfl
@[simp] theorem lookup_previous_8_17 : previousPadding literalP (4, 0) (8, 1) = (-118246931 / 10000000000) := rfl
@[simp] theorem lookup_current_8_17 : currentPadding literalP (4, 0) (8, 1) = (-57303819 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_18 : literalDescent (4, 0) (9, 0) = (-22175591 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_18 : previousPadding literalP (4, 0) (9, 0) = (-22175591 / 10000000000) := rfl
@[simp] theorem lookup_current_8_18 : currentPadding literalP (4, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_8_19 : literalDescent (4, 0) (9, 1) = (22339237 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_19 : previousPadding literalP (4, 0) (9, 1) = (22339237 / 10000000000) := rfl
@[simp] theorem lookup_current_8_19 : currentPadding literalP (4, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_9_0 : literalDescent (4, 1) (0, 0) = (-1211312239 / 1000000000000) := rfl
@[simp] theorem lookup_previous_9_0 : previousPadding literalP (4, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_9_0 : currentPadding literalP (4, 1) (0, 0) = (-168148297 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_1 : literalDescent (4, 1) (0, 1) = (-198640463 / 400000000000) := rfl
@[simp] theorem lookup_previous_9_1 : previousPadding literalP (4, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_9_1 : currentPadding literalP (4, 1) (0, 1) = (-43824029 / 2500000000) := rfl
@[simp] theorem lookup_descent_9_2 : literalDescent (4, 1) (1, 0) = (39839541 / 20000000000) := rfl
@[simp] theorem lookup_previous_9_2 : previousPadding literalP (4, 1) (1, 0) = (1233703 / 625000000) := rfl
@[simp] theorem lookup_current_9_2 : currentPadding literalP (4, 1) (1, 0) = (352747 / 40000000) := rfl
@[simp] theorem lookup_descent_9_3 : literalDescent (4, 1) (1, 1) = (3517497 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_3 : previousPadding literalP (4, 1) (1, 1) = (7706081 / 5000000000) := rfl
@[simp] theorem lookup_current_9_3 : currentPadding literalP (4, 1) (1, 1) = (26909993 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_4 : literalDescent (4, 1) (2, 0) = (1720134901 / 500000000000) := rfl
@[simp] theorem lookup_previous_9_4 : previousPadding literalP (4, 1) (2, 0) = (88068465209 / 2000000000000) := rfl
@[simp] theorem lookup_current_9_4 : currentPadding literalP (4, 1) (2, 0) = (16237585121 / 400000000000) := rfl
@[simp] theorem lookup_descent_9_5 : literalDescent (4, 1) (2, 1) = (-2616127 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_5 : previousPadding literalP (4, 1) (2, 1) = (-365509 / 62500000) := rfl
@[simp] theorem lookup_current_9_5 : currentPadding literalP (4, 1) (2, 1) = (-55865313 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_6 : literalDescent (4, 1) (3, 0) = (-5553811961 / 1000000000000) := rfl
@[simp] theorem lookup_previous_9_6 : previousPadding literalP (4, 1) (3, 0) = (-11227663 / 312500000) := rfl
@[simp] theorem lookup_current_9_6 : currentPadding literalP (4, 1) (3, 0) = (-62752687 / 2000000000) := rfl
@[simp] theorem lookup_descent_9_7 : literalDescent (4, 1) (3, 1) = (-419044057 / 400000000000) := rfl
@[simp] theorem lookup_previous_9_7 : previousPadding literalP (4, 1) (3, 1) = (-79278607 / 10000000000) := rfl
@[simp] theorem lookup_current_9_7 : currentPadding literalP (4, 1) (3, 1) = (-788183 / 100000000) := rfl
@[simp] theorem lookup_descent_9_8 : literalDescent (4, 1) (4, 0) = (70453329 / 20000000000) := rfl
@[simp] theorem lookup_previous_9_8 : previousPadding literalP (4, 1) (4, 0) = (-93090529 / 10000000000) := rfl
@[simp] theorem lookup_current_9_8 : currentPadding literalP (4, 1) (4, 0) = (-1540631 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_9 : literalDescent (4, 1) (4, 1) = (3875731201 / 1000000000000) := rfl
@[simp] theorem lookup_previous_9_9 : previousPadding literalP (4, 1) (4, 1) = (38301231359 / 1000000000000) := rfl
@[simp] theorem lookup_current_9_9 : currentPadding literalP (4, 1) (4, 1) = (25992959943 / 1000000000000) := rfl
@[simp] theorem lookup_descent_9_10 : literalDescent (4, 1) (5, 0) = (-34440669 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_10 : previousPadding literalP (4, 1) (5, 0) = (-131361 / 250000000) := rfl
@[simp] theorem lookup_current_9_10 : currentPadding literalP (4, 1) (5, 0) = (540019 / 1250000000) := rfl
@[simp] theorem lookup_descent_9_11 : literalDescent (4, 1) (5, 1) = (-1327019601 / 1000000000000) := rfl
@[simp] theorem lookup_previous_9_11 : previousPadding literalP (4, 1) (5, 1) = (-788183 / 100000000) := rfl
@[simp] theorem lookup_current_9_11 : currentPadding literalP (4, 1) (5, 1) = (-34390347 / 5000000000) := rfl
@[simp] theorem lookup_descent_9_12 : literalDescent (4, 1) (6, 0) = (-28279929 / 5000000000) := rfl
@[simp] theorem lookup_previous_9_12 : previousPadding literalP (4, 1) (6, 0) = (-130623357 / 10000000000) := rfl
@[simp] theorem lookup_current_9_12 : currentPadding literalP (4, 1) (6, 0) = (-74063499 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_13 : literalDescent (4, 1) (6, 1) = (-9500077 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_13 : previousPadding literalP (4, 1) (6, 1) = (-9764677 / 2000000000) := rfl
@[simp] theorem lookup_current_9_13 : currentPadding literalP (4, 1) (6, 1) = (-9830827 / 2500000000) := rfl
@[simp] theorem lookup_descent_9_14 : literalDescent (4, 1) (7, 0) = (4338496799 / 500000000000) := rfl
@[simp] theorem lookup_previous_9_14 : previousPadding literalP (4, 1) (7, 0) = (26360031391 / 2000000000000) := rfl
@[simp] theorem lookup_current_9_14 : currentPadding literalP (4, 1) (7, 0) = (1801208839 / 400000000000) := rfl
@[simp] theorem lookup_descent_9_15 : literalDescent (4, 1) (7, 1) = (3489649 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_15 : previousPadding literalP (4, 1) (7, 1) = (1648333 / 1000000000) := rfl
@[simp] theorem lookup_current_9_15 : currentPadding literalP (4, 1) (7, 1) = (12993681 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_16 : literalDescent (4, 1) (8, 0) = (-252843 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_16 : previousPadding literalP (4, 1) (8, 0) = (3446567 / 2500000000) := rfl
@[simp] theorem lookup_current_9_16 : currentPadding literalP (4, 1) (8, 0) = (14039111 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_17 : literalDescent (4, 1) (8, 1) = (-67201 / 31250000) := rfl
@[simp] theorem lookup_previous_9_17 : previousPadding literalP (4, 1) (8, 1) = (-22001127 / 10000000000) := rfl
@[simp] theorem lookup_current_9_17 : currentPadding literalP (4, 1) (8, 1) = (-496807 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_18 : literalDescent (4, 1) (9, 0) = (-17414457 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_18 : previousPadding literalP (4, 1) (9, 0) = (-17414457 / 10000000000) := rfl
@[simp] theorem lookup_current_9_18 : currentPadding literalP (4, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_9_19 : literalDescent (4, 1) (9, 1) = (132547 / 80000000) := rfl
@[simp] theorem lookup_previous_9_19 : previousPadding literalP (4, 1) (9, 1) = (132547 / 80000000) := rfl
@[simp] theorem lookup_current_9_19 : currentPadding literalP (4, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_10_0 : literalDescent (5, 0) (0, 0) = (175693 / 800000000) := rfl
@[simp] theorem lookup_previous_10_0 : previousPadding literalP (5, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_10_0 : currentPadding literalP (5, 0) (0, 0) = (1534173 / 2000000000) := rfl
@[simp] theorem lookup_descent_10_1 : literalDescent (5, 0) (0, 1) = (-46089 / 2000000000) := rfl
@[simp] theorem lookup_previous_10_1 : previousPadding literalP (5, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_10_1 : currentPadding literalP (5, 0) (0, 1) = (2524381 / 2500000000) := rfl
@[simp] theorem lookup_descent_10_2 : literalDescent (5, 0) (1, 0) = (-423479 / 800000000) := rfl
@[simp] theorem lookup_previous_10_2 : previousPadding literalP (5, 0) (1, 0) = (-11460221 / 5000000000) := rfl
@[simp] theorem lookup_current_10_2 : currentPadding literalP (5, 0) (1, 0) = (-17626927 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_3 : literalDescent (5, 0) (1, 1) = (-87087103 / 250000000000) := rfl
@[simp] theorem lookup_previous_10_3 : previousPadding literalP (5, 0) (1, 1) = (-6459289 / 2500000000) := rfl
@[simp] theorem lookup_current_10_3 : currentPadding literalP (5, 0) (1, 1) = (-16110353 / 5000000000) := rfl
@[simp] theorem lookup_descent_10_4 : literalDescent (5, 0) (2, 0) = (15288967 / 2500000000) := rfl
@[simp] theorem lookup_previous_10_4 : previousPadding literalP (5, 0) (2, 0) = (399565111 / 10000000000) := rfl
@[simp] theorem lookup_current_10_4 : currentPadding literalP (5, 0) (2, 0) = (338409243 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_5 : literalDescent (5, 0) (2, 1) = (8871209677 / 2000000000000) := rfl
@[simp] theorem lookup_previous_10_5 : previousPadding literalP (5, 0) (2, 1) = (5918697 / 250000000) := rfl
@[simp] theorem lookup_current_10_5 : currentPadding literalP (5, 0) (2, 1) = (38478366323 / 2000000000000) := rfl
@[simp] theorem lookup_descent_10_6 : literalDescent (5, 0) (3, 0) = (-6814203 / 400000000) := rfl
@[simp] theorem lookup_previous_10_6 : previousPadding literalP (5, 0) (3, 0) = (-194874581 / 2500000000) := rfl
@[simp] theorem lookup_current_10_6 : currentPadding literalP (5, 0) (3, 0) = (-609143249 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_7 : literalDescent (5, 0) (3, 1) = (-27690857 / 10000000000) := rfl
@[simp] theorem lookup_previous_10_7 : previousPadding literalP (5, 0) (3, 1) = (-79157107 / 5000000000) := rfl
@[simp] theorem lookup_current_10_7 : currentPadding literalP (5, 0) (3, 1) = (-130623357 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_8 : literalDescent (5, 0) (4, 0) = (-116427657 / 10000000000) := rfl
@[simp] theorem lookup_previous_10_8 : previousPadding literalP (5, 0) (4, 0) = (-439718213 / 10000000000) := rfl
@[simp] theorem lookup_current_10_8 : currentPadding literalP (5, 0) (4, 0) = (-348156633 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_9 : literalDescent (5, 0) (4, 1) = (-34440669 / 10000000000) := rfl
@[simp] theorem lookup_previous_10_9 : previousPadding literalP (5, 0) (4, 1) = (-131361 / 250000000) := rfl
@[simp] theorem lookup_current_10_9 : currentPadding literalP (5, 0) (4, 1) = (540019 / 1250000000) := rfl
@[simp] theorem lookup_descent_10_10 : literalDescent (5, 0) (5, 0) = (218262301 / 5000000000) := rfl
@[simp] theorem lookup_previous_10_10 : previousPadding literalP (5, 0) (5, 0) = (369017661 / 2500000000) := rfl
@[simp] theorem lookup_current_10_10 : currentPadding literalP (5, 0) (5, 0) = (534772043 / 5000000000) := rfl
@[simp] theorem lookup_descent_10_11 : literalDescent (5, 0) (5, 1) = (29346099 / 20000000000) := rfl
@[simp] theorem lookup_previous_10_11 : previousPadding literalP (5, 0) (5, 1) = (-1540631 / 10000000000) := rfl
@[simp] theorem lookup_current_10_11 : currentPadding literalP (5, 0) (5, 1) = (38648767 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_12 : literalDescent (5, 0) (6, 0) = (-7252517 / 2500000000) := rfl
@[simp] theorem lookup_previous_10_12 : previousPadding literalP (5, 0) (6, 0) = (-348156633 / 10000000000) := rfl
@[simp] theorem lookup_current_10_12 : currentPadding literalP (5, 0) (6, 0) = (-334145587 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_13 : literalDescent (5, 0) (6, 1) = (-14595691353 / 2000000000000) := rfl
@[simp] theorem lookup_previous_10_13 : previousPadding literalP (5, 0) (6, 1) = (-776668953 / 31250000000) := rfl
@[simp] theorem lookup_current_10_13 : currentPadding literalP (5, 0) (6, 1) = (-177506937 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_14 : literalDescent (5, 0) (7, 0) = (-51686991 / 2000000000) := rfl
@[simp] theorem lookup_previous_10_14 : previousPadding literalP (5, 0) (7, 0) = (-403669997 / 10000000000) := rfl
@[simp] theorem lookup_current_10_14 : currentPadding literalP (5, 0) (7, 0) = (-72617521 / 5000000000) := rfl
@[simp] theorem lookup_descent_10_15 : literalDescent (5, 0) (7, 1) = (16292303 / 2000000000) := rfl
@[simp] theorem lookup_previous_10_15 : previousPadding literalP (5, 0) (7, 1) = (269483597 / 10000000000) := rfl
@[simp] theorem lookup_current_10_15 : currentPadding literalP (5, 0) (7, 1) = (94011041 / 5000000000) := rfl
@[simp] theorem lookup_descent_10_16 : literalDescent (5, 0) (8, 0) = (11384479 / 2000000000) := rfl
@[simp] theorem lookup_previous_10_16 : previousPadding literalP (5, 0) (8, 0) = (95605639 / 10000000000) := rfl
@[simp] theorem lookup_current_10_16 : currentPadding literalP (5, 0) (8, 0) = (9670811 / 2500000000) := rfl
@[simp] theorem lookup_descent_10_17 : literalDescent (5, 0) (8, 1) = (27818559 / 5000000000) := rfl
@[simp] theorem lookup_previous_10_17 : previousPadding literalP (5, 0) (8, 1) = (5536639 / 5000000000) := rfl
@[simp] theorem lookup_current_10_17 : currentPadding literalP (5, 0) (8, 1) = (-69631 / 15625000) := rfl
@[simp] theorem lookup_descent_10_18 : literalDescent (5, 0) (9, 0) = (4544443 / 2000000000) := rfl
@[simp] theorem lookup_previous_10_18 : previousPadding literalP (5, 0) (9, 0) = (4544443 / 2000000000) := rfl
@[simp] theorem lookup_current_10_18 : currentPadding literalP (5, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_10_19 : literalDescent (5, 0) (9, 1) = (-57303819 / 10000000000) := rfl
@[simp] theorem lookup_previous_10_19 : previousPadding literalP (5, 0) (9, 1) = (-57303819 / 10000000000) := rfl
@[simp] theorem lookup_current_10_19 : currentPadding literalP (5, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_11_0 : literalDescent (5, 1) (0, 0) = (1339159969 / 1000000000000) := rfl
@[simp] theorem lookup_previous_11_0 : previousPadding literalP (5, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_11_0 : currentPadding literalP (5, 1) (0, 0) = (4793121 / 1250000000) := rfl
@[simp] theorem lookup_descent_11_1 : literalDescent (5, 1) (0, 1) = (774265751 / 1000000000000) := rfl
@[simp] theorem lookup_previous_11_1 : previousPadding literalP (5, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_11_1 : currentPadding literalP (5, 1) (0, 1) = (21996047 / 5000000000) := rfl
@[simp] theorem lookup_descent_11_2 : literalDescent (5, 1) (1, 0) = (-728569 / 160000000) := rfl
@[simp] theorem lookup_previous_11_2 : previousPadding literalP (5, 1) (1, 0) = (-168148297 / 10000000000) := rfl
@[simp] theorem lookup_current_11_2 : currentPadding literalP (5, 1) (1, 0) = (-42195999 / 2000000000) := rfl
@[simp] theorem lookup_descent_11_3 : literalDescent (5, 1) (1, 1) = (-104732131 / 80000000000) := rfl
@[simp] theorem lookup_previous_11_3 : previousPadding literalP (5, 1) (1, 1) = (-43824029 / 2500000000) := rfl
@[simp] theorem lookup_current_11_3 : currentPadding literalP (5, 1) (1, 1) = (-24346287 / 5000000000) := rfl
@[simp] theorem lookup_descent_11_4 : literalDescent (5, 1) (2, 0) = (22425197 / 10000000000) := rfl
@[simp] theorem lookup_previous_11_4 : previousPadding literalP (5, 1) (2, 0) = (352747 / 40000000) := rfl
@[simp] theorem lookup_current_11_4 : currentPadding literalP (5, 1) (2, 0) = (65761553 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_5 : literalDescent (5, 1) (2, 1) = (2631679 / 5000000000) := rfl
@[simp] theorem lookup_previous_11_5 : previousPadding literalP (5, 1) (2, 1) = (26909993 / 10000000000) := rfl
@[simp] theorem lookup_current_11_5 : currentPadding literalP (5, 1) (2, 1) = (4329327 / 2000000000) := rfl
@[simp] theorem lookup_descent_11_6 : literalDescent (5, 1) (3, 0) = (13599221613 / 2000000000000) := rfl
@[simp] theorem lookup_previous_11_6 : previousPadding literalP (5, 1) (3, 0) = (16237585121 / 400000000000) := rfl
@[simp] theorem lookup_current_11_6 : currentPadding literalP (5, 1) (3, 0) = (8448587999 / 250000000000) := rfl
@[simp] theorem lookup_descent_11_7 : literalDescent (5, 1) (3, 1) = (-880241 / 1250000000) := rfl
@[simp] theorem lookup_previous_11_7 : previousPadding literalP (5, 1) (3, 1) = (-55865313 / 10000000000) := rfl
@[simp] theorem lookup_current_11_7 : currentPadding literalP (5, 1) (3, 1) = (-9764677 / 2000000000) := rfl
@[simp] theorem lookup_descent_11_8 : literalDescent (5, 1) (4, 0) = (-6846210273 / 1000000000000) := rfl
@[simp] theorem lookup_previous_11_8 : previousPadding literalP (5, 1) (4, 0) = (-62752687 / 2000000000) := rfl
@[simp] theorem lookup_current_11_8 : currentPadding literalP (5, 1) (4, 0) = (-776668953 / 31250000000) := rfl
@[simp] theorem lookup_descent_11_9 : literalDescent (5, 1) (4, 1) = (-1327019601 / 1000000000000) := rfl
@[simp] theorem lookup_previous_11_9 : previousPadding literalP (5, 1) (4, 1) = (-788183 / 100000000) := rfl
@[simp] theorem lookup_current_11_9 : currentPadding literalP (5, 1) (4, 1) = (-34390347 / 5000000000) := rfl
@[simp] theorem lookup_descent_11_10 : literalDescent (5, 1) (5, 0) = (29346099 / 20000000000) := rfl
@[simp] theorem lookup_previous_11_10 : previousPadding literalP (5, 1) (5, 0) = (-1540631 / 10000000000) := rfl
@[simp] theorem lookup_current_11_10 : currentPadding literalP (5, 1) (5, 0) = (38648767 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_11 : literalDescent (5, 1) (5, 1) = (7818813547 / 2000000000000) := rfl
@[simp] theorem lookup_previous_11_11 : previousPadding literalP (5, 1) (5, 1) = (25992959943 / 1000000000000) := rfl
@[simp] theorem lookup_current_11_11 : currentPadding literalP (5, 1) (5, 1) = (41513320343 / 2000000000000) := rfl
@[simp] theorem lookup_descent_11_12 : literalDescent (5, 1) (6, 0) = (7311217 / 10000000000) := rfl
@[simp] theorem lookup_previous_11_12 : previousPadding literalP (5, 1) (6, 0) = (540019 / 1250000000) := rfl
@[simp] theorem lookup_current_11_12 : currentPadding literalP (5, 1) (6, 0) = (-17990087 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_13 : literalDescent (5, 1) (6, 1) = (-472229993 / 500000000000) := rfl
@[simp] theorem lookup_previous_11_13 : previousPadding literalP (5, 1) (6, 1) = (-34390347 / 5000000000) := rfl
@[simp] theorem lookup_current_11_13 : currentPadding literalP (5, 1) (6, 1) = (-61285967 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_14 : literalDescent (5, 1) (7, 0) = (-16816941 / 5000000000) := rfl
@[simp] theorem lookup_previous_11_14 : previousPadding literalP (5, 1) (7, 0) = (-74063499 / 10000000000) := rfl
@[simp] theorem lookup_current_11_14 : currentPadding literalP (5, 1) (7, 0) = (-40429617 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_15 : literalDescent (5, 1) (7, 1) = (-12269171 / 10000000000) := rfl
@[simp] theorem lookup_previous_11_15 : previousPadding literalP (5, 1) (7, 1) = (-9830827 / 2500000000) := rfl
@[simp] theorem lookup_current_11_15 : currentPadding literalP (5, 1) (7, 1) = (-27054137 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_16 : literalDescent (5, 1) (8, 0) = (311810599 / 400000000000) := rfl
@[simp] theorem lookup_previous_11_16 : previousPadding literalP (5, 1) (8, 0) = (1801208839 / 400000000000) := rfl
@[simp] theorem lookup_current_11_16 : currentPadding literalP (5, 1) (8, 0) = (9308739 / 2500000000) := rfl
@[simp] theorem lookup_descent_11_17 : literalDescent (5, 1) (8, 1) = (702827 / 2000000000) := rfl
@[simp] theorem lookup_previous_11_17 : previousPadding literalP (5, 1) (8, 1) = (12993681 / 10000000000) := rfl
@[simp] theorem lookup_current_11_17 : currentPadding literalP (5, 1) (8, 1) = (4739773 / 5000000000) := rfl
@[simp] theorem lookup_descent_11_18 : literalDescent (5, 1) (9, 0) = (14039111 / 10000000000) := rfl
@[simp] theorem lookup_previous_11_18 : previousPadding literalP (5, 1) (9, 0) = (14039111 / 10000000000) := rfl
@[simp] theorem lookup_current_11_18 : currentPadding literalP (5, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_11_19 : literalDescent (5, 1) (9, 1) = (-496807 / 10000000000) := rfl
@[simp] theorem lookup_previous_11_19 : previousPadding literalP (5, 1) (9, 1) = (-496807 / 10000000000) := rfl
@[simp] theorem lookup_current_11_19 : currentPadding literalP (5, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_12_0 : literalDescent (6, 0) (0, 0) = (-12650727 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_0 : previousPadding literalP (6, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_12_0 : currentPadding literalP (6, 0) (0, 0) = (1936951 / 1000000000) := rfl
@[simp] theorem lookup_descent_12_1 : literalDescent (6, 0) (0, 1) = (2078807 / 20000000000) := rfl
@[simp] theorem lookup_previous_12_1 : previousPadding literalP (6, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_12_1 : currentPadding literalP (6, 0) (0, 1) = (283971 / 500000000) := rfl
@[simp] theorem lookup_descent_12_2 : literalDescent (6, 0) (1, 0) = (327849 / 160000000) := rfl
@[simp] theorem lookup_previous_12_2 : previousPadding literalP (6, 0) (1, 0) = (1534173 / 2000000000) := rfl
@[simp] theorem lookup_current_12_2 : currentPadding literalP (6, 0) (1, 0) = (-227069 / 500000000) := rfl
@[simp] theorem lookup_descent_12_3 : literalDescent (6, 0) (1, 1) = (159508751 / 1000000000000) := rfl
@[simp] theorem lookup_previous_12_3 : previousPadding literalP (6, 0) (1, 1) = (2524381 / 2500000000) := rfl
@[simp] theorem lookup_current_12_3 : currentPadding literalP (6, 0) (1, 1) = (-2739353 / 2000000000) := rfl
@[simp] theorem lookup_descent_12_4 : literalDescent (6, 0) (2, 0) = (-21767951 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_4 : previousPadding literalP (6, 0) (2, 0) = (-17626927 / 10000000000) := rfl
@[simp] theorem lookup_current_12_4 : currentPadding literalP (6, 0) (2, 0) = (129407 / 312500000) := rfl
@[simp] theorem lookup_descent_12_5 : literalDescent (6, 0) (2, 1) = (-1245337 / 625000000) := rfl
@[simp] theorem lookup_previous_12_5 : previousPadding literalP (6, 0) (2, 1) = (-16110353 / 5000000000) := rfl
@[simp] theorem lookup_current_12_5 : currentPadding literalP (6, 0) (2, 1) = (-6147657 / 5000000000) := rfl
@[simp] theorem lookup_descent_12_6 : literalDescent (6, 0) (3, 0) = (104202629 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_6 : previousPadding literalP (6, 0) (3, 0) = (338409243 / 10000000000) := rfl
@[simp] theorem lookup_current_12_6 : currentPadding literalP (6, 0) (3, 0) = (117103307 / 5000000000) := rfl
@[simp] theorem lookup_descent_12_7 : literalDescent (6, 0) (3, 1) = (3029583733 / 500000000000) := rfl
@[simp] theorem lookup_previous_12_7 : previousPadding literalP (6, 0) (3, 1) = (38478366323 / 2000000000000) := rfl
@[simp] theorem lookup_current_12_7 : currentPadding literalP (6, 0) (3, 1) = (26360031391 / 2000000000000) := rfl
@[simp] theorem lookup_descent_12_8 : literalDescent (6, 0) (4, 0) = (-51368313 / 2500000000) := rfl
@[simp] theorem lookup_previous_12_8 : previousPadding literalP (6, 0) (4, 0) = (-609143249 / 10000000000) := rfl
@[simp] theorem lookup_current_12_8 : currentPadding literalP (6, 0) (4, 0) = (-403669997 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_9 : literalDescent (6, 0) (4, 1) = (-28279929 / 5000000000) := rfl
@[simp] theorem lookup_previous_12_9 : previousPadding literalP (6, 0) (4, 1) = (-130623357 / 10000000000) := rfl
@[simp] theorem lookup_current_12_9 : currentPadding literalP (6, 0) (4, 1) = (-74063499 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_10 : literalDescent (6, 0) (5, 0) = (-7252517 / 2500000000) := rfl
@[simp] theorem lookup_previous_12_10 : previousPadding literalP (6, 0) (5, 0) = (-348156633 / 10000000000) := rfl
@[simp] theorem lookup_current_12_10 : currentPadding literalP (6, 0) (5, 0) = (-334145587 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_11 : literalDescent (6, 0) (5, 1) = (7311217 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_11 : previousPadding literalP (6, 0) (5, 1) = (540019 / 1250000000) := rfl
@[simp] theorem lookup_current_12_11 : currentPadding literalP (6, 0) (5, 1) = (-17990087 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_12 : literalDescent (6, 0) (6, 0) = (371485861 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_12 : previousPadding literalP (6, 0) (6, 0) = (534772043 / 5000000000) := rfl
@[simp] theorem lookup_current_12_12 : currentPadding literalP (6, 0) (6, 0) = (174515517 / 2500000000) := rfl
@[simp] theorem lookup_descent_12_13 : literalDescent (6, 0) (6, 1) = (20979931 / 20000000000) := rfl
@[simp] theorem lookup_previous_12_13 : previousPadding literalP (6, 0) (6, 1) = (38648767 / 10000000000) := rfl
@[simp] theorem lookup_current_12_13 : currentPadding literalP (6, 0) (6, 1) = (2697569 / 625000000) := rfl
@[simp] theorem lookup_descent_12_14 : literalDescent (6, 0) (7, 0) = (-455743847 / 20000000000) := rfl
@[simp] theorem lookup_previous_12_14 : previousPadding literalP (6, 0) (7, 0) = (-334145587 / 10000000000) := rfl
@[simp] theorem lookup_current_12_14 : currentPadding literalP (6, 0) (7, 0) = (-21255117 / 2000000000) := rfl
@[simp] theorem lookup_descent_12_15 : literalDescent (6, 0) (7, 1) = (-6405985717 / 1000000000000) := rfl
@[simp] theorem lookup_previous_12_15 : previousPadding literalP (6, 0) (7, 1) = (-177506937 / 10000000000) := rfl
@[simp] theorem lookup_current_12_15 : currentPadding literalP (6, 0) (7, 1) = (-113447819 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_16 : literalDescent (6, 0) (8, 0) = (-304707 / 80000000) := rfl
@[simp] theorem lookup_previous_12_16 : previousPadding literalP (6, 0) (8, 0) = (-72617521 / 5000000000) := rfl
@[simp] theorem lookup_current_12_16 : currentPadding literalP (6, 0) (8, 0) = (-107146667 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_17 : literalDescent (6, 0) (8, 1) = (104081599 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_17 : previousPadding literalP (6, 0) (8, 1) = (94011041 / 5000000000) := rfl
@[simp] theorem lookup_current_12_17 : currentPadding literalP (6, 0) (8, 1) = (83940483 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_18 : literalDescent (6, 0) (9, 0) = (9670811 / 2500000000) := rfl
@[simp] theorem lookup_previous_12_18 : previousPadding literalP (6, 0) (9, 0) = (9670811 / 2500000000) := rfl
@[simp] theorem lookup_current_12_18 : currentPadding literalP (6, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_12_19 : literalDescent (6, 0) (9, 1) = (-69631 / 15625000) := rfl
@[simp] theorem lookup_previous_12_19 : previousPadding literalP (6, 0) (9, 1) = (-69631 / 15625000) := rfl
@[simp] theorem lookup_current_12_19 : currentPadding literalP (6, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_13_0 : literalDescent (6, 1) (0, 0) = (150821561 / 2000000000000) := rfl
@[simp] theorem lookup_previous_13_0 : previousPadding literalP (6, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_13_0 : currentPadding literalP (6, 1) (0, 0) = (-441629 / 200000000) := rfl
@[simp] theorem lookup_descent_13_1 : literalDescent (6, 1) (0, 1) = (25877267 / 125000000000) := rfl
@[simp] theorem lookup_previous_13_1 : previousPadding literalP (6, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_13_1 : currentPadding literalP (6, 1) (0, 1) = (-11699771 / 5000000000) := rfl
@[simp] theorem lookup_descent_13_2 : literalDescent (6, 1) (1, 0) = (8410359 / 10000000000) := rfl
@[simp] theorem lookup_previous_13_2 : previousPadding literalP (6, 1) (1, 0) = (4793121 / 1250000000) := rfl
@[simp] theorem lookup_current_13_2 : currentPadding literalP (6, 1) (1, 0) = (38212899 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_3 : literalDescent (6, 1) (1, 1) = (220195267 / 500000000000) := rfl
@[simp] theorem lookup_previous_13_3 : previousPadding literalP (6, 1) (1, 1) = (21996047 / 5000000000) := rfl
@[simp] theorem lookup_current_13_3 : currentPadding literalP (6, 1) (1, 1) = (45437147 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_4 : literalDescent (6, 1) (2, 0) = (-8698681 / 2000000000) := rfl
@[simp] theorem lookup_previous_13_4 : previousPadding literalP (6, 1) (2, 0) = (-42195999 / 2000000000) := rfl
@[simp] theorem lookup_current_13_4 : currentPadding literalP (6, 1) (2, 0) = (-16748659 / 1000000000) := rfl
@[simp] theorem lookup_descent_13_5 : literalDescent (6, 1) (2, 1) = (-13300741 / 10000000000) := rfl
@[simp] theorem lookup_previous_13_5 : previousPadding literalP (6, 1) (2, 1) = (-24346287 / 5000000000) := rfl
@[simp] theorem lookup_current_13_5 : currentPadding literalP (6, 1) (2, 1) = (-35391833 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_6 : literalDescent (6, 1) (3, 0) = (3210901 / 1000000000) := rfl
@[simp] theorem lookup_previous_13_6 : previousPadding literalP (6, 1) (3, 0) = (65761553 / 10000000000) := rfl
@[simp] theorem lookup_current_13_6 : currentPadding literalP (6, 1) (3, 0) = (33652543 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_7 : literalDescent (6, 1) (3, 1) = (1032661 / 2000000000) := rfl
@[simp] theorem lookup_previous_13_7 : previousPadding literalP (6, 1) (3, 1) = (4329327 / 2000000000) := rfl
@[simp] theorem lookup_current_13_7 : currentPadding literalP (6, 1) (3, 1) = (1648333 / 1000000000) := rfl
@[simp] theorem lookup_descent_13_8 : literalDescent (6, 1) (4, 0) = (855749037 / 125000000000) := rfl
@[simp] theorem lookup_previous_13_8 : previousPadding literalP (6, 1) (4, 0) = (8448587999 / 250000000000) := rfl
@[simp] theorem lookup_current_13_8 : currentPadding literalP (6, 1) (4, 0) = (269483597 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_9 : literalDescent (6, 1) (4, 1) = (-9500077 / 10000000000) := rfl
@[simp] theorem lookup_previous_13_9 : previousPadding literalP (6, 1) (4, 1) = (-9764677 / 2000000000) := rfl
@[simp] theorem lookup_current_13_9 : currentPadding literalP (6, 1) (4, 1) = (-9830827 / 2500000000) := rfl
@[simp] theorem lookup_descent_13_10 : literalDescent (6, 1) (5, 0) = (-14595691353 / 2000000000000) := rfl
@[simp] theorem lookup_previous_13_10 : previousPadding literalP (6, 1) (5, 0) = (-776668953 / 31250000000) := rfl
@[simp] theorem lookup_current_13_10 : currentPadding literalP (6, 1) (5, 0) = (-177506937 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_11 : literalDescent (6, 1) (5, 1) = (-472229993 / 500000000000) := rfl
@[simp] theorem lookup_previous_13_11 : previousPadding literalP (6, 1) (5, 1) = (-34390347 / 5000000000) := rfl
@[simp] theorem lookup_current_13_11 : currentPadding literalP (6, 1) (5, 1) = (-61285967 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_12 : literalDescent (6, 1) (6, 0) = (20979931 / 20000000000) := rfl
@[simp] theorem lookup_previous_13_12 : previousPadding literalP (6, 1) (6, 0) = (38648767 / 10000000000) := rfl
@[simp] theorem lookup_current_13_12 : currentPadding literalP (6, 1) (6, 0) = (2697569 / 625000000) := rfl
@[simp] theorem lookup_descent_13_13 : literalDescent (6, 1) (6, 1) = (9715388591 / 2000000000000) := rfl
@[simp] theorem lookup_previous_13_13 : previousPadding literalP (6, 1) (6, 1) = (41513320343 / 2000000000000) := rfl
@[simp] theorem lookup_current_13_13 : currentPadding literalP (6, 1) (6, 1) = (3322380087 / 250000000000) := rfl
@[simp] theorem lookup_descent_13_14 : literalDescent (6, 1) (7, 0) = (-6211379 / 20000000000) := rfl
@[simp] theorem lookup_previous_13_14 : previousPadding literalP (6, 1) (7, 0) = (-17990087 / 10000000000) := rfl
@[simp] theorem lookup_current_13_14 : currentPadding literalP (6, 1) (7, 0) = (-14886319 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_15 : literalDescent (6, 1) (7, 1) = (-2913642159 / 2000000000000) := rfl
@[simp] theorem lookup_previous_13_15 : previousPadding literalP (6, 1) (7, 1) = (-61285967 / 10000000000) := rfl
@[simp] theorem lookup_current_13_15 : currentPadding literalP (6, 1) (7, 1) = (-23359003 / 5000000000) := rfl
@[simp] theorem lookup_descent_13_16 : literalDescent (6, 1) (8, 0) = (-3788077 / 1000000000) := rfl
@[simp] theorem lookup_previous_13_16 : previousPadding literalP (6, 1) (8, 0) = (-40429617 / 10000000000) := rfl
@[simp] theorem lookup_current_13_16 : currentPadding literalP (6, 1) (8, 0) = (-2548847 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_17 : literalDescent (6, 1) (8, 1) = (-5720063 / 2500000000) := rfl
@[simp] theorem lookup_previous_13_17 : previousPadding literalP (6, 1) (8, 1) = (-27054137 / 10000000000) := rfl
@[simp] theorem lookup_current_13_17 : currentPadding literalP (6, 1) (8, 1) = (-834777 / 2000000000) := rfl
@[simp] theorem lookup_descent_13_18 : literalDescent (6, 1) (9, 0) = (9308739 / 2500000000) := rfl
@[simp] theorem lookup_previous_13_18 : previousPadding literalP (6, 1) (9, 0) = (9308739 / 2500000000) := rfl
@[simp] theorem lookup_current_13_18 : currentPadding literalP (6, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_13_19 : literalDescent (6, 1) (9, 1) = (4739773 / 5000000000) := rfl
@[simp] theorem lookup_previous_13_19 : previousPadding literalP (6, 1) (9, 1) = (4739773 / 5000000000) := rfl
@[simp] theorem lookup_current_13_19 : currentPadding literalP (6, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_14_0 : literalDescent (7, 0) (0, 0) = (-2502637 / 2500000000) := rfl
@[simp] theorem lookup_previous_14_0 : previousPadding literalP (7, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_14_0 : currentPadding literalP (7, 0) (0, 0) = (5405339 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_1 : literalDescent (7, 0) (0, 1) = (-18622063 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_1 : previousPadding literalP (7, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_14_1 : currentPadding literalP (7, 0) (0, 1) = (4705859 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_2 : literalDescent (7, 0) (1, 0) = (-327987 / 2000000000) := rfl
@[simp] theorem lookup_previous_14_2 : previousPadding literalP (7, 0) (1, 0) = (1936951 / 1000000000) := rfl
@[simp] theorem lookup_current_14_2 : currentPadding literalP (7, 0) (1, 0) = (2626187 / 1250000000) := rfl
@[simp] theorem lookup_descent_14_3 : literalDescent (7, 0) (1, 1) = (14165477 / 2000000000000) := rfl
@[simp] theorem lookup_previous_14_3 : previousPadding literalP (7, 0) (1, 1) = (283971 / 500000000) := rfl
@[simp] theorem lookup_current_14_3 : currentPadding literalP (7, 0) (1, 1) = (5106869 / 5000000000) := rfl
@[simp] theorem lookup_descent_14_4 : literalDescent (7, 0) (2, 0) = (26578337 / 5000000000) := rfl
@[simp] theorem lookup_previous_14_4 : previousPadding literalP (7, 0) (2, 0) = (-227069 / 500000000) := rfl
@[simp] theorem lookup_current_14_4 : currentPadding literalP (7, 0) (2, 0) = (-28849027 / 5000000000) := rfl
@[simp] theorem lookup_descent_14_5 : literalDescent (7, 0) (2, 1) = (1533097 / 2500000000) := rfl
@[simp] theorem lookup_previous_14_5 : previousPadding literalP (7, 0) (2, 1) = (-2739353 / 2000000000) := rfl
@[simp] theorem lookup_current_14_5 : currentPadding literalP (7, 0) (2, 1) = (-19829153 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_6 : literalDescent (7, 0) (3, 0) = (-26563309 / 10000000000) := rfl
@[simp] theorem lookup_previous_14_6 : previousPadding literalP (7, 0) (3, 0) = (129407 / 312500000) := rfl
@[simp] theorem lookup_current_14_6 : currentPadding literalP (7, 0) (3, 0) = (30704333 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_7 : literalDescent (7, 0) (3, 1) = (-13040791 / 5000000000) := rfl
@[simp] theorem lookup_previous_14_7 : previousPadding literalP (7, 0) (3, 1) = (-6147657 / 5000000000) := rfl
@[simp] theorem lookup_current_14_7 : currentPadding literalP (7, 0) (3, 1) = (3446567 / 2500000000) := rfl
@[simp] theorem lookup_descent_14_8 : literalDescent (7, 0) (4, 0) = (5544039 / 400000000) := rfl
@[simp] theorem lookup_previous_14_8 : previousPadding literalP (7, 0) (4, 0) = (117103307 / 5000000000) := rfl
@[simp] theorem lookup_current_14_8 : currentPadding literalP (7, 0) (4, 0) = (95605639 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_9 : literalDescent (7, 0) (4, 1) = (4338496799 / 500000000000) := rfl
@[simp] theorem lookup_previous_14_9 : previousPadding literalP (7, 0) (4, 1) = (26360031391 / 2000000000000) := rfl
@[simp] theorem lookup_current_14_9 : currentPadding literalP (7, 0) (4, 1) = (1801208839 / 400000000000) := rfl
@[simp] theorem lookup_descent_14_10 : literalDescent (7, 0) (5, 0) = (-51686991 / 2000000000) := rfl
@[simp] theorem lookup_previous_14_10 : previousPadding literalP (7, 0) (5, 0) = (-403669997 / 10000000000) := rfl
@[simp] theorem lookup_current_14_10 : currentPadding literalP (7, 0) (5, 0) = (-72617521 / 5000000000) := rfl
@[simp] theorem lookup_descent_14_11 : literalDescent (7, 0) (5, 1) = (-16816941 / 5000000000) := rfl
@[simp] theorem lookup_previous_14_11 : previousPadding literalP (7, 0) (5, 1) = (-74063499 / 10000000000) := rfl
@[simp] theorem lookup_current_14_11 : currentPadding literalP (7, 0) (5, 1) = (-40429617 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_12 : literalDescent (7, 0) (6, 0) = (-455743847 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_12 : previousPadding literalP (7, 0) (6, 0) = (-334145587 / 10000000000) := rfl
@[simp] theorem lookup_current_14_12 : currentPadding literalP (7, 0) (6, 0) = (-21255117 / 2000000000) := rfl
@[simp] theorem lookup_descent_14_13 : literalDescent (7, 0) (6, 1) = (-6211379 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_13 : previousPadding literalP (7, 0) (6, 1) = (-17990087 / 10000000000) := rfl
@[simp] theorem lookup_current_14_13 : currentPadding literalP (7, 0) (6, 1) = (-14886319 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_14 : literalDescent (7, 0) (7, 0) = (474598673 / 10000000000) := rfl
@[simp] theorem lookup_previous_14_14 : previousPadding literalP (7, 0) (7, 0) = (174515517 / 2500000000) := rfl
@[simp] theorem lookup_current_14_14 : currentPadding literalP (7, 0) (7, 0) = (116338777 / 5000000000) := rfl
@[simp] theorem lookup_descent_14_15 : literalDescent (7, 0) (7, 1) = (21332463 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_15 : previousPadding literalP (7, 0) (7, 1) = (2697569 / 625000000) := rfl
@[simp] theorem lookup_current_14_15 : currentPadding literalP (7, 0) (7, 1) = (8714367 / 5000000000) := rfl
@[simp] theorem lookup_descent_14_16 : literalDescent (7, 0) (8, 0) = (-69377969 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_16 : previousPadding literalP (7, 0) (8, 0) = (-21255117 / 2000000000) := rfl
@[simp] theorem lookup_current_14_16 : currentPadding literalP (7, 0) (8, 0) = (-952421 / 125000000) := rfl
@[simp] theorem lookup_descent_14_17 : literalDescent (7, 0) (8, 1) = (-23089536173 / 2000000000000) := rfl
@[simp] theorem lookup_previous_14_17 : previousPadding literalP (7, 0) (8, 1) = (-113447819 / 10000000000) := rfl
@[simp] theorem lookup_current_14_17 : currentPadding literalP (7, 0) (8, 1) = (-19724589 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_18 : literalDescent (7, 0) (9, 0) = (-107146667 / 10000000000) := rfl
@[simp] theorem lookup_previous_14_18 : previousPadding literalP (7, 0) (9, 0) = (-107146667 / 10000000000) := rfl
@[simp] theorem lookup_current_14_18 : currentPadding literalP (7, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_14_19 : literalDescent (7, 0) (9, 1) = (83940483 / 10000000000) := rfl
@[simp] theorem lookup_previous_14_19 : previousPadding literalP (7, 0) (9, 1) = (83940483 / 10000000000) := rfl
@[simp] theorem lookup_current_14_19 : currentPadding literalP (7, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_15_0 : literalDescent (7, 1) (0, 0) = (200012567 / 1000000000000) := rfl
@[simp] theorem lookup_previous_15_0 : previousPadding literalP (7, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_15_0 : currentPadding literalP (7, 1) (0, 0) = (12976049 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_1 : literalDescent (7, 1) (0, 1) = (348008459 / 2000000000000) := rfl
@[simp] theorem lookup_previous_15_1 : previousPadding literalP (7, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_15_1 : currentPadding literalP (7, 1) (0, 1) = (1929473 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_2 : literalDescent (7, 1) (1, 0) = (-720677 / 800000000) := rfl
@[simp] theorem lookup_previous_15_2 : previousPadding literalP (7, 1) (1, 0) = (-441629 / 200000000) := rfl
@[simp] theorem lookup_current_15_2 : currentPadding literalP (7, 1) (1, 0) = (-10675627 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_3 : literalDescent (7, 1) (1, 1) = (-66169397 / 500000000000) := rfl
@[simp] theorem lookup_previous_15_3 : previousPadding literalP (7, 1) (1, 1) = (-11699771 / 5000000000) := rfl
@[simp] theorem lookup_current_15_3 : currentPadding literalP (7, 1) (1, 1) = (-10265311 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_4 : literalDescent (7, 1) (2, 0) = (6125423 / 5000000000) := rfl
@[simp] theorem lookup_previous_15_4 : previousPadding literalP (7, 1) (2, 0) = (38212899 / 10000000000) := rfl
@[simp] theorem lookup_current_15_4 : currentPadding literalP (7, 1) (2, 0) = (25962053 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_5 : literalDescent (7, 1) (2, 1) = (354779 / 312500000) := rfl
@[simp] theorem lookup_previous_15_5 : previousPadding literalP (7, 1) (2, 1) = (45437147 / 10000000000) := rfl
@[simp] theorem lookup_current_15_5 : currentPadding literalP (7, 1) (2, 1) = (34084219 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_6 : literalDescent (7, 1) (3, 0) = (-49239659 / 10000000000) := rfl
@[simp] theorem lookup_previous_15_6 : previousPadding literalP (7, 1) (3, 0) = (-16748659 / 1000000000) := rfl
@[simp] theorem lookup_current_15_6 : currentPadding literalP (7, 1) (3, 0) = (-118246931 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_7 : literalDescent (7, 1) (3, 1) = (-6695353 / 5000000000) := rfl
@[simp] theorem lookup_previous_15_7 : previousPadding literalP (7, 1) (3, 1) = (-35391833 / 10000000000) := rfl
@[simp] theorem lookup_current_15_7 : currentPadding literalP (7, 1) (3, 1) = (-22001127 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_8 : literalDescent (7, 1) (4, 0) = (4515853 / 2000000000) := rfl
@[simp] theorem lookup_previous_15_8 : previousPadding literalP (7, 1) (4, 0) = (33652543 / 10000000000) := rfl
@[simp] theorem lookup_current_15_8 : currentPadding literalP (7, 1) (4, 0) = (5536639 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_9 : literalDescent (7, 1) (4, 1) = (3489649 / 10000000000) := rfl
@[simp] theorem lookup_previous_15_9 : previousPadding literalP (7, 1) (4, 1) = (1648333 / 1000000000) := rfl
@[simp] theorem lookup_current_15_9 : currentPadding literalP (7, 1) (4, 1) = (12993681 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_10 : literalDescent (7, 1) (5, 0) = (16292303 / 2000000000) := rfl
@[simp] theorem lookup_previous_15_10 : previousPadding literalP (7, 1) (5, 0) = (269483597 / 10000000000) := rfl
@[simp] theorem lookup_current_15_10 : currentPadding literalP (7, 1) (5, 0) = (94011041 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_11 : literalDescent (7, 1) (5, 1) = (-12269171 / 10000000000) := rfl
@[simp] theorem lookup_previous_15_11 : previousPadding literalP (7, 1) (5, 1) = (-9830827 / 2500000000) := rfl
@[simp] theorem lookup_current_15_11 : currentPadding literalP (7, 1) (5, 1) = (-27054137 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_12 : literalDescent (7, 1) (6, 0) = (-6405985717 / 1000000000000) := rfl
@[simp] theorem lookup_previous_15_12 : previousPadding literalP (7, 1) (6, 0) = (-177506937 / 10000000000) := rfl
@[simp] theorem lookup_current_15_12 : currentPadding literalP (7, 1) (6, 0) = (-113447819 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_13 : literalDescent (7, 1) (6, 1) = (-2913642159 / 2000000000000) := rfl
@[simp] theorem lookup_previous_15_13 : previousPadding literalP (7, 1) (6, 1) = (-61285967 / 10000000000) := rfl
@[simp] theorem lookup_current_15_13 : currentPadding literalP (7, 1) (6, 1) = (-23359003 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_14 : literalDescent (7, 1) (7, 0) = (21332463 / 20000000000) := rfl
@[simp] theorem lookup_previous_15_14 : previousPadding literalP (7, 1) (7, 0) = (2697569 / 625000000) := rfl
@[simp] theorem lookup_current_15_14 : currentPadding literalP (7, 1) (7, 0) = (8714367 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_15 : literalDescent (7, 1) (7, 1) = (1686428671 / 400000000000) := rfl
@[simp] theorem lookup_previous_15_15 : previousPadding literalP (7, 1) (7, 1) = (3322380087 / 250000000000) := rfl
@[simp] theorem lookup_current_15_15 : currentPadding literalP (7, 1) (7, 1) = (19989060459 / 2000000000000) := rfl
@[simp] theorem lookup_descent_15_16 : literalDescent (7, 1) (8, 0) = (-1640463 / 4000000000) := rfl
@[simp] theorem lookup_previous_15_16 : previousPadding literalP (7, 1) (8, 0) = (-14886319 / 10000000000) := rfl
@[simp] theorem lookup_current_15_16 : currentPadding literalP (7, 1) (8, 0) = (-15392241 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_17 : literalDescent (7, 1) (8, 1) = (-2603595067 / 2000000000000) := rfl
@[simp] theorem lookup_previous_15_17 : previousPadding literalP (7, 1) (8, 1) = (-23359003 / 5000000000) := rfl
@[simp] theorem lookup_current_15_17 : currentPadding literalP (7, 1) (8, 1) = (-34298951 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_18 : literalDescent (7, 1) (9, 0) = (-2548847 / 10000000000) := rfl
@[simp] theorem lookup_previous_15_18 : previousPadding literalP (7, 1) (9, 0) = (-2548847 / 10000000000) := rfl
@[simp] theorem lookup_current_15_18 : currentPadding literalP (7, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_15_19 : literalDescent (7, 1) (9, 1) = (-834777 / 2000000000) := rfl
@[simp] theorem lookup_previous_15_19 : previousPadding literalP (7, 1) (9, 1) = (-834777 / 2000000000) := rfl
@[simp] theorem lookup_current_15_19 : currentPadding literalP (7, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_16_0 : literalDescent (8, 0) (0, 0) = (769927 / 2500000000) := rfl
@[simp] theorem lookup_previous_16_0 : previousPadding literalP (8, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_16_0 : currentPadding literalP (8, 0) (0, 0) = (-1848249 / 1250000000) := rfl
@[simp] theorem lookup_descent_16_1 : literalDescent (8, 0) (0, 1) = (-15357991 / 20000000000) := rfl
@[simp] theorem lookup_previous_16_1 : previousPadding literalP (8, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_16_1 : currentPadding literalP (8, 0) (0, 1) = (-805441 / 2000000000) := rfl
@[simp] theorem lookup_descent_16_2 : literalDescent (8, 0) (1, 0) = (23512079 / 20000000000) := rfl
@[simp] theorem lookup_previous_16_2 : previousPadding literalP (8, 0) (1, 0) = (5405339 / 10000000000) := rfl
@[simp] theorem lookup_current_16_2 : currentPadding literalP (8, 0) (1, 0) = (16303 / 200000000) := rfl
@[simp] theorem lookup_descent_16_3 : literalDescent (8, 0) (1, 1) = (964965721 / 1000000000000) := rfl
@[simp] theorem lookup_previous_16_3 : previousPadding literalP (8, 0) (1, 1) = (4705859 / 10000000000) := rfl
@[simp] theorem lookup_current_16_3 : currentPadding literalP (8, 0) (1, 1) = (-3318791 / 5000000000) := rfl
@[simp] theorem lookup_descent_16_4 : literalDescent (8, 0) (2, 0) = (-17740091 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_4 : previousPadding literalP (8, 0) (2, 0) = (2626187 / 1250000000) := rfl
@[simp] theorem lookup_current_16_4 : currentPadding literalP (8, 0) (2, 0) = (38749587 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_5 : literalDescent (8, 0) (2, 1) = (3547419 / 5000000000) := rfl
@[simp] theorem lookup_previous_16_5 : previousPadding literalP (8, 0) (2, 1) = (5106869 / 5000000000) := rfl
@[simp] theorem lookup_current_16_5 : currentPadding literalP (8, 0) (2, 1) = (31189 / 100000000) := rfl
@[simp] theorem lookup_descent_16_6 : literalDescent (8, 0) (3, 0) = (-35522463 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_6 : previousPadding literalP (8, 0) (3, 0) = (-28849027 / 5000000000) := rfl
@[simp] theorem lookup_current_16_6 : currentPadding literalP (8, 0) (3, 0) = (-22175591 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_7 : literalDescent (8, 0) (3, 1) = (-301837 / 1250000000) := rfl
@[simp] theorem lookup_previous_16_7 : previousPadding literalP (8, 0) (3, 1) = (-19829153 / 10000000000) := rfl
@[simp] theorem lookup_current_16_7 : currentPadding literalP (8, 0) (3, 1) = (-17414457 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_8 : literalDescent (8, 0) (4, 0) = (3991059 / 5000000000) := rfl
@[simp] theorem lookup_previous_16_8 : previousPadding literalP (8, 0) (4, 0) = (30704333 / 10000000000) := rfl
@[simp] theorem lookup_current_16_8 : currentPadding literalP (8, 0) (4, 0) = (4544443 / 2000000000) := rfl
@[simp] theorem lookup_descent_16_9 : literalDescent (8, 0) (4, 1) = (-252843 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_9 : previousPadding literalP (8, 0) (4, 1) = (3446567 / 2500000000) := rfl
@[simp] theorem lookup_current_16_9 : currentPadding literalP (8, 0) (4, 1) = (14039111 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_10 : literalDescent (8, 0) (5, 0) = (11384479 / 2000000000) := rfl
@[simp] theorem lookup_previous_16_10 : previousPadding literalP (8, 0) (5, 0) = (95605639 / 10000000000) := rfl
@[simp] theorem lookup_current_16_10 : currentPadding literalP (8, 0) (5, 0) = (9670811 / 2500000000) := rfl
@[simp] theorem lookup_descent_16_11 : literalDescent (8, 0) (5, 1) = (311810599 / 400000000000) := rfl
@[simp] theorem lookup_previous_16_11 : previousPadding literalP (8, 0) (5, 1) = (1801208839 / 400000000000) := rfl
@[simp] theorem lookup_current_16_11 : currentPadding literalP (8, 0) (5, 1) = (9308739 / 2500000000) := rfl
@[simp] theorem lookup_descent_16_12 : literalDescent (8, 0) (6, 0) = (-304707 / 80000000) := rfl
@[simp] theorem lookup_previous_16_12 : previousPadding literalP (8, 0) (6, 0) = (-72617521 / 5000000000) := rfl
@[simp] theorem lookup_current_16_12 : currentPadding literalP (8, 0) (6, 0) = (-107146667 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_13 : literalDescent (8, 0) (6, 1) = (-3788077 / 1000000000) := rfl
@[simp] theorem lookup_previous_16_13 : previousPadding literalP (8, 0) (6, 1) = (-40429617 / 10000000000) := rfl
@[simp] theorem lookup_current_16_13 : currentPadding literalP (8, 0) (6, 1) = (-2548847 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_14 : literalDescent (8, 0) (7, 0) = (-69377969 / 20000000000) := rfl
@[simp] theorem lookup_previous_16_14 : previousPadding literalP (8, 0) (7, 0) = (-21255117 / 2000000000) := rfl
@[simp] theorem lookup_current_16_14 : currentPadding literalP (8, 0) (7, 0) = (-952421 / 125000000) := rfl
@[simp] theorem lookup_descent_16_15 : literalDescent (8, 0) (7, 1) = (-1640463 / 4000000000) := rfl
@[simp] theorem lookup_previous_16_15 : previousPadding literalP (8, 0) (7, 1) = (-14886319 / 10000000000) := rfl
@[simp] theorem lookup_current_16_15 : currentPadding literalP (8, 0) (7, 1) = (-15392241 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_16 : literalDescent (8, 0) (8, 0) = (65820423 / 5000000000) := rfl
@[simp] theorem lookup_previous_16_16 : previousPadding literalP (8, 0) (8, 0) = (116338777 / 5000000000) := rfl
@[simp] theorem lookup_current_16_16 : currentPadding literalP (8, 0) (8, 0) = (59665867 / 5000000000) := rfl
@[simp] theorem lookup_descent_16_17 : literalDescent (8, 0) (8, 1) = (6087867 / 1250000000) := rfl
@[simp] theorem lookup_previous_16_17 : previousPadding literalP (8, 0) (8, 1) = (8714367 / 5000000000) := rfl
@[simp] theorem lookup_current_16_17 : currentPadding literalP (8, 0) (8, 1) = (-1674527 / 2000000000) := rfl
@[simp] theorem lookup_descent_16_18 : literalDescent (8, 0) (9, 0) = (-85341193 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_18 : previousPadding literalP (8, 0) (9, 0) = (-952421 / 125000000) := rfl
@[simp] theorem lookup_current_16_18 : currentPadding literalP (8, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_16_19 : literalDescent (8, 0) (9, 1) = (-4182846837 / 2000000000000) := rfl
@[simp] theorem lookup_previous_16_19 : previousPadding literalP (8, 0) (9, 1) = (-19724589 / 10000000000) := rfl
@[simp] theorem lookup_current_16_19 : currentPadding literalP (8, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_17_0 : literalDescent (8, 1) (0, 0) = (-717316127 / 2000000000000) := rfl
@[simp] theorem lookup_previous_17_0 : previousPadding literalP (8, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_17_0 : currentPadding literalP (8, 1) (0, 0) = (2195589 / 5000000000) := rfl
@[simp] theorem lookup_descent_17_1 : literalDescent (8, 1) (0, 1) = (-529102333 / 2000000000000) := rfl
@[simp] theorem lookup_previous_17_1 : previousPadding literalP (8, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_17_1 : currentPadding literalP (8, 1) (0, 1) = (-441899 / 250000000) := rfl
@[simp] theorem lookup_descent_17_2 : literalDescent (8, 1) (1, 0) = (30813587 / 20000000000) := rfl
@[simp] theorem lookup_previous_17_2 : previousPadding literalP (8, 1) (1, 0) = (12976049 / 5000000000) := rfl
@[simp] theorem lookup_current_17_2 : currentPadding literalP (8, 1) (1, 0) = (17296 / 9765625) := rfl
@[simp] theorem lookup_descent_17_3 : literalDescent (8, 1) (1, 1) = (39448533 / 50000000000) := rfl
@[simp] theorem lookup_previous_17_3 : previousPadding literalP (8, 1) (1, 1) = (1929473 / 10000000000) := rfl
@[simp] theorem lookup_current_17_3 : currentPadding literalP (8, 1) (1, 1) = (961193 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_4 : literalDescent (8, 1) (2, 0) = (-4586827 / 2000000000) := rfl
@[simp] theorem lookup_previous_17_4 : previousPadding literalP (8, 1) (2, 0) = (-10675627 / 5000000000) := rfl
@[simp] theorem lookup_current_17_4 : currentPadding literalP (8, 1) (2, 0) = (1582881 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_5 : literalDescent (8, 1) (2, 1) = (-1892563 / 5000000000) := rfl
@[simp] theorem lookup_previous_17_5 : previousPadding literalP (8, 1) (2, 1) = (-10265311 / 10000000000) := rfl
@[simp] theorem lookup_current_17_5 : currentPadding literalP (8, 1) (2, 1) = (-1296037 / 2000000000) := rfl
@[simp] theorem lookup_descent_17_6 : literalDescent (8, 1) (3, 0) = (113213 / 312500000) := rfl
@[simp] theorem lookup_previous_17_6 : previousPadding literalP (8, 1) (3, 0) = (25962053 / 10000000000) := rfl
@[simp] theorem lookup_current_17_6 : currentPadding literalP (8, 1) (3, 0) = (22339237 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_7 : literalDescent (8, 1) (3, 1) = (4378961 / 2500000000) := rfl
@[simp] theorem lookup_previous_17_7 : previousPadding literalP (8, 1) (3, 1) = (34084219 / 10000000000) := rfl
@[simp] theorem lookup_current_17_7 : currentPadding literalP (8, 1) (3, 1) = (132547 / 80000000) := rfl
@[simp] theorem lookup_descent_17_8 : literalDescent (8, 1) (4, 0) = (-7617889 / 1250000000) := rfl
@[simp] theorem lookup_previous_17_8 : previousPadding literalP (8, 1) (4, 0) = (-118246931 / 10000000000) := rfl
@[simp] theorem lookup_current_17_8 : currentPadding literalP (8, 1) (4, 0) = (-57303819 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_9 : literalDescent (8, 1) (4, 1) = (-67201 / 31250000) := rfl
@[simp] theorem lookup_previous_17_9 : previousPadding literalP (8, 1) (4, 1) = (-22001127 / 10000000000) := rfl
@[simp] theorem lookup_current_17_9 : currentPadding literalP (8, 1) (4, 1) = (-496807 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_10 : literalDescent (8, 1) (5, 0) = (27818559 / 5000000000) := rfl
@[simp] theorem lookup_previous_17_10 : previousPadding literalP (8, 1) (5, 0) = (5536639 / 5000000000) := rfl
@[simp] theorem lookup_current_17_10 : currentPadding literalP (8, 1) (5, 0) = (-69631 / 15625000) := rfl
@[simp] theorem lookup_descent_17_11 : literalDescent (8, 1) (5, 1) = (702827 / 2000000000) := rfl
@[simp] theorem lookup_previous_17_11 : previousPadding literalP (8, 1) (5, 1) = (12993681 / 10000000000) := rfl
@[simp] theorem lookup_current_17_11 : currentPadding literalP (8, 1) (5, 1) = (4739773 / 5000000000) := rfl
@[simp] theorem lookup_descent_17_12 : literalDescent (8, 1) (6, 0) = (104081599 / 10000000000) := rfl
@[simp] theorem lookup_previous_17_12 : previousPadding literalP (8, 1) (6, 0) = (94011041 / 5000000000) := rfl
@[simp] theorem lookup_current_17_12 : currentPadding literalP (8, 1) (6, 0) = (83940483 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_13 : literalDescent (8, 1) (6, 1) = (-5720063 / 2500000000) := rfl
@[simp] theorem lookup_previous_17_13 : previousPadding literalP (8, 1) (6, 1) = (-27054137 / 10000000000) := rfl
@[simp] theorem lookup_current_17_13 : currentPadding literalP (8, 1) (6, 1) = (-834777 / 2000000000) := rfl
@[simp] theorem lookup_descent_17_14 : literalDescent (8, 1) (7, 0) = (-23089536173 / 2000000000000) := rfl
@[simp] theorem lookup_previous_17_14 : previousPadding literalP (8, 1) (7, 0) = (-113447819 / 10000000000) := rfl
@[simp] theorem lookup_current_17_14 : currentPadding literalP (8, 1) (7, 0) = (-19724589 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_15 : literalDescent (8, 1) (7, 1) = (-2603595067 / 2000000000000) := rfl
@[simp] theorem lookup_previous_17_15 : previousPadding literalP (8, 1) (7, 1) = (-23359003 / 5000000000) := rfl
@[simp] theorem lookup_current_17_15 : currentPadding literalP (8, 1) (7, 1) = (-34298951 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_16 : literalDescent (8, 1) (8, 0) = (6087867 / 1250000000) := rfl
@[simp] theorem lookup_previous_17_16 : previousPadding literalP (8, 1) (8, 0) = (8714367 / 5000000000) := rfl
@[simp] theorem lookup_current_17_16 : currentPadding literalP (8, 1) (8, 0) = (-1674527 / 2000000000) := rfl
@[simp] theorem lookup_descent_17_17 : literalDescent (8, 1) (8, 1) = (7040162709 / 1000000000000) := rfl
@[simp] theorem lookup_previous_17_17 : previousPadding literalP (8, 1) (8, 1) = (19989060459 / 2000000000000) := rfl
@[simp] theorem lookup_current_17_17 : currentPadding literalP (8, 1) (8, 1) = (318579063 / 80000000000) := rfl
@[simp] theorem lookup_descent_17_18 : literalDescent (8, 1) (9, 0) = (-12269877 / 5000000000) := rfl
@[simp] theorem lookup_previous_17_18 : previousPadding literalP (8, 1) (9, 0) = (-15392241 / 10000000000) := rfl
@[simp] theorem lookup_current_17_18 : currentPadding literalP (8, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_17_19 : literalDescent (8, 1) (9, 1) = (-3548812769 / 1000000000000) := rfl
@[simp] theorem lookup_previous_17_19 : previousPadding literalP (8, 1) (9, 1) = (-34298951 / 10000000000) := rfl
@[simp] theorem lookup_current_17_19 : currentPadding literalP (8, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_0 : literalDescent (9, 0) (0, 0) = (9147513 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_0 : previousPadding literalP (9, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_18_0 : currentPadding literalP (9, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_1 : literalDescent (9, 0) (0, 1) = (9147513 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_1 : previousPadding literalP (9, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_18_1 : currentPadding literalP (9, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_2 : literalDescent (9, 0) (1, 0) = (-1848249 / 1250000000) := rfl
@[simp] theorem lookup_previous_18_2 : previousPadding literalP (9, 0) (1, 0) = (-1848249 / 1250000000) := rfl
@[simp] theorem lookup_current_18_2 : currentPadding literalP (9, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_3 : literalDescent (9, 0) (1, 1) = (-6587359 / 5000000000) := rfl
@[simp] theorem lookup_previous_18_3 : previousPadding literalP (9, 0) (1, 1) = (-805441 / 2000000000) := rfl
@[simp] theorem lookup_current_18_3 : currentPadding literalP (9, 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_4 : literalDescent (9, 0) (2, 0) = (16303 / 200000000) := rfl
@[simp] theorem lookup_previous_18_4 : previousPadding literalP (9, 0) (2, 0) = (16303 / 200000000) := rfl
@[simp] theorem lookup_current_18_4 : currentPadding literalP (9, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_5 : literalDescent (9, 0) (2, 1) = (-3318791 / 5000000000) := rfl
@[simp] theorem lookup_previous_18_5 : previousPadding literalP (9, 0) (2, 1) = (-3318791 / 5000000000) := rfl
@[simp] theorem lookup_current_18_5 : currentPadding literalP (9, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_6 : literalDescent (9, 0) (3, 0) = (38749587 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_6 : previousPadding literalP (9, 0) (3, 0) = (38749587 / 10000000000) := rfl
@[simp] theorem lookup_current_18_6 : currentPadding literalP (9, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_7 : literalDescent (9, 0) (3, 1) = (31189 / 100000000) := rfl
@[simp] theorem lookup_previous_18_7 : previousPadding literalP (9, 0) (3, 1) = (31189 / 100000000) := rfl
@[simp] theorem lookup_current_18_7 : currentPadding literalP (9, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_8 : literalDescent (9, 0) (4, 0) = (-22175591 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_8 : previousPadding literalP (9, 0) (4, 0) = (-22175591 / 10000000000) := rfl
@[simp] theorem lookup_current_18_8 : currentPadding literalP (9, 0) (4, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_9 : literalDescent (9, 0) (4, 1) = (-17414457 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_9 : previousPadding literalP (9, 0) (4, 1) = (-17414457 / 10000000000) := rfl
@[simp] theorem lookup_current_18_9 : currentPadding literalP (9, 0) (4, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_10 : literalDescent (9, 0) (5, 0) = (4544443 / 2000000000) := rfl
@[simp] theorem lookup_previous_18_10 : previousPadding literalP (9, 0) (5, 0) = (4544443 / 2000000000) := rfl
@[simp] theorem lookup_current_18_10 : currentPadding literalP (9, 0) (5, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_11 : literalDescent (9, 0) (5, 1) = (14039111 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_11 : previousPadding literalP (9, 0) (5, 1) = (14039111 / 10000000000) := rfl
@[simp] theorem lookup_current_18_11 : currentPadding literalP (9, 0) (5, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_12 : literalDescent (9, 0) (6, 0) = (9670811 / 2500000000) := rfl
@[simp] theorem lookup_previous_18_12 : previousPadding literalP (9, 0) (6, 0) = (9670811 / 2500000000) := rfl
@[simp] theorem lookup_current_18_12 : currentPadding literalP (9, 0) (6, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_13 : literalDescent (9, 0) (6, 1) = (9308739 / 2500000000) := rfl
@[simp] theorem lookup_previous_18_13 : previousPadding literalP (9, 0) (6, 1) = (9308739 / 2500000000) := rfl
@[simp] theorem lookup_current_18_13 : currentPadding literalP (9, 0) (6, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_14 : literalDescent (9, 0) (7, 0) = (-107146667 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_14 : previousPadding literalP (9, 0) (7, 0) = (-107146667 / 10000000000) := rfl
@[simp] theorem lookup_current_18_14 : currentPadding literalP (9, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_15 : literalDescent (9, 0) (7, 1) = (-2548847 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_15 : previousPadding literalP (9, 0) (7, 1) = (-2548847 / 10000000000) := rfl
@[simp] theorem lookup_current_18_15 : currentPadding literalP (9, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_16 : literalDescent (9, 0) (8, 0) = (-85341193 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_16 : previousPadding literalP (9, 0) (8, 0) = (-952421 / 125000000) := rfl
@[simp] theorem lookup_current_18_16 : currentPadding literalP (9, 0) (8, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_17 : literalDescent (9, 0) (8, 1) = (-12269877 / 5000000000) := rfl
@[simp] theorem lookup_previous_18_17 : previousPadding literalP (9, 0) (8, 1) = (-15392241 / 10000000000) := rfl
@[simp] theorem lookup_current_18_17 : currentPadding literalP (9, 0) (8, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_18 : literalDescent (9, 0) (9, 0) = (59665867 / 5000000000) := rfl
@[simp] theorem lookup_previous_18_18 : previousPadding literalP (9, 0) (9, 0) = (59665867 / 5000000000) := rfl
@[simp] theorem lookup_current_18_18 : currentPadding literalP (9, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_19 : literalDescent (9, 0) (9, 1) = (387439 / 5000000000) := rfl
@[simp] theorem lookup_previous_18_19 : previousPadding literalP (9, 0) (9, 1) = (-1674527 / 2000000000) := rfl
@[simp] theorem lookup_current_18_19 : currentPadding literalP (9, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_0 : literalDescent (9, 1) (0, 0) = (-158403463 / 2000000000000) := rfl
@[simp] theorem lookup_previous_19_0 : previousPadding literalP (9, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_19_0 : currentPadding literalP (9, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_1 : literalDescent (9, 1) (0, 1) = (-79248581 / 1000000000000) := rfl
@[simp] theorem lookup_previous_19_1 : previousPadding literalP (9, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_19_1 : currentPadding literalP (9, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_2 : literalDescent (9, 1) (1, 0) = (-1109869 / 4000000000) := rfl
@[simp] theorem lookup_previous_19_2 : previousPadding literalP (9, 1) (1, 0) = (2195589 / 5000000000) := rfl
@[simp] theorem lookup_current_19_2 : currentPadding literalP (9, 1) (1, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_3 : literalDescent (9, 1) (1, 1) = (-696666751 / 2000000000000) := rfl
@[simp] theorem lookup_previous_19_3 : previousPadding literalP (9, 1) (1, 1) = (-441899 / 250000000) := rfl
@[simp] theorem lookup_current_19_3 : currentPadding literalP (9, 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_4 : literalDescent (9, 1) (2, 0) = (17296 / 9765625) := rfl
@[simp] theorem lookup_previous_19_4 : previousPadding literalP (9, 1) (2, 0) = (17296 / 9765625) := rfl
@[simp] theorem lookup_current_19_4 : currentPadding literalP (9, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_5 : literalDescent (9, 1) (2, 1) = (961193 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_5 : previousPadding literalP (9, 1) (2, 1) = (961193 / 10000000000) := rfl
@[simp] theorem lookup_current_19_5 : currentPadding literalP (9, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_6 : literalDescent (9, 1) (3, 0) = (1582881 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_6 : previousPadding literalP (9, 1) (3, 0) = (1582881 / 10000000000) := rfl
@[simp] theorem lookup_current_19_6 : currentPadding literalP (9, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_7 : literalDescent (9, 1) (3, 1) = (-1296037 / 2000000000) := rfl
@[simp] theorem lookup_previous_19_7 : previousPadding literalP (9, 1) (3, 1) = (-1296037 / 2000000000) := rfl
@[simp] theorem lookup_current_19_7 : currentPadding literalP (9, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_8 : literalDescent (9, 1) (4, 0) = (22339237 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_8 : previousPadding literalP (9, 1) (4, 0) = (22339237 / 10000000000) := rfl
@[simp] theorem lookup_current_19_8 : currentPadding literalP (9, 1) (4, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_9 : literalDescent (9, 1) (4, 1) = (132547 / 80000000) := rfl
@[simp] theorem lookup_previous_19_9 : previousPadding literalP (9, 1) (4, 1) = (132547 / 80000000) := rfl
@[simp] theorem lookup_current_19_9 : currentPadding literalP (9, 1) (4, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_10 : literalDescent (9, 1) (5, 0) = (-57303819 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_10 : previousPadding literalP (9, 1) (5, 0) = (-57303819 / 10000000000) := rfl
@[simp] theorem lookup_current_19_10 : currentPadding literalP (9, 1) (5, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_11 : literalDescent (9, 1) (5, 1) = (-496807 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_11 : previousPadding literalP (9, 1) (5, 1) = (-496807 / 10000000000) := rfl
@[simp] theorem lookup_current_19_11 : currentPadding literalP (9, 1) (5, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_12 : literalDescent (9, 1) (6, 0) = (-69631 / 15625000) := rfl
@[simp] theorem lookup_previous_19_12 : previousPadding literalP (9, 1) (6, 0) = (-69631 / 15625000) := rfl
@[simp] theorem lookup_current_19_12 : currentPadding literalP (9, 1) (6, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_13 : literalDescent (9, 1) (6, 1) = (4739773 / 5000000000) := rfl
@[simp] theorem lookup_previous_19_13 : previousPadding literalP (9, 1) (6, 1) = (4739773 / 5000000000) := rfl
@[simp] theorem lookup_current_19_13 : currentPadding literalP (9, 1) (6, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_14 : literalDescent (9, 1) (7, 0) = (83940483 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_14 : previousPadding literalP (9, 1) (7, 0) = (83940483 / 10000000000) := rfl
@[simp] theorem lookup_current_19_14 : currentPadding literalP (9, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_15 : literalDescent (9, 1) (7, 1) = (-834777 / 2000000000) := rfl
@[simp] theorem lookup_previous_19_15 : previousPadding literalP (9, 1) (7, 1) = (-834777 / 2000000000) := rfl
@[simp] theorem lookup_current_19_15 : currentPadding literalP (9, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_16 : literalDescent (9, 1) (8, 0) = (-4182846837 / 2000000000000) := rfl
@[simp] theorem lookup_previous_19_16 : previousPadding literalP (9, 1) (8, 0) = (-19724589 / 10000000000) := rfl
@[simp] theorem lookup_current_19_16 : currentPadding literalP (9, 1) (8, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_17 : literalDescent (9, 1) (8, 1) = (-3548812769 / 1000000000000) := rfl
@[simp] theorem lookup_previous_19_17 : previousPadding literalP (9, 1) (8, 1) = (-34298951 / 10000000000) := rfl
@[simp] theorem lookup_current_19_17 : currentPadding literalP (9, 1) (8, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_18 : literalDescent (9, 1) (9, 0) = (387439 / 5000000000) := rfl
@[simp] theorem lookup_previous_19_18 : previousPadding literalP (9, 1) (9, 0) = (-1674527 / 2000000000) := rfl
@[simp] theorem lookup_current_19_18 : currentPadding literalP (9, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_19 : literalDescent (9, 1) (9, 1) = (4781142051 / 2000000000000) := rfl
@[simp] theorem lookup_previous_19_19 : previousPadding literalP (9, 1) (9, 1) = (318579063 / 80000000000) := rfl
@[simp] theorem lookup_current_19_19 : currentPadding literalP (9, 1) (9, 1) = 0 := rfl

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Lower.MatrixBridge
