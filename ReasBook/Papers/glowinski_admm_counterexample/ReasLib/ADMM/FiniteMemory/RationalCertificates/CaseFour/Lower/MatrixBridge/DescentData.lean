/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseFour.Lower.MatrixBridge.Lookups
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixDescent

@[expose] public section
set_option maxRecDepth 4096
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Lower.MatrixBridge
open MatrixAssembly

-- These candidates become certificates only through the subsequent Lean proofs.
def literalDescentData : List (List ℚ) := [
  [(13469777 / 5000000000), (12911629 / 20000000000), (-26687847 / 5000000000), (-342335539 / 250000000000), (-50543 / 5000000000), (244904621 / 250000000000), (54866773 / 10000000000), (-43226931 / 125000000000), (-33976901 / 20000000000), (-563461407 / 500000000000), (-127963 / 10000000000), (147305437 / 100000000000), (-14550959 / 10000000000), (2284113 / 500000000000), (-17375753 / 20000000000), (16059651 / 62500000000), (2588017 / 10000000000), (-106656919 / 250000000000), (1887537 / 2000000000), (-22767213 / 250000000000)],
  [(12911629 / 20000000000), (36606237 / 50000000000), (-110565459 / 50000000000), (-34035153 / 50000000000), (-841347 / 2000000000), (-164322437 / 500000000000), (368954193 / 100000000000), (648763 / 6250000000), (-3322053 / 4000000000), (-323074399 / 500000000000), (-1665311 / 20000000000), (177831779 / 250000000000), (88741 / 20000000000), (63804443 / 250000000000), (-22036387 / 20000000000), (54418421 / 250000000000), (-6357481 / 10000000000), (-1709403 / 6250000000), (1887537 / 2000000000), (-4557209 / 50000000000)],
  [(-26687847 / 5000000000), (-110565459 / 50000000000), (15036977 / 1000000000), (1916689001 / 500000000000), (-48762259 / 10000000000), (-1210276171 / 500000000000), (-292972459 / 20000000000), (159545357 / 100000000000), (17758527 / 2000000000), (43019893 / 20000000000), (-828373 / 4000000000), (-82800703 / 20000000000), (291703 / 125000000), (20595489 / 20000000000), (-532371 / 500000000), (-1523567 / 1250000000), (13330203 / 10000000000), (17576467 / 10000000000), (-14486313 / 10000000000), (-3764971 / 10000000000)],
  [(-342335539 / 250000000000), (-34035153 / 50000000000), (1916689001 / 500000000000), (834716701 / 500000000000), (-1051878983 / 500000000000), (-178158359 / 250000000000), (-2342224527 / 500000000000), (-107988129 / 500000000000), (450105987 / 100000000000), (83743121 / 125000000000), (65638183 / 500000000000), (-704582059 / 500000000000), (20583071 / 125000000000), (113640481 / 500000000000), (-28694703 / 500000000000), (-35657159 / 250000000000), (67650311 / 62500000000), (239256637 / 250000000000), (-3744613 / 2500000000), (-90645093 / 250000000000)],
  [(-50543 / 5000000000), (-841347 / 2000000000), (-48762259 / 10000000000), (-1051878983 / 500000000000), (40444429 / 2500000000), (2041561599 / 500000000000), (-7679379 / 1250000000), (-702782463 / 250000000000), (-136222327 / 10000000000), (2018929 / 781250000), (8658339 / 1250000000), (3714111 / 2000000000), (-22755319 / 10000000000), (-20134553 / 5000000000), (29547999 / 5000000000), (14810711 / 10000000000), (-14959 / 8000000), (-23416419 / 10000000000), (-2165653 / 10000000000), (16986349 / 10000000000)],
  [(244904621 / 250000000000), (-164322437 / 500000000000), (-1210276171 / 500000000000), (-178158359 / 250000000000), (2041561599 / 500000000000), (241705199 / 100000000000), (-11580541 / 5000000000), (-58363269 / 50000000000), (-8177543 / 2000000000), (-1310123 / 5000000000), (113413939 / 25000000000), (3220477 / 5000000000), (-13912491 / 10000000000), (-13924049 / 10000000000), (10438369 / 10000000000), (5243573 / 5000000000), (1230083 / 5000000000), (-2198967 / 5000000000), (-1681179 / 2500000000), (964523 / 5000000000)],
  [(54866773 / 10000000000), (368954193 / 100000000000), (-292972459 / 20000000000), (-2342224527 / 500000000000), (-7679379 / 1250000000), (-11580541 / 5000000000), (36818217 / 1000000000), (2093391891 / 500000000000), (-242858427 / 20000000000), (-3019286743 / 500000000000), (-178658711 / 10000000000), (765337191 / 125000000000), (13100263 / 1250000000), (6434287 / 2000000000), (-28273383 / 10000000000), (-10666967 / 2500000000), (-7402427 / 2000000000), (-585841 / 10000000000), (45443657 / 10000000000), (1483349 / 10000000000)],
  [(-43226931 / 125000000000), (648763 / 6250000000), (159545357 / 100000000000), (-107988129 / 500000000000), (-702782463 / 250000000000), (-58363269 / 50000000000), (2093391891 / 500000000000), (133748533 / 50000000000), (-1926601 / 800000000), (-604039451 / 500000000000), (-22203633 / 5000000000), (-1457131 / 2500000000), (3199557549 / 500000000000), (4624379 / 5000000000), (-3718079 / 2000000000), (-7042983 / 5000000000), (-3848379 / 5000000000), (13314091 / 10000000000), (226643 / 500000000), (-4522881 / 10000000000)],
  [(-33976901 / 20000000000), (-3322053 / 4000000000), (17758527 / 2000000000), (450105987 / 100000000000), (-136222327 / 10000000000), (-8177543 / 2000000000), (-242858427 / 20000000000), (-1926601 / 800000000), (3019013 / 78125000), (108593857 / 20000000000), (-57884603 / 5000000000), (-342907911 / 50000000000), (-26912739 / 1250000000), (10269589 / 2000000000), (138546279 / 10000000000), (10219941 / 5000000000), (382343 / 156250000), (-46621447 / 10000000000), (-32531421 / 10000000000), (3476607 / 2000000000)],
  [(-563461407 / 500000000000), (-323074399 / 500000000000), (43019893 / 20000000000), (83743121 / 125000000000), (2018929 / 781250000), (-1310123 / 5000000000), (-3019286743 / 500000000000), (-604039451 / 500000000000), (108593857 / 20000000000), (1004168187 / 250000000000), (-36399933 / 10000000000), (-207002127 / 125000000000), (-3520769 / 500000000), (-5853459 / 5000000000), (235636977 / 25000000000), (6819061 / 10000000000), (151969 / 200000000), (-1108671 / 625000000), (-25032131 / 10000000000), (13483109 / 10000000000)],
  [(-127963 / 10000000000), (-1665311 / 20000000000), (-828373 / 4000000000), (65638183 / 500000000000), (8658339 / 1250000000), (113413939 / 25000000000), (-178658711 / 10000000000), (-22203633 / 5000000000), (-57884603 / 5000000000), (-36399933 / 10000000000), (442781683 / 10000000000), (68115403 / 20000000000), (-63730673 / 20000000000), (-3011174513 / 500000000000), (-16696171 / 625000000), (13341241 / 2000000000), (1698869 / 400000000), (7809941 / 2000000000), (8222153 / 2000000000), (-22314303 / 5000000000)],
  [(147305437 / 100000000000), (177831779 / 250000000000), (-82800703 / 20000000000), (-704582059 / 500000000000), (3714111 / 2000000000), (3220477 / 5000000000), (765337191 / 125000000000), (-1457131 / 2500000000), (-342907911 / 50000000000), (-207002127 / 125000000000), (68115403 / 20000000000), (200426427 / 50000000000), (8256277 / 20000000000), (-323682311 / 500000000000), (-278759 / 50000000), (-2709389 / 2500000000), (176000643 / 250000000000), (52269 / 250000000), (12989897 / 5000000000), (-1938733 / 10000000000)],
  [(-14550959 / 10000000000), (88741 / 20000000000), (291703 / 125000000), (20583071 / 125000000000), (-22755319 / 10000000000), (-13912491 / 10000000000), (13100263 / 1250000000), (3199557549 / 500000000000), (-26912739 / 1250000000), (-3520769 / 500000000), (-63730673 / 20000000000), (8256277 / 20000000000), (197600067 / 5000000000), (2956197 / 1250000000), (-469649151 / 20000000000), (-3395153833 / 500000000000), (-1161861 / 312500000), (100407769 / 10000000000), (4142397 / 1250000000), (-41636703 / 10000000000)],
  [(2284113 / 500000000000), (63804443 / 250000000000), (20595489 / 20000000000), (113640481 / 500000000000), (-20134553 / 5000000000), (-13924049 / 10000000000), (6434287 / 2000000000), (4624379 / 5000000000), (10269589 / 2000000000), (-5853459 / 5000000000), (-3011174513 / 500000000000), (-323682311 / 500000000000), (2956197 / 1250000000), (2253703011 / 500000000000), (-47594519 / 20000000000), (-825432717 / 500000000000), (-33161627 / 10000000000), (-850351 / 500000000), (399391 / 100000000), (3236241 / 5000000000)],
  [(-17375753 / 20000000000), (-22036387 / 20000000000), (-532371 / 500000000), (-28694703 / 500000000000), (29547999 / 5000000000), (10438369 / 10000000000), (-28273383 / 10000000000), (-3718079 / 2000000000), (138546279 / 10000000000), (235636977 / 25000000000), (-16696171 / 625000000), (-278759 / 50000000), (-469649151 / 20000000000), (-47594519 / 20000000000), (10279221 / 200000000), (65904011 / 20000000000), (-14129983 / 5000000000), (-2512562881 / 250000000000), (-13377137 / 1000000000), (18147223 / 2500000000)],
  [(16059651 / 62500000000), (54418421 / 250000000000), (-1523567 / 1250000000), (-35657159 / 250000000000), (14810711 / 10000000000), (5243573 / 5000000000), (-10666967 / 2500000000), (-7042983 / 5000000000), (10219941 / 5000000000), (6819061 / 10000000000), (13341241 / 2000000000), (-2709389 / 2500000000), (-3395153833 / 500000000000), (-825432717 / 500000000000), (65904011 / 20000000000), (1936005153 / 500000000000), (-2236163 / 5000000000), (-78105651 / 50000000000), (-10246541 / 10000000000), (138273 / 5000000000)],
  [(2588017 / 10000000000), (-6357481 / 10000000000), (13330203 / 10000000000), (67650311 / 62500000000), (-14959 / 8000000), (1230083 / 5000000000), (-7402427 / 2000000000), (-3848379 / 5000000000), (382343 / 156250000), (151969 / 200000000), (1698869 / 400000000), (176000643 / 250000000000), (-1161861 / 312500000), (-33161627 / 10000000000), (-14129983 / 5000000000), (-2236163 / 5000000000), (24721789 / 2500000000), (5243501 / 1250000000), (-1211933 / 200000000), (-454562687 / 250000000000)],
  [(-106656919 / 250000000000), (-1709403 / 6250000000), (17576467 / 10000000000), (239256637 / 250000000000), (-23416419 / 10000000000), (-2198967 / 5000000000), (-585841 / 10000000000), (13314091 / 10000000000), (-46621447 / 10000000000), (-1108671 / 625000000), (7809941 / 2000000000), (52269 / 250000000), (100407769 / 10000000000), (-850351 / 500000000), (-2512562881 / 250000000000), (-78105651 / 50000000000), (5243501 / 1250000000), (771121909 / 125000000000), (-471789 / 200000000), (-145825021 / 50000000000)],
  [(1887537 / 2000000000), (1887537 / 2000000000), (-14486313 / 10000000000), (-3744613 / 2500000000), (-2165653 / 10000000000), (-1681179 / 2500000000), (45443657 / 10000000000), (226643 / 500000000), (-32531421 / 10000000000), (-25032131 / 10000000000), (8222153 / 2000000000), (12989897 / 5000000000), (4142397 / 1250000000), (399391 / 100000000), (-13377137 / 1000000000), (-10246541 / 10000000000), (-1211933 / 200000000), (-471789 / 200000000), (28605031 / 2500000000), (681851 / 10000000000)],
  [(-22767213 / 250000000000), (-4557209 / 50000000000), (-3764971 / 10000000000), (-90645093 / 250000000000), (16986349 / 10000000000), (964523 / 5000000000), (1483349 / 10000000000), (-4522881 / 10000000000), (3476607 / 2000000000), (13483109 / 10000000000), (-22314303 / 5000000000), (-1938733 / 10000000000), (-41636703 / 10000000000), (3236241 / 5000000000), (18147223 / 2500000000), (138273 / 5000000000), (-454562687 / 250000000000), (-145825021 / 50000000000), (681851 / 10000000000), (225033509 / 125000000000)]
]
def literalDescent : Matrix (Fin 10 × Fin 2) (Fin 10 × Fin 2) ℚ := readFlat literalDescentData
@[simp] theorem lookup_descent_0_0 : literalDescent (0, 0) (0, 0) = (13469777 / 5000000000) := rfl
@[simp] theorem lookup_previous_0_0 : previousPadding literalP (0, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_0_0 : currentPadding literalP (0, 0) (0, 0) = (1304136281 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_1 : literalDescent (0, 0) (0, 1) = (12911629 / 20000000000) := rfl
@[simp] theorem lookup_previous_0_1 : previousPadding literalP (0, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_0_1 : currentPadding literalP (0, 0) (0, 1) = (51749561 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_2 : literalDescent (0, 0) (1, 0) = (-26687847 / 5000000000) := rfl
@[simp] theorem lookup_previous_0_2 : previousPadding literalP (0, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_current_0_2 : currentPadding literalP (0, 0) (1, 0) = (-153040573 / 2500000000) := rfl
@[simp] theorem lookup_descent_0_3 : literalDescent (0, 0) (1, 1) = (-342335539 / 250000000000) := rfl
@[simp] theorem lookup_previous_0_3 : previousPadding literalP (0, 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_current_0_3 : currentPadding literalP (0, 0) (1, 1) = (5954248003 / 50000000000) := rfl
@[simp] theorem lookup_descent_0_4 : literalDescent (0, 0) (2, 0) = (-50543 / 5000000000) := rfl
@[simp] theorem lookup_previous_0_4 : previousPadding literalP (0, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_current_0_4 : currentPadding literalP (0, 0) (2, 0) = (-1114758857 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_5 : literalDescent (0, 0) (2, 1) = (244904621 / 250000000000) := rfl
@[simp] theorem lookup_previous_0_5 : previousPadding literalP (0, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_current_0_5 : currentPadding literalP (0, 0) (2, 1) = (6045207623 / 62500000000) := rfl
@[simp] theorem lookup_descent_0_6 : literalDescent (0, 0) (3, 0) = (54866773 / 10000000000) := rfl
@[simp] theorem lookup_previous_0_6 : previousPadding literalP (0, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_current_0_6 : currentPadding literalP (0, 0) (3, 0) = (25388829 / 625000000) := rfl
@[simp] theorem lookup_descent_0_7 : literalDescent (0, 0) (3, 1) = (-43226931 / 125000000000) := rfl
@[simp] theorem lookup_previous_0_7 : previousPadding literalP (0, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_current_0_7 : currentPadding literalP (0, 0) (3, 1) = (19307473 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_8 : literalDescent (0, 0) (4, 0) = (-33976901 / 20000000000) := rfl
@[simp] theorem lookup_previous_0_8 : previousPadding literalP (0, 0) (4, 0) = 0 := rfl
@[simp] theorem lookup_current_0_8 : currentPadding literalP (0, 0) (4, 0) = (12481049 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_9 : literalDescent (0, 0) (4, 1) = (-563461407 / 500000000000) := rfl
@[simp] theorem lookup_previous_0_9 : previousPadding literalP (0, 0) (4, 1) = 0 := rfl
@[simp] theorem lookup_current_0_9 : currentPadding literalP (0, 0) (4, 1) = (-28958009 / 2000000000) := rfl
@[simp] theorem lookup_descent_0_10 : literalDescent (0, 0) (5, 0) = (-127963 / 10000000000) := rfl
@[simp] theorem lookup_previous_0_10 : previousPadding literalP (0, 0) (5, 0) = 0 := rfl
@[simp] theorem lookup_current_0_10 : currentPadding literalP (0, 0) (5, 0) = (1537679 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_11 : literalDescent (0, 0) (5, 1) = (147305437 / 100000000000) := rfl
@[simp] theorem lookup_previous_0_11 : previousPadding literalP (0, 0) (5, 1) = 0 := rfl
@[simp] theorem lookup_current_0_11 : currentPadding literalP (0, 0) (5, 1) = (763867 / 250000000) := rfl
@[simp] theorem lookup_descent_0_12 : literalDescent (0, 0) (6, 0) = (-14550959 / 10000000000) := rfl
@[simp] theorem lookup_previous_0_12 : previousPadding literalP (0, 0) (6, 0) = 0 := rfl
@[simp] theorem lookup_current_0_12 : currentPadding literalP (0, 0) (6, 0) = (1609743 / 1000000000) := rfl
@[simp] theorem lookup_descent_0_13 : literalDescent (0, 0) (6, 1) = (2284113 / 500000000000) := rfl
@[simp] theorem lookup_previous_0_13 : previousPadding literalP (0, 0) (6, 1) = 0 := rfl
@[simp] theorem lookup_current_0_13 : currentPadding literalP (0, 0) (6, 1) = (-1138533 / 500000000) := rfl
@[simp] theorem lookup_descent_0_14 : literalDescent (0, 0) (7, 0) = (-17375753 / 20000000000) := rfl
@[simp] theorem lookup_previous_0_14 : previousPadding literalP (0, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_current_0_14 : currentPadding literalP (0, 0) (7, 0) = (3770829 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_15 : literalDescent (0, 0) (7, 1) = (16059651 / 62500000000) := rfl
@[simp] theorem lookup_previous_0_15 : previousPadding literalP (0, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_current_0_15 : currentPadding literalP (0, 0) (7, 1) = (212259 / 78125000) := rfl
@[simp] theorem lookup_descent_0_16 : literalDescent (0, 0) (8, 0) = (2588017 / 10000000000) := rfl
@[simp] theorem lookup_previous_0_16 : previousPadding literalP (0, 0) (8, 0) = 0 := rfl
@[simp] theorem lookup_current_0_16 : currentPadding literalP (0, 0) (8, 0) = (-14486313 / 10000000000) := rfl
@[simp] theorem lookup_descent_0_17 : literalDescent (0, 0) (8, 1) = (-106656919 / 250000000000) := rfl
@[simp] theorem lookup_previous_0_17 : previousPadding literalP (0, 0) (8, 1) = 0 := rfl
@[simp] theorem lookup_current_0_17 : currentPadding literalP (0, 0) (8, 1) = (2903 / 8000000) := rfl
@[simp] theorem lookup_descent_0_18 : literalDescent (0, 0) (9, 0) = (1887537 / 2000000000) := rfl
@[simp] theorem lookup_previous_0_18 : previousPadding literalP (0, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_current_0_18 : currentPadding literalP (0, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_0_19 : literalDescent (0, 0) (9, 1) = (-22767213 / 250000000000) := rfl
@[simp] theorem lookup_previous_0_19 : previousPadding literalP (0, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_current_0_19 : currentPadding literalP (0, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_1_0 : literalDescent (0, 1) (0, 0) = (12911629 / 20000000000) := rfl
@[simp] theorem lookup_previous_1_0 : previousPadding literalP (0, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_1_0 : currentPadding literalP (0, 1) (0, 0) = (51749561 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_1 : literalDescent (0, 1) (0, 1) = (36606237 / 50000000000) := rfl
@[simp] theorem lookup_previous_1_1 : previousPadding literalP (0, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_1_1 : currentPadding literalP (0, 1) (0, 1) = (3308886469 / 25000000000) := rfl
@[simp] theorem lookup_descent_1_2 : literalDescent (0, 1) (1, 0) = (-110565459 / 50000000000) := rfl
@[simp] theorem lookup_previous_1_2 : previousPadding literalP (0, 1) (1, 0) = 0 := rfl
@[simp] theorem lookup_current_1_2 : currentPadding literalP (0, 1) (1, 0) = (-6434183097 / 100000000000) := rfl
@[simp] theorem lookup_descent_1_3 : literalDescent (0, 1) (1, 1) = (-34035153 / 50000000000) := rfl
@[simp] theorem lookup_previous_1_3 : previousPadding literalP (0, 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_current_1_3 : currentPadding literalP (0, 1) (1, 1) = (-18214397 / 2500000000) := rfl
@[simp] theorem lookup_descent_1_4 : literalDescent (0, 1) (2, 0) = (-841347 / 2000000000) := rfl
@[simp] theorem lookup_previous_1_4 : previousPadding literalP (0, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_current_1_4 : currentPadding literalP (0, 1) (2, 0) = (159373101 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_5 : literalDescent (0, 1) (2, 1) = (-164322437 / 500000000000) := rfl
@[simp] theorem lookup_previous_1_5 : previousPadding literalP (0, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_current_1_5 : currentPadding literalP (0, 1) (2, 1) = (-277893391 / 2500000000) := rfl
@[simp] theorem lookup_descent_1_6 : literalDescent (0, 1) (3, 0) = (368954193 / 100000000000) := rfl
@[simp] theorem lookup_previous_1_6 : previousPadding literalP (0, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_current_1_6 : currentPadding literalP (0, 1) (3, 0) = (4241927917 / 100000000000) := rfl
@[simp] theorem lookup_descent_1_7 : literalDescent (0, 1) (3, 1) = (648763 / 6250000000) := rfl
@[simp] theorem lookup_previous_1_7 : previousPadding literalP (0, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_current_1_7 : currentPadding literalP (0, 1) (3, 1) = (3702519 / 2500000000) := rfl
@[simp] theorem lookup_descent_1_8 : literalDescent (0, 1) (4, 0) = (-3322053 / 4000000000) := rfl
@[simp] theorem lookup_previous_1_8 : previousPadding literalP (0, 1) (4, 0) = 0 := rfl
@[simp] theorem lookup_current_1_8 : currentPadding literalP (0, 1) (4, 0) = (3797843 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_9 : literalDescent (0, 1) (4, 1) = (-323074399 / 500000000000) := rfl
@[simp] theorem lookup_previous_1_9 : previousPadding literalP (0, 1) (4, 1) = 0 := rfl
@[simp] theorem lookup_current_1_9 : currentPadding literalP (0, 1) (4, 1) = (-74799457 / 5000000000) := rfl
@[simp] theorem lookup_descent_1_10 : literalDescent (0, 1) (5, 0) = (-1665311 / 20000000000) := rfl
@[simp] theorem lookup_previous_1_10 : previousPadding literalP (0, 1) (5, 0) = 0 := rfl
@[simp] theorem lookup_current_1_10 : currentPadding literalP (0, 1) (5, 0) = (2242437 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_11 : literalDescent (0, 1) (5, 1) = (177831779 / 250000000000) := rfl
@[simp] theorem lookup_previous_1_11 : previousPadding literalP (0, 1) (5, 1) = 0 := rfl
@[simp] theorem lookup_current_1_11 : currentPadding literalP (0, 1) (5, 1) = (38165927 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_12 : literalDescent (0, 1) (6, 0) = (88741 / 20000000000) := rfl
@[simp] theorem lookup_previous_1_12 : previousPadding literalP (0, 1) (6, 0) = 0 := rfl
@[simp] theorem lookup_current_1_12 : currentPadding literalP (0, 1) (6, 0) = (187769 / 1250000000) := rfl
@[simp] theorem lookup_descent_1_13 : literalDescent (0, 1) (6, 1) = (63804443 / 250000000000) := rfl
@[simp] theorem lookup_previous_1_13 : previousPadding literalP (0, 1) (6, 1) = 0 := rfl
@[simp] theorem lookup_current_1_13 : currentPadding literalP (0, 1) (6, 1) = (-25283229 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_14 : literalDescent (0, 1) (7, 0) = (-22036387 / 20000000000) := rfl
@[simp] theorem lookup_previous_1_14 : previousPadding literalP (0, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_current_1_14 : currentPadding literalP (0, 1) (7, 0) = (6101191 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_15 : literalDescent (0, 1) (7, 1) = (54418421 / 250000000000) := rfl
@[simp] theorem lookup_previous_1_15 : previousPadding literalP (0, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_current_1_15 : currentPadding literalP (0, 1) (7, 1) = (2113457 / 5000000000) := rfl
@[simp] theorem lookup_descent_1_16 : literalDescent (0, 1) (8, 0) = (-6357481 / 10000000000) := rfl
@[simp] theorem lookup_previous_1_16 : previousPadding literalP (0, 1) (8, 0) = 0 := rfl
@[simp] theorem lookup_current_1_16 : currentPadding literalP (0, 1) (8, 0) = (-5540767 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_17 : literalDescent (0, 1) (8, 1) = (-1709403 / 6250000000) := rfl
@[simp] theorem lookup_previous_1_17 : previousPadding literalP (0, 1) (8, 1) = 0 := rfl
@[simp] theorem lookup_current_1_17 : currentPadding literalP (0, 1) (8, 1) = (-18437441 / 10000000000) := rfl
@[simp] theorem lookup_descent_1_18 : literalDescent (0, 1) (9, 0) = (1887537 / 2000000000) := rfl
@[simp] theorem lookup_previous_1_18 : previousPadding literalP (0, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_current_1_18 : currentPadding literalP (0, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_1_19 : literalDescent (0, 1) (9, 1) = (-4557209 / 50000000000) := rfl
@[simp] theorem lookup_previous_1_19 : previousPadding literalP (0, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_current_1_19 : currentPadding literalP (0, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_2_0 : literalDescent (1, 0) (0, 0) = (-26687847 / 5000000000) := rfl
@[simp] theorem lookup_previous_2_0 : previousPadding literalP (1, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_2_0 : currentPadding literalP (1, 0) (0, 0) = (-153040573 / 2500000000) := rfl
@[simp] theorem lookup_descent_2_1 : literalDescent (1, 0) (0, 1) = (-110565459 / 50000000000) := rfl
@[simp] theorem lookup_previous_2_1 : previousPadding literalP (1, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_2_1 : currentPadding literalP (1, 0) (0, 1) = (-6434183097 / 100000000000) := rfl
@[simp] theorem lookup_descent_2_2 : literalDescent (1, 0) (1, 0) = (15036977 / 1000000000) := rfl
@[simp] theorem lookup_previous_2_2 : previousPadding literalP (1, 0) (1, 0) = (1304136281 / 10000000000) := rfl
@[simp] theorem lookup_current_2_2 : currentPadding literalP (1, 0) (1, 0) = (144220831 / 1250000000) := rfl
@[simp] theorem lookup_descent_2_3 : literalDescent (1, 0) (1, 1) = (1916689001 / 500000000000) := rfl
@[simp] theorem lookup_previous_2_3 : previousPadding literalP (1, 0) (1, 1) = (51749561 / 10000000000) := rfl
@[simp] theorem lookup_current_2_3 : currentPadding literalP (1, 0) (1, 1) = (-16981871627 / 100000000000) := rfl
@[simp] theorem lookup_descent_2_4 : literalDescent (1, 0) (2, 0) = (-48762259 / 10000000000) := rfl
@[simp] theorem lookup_previous_2_4 : previousPadding literalP (1, 0) (2, 0) = (-153040573 / 2500000000) := rfl
@[simp] theorem lookup_current_2_4 : currentPadding literalP (1, 0) (2, 0) = (1951709 / 2000000000) := rfl
@[simp] theorem lookup_descent_2_5 : literalDescent (1, 0) (2, 1) = (-1210276171 / 500000000000) := rfl
@[simp] theorem lookup_previous_2_5 : previousPadding literalP (1, 0) (2, 1) = (5954248003 / 50000000000) := rfl
@[simp] theorem lookup_current_2_5 : currentPadding literalP (1, 0) (2, 1) = (-151837731 / 5000000000) := rfl
@[simp] theorem lookup_descent_2_6 : literalDescent (1, 0) (3, 0) = (-292972459 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_6 : previousPadding literalP (1, 0) (3, 0) = (-1114758857 / 10000000000) := rfl
@[simp] theorem lookup_current_2_6 : currentPadding literalP (1, 0) (3, 0) = (-30258519 / 312500000) := rfl
@[simp] theorem lookup_descent_2_7 : literalDescent (1, 0) (3, 1) = (159545357 / 100000000000) := rfl
@[simp] theorem lookup_previous_2_7 : previousPadding literalP (1, 0) (3, 1) = (6045207623 / 62500000000) := rfl
@[simp] theorem lookup_current_2_7 : currentPadding literalP (1, 0) (3, 1) = (9453001937 / 250000000000) := rfl
@[simp] theorem lookup_descent_2_8 : literalDescent (1, 0) (4, 0) = (17758527 / 2000000000) := rfl
@[simp] theorem lookup_previous_2_8 : previousPadding literalP (1, 0) (4, 0) = (25388829 / 625000000) := rfl
@[simp] theorem lookup_current_2_8 : currentPadding literalP (1, 0) (4, 0) = (97056499 / 2500000000) := rfl
@[simp] theorem lookup_descent_2_9 : literalDescent (1, 0) (4, 1) = (43019893 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_9 : previousPadding literalP (1, 0) (4, 1) = (19307473 / 10000000000) := rfl
@[simp] theorem lookup_current_2_9 : currentPadding literalP (1, 0) (4, 1) = (34297437 / 5000000000) := rfl
@[simp] theorem lookup_descent_2_10 : literalDescent (1, 0) (5, 0) = (-828373 / 4000000000) := rfl
@[simp] theorem lookup_previous_2_10 : previousPadding literalP (1, 0) (5, 0) = (12481049 / 10000000000) := rfl
@[simp] theorem lookup_current_2_10 : currentPadding literalP (1, 0) (5, 0) = (2910403 / 2000000000) := rfl
@[simp] theorem lookup_descent_2_11 : literalDescent (1, 0) (5, 1) = (-82800703 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_11 : previousPadding literalP (1, 0) (5, 1) = (-28958009 / 2000000000) := rfl
@[simp] theorem lookup_current_2_11 : currentPadding literalP (1, 0) (5, 1) = (-174187027 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_12 : literalDescent (1, 0) (6, 0) = (291703 / 125000000) := rfl
@[simp] theorem lookup_previous_2_12 : previousPadding literalP (1, 0) (6, 0) = (1537679 / 10000000000) := rfl
@[simp] theorem lookup_current_2_12 : currentPadding literalP (1, 0) (6, 0) = (-5223779 / 5000000000) := rfl
@[simp] theorem lookup_descent_2_13 : literalDescent (1, 0) (6, 1) = (20595489 / 20000000000) := rfl
@[simp] theorem lookup_previous_2_13 : previousPadding literalP (1, 0) (6, 1) = (763867 / 250000000) := rfl
@[simp] theorem lookup_current_2_13 : currentPadding literalP (1, 0) (6, 1) = (6321581 / 2000000000) := rfl
@[simp] theorem lookup_descent_2_14 : literalDescent (1, 0) (7, 0) = (-532371 / 500000000) := rfl
@[simp] theorem lookup_previous_2_14 : previousPadding literalP (1, 0) (7, 0) = (1609743 / 1000000000) := rfl
@[simp] theorem lookup_current_2_14 : currentPadding literalP (1, 0) (7, 0) = (26744907 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_15 : literalDescent (1, 0) (7, 1) = (-1523567 / 1250000000) := rfl
@[simp] theorem lookup_previous_2_15 : previousPadding literalP (1, 0) (7, 1) = (-1138533 / 500000000) := rfl
@[simp] theorem lookup_current_2_15 : currentPadding literalP (1, 0) (7, 1) = (-2193307 / 1000000000) := rfl
@[simp] theorem lookup_descent_2_16 : literalDescent (1, 0) (8, 0) = (13330203 / 10000000000) := rfl
@[simp] theorem lookup_previous_2_16 : previousPadding literalP (1, 0) (8, 0) = (3770829 / 10000000000) := rfl
@[simp] theorem lookup_current_2_16 : currentPadding literalP (1, 0) (8, 0) = (-2165653 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_17 : literalDescent (1, 0) (8, 1) = (17576467 / 10000000000) := rfl
@[simp] theorem lookup_previous_2_17 : previousPadding literalP (1, 0) (8, 1) = (212259 / 78125000) := rfl
@[simp] theorem lookup_current_2_17 : currentPadding literalP (1, 0) (8, 1) = (16986349 / 10000000000) := rfl
@[simp] theorem lookup_descent_2_18 : literalDescent (1, 0) (9, 0) = (-14486313 / 10000000000) := rfl
@[simp] theorem lookup_previous_2_18 : previousPadding literalP (1, 0) (9, 0) = (-14486313 / 10000000000) := rfl
@[simp] theorem lookup_current_2_18 : currentPadding literalP (1, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_2_19 : literalDescent (1, 0) (9, 1) = (-3764971 / 10000000000) := rfl
@[simp] theorem lookup_previous_2_19 : previousPadding literalP (1, 0) (9, 1) = (2903 / 8000000) := rfl
@[simp] theorem lookup_current_2_19 : currentPadding literalP (1, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_3_0 : literalDescent (1, 1) (0, 0) = (-342335539 / 250000000000) := rfl
@[simp] theorem lookup_previous_3_0 : previousPadding literalP (1, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_3_0 : currentPadding literalP (1, 1) (0, 0) = (5954248003 / 50000000000) := rfl
@[simp] theorem lookup_descent_3_1 : literalDescent (1, 1) (0, 1) = (-34035153 / 50000000000) := rfl
@[simp] theorem lookup_previous_3_1 : previousPadding literalP (1, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_3_1 : currentPadding literalP (1, 1) (0, 1) = (-18214397 / 2500000000) := rfl
@[simp] theorem lookup_descent_3_2 : literalDescent (1, 1) (1, 0) = (1916689001 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_2 : previousPadding literalP (1, 1) (1, 0) = (51749561 / 10000000000) := rfl
@[simp] theorem lookup_current_3_2 : currentPadding literalP (1, 1) (1, 0) = (-16981871627 / 100000000000) := rfl
@[simp] theorem lookup_descent_3_3 : literalDescent (1, 1) (1, 1) = (834716701 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_3 : previousPadding literalP (1, 1) (1, 1) = (3308886469 / 25000000000) := rfl
@[simp] theorem lookup_current_3_3 : currentPadding literalP (1, 1) (1, 1) = (1353136747 / 100000000000) := rfl
@[simp] theorem lookup_descent_3_4 : literalDescent (1, 1) (2, 0) = (-1051878983 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_4 : previousPadding literalP (1, 1) (2, 0) = (-6434183097 / 100000000000) := rfl
@[simp] theorem lookup_current_3_4 : currentPadding literalP (1, 1) (2, 0) = (5325641 / 100000000) := rfl
@[simp] theorem lookup_descent_3_5 : literalDescent (1, 1) (2, 1) = (-178158359 / 250000000000) := rfl
@[simp] theorem lookup_previous_3_5 : previousPadding literalP (1, 1) (2, 1) = (-18214397 / 2500000000) := rfl
@[simp] theorem lookup_current_3_5 : currentPadding literalP (1, 1) (2, 1) = (-1136377 / 400000000) := rfl
@[simp] theorem lookup_descent_3_6 : literalDescent (1, 1) (3, 0) = (-2342224527 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_6 : previousPadding literalP (1, 1) (3, 0) = (159373101 / 10000000000) := rfl
@[simp] theorem lookup_current_3_6 : currentPadding literalP (1, 1) (3, 0) = (-254870329 / 10000000000) := rfl
@[simp] theorem lookup_descent_3_7 : literalDescent (1, 1) (3, 1) = (-107988129 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_7 : previousPadding literalP (1, 1) (3, 1) = (-277893391 / 2500000000) := rfl
@[simp] theorem lookup_current_3_7 : currentPadding literalP (1, 1) (3, 1) = (-23861859 / 5000000000) := rfl
@[simp] theorem lookup_descent_3_8 : literalDescent (1, 1) (4, 0) = (450105987 / 100000000000) := rfl
@[simp] theorem lookup_previous_3_8 : previousPadding literalP (1, 1) (4, 0) = (4241927917 / 100000000000) := rfl
@[simp] theorem lookup_current_3_8 : currentPadding literalP (1, 1) (4, 0) = (2505906431 / 100000000000) := rfl
@[simp] theorem lookup_descent_3_9 : literalDescent (1, 1) (4, 1) = (83743121 / 125000000000) := rfl
@[simp] theorem lookup_previous_3_9 : previousPadding literalP (1, 1) (4, 1) = (3702519 / 2500000000) := rfl
@[simp] theorem lookup_current_3_9 : currentPadding literalP (1, 1) (4, 1) = (6214403 / 2000000000) := rfl
@[simp] theorem lookup_descent_3_10 : literalDescent (1, 1) (5, 0) = (65638183 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_10 : previousPadding literalP (1, 1) (5, 0) = (3797843 / 10000000000) := rfl
@[simp] theorem lookup_current_3_10 : currentPadding literalP (1, 1) (5, 0) = (537679 / 5000000000) := rfl
@[simp] theorem lookup_descent_3_11 : literalDescent (1, 1) (5, 1) = (-704582059 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_11 : previousPadding literalP (1, 1) (5, 1) = (-74799457 / 5000000000) := rfl
@[simp] theorem lookup_current_3_11 : currentPadding literalP (1, 1) (5, 1) = (-11921871 / 2500000000) := rfl
@[simp] theorem lookup_descent_3_12 : literalDescent (1, 1) (6, 0) = (20583071 / 125000000000) := rfl
@[simp] theorem lookup_previous_3_12 : previousPadding literalP (1, 1) (6, 0) = (2242437 / 10000000000) := rfl
@[simp] theorem lookup_current_3_12 : currentPadding literalP (1, 1) (6, 0) = (-557263 / 250000000) := rfl
@[simp] theorem lookup_descent_3_13 : literalDescent (1, 1) (6, 1) = (113640481 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_13 : previousPadding literalP (1, 1) (6, 1) = (38165927 / 10000000000) := rfl
@[simp] theorem lookup_current_3_13 : currentPadding literalP (1, 1) (6, 1) = (18642173 / 5000000000) := rfl
@[simp] theorem lookup_descent_3_14 : literalDescent (1, 1) (7, 0) = (-28694703 / 500000000000) := rfl
@[simp] theorem lookup_previous_3_14 : previousPadding literalP (1, 1) (7, 0) = (187769 / 1250000000) := rfl
@[simp] theorem lookup_current_3_14 : currentPadding literalP (1, 1) (7, 0) = (3496513 / 5000000000) := rfl
@[simp] theorem lookup_descent_3_15 : literalDescent (1, 1) (7, 1) = (-35657159 / 250000000000) := rfl
@[simp] theorem lookup_previous_3_15 : previousPadding literalP (1, 1) (7, 1) = (-25283229 / 10000000000) := rfl
@[simp] theorem lookup_current_3_15 : currentPadding literalP (1, 1) (7, 1) = (-1784163 / 2000000000) := rfl
@[simp] theorem lookup_descent_3_16 : literalDescent (1, 1) (8, 0) = (67650311 / 62500000000) := rfl
@[simp] theorem lookup_previous_3_16 : previousPadding literalP (1, 1) (8, 0) = (6101191 / 10000000000) := rfl
@[simp] theorem lookup_current_3_16 : currentPadding literalP (1, 1) (8, 0) = (-1681179 / 2500000000) := rfl
@[simp] theorem lookup_descent_3_17 : literalDescent (1, 1) (8, 1) = (239256637 / 250000000000) := rfl
@[simp] theorem lookup_previous_3_17 : previousPadding literalP (1, 1) (8, 1) = (2113457 / 5000000000) := rfl
@[simp] theorem lookup_current_3_17 : currentPadding literalP (1, 1) (8, 1) = (964523 / 5000000000) := rfl
@[simp] theorem lookup_descent_3_18 : literalDescent (1, 1) (9, 0) = (-3744613 / 2500000000) := rfl
@[simp] theorem lookup_previous_3_18 : previousPadding literalP (1, 1) (9, 0) = (-5540767 / 10000000000) := rfl
@[simp] theorem lookup_current_3_18 : currentPadding literalP (1, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_3_19 : literalDescent (1, 1) (9, 1) = (-90645093 / 250000000000) := rfl
@[simp] theorem lookup_previous_3_19 : previousPadding literalP (1, 1) (9, 1) = (-18437441 / 10000000000) := rfl
@[simp] theorem lookup_current_3_19 : currentPadding literalP (1, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_4_0 : literalDescent (2, 0) (0, 0) = (-50543 / 5000000000) := rfl
@[simp] theorem lookup_previous_4_0 : previousPadding literalP (2, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_4_0 : currentPadding literalP (2, 0) (0, 0) = (-1114758857 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_1 : literalDescent (2, 0) (0, 1) = (-841347 / 2000000000) := rfl
@[simp] theorem lookup_previous_4_1 : previousPadding literalP (2, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_4_1 : currentPadding literalP (2, 0) (0, 1) = (159373101 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_2 : literalDescent (2, 0) (1, 0) = (-48762259 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_2 : previousPadding literalP (2, 0) (1, 0) = (-153040573 / 2500000000) := rfl
@[simp] theorem lookup_current_4_2 : currentPadding literalP (2, 0) (1, 0) = (1951709 / 2000000000) := rfl
@[simp] theorem lookup_descent_4_3 : literalDescent (2, 0) (1, 1) = (-1051878983 / 500000000000) := rfl
@[simp] theorem lookup_previous_4_3 : previousPadding literalP (2, 0) (1, 1) = (-6434183097 / 100000000000) := rfl
@[simp] theorem lookup_current_4_3 : currentPadding literalP (2, 0) (1, 1) = (5325641 / 100000000) := rfl
@[simp] theorem lookup_descent_4_4 : literalDescent (2, 0) (2, 0) = (40444429 / 2500000000) := rfl
@[simp] theorem lookup_previous_4_4 : previousPadding literalP (2, 0) (2, 0) = (144220831 / 1250000000) := rfl
@[simp] theorem lookup_current_4_4 : currentPadding literalP (2, 0) (2, 0) = (1037695831 / 5000000000) := rfl
@[simp] theorem lookup_descent_4_5 : literalDescent (2, 0) (2, 1) = (2041561599 / 500000000000) := rfl
@[simp] theorem lookup_previous_4_5 : previousPadding literalP (2, 0) (2, 1) = (-16981871627 / 100000000000) := rfl
@[simp] theorem lookup_current_4_5 : currentPadding literalP (2, 0) (2, 1) = (-32780792409 / 500000000000) := rfl
@[simp] theorem lookup_descent_4_6 : literalDescent (2, 0) (3, 0) = (-7679379 / 1250000000) := rfl
@[simp] theorem lookup_previous_4_6 : previousPadding literalP (2, 0) (3, 0) = (1951709 / 2000000000) := rfl
@[simp] theorem lookup_current_4_6 : currentPadding literalP (2, 0) (3, 0) = (-117626947 / 2500000000) := rfl
@[simp] theorem lookup_descent_4_7 : literalDescent (2, 0) (3, 1) = (-702782463 / 250000000000) := rfl
@[simp] theorem lookup_previous_4_7 : previousPadding literalP (2, 0) (3, 1) = (-151837731 / 5000000000) := rfl
@[simp] theorem lookup_current_4_7 : currentPadding literalP (2, 0) (3, 1) = (-340568531 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_8 : literalDescent (2, 0) (4, 0) = (-136222327 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_8 : previousPadding literalP (2, 0) (4, 0) = (-30258519 / 312500000) := rfl
@[simp] theorem lookup_current_4_8 : currentPadding literalP (2, 0) (4, 0) = (-832050281 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_9 : literalDescent (2, 0) (4, 1) = (2018929 / 781250000) := rfl
@[simp] theorem lookup_previous_4_9 : previousPadding literalP (2, 0) (4, 1) = (9453001937 / 250000000000) := rfl
@[simp] theorem lookup_current_4_9 : currentPadding literalP (2, 0) (4, 1) = (8806944657 / 250000000000) := rfl
@[simp] theorem lookup_descent_4_10 : literalDescent (2, 0) (5, 0) = (8658339 / 1250000000) := rfl
@[simp] theorem lookup_previous_4_10 : previousPadding literalP (2, 0) (5, 0) = (97056499 / 2500000000) := rfl
@[simp] theorem lookup_current_4_10 : currentPadding literalP (2, 0) (5, 0) = (79739821 / 2500000000) := rfl
@[simp] theorem lookup_descent_4_11 : literalDescent (2, 0) (5, 1) = (3714111 / 2000000000) := rfl
@[simp] theorem lookup_previous_4_11 : previousPadding literalP (2, 0) (5, 1) = (34297437 / 5000000000) := rfl
@[simp] theorem lookup_current_4_11 : currentPadding literalP (2, 0) (5, 1) = (50024319 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_12 : literalDescent (2, 0) (6, 0) = (-22755319 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_12 : previousPadding literalP (2, 0) (6, 0) = (2910403 / 2000000000) := rfl
@[simp] theorem lookup_current_4_12 : currentPadding literalP (2, 0) (6, 0) = (18653667 / 5000000000) := rfl
@[simp] theorem lookup_descent_4_13 : literalDescent (2, 0) (6, 1) = (-20134553 / 5000000000) := rfl
@[simp] theorem lookup_previous_4_13 : previousPadding literalP (2, 0) (6, 1) = (-174187027 / 10000000000) := rfl
@[simp] theorem lookup_current_4_13 : currentPadding literalP (2, 0) (6, 1) = (-133917921 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_14 : literalDescent (2, 0) (7, 0) = (29547999 / 5000000000) := rfl
@[simp] theorem lookup_previous_4_14 : previousPadding literalP (2, 0) (7, 0) = (-5223779 / 5000000000) := rfl
@[simp] theorem lookup_current_4_14 : currentPadding literalP (2, 0) (7, 0) = (-17385889 / 2500000000) := rfl
@[simp] theorem lookup_descent_4_15 : literalDescent (2, 0) (7, 1) = (14810711 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_15 : previousPadding literalP (2, 0) (7, 1) = (6321581 / 2000000000) := rfl
@[simp] theorem lookup_current_4_15 : currentPadding literalP (2, 0) (7, 1) = (8398597 / 5000000000) := rfl
@[simp] theorem lookup_descent_4_16 : literalDescent (2, 0) (8, 0) = (-14959 / 8000000) := rfl
@[simp] theorem lookup_previous_4_16 : previousPadding literalP (2, 0) (8, 0) = (26744907 / 10000000000) := rfl
@[simp] theorem lookup_current_4_16 : currentPadding literalP (2, 0) (8, 0) = (45443657 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_17 : literalDescent (2, 0) (8, 1) = (-23416419 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_17 : previousPadding literalP (2, 0) (8, 1) = (-2193307 / 1000000000) := rfl
@[simp] theorem lookup_current_4_17 : currentPadding literalP (2, 0) (8, 1) = (1483349 / 10000000000) := rfl
@[simp] theorem lookup_descent_4_18 : literalDescent (2, 0) (9, 0) = (-2165653 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_18 : previousPadding literalP (2, 0) (9, 0) = (-2165653 / 10000000000) := rfl
@[simp] theorem lookup_current_4_18 : currentPadding literalP (2, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_4_19 : literalDescent (2, 0) (9, 1) = (16986349 / 10000000000) := rfl
@[simp] theorem lookup_previous_4_19 : previousPadding literalP (2, 0) (9, 1) = (16986349 / 10000000000) := rfl
@[simp] theorem lookup_current_4_19 : currentPadding literalP (2, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_5_0 : literalDescent (2, 1) (0, 0) = (244904621 / 250000000000) := rfl
@[simp] theorem lookup_previous_5_0 : previousPadding literalP (2, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_5_0 : currentPadding literalP (2, 1) (0, 0) = (6045207623 / 62500000000) := rfl
@[simp] theorem lookup_descent_5_1 : literalDescent (2, 1) (0, 1) = (-164322437 / 500000000000) := rfl
@[simp] theorem lookup_previous_5_1 : previousPadding literalP (2, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_5_1 : currentPadding literalP (2, 1) (0, 1) = (-277893391 / 2500000000) := rfl
@[simp] theorem lookup_descent_5_2 : literalDescent (2, 1) (1, 0) = (-1210276171 / 500000000000) := rfl
@[simp] theorem lookup_previous_5_2 : previousPadding literalP (2, 1) (1, 0) = (5954248003 / 50000000000) := rfl
@[simp] theorem lookup_current_5_2 : currentPadding literalP (2, 1) (1, 0) = (-151837731 / 5000000000) := rfl
@[simp] theorem lookup_descent_5_3 : literalDescent (2, 1) (1, 1) = (-178158359 / 250000000000) := rfl
@[simp] theorem lookup_previous_5_3 : previousPadding literalP (2, 1) (1, 1) = (-18214397 / 2500000000) := rfl
@[simp] theorem lookup_current_5_3 : currentPadding literalP (2, 1) (1, 1) = (-1136377 / 400000000) := rfl
@[simp] theorem lookup_descent_5_4 : literalDescent (2, 1) (2, 0) = (2041561599 / 500000000000) := rfl
@[simp] theorem lookup_previous_5_4 : previousPadding literalP (2, 1) (2, 0) = (-16981871627 / 100000000000) := rfl
@[simp] theorem lookup_current_5_4 : currentPadding literalP (2, 1) (2, 0) = (-32780792409 / 500000000000) := rfl
@[simp] theorem lookup_descent_5_5 : literalDescent (2, 1) (2, 1) = (241705199 / 100000000000) := rfl
@[simp] theorem lookup_previous_5_5 : previousPadding literalP (2, 1) (2, 1) = (1353136747 / 100000000000) := rfl
@[simp] theorem lookup_current_5_5 : currentPadding literalP (2, 1) (2, 1) = (1866477813 / 15625000000) := rfl
@[simp] theorem lookup_descent_5_6 : literalDescent (2, 1) (3, 0) = (-11580541 / 5000000000) := rfl
@[simp] theorem lookup_previous_5_6 : previousPadding literalP (2, 1) (3, 0) = (5325641 / 100000000) := rfl
@[simp] theorem lookup_current_5_6 : currentPadding literalP (2, 1) (3, 0) = (14023817 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_7 : literalDescent (2, 1) (3, 1) = (-58363269 / 50000000000) := rfl
@[simp] theorem lookup_previous_5_7 : previousPadding literalP (2, 1) (3, 1) = (-1136377 / 400000000) := rfl
@[simp] theorem lookup_current_5_7 : currentPadding literalP (2, 1) (3, 1) = (-16348187 / 2000000000) := rfl
@[simp] theorem lookup_descent_5_8 : literalDescent (2, 1) (4, 0) = (-8177543 / 2000000000) := rfl
@[simp] theorem lookup_previous_5_8 : previousPadding literalP (2, 1) (4, 0) = (-254870329 / 10000000000) := rfl
@[simp] theorem lookup_current_5_8 : currentPadding literalP (2, 1) (4, 0) = (-106991307 / 5000000000) := rfl
@[simp] theorem lookup_descent_5_9 : literalDescent (2, 1) (4, 1) = (-1310123 / 5000000000) := rfl
@[simp] theorem lookup_previous_5_9 : previousPadding literalP (2, 1) (4, 1) = (-23861859 / 5000000000) := rfl
@[simp] theorem lookup_current_5_9 : currentPadding literalP (2, 1) (4, 1) = (-2818967 / 625000000) := rfl
@[simp] theorem lookup_descent_5_10 : literalDescent (2, 1) (5, 0) = (113413939 / 25000000000) := rfl
@[simp] theorem lookup_previous_5_10 : previousPadding literalP (2, 1) (5, 0) = (2505906431 / 100000000000) := rfl
@[simp] theorem lookup_current_5_10 : currentPadding literalP (2, 1) (5, 0) = (82090027 / 4000000000) := rfl
@[simp] theorem lookup_descent_5_11 : literalDescent (2, 1) (5, 1) = (3220477 / 5000000000) := rfl
@[simp] theorem lookup_previous_5_11 : previousPadding literalP (2, 1) (5, 1) = (6214403 / 2000000000) := rfl
@[simp] theorem lookup_current_5_11 : currentPadding literalP (2, 1) (5, 1) = (24631061 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_12 : literalDescent (2, 1) (6, 0) = (-13912491 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_12 : previousPadding literalP (2, 1) (6, 0) = (537679 / 5000000000) := rfl
@[simp] theorem lookup_current_5_12 : currentPadding literalP (2, 1) (6, 0) = (14987849 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_13 : literalDescent (2, 1) (6, 1) = (-13924049 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_13 : previousPadding literalP (2, 1) (6, 1) = (-11921871 / 2500000000) := rfl
@[simp] theorem lookup_current_5_13 : currentPadding literalP (2, 1) (6, 1) = (-6752687 / 2000000000) := rfl
@[simp] theorem lookup_descent_5_14 : literalDescent (2, 1) (7, 0) = (10438369 / 10000000000) := rfl
@[simp] theorem lookup_previous_5_14 : previousPadding literalP (2, 1) (7, 0) = (-557263 / 250000000) := rfl
@[simp] theorem lookup_current_5_14 : currentPadding literalP (2, 1) (7, 0) = (-32728889 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_15 : literalDescent (2, 1) (7, 1) = (5243573 / 5000000000) := rfl
@[simp] theorem lookup_previous_5_15 : previousPadding literalP (2, 1) (7, 1) = (18642173 / 5000000000) := rfl
@[simp] theorem lookup_current_5_15 : currentPadding literalP (2, 1) (7, 1) = (66993 / 25000000) := rfl
@[simp] theorem lookup_descent_5_16 : literalDescent (2, 1) (8, 0) = (1230083 / 5000000000) := rfl
@[simp] theorem lookup_previous_5_16 : previousPadding literalP (2, 1) (8, 0) = (3496513 / 5000000000) := rfl
@[simp] theorem lookup_current_5_16 : currentPadding literalP (2, 1) (8, 0) = (226643 / 500000000) := rfl
@[simp] theorem lookup_descent_5_17 : literalDescent (2, 1) (8, 1) = (-2198967 / 5000000000) := rfl
@[simp] theorem lookup_previous_5_17 : previousPadding literalP (2, 1) (8, 1) = (-1784163 / 2000000000) := rfl
@[simp] theorem lookup_current_5_17 : currentPadding literalP (2, 1) (8, 1) = (-4522881 / 10000000000) := rfl
@[simp] theorem lookup_descent_5_18 : literalDescent (2, 1) (9, 0) = (-1681179 / 2500000000) := rfl
@[simp] theorem lookup_previous_5_18 : previousPadding literalP (2, 1) (9, 0) = (-1681179 / 2500000000) := rfl
@[simp] theorem lookup_current_5_18 : currentPadding literalP (2, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_5_19 : literalDescent (2, 1) (9, 1) = (964523 / 5000000000) := rfl
@[simp] theorem lookup_previous_5_19 : previousPadding literalP (2, 1) (9, 1) = (964523 / 5000000000) := rfl
@[simp] theorem lookup_current_5_19 : currentPadding literalP (2, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_6_0 : literalDescent (3, 0) (0, 0) = (54866773 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_0 : previousPadding literalP (3, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_6_0 : currentPadding literalP (3, 0) (0, 0) = (25388829 / 625000000) := rfl
@[simp] theorem lookup_descent_6_1 : literalDescent (3, 0) (0, 1) = (368954193 / 100000000000) := rfl
@[simp] theorem lookup_previous_6_1 : previousPadding literalP (3, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_6_1 : currentPadding literalP (3, 0) (0, 1) = (4241927917 / 100000000000) := rfl
@[simp] theorem lookup_descent_6_2 : literalDescent (3, 0) (1, 0) = (-292972459 / 20000000000) := rfl
@[simp] theorem lookup_previous_6_2 : previousPadding literalP (3, 0) (1, 0) = (-1114758857 / 10000000000) := rfl
@[simp] theorem lookup_current_6_2 : currentPadding literalP (3, 0) (1, 0) = (-30258519 / 312500000) := rfl
@[simp] theorem lookup_descent_6_3 : literalDescent (3, 0) (1, 1) = (-2342224527 / 500000000000) := rfl
@[simp] theorem lookup_previous_6_3 : previousPadding literalP (3, 0) (1, 1) = (159373101 / 10000000000) := rfl
@[simp] theorem lookup_current_6_3 : currentPadding literalP (3, 0) (1, 1) = (-254870329 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_4 : literalDescent (3, 0) (2, 0) = (-7679379 / 1250000000) := rfl
@[simp] theorem lookup_previous_6_4 : previousPadding literalP (3, 0) (2, 0) = (1951709 / 2000000000) := rfl
@[simp] theorem lookup_current_6_4 : currentPadding literalP (3, 0) (2, 0) = (-117626947 / 2500000000) := rfl
@[simp] theorem lookup_descent_6_5 : literalDescent (3, 0) (2, 1) = (-11580541 / 5000000000) := rfl
@[simp] theorem lookup_previous_6_5 : previousPadding literalP (3, 0) (2, 1) = (5325641 / 100000000) := rfl
@[simp] theorem lookup_current_6_5 : currentPadding literalP (3, 0) (2, 1) = (14023817 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_6 : literalDescent (3, 0) (3, 0) = (36818217 / 1000000000) := rfl
@[simp] theorem lookup_previous_6_6 : previousPadding literalP (3, 0) (3, 0) = (1037695831 / 5000000000) := rfl
@[simp] theorem lookup_current_6_6 : currentPadding literalP (3, 0) (3, 0) = (1868436109 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_7 : literalDescent (3, 0) (3, 1) = (2093391891 / 500000000000) := rfl
@[simp] theorem lookup_previous_6_7 : previousPadding literalP (3, 0) (3, 1) = (-32780792409 / 500000000000) := rfl
@[simp] theorem lookup_current_6_7 : currentPadding literalP (3, 0) (3, 1) = (2721639 / 5000000000) := rfl
@[simp] theorem lookup_descent_6_8 : literalDescent (3, 0) (4, 0) = (-242858427 / 20000000000) := rfl
@[simp] theorem lookup_previous_6_8 : previousPadding literalP (3, 0) (4, 0) = (-117626947 / 2500000000) := rfl
@[simp] theorem lookup_current_6_8 : currentPadding literalP (3, 0) (4, 0) = (-429691883 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_9 : literalDescent (3, 0) (4, 1) = (-3019286743 / 500000000000) := rfl
@[simp] theorem lookup_previous_6_9 : previousPadding literalP (3, 0) (4, 1) = (-340568531 / 10000000000) := rfl
@[simp] theorem lookup_current_6_9 : currentPadding literalP (3, 0) (4, 1) = (-289857289 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_10 : literalDescent (3, 0) (5, 0) = (-178658711 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_10 : previousPadding literalP (3, 0) (5, 0) = (-832050281 / 10000000000) := rfl
@[simp] theorem lookup_current_6_10 : currentPadding literalP (3, 0) (5, 0) = (-65339157 / 1000000000) := rfl
@[simp] theorem lookup_descent_6_11 : literalDescent (3, 0) (5, 1) = (765337191 / 125000000000) := rfl
@[simp] theorem lookup_previous_6_11 : previousPadding literalP (3, 0) (5, 1) = (8806944657 / 250000000000) := rfl
@[simp] theorem lookup_current_6_11 : currentPadding literalP (3, 0) (5, 1) = (291050811 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_12 : literalDescent (3, 0) (6, 0) = (13100263 / 1250000000) := rfl
@[simp] theorem lookup_previous_6_12 : previousPadding literalP (3, 0) (6, 0) = (79739821 / 2500000000) := rfl
@[simp] theorem lookup_current_6_12 : currentPadding literalP (3, 0) (6, 0) = (10707859 / 500000000) := rfl
@[simp] theorem lookup_descent_6_13 : literalDescent (3, 0) (6, 1) = (6434287 / 2000000000) := rfl
@[simp] theorem lookup_previous_6_13 : previousPadding literalP (3, 0) (6, 1) = (50024319 / 10000000000) := rfl
@[simp] theorem lookup_current_6_13 : currentPadding literalP (3, 0) (6, 1) = (4463221 / 2500000000) := rfl
@[simp] theorem lookup_descent_6_14 : literalDescent (3, 0) (7, 0) = (-28273383 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_14 : previousPadding literalP (3, 0) (7, 0) = (18653667 / 5000000000) := rfl
@[simp] theorem lookup_current_6_14 : currentPadding literalP (3, 0) (7, 0) = (65580717 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_15 : literalDescent (3, 0) (7, 1) = (-10666967 / 2500000000) := rfl
@[simp] theorem lookup_previous_6_15 : previousPadding literalP (3, 0) (7, 1) = (-133917921 / 10000000000) := rfl
@[simp] theorem lookup_current_6_15 : currentPadding literalP (3, 0) (7, 1) = (-91250053 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_16 : literalDescent (3, 0) (8, 0) = (-7402427 / 2000000000) := rfl
@[simp] theorem lookup_previous_6_16 : previousPadding literalP (3, 0) (8, 0) = (-17385889 / 2500000000) := rfl
@[simp] theorem lookup_current_6_16 : currentPadding literalP (3, 0) (8, 0) = (-32531421 / 10000000000) := rfl
@[simp] theorem lookup_descent_6_17 : literalDescent (3, 0) (8, 1) = (-585841 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_17 : previousPadding literalP (3, 0) (8, 1) = (8398597 / 5000000000) := rfl
@[simp] theorem lookup_current_6_17 : currentPadding literalP (3, 0) (8, 1) = (3476607 / 2000000000) := rfl
@[simp] theorem lookup_descent_6_18 : literalDescent (3, 0) (9, 0) = (45443657 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_18 : previousPadding literalP (3, 0) (9, 0) = (45443657 / 10000000000) := rfl
@[simp] theorem lookup_current_6_18 : currentPadding literalP (3, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_6_19 : literalDescent (3, 0) (9, 1) = (1483349 / 10000000000) := rfl
@[simp] theorem lookup_previous_6_19 : previousPadding literalP (3, 0) (9, 1) = (1483349 / 10000000000) := rfl
@[simp] theorem lookup_current_6_19 : currentPadding literalP (3, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_7_0 : literalDescent (3, 1) (0, 0) = (-43226931 / 125000000000) := rfl
@[simp] theorem lookup_previous_7_0 : previousPadding literalP (3, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_7_0 : currentPadding literalP (3, 1) (0, 0) = (19307473 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_1 : literalDescent (3, 1) (0, 1) = (648763 / 6250000000) := rfl
@[simp] theorem lookup_previous_7_1 : previousPadding literalP (3, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_7_1 : currentPadding literalP (3, 1) (0, 1) = (3702519 / 2500000000) := rfl
@[simp] theorem lookup_descent_7_2 : literalDescent (3, 1) (1, 0) = (159545357 / 100000000000) := rfl
@[simp] theorem lookup_previous_7_2 : previousPadding literalP (3, 1) (1, 0) = (6045207623 / 62500000000) := rfl
@[simp] theorem lookup_current_7_2 : currentPadding literalP (3, 1) (1, 0) = (9453001937 / 250000000000) := rfl
@[simp] theorem lookup_descent_7_3 : literalDescent (3, 1) (1, 1) = (-107988129 / 500000000000) := rfl
@[simp] theorem lookup_previous_7_3 : previousPadding literalP (3, 1) (1, 1) = (-277893391 / 2500000000) := rfl
@[simp] theorem lookup_current_7_3 : currentPadding literalP (3, 1) (1, 1) = (-23861859 / 5000000000) := rfl
@[simp] theorem lookup_descent_7_4 : literalDescent (3, 1) (2, 0) = (-702782463 / 250000000000) := rfl
@[simp] theorem lookup_previous_7_4 : previousPadding literalP (3, 1) (2, 0) = (-151837731 / 5000000000) := rfl
@[simp] theorem lookup_current_7_4 : currentPadding literalP (3, 1) (2, 0) = (-340568531 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_5 : literalDescent (3, 1) (2, 1) = (-58363269 / 50000000000) := rfl
@[simp] theorem lookup_previous_7_5 : previousPadding literalP (3, 1) (2, 1) = (-1136377 / 400000000) := rfl
@[simp] theorem lookup_current_7_5 : currentPadding literalP (3, 1) (2, 1) = (-16348187 / 2000000000) := rfl
@[simp] theorem lookup_descent_7_6 : literalDescent (3, 1) (3, 0) = (2093391891 / 500000000000) := rfl
@[simp] theorem lookup_previous_7_6 : previousPadding literalP (3, 1) (3, 0) = (-32780792409 / 500000000000) := rfl
@[simp] theorem lookup_current_7_6 : currentPadding literalP (3, 1) (3, 0) = (2721639 / 5000000000) := rfl
@[simp] theorem lookup_descent_7_7 : literalDescent (3, 1) (3, 1) = (133748533 / 50000000000) := rfl
@[simp] theorem lookup_previous_7_7 : previousPadding literalP (3, 1) (3, 1) = (1866477813 / 15625000000) := rfl
@[simp] theorem lookup_current_7_7 : currentPadding literalP (3, 1) (3, 1) = (2347676927 / 62500000000) := rfl
@[simp] theorem lookup_descent_7_8 : literalDescent (3, 1) (4, 0) = (-1926601 / 800000000) := rfl
@[simp] theorem lookup_previous_7_8 : previousPadding literalP (3, 1) (4, 0) = (14023817 / 10000000000) := rfl
@[simp] theorem lookup_current_7_8 : currentPadding literalP (3, 1) (4, 0) = (-42506979 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_9 : literalDescent (3, 1) (4, 1) = (-604039451 / 500000000000) := rfl
@[simp] theorem lookup_previous_7_9 : previousPadding literalP (3, 1) (4, 1) = (-16348187 / 2000000000) := rfl
@[simp] theorem lookup_current_7_9 : currentPadding literalP (3, 1) (4, 1) = (-79333743 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_10 : literalDescent (3, 1) (5, 0) = (-22203633 / 5000000000) := rfl
@[simp] theorem lookup_previous_7_10 : previousPadding literalP (3, 1) (5, 0) = (-106991307 / 5000000000) := rfl
@[simp] theorem lookup_current_7_10 : currentPadding literalP (3, 1) (5, 0) = (-42393837 / 2500000000) := rfl
@[simp] theorem lookup_descent_7_11 : literalDescent (3, 1) (5, 1) = (-1457131 / 2500000000) := rfl
@[simp] theorem lookup_previous_7_11 : previousPadding literalP (3, 1) (5, 1) = (-2818967 / 625000000) := rfl
@[simp] theorem lookup_current_7_11 : currentPadding literalP (3, 1) (5, 1) = (-9818737 / 2500000000) := rfl
@[simp] theorem lookup_descent_7_12 : literalDescent (3, 1) (6, 0) = (3199557549 / 500000000000) := rfl
@[simp] theorem lookup_previous_7_12 : previousPadding literalP (3, 1) (6, 0) = (82090027 / 4000000000) := rfl
@[simp] theorem lookup_current_7_12 : currentPadding literalP (3, 1) (6, 0) = (3530847913 / 250000000000) := rfl
@[simp] theorem lookup_descent_7_13 : literalDescent (3, 1) (6, 1) = (4624379 / 5000000000) := rfl
@[simp] theorem lookup_previous_7_13 : previousPadding literalP (3, 1) (6, 1) = (24631061 / 10000000000) := rfl
@[simp] theorem lookup_current_7_13 : currentPadding literalP (3, 1) (6, 1) = (15382303 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_14 : literalDescent (3, 1) (7, 0) = (-3718079 / 2000000000) := rfl
@[simp] theorem lookup_previous_7_14 : previousPadding literalP (3, 1) (7, 0) = (14987849 / 10000000000) := rfl
@[simp] theorem lookup_current_7_14 : currentPadding literalP (3, 1) (7, 0) = (8394561 / 2500000000) := rfl
@[simp] theorem lookup_descent_7_15 : literalDescent (3, 1) (7, 1) = (-7042983 / 5000000000) := rfl
@[simp] theorem lookup_previous_7_15 : previousPadding literalP (3, 1) (7, 1) = (-6752687 / 2000000000) := rfl
@[simp] theorem lookup_current_7_15 : currentPadding literalP (3, 1) (7, 1) = (-19677469 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_16 : literalDescent (3, 1) (8, 0) = (-3848379 / 5000000000) := rfl
@[simp] theorem lookup_previous_7_16 : previousPadding literalP (3, 1) (8, 0) = (-32728889 / 10000000000) := rfl
@[simp] theorem lookup_current_7_16 : currentPadding literalP (3, 1) (8, 0) = (-25032131 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_17 : literalDescent (3, 1) (8, 1) = (13314091 / 10000000000) := rfl
@[simp] theorem lookup_previous_7_17 : previousPadding literalP (3, 1) (8, 1) = (66993 / 25000000) := rfl
@[simp] theorem lookup_current_7_17 : currentPadding literalP (3, 1) (8, 1) = (13483109 / 10000000000) := rfl
@[simp] theorem lookup_descent_7_18 : literalDescent (3, 1) (9, 0) = (226643 / 500000000) := rfl
@[simp] theorem lookup_previous_7_18 : previousPadding literalP (3, 1) (9, 0) = (226643 / 500000000) := rfl
@[simp] theorem lookup_current_7_18 : currentPadding literalP (3, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_7_19 : literalDescent (3, 1) (9, 1) = (-4522881 / 10000000000) := rfl
@[simp] theorem lookup_previous_7_19 : previousPadding literalP (3, 1) (9, 1) = (-4522881 / 10000000000) := rfl
@[simp] theorem lookup_current_7_19 : currentPadding literalP (3, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_8_0 : literalDescent (4, 0) (0, 0) = (-33976901 / 20000000000) := rfl
@[simp] theorem lookup_previous_8_0 : previousPadding literalP (4, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_8_0 : currentPadding literalP (4, 0) (0, 0) = (12481049 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_1 : literalDescent (4, 0) (0, 1) = (-3322053 / 4000000000) := rfl
@[simp] theorem lookup_previous_8_1 : previousPadding literalP (4, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_8_1 : currentPadding literalP (4, 0) (0, 1) = (3797843 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_2 : literalDescent (4, 0) (1, 0) = (17758527 / 2000000000) := rfl
@[simp] theorem lookup_previous_8_2 : previousPadding literalP (4, 0) (1, 0) = (25388829 / 625000000) := rfl
@[simp] theorem lookup_current_8_2 : currentPadding literalP (4, 0) (1, 0) = (97056499 / 2500000000) := rfl
@[simp] theorem lookup_descent_8_3 : literalDescent (4, 0) (1, 1) = (450105987 / 100000000000) := rfl
@[simp] theorem lookup_previous_8_3 : previousPadding literalP (4, 0) (1, 1) = (4241927917 / 100000000000) := rfl
@[simp] theorem lookup_current_8_3 : currentPadding literalP (4, 0) (1, 1) = (2505906431 / 100000000000) := rfl
@[simp] theorem lookup_descent_8_4 : literalDescent (4, 0) (2, 0) = (-136222327 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_4 : previousPadding literalP (4, 0) (2, 0) = (-30258519 / 312500000) := rfl
@[simp] theorem lookup_current_8_4 : currentPadding literalP (4, 0) (2, 0) = (-832050281 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_5 : literalDescent (4, 0) (2, 1) = (-8177543 / 2000000000) := rfl
@[simp] theorem lookup_previous_8_5 : previousPadding literalP (4, 0) (2, 1) = (-254870329 / 10000000000) := rfl
@[simp] theorem lookup_current_8_5 : currentPadding literalP (4, 0) (2, 1) = (-106991307 / 5000000000) := rfl
@[simp] theorem lookup_descent_8_6 : literalDescent (4, 0) (3, 0) = (-242858427 / 20000000000) := rfl
@[simp] theorem lookup_previous_8_6 : previousPadding literalP (4, 0) (3, 0) = (-117626947 / 2500000000) := rfl
@[simp] theorem lookup_current_8_6 : currentPadding literalP (4, 0) (3, 0) = (-429691883 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_7 : literalDescent (4, 0) (3, 1) = (-1926601 / 800000000) := rfl
@[simp] theorem lookup_previous_8_7 : previousPadding literalP (4, 0) (3, 1) = (14023817 / 10000000000) := rfl
@[simp] theorem lookup_current_8_7 : currentPadding literalP (4, 0) (3, 1) = (-42506979 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_8 : literalDescent (4, 0) (4, 0) = (3019013 / 78125000) := rfl
@[simp] theorem lookup_previous_8_8 : previousPadding literalP (4, 0) (4, 0) = (1868436109 / 10000000000) := rfl
@[simp] theorem lookup_current_8_8 : currentPadding literalP (4, 0) (4, 0) = (1510649131 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_9 : literalDescent (4, 0) (4, 1) = (108593857 / 20000000000) := rfl
@[simp] theorem lookup_previous_8_9 : previousPadding literalP (4, 0) (4, 1) = (2721639 / 5000000000) := rfl
@[simp] theorem lookup_current_8_9 : currentPadding literalP (4, 0) (4, 1) = (60406111 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_10 : literalDescent (4, 0) (5, 0) = (-57884603 / 5000000000) := rfl
@[simp] theorem lookup_previous_8_10 : previousPadding literalP (4, 0) (5, 0) = (-429691883 / 10000000000) := rfl
@[simp] theorem lookup_current_8_10 : currentPadding literalP (4, 0) (5, 0) = (-16412301 / 500000000) := rfl
@[simp] theorem lookup_descent_8_11 : literalDescent (4, 0) (5, 1) = (-342907911 / 50000000000) := rfl
@[simp] theorem lookup_previous_8_11 : previousPadding literalP (4, 0) (5, 1) = (-289857289 / 10000000000) := rfl
@[simp] theorem lookup_current_8_11 : currentPadding literalP (4, 0) (5, 1) = (-222994713 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_12 : literalDescent (4, 0) (6, 0) = (-26912739 / 1250000000) := rfl
@[simp] theorem lookup_previous_8_12 : previousPadding literalP (4, 0) (6, 0) = (-65339157 / 1000000000) := rfl
@[simp] theorem lookup_current_8_12 : currentPadding literalP (4, 0) (6, 0) = (-219044829 / 5000000000) := rfl
@[simp] theorem lookup_descent_8_13 : literalDescent (4, 0) (6, 1) = (10269589 / 2000000000) := rfl
@[simp] theorem lookup_previous_8_13 : previousPadding literalP (4, 0) (6, 1) = (291050811 / 10000000000) := rfl
@[simp] theorem lookup_current_8_13 : currentPadding literalP (4, 0) (6, 1) = (119851433 / 5000000000) := rfl
@[simp] theorem lookup_descent_8_14 : literalDescent (4, 0) (7, 0) = (138546279 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_14 : previousPadding literalP (4, 0) (7, 0) = (10707859 / 500000000) := rfl
@[simp] theorem lookup_current_8_14 : currentPadding literalP (4, 0) (7, 0) = (75610901 / 10000000000) := rfl
@[simp] theorem lookup_descent_8_15 : literalDescent (4, 0) (7, 1) = (10219941 / 5000000000) := rfl
@[simp] theorem lookup_previous_8_15 : previousPadding literalP (4, 0) (7, 1) = (4463221 / 2500000000) := rfl
@[simp] theorem lookup_current_8_15 : currentPadding literalP (4, 0) (7, 1) = (-1293499 / 5000000000) := rfl
@[simp] theorem lookup_descent_8_16 : literalDescent (4, 0) (8, 0) = (382343 / 156250000) := rfl
@[simp] theorem lookup_previous_8_16 : previousPadding literalP (4, 0) (8, 0) = (65580717 / 10000000000) := rfl
@[simp] theorem lookup_current_8_16 : currentPadding literalP (4, 0) (8, 0) = (8222153 / 2000000000) := rfl
@[simp] theorem lookup_descent_8_17 : literalDescent (4, 0) (8, 1) = (-46621447 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_17 : previousPadding literalP (4, 0) (8, 1) = (-91250053 / 10000000000) := rfl
@[simp] theorem lookup_current_8_17 : currentPadding literalP (4, 0) (8, 1) = (-22314303 / 5000000000) := rfl
@[simp] theorem lookup_descent_8_18 : literalDescent (4, 0) (9, 0) = (-32531421 / 10000000000) := rfl
@[simp] theorem lookup_previous_8_18 : previousPadding literalP (4, 0) (9, 0) = (-32531421 / 10000000000) := rfl
@[simp] theorem lookup_current_8_18 : currentPadding literalP (4, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_8_19 : literalDescent (4, 0) (9, 1) = (3476607 / 2000000000) := rfl
@[simp] theorem lookup_previous_8_19 : previousPadding literalP (4, 0) (9, 1) = (3476607 / 2000000000) := rfl
@[simp] theorem lookup_current_8_19 : currentPadding literalP (4, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_9_0 : literalDescent (4, 1) (0, 0) = (-563461407 / 500000000000) := rfl
@[simp] theorem lookup_previous_9_0 : previousPadding literalP (4, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_9_0 : currentPadding literalP (4, 1) (0, 0) = (-28958009 / 2000000000) := rfl
@[simp] theorem lookup_descent_9_1 : literalDescent (4, 1) (0, 1) = (-323074399 / 500000000000) := rfl
@[simp] theorem lookup_previous_9_1 : previousPadding literalP (4, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_9_1 : currentPadding literalP (4, 1) (0, 1) = (-74799457 / 5000000000) := rfl
@[simp] theorem lookup_descent_9_2 : literalDescent (4, 1) (1, 0) = (43019893 / 20000000000) := rfl
@[simp] theorem lookup_previous_9_2 : previousPadding literalP (4, 1) (1, 0) = (19307473 / 10000000000) := rfl
@[simp] theorem lookup_current_9_2 : currentPadding literalP (4, 1) (1, 0) = (34297437 / 5000000000) := rfl
@[simp] theorem lookup_descent_9_3 : literalDescent (4, 1) (1, 1) = (83743121 / 125000000000) := rfl
@[simp] theorem lookup_previous_9_3 : previousPadding literalP (4, 1) (1, 1) = (3702519 / 2500000000) := rfl
@[simp] theorem lookup_current_9_3 : currentPadding literalP (4, 1) (1, 1) = (6214403 / 2000000000) := rfl
@[simp] theorem lookup_descent_9_4 : literalDescent (4, 1) (2, 0) = (2018929 / 781250000) := rfl
@[simp] theorem lookup_previous_9_4 : previousPadding literalP (4, 1) (2, 0) = (9453001937 / 250000000000) := rfl
@[simp] theorem lookup_current_9_4 : currentPadding literalP (4, 1) (2, 0) = (8806944657 / 250000000000) := rfl
@[simp] theorem lookup_descent_9_5 : literalDescent (4, 1) (2, 1) = (-1310123 / 5000000000) := rfl
@[simp] theorem lookup_previous_9_5 : previousPadding literalP (4, 1) (2, 1) = (-23861859 / 5000000000) := rfl
@[simp] theorem lookup_current_9_5 : currentPadding literalP (4, 1) (2, 1) = (-2818967 / 625000000) := rfl
@[simp] theorem lookup_descent_9_6 : literalDescent (4, 1) (3, 0) = (-3019286743 / 500000000000) := rfl
@[simp] theorem lookup_previous_9_6 : previousPadding literalP (4, 1) (3, 0) = (-340568531 / 10000000000) := rfl
@[simp] theorem lookup_current_9_6 : currentPadding literalP (4, 1) (3, 0) = (-289857289 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_7 : literalDescent (4, 1) (3, 1) = (-604039451 / 500000000000) := rfl
@[simp] theorem lookup_previous_9_7 : previousPadding literalP (4, 1) (3, 1) = (-16348187 / 2000000000) := rfl
@[simp] theorem lookup_current_9_7 : currentPadding literalP (4, 1) (3, 1) = (-79333743 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_8 : literalDescent (4, 1) (4, 0) = (108593857 / 20000000000) := rfl
@[simp] theorem lookup_previous_9_8 : previousPadding literalP (4, 1) (4, 0) = (2721639 / 5000000000) := rfl
@[simp] theorem lookup_current_9_8 : currentPadding literalP (4, 1) (4, 0) = (60406111 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_9 : literalDescent (4, 1) (4, 1) = (1004168187 / 250000000000) := rfl
@[simp] theorem lookup_previous_9_9 : previousPadding literalP (4, 1) (4, 1) = (2347676927 / 62500000000) := rfl
@[simp] theorem lookup_current_9_9 : currentPadding literalP (4, 1) (4, 1) = (5555721097 / 250000000000) := rfl
@[simp] theorem lookup_descent_9_10 : literalDescent (4, 1) (5, 0) = (-36399933 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_10 : previousPadding literalP (4, 1) (5, 0) = (-42506979 / 10000000000) := rfl
@[simp] theorem lookup_current_9_10 : currentPadding literalP (4, 1) (5, 0) = (-20430389 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_11 : literalDescent (4, 1) (5, 1) = (-207002127 / 125000000000) := rfl
@[simp] theorem lookup_previous_9_11 : previousPadding literalP (4, 1) (5, 1) = (-79333743 / 10000000000) := rfl
@[simp] theorem lookup_current_9_11 : currentPadding literalP (4, 1) (5, 1) = (-32246187 / 5000000000) := rfl
@[simp] theorem lookup_descent_9_12 : literalDescent (4, 1) (6, 0) = (-3520769 / 500000000) := rfl
@[simp] theorem lookup_previous_9_12 : previousPadding literalP (4, 1) (6, 0) = (-42393837 / 2500000000) := rfl
@[simp] theorem lookup_current_9_12 : currentPadding literalP (4, 1) (6, 0) = (-3098749 / 312500000) := rfl
@[simp] theorem lookup_descent_9_13 : literalDescent (4, 1) (6, 1) = (-5853459 / 5000000000) := rfl
@[simp] theorem lookup_previous_9_13 : previousPadding literalP (4, 1) (6, 1) = (-9818737 / 2500000000) := rfl
@[simp] theorem lookup_current_9_13 : currentPadding literalP (4, 1) (6, 1) = (-2756803 / 1000000000) := rfl
@[simp] theorem lookup_descent_9_14 : literalDescent (4, 1) (7, 0) = (235636977 / 25000000000) := rfl
@[simp] theorem lookup_previous_9_14 : previousPadding literalP (4, 1) (7, 0) = (3530847913 / 250000000000) := rfl
@[simp] theorem lookup_current_9_14 : currentPadding literalP (4, 1) (7, 0) = (1174478143 / 250000000000) := rfl
@[simp] theorem lookup_descent_9_15 : literalDescent (4, 1) (7, 1) = (6819061 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_15 : previousPadding literalP (4, 1) (7, 1) = (15382303 / 10000000000) := rfl
@[simp] theorem lookup_current_9_15 : currentPadding literalP (4, 1) (7, 1) = (4281621 / 5000000000) := rfl
@[simp] theorem lookup_descent_9_16 : literalDescent (4, 1) (8, 0) = (151969 / 200000000) := rfl
@[simp] theorem lookup_previous_9_16 : previousPadding literalP (4, 1) (8, 0) = (8394561 / 2500000000) := rfl
@[simp] theorem lookup_current_9_16 : currentPadding literalP (4, 1) (8, 0) = (12989897 / 5000000000) := rfl
@[simp] theorem lookup_descent_9_17 : literalDescent (4, 1) (8, 1) = (-1108671 / 625000000) := rfl
@[simp] theorem lookup_previous_9_17 : previousPadding literalP (4, 1) (8, 1) = (-19677469 / 10000000000) := rfl
@[simp] theorem lookup_current_9_17 : currentPadding literalP (4, 1) (8, 1) = (-1938733 / 10000000000) := rfl
@[simp] theorem lookup_descent_9_18 : literalDescent (4, 1) (9, 0) = (-25032131 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_18 : previousPadding literalP (4, 1) (9, 0) = (-25032131 / 10000000000) := rfl
@[simp] theorem lookup_current_9_18 : currentPadding literalP (4, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_9_19 : literalDescent (4, 1) (9, 1) = (13483109 / 10000000000) := rfl
@[simp] theorem lookup_previous_9_19 : previousPadding literalP (4, 1) (9, 1) = (13483109 / 10000000000) := rfl
@[simp] theorem lookup_current_9_19 : currentPadding literalP (4, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_10_0 : literalDescent (5, 0) (0, 0) = (-127963 / 10000000000) := rfl
@[simp] theorem lookup_previous_10_0 : previousPadding literalP (5, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_10_0 : currentPadding literalP (5, 0) (0, 0) = (1537679 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_1 : literalDescent (5, 0) (0, 1) = (-1665311 / 20000000000) := rfl
@[simp] theorem lookup_previous_10_1 : previousPadding literalP (5, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_10_1 : currentPadding literalP (5, 0) (0, 1) = (2242437 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_2 : literalDescent (5, 0) (1, 0) = (-828373 / 4000000000) := rfl
@[simp] theorem lookup_previous_10_2 : previousPadding literalP (5, 0) (1, 0) = (12481049 / 10000000000) := rfl
@[simp] theorem lookup_current_10_2 : currentPadding literalP (5, 0) (1, 0) = (2910403 / 2000000000) := rfl
@[simp] theorem lookup_descent_10_3 : literalDescent (5, 0) (1, 1) = (65638183 / 500000000000) := rfl
@[simp] theorem lookup_previous_10_3 : previousPadding literalP (5, 0) (1, 1) = (3797843 / 10000000000) := rfl
@[simp] theorem lookup_current_10_3 : currentPadding literalP (5, 0) (1, 1) = (537679 / 5000000000) := rfl
@[simp] theorem lookup_descent_10_4 : literalDescent (5, 0) (2, 0) = (8658339 / 1250000000) := rfl
@[simp] theorem lookup_previous_10_4 : previousPadding literalP (5, 0) (2, 0) = (97056499 / 2500000000) := rfl
@[simp] theorem lookup_current_10_4 : currentPadding literalP (5, 0) (2, 0) = (79739821 / 2500000000) := rfl
@[simp] theorem lookup_descent_10_5 : literalDescent (5, 0) (2, 1) = (113413939 / 25000000000) := rfl
@[simp] theorem lookup_previous_10_5 : previousPadding literalP (5, 0) (2, 1) = (2505906431 / 100000000000) := rfl
@[simp] theorem lookup_current_10_5 : currentPadding literalP (5, 0) (2, 1) = (82090027 / 4000000000) := rfl
@[simp] theorem lookup_descent_10_6 : literalDescent (5, 0) (3, 0) = (-178658711 / 10000000000) := rfl
@[simp] theorem lookup_previous_10_6 : previousPadding literalP (5, 0) (3, 0) = (-832050281 / 10000000000) := rfl
@[simp] theorem lookup_current_10_6 : currentPadding literalP (5, 0) (3, 0) = (-65339157 / 1000000000) := rfl
@[simp] theorem lookup_descent_10_7 : literalDescent (5, 0) (3, 1) = (-22203633 / 5000000000) := rfl
@[simp] theorem lookup_previous_10_7 : previousPadding literalP (5, 0) (3, 1) = (-106991307 / 5000000000) := rfl
@[simp] theorem lookup_current_10_7 : currentPadding literalP (5, 0) (3, 1) = (-42393837 / 2500000000) := rfl
@[simp] theorem lookup_descent_10_8 : literalDescent (5, 0) (4, 0) = (-57884603 / 5000000000) := rfl
@[simp] theorem lookup_previous_10_8 : previousPadding literalP (5, 0) (4, 0) = (-429691883 / 10000000000) := rfl
@[simp] theorem lookup_current_10_8 : currentPadding literalP (5, 0) (4, 0) = (-16412301 / 500000000) := rfl
@[simp] theorem lookup_descent_10_9 : literalDescent (5, 0) (4, 1) = (-36399933 / 10000000000) := rfl
@[simp] theorem lookup_previous_10_9 : previousPadding literalP (5, 0) (4, 1) = (-42506979 / 10000000000) := rfl
@[simp] theorem lookup_current_10_9 : currentPadding literalP (5, 0) (4, 1) = (-20430389 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_10 : literalDescent (5, 0) (5, 0) = (442781683 / 10000000000) := rfl
@[simp] theorem lookup_previous_10_10 : previousPadding literalP (5, 0) (5, 0) = (1510649131 / 10000000000) := rfl
@[simp] theorem lookup_current_10_10 : currentPadding literalP (5, 0) (5, 0) = (218738927 / 2000000000) := rfl
@[simp] theorem lookup_descent_10_11 : literalDescent (5, 0) (5, 1) = (68115403 / 20000000000) := rfl
@[simp] theorem lookup_previous_10_11 : previousPadding literalP (5, 0) (5, 1) = (60406111 / 10000000000) := rfl
@[simp] theorem lookup_current_10_11 : currentPadding literalP (5, 0) (5, 1) = (66493119 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_12 : literalDescent (5, 0) (6, 0) = (-63730673 / 20000000000) := rfl
@[simp] theorem lookup_previous_10_12 : previousPadding literalP (5, 0) (6, 0) = (-16412301 / 500000000) := rfl
@[simp] theorem lookup_current_10_12 : currentPadding literalP (5, 0) (6, 0) = (-309294277 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_13 : literalDescent (5, 0) (6, 1) = (-3011174513 / 500000000000) := rfl
@[simp] theorem lookup_previous_10_13 : previousPadding literalP (5, 0) (6, 1) = (-222994713 / 10000000000) := rfl
@[simp] theorem lookup_current_10_13 : currentPadding literalP (5, 0) (6, 1) = (-20540747 / 1250000000) := rfl
@[simp] theorem lookup_descent_10_14 : literalDescent (5, 0) (7, 0) = (-16696171 / 625000000) := rfl
@[simp] theorem lookup_previous_10_14 : previousPadding literalP (5, 0) (7, 0) = (-219044829 / 5000000000) := rfl
@[simp] theorem lookup_current_10_14 : currentPadding literalP (5, 0) (7, 0) = (-85475461 / 5000000000) := rfl
@[simp] theorem lookup_descent_10_15 : literalDescent (5, 0) (7, 1) = (13341241 / 2000000000) := rfl
@[simp] theorem lookup_previous_10_15 : previousPadding literalP (5, 0) (7, 1) = (119851433 / 5000000000) := rfl
@[simp] theorem lookup_current_10_15 : currentPadding literalP (5, 0) (7, 1) = (172996661 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_16 : literalDescent (5, 0) (8, 0) = (1698869 / 400000000) := rfl
@[simp] theorem lookup_previous_10_16 : previousPadding literalP (5, 0) (8, 0) = (75610901 / 10000000000) := rfl
@[simp] theorem lookup_current_10_16 : currentPadding literalP (5, 0) (8, 0) = (4142397 / 1250000000) := rfl
@[simp] theorem lookup_descent_10_17 : literalDescent (5, 0) (8, 1) = (7809941 / 2000000000) := rfl
@[simp] theorem lookup_previous_10_17 : previousPadding literalP (5, 0) (8, 1) = (-1293499 / 5000000000) := rfl
@[simp] theorem lookup_current_10_17 : currentPadding literalP (5, 0) (8, 1) = (-41636703 / 10000000000) := rfl
@[simp] theorem lookup_descent_10_18 : literalDescent (5, 0) (9, 0) = (8222153 / 2000000000) := rfl
@[simp] theorem lookup_previous_10_18 : previousPadding literalP (5, 0) (9, 0) = (8222153 / 2000000000) := rfl
@[simp] theorem lookup_current_10_18 : currentPadding literalP (5, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_10_19 : literalDescent (5, 0) (9, 1) = (-22314303 / 5000000000) := rfl
@[simp] theorem lookup_previous_10_19 : previousPadding literalP (5, 0) (9, 1) = (-22314303 / 5000000000) := rfl
@[simp] theorem lookup_current_10_19 : currentPadding literalP (5, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_11_0 : literalDescent (5, 1) (0, 0) = (147305437 / 100000000000) := rfl
@[simp] theorem lookup_previous_11_0 : previousPadding literalP (5, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_11_0 : currentPadding literalP (5, 1) (0, 0) = (763867 / 250000000) := rfl
@[simp] theorem lookup_descent_11_1 : literalDescent (5, 1) (0, 1) = (177831779 / 250000000000) := rfl
@[simp] theorem lookup_previous_11_1 : previousPadding literalP (5, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_11_1 : currentPadding literalP (5, 1) (0, 1) = (38165927 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_2 : literalDescent (5, 1) (1, 0) = (-82800703 / 20000000000) := rfl
@[simp] theorem lookup_previous_11_2 : previousPadding literalP (5, 1) (1, 0) = (-28958009 / 2000000000) := rfl
@[simp] theorem lookup_current_11_2 : currentPadding literalP (5, 1) (1, 0) = (-174187027 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_3 : literalDescent (5, 1) (1, 1) = (-704582059 / 500000000000) := rfl
@[simp] theorem lookup_previous_11_3 : previousPadding literalP (5, 1) (1, 1) = (-74799457 / 5000000000) := rfl
@[simp] theorem lookup_current_11_3 : currentPadding literalP (5, 1) (1, 1) = (-11921871 / 2500000000) := rfl
@[simp] theorem lookup_descent_11_4 : literalDescent (5, 1) (2, 0) = (3714111 / 2000000000) := rfl
@[simp] theorem lookup_previous_11_4 : previousPadding literalP (5, 1) (2, 0) = (34297437 / 5000000000) := rfl
@[simp] theorem lookup_current_11_4 : currentPadding literalP (5, 1) (2, 0) = (50024319 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_5 : literalDescent (5, 1) (2, 1) = (3220477 / 5000000000) := rfl
@[simp] theorem lookup_previous_11_5 : previousPadding literalP (5, 1) (2, 1) = (6214403 / 2000000000) := rfl
@[simp] theorem lookup_current_11_5 : currentPadding literalP (5, 1) (2, 1) = (24631061 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_6 : literalDescent (5, 1) (3, 0) = (765337191 / 125000000000) := rfl
@[simp] theorem lookup_previous_11_6 : previousPadding literalP (5, 1) (3, 0) = (8806944657 / 250000000000) := rfl
@[simp] theorem lookup_current_11_6 : currentPadding literalP (5, 1) (3, 0) = (291050811 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_7 : literalDescent (5, 1) (3, 1) = (-1457131 / 2500000000) := rfl
@[simp] theorem lookup_previous_11_7 : previousPadding literalP (5, 1) (3, 1) = (-2818967 / 625000000) := rfl
@[simp] theorem lookup_current_11_7 : currentPadding literalP (5, 1) (3, 1) = (-9818737 / 2500000000) := rfl
@[simp] theorem lookup_descent_11_8 : literalDescent (5, 1) (4, 0) = (-342907911 / 50000000000) := rfl
@[simp] theorem lookup_previous_11_8 : previousPadding literalP (5, 1) (4, 0) = (-289857289 / 10000000000) := rfl
@[simp] theorem lookup_current_11_8 : currentPadding literalP (5, 1) (4, 0) = (-222994713 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_9 : literalDescent (5, 1) (4, 1) = (-207002127 / 125000000000) := rfl
@[simp] theorem lookup_previous_11_9 : previousPadding literalP (5, 1) (4, 1) = (-79333743 / 10000000000) := rfl
@[simp] theorem lookup_current_11_9 : currentPadding literalP (5, 1) (4, 1) = (-32246187 / 5000000000) := rfl
@[simp] theorem lookup_descent_11_10 : literalDescent (5, 1) (5, 0) = (68115403 / 20000000000) := rfl
@[simp] theorem lookup_previous_11_10 : previousPadding literalP (5, 1) (5, 0) = (60406111 / 10000000000) := rfl
@[simp] theorem lookup_current_11_10 : currentPadding literalP (5, 1) (5, 0) = (66493119 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_11 : literalDescent (5, 1) (5, 1) = (200426427 / 50000000000) := rfl
@[simp] theorem lookup_previous_11_11 : previousPadding literalP (5, 1) (5, 1) = (5555721097 / 250000000000) := rfl
@[simp] theorem lookup_current_11_11 : currentPadding literalP (5, 1) (5, 1) = (913808309 / 50000000000) := rfl
@[simp] theorem lookup_descent_11_12 : literalDescent (5, 1) (6, 0) = (8256277 / 20000000000) := rfl
@[simp] theorem lookup_previous_11_12 : previousPadding literalP (5, 1) (6, 0) = (-20430389 / 10000000000) := rfl
@[simp] theorem lookup_current_11_12 : currentPadding literalP (5, 1) (6, 0) = (-37472121 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_13 : literalDescent (5, 1) (6, 1) = (-323682311 / 500000000000) := rfl
@[simp] theorem lookup_previous_11_13 : previousPadding literalP (5, 1) (6, 1) = (-32246187 / 5000000000) := rfl
@[simp] theorem lookup_current_11_13 : currentPadding literalP (5, 1) (6, 1) = (-59568359 / 10000000000) := rfl
@[simp] theorem lookup_descent_11_14 : literalDescent (5, 1) (7, 0) = (-278759 / 50000000) := rfl
@[simp] theorem lookup_previous_11_14 : previousPadding literalP (5, 1) (7, 0) = (-3098749 / 312500000) := rfl
@[simp] theorem lookup_current_11_14 : currentPadding literalP (5, 1) (7, 0) = (-5426021 / 1250000000) := rfl
@[simp] theorem lookup_descent_11_15 : literalDescent (5, 1) (7, 1) = (-2709389 / 2500000000) := rfl
@[simp] theorem lookup_previous_11_15 : previousPadding literalP (5, 1) (7, 1) = (-2756803 / 1000000000) := rfl
@[simp] theorem lookup_current_11_15 : currentPadding literalP (5, 1) (7, 1) = (-8365237 / 5000000000) := rfl
@[simp] theorem lookup_descent_11_16 : literalDescent (5, 1) (8, 0) = (176000643 / 250000000000) := rfl
@[simp] theorem lookup_previous_11_16 : previousPadding literalP (5, 1) (8, 0) = (1174478143 / 250000000000) := rfl
@[simp] theorem lookup_current_11_16 : currentPadding literalP (5, 1) (8, 0) = (399391 / 100000000) := rfl
@[simp] theorem lookup_descent_11_17 : literalDescent (5, 1) (8, 1) = (52269 / 250000000) := rfl
@[simp] theorem lookup_previous_11_17 : previousPadding literalP (5, 1) (8, 1) = (4281621 / 5000000000) := rfl
@[simp] theorem lookup_current_11_17 : currentPadding literalP (5, 1) (8, 1) = (3236241 / 5000000000) := rfl
@[simp] theorem lookup_descent_11_18 : literalDescent (5, 1) (9, 0) = (12989897 / 5000000000) := rfl
@[simp] theorem lookup_previous_11_18 : previousPadding literalP (5, 1) (9, 0) = (12989897 / 5000000000) := rfl
@[simp] theorem lookup_current_11_18 : currentPadding literalP (5, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_11_19 : literalDescent (5, 1) (9, 1) = (-1938733 / 10000000000) := rfl
@[simp] theorem lookup_previous_11_19 : previousPadding literalP (5, 1) (9, 1) = (-1938733 / 10000000000) := rfl
@[simp] theorem lookup_current_11_19 : currentPadding literalP (5, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_12_0 : literalDescent (6, 0) (0, 0) = (-14550959 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_0 : previousPadding literalP (6, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_12_0 : currentPadding literalP (6, 0) (0, 0) = (1609743 / 1000000000) := rfl
@[simp] theorem lookup_descent_12_1 : literalDescent (6, 0) (0, 1) = (88741 / 20000000000) := rfl
@[simp] theorem lookup_previous_12_1 : previousPadding literalP (6, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_12_1 : currentPadding literalP (6, 0) (0, 1) = (187769 / 1250000000) := rfl
@[simp] theorem lookup_descent_12_2 : literalDescent (6, 0) (1, 0) = (291703 / 125000000) := rfl
@[simp] theorem lookup_previous_12_2 : previousPadding literalP (6, 0) (1, 0) = (1537679 / 10000000000) := rfl
@[simp] theorem lookup_current_12_2 : currentPadding literalP (6, 0) (1, 0) = (-5223779 / 5000000000) := rfl
@[simp] theorem lookup_descent_12_3 : literalDescent (6, 0) (1, 1) = (20583071 / 125000000000) := rfl
@[simp] theorem lookup_previous_12_3 : previousPadding literalP (6, 0) (1, 1) = (2242437 / 10000000000) := rfl
@[simp] theorem lookup_current_12_3 : currentPadding literalP (6, 0) (1, 1) = (-557263 / 250000000) := rfl
@[simp] theorem lookup_descent_12_4 : literalDescent (6, 0) (2, 0) = (-22755319 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_4 : previousPadding literalP (6, 0) (2, 0) = (2910403 / 2000000000) := rfl
@[simp] theorem lookup_current_12_4 : currentPadding literalP (6, 0) (2, 0) = (18653667 / 5000000000) := rfl
@[simp] theorem lookup_descent_12_5 : literalDescent (6, 0) (2, 1) = (-13912491 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_5 : previousPadding literalP (6, 0) (2, 1) = (537679 / 5000000000) := rfl
@[simp] theorem lookup_current_12_5 : currentPadding literalP (6, 0) (2, 1) = (14987849 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_6 : literalDescent (6, 0) (3, 0) = (13100263 / 1250000000) := rfl
@[simp] theorem lookup_previous_12_6 : previousPadding literalP (6, 0) (3, 0) = (79739821 / 2500000000) := rfl
@[simp] theorem lookup_current_12_6 : currentPadding literalP (6, 0) (3, 0) = (10707859 / 500000000) := rfl
@[simp] theorem lookup_descent_12_7 : literalDescent (6, 0) (3, 1) = (3199557549 / 500000000000) := rfl
@[simp] theorem lookup_previous_12_7 : previousPadding literalP (6, 0) (3, 1) = (82090027 / 4000000000) := rfl
@[simp] theorem lookup_current_12_7 : currentPadding literalP (6, 0) (3, 1) = (3530847913 / 250000000000) := rfl
@[simp] theorem lookup_descent_12_8 : literalDescent (6, 0) (4, 0) = (-26912739 / 1250000000) := rfl
@[simp] theorem lookup_previous_12_8 : previousPadding literalP (6, 0) (4, 0) = (-65339157 / 1000000000) := rfl
@[simp] theorem lookup_current_12_8 : currentPadding literalP (6, 0) (4, 0) = (-219044829 / 5000000000) := rfl
@[simp] theorem lookup_descent_12_9 : literalDescent (6, 0) (4, 1) = (-3520769 / 500000000) := rfl
@[simp] theorem lookup_previous_12_9 : previousPadding literalP (6, 0) (4, 1) = (-42393837 / 2500000000) := rfl
@[simp] theorem lookup_current_12_9 : currentPadding literalP (6, 0) (4, 1) = (-3098749 / 312500000) := rfl
@[simp] theorem lookup_descent_12_10 : literalDescent (6, 0) (5, 0) = (-63730673 / 20000000000) := rfl
@[simp] theorem lookup_previous_12_10 : previousPadding literalP (6, 0) (5, 0) = (-16412301 / 500000000) := rfl
@[simp] theorem lookup_current_12_10 : currentPadding literalP (6, 0) (5, 0) = (-309294277 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_11 : literalDescent (6, 0) (5, 1) = (8256277 / 20000000000) := rfl
@[simp] theorem lookup_previous_12_11 : previousPadding literalP (6, 0) (5, 1) = (-20430389 / 10000000000) := rfl
@[simp] theorem lookup_current_12_11 : currentPadding literalP (6, 0) (5, 1) = (-37472121 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_12 : literalDescent (6, 0) (6, 0) = (197600067 / 5000000000) := rfl
@[simp] theorem lookup_previous_12_12 : previousPadding literalP (6, 0) (6, 0) = (218738927 / 2000000000) := rfl
@[simp] theorem lookup_current_12_12 : currentPadding literalP (6, 0) (6, 0) = (34926337 / 500000000) := rfl
@[simp] theorem lookup_descent_12_13 : literalDescent (6, 0) (6, 1) = (2956197 / 1250000000) := rfl
@[simp] theorem lookup_previous_12_13 : previousPadding literalP (6, 0) (6, 1) = (66493119 / 10000000000) := rfl
@[simp] theorem lookup_current_12_13 : currentPadding literalP (6, 0) (6, 1) = (6973553 / 1250000000) := rfl
@[simp] theorem lookup_descent_12_14 : literalDescent (6, 0) (7, 0) = (-469649151 / 20000000000) := rfl
@[simp] theorem lookup_previous_12_14 : previousPadding literalP (6, 0) (7, 0) = (-309294277 / 10000000000) := rfl
@[simp] theorem lookup_current_12_14 : currentPadding literalP (6, 0) (7, 0) = (-74485821 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_15 : literalDescent (6, 0) (7, 1) = (-3395153833 / 500000000000) := rfl
@[simp] theorem lookup_previous_12_15 : previousPadding literalP (6, 0) (7, 1) = (-20540747 / 1250000000) := rfl
@[simp] theorem lookup_current_12_15 : currentPadding literalP (6, 0) (7, 1) = (-96425671 / 10000000000) := rfl
@[simp] theorem lookup_descent_12_16 : literalDescent (6, 0) (8, 0) = (-1161861 / 312500000) := rfl
@[simp] theorem lookup_previous_12_16 : previousPadding literalP (6, 0) (8, 0) = (-85475461 / 5000000000) := rfl
@[simp] theorem lookup_current_12_16 : currentPadding literalP (6, 0) (8, 0) = (-13377137 / 1000000000) := rfl
@[simp] theorem lookup_descent_12_17 : literalDescent (6, 0) (8, 1) = (100407769 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_17 : previousPadding literalP (6, 0) (8, 1) = (172996661 / 10000000000) := rfl
@[simp] theorem lookup_current_12_17 : currentPadding literalP (6, 0) (8, 1) = (18147223 / 2500000000) := rfl
@[simp] theorem lookup_descent_12_18 : literalDescent (6, 0) (9, 0) = (4142397 / 1250000000) := rfl
@[simp] theorem lookup_previous_12_18 : previousPadding literalP (6, 0) (9, 0) = (4142397 / 1250000000) := rfl
@[simp] theorem lookup_current_12_18 : currentPadding literalP (6, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_12_19 : literalDescent (6, 0) (9, 1) = (-41636703 / 10000000000) := rfl
@[simp] theorem lookup_previous_12_19 : previousPadding literalP (6, 0) (9, 1) = (-41636703 / 10000000000) := rfl
@[simp] theorem lookup_current_12_19 : currentPadding literalP (6, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_13_0 : literalDescent (6, 1) (0, 0) = (2284113 / 500000000000) := rfl
@[simp] theorem lookup_previous_13_0 : previousPadding literalP (6, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_13_0 : currentPadding literalP (6, 1) (0, 0) = (-1138533 / 500000000) := rfl
@[simp] theorem lookup_descent_13_1 : literalDescent (6, 1) (0, 1) = (63804443 / 250000000000) := rfl
@[simp] theorem lookup_previous_13_1 : previousPadding literalP (6, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_13_1 : currentPadding literalP (6, 1) (0, 1) = (-25283229 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_2 : literalDescent (6, 1) (1, 0) = (20595489 / 20000000000) := rfl
@[simp] theorem lookup_previous_13_2 : previousPadding literalP (6, 1) (1, 0) = (763867 / 250000000) := rfl
@[simp] theorem lookup_current_13_2 : currentPadding literalP (6, 1) (1, 0) = (6321581 / 2000000000) := rfl
@[simp] theorem lookup_descent_13_3 : literalDescent (6, 1) (1, 1) = (113640481 / 500000000000) := rfl
@[simp] theorem lookup_previous_13_3 : previousPadding literalP (6, 1) (1, 1) = (38165927 / 10000000000) := rfl
@[simp] theorem lookup_current_13_3 : currentPadding literalP (6, 1) (1, 1) = (18642173 / 5000000000) := rfl
@[simp] theorem lookup_descent_13_4 : literalDescent (6, 1) (2, 0) = (-20134553 / 5000000000) := rfl
@[simp] theorem lookup_previous_13_4 : previousPadding literalP (6, 1) (2, 0) = (-174187027 / 10000000000) := rfl
@[simp] theorem lookup_current_13_4 : currentPadding literalP (6, 1) (2, 0) = (-133917921 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_5 : literalDescent (6, 1) (2, 1) = (-13924049 / 10000000000) := rfl
@[simp] theorem lookup_previous_13_5 : previousPadding literalP (6, 1) (2, 1) = (-11921871 / 2500000000) := rfl
@[simp] theorem lookup_current_13_5 : currentPadding literalP (6, 1) (2, 1) = (-6752687 / 2000000000) := rfl
@[simp] theorem lookup_descent_13_6 : literalDescent (6, 1) (3, 0) = (6434287 / 2000000000) := rfl
@[simp] theorem lookup_previous_13_6 : previousPadding literalP (6, 1) (3, 0) = (50024319 / 10000000000) := rfl
@[simp] theorem lookup_current_13_6 : currentPadding literalP (6, 1) (3, 0) = (4463221 / 2500000000) := rfl
@[simp] theorem lookup_descent_13_7 : literalDescent (6, 1) (3, 1) = (4624379 / 5000000000) := rfl
@[simp] theorem lookup_previous_13_7 : previousPadding literalP (6, 1) (3, 1) = (24631061 / 10000000000) := rfl
@[simp] theorem lookup_current_13_7 : currentPadding literalP (6, 1) (3, 1) = (15382303 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_8 : literalDescent (6, 1) (4, 0) = (10269589 / 2000000000) := rfl
@[simp] theorem lookup_previous_13_8 : previousPadding literalP (6, 1) (4, 0) = (291050811 / 10000000000) := rfl
@[simp] theorem lookup_current_13_8 : currentPadding literalP (6, 1) (4, 0) = (119851433 / 5000000000) := rfl
@[simp] theorem lookup_descent_13_9 : literalDescent (6, 1) (4, 1) = (-5853459 / 5000000000) := rfl
@[simp] theorem lookup_previous_13_9 : previousPadding literalP (6, 1) (4, 1) = (-9818737 / 2500000000) := rfl
@[simp] theorem lookup_current_13_9 : currentPadding literalP (6, 1) (4, 1) = (-2756803 / 1000000000) := rfl
@[simp] theorem lookup_descent_13_10 : literalDescent (6, 1) (5, 0) = (-3011174513 / 500000000000) := rfl
@[simp] theorem lookup_previous_13_10 : previousPadding literalP (6, 1) (5, 0) = (-222994713 / 10000000000) := rfl
@[simp] theorem lookup_current_13_10 : currentPadding literalP (6, 1) (5, 0) = (-20540747 / 1250000000) := rfl
@[simp] theorem lookup_descent_13_11 : literalDescent (6, 1) (5, 1) = (-323682311 / 500000000000) := rfl
@[simp] theorem lookup_previous_13_11 : previousPadding literalP (6, 1) (5, 1) = (-32246187 / 5000000000) := rfl
@[simp] theorem lookup_current_13_11 : currentPadding literalP (6, 1) (5, 1) = (-59568359 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_12 : literalDescent (6, 1) (6, 0) = (2956197 / 1250000000) := rfl
@[simp] theorem lookup_previous_13_12 : previousPadding literalP (6, 1) (6, 0) = (66493119 / 10000000000) := rfl
@[simp] theorem lookup_current_13_12 : currentPadding literalP (6, 1) (6, 0) = (6973553 / 1250000000) := rfl
@[simp] theorem lookup_descent_13_13 : literalDescent (6, 1) (6, 1) = (2253703011 / 500000000000) := rfl
@[simp] theorem lookup_previous_13_13 : previousPadding literalP (6, 1) (6, 1) = (913808309 / 50000000000) := rfl
@[simp] theorem lookup_current_13_13 : currentPadding literalP (6, 1) (6, 1) = (5749595801 / 500000000000) := rfl
@[simp] theorem lookup_descent_13_14 : literalDescent (6, 1) (7, 0) = (-47594519 / 20000000000) := rfl
@[simp] theorem lookup_previous_13_14 : previousPadding literalP (6, 1) (7, 0) = (-37472121 / 10000000000) := rfl
@[simp] theorem lookup_current_13_14 : currentPadding literalP (6, 1) (7, 0) = (-13690981 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_15 : literalDescent (6, 1) (7, 1) = (-825432717 / 500000000000) := rfl
@[simp] theorem lookup_previous_13_15 : previousPadding literalP (6, 1) (7, 1) = (-59568359 / 10000000000) := rfl
@[simp] theorem lookup_current_13_15 : currentPadding literalP (6, 1) (7, 1) = (-43061639 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_16 : literalDescent (6, 1) (8, 0) = (-33161627 / 10000000000) := rfl
@[simp] theorem lookup_previous_13_16 : previousPadding literalP (6, 1) (8, 0) = (-5426021 / 1250000000) := rfl
@[simp] theorem lookup_current_13_16 : currentPadding literalP (6, 1) (8, 0) = (-10246541 / 10000000000) := rfl
@[simp] theorem lookup_descent_13_17 : literalDescent (6, 1) (8, 1) = (-850351 / 500000000) := rfl
@[simp] theorem lookup_previous_13_17 : previousPadding literalP (6, 1) (8, 1) = (-8365237 / 5000000000) := rfl
@[simp] theorem lookup_current_13_17 : currentPadding literalP (6, 1) (8, 1) = (138273 / 5000000000) := rfl
@[simp] theorem lookup_descent_13_18 : literalDescent (6, 1) (9, 0) = (399391 / 100000000) := rfl
@[simp] theorem lookup_previous_13_18 : previousPadding literalP (6, 1) (9, 0) = (399391 / 100000000) := rfl
@[simp] theorem lookup_current_13_18 : currentPadding literalP (6, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_13_19 : literalDescent (6, 1) (9, 1) = (3236241 / 5000000000) := rfl
@[simp] theorem lookup_previous_13_19 : previousPadding literalP (6, 1) (9, 1) = (3236241 / 5000000000) := rfl
@[simp] theorem lookup_current_13_19 : currentPadding literalP (6, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_14_0 : literalDescent (7, 0) (0, 0) = (-17375753 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_0 : previousPadding literalP (7, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_14_0 : currentPadding literalP (7, 0) (0, 0) = (3770829 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_1 : literalDescent (7, 0) (0, 1) = (-22036387 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_1 : previousPadding literalP (7, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_14_1 : currentPadding literalP (7, 0) (0, 1) = (6101191 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_2 : literalDescent (7, 0) (1, 0) = (-532371 / 500000000) := rfl
@[simp] theorem lookup_previous_14_2 : previousPadding literalP (7, 0) (1, 0) = (1609743 / 1000000000) := rfl
@[simp] theorem lookup_current_14_2 : currentPadding literalP (7, 0) (1, 0) = (26744907 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_3 : literalDescent (7, 0) (1, 1) = (-28694703 / 500000000000) := rfl
@[simp] theorem lookup_previous_14_3 : previousPadding literalP (7, 0) (1, 1) = (187769 / 1250000000) := rfl
@[simp] theorem lookup_current_14_3 : currentPadding literalP (7, 0) (1, 1) = (3496513 / 5000000000) := rfl
@[simp] theorem lookup_descent_14_4 : literalDescent (7, 0) (2, 0) = (29547999 / 5000000000) := rfl
@[simp] theorem lookup_previous_14_4 : previousPadding literalP (7, 0) (2, 0) = (-5223779 / 5000000000) := rfl
@[simp] theorem lookup_current_14_4 : currentPadding literalP (7, 0) (2, 0) = (-17385889 / 2500000000) := rfl
@[simp] theorem lookup_descent_14_5 : literalDescent (7, 0) (2, 1) = (10438369 / 10000000000) := rfl
@[simp] theorem lookup_previous_14_5 : previousPadding literalP (7, 0) (2, 1) = (-557263 / 250000000) := rfl
@[simp] theorem lookup_current_14_5 : currentPadding literalP (7, 0) (2, 1) = (-32728889 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_6 : literalDescent (7, 0) (3, 0) = (-28273383 / 10000000000) := rfl
@[simp] theorem lookup_previous_14_6 : previousPadding literalP (7, 0) (3, 0) = (18653667 / 5000000000) := rfl
@[simp] theorem lookup_current_14_6 : currentPadding literalP (7, 0) (3, 0) = (65580717 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_7 : literalDescent (7, 0) (3, 1) = (-3718079 / 2000000000) := rfl
@[simp] theorem lookup_previous_14_7 : previousPadding literalP (7, 0) (3, 1) = (14987849 / 10000000000) := rfl
@[simp] theorem lookup_current_14_7 : currentPadding literalP (7, 0) (3, 1) = (8394561 / 2500000000) := rfl
@[simp] theorem lookup_descent_14_8 : literalDescent (7, 0) (4, 0) = (138546279 / 10000000000) := rfl
@[simp] theorem lookup_previous_14_8 : previousPadding literalP (7, 0) (4, 0) = (10707859 / 500000000) := rfl
@[simp] theorem lookup_current_14_8 : currentPadding literalP (7, 0) (4, 0) = (75610901 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_9 : literalDescent (7, 0) (4, 1) = (235636977 / 25000000000) := rfl
@[simp] theorem lookup_previous_14_9 : previousPadding literalP (7, 0) (4, 1) = (3530847913 / 250000000000) := rfl
@[simp] theorem lookup_current_14_9 : currentPadding literalP (7, 0) (4, 1) = (1174478143 / 250000000000) := rfl
@[simp] theorem lookup_descent_14_10 : literalDescent (7, 0) (5, 0) = (-16696171 / 625000000) := rfl
@[simp] theorem lookup_previous_14_10 : previousPadding literalP (7, 0) (5, 0) = (-219044829 / 5000000000) := rfl
@[simp] theorem lookup_current_14_10 : currentPadding literalP (7, 0) (5, 0) = (-85475461 / 5000000000) := rfl
@[simp] theorem lookup_descent_14_11 : literalDescent (7, 0) (5, 1) = (-278759 / 50000000) := rfl
@[simp] theorem lookup_previous_14_11 : previousPadding literalP (7, 0) (5, 1) = (-3098749 / 312500000) := rfl
@[simp] theorem lookup_current_14_11 : currentPadding literalP (7, 0) (5, 1) = (-5426021 / 1250000000) := rfl
@[simp] theorem lookup_descent_14_12 : literalDescent (7, 0) (6, 0) = (-469649151 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_12 : previousPadding literalP (7, 0) (6, 0) = (-309294277 / 10000000000) := rfl
@[simp] theorem lookup_current_14_12 : currentPadding literalP (7, 0) (6, 0) = (-74485821 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_13 : literalDescent (7, 0) (6, 1) = (-47594519 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_13 : previousPadding literalP (7, 0) (6, 1) = (-37472121 / 10000000000) := rfl
@[simp] theorem lookup_current_14_13 : currentPadding literalP (7, 0) (6, 1) = (-13690981 / 10000000000) := rfl
@[simp] theorem lookup_descent_14_14 : literalDescent (7, 0) (7, 0) = (10279221 / 200000000) := rfl
@[simp] theorem lookup_previous_14_14 : previousPadding literalP (7, 0) (7, 0) = (34926337 / 500000000) := rfl
@[simp] theorem lookup_current_14_14 : currentPadding literalP (7, 0) (7, 0) = (19443191 / 1000000000) := rfl
@[simp] theorem lookup_descent_14_15 : literalDescent (7, 0) (7, 1) = (65904011 / 20000000000) := rfl
@[simp] theorem lookup_previous_14_15 : previousPadding literalP (7, 0) (7, 1) = (6973553 / 1250000000) := rfl
@[simp] theorem lookup_current_14_15 : currentPadding literalP (7, 0) (7, 1) = (187691 / 200000000) := rfl
@[simp] theorem lookup_descent_14_16 : literalDescent (7, 0) (8, 0) = (-14129983 / 5000000000) := rfl
@[simp] theorem lookup_previous_14_16 : previousPadding literalP (7, 0) (8, 0) = (-74485821 / 10000000000) := rfl
@[simp] theorem lookup_current_14_16 : currentPadding literalP (7, 0) (8, 0) = (-10231793 / 2000000000) := rfl
@[simp] theorem lookup_descent_14_17 : literalDescent (7, 0) (8, 1) = (-2512562881 / 250000000000) := rfl
@[simp] theorem lookup_previous_14_17 : previousPadding literalP (7, 0) (8, 1) = (-96425671 / 10000000000) := rfl
@[simp] theorem lookup_current_14_17 : currentPadding literalP (7, 0) (8, 1) = (-1065577 / 625000000) := rfl
@[simp] theorem lookup_descent_14_18 : literalDescent (7, 0) (9, 0) = (-13377137 / 1000000000) := rfl
@[simp] theorem lookup_previous_14_18 : previousPadding literalP (7, 0) (9, 0) = (-13377137 / 1000000000) := rfl
@[simp] theorem lookup_current_14_18 : currentPadding literalP (7, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_14_19 : literalDescent (7, 0) (9, 1) = (18147223 / 2500000000) := rfl
@[simp] theorem lookup_previous_14_19 : previousPadding literalP (7, 0) (9, 1) = (18147223 / 2500000000) := rfl
@[simp] theorem lookup_current_14_19 : currentPadding literalP (7, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_15_0 : literalDescent (7, 1) (0, 0) = (16059651 / 62500000000) := rfl
@[simp] theorem lookup_previous_15_0 : previousPadding literalP (7, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_15_0 : currentPadding literalP (7, 1) (0, 0) = (212259 / 78125000) := rfl
@[simp] theorem lookup_descent_15_1 : literalDescent (7, 1) (0, 1) = (54418421 / 250000000000) := rfl
@[simp] theorem lookup_previous_15_1 : previousPadding literalP (7, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_15_1 : currentPadding literalP (7, 1) (0, 1) = (2113457 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_2 : literalDescent (7, 1) (1, 0) = (-1523567 / 1250000000) := rfl
@[simp] theorem lookup_previous_15_2 : previousPadding literalP (7, 1) (1, 0) = (-1138533 / 500000000) := rfl
@[simp] theorem lookup_current_15_2 : currentPadding literalP (7, 1) (1, 0) = (-2193307 / 1000000000) := rfl
@[simp] theorem lookup_descent_15_3 : literalDescent (7, 1) (1, 1) = (-35657159 / 250000000000) := rfl
@[simp] theorem lookup_previous_15_3 : previousPadding literalP (7, 1) (1, 1) = (-25283229 / 10000000000) := rfl
@[simp] theorem lookup_current_15_3 : currentPadding literalP (7, 1) (1, 1) = (-1784163 / 2000000000) := rfl
@[simp] theorem lookup_descent_15_4 : literalDescent (7, 1) (2, 0) = (14810711 / 10000000000) := rfl
@[simp] theorem lookup_previous_15_4 : previousPadding literalP (7, 1) (2, 0) = (6321581 / 2000000000) := rfl
@[simp] theorem lookup_current_15_4 : currentPadding literalP (7, 1) (2, 0) = (8398597 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_5 : literalDescent (7, 1) (2, 1) = (5243573 / 5000000000) := rfl
@[simp] theorem lookup_previous_15_5 : previousPadding literalP (7, 1) (2, 1) = (18642173 / 5000000000) := rfl
@[simp] theorem lookup_current_15_5 : currentPadding literalP (7, 1) (2, 1) = (66993 / 25000000) := rfl
@[simp] theorem lookup_descent_15_6 : literalDescent (7, 1) (3, 0) = (-10666967 / 2500000000) := rfl
@[simp] theorem lookup_previous_15_6 : previousPadding literalP (7, 1) (3, 0) = (-133917921 / 10000000000) := rfl
@[simp] theorem lookup_current_15_6 : currentPadding literalP (7, 1) (3, 0) = (-91250053 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_7 : literalDescent (7, 1) (3, 1) = (-7042983 / 5000000000) := rfl
@[simp] theorem lookup_previous_15_7 : previousPadding literalP (7, 1) (3, 1) = (-6752687 / 2000000000) := rfl
@[simp] theorem lookup_current_15_7 : currentPadding literalP (7, 1) (3, 1) = (-19677469 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_8 : literalDescent (7, 1) (4, 0) = (10219941 / 5000000000) := rfl
@[simp] theorem lookup_previous_15_8 : previousPadding literalP (7, 1) (4, 0) = (4463221 / 2500000000) := rfl
@[simp] theorem lookup_current_15_8 : currentPadding literalP (7, 1) (4, 0) = (-1293499 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_9 : literalDescent (7, 1) (4, 1) = (6819061 / 10000000000) := rfl
@[simp] theorem lookup_previous_15_9 : previousPadding literalP (7, 1) (4, 1) = (15382303 / 10000000000) := rfl
@[simp] theorem lookup_current_15_9 : currentPadding literalP (7, 1) (4, 1) = (4281621 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_10 : literalDescent (7, 1) (5, 0) = (13341241 / 2000000000) := rfl
@[simp] theorem lookup_previous_15_10 : previousPadding literalP (7, 1) (5, 0) = (119851433 / 5000000000) := rfl
@[simp] theorem lookup_current_15_10 : currentPadding literalP (7, 1) (5, 0) = (172996661 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_11 : literalDescent (7, 1) (5, 1) = (-2709389 / 2500000000) := rfl
@[simp] theorem lookup_previous_15_11 : previousPadding literalP (7, 1) (5, 1) = (-2756803 / 1000000000) := rfl
@[simp] theorem lookup_current_15_11 : currentPadding literalP (7, 1) (5, 1) = (-8365237 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_12 : literalDescent (7, 1) (6, 0) = (-3395153833 / 500000000000) := rfl
@[simp] theorem lookup_previous_15_12 : previousPadding literalP (7, 1) (6, 0) = (-20540747 / 1250000000) := rfl
@[simp] theorem lookup_current_15_12 : currentPadding literalP (7, 1) (6, 0) = (-96425671 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_13 : literalDescent (7, 1) (6, 1) = (-825432717 / 500000000000) := rfl
@[simp] theorem lookup_previous_15_13 : previousPadding literalP (7, 1) (6, 1) = (-59568359 / 10000000000) := rfl
@[simp] theorem lookup_current_15_13 : currentPadding literalP (7, 1) (6, 1) = (-43061639 / 10000000000) := rfl
@[simp] theorem lookup_descent_15_14 : literalDescent (7, 1) (7, 0) = (65904011 / 20000000000) := rfl
@[simp] theorem lookup_previous_15_14 : previousPadding literalP (7, 1) (7, 0) = (6973553 / 1250000000) := rfl
@[simp] theorem lookup_current_15_14 : currentPadding literalP (7, 1) (7, 0) = (187691 / 200000000) := rfl
@[simp] theorem lookup_descent_15_15 : literalDescent (7, 1) (7, 1) = (1936005153 / 500000000000) := rfl
@[simp] theorem lookup_previous_15_15 : previousPadding literalP (7, 1) (7, 1) = (5749595801 / 500000000000) := rfl
@[simp] theorem lookup_current_15_15 : currentPadding literalP (7, 1) (7, 1) = (1076370783 / 125000000000) := rfl
@[simp] theorem lookup_descent_15_16 : literalDescent (7, 1) (8, 0) = (-2236163 / 5000000000) := rfl
@[simp] theorem lookup_previous_15_16 : previousPadding literalP (7, 1) (8, 0) = (-13690981 / 10000000000) := rfl
@[simp] theorem lookup_current_15_16 : currentPadding literalP (7, 1) (8, 0) = (-2830353 / 2000000000) := rfl
@[simp] theorem lookup_descent_15_17 : literalDescent (7, 1) (8, 1) = (-78105651 / 50000000000) := rfl
@[simp] theorem lookup_previous_15_17 : previousPadding literalP (7, 1) (8, 1) = (-43061639 / 10000000000) := rfl
@[simp] theorem lookup_current_15_17 : currentPadding literalP (7, 1) (8, 1) = (-14016241 / 5000000000) := rfl
@[simp] theorem lookup_descent_15_18 : literalDescent (7, 1) (9, 0) = (-10246541 / 10000000000) := rfl
@[simp] theorem lookup_previous_15_18 : previousPadding literalP (7, 1) (9, 0) = (-10246541 / 10000000000) := rfl
@[simp] theorem lookup_current_15_18 : currentPadding literalP (7, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_15_19 : literalDescent (7, 1) (9, 1) = (138273 / 5000000000) := rfl
@[simp] theorem lookup_previous_15_19 : previousPadding literalP (7, 1) (9, 1) = (138273 / 5000000000) := rfl
@[simp] theorem lookup_current_15_19 : currentPadding literalP (7, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_16_0 : literalDescent (8, 0) (0, 0) = (2588017 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_0 : previousPadding literalP (8, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_16_0 : currentPadding literalP (8, 0) (0, 0) = (-14486313 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_1 : literalDescent (8, 0) (0, 1) = (-6357481 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_1 : previousPadding literalP (8, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_16_1 : currentPadding literalP (8, 0) (0, 1) = (-5540767 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_2 : literalDescent (8, 0) (1, 0) = (13330203 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_2 : previousPadding literalP (8, 0) (1, 0) = (3770829 / 10000000000) := rfl
@[simp] theorem lookup_current_16_2 : currentPadding literalP (8, 0) (1, 0) = (-2165653 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_3 : literalDescent (8, 0) (1, 1) = (67650311 / 62500000000) := rfl
@[simp] theorem lookup_previous_16_3 : previousPadding literalP (8, 0) (1, 1) = (6101191 / 10000000000) := rfl
@[simp] theorem lookup_current_16_3 : currentPadding literalP (8, 0) (1, 1) = (-1681179 / 2500000000) := rfl
@[simp] theorem lookup_descent_16_4 : literalDescent (8, 0) (2, 0) = (-14959 / 8000000) := rfl
@[simp] theorem lookup_previous_16_4 : previousPadding literalP (8, 0) (2, 0) = (26744907 / 10000000000) := rfl
@[simp] theorem lookup_current_16_4 : currentPadding literalP (8, 0) (2, 0) = (45443657 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_5 : literalDescent (8, 0) (2, 1) = (1230083 / 5000000000) := rfl
@[simp] theorem lookup_previous_16_5 : previousPadding literalP (8, 0) (2, 1) = (3496513 / 5000000000) := rfl
@[simp] theorem lookup_current_16_5 : currentPadding literalP (8, 0) (2, 1) = (226643 / 500000000) := rfl
@[simp] theorem lookup_descent_16_6 : literalDescent (8, 0) (3, 0) = (-7402427 / 2000000000) := rfl
@[simp] theorem lookup_previous_16_6 : previousPadding literalP (8, 0) (3, 0) = (-17385889 / 2500000000) := rfl
@[simp] theorem lookup_current_16_6 : currentPadding literalP (8, 0) (3, 0) = (-32531421 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_7 : literalDescent (8, 0) (3, 1) = (-3848379 / 5000000000) := rfl
@[simp] theorem lookup_previous_16_7 : previousPadding literalP (8, 0) (3, 1) = (-32728889 / 10000000000) := rfl
@[simp] theorem lookup_current_16_7 : currentPadding literalP (8, 0) (3, 1) = (-25032131 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_8 : literalDescent (8, 0) (4, 0) = (382343 / 156250000) := rfl
@[simp] theorem lookup_previous_16_8 : previousPadding literalP (8, 0) (4, 0) = (65580717 / 10000000000) := rfl
@[simp] theorem lookup_current_16_8 : currentPadding literalP (8, 0) (4, 0) = (8222153 / 2000000000) := rfl
@[simp] theorem lookup_descent_16_9 : literalDescent (8, 0) (4, 1) = (151969 / 200000000) := rfl
@[simp] theorem lookup_previous_16_9 : previousPadding literalP (8, 0) (4, 1) = (8394561 / 2500000000) := rfl
@[simp] theorem lookup_current_16_9 : currentPadding literalP (8, 0) (4, 1) = (12989897 / 5000000000) := rfl
@[simp] theorem lookup_descent_16_10 : literalDescent (8, 0) (5, 0) = (1698869 / 400000000) := rfl
@[simp] theorem lookup_previous_16_10 : previousPadding literalP (8, 0) (5, 0) = (75610901 / 10000000000) := rfl
@[simp] theorem lookup_current_16_10 : currentPadding literalP (8, 0) (5, 0) = (4142397 / 1250000000) := rfl
@[simp] theorem lookup_descent_16_11 : literalDescent (8, 0) (5, 1) = (176000643 / 250000000000) := rfl
@[simp] theorem lookup_previous_16_11 : previousPadding literalP (8, 0) (5, 1) = (1174478143 / 250000000000) := rfl
@[simp] theorem lookup_current_16_11 : currentPadding literalP (8, 0) (5, 1) = (399391 / 100000000) := rfl
@[simp] theorem lookup_descent_16_12 : literalDescent (8, 0) (6, 0) = (-1161861 / 312500000) := rfl
@[simp] theorem lookup_previous_16_12 : previousPadding literalP (8, 0) (6, 0) = (-85475461 / 5000000000) := rfl
@[simp] theorem lookup_current_16_12 : currentPadding literalP (8, 0) (6, 0) = (-13377137 / 1000000000) := rfl
@[simp] theorem lookup_descent_16_13 : literalDescent (8, 0) (6, 1) = (-33161627 / 10000000000) := rfl
@[simp] theorem lookup_previous_16_13 : previousPadding literalP (8, 0) (6, 1) = (-5426021 / 1250000000) := rfl
@[simp] theorem lookup_current_16_13 : currentPadding literalP (8, 0) (6, 1) = (-10246541 / 10000000000) := rfl
@[simp] theorem lookup_descent_16_14 : literalDescent (8, 0) (7, 0) = (-14129983 / 5000000000) := rfl
@[simp] theorem lookup_previous_16_14 : previousPadding literalP (8, 0) (7, 0) = (-74485821 / 10000000000) := rfl
@[simp] theorem lookup_current_16_14 : currentPadding literalP (8, 0) (7, 0) = (-10231793 / 2000000000) := rfl
@[simp] theorem lookup_descent_16_15 : literalDescent (8, 0) (7, 1) = (-2236163 / 5000000000) := rfl
@[simp] theorem lookup_previous_16_15 : previousPadding literalP (8, 0) (7, 1) = (-13690981 / 10000000000) := rfl
@[simp] theorem lookup_current_16_15 : currentPadding literalP (8, 0) (7, 1) = (-2830353 / 2000000000) := rfl
@[simp] theorem lookup_descent_16_16 : literalDescent (8, 0) (8, 0) = (24721789 / 2500000000) := rfl
@[simp] theorem lookup_previous_16_16 : previousPadding literalP (8, 0) (8, 0) = (19443191 / 1000000000) := rfl
@[simp] theorem lookup_current_16_16 : currentPadding literalP (8, 0) (8, 0) = (28605031 / 2500000000) := rfl
@[simp] theorem lookup_descent_16_17 : literalDescent (8, 0) (8, 1) = (5243501 / 1250000000) := rfl
@[simp] theorem lookup_previous_16_17 : previousPadding literalP (8, 0) (8, 1) = (187691 / 200000000) := rfl
@[simp] theorem lookup_current_16_17 : currentPadding literalP (8, 0) (8, 1) = (-4377917 / 5000000000) := rfl
@[simp] theorem lookup_descent_16_18 : literalDescent (8, 0) (9, 0) = (-1211933 / 200000000) := rfl
@[simp] theorem lookup_previous_16_18 : previousPadding literalP (8, 0) (9, 0) = (-10231793 / 2000000000) := rfl
@[simp] theorem lookup_current_16_18 : currentPadding literalP (8, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_16_19 : literalDescent (8, 0) (9, 1) = (-454562687 / 250000000000) := rfl
@[simp] theorem lookup_previous_16_19 : previousPadding literalP (8, 0) (9, 1) = (-1065577 / 625000000) := rfl
@[simp] theorem lookup_current_16_19 : currentPadding literalP (8, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_17_0 : literalDescent (8, 1) (0, 0) = (-106656919 / 250000000000) := rfl
@[simp] theorem lookup_previous_17_0 : previousPadding literalP (8, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_17_0 : currentPadding literalP (8, 1) (0, 0) = (2903 / 8000000) := rfl
@[simp] theorem lookup_descent_17_1 : literalDescent (8, 1) (0, 1) = (-1709403 / 6250000000) := rfl
@[simp] theorem lookup_previous_17_1 : previousPadding literalP (8, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_17_1 : currentPadding literalP (8, 1) (0, 1) = (-18437441 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_2 : literalDescent (8, 1) (1, 0) = (17576467 / 10000000000) := rfl
@[simp] theorem lookup_previous_17_2 : previousPadding literalP (8, 1) (1, 0) = (212259 / 78125000) := rfl
@[simp] theorem lookup_current_17_2 : currentPadding literalP (8, 1) (1, 0) = (16986349 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_3 : literalDescent (8, 1) (1, 1) = (239256637 / 250000000000) := rfl
@[simp] theorem lookup_previous_17_3 : previousPadding literalP (8, 1) (1, 1) = (2113457 / 5000000000) := rfl
@[simp] theorem lookup_current_17_3 : currentPadding literalP (8, 1) (1, 1) = (964523 / 5000000000) := rfl
@[simp] theorem lookup_descent_17_4 : literalDescent (8, 1) (2, 0) = (-23416419 / 10000000000) := rfl
@[simp] theorem lookup_previous_17_4 : previousPadding literalP (8, 1) (2, 0) = (-2193307 / 1000000000) := rfl
@[simp] theorem lookup_current_17_4 : currentPadding literalP (8, 1) (2, 0) = (1483349 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_5 : literalDescent (8, 1) (2, 1) = (-2198967 / 5000000000) := rfl
@[simp] theorem lookup_previous_17_5 : previousPadding literalP (8, 1) (2, 1) = (-1784163 / 2000000000) := rfl
@[simp] theorem lookup_current_17_5 : currentPadding literalP (8, 1) (2, 1) = (-4522881 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_6 : literalDescent (8, 1) (3, 0) = (-585841 / 10000000000) := rfl
@[simp] theorem lookup_previous_17_6 : previousPadding literalP (8, 1) (3, 0) = (8398597 / 5000000000) := rfl
@[simp] theorem lookup_current_17_6 : currentPadding literalP (8, 1) (3, 0) = (3476607 / 2000000000) := rfl
@[simp] theorem lookup_descent_17_7 : literalDescent (8, 1) (3, 1) = (13314091 / 10000000000) := rfl
@[simp] theorem lookup_previous_17_7 : previousPadding literalP (8, 1) (3, 1) = (66993 / 25000000) := rfl
@[simp] theorem lookup_current_17_7 : currentPadding literalP (8, 1) (3, 1) = (13483109 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_8 : literalDescent (8, 1) (4, 0) = (-46621447 / 10000000000) := rfl
@[simp] theorem lookup_previous_17_8 : previousPadding literalP (8, 1) (4, 0) = (-91250053 / 10000000000) := rfl
@[simp] theorem lookup_current_17_8 : currentPadding literalP (8, 1) (4, 0) = (-22314303 / 5000000000) := rfl
@[simp] theorem lookup_descent_17_9 : literalDescent (8, 1) (4, 1) = (-1108671 / 625000000) := rfl
@[simp] theorem lookup_previous_17_9 : previousPadding literalP (8, 1) (4, 1) = (-19677469 / 10000000000) := rfl
@[simp] theorem lookup_current_17_9 : currentPadding literalP (8, 1) (4, 1) = (-1938733 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_10 : literalDescent (8, 1) (5, 0) = (7809941 / 2000000000) := rfl
@[simp] theorem lookup_previous_17_10 : previousPadding literalP (8, 1) (5, 0) = (-1293499 / 5000000000) := rfl
@[simp] theorem lookup_current_17_10 : currentPadding literalP (8, 1) (5, 0) = (-41636703 / 10000000000) := rfl
@[simp] theorem lookup_descent_17_11 : literalDescent (8, 1) (5, 1) = (52269 / 250000000) := rfl
@[simp] theorem lookup_previous_17_11 : previousPadding literalP (8, 1) (5, 1) = (4281621 / 5000000000) := rfl
@[simp] theorem lookup_current_17_11 : currentPadding literalP (8, 1) (5, 1) = (3236241 / 5000000000) := rfl
@[simp] theorem lookup_descent_17_12 : literalDescent (8, 1) (6, 0) = (100407769 / 10000000000) := rfl
@[simp] theorem lookup_previous_17_12 : previousPadding literalP (8, 1) (6, 0) = (172996661 / 10000000000) := rfl
@[simp] theorem lookup_current_17_12 : currentPadding literalP (8, 1) (6, 0) = (18147223 / 2500000000) := rfl
@[simp] theorem lookup_descent_17_13 : literalDescent (8, 1) (6, 1) = (-850351 / 500000000) := rfl
@[simp] theorem lookup_previous_17_13 : previousPadding literalP (8, 1) (6, 1) = (-8365237 / 5000000000) := rfl
@[simp] theorem lookup_current_17_13 : currentPadding literalP (8, 1) (6, 1) = (138273 / 5000000000) := rfl
@[simp] theorem lookup_descent_17_14 : literalDescent (8, 1) (7, 0) = (-2512562881 / 250000000000) := rfl
@[simp] theorem lookup_previous_17_14 : previousPadding literalP (8, 1) (7, 0) = (-96425671 / 10000000000) := rfl
@[simp] theorem lookup_current_17_14 : currentPadding literalP (8, 1) (7, 0) = (-1065577 / 625000000) := rfl
@[simp] theorem lookup_descent_17_15 : literalDescent (8, 1) (7, 1) = (-78105651 / 50000000000) := rfl
@[simp] theorem lookup_previous_17_15 : previousPadding literalP (8, 1) (7, 1) = (-43061639 / 10000000000) := rfl
@[simp] theorem lookup_current_17_15 : currentPadding literalP (8, 1) (7, 1) = (-14016241 / 5000000000) := rfl
@[simp] theorem lookup_descent_17_16 : literalDescent (8, 1) (8, 0) = (5243501 / 1250000000) := rfl
@[simp] theorem lookup_previous_17_16 : previousPadding literalP (8, 1) (8, 0) = (187691 / 200000000) := rfl
@[simp] theorem lookup_current_17_16 : currentPadding literalP (8, 1) (8, 0) = (-4377917 / 5000000000) := rfl
@[simp] theorem lookup_descent_17_17 : literalDescent (8, 1) (8, 1) = (771121909 / 125000000000) := rfl
@[simp] theorem lookup_previous_17_17 : previousPadding literalP (8, 1) (8, 1) = (1076370783 / 125000000000) := rfl
@[simp] theorem lookup_current_17_17 : currentPadding literalP (8, 1) (8, 1) = (432662579 / 125000000000) := rfl
@[simp] theorem lookup_descent_17_18 : literalDescent (8, 1) (9, 0) = (-471789 / 200000000) := rfl
@[simp] theorem lookup_previous_17_18 : previousPadding literalP (8, 1) (9, 0) = (-2830353 / 2000000000) := rfl
@[simp] theorem lookup_current_17_18 : currentPadding literalP (8, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_17_19 : literalDescent (8, 1) (9, 1) = (-145825021 / 50000000000) := rfl
@[simp] theorem lookup_previous_17_19 : previousPadding literalP (8, 1) (9, 1) = (-14016241 / 5000000000) := rfl
@[simp] theorem lookup_current_17_19 : currentPadding literalP (8, 1) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_0 : literalDescent (9, 0) (0, 0) = (1887537 / 2000000000) := rfl
@[simp] theorem lookup_previous_18_0 : previousPadding literalP (9, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_18_0 : currentPadding literalP (9, 0) (0, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_1 : literalDescent (9, 0) (0, 1) = (1887537 / 2000000000) := rfl
@[simp] theorem lookup_previous_18_1 : previousPadding literalP (9, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_18_1 : currentPadding literalP (9, 0) (0, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_2 : literalDescent (9, 0) (1, 0) = (-14486313 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_2 : previousPadding literalP (9, 0) (1, 0) = (-14486313 / 10000000000) := rfl
@[simp] theorem lookup_current_18_2 : currentPadding literalP (9, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_3 : literalDescent (9, 0) (1, 1) = (-3744613 / 2500000000) := rfl
@[simp] theorem lookup_previous_18_3 : previousPadding literalP (9, 0) (1, 1) = (-5540767 / 10000000000) := rfl
@[simp] theorem lookup_current_18_3 : currentPadding literalP (9, 0) (1, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_4 : literalDescent (9, 0) (2, 0) = (-2165653 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_4 : previousPadding literalP (9, 0) (2, 0) = (-2165653 / 10000000000) := rfl
@[simp] theorem lookup_current_18_4 : currentPadding literalP (9, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_5 : literalDescent (9, 0) (2, 1) = (-1681179 / 2500000000) := rfl
@[simp] theorem lookup_previous_18_5 : previousPadding literalP (9, 0) (2, 1) = (-1681179 / 2500000000) := rfl
@[simp] theorem lookup_current_18_5 : currentPadding literalP (9, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_6 : literalDescent (9, 0) (3, 0) = (45443657 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_6 : previousPadding literalP (9, 0) (3, 0) = (45443657 / 10000000000) := rfl
@[simp] theorem lookup_current_18_6 : currentPadding literalP (9, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_7 : literalDescent (9, 0) (3, 1) = (226643 / 500000000) := rfl
@[simp] theorem lookup_previous_18_7 : previousPadding literalP (9, 0) (3, 1) = (226643 / 500000000) := rfl
@[simp] theorem lookup_current_18_7 : currentPadding literalP (9, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_8 : literalDescent (9, 0) (4, 0) = (-32531421 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_8 : previousPadding literalP (9, 0) (4, 0) = (-32531421 / 10000000000) := rfl
@[simp] theorem lookup_current_18_8 : currentPadding literalP (9, 0) (4, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_9 : literalDescent (9, 0) (4, 1) = (-25032131 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_9 : previousPadding literalP (9, 0) (4, 1) = (-25032131 / 10000000000) := rfl
@[simp] theorem lookup_current_18_9 : currentPadding literalP (9, 0) (4, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_10 : literalDescent (9, 0) (5, 0) = (8222153 / 2000000000) := rfl
@[simp] theorem lookup_previous_18_10 : previousPadding literalP (9, 0) (5, 0) = (8222153 / 2000000000) := rfl
@[simp] theorem lookup_current_18_10 : currentPadding literalP (9, 0) (5, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_11 : literalDescent (9, 0) (5, 1) = (12989897 / 5000000000) := rfl
@[simp] theorem lookup_previous_18_11 : previousPadding literalP (9, 0) (5, 1) = (12989897 / 5000000000) := rfl
@[simp] theorem lookup_current_18_11 : currentPadding literalP (9, 0) (5, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_12 : literalDescent (9, 0) (6, 0) = (4142397 / 1250000000) := rfl
@[simp] theorem lookup_previous_18_12 : previousPadding literalP (9, 0) (6, 0) = (4142397 / 1250000000) := rfl
@[simp] theorem lookup_current_18_12 : currentPadding literalP (9, 0) (6, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_13 : literalDescent (9, 0) (6, 1) = (399391 / 100000000) := rfl
@[simp] theorem lookup_previous_18_13 : previousPadding literalP (9, 0) (6, 1) = (399391 / 100000000) := rfl
@[simp] theorem lookup_current_18_13 : currentPadding literalP (9, 0) (6, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_14 : literalDescent (9, 0) (7, 0) = (-13377137 / 1000000000) := rfl
@[simp] theorem lookup_previous_18_14 : previousPadding literalP (9, 0) (7, 0) = (-13377137 / 1000000000) := rfl
@[simp] theorem lookup_current_18_14 : currentPadding literalP (9, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_15 : literalDescent (9, 0) (7, 1) = (-10246541 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_15 : previousPadding literalP (9, 0) (7, 1) = (-10246541 / 10000000000) := rfl
@[simp] theorem lookup_current_18_15 : currentPadding literalP (9, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_16 : literalDescent (9, 0) (8, 0) = (-1211933 / 200000000) := rfl
@[simp] theorem lookup_previous_18_16 : previousPadding literalP (9, 0) (8, 0) = (-10231793 / 2000000000) := rfl
@[simp] theorem lookup_current_18_16 : currentPadding literalP (9, 0) (8, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_17 : literalDescent (9, 0) (8, 1) = (-471789 / 200000000) := rfl
@[simp] theorem lookup_previous_18_17 : previousPadding literalP (9, 0) (8, 1) = (-2830353 / 2000000000) := rfl
@[simp] theorem lookup_current_18_17 : currentPadding literalP (9, 0) (8, 1) = 0 := rfl
@[simp] theorem lookup_descent_18_18 : literalDescent (9, 0) (9, 0) = (28605031 / 2500000000) := rfl
@[simp] theorem lookup_previous_18_18 : previousPadding literalP (9, 0) (9, 0) = (28605031 / 2500000000) := rfl
@[simp] theorem lookup_current_18_18 : currentPadding literalP (9, 0) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_18_19 : literalDescent (9, 0) (9, 1) = (681851 / 10000000000) := rfl
@[simp] theorem lookup_previous_18_19 : previousPadding literalP (9, 0) (9, 1) = (-4377917 / 5000000000) := rfl
@[simp] theorem lookup_current_18_19 : currentPadding literalP (9, 0) (9, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_0 : literalDescent (9, 1) (0, 0) = (-22767213 / 250000000000) := rfl
@[simp] theorem lookup_previous_19_0 : previousPadding literalP (9, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_current_19_0 : currentPadding literalP (9, 1) (0, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_1 : literalDescent (9, 1) (0, 1) = (-4557209 / 50000000000) := rfl
@[simp] theorem lookup_previous_19_1 : previousPadding literalP (9, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_current_19_1 : currentPadding literalP (9, 1) (0, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_2 : literalDescent (9, 1) (1, 0) = (-3764971 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_2 : previousPadding literalP (9, 1) (1, 0) = (2903 / 8000000) := rfl
@[simp] theorem lookup_current_19_2 : currentPadding literalP (9, 1) (1, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_3 : literalDescent (9, 1) (1, 1) = (-90645093 / 250000000000) := rfl
@[simp] theorem lookup_previous_19_3 : previousPadding literalP (9, 1) (1, 1) = (-18437441 / 10000000000) := rfl
@[simp] theorem lookup_current_19_3 : currentPadding literalP (9, 1) (1, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_4 : literalDescent (9, 1) (2, 0) = (16986349 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_4 : previousPadding literalP (9, 1) (2, 0) = (16986349 / 10000000000) := rfl
@[simp] theorem lookup_current_19_4 : currentPadding literalP (9, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_5 : literalDescent (9, 1) (2, 1) = (964523 / 5000000000) := rfl
@[simp] theorem lookup_previous_19_5 : previousPadding literalP (9, 1) (2, 1) = (964523 / 5000000000) := rfl
@[simp] theorem lookup_current_19_5 : currentPadding literalP (9, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_6 : literalDescent (9, 1) (3, 0) = (1483349 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_6 : previousPadding literalP (9, 1) (3, 0) = (1483349 / 10000000000) := rfl
@[simp] theorem lookup_current_19_6 : currentPadding literalP (9, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_7 : literalDescent (9, 1) (3, 1) = (-4522881 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_7 : previousPadding literalP (9, 1) (3, 1) = (-4522881 / 10000000000) := rfl
@[simp] theorem lookup_current_19_7 : currentPadding literalP (9, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_8 : literalDescent (9, 1) (4, 0) = (3476607 / 2000000000) := rfl
@[simp] theorem lookup_previous_19_8 : previousPadding literalP (9, 1) (4, 0) = (3476607 / 2000000000) := rfl
@[simp] theorem lookup_current_19_8 : currentPadding literalP (9, 1) (4, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_9 : literalDescent (9, 1) (4, 1) = (13483109 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_9 : previousPadding literalP (9, 1) (4, 1) = (13483109 / 10000000000) := rfl
@[simp] theorem lookup_current_19_9 : currentPadding literalP (9, 1) (4, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_10 : literalDescent (9, 1) (5, 0) = (-22314303 / 5000000000) := rfl
@[simp] theorem lookup_previous_19_10 : previousPadding literalP (9, 1) (5, 0) = (-22314303 / 5000000000) := rfl
@[simp] theorem lookup_current_19_10 : currentPadding literalP (9, 1) (5, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_11 : literalDescent (9, 1) (5, 1) = (-1938733 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_11 : previousPadding literalP (9, 1) (5, 1) = (-1938733 / 10000000000) := rfl
@[simp] theorem lookup_current_19_11 : currentPadding literalP (9, 1) (5, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_12 : literalDescent (9, 1) (6, 0) = (-41636703 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_12 : previousPadding literalP (9, 1) (6, 0) = (-41636703 / 10000000000) := rfl
@[simp] theorem lookup_current_19_12 : currentPadding literalP (9, 1) (6, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_13 : literalDescent (9, 1) (6, 1) = (3236241 / 5000000000) := rfl
@[simp] theorem lookup_previous_19_13 : previousPadding literalP (9, 1) (6, 1) = (3236241 / 5000000000) := rfl
@[simp] theorem lookup_current_19_13 : currentPadding literalP (9, 1) (6, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_14 : literalDescent (9, 1) (7, 0) = (18147223 / 2500000000) := rfl
@[simp] theorem lookup_previous_19_14 : previousPadding literalP (9, 1) (7, 0) = (18147223 / 2500000000) := rfl
@[simp] theorem lookup_current_19_14 : currentPadding literalP (9, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_15 : literalDescent (9, 1) (7, 1) = (138273 / 5000000000) := rfl
@[simp] theorem lookup_previous_19_15 : previousPadding literalP (9, 1) (7, 1) = (138273 / 5000000000) := rfl
@[simp] theorem lookup_current_19_15 : currentPadding literalP (9, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_16 : literalDescent (9, 1) (8, 0) = (-454562687 / 250000000000) := rfl
@[simp] theorem lookup_previous_19_16 : previousPadding literalP (9, 1) (8, 0) = (-1065577 / 625000000) := rfl
@[simp] theorem lookup_current_19_16 : currentPadding literalP (9, 1) (8, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_17 : literalDescent (9, 1) (8, 1) = (-145825021 / 50000000000) := rfl
@[simp] theorem lookup_previous_19_17 : previousPadding literalP (9, 1) (8, 1) = (-14016241 / 5000000000) := rfl
@[simp] theorem lookup_current_19_17 : currentPadding literalP (9, 1) (8, 1) = 0 := rfl
@[simp] theorem lookup_descent_19_18 : literalDescent (9, 1) (9, 0) = (681851 / 10000000000) := rfl
@[simp] theorem lookup_previous_19_18 : previousPadding literalP (9, 1) (9, 0) = (-4377917 / 5000000000) := rfl
@[simp] theorem lookup_current_19_18 : currentPadding literalP (9, 1) (9, 0) = 0 := rfl
@[simp] theorem lookup_descent_19_19 : literalDescent (9, 1) (9, 1) = (225033509 / 125000000000) := rfl
@[simp] theorem lookup_previous_19_19 : previousPadding literalP (9, 1) (9, 1) = (432662579 / 125000000000) := rfl
@[simp] theorem lookup_current_19_19 : currentPadding literalP (9, 1) (9, 1) = 0 := rfl

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseFour.Lower.MatrixBridge
