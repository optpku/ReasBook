module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCaseData
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalComputation

@[expose] public section
set_option linter.style.longLine false
set_option maxRecDepth 4096

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.MatrixBridge

abbrev caseData := ADMM.FiniteMemory.Reconstruction.caseOne

-- Candidate literals require the equality proofs in the subsequent bridge modules.
def readFlat {r s : ℕ} (values : List (List ℚ)) :
    Matrix (Fin r × Fin 2) (Fin s × Fin 2) ℚ := fun i j ↦
  (values.getD (coordinateRank i) []).getD (coordinateRank j) 0

def readTwo {r : ℕ} (values : List (List ℚ)) :
    Matrix (Fin r × Fin 2) (Fin 2) ℚ := fun i j ↦
  (values.getD (coordinateRank i) []).getD j.val 0

def literalQData : List (List ℚ) := [
  [(-123333 / 1000000), (559 / 10000), (37261 / 400000), (-33633 / 800000), (31909 / 500000), (28117 / 2000000), (-81293 / 2000000), (-137337 / 4000000)],
  [(559 / 10000), (-122333 / 1000000), (-24313 / 400000), (245277 / 4000000), (45529 / 1000000), (111047 / 1000000), (-81293 / 2000000), (-137337 / 4000000)],
  [(37261 / 400000), (-24313 / 400000), (-15743 / 250000), (-7823 / 200000), (-46343 / 2000000), (29037 / 500000), 0, (21863 / 400000)],
  [(-33633 / 800000), (245277 / 4000000), (-7823 / 200000), (-25311 / 400000), (162039 / 4000000), (-53271 / 4000000), (81293 / 2000000), (-11913 / 250000)],
  [(31909 / 500000), (45529 / 1000000), (-46343 / 2000000), (162039 / 4000000), (-81293 / 1000000), (-112779 / 1000000), (81293 / 2000000), (81293 / 4000000)],
  [(28117 / 2000000), (111047 / 1000000), (29037 / 500000), (-53271 / 4000000), (-112779 / 1000000), (-49807 / 1000000), (81293 / 2000000), (81293 / 4000000)],
  [(-81293 / 2000000), (-81293 / 2000000), 0, (81293 / 2000000), (81293 / 2000000), (81293 / 2000000), 0, (-81293 / 2000000)],
  [(-137337 / 4000000), (-137337 / 4000000), (21863 / 400000), (-11913 / 250000), (81293 / 4000000), (81293 / 4000000), (-81293 / 2000000), (81293 / 2000000)]
]

def literalActionData : List (List ℚ) := [
  [(-7009 / 1000000), (-6417 / 1000000)],
  [0, (15699 / 1000000)],
  [(7009 / 1000000), (6417 / 500000)],
  [0, (-3933 / 62500)],
  [0, (-6417 / 1000000)],
  [0, (136491 / 2000000)],
  [0, 0],
  [0, (-42033 / 2000000)]
]

def literalPrefixData : List (List ℚ) := [
  [(7009 / 1000000), (6417 / 1000000)],
  [0, (-15699 / 1000000)],
  [0, (-6417 / 1000000)],
  [0, (47229 / 1000000)],
  [0, 0],
  [0, (-42033 / 2000000)]
]

def literalAData : List (List ℚ) := [
  [(8350767 / 100000000), (-8831839 / 100000000), (-678671 / 12500000), (7013879 / 100000000)],
  [(-8831839 / 100000000), (8422643 / 100000000), (8469609 / 100000000), (-2429443 / 100000000)],
  [(-678671 / 12500000), (8469609 / 100000000), (2272261 / 25000000), (-852583 / 12500000)],
  [(7013879 / 100000000), (-2429443 / 100000000), (-852583 / 12500000), (10436193 / 100000000)]
]

def literalTData : List (List ℚ) := [
  [(-2220499 / 100000000), (122983 / 5000000)],
  [(36223 / 10000000), (-75631 / 1000000)],
  [(-914919 / 25000000), (-458129 / 20000000)],
  [(-38643 / 20000000), (-65677 / 2000000)]
]

def literalWData : List (List ℚ) := [
  [(235207 / 4000000), (-33803 / 20000000)],
  [(-33803 / 20000000), (87453 / 1000000)]
]

def literalPData : List (List ℚ) := [
  [(8350767 / 100000000), (-8831839 / 100000000), (-678671 / 12500000), (7013879 / 100000000), (-2220499 / 100000000), (122983 / 5000000)],
  [(-8831839 / 100000000), (8422643 / 100000000), (8469609 / 100000000), (-2429443 / 100000000), (36223 / 10000000), (-75631 / 1000000)],
  [(-678671 / 12500000), (8469609 / 100000000), (2272261 / 25000000), (-852583 / 12500000), (-914919 / 25000000), (-458129 / 20000000)],
  [(7013879 / 100000000), (-2429443 / 100000000), (-852583 / 12500000), (10436193 / 100000000), (-38643 / 20000000), (-65677 / 2000000)],
  [(-2220499 / 100000000), (36223 / 10000000), (-914919 / 25000000), (-38643 / 20000000), (235207 / 4000000), (-33803 / 20000000)],
  [(122983 / 5000000), (-75631 / 1000000), (-458129 / 20000000), (-65677 / 2000000), (-33803 / 20000000), (87453 / 1000000)]
]

def literalMuFData : List (List ℚ) := [
  [0, (394093 / 100000000), (60309 / 20000000)],
  [(1717 / 100000000), 0, (418251 / 20000000)],
  [(1121 / 100000000), (5193879 / 100000000), 0]
]

def literalMuJData : List (List ℚ) := [
  [0, (93889 / 25000000), (9999 / 3125000)],
  [(2033 / 100000000), 0, (1371209 / 50000000)],
  [(691 / 100000000), (1343899 / 20000000), 0]
]

def literalQ : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℚ := readFlat literalQData
def literalA : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℚ := readFlat literalAData
def literalP : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℚ := readFlat literalPData
def literalAction : Matrix (Fin 4 × Fin 2) (Fin 2) ℚ := readTwo literalActionData
def literalPrefix : Matrix (Fin 3 × Fin 2) (Fin 2) ℚ := readTwo literalPrefixData
def literalT : Matrix (Fin 2 × Fin 2) (Fin 2) ℚ := readTwo literalTData
def literalW : Matrix (Fin 2) (Fin 2) ℚ := fun i j ↦
  (literalWData.getD i.val []).getD j.val 0
def literalMu (b : Block) (i j : Option (Fin 2)) : ℚ :=
  let data := match b with | .F => literalMuFData | .J => literalMuJData
  (data.getD (Computation.optionIndex i).val []).getD (Computation.optionIndex j).val 0

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.MatrixBridge
