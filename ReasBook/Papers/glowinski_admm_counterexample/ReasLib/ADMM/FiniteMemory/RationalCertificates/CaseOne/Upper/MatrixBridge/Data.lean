module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCaseData
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalComputation

@[expose] public section
set_option linter.style.longLine false
set_option maxRecDepth 4096

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.MatrixBridge

abbrev caseData := ADMM.FiniteMemory.Reconstruction.caseOne

-- Candidate literals require the equality proofs in the subsequent bridge modules.
def readFlat {r s : ℕ} (values : List (List ℚ)) :
    Matrix (Fin r × Fin 2) (Fin s × Fin 2) ℚ := fun i j ↦
  (values.getD (coordinateRank i) []).getD (coordinateRank j) 0

def readTwo {r : ℕ} (values : List (List ℚ)) :
    Matrix (Fin r × Fin 2) (Fin 2) ℚ := fun i j ↦
  (values.getD (coordinateRank i) []).getD j.val 0

def literalQData : List (List ℚ) := [
  [(-123333 / 1000000), (559 / 10000), (37261 / 400000), (-370559 / 20000000), (31909 / 500000), (-184397 / 10000000), (-81293 / 2000000), (-524099 / 20000000)],
  [(559 / 10000), (-122333 / 1000000), (-24313 / 400000), (979719 / 20000000), (45529 / 1000000), (586721 / 5000000), (-81293 / 2000000), (-524099 / 20000000)],
  [(37261 / 400000), (-24313 / 400000), (-15743 / 250000), (-34951 / 500000), (-46343 / 2000000), (452861 / 5000000), 0, (21863 / 400000)],
  [(-370559 / 20000000), (979719 / 20000000), (-34951 / 500000), (-386109 / 10000000), (955669 / 20000000), (-299613 / 20000000), (81293 / 2000000), (-83391 / 1250000)],
  [(31909 / 500000), (45529 / 1000000), (-46343 / 2000000), (955669 / 20000000), (-81293 / 1000000), (-112779 / 1000000), (81293 / 2000000), (243879 / 20000000)],
  [(-184397 / 10000000), (586721 / 5000000), (452861 / 5000000), (-299613 / 20000000), (-112779 / 1000000), (-186063 / 5000000), (81293 / 2000000), (243879 / 20000000)],
  [(-81293 / 2000000), (-81293 / 2000000), 0, (81293 / 2000000), (81293 / 2000000), (81293 / 2000000), 0, (-81293 / 2000000)],
  [(-524099 / 20000000), (-524099 / 20000000), (21863 / 400000), (-83391 / 1250000), (243879 / 20000000), (243879 / 20000000), (-81293 / 2000000), (569051 / 10000000)]
]

def literalActionData : List (List ℚ) := [
  [(-7009 / 1000000), (-36363 / 5000000)],
  [0, (88961 / 5000000)],
  [(7009 / 1000000), (36363 / 2500000)],
  [0, (-22287 / 312500)],
  [0, (-36363 / 5000000)],
  [0, (773449 / 10000000)],
  [0, 0],
  [0, (-238187 / 10000000)]
]

def literalPrefixData : List (List ℚ) := [
  [(7009 / 1000000), (36363 / 5000000)],
  [0, (-88961 / 5000000)],
  [0, (-36363 / 5000000)],
  [0, (267631 / 5000000)],
  [0, 0],
  [0, (-238187 / 10000000)]
]

def literalAData : List (List ℚ) := [
  [(4596577 / 50000000), (-41714243 / 500000000), (-3543031 / 50000000), (113917 / 2500000)],
  [(-41714243 / 500000000), (45980937 / 500000000), (75378799 / 1000000000), (-21647613 / 1000000000)],
  [(-3543031 / 50000000), (75378799 / 1000000000), (12432659 / 100000000), (-3513713 / 100000000)],
  [(113917 / 2500000), (-21647613 / 1000000000), (-3513713 / 100000000), (49850477 / 500000000)]
]

def literalTData : List (List ℚ) := [
  [(-87887 / 6250000), (22567143 / 500000000)],
  [(8049687 / 1000000000), (-88106461 / 1000000000)],
  [(-5346597 / 100000000), (-47514269 / 1000000000)],
  [(-1042967 / 100000000), (-24527141 / 1000000000)]
]

def literalWData : List (List ℚ) := [
  [(6752789 / 100000000), (2379983 / 1000000000)],
  [(2379983 / 1000000000), (44407451 / 500000000)]
]

def literalPData : List (List ℚ) := [
  [(4596577 / 50000000), (-41714243 / 500000000), (-3543031 / 50000000), (113917 / 2500000), (-87887 / 6250000), (22567143 / 500000000)],
  [(-41714243 / 500000000), (45980937 / 500000000), (75378799 / 1000000000), (-21647613 / 1000000000), (8049687 / 1000000000), (-88106461 / 1000000000)],
  [(-3543031 / 50000000), (75378799 / 1000000000), (12432659 / 100000000), (-3513713 / 100000000), (-5346597 / 100000000), (-47514269 / 1000000000)],
  [(113917 / 2500000), (-21647613 / 1000000000), (-3513713 / 100000000), (49850477 / 500000000), (-1042967 / 100000000), (-24527141 / 1000000000)],
  [(-87887 / 6250000), (8049687 / 1000000000), (-5346597 / 100000000), (-1042967 / 100000000), (6752789 / 100000000), (2379983 / 1000000000)],
  [(22567143 / 500000000), (-88106461 / 1000000000), (-47514269 / 1000000000), (-24527141 / 1000000000), (2379983 / 1000000000), (44407451 / 500000000)]
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

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.MatrixBridge
