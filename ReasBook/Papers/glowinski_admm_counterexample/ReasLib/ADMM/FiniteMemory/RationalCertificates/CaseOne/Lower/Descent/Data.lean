/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.LDLCertificate
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCaseData
@[expose] public section
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.Descent

abbrev caseData := ADMM.FiniteMemory.Reconstruction.caseOne

def literalMatrix (values : List (List ℚ)) :
    Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℚ := fun i j ↦
  (values.getD (coordinateRank i) []).getD (coordinateRank j) 0

def candidateKData : List (List ℚ) := [
  [(3982533 / 100000000), (3241839 / 100000000), (-1942941 / 50000000), (-1404877 / 50000000), (-4161301 / 100000000), (-386551 / 10000000)],
  [(3241839 / 100000000), (3810657 / 100000000), (-2391359 / 100000000), (-1851241 / 50000000), (-491513 / 10000000), (-4427 / 125000)],
  [(-1942941 / 50000000), (-2391359 / 100000000), (5558923 / 100000000), (76013 / 4000000), (273729 / 50000000), (874281 / 25000000)],
  [(-1404877 / 50000000), (-1851241 / 50000000), (76013 / 4000000), (21571 / 500000), (4611849 / 100000000), (1093091 / 50000000)],
  [(-4161301 / 100000000), (-491513 / 10000000), (273729 / 50000000), (4611849 / 100000000), (11338169 / 100000000), (4626251 / 100000000)],
  [(-386551 / 10000000), (-4427 / 125000), (874281 / 25000000), (1093091 / 50000000), (4626251 / 100000000), (6671593 / 100000000)]
]

def candidateK := literalMatrix candidateKData

def candidateLData : List (List ℚ) := [
  [1, 0, 0, 0, 0, 0],
  [(1080613 / 1327511), 1, 0, 0, 0, 0],
  [(-1295294 / 1327511), (1024579228217 / 1555515717420), 1, 0, 0, 0],
  [(-2809754 / 3982533), (-93941444155 / 77775785871), (141527149978958480 / 1958360045461650301), 1, 0, 0],
  [(-4161301 / 3982533), (-676044394639 / 518505239140), (-3898976154335161821 / 1958360045461650301), (17326649157141831981575 / 904493942631276149014996), 1, 0],
  [(-3865510 / 3982533), (-52439259997 / 155551571742), (-22377053694484130 / 1958360045461650301), (-1493877740660299527370171 / 904493942631276149014996), (1425239014621759655886088789 / 169672809748432952560313382), 1]
]

def candidateL := literalMatrix candidateLData

def candidateDData : List ℚ := [(3982533 / 100000000), (77775785871 / 6637555000000), (1958360045461650301 / 155551571742000000000), (226123485657819037253749 / 36719250852405943143750000), (84836404874216476280156691 / 1130617428289095186268745000000), (9790856746765097002909144645901 / 1696728097484329525603133820000000)]

def candidateD (i : Fin 3 × Fin 2) : ℚ := candidateDData.getD (coordinateRank i) 0

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.Descent
