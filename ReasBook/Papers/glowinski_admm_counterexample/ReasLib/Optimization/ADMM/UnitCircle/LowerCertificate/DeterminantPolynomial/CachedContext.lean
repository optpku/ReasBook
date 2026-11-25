/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.SparseContext
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.CoefficientCache.Proof

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

open scoped BigOperators

/-- The degree/parity guards and the two-level coefficient cache change only
computation time. Every stored coefficient is definitionally the certified row. -/
def cachedChebCoefficient (c : Fin 513 → ℤ) (j : ℕ) : ℤ :=
  ∑ k : Fin 513, if j ≤ (k : ℕ) ∧ (k : ℕ) % 2 = j % 2 then
    c k * CoefficientCache.coefficient k j else 0

theorem cachedChebCoefficient_eq (c : Fin 513 → ℤ) (j : ℕ) :
    cachedChebCoefficient c j =
      sparseChebCoefficient FirstKind512.tree.get 512 c j := by
  apply Finset.sum_congr rfl
  intro k _
  rw [CoefficientCache.coefficient_correct]

def startCachedLeftCoefficient (j : ℕ) : ℤ :=
  cachedChebCoefficient startChebWeight j

def lowerCachedLeftCoefficient (j : ℕ) : ℤ :=
  cachedChebCoefficient lowerChebWeight j

theorem startCachedLeftCoefficient_eq (j : ℕ) :
    startCachedLeftCoefficient j = startLeftCoefficient j := by
  rw [startCachedLeftCoefficient, cachedChebCoefficient_eq]
  exact startSparseLeftCoefficient_eq j

theorem lowerCachedLeftCoefficient_eq (j : ℕ) :
    lowerCachedLeftCoefficient j = lowerLeftCoefficient j := by
  rw [lowerCachedLeftCoefficient, cachedChebCoefficient_eq]
  exact lowerSparseLeftCoefficient_eq j

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
