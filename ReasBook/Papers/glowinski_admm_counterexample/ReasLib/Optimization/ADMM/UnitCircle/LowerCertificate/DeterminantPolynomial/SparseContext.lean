/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.TargetContext
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.SparseTransform

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

def startSparseLeftCoefficient (j : ℕ) : ℤ :=
  sparseChebCoefficient FirstKind512.tree.get 512 startChebWeight j

def lowerSparseLeftCoefficient (j : ℕ) : ℤ :=
  sparseChebCoefficient FirstKind512.tree.get 512 lowerChebWeight j

theorem startSparseLeftCoefficient_eq (j : ℕ) :
    startSparseLeftCoefficient j = startLeftCoefficient j :=
  sparseChebCoefficient_eq FirstKind512.tree.get 512 FirstKind512.cache_valid
    512 (by rfl) startChebWeight j

theorem lowerSparseLeftCoefficient_eq (j : ℕ) :
    lowerSparseLeftCoefficient j = lowerLeftCoefficient j :=
  sparseChebCoefficient_eq FirstKind512.tree.get 512 FirstKind512.cache_valid
    512 (by rfl) lowerChebWeight j

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
