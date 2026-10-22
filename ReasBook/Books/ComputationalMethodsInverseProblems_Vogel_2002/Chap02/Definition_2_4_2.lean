/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_4_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_27
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_28
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_17.PoissonLikelihood
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Exercise_9_13.NegLogLikelihood
public import Mathlib.Analysis.InnerProductSpace.Basic

public section

/- Definition 2.4.2-extra-1 (1). The least-squares discrepancy clause `(2.51)`
is the residual specialization of the earlier Chapter 2 quadratic penalty:
`(g₁, g₂) ↦ quadraticPenalty (g₁ - g₂)`. -/
section

universe u

variable {H₂ : Type u} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]

#check (fun p : H₂ × H₂ ↦ quadraticPenalty (p.1 - p.2))

end

/- Companion formula anchor for the defining equation of `(2.51)`. -/
#check quadraticPenalty_def

/- Definition 2.4.2-extra-1 (2). Source-facing blocker/check-only entry for the
Kullback-Leibler discrepancy clause `(2.52)`.

The source requires an admissible Chapter 2 set `𝒞` from Example 2.27 or
Example 2.28 together with a faithful meaning for `log (g₁ / g₂)`. The current
repository snapshot exposes only the underlying nonnegativity-domain examples,
not the missing shared admissible/log-domain owner. The `#check` below records
those verified Chapter 2 anchors without replacing the clause by the
measure-level `InformationTheory.klDiv` owner. -/
#check
  (let _ := EuclideanQuadrant.isClosed_nonnegativeOrthant
   let _ := RealL2.aeNonneg_set_eq_Ici
   PUnit.unit)

/- Definition 2.4.2-extra-1 (3). Source-facing blocker/check-only entry for the
negative Poisson log-likelihood clause `(2.53)`.

The source formula
`ρ_LHD (g₁, g₂) = ⟪g₁, 1⟫ - ⟪g₂, log g₁⟫`
still depends on the same unresolved Chapter 2 admissible/log-domain owner and
on an explicit meaning of the constant-one vector/function in the ambient
Hilbert space. The `#check` below records verified later Poisson
negative-log-likelihood analogues already present in the repository, without
identifying them with the Chapter 2 clause. -/
#check
  (let _ := PoissonLikelihood.poissonNegLogLikelihood
   let _ := PoissonInverse.negLogLikelihood
   PUnit.unit)
