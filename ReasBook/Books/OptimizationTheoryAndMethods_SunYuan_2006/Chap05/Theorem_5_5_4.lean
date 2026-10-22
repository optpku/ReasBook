/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Theorem_4_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_5_3
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped BigOperators

noncomputable section

-- Domain sampling for this file:
-- * primary domain: exact-line-search self-scaling variable-metric runs on Euclidean quadratic
--   objectives;
-- * sampled same-domain owners in the minimal closure:
--   `SelfScalingVariableMetricMethod`,
--   `GeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay`,
--   `DfpMethod.IsExactLineSearchOnQuadratic`, and
--   `GeneralQuasiNewtonMethod.IsBroydenClassMethod`;
-- * best owner abstraction: `SelfScalingVariableMetricMethod`, with the theorem-specific
--   quadratic exact-line-search data factored into `IsExactLineSearchOnQuadratic`;
-- * primitive data already owned upstream: the SSVM run data itself and the exact-line-search
--   owner on nonnegative rays;
-- * derived API kept here: only the quadratic exact-line-search specialization, while the
--   eigenvalue product in `(5.5.22)` is stated directly through the canonical finite interval
--   product on `Finset.Icc`.

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- Chapter05 Theorem 5.5.4 (1): if `H` is positive definite, `dotProduct s y > 0`, `φ ≥ 0`,
and `γ > 0`, then the SSVM update `ssvmInverseUpdate H s y φ γ` is positive definite. -/
theorem ssvmInverseUpdate_posDef
    (H : MatrixN) (hH : H.PosDef) (s y : Point) (φ γ : ℝ)
    (hφ : 0 ≤ φ) (hγ : 0 < γ) (hsy : 0 < dotProduct s y) :
    (ssvmInverseUpdate H s y φ γ).PosDef := sorry

section QuadraticSsvmMethod

variable {G : MatrixN} {b : Point} {c : ℝ}

local notation "f" => quadraticObjective G b c

namespace SelfScalingVariableMetricMethod

/-- An SSVM run for `quadraticObjective G b c` satisfies the Theorem 5.5.4 hypotheses when the
quadratic Hessian `G` is symmetric and every nonterminal stage uses exact line search on
`Set.Ici 0` with positive secant curvature. The SSVM-specific update law and denominator data
remain owned by `SelfScalingVariableMetricMethod` itself, while exact line search is reused from
the canonical Chapter 5 owner `A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay`. -/
structure IsExactLineSearchOnQuadratic
    (A : SelfScalingVariableMetricMethod f) : Prop
    extends A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay where
  hessian_symm : G.IsSymm
  secantDotPos :
    ∀ k : ℕ, A.ε < ‖A.g k‖ →
      0 < dotProduct (broydenStep A k) (broydenSecant A.g k)

/-- The predicate `IsExactLineSearchOnQuadratic` is proof-irrelevant. -/
instance isExactLineSearchOnQuadratic_subsingleton
    {A : SelfScalingVariableMetricMethod f} :
    Subsingleton (A.IsExactLineSearchOnQuadratic) := inferInstance

end SelfScalingVariableMetricMethod

open SelfScalingVariableMetricMethod

/-- Chapter05 Theorem 5.5.4 (2): for a quadratic objective with symmetric Hessian matrix `G`,
the first `n` step vectors `broydenStep A k` produced by an SSVM method are pairwise
`G`-conjugate, namely `dotProduct (broydenStep A i) (G.mulVec (broydenStep A j)) = 0`
whenever `i ≠ j`. -/
theorem ssvmMethod_conjugateSteps
    (A : SelfScalingVariableMetricMethod f)
    (hSSVM : A.IsExactLineSearchOnQuadratic)
    (hGenerated : A.toGeneralQuasiNewtonMethod.GeneratedThrough n)
    (i j : ℕ) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    dotProduct (broydenStep A i) (G.mulVec (broydenStep A j)) = 0 := sorry

/-- Chapter05 Theorem 5.5.4 (3): for a quadratic objective with symmetric Hessian matrix `G`,
each generated stage `k` has every step vector `broydenStep A i` with `i ≤ k` as an
eigenvector of `(A.matrix (k + 1)) * G` with eigenvalue
`(Finset.Icc (i + 1) k).prod A.gamma`. -/
theorem ssvmMethod_step_eigenvector
    (A : SelfScalingVariableMetricMethod f)
    (hSSVM : A.IsExactLineSearchOnQuadratic)
    (hGenerated : A.toGeneralQuasiNewtonMethod.GeneratedThrough n)
    (i k : ℕ) (hik : i ≤ k) (hk : k < n) :
    (A.matrix (k + 1)).mulVec (G.mulVec (broydenStep A i)) =
      (Finset.Icc (i + 1) k).prod A.gamma • broydenStep A i := sorry

end QuadraticSsvmMethod

end
