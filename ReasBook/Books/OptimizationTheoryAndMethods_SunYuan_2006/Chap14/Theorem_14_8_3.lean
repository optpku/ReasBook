/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_5_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_8_extra_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Exercise_14_13

noncomputable section

open Filter
open scoped GeneralizedJacobian

section Chapter14Theorem1483

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "JacobianMap" => Point →L[ℝ] Point

-- Domain sampling pass:
-- * canonical Chapter 14 owners reused here: `LocallyLipschitzAt` and `SemismoothAt` from
--   `Definition_14_8_extra_2`, `generalizedJacobian F` from `Definition_14_8_extra_1`, and
--   `NonsmoothNewtonMethod` from `Algorithm_14_8_extra_5` together with
--   `generalizedNewtonStep` from `Exercise_14_13`
-- * source-facing order bridge reused here: `OrderSemismoothAt`, `semismoothRemainderFilter`,
--   and `semismoothRemainder` from `Definition_14_8_extra_4`
-- * upstream directional-derivative owner reused through that file:
--   `HasOneSidedDirectionalDerivAt` and `oneSidedDirectionalDeriv`
-- * theorem-local layer here: Newton iteration well-definedness on closed balls, together with
--   the local convergence and source-facing error-estimate owners built on the canonical
--   Chapter 1 owner `HasQOrderConvergenceTo`

/-- The local hypotheses for semismooth Newton at the source solution `xStar`: `F xStar = 0`,
`F` is semismooth at `xStar`, and every element of the canonical generalized Jacobian
`(∂ F) xStar = ∂F(xStar)` is invertible. -/
structure HasSemismoothNewtonLocalConvergenceAssumptions
    (F : Point → Point) (xStar : Point) : Prop where
  map_eq_zero : F xStar = 0
  semismoothAt : SemismoothAt F xStar
  jacobian_isInvertible {V : JacobianMap} (_ : V ∈ (∂ F) xStar) : V.IsInvertible

/-- A radius `r` is a semismooth Newton well-defined neighborhood of `xStar` when every point of
`Metric.closedBall xStar r` admits at least one generalized-Jacobian choice, every allowed choice
there is invertible, and every corresponding semismooth Newton step `(14.8.18)` stays in that
closed ball. Hence admissible semismooth Newton selections exist and remain admissible in the
neighborhood. -/
structure SemismoothNewtonWellDefinedOnClosedBall
    (F : Point → Point) (xStar : Point) (r : ℝ) : Prop where
  /-- Every point of `Metric.closedBall xStar r` admits at least one generalized-Jacobian choice,
  so the local semismooth Newton method has an admissible operator to select there. -/
  selectedOperator_nonempty {x : Point} (_ : x ∈ Metric.closedBall xStar r) :
    ((∂ F) x).Nonempty
  /-- Every allowed generalized-Jacobian element on `Metric.closedBall xStar r` is invertible,
  so the source Newton step is genuinely defined for arbitrary selections there. -/
  selectedOperator_isInvertible {x : Point} (_ : x ∈ Metric.closedBall xStar r)
      {V : JacobianMap} (_ : V ∈ (∂ F) x) : V.IsInvertible
  /-- Every semismooth Newton step produced by an allowed generalized-Jacobian choice at a point
  of `Metric.closedBall xStar r` stays in that closed ball. -/
  step_mem_closedBall {x : Point} (hx : x ∈ Metric.closedBall xStar r)
      {V : JacobianMap} (hV : V ∈ (∂ F) x) :
      generalizedNewtonStep F x V (selectedOperator_isInvertible hx hV) ∈
        Metric.closedBall xStar r

/-- A closed ball centered at `xStar` is a semismooth Newton well-defined neighborhood exactly
when every point in the ball admits an allowed generalized-Jacobian choice, every such choice is
invertible, and every corresponding semismooth Newton step stays in the ball. -/
theorem semismoothNewtonWellDefinedOnClosedBall_iff
    (F : Point → Point) (xStar : Point) (r : ℝ) :
    SemismoothNewtonWellDefinedOnClosedBall F xStar r ↔
      (∀ ⦃x : Point⦄, x ∈ Metric.closedBall xStar r →
        ((∂ F) x).Nonempty) ∧
      (∀ ⦃x : Point⦄, x ∈ Metric.closedBall xStar r →
        ∀ ⦃V : JacobianMap⦄, V ∈ (∂ F) x → V.IsInvertible) ∧
      (∀ ⦃x : Point⦄, x ∈ Metric.closedBall xStar r →
        ∀ ⦃V : JacobianMap⦄, (hV : V ∈ (∂ F) x) → (hVInv : V.IsInvertible) →
          generalizedNewtonStep F x V hVInv ∈
            Metric.closedBall xStar r) := sorry

/-- `SemismoothNewtonConvergesOnClosedBall F xStar r` means that the
semismooth Newton method `(14.8.18)` is well-defined on `Metric.closedBall xStar r` and every
semismooth Newton method for `F` whose initial point lies there converges to `xStar`. -/
class SemismoothNewtonConvergesOnClosedBall
    (F : Point → Point) (xStar : Point) (r : ℝ) : Prop where
  /-- The semismooth Newton method is well-defined on `Metric.closedBall xStar r`. -/
  wellDefined :
    SemismoothNewtonWellDefinedOnClosedBall F xStar r
  /-- Every semismooth Newton method for `F` started in `Metric.closedBall xStar r` converges
  to `xStar`. -/
  tendsto_of_method (method : NonsmoothNewtonMethod n)
      (_ : method.map = F)
      (_ : method.initialPoint ∈ Metric.closedBall xStar r) :
      Tendsto method.iterate atTop (nhds xStar)

/-- `SemismoothNewtonConvergesOnClosedBall F xStar r` holds exactly when
the semismooth Newton method `(14.8.18)` is well-defined on `Metric.closedBall xStar r` and
every semismooth Newton method for `F` whose initial point lies there converges to `xStar`. -/
theorem semismoothNewtonConvergesOnClosedBall_iff
    (F : Point → Point) (xStar : Point) (r : ℝ) :
    SemismoothNewtonConvergesOnClosedBall F xStar r ↔
      SemismoothNewtonWellDefinedOnClosedBall F xStar r ∧
      (∀ method : NonsmoothNewtonMethod n,
        method.map = F →
        method.initialPoint ∈ Metric.closedBall xStar r →
          Tendsto method.iterate atTop (nhds xStar)) := sorry

/-- `SemismoothNewtonHasEventualRpowErrorEstimateOnClosedBall F xStar p r` means
that the semismooth Newton method `(14.8.18)` is well-defined on `Metric.closedBall xStar r`
and every semismooth Newton method for `F` whose initial point lies there satisfies the textbook
eventual estimate `‖x_(k + 1) - xStar‖ ≤ C * ‖x_k - xStar‖^(1 + p)` on a tail. This is the
source-facing local-rate owner for Theorem 14.8.3. -/
class SemismoothNewtonHasEventualRpowErrorEstimateOnClosedBall
    (F : Point → Point) (xStar : Point) (p r : ℝ) : Prop where
  /-- The semismooth Newton method is well-defined on `Metric.closedBall xStar r`. -/
  wellDefined :
    SemismoothNewtonWellDefinedOnClosedBall F xStar r
  /-- Every semismooth Newton method for `F` started in `Metric.closedBall xStar r` satisfies
  the eventual error estimate
  `‖x_(k + 1) - xStar‖ ≤ C * ‖x_k - xStar‖^(1 + p)` on a tail. -/
  hasEventualRpowErrorEstimateTo_of_method (method : NonsmoothNewtonMethod n)
      (_ : method.map = F)
      (_ : method.initialPoint ∈ Metric.closedBall xStar r) :
      ∃ C ∈ Set.Ioi (0 : ℝ),
        ∀ᶠ k in atTop,
          ‖method.iterate (k + 1) - xStar‖ ≤
            C * Real.rpow ‖method.iterate k - xStar‖ (1 + p)

/-- `SemismoothNewtonHasEventualRpowErrorEstimateOnClosedBall F xStar p r` holds
exactly when the semismooth Newton method `(14.8.18)` is well-defined on
`Metric.closedBall xStar r` and every semismooth Newton method for `F` whose initial point lies
there satisfies the textbook eventual estimate
`‖x_(k + 1) - xStar‖ ≤ C * ‖x_k - xStar‖^(1 + p)` on a tail. -/
theorem semismoothNewtonHasEventualRpowErrorEstimateOnClosedBall_iff
    (F : Point → Point) (xStar : Point) (p r : ℝ) :
    SemismoothNewtonHasEventualRpowErrorEstimateOnClosedBall F xStar p r ↔
      SemismoothNewtonWellDefinedOnClosedBall F xStar r ∧
      (∀ method : NonsmoothNewtonMethod n,
        method.map = F →
        method.initialPoint ∈ Metric.closedBall xStar r →
          ∃ C ∈ Set.Ioi (0 : ℝ),
            ∀ᶠ k in atTop,
              ‖method.iterate (k + 1) - xStar‖ ≤
                C * Real.rpow ‖method.iterate k - xStar‖ (1 + p)) := sorry

/-- `SemismoothNewtonHasQOrderConvergenceOnClosedBall F xStar p r` is the canonical Chapter 1
strengthening of the source-facing eventual-error-estimate owner: every admissible semismooth
Newton method on the closed ball has `Q`-order convergence of order `1 + p` relative to
`xStar`, and therefore satisfies the textbook eventual estimate by the Chapter 1 bridge theorem
`HasQOrderConvergenceTo.hasEventualRpowErrorEstimateTo`. -/
class SemismoothNewtonHasQOrderConvergenceOnClosedBall
    (F : Point → Point) (xStar : Point) (p r : ℝ) : Prop where
  /-- The semismooth Newton method is well-defined on `Metric.closedBall xStar r`. -/
  wellDefined :
    SemismoothNewtonWellDefinedOnClosedBall F xStar r
  /-- Every semismooth Newton method for `F` started in `Metric.closedBall xStar r` has the
  canonical Chapter 1 `Q`-order convergence of order `1 + p` relative to `xStar`. -/
  hasQOrderConvergenceTo_of_method (method : NonsmoothNewtonMethod n)
      (_ : method.map = F)
      (_ : method.initialPoint ∈ Metric.closedBall xStar r) :
      ∃ β : ℝ, HasQOrderConvergenceTo method.iterate xStar (1 + p) β

/-- `SemismoothNewtonHasQOrderConvergenceOnClosedBall F xStar p r` holds
exactly when the semismooth Newton method `(14.8.18)` is well-defined on
`Metric.closedBall xStar r` and every semismooth Newton method for `F` whose initial point lies
there has the canonical Chapter 1 `Q`-order convergence of order `1 + p` relative to `xStar`. -/
theorem semismoothNewtonHasQOrderConvergenceOnClosedBall_iff
    (F : Point → Point) (xStar : Point) (p r : ℝ) :
    SemismoothNewtonHasQOrderConvergenceOnClosedBall F xStar p r ↔
      SemismoothNewtonWellDefinedOnClosedBall F xStar r ∧
      (∀ method : NonsmoothNewtonMethod n,
        method.map = F →
        method.initialPoint ∈ Metric.closedBall xStar r →
          ∃ β : ℝ, HasQOrderConvergenceTo method.iterate xStar (1 + p) β) := sorry

/-- The canonical Chapter 1 `Q`-order basin refines to the source-facing eventual error estimate
basin on the same closed ball. -/
instance
    semismoothNewtonHasEventualRpowErrorEstimateOnClosedBall_of_hasQOrderConvergenceOnClosedBall
    {F : Point → Point} {xStar : Point} {p r : ℝ}
    [h : SemismoothNewtonHasQOrderConvergenceOnClosedBall F xStar p r] :
    SemismoothNewtonHasEventualRpowErrorEstimateOnClosedBall F xStar p r where
  wellDefined := h.wellDefined
  hasEventualRpowErrorEstimateTo_of_method method h_map h_initial := by
    rcases h.hasQOrderConvergenceTo_of_method method h_map h_initial with ⟨β, hβ⟩
    exact hβ.hasEventualRpowErrorEstimateTo

/-- Chapter14 Theorem 14.8.3 (1): if `xStar` solves `F x = 0`, `F` is semismooth at `xStar`,
and every `V ∈ (∂ F) xStar = ∂F(xStar)` is invertible, then the semismooth Newton
method `(14.8.18)` is well-defined on some positive-radius closed-ball neighborhood of `xStar`. -/
theorem semismoothNewton_exists_wellDefined_closedBall
    (F : Point → Point) (xStar : Point)
    (h_assumptions : HasSemismoothNewtonLocalConvergenceAssumptions F xStar) :
    ∃ r : ℝ, 0 < r ∧
      SemismoothNewtonWellDefinedOnClosedBall F xStar r := sorry

/-- Chapter14 Theorem 14.8.3 (2): under the same hypotheses, every admissible semismooth Newton
method `(14.8.18)` is convergent to `xStar` on some positive-radius closed-ball neighborhood of
`xStar`. -/
theorem semismoothNewton_exists_converges_closedBall
    (F : Point → Point) (xStar : Point)
    (h_assumptions : HasSemismoothNewtonLocalConvergenceAssumptions F xStar) :
    ∃ r ∈ Set.Ioi (0 : ℝ),
      SemismoothNewtonConvergesOnClosedBall F xStar r := sorry

/-- The canonical Chapter 1 strengthening of Theorem 14.8.3 (3): if, in addition, `F` is
`p`-order semismooth at `xStar`, then on some positive-radius closed-ball neighborhood of
`xStar` every admissible semismooth Newton method has `Q`-order convergence of order `1 + p`.
This stronger owner is kept as a reusable bridge to Chapter 1 rate API. -/
theorem semismoothNewton_exists_qOrderConvergence_closedBall_of_orderSemismooth
    (F : Point → Point) (xStar : Point) (p : ℝ)
    (h_assumptions : HasSemismoothNewtonLocalConvergenceAssumptions F xStar)
    (h_order : OrderSemismoothAt F xStar p) :
    ∃ r ∈ Set.Ioi (0 : ℝ),
      SemismoothNewtonConvergesOnClosedBall F xStar r ∧
      SemismoothNewtonHasQOrderConvergenceOnClosedBall F xStar p r := sorry

/-- Chapter14 Theorem 14.8.3 (3): if, in addition, `F` is `p`-order semismooth at `xStar`, then
the semismooth Newton method `(14.8.18)` is convergent to `xStar` on some positive-radius
closed-ball neighborhood of `xStar`, and every admissible semismooth Newton method on that
neighborhood satisfies the source eventual estimate
`‖x_(k + 1) - xStar‖ ≤ C * ‖x_k - xStar‖^(1 + p)` on a tail. -/
theorem semismoothNewton_exists_orderConvergence_closedBall_of_orderSemismooth
    (F : Point → Point) (xStar : Point) (p : ℝ)
    (h_assumptions : HasSemismoothNewtonLocalConvergenceAssumptions F xStar)
    (h_order : OrderSemismoothAt F xStar p) :
    ∃ r ∈ Set.Ioi (0 : ℝ),
      SemismoothNewtonConvergesOnClosedBall F xStar r ∧
      SemismoothNewtonHasEventualRpowErrorEstimateOnClosedBall F xStar p r := by
  rcases semismoothNewton_exists_qOrderConvergence_closedBall_of_orderSemismooth
      F xStar p h_assumptions h_order with ⟨r, hr, h_converges, h_qOrder⟩
  haveI : SemismoothNewtonHasQOrderConvergenceOnClosedBall F xStar p r := h_qOrder
  exact ⟨r, hr, h_converges, inferInstance⟩

end Chapter14Theorem1483
