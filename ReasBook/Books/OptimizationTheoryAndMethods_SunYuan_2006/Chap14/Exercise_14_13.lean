/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Lipschitz
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_1_extra_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Algorithm_14_8_extra_5
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_8_extra_2

noncomputable section

open Filter
open scoped GeneralizedJacobian BigOperators

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "Operator" => E →L[ℝ] E

-- Domain-style sampling:
-- * primary domain: Clarke-stationary generalized Newton methods for nonsmooth optimization on
--   real normed spaces
-- * sampled project declarations in this domain:
--   `IsClarkeStationaryPoint` from `Definition_14_1_extra_4`,
--   `generalizedJacobian` / `(∂ Φ) x` from `Definition_14_8_extra_1` and
--   `Definition_14_8_extra_2`,
--   and the Euclidean matrix bridge `NonsmoothNewtonMethod` from `Algorithm_14_8_extra_5`
-- * best owner abstraction: the intrinsic generalized-Jacobian/operator layer on a real normed
--   space, with `generalizedJacobian` as the core owner and `NonsmoothNewtonMethod` retained
--   only as the Euclidean bridge/view
-- * source-facing owner introduced here: the damped optimization-facing owner
--   `GeneralizedNewtonLineSearchMethod E`, whose stationarity-map zeros are Clarke stationary
--   for the recorded objective
-- * core/canonical owners refined here: `generalizedNewtonStep`,
--   `generalizedNewtonLineSearchStep`, `IsUniqueZeroOnClosedBall`, and the closed-ball/local
--   estimate packages for the stationarity map, all on the intrinsic space `E`
-- * primitive data: the objective, the stationarity map, the iterate sequence, the selected
--   generalized-Jacobian operators, and the accepted step sizes
-- * derived API: the damped update law, the bounded stationary-cluster convergence criterion,
--   and convergence conclusions whose limits are Clarke stationary points

/-- The generalized Newton update `x - V⁻¹(F x)` for an invertible selected
generalized-Jacobian element `V`. -/
def generalizedNewtonStep
    (F : E → E) (x : E) (V : Operator) (_ : V.IsInvertible) : E :=
  x - V.inverse (F x)

/-- Unfolding `generalizedNewtonStep F x V hV` gives the source formula `x - V⁻¹(F x)`. -/
@[simp] theorem generalizedNewtonStep_eq
    (F : E → E) (x : E) (V : Operator) (hV : V.IsInvertible) :
    generalizedNewtonStep F x V hV = x - V.inverse (F x) :=
  rfl

/-- The damped generalized Newton update `x - α • V⁻¹(F x)` used by the line-search
globalization. -/
def generalizedNewtonLineSearchStep
    (F : E → E) (x : E) (V : Operator) (_ : V.IsInvertible) (α : ℝ) : E :=
  x - α • V.inverse (F x)

/-- Unfolding `generalizedNewtonLineSearchStep F x V hV α` gives the source damped update
`x - α • V⁻¹(F x)`. -/
@[simp] theorem generalizedNewtonLineSearchStep_eq
    (F : E → E) (x : E) (V : Operator) (hV : V.IsInvertible) (α : ℝ) :
    generalizedNewtonLineSearchStep F x V hV α = x - α • V.inverse (F x) :=
  rfl

/-- A line-search generalized Newton method for Chapter14 Exercise 14.13 (2) records a
stationarity map for a nonsmooth
objective `f : E → ℝ` records a stationarity map `Φ : E → E`, an iterate sequence `x_k`, invertible
selected generalized-Jacobian operators `V_k ∈ (∂ Φ) (x_k)`, and accepted step sizes
`α_k ∈ (0, 1]` satisfying the damped update
`x_(k + 1) = x_k - α_k • V_k⁻¹(Φ(x_k))`. The optimization-facing datum is that every zero of
`Φ` is a Clarke stationary point of `f`; the textbook `ℝ^n` case is recovered by specializing
`E := EuclideanSpace ℝ (Fin n)`. Merit-function globalization conditions are kept separate from
this owner. -/
structure GeneralizedNewtonLineSearchMethod (X : Type u)
    [NormedAddCommGroup X] [NormedSpace ℝ X] where
  objective : X → ℝ
  stationarityMap : X → X
  iterate : ℕ → X
  selectedOperator : ℕ → X →L[ℝ] X
  selectedOperator_mem (k : ℕ) :
    selectedOperator k ∈ (∂ stationarityMap) (iterate k)
  selectedOperator_isInvertible (k : ℕ) : (selectedOperator k).IsInvertible
  stepSize : ℕ → ℝ
  stepSize_pos (k : ℕ) : 0 < stepSize k
  stepSize_le_one (k : ℕ) : stepSize k ≤ 1
  iterate_succ (k : ℕ) :
    iterate (k + 1) =
      generalizedNewtonLineSearchStep
        stationarityMap (iterate k) (selectedOperator k) (selectedOperator_isInvertible k)
        (stepSize k)
  stationary_of_map_eq_zero {x : X} :
    stationarityMap x = 0 → IsClarkeStationaryPoint objective x

end

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "Operator" => E →L[ℝ] E

namespace GeneralizedNewtonLineSearchMethod

/-- A generalized Newton line-search method can be evaluated at stage `k` as its iterate `x_k`.
-/
instance : CoeFun (_root_.GeneralizedNewtonLineSearchMethod E) (fun _ ↦ ℕ → E) where
  coe method := method.iterate

/-- Evaluating `method` as a function returns its iterate sequence. -/
theorem coe_apply (method : _root_.GeneralizedNewtonLineSearchMethod E) (k : ℕ) :
    method k = method.iterate k :=
  rfl

/-- The initial point of a generalized Newton line-search method is its stage-`0` iterate. -/
abbrev initialPoint (method : GeneralizedNewtonLineSearchMethod E) : E := method.iterate 0

/-- The objective value recorded at stage `k` is `method.objective (method.iterate k)`. -/
def objectiveValueAt (method : GeneralizedNewtonLineSearchMethod E) (k : ℕ) : ℝ :=
  method.objective (method.iterate k)

/-- Unfolding `method.objectiveValueAt k` gives the source objective value `f(x_k)`. -/
@[simp] theorem objectiveValueAt_eq
    (method : GeneralizedNewtonLineSearchMethod E) (k : ℕ) :
    method.objectiveValueAt k = method.objective (method.iterate k) :=
  rfl

/-- At each stage `k`, the selected operator belongs to the generalized Jacobian of the
stationarity map at the current iterate. -/
theorem selectedOperator_mem_at
    (method : GeneralizedNewtonLineSearchMethod E) (k : ℕ) :
    method.selectedOperator k ∈ (∂ method.stationarityMap) (method.iterate k) :=
  method.selectedOperator_mem k

/-- At each stage `k`, the selected operator is invertible. -/
theorem selectedOperator_isInvertible_at
    (method : GeneralizedNewtonLineSearchMethod E) (k : ℕ) :
    (method.selectedOperator k).IsInvertible :=
  method.selectedOperator_isInvertible k

/-- At each stage `k`, the accepted stepsize lies in the source interval `(0, 1]`. -/
theorem stepSize_mem_Ioc
    (method : GeneralizedNewtonLineSearchMethod E) (k : ℕ) :
    method.stepSize k ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨method.stepSize_pos k, method.stepSize_le_one k⟩

/-- The recorded iterate sequence satisfies the damped generalized Newton update
`x_(k + 1) = x_k - α_k • V_k⁻¹(Φ(x_k))`. -/
theorem iterate_succ_eq
    (method : GeneralizedNewtonLineSearchMethod E) (k : ℕ) :
    method.iterate (k + 1) =
      generalizedNewtonLineSearchStep
        method.stationarityMap
        (method.iterate k)
        (method.selectedOperator k)
        (method.selectedOperator_isInvertible_at k)
        (method.stepSize k) := by
  simpa using method.iterate_succ k

/-- Every zero of the recorded stationarity map is Clarke stationary for the recorded objective.
-/
theorem isClarkeStationaryPoint_of_stationarityMap_eq_zero
    (method : GeneralizedNewtonLineSearchMethod E) {x : E}
    (hx : method.stationarityMap x = 0) :
    IsClarkeStationaryPoint method.objective x :=
  method.stationary_of_map_eq_zero hx

/-- `method.HasBoundedStationaryClusterCriterion xStar` means that the iterates of `method`
stay in a fixed closed ball around their initial point, every cluster point of the iterate
sequence is Clarke stationary for `method.objective`, and `xStar` is the unique cluster point.
This is the source-facing stationary-cluster criterion used for the line-search convergence
statement in Exercise 14.13 (2); it does not claim a separate globalization mechanism. -/
class HasBoundedStationaryClusterCriterion
    (method : GeneralizedNewtonLineSearchMethod E) (xStar : E) : Prop where
  isClusterPt : MapClusterPt xStar atTop method.iterate
  stationary_of_mapClusterPt
      (y : E) (_ : MapClusterPt y atTop method.iterate) :
      IsClarkeStationaryPoint method.objective y
  eq_of_mapClusterPt
      (y : E) (_ : MapClusterPt y atTop method.iterate) :
      y = xStar
  iterates_bounded :
    ∃ R : ℝ, ∀ k : ℕ, method.iterate k ∈ Metric.closedBall method.initialPoint R

namespace HasBoundedStationaryClusterCriterion

/-- The distinguished cluster point `xStar` is Clarke stationary for `method.objective`. -/
theorem stationary
    {method : GeneralizedNewtonLineSearchMethod E} {xStar : E}
    (h : method.HasBoundedStationaryClusterCriterion xStar) :
    IsClarkeStationaryPoint method.objective xStar :=
  h.stationary_of_mapClusterPt xStar h.isClusterPt

end HasBoundedStationaryClusterCriterion
end GeneralizedNewtonLineSearchMethod

/-- `xStar` is the unique zero of `Φ` in the closed ball `Metric.closedBall x0 r`. This is the
intrinsic closed-ball uniqueness owner used by the generalized Newton convergence statements. -/
class IsUniqueZeroOnClosedBall
    (Φ : E → E) (x0 : E) (r : ℝ) (xStar : E) : Prop where
  mem_closedBall : xStar ∈ Metric.closedBall x0 r
  map_eq_zero : Φ xStar = 0
  eq_of_mem_closedBall_of_map_eq_zero
      (y : E) (_ : y ∈ Metric.closedBall x0 r) (_ : Φ y = 0) :
      y = xStar

namespace IsUniqueZeroOnClosedBall

/-- On the closed ball, every zero of `Φ` coincides with the distinguished point `xStar`. -/
theorem eq_of_map_eq_zero
    {Y : Type u} [NormedAddCommGroup Y]
    {Φ : Y → Y} {x0 xStar y : Y} {r : ℝ}
    (h : IsUniqueZeroOnClosedBall Φ x0 r xStar)
    (hy : y ∈ Metric.closedBall x0 r) (hΦ : Φ y = 0) :
    y = xStar :=
  h.eq_of_mem_closedBall_of_map_eq_zero y hy hΦ

/-- On the closed ball, the vanishing condition `Φ y = 0` is equivalent to `y = xStar`. -/
@[simp] theorem map_eq_zero_iff
    {Y : Type u} [NormedAddCommGroup Y]
    {Φ : Y → Y} {x0 xStar y : Y} {r : ℝ}
    (h : IsUniqueZeroOnClosedBall Φ x0 r xStar)
    (hy : y ∈ Metric.closedBall x0 r) :
    Φ y = 0 ↔ y = xStar := by
  constructor
  · intro hΦ
    exact h.eq_of_map_eq_zero hy hΦ
  · intro hyx
    simpa [hyx] using h.map_eq_zero

end IsUniqueZeroOnClosedBall

/-- The closed-ball convergence hypotheses for the generalized Newton iteration on
`Metric.closedBall x₀ r`: every selected generalized-Jacobian element is invertible with inverse
norm bounded by `β`, the explicit semiderivative model `semideriv x h` for `Φ` satisfies the
source linearization and remainder bounds with constants `γ` and `δ`, the contraction factor
`β * (γ + δ)` is strictly less than `1`, and the initial residual bound holds. The unique zero
in the closed ball is kept explicit on the theorem interface, rather than hidden inside this
hypothesis package. -/
structure HasGeneralizedNewtonClosedBallConvergenceAssumptions
    (Φ : E → E) (semideriv : E → E → E)
    (x0 : E) (r β γ δ : ℝ) : Prop where
  beta_nonneg : 0 ≤ β
  gamma_nonneg : 0 ≤ γ
  delta_nonneg : 0 ≤ δ
  jacobian_isInvertible {x : E} (_ : x ∈ Metric.closedBall x0 r)
      {V : Operator} (_ : V ∈ (∂ Φ) x) : V.IsInvertible
  inverse_bound {x : E} (_ : x ∈ Metric.closedBall x0 r)
      {V : Operator} (_ : V ∈ (∂ Φ) x) : ‖V.inverse‖ ≤ β
  linearization_bound {x y : E}
      (_ : x ∈ Metric.closedBall x0 r) (_ : y ∈ Metric.closedBall x0 r)
      {V : Operator} (_ : V ∈ (∂ Φ) x) :
      ‖V (y - x) - semideriv x (y - x)‖ ≤ γ * ‖y - x‖
  remainder_bound {x y : E}
      (_ : x ∈ Metric.closedBall x0 r) (_ : y ∈ Metric.closedBall x0 r) :
      ‖Φ y - Φ x - semideriv x (y - x)‖ ≤ δ * ‖y - x‖
  contraction_lt_one : β * (γ + δ) < 1
  initial_residual_bound : β * ‖Φ x0‖ ≤ r * (1 - β * (γ + δ))

/-- If `xStar` is the unique zero of the stationarity map `Φ` on a closed ball and every zero of
`Φ` is Clarke stationary for the objective `f`, then `xStar` is Clarke stationary for `f`. -/
theorem IsUniqueZeroOnClosedBall.isClarkeStationaryPoint
    {objective : E → ℝ} {Φ : E → E} {x0 xStar : E} {r : ℝ}
    (h_unique : IsUniqueZeroOnClosedBall Φ x0 r xStar)
    (h_stationary :
      ∀ {x : E}, Φ x = 0 → IsClarkeStationaryPoint objective x) :
    IsClarkeStationaryPoint objective xStar :=
  h_stationary h_unique.map_eq_zero

/-- For Chapter14 Exercise 14.13 (2), if a line-search generalized Newton method satisfies the
bounded stationary-cluster criterion, then its iterates converge to the unique Clarke stationary
cluster point `xStar`. -/
theorem generalizedNewtonLineSearch_tendsto_of_boundedStationaryClusterCriterion
    [ProperSpace E]
    (method : GeneralizedNewtonLineSearchMethod E) (xStar : E)
    (h_assumptions :
      method.HasBoundedStationaryClusterCriterion xStar) :
    Tendsto method.iterate atTop (nhds xStar) ∧
      IsClarkeStationaryPoint method.objective xStar := by
  rcases h_assumptions.iterates_bounded with ⟨R, h_iterate_mem⟩
  let s := Metric.closedBall method.initialPoint R
  have hs : IsCompact s := by
    simpa [s] using (ProperSpace.isCompact_closedBall method.initialPoint R)
  refine ⟨hs.tendsto_nhds_of_unique_mapClusterPt ?_ ?_, h_assumptions.stationary⟩
  · exact Filter.Eventually.of_forall h_iterate_mem
  · intro y hy hyCluster
    exact h_assumptions.eq_of_mapClusterPt y hyCluster

end

section

universe u

variable {E : Type u} [NormedAddCommGroup E]

/-- Helper for Chapter14 Exercise 14.13: iterate a possibly signed scalar contraction by replacing
the factor `q` with the nonnegative majorant `max q 0`. -/
lemma contractionNorm_le_maxPow
    (iterate : ℕ → E) (xStar : E) (q : ℝ)
    (h_contraction :
      ∀ k : ℕ,
        ‖iterate (k + 1) - xStar‖ ≤ q * ‖iterate k - xStar‖) :
    ∀ k : ℕ, ‖iterate k - xStar‖ ≤ (max q 0) ^ k * ‖iterate 0 - xStar‖ := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k hk =>
      -- Replace the possibly signed factor `q` by `max q 0`, then reuse the inductive decay.
      calc
        ‖iterate (k + 1) - xStar‖ ≤ q * ‖iterate k - xStar‖ :=
          h_contraction k
        _ ≤ max q 0 * ‖iterate k - xStar‖ :=
          mul_le_mul_of_nonneg_right (le_max_left q 0) (norm_nonneg _)
        _ ≤ max q 0 * ((max q 0) ^ k * ‖iterate 0 - xStar‖) :=
          mul_le_mul_of_nonneg_left hk (le_max_right q 0)
        _ = (max q 0) ^ (k + 1) * ‖iterate 0 - xStar‖ := by
          ring

/-- A contraction-based convergence helper for generalized Newton: if the iterate sequence
satisfies a uniform contraction estimate toward `xStar`, then the iterates
converge to `xStar`. -/
theorem generalizedNewton_tendsto_of_contraction
    (iterate : ℕ → E) (xStar : E) (q : ℝ)
    (h_q_lt_one : q < 1)
    (h_contraction :
      ∀ k : ℕ,
        ‖iterate (k + 1) - xStar‖ ≤ q * ‖iterate k - xStar‖) :
    Tendsto iterate atTop (nhds xStar) := by
  -- Route correction: normalize the contraction factor to `max q 0` before invoking
  -- geometric-decay convergence.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let q0 : ℝ := max q 0
  have hq0_nonneg : 0 ≤ q0 := le_max_right q 0
  have hq0_lt_one : q0 < 1 := by
    refine max_lt_iff.mpr ?_
    exact ⟨h_q_lt_one, zero_lt_one⟩
  have hbound := contractionNorm_le_maxPow iterate xStar q h_contraction
  have hgeom :
      Tendsto (fun k : ℕ ↦ q0 ^ k * ‖iterate 0 - xStar‖) atTop (nhds 0) := by
    simpa [q0, mul_comm] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0_nonneg hq0_lt_one).const_mul
        ‖iterate 0 - xStar‖
  -- Squeeze the error norms between `0` and the geometric majorant.
  exact squeeze_zero (fun _ ↦ norm_nonneg _) hbound hgeom

end

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "Operator" => E →L[ℝ] E

/-- The local-convergence hypotheses for generalized Newton at a zero `xStar` of `Φ`: on
the closed ball `Metric.closedBall xStar r`, every generalized-Jacobian selection is invertible
with inverse norm bounded by `β`, the explicit local linearization at `xStar` for the
map `Φ` satisfies the source linearization and remainder bounds with constants `γ` and `δ`, and
the contraction factor `β * (γ + δ)` is strictly less than `1`. -/
structure HasGeneralizedNewtonLocalConvergenceAssumptions
    (Φ : E → E) (localSemideriv : Operator)
    (xStar : E) (r β γ δ : ℝ) : Prop where
  radius_pos : 0 < r
  beta_nonneg : 0 ≤ β
  gamma_nonneg : 0 ≤ γ
  delta_nonneg : 0 ≤ δ
  map_eq_zero : Φ xStar = 0
  jacobian_isInvertible {x : E} (_ : x ∈ Metric.closedBall xStar r)
      {V : Operator} (_ : V ∈ (∂ Φ) x) : V.IsInvertible
  inverse_bound {x : E} (_ : x ∈ Metric.closedBall xStar r)
      {V : Operator} (_ : V ∈ (∂ Φ) x) : ‖V.inverse‖ ≤ β
  linearization_bound {x : E} (_ : x ∈ Metric.closedBall xStar r)
      {V : Operator} (_ : V ∈ (∂ Φ) x) :
      ‖V (x - xStar) - localSemideriv (x - xStar)‖ ≤ γ * ‖x - xStar‖
  remainder_bound {x : E} (_ : x ∈ Metric.closedBall xStar r) :
    ‖Φ x - Φ xStar - localSemideriv (x - xStar)‖ ≤ δ * ‖x - xStar‖
  contraction_lt_one : β * (γ + δ) < 1

end

section

variable {n : ℕ}

private abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The earlier Chapter 14 owner `NonsmoothNewtonMethod` satisfies the intrinsic generalized
Newton update when read through its canonical selected operators. -/
theorem NonsmoothNewtonMethod.iterate_succ_eq_generalizedNewtonStep
    (method : NonsmoothNewtonMethod n) (k : ℕ) :
    method.iterate (k + 1) =
      generalizedNewtonStep method.map (method.iterate k) (method.selectedOperator k)
        (method.selectedOperator_isInvertible_at k) := by
  simpa [generalizedNewtonStep, nonsmoothNewtonStep]
    using congrArg id (method.iterate_succ_eq k)

/-- Helper for Chapter14 Exercise 14.13: under the local convergence assumptions, one
generalized Newton step contracts the distance to `xStar` by the factor `β * (γ + δ)`. -/
lemma generalizedNewtonStep_norm_le_ofLocalConvergenceAssumptions
    (method : NonsmoothNewtonMethod n)
    (localSemideriv : Point n →L[ℝ] Point n)
    (xStar : Point n) (r β γ δ : ℝ)
    (h_assumptions :
      HasGeneralizedNewtonLocalConvergenceAssumptions
        method.map localSemideriv xStar r β γ δ)
    {x : Point n}
    (hx : x ∈ Metric.closedBall xStar r)
    {V : Point n →L[ℝ] Point n}
    (hV : V ∈ generalizedJacobian method.map x) :
    ‖generalizedNewtonStep method.map x V (h_assumptions.jacobian_isInvertible hx hV) - xStar‖ ≤
      (β * (γ + δ)) * ‖x - xStar‖ := by
  let hVInv := h_assumptions.jacobian_isInvertible hx hV
  have h_step_eq :
      generalizedNewtonStep method.map x V hVInv - xStar =
        V.inverse (V (x - xStar) - method.map x) := by
    -- Rewrite the Newton update so the whole defect is carried by `V⁻¹`.
    calc
      generalizedNewtonStep method.map x V hVInv - xStar
          = (x - xStar) - V.inverse (method.map x) := by
              simp [generalizedNewtonStep_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = V.inverse (V (x - xStar)) - V.inverse (method.map x) := by
              rw [hVInv.inverse_apply_self]
      _ = V.inverse (V (x - xStar) - method.map x) := by
              simp [map_sub]
  have h_expand :
      V (x - xStar) - method.map x =
        (V (x - xStar) - localSemideriv (x - xStar)) -
          (method.map x - method.map xStar - localSemideriv (x - xStar)) := by
    rw [h_assumptions.map_eq_zero]
    abel
  have h_defect :
      ‖V (x - xStar) - method.map x‖ ≤ (γ + δ) * ‖x - xStar‖ := by
    -- Split the Newton defect into the linearization error and the nonlinear remainder.
    calc
      ‖V (x - xStar) - method.map x‖
          = ‖(V (x - xStar) - localSemideriv (x - xStar)) -
              (method.map x - method.map xStar - localSemideriv (x - xStar))‖ := by
                rw [h_expand]
      _ ≤ ‖V (x - xStar) - localSemideriv (x - xStar)‖ +
            ‖method.map x - method.map xStar - localSemideriv (x - xStar)‖ :=
          norm_sub_le _ _
      _ ≤ γ * ‖x - xStar‖ + δ * ‖x - xStar‖ :=
          add_le_add (h_assumptions.linearization_bound hx hV) (h_assumptions.remainder_bound hx)
      _ = (γ + δ) * ‖x - xStar‖ := by
          ring
  -- Apply the inverse-norm bound after the defect has been normalized.
  calc
    ‖generalizedNewtonStep method.map x V hVInv - xStar‖
        = ‖V.inverse (V (x - xStar) - method.map x)‖ := by
            rw [h_step_eq]
    _ ≤ ‖V.inverse‖ * ‖V (x - xStar) - method.map x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ β * ‖V (x - xStar) - method.map x‖ :=
      mul_le_mul_of_nonneg_right (h_assumptions.inverse_bound hx hV) (norm_nonneg _)
    _ ≤ β * ((γ + δ) * ‖x - xStar‖) :=
      mul_le_mul_of_nonneg_left h_defect h_assumptions.beta_nonneg
    _ = (β * (γ + δ)) * ‖x - xStar‖ := by
      ring

/-- For Chapter14 Exercise 14.13 (3), under the local-convergence assumptions at a zero `xStar` of
the stationarity map `method.map`, if zeros of that map are Clarke stationary for the objective
`f` and the initial point lies in `Metric.closedBall xStar r`, then the generalized Newton
iterates converge locally to the Clarke stationary point `xStar`. -/
theorem generalizedNewton_tendsto_of_localConvergenceAssumptions
    (objective : Point n → ℝ) (method : NonsmoothNewtonMethod n)
    (localSemideriv : Point n →L[ℝ] Point n)
    (xStar : Point n) (r β γ δ : ℝ)
    (h_assumptions :
      HasGeneralizedNewtonLocalConvergenceAssumptions
        method.map localSemideriv xStar r β γ δ)
    (h_stationary :
      ∀ {x : Point n}, method.map x = 0 → IsClarkeStationaryPoint objective x)
    (h_initial : method.initialPoint ∈ Metric.closedBall xStar r) :
    Tendsto method.iterate atTop (nhds xStar) ∧
      IsClarkeStationaryPoint objective xStar := by
  refine ⟨?_, h_stationary h_assumptions.map_eq_zero⟩
  let q : ℝ := β * (γ + δ)
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg h_assumptions.beta_nonneg
      (add_nonneg h_assumptions.gamma_nonneg h_assumptions.delta_nonneg)
  have h_iterate_mem : ∀ k : ℕ, method.iterate k ∈ Metric.closedBall xStar r := by
    intro k
    induction k with
    | zero =>
        simpa [NonsmoothNewtonMethod.initialPoint] using h_initial
    | succ k hk =>
        have hk_step :
            ‖method.iterate (k + 1) - xStar‖ ≤ q * ‖method.iterate k - xStar‖ := by
          -- Apply the one-step local contraction at the current iterate.
          simpa [q, method.iterate_succ_eq_generalizedNewtonStep] using
            generalizedNewtonStep_norm_le_ofLocalConvergenceAssumptions
              (method := method) (localSemideriv := localSemideriv)
              (xStar := xStar) (r := r) (β := β) (γ := γ) (δ := δ)
              h_assumptions hk (method.selectedOperator_mem_at k)
        -- The contraction factor is strictly below `1`, so the closed ball is invariant.
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc
          ‖method.iterate (k + 1) - xStar‖ ≤ q * ‖method.iterate k - xStar‖ :=
            hk_step
          _ ≤ q * r := by
            have hk_norm : ‖method.iterate k - xStar‖ ≤ r := by
              simpa [Metric.mem_closedBall, dist_eq_norm] using hk
            exact mul_le_mul_of_nonneg_left hk_norm hq_nonneg
          _ ≤ r := by
            dsimp [q]
            nlinarith [h_assumptions.radius_pos, h_assumptions.contraction_lt_one]
  have h_contraction :
      ∀ k : ℕ, ‖method.iterate (k + 1) - xStar‖ ≤ q * ‖method.iterate k - xStar‖ := by
    intro k
    -- Reuse the same one-step estimate once the iterate is known to stay in the admissible ball.
    simpa [q, method.iterate_succ_eq_generalizedNewtonStep] using
      generalizedNewtonStep_norm_le_ofLocalConvergenceAssumptions
        (method := method) (localSemideriv := localSemideriv)
        (xStar := xStar) (r := r) (β := β) (γ := γ) (δ := δ)
        h_assumptions (h_iterate_mem k) (method.selectedOperator_mem_at k)
  exact generalizedNewton_tendsto_of_contraction
    method.iterate xStar q h_assumptions.contraction_lt_one h_contraction

/-- Helper for Chapter14 Exercise 14.13: on the closed ball around the initial point, the next
residual is controlled by the current Newton step. -/
lemma generalizedNewtonStep_map_norm_le_ofClosedBallConvergenceAssumptions
    (method : NonsmoothNewtonMethod n)
    (semideriv : Point n → Point n → Point n)
    (r β γ δ : ℝ)
    (h_assumptions :
      HasGeneralizedNewtonClosedBallConvergenceAssumptions
        method.map semideriv method.initialPoint r β γ δ)
    {x xNext : Point n}
    (hx : x ∈ Metric.closedBall method.initialPoint r)
    (hxNext : xNext ∈ Metric.closedBall method.initialPoint r)
    {V : Point n →L[ℝ] Point n}
    (hV : V ∈ generalizedJacobian method.map x)
    (hxNext_eq :
      xNext = generalizedNewtonStep method.map x V (h_assumptions.jacobian_isInvertible hx hV)) :
    ‖method.map xNext‖ ≤ (γ + δ) * ‖xNext - x‖ := by
  let hVInv := h_assumptions.jacobian_isInvertible hx hV
  have h_cancel : V (xNext - x) = -method.map x := by
    -- The Newton step is chosen so that the linearized residual cancels exactly.
    subst hxNext_eq
    calc
      V (generalizedNewtonStep method.map x V hVInv - x)
          = V (-V.inverse (method.map x)) := by
              simp [generalizedNewtonStep_eq, sub_eq_add_neg, add_left_comm, add_comm]
      _ = -V (V.inverse (method.map x)) := by
            simp [map_neg]
      _ = -method.map x := by
            rw [hVInv.self_apply_inverse]
  -- Decompose the new residual into the remainder term and the linearization defect.
  calc
    ‖method.map xNext‖
        = ‖(method.map xNext - method.map x - semideriv x (xNext - x)) -
            (V (xNext - x) - semideriv x (xNext - x))‖ := by
              rw [h_cancel]
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ ≤ ‖method.map xNext - method.map x - semideriv x (xNext - x)‖ +
          ‖V (xNext - x) - semideriv x (xNext - x)‖ :=
      norm_sub_le _ _
    _ ≤ δ * ‖xNext - x‖ + γ * ‖xNext - x‖ :=
      add_le_add
        (h_assumptions.remainder_bound hx hxNext)
        (h_assumptions.linearization_bound hx hxNext hV)
    _ = (γ + δ) * ‖xNext - x‖ := by
      ring

/-- Helper for Chapter14 Exercise 14.13: under the closed-ball assumptions, every iterate stays
in the admissible ball and every Newton step decays geometrically. -/
lemma iterate_mem_closedBall_and_step_norm_le_geom_ofClosedBallConvergenceAssumptions
    (method : NonsmoothNewtonMethod n)
    (semideriv : Point n → Point n → Point n)
    (r β γ δ : ℝ)
    (h_assumptions :
      HasGeneralizedNewtonClosedBallConvergenceAssumptions
        method.map semideriv method.initialPoint r β γ δ) :
    ∀ k : ℕ,
      method.iterate k ∈ Metric.closedBall method.initialPoint r ∧
      ‖method.iterate (k + 1) - method.iterate k‖ ≤
        (β * (γ + δ)) ^ k * (β * ‖method.map method.initialPoint‖) := by
  let q : ℝ := β * (γ + δ)
  let step0 : ℝ := β * ‖method.map method.initialPoint‖
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg h_assumptions.beta_nonneg
      (add_nonneg h_assumptions.gamma_nonneg h_assumptions.delta_nonneg)
  have hstep0_nonneg : 0 ≤ step0 := by
    dsimp [step0]
    exact mul_nonneg h_assumptions.beta_nonneg (norm_nonneg _)
  have h_radius_budget : step0 * (1 - q)⁻¹ ≤ r := by
    -- Rewrite the initial residual estimate into the radius budget used for the geometric path.
    have hbudget_div : step0 / (1 - q) ≤ r := by
      refine (div_le_iff₀ (sub_pos.2 h_assumptions.contraction_lt_one)).2 ?_
      simpa [q, step0, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
        h_assumptions.initial_residual_bound
    simpa [div_eq_mul_inv] using hbudget_div
  have hr_nonneg : 0 ≤ r := by
    exact le_trans
      (mul_nonneg hstep0_nonneg <|
        inv_nonneg.mpr (sub_nonneg.2 (le_of_lt h_assumptions.contraction_lt_one)))
      h_radius_budget
  have hsummable : Summable (fun k : ℕ ↦ q ^ k) :=
    summable_geometric_of_lt_one hq_nonneg h_assumptions.contraction_lt_one
  have hgeom_sum_le :
      ∀ k : ℕ, Finset.sum (Finset.range k) (fun i ↦ q ^ i) ≤ (1 - q)⁻¹ := by
    intro k
    have hpartial :
        Finset.sum (Finset.range k) (fun i ↦ q ^ i) ≤ ∑' i : ℕ, q ^ i :=
      hsummable.sum_le_tsum _ (fun _ _ ↦ pow_nonneg hq_nonneg _)
    simpa [tsum_geometric_of_lt_one hq_nonneg h_assumptions.contraction_lt_one] using hpartial
  have hstep_bound :
      ∀ {x : Point n} (hx : x ∈ Metric.closedBall method.initialPoint r)
        {V : Point n →L[ℝ] Point n} (hV : V ∈ generalizedJacobian method.map x),
        ‖generalizedNewtonStep method.map x V (h_assumptions.jacobian_isInvertible hx hV) - x‖ ≤
          β * ‖method.map x‖ := by
    intro x hx V hV
    let hVInv := h_assumptions.jacobian_isInvertible hx hV
    -- The step size is controlled directly by the inverse-norm bound and the current residual.
    calc
      ‖generalizedNewtonStep method.map x V hVInv - x‖
          = ‖-V.inverse (method.map x)‖ := by
              simp [generalizedNewtonStep_eq, sub_eq_add_neg, add_left_comm, add_comm]
      _ = ‖V.inverse (method.map x)‖ := by
            rw [norm_neg]
      _ ≤ ‖V.inverse‖ * ‖method.map x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ β * ‖method.map x‖ :=
        mul_le_mul_of_nonneg_right (h_assumptions.inverse_bound hx hV) (norm_nonneg _)
  have h_strong :
      ∀ k : ℕ,
        method.iterate k ∈ Metric.closedBall method.initialPoint r ∧
        dist (method.iterate k) method.initialPoint ≤
          step0 * Finset.sum (Finset.range k) (fun i ↦ q ^ i) ∧
        ‖method.iterate (k + 1) - method.iterate k‖ ≤ q ^ k * step0 := by
    intro k
    induction k with
    | zero =>
        have h0_mem : method.initialPoint ∈ Metric.closedBall method.initialPoint r := by
          rw [Metric.mem_closedBall]
          simpa using hr_nonneg
        refine ⟨h0_mem, ?_, ?_⟩
        · simp [step0]
        · -- The first Newton step is bounded by the initial residual budget.
          simpa [q, step0, NonsmoothNewtonMethod.initialPoint,
            method.iterate_succ_eq_generalizedNewtonStep] using
            hstep_bound h0_mem (method.selectedOperator_mem_at 0)
    | succ k hk =>
        rcases hk with ⟨hk_mem, hk_path, hk_step⟩
        have hk1_path :
            dist (method.iterate (k + 1)) method.initialPoint ≤
              step0 * Finset.sum (Finset.range (k + 1)) (fun i ↦ q ^ i) := by
          -- Add the new step length to the previously accumulated path length.
          calc
            dist (method.iterate (k + 1)) method.initialPoint
                ≤ dist (method.iterate (k + 1)) (method.iterate k) +
                    dist (method.iterate k) method.initialPoint :=
              dist_triangle _ _ _
            _ = ‖method.iterate (k + 1) - method.iterate k‖ +
                  dist (method.iterate k) method.initialPoint := by
                    rw [dist_eq_norm]
            _ ≤ ‖method.iterate (k + 1) - method.iterate k‖ +
                  step0 * Finset.sum (Finset.range k) (fun i ↦ q ^ i) :=
              add_le_add le_rfl hk_path
            _ ≤ q ^ k * step0 + step0 * Finset.sum (Finset.range k) (fun i ↦ q ^ i) := by
                  gcongr
            _ = step0 * Finset.sum (Finset.range (k + 1)) (fun i ↦ q ^ i) := by
                  rw [Finset.sum_range_succ]
                  ring
        have hk1_mem : method.iterate (k + 1) ∈ Metric.closedBall method.initialPoint r := by
          -- Compare the accumulated path length with the radius budget.
          rw [Metric.mem_closedBall]
          exact hk1_path.trans <|
            (mul_le_mul_of_nonneg_left (hgeom_sum_le (k + 1)) hstep0_nonneg).trans h_radius_budget
        have hk1_residual :
            ‖method.map (method.iterate (k + 1))‖ ≤
              (γ + δ) * ‖method.iterate (k + 1) - method.iterate k‖ := by
          -- Once the next iterate stays in the ball, the residual recurrence becomes available.
          have hk1_eq :
              method.iterate (k + 1) =
                generalizedNewtonStep method.map (method.iterate k) (method.selectedOperator k)
                  (h_assumptions.jacobian_isInvertible
                    hk_mem
                    (method.selectedOperator_mem_at k)) := by
            simp [method.iterate_succ_eq_generalizedNewtonStep]
          simpa [dist_eq_norm] using
            generalizedNewtonStep_map_norm_le_ofClosedBallConvergenceAssumptions
              (method := method) (semideriv := semideriv)
              (r := r) (β := β) (γ := γ) (δ := δ)
              h_assumptions hk_mem hk1_mem (method.selectedOperator_mem_at k) hk1_eq
        have hk1_step :
            ‖method.iterate (k + 2) - method.iterate (k + 1)‖ ≤ q ^ (k + 1) * step0 := by
          have hk1_step_raw :
              ‖method.iterate (k + 2) - method.iterate (k + 1)‖ ≤
                β * ‖method.map (method.iterate (k + 1))‖ := by
            simpa [method.iterate_succ_eq_generalizedNewtonStep] using
              hstep_bound hk1_mem (method.selectedOperator_mem_at (k + 1))
          -- Combine the inverse bound, the residual recurrence, and the previous geometric step.
          calc
            ‖method.iterate (k + 2) - method.iterate (k + 1)‖ ≤
                β * ‖method.map (method.iterate (k + 1))‖ :=
              hk1_step_raw
            _ ≤ β * ((γ + δ) * ‖method.iterate (k + 1) - method.iterate k‖) :=
              mul_le_mul_of_nonneg_left hk1_residual h_assumptions.beta_nonneg
            _ ≤ β * ((γ + δ) * (q ^ k * step0)) := by
              have hgd_nonneg : 0 ≤ γ + δ :=
                add_nonneg h_assumptions.gamma_nonneg h_assumptions.delta_nonneg
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hk_step hgd_nonneg)
                h_assumptions.beta_nonneg
            _ = q ^ (k + 1) * step0 := by
              dsimp [q]
              ring
        exact ⟨hk1_mem, hk1_path, hk1_step⟩
  intro k
  rcases h_strong k with ⟨hk_mem, _, hk_step⟩
  exact ⟨hk_mem, by simpa [q, step0] using hk_step⟩

/-- Helper for Chapter14 Exercise 14.13: once the iterates stay in the initial closed ball, one
generalized Newton step contracts the distance to the unique zero `xStar`. -/
lemma generalizedNewtonStep_norm_le_ofClosedBallConvergenceAssumptions
    (method : NonsmoothNewtonMethod n)
    (semideriv : Point n → Point n → Point n)
    (xStar : Point n) (r β γ δ : ℝ)
    (h_assumptions :
      HasGeneralizedNewtonClosedBallConvergenceAssumptions
        method.map semideriv method.initialPoint r β γ δ)
    (h_unique :
      IsUniqueZeroOnClosedBall method.map method.initialPoint r xStar)
    {x : Point n}
    (hx : x ∈ Metric.closedBall method.initialPoint r)
    {V : Point n →L[ℝ] Point n}
    (hV : V ∈ generalizedJacobian method.map x) :
    ‖generalizedNewtonStep method.map x V (h_assumptions.jacobian_isInvertible hx hV) - xStar‖ ≤
      (β * (γ + δ)) * ‖x - xStar‖ := by
  let hVInv := h_assumptions.jacobian_isInvertible hx hV
  have h_step_eq :
      generalizedNewtonStep method.map x V hVInv - xStar =
        V.inverse (V (x - xStar) - (method.map x - method.map xStar)) := by
    -- Rewrite the Newton update so the defect is measured against the distinguished zero.
    calc
      generalizedNewtonStep method.map x V hVInv - xStar
          = V.inverse (V (x - xStar) - method.map x) := by
              calc
                generalizedNewtonStep method.map x V hVInv - xStar
                    = (x - xStar) - V.inverse (method.map x) := by
                        simp [generalizedNewtonStep_eq, sub_eq_add_neg, add_assoc, add_left_comm,
                          add_comm]
                _ = V.inverse (V (x - xStar)) - V.inverse (method.map x) := by
                        rw [hVInv.inverse_apply_self]
                _ = V.inverse (V (x - xStar) - method.map x) := by
                        simp [map_sub]
      _ = V.inverse (V (x - xStar) - (method.map x - method.map xStar)) := by
            simp [h_unique.map_eq_zero]
  have h_step_norm_eq :
      ‖generalizedNewtonStep method.map x V hVInv - xStar‖ =
        ‖V.inverse (V (xStar - x) - (method.map xStar - method.map x))‖ := by
    -- Keep the source direction `xStar - x`, which matches the closed-ball assumptions.
    have h_arg :
        V (xStar - x) - (method.map xStar - method.map x) =
          -(V (x - xStar) - (method.map x - method.map xStar)) := by
      simp [sub_eq_add_neg, map_neg, add_assoc, add_left_comm, add_comm]
    have h_arg_inv :
        -V.inverse (V (x - xStar) - (method.map x - method.map xStar)) =
          V.inverse (V (xStar - x) - (method.map xStar - method.map x)) := by
      rw [h_arg]
      simp
    rw [h_step_eq]
    have hnorm :
        ‖V.inverse (V (x - xStar) - (method.map x - method.map xStar))‖ =
          ‖-V.inverse (V (x - xStar) - (method.map x - method.map xStar))‖ := by
      simpa using
        (norm_neg (V.inverse (V (x - xStar) - (method.map x - method.map xStar)))).symm
    exact hnorm.trans (by rw [h_arg_inv])
  have h_linearization :
      ‖V (xStar - x) - semideriv x (xStar - x)‖ ≤ γ * ‖xStar - x‖ :=
    h_assumptions.linearization_bound hx h_unique.mem_closedBall hV
  have h_remainder :
      ‖method.map xStar - method.map x - semideriv x (xStar - x)‖ ≤ δ * ‖xStar - x‖ :=
    h_assumptions.remainder_bound hx h_unique.mem_closedBall
  have h_expand :
      V (xStar - x) - (method.map xStar - method.map x) =
        (V (xStar - x) - semideriv x (xStar - x)) -
          (method.map xStar - method.map x - semideriv x (xStar - x)) := by
    abel
  have h_defect :
      ‖V (xStar - x) - (method.map xStar - method.map x)‖ ≤
        (γ + δ) * ‖xStar - x‖ := by
    -- Sum the linearization error and the nonlinear remainder.
    calc
      ‖V (xStar - x) - (method.map xStar - method.map x)‖
          = ‖(V (xStar - x) - semideriv x (xStar - x)) -
              (method.map xStar - method.map x - semideriv x (xStar - x))‖ := by
                rw [h_expand]
      _ ≤ ‖V (xStar - x) - semideriv x (xStar - x)‖ +
            ‖method.map xStar - method.map x - semideriv x (xStar - x)‖ :=
          norm_sub_le _ _
      _ ≤ γ * ‖xStar - x‖ + δ * ‖xStar - x‖ :=
          add_le_add h_linearization h_remainder
      _ = (γ + δ) * ‖xStar - x‖ := by
          ring
  -- Apply the inverse-norm estimate exactly as in the local case.
  calc
    ‖generalizedNewtonStep method.map x V hVInv - xStar‖
        = ‖V.inverse (V (xStar - x) - (method.map xStar - method.map x))‖ := by
            rw [h_step_norm_eq]
    _ ≤ ‖V.inverse‖ * ‖V (xStar - x) - (method.map xStar - method.map x)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ β * ‖V (xStar - x) - (method.map xStar - method.map x)‖ :=
      mul_le_mul_of_nonneg_right (h_assumptions.inverse_bound hx hV) (norm_nonneg _)
    _ ≤ β * ((γ + δ) * ‖xStar - x‖) :=
      mul_le_mul_of_nonneg_left h_defect h_assumptions.beta_nonneg
    _ = (β * (γ + δ)) * ‖x - xStar‖ := by
      rw [norm_sub_rev, mul_assoc]

/-- Chapter14 Exercise 14.13: a semilocal closed-ball convergence companion for generalized
Newton. If `xStar` is the
unique zero of the stationarity map `method.map` in `Metric.closedBall method.initialPoint r`,
if zeros of that map are Clarke stationary for the objective `f`, and the generalized Newton
iteration satisfies the closed-ball convergence assumptions on that ball, then the generalized
Newton iterates converge to the Clarke stationary point `xStar`. -/
theorem generalizedNewton_tendsto_of_closedBallConvergenceAssumptions
    (objective : Point n → ℝ) (method : NonsmoothNewtonMethod n)
    (semideriv : Point n → Point n → Point n)
    (xStar : Point n) (r β γ δ : ℝ)
    (h_assumptions :
      HasGeneralizedNewtonClosedBallConvergenceAssumptions
        method.map semideriv method.initialPoint r β γ δ)
    (h_stationary :
      ∀ {x : Point n}, method.map x = 0 → IsClarkeStationaryPoint objective x)
    (h_unique :
      IsUniqueZeroOnClosedBall method.map method.initialPoint r xStar) :
    Tendsto method.iterate atTop (nhds xStar) ∧
      IsClarkeStationaryPoint objective xStar := by
  refine ⟨?_, h_unique.isClarkeStationaryPoint h_stationary⟩
  let q : ℝ := β * (γ + δ)
  have h_iterate_mem :
      ∀ k : ℕ, method.iterate k ∈ Metric.closedBall method.initialPoint r := by
    intro k
    exact
      (iterate_mem_closedBall_and_step_norm_le_geom_ofClosedBallConvergenceAssumptions
        (method := method) (semideriv := semideriv)
        (r := r) (β := β) (γ := γ) (δ := δ) h_assumptions k).1
  have h_contraction :
      ∀ k : ℕ, ‖method.iterate (k + 1) - xStar‖ ≤ q * ‖method.iterate k - xStar‖ := by
    intro k
    -- Once the invariant closed ball is available, the local contraction-to-root estimate applies.
    simpa [q, method.iterate_succ_eq_generalizedNewtonStep] using
      generalizedNewtonStep_norm_le_ofClosedBallConvergenceAssumptions
        (method := method) (semideriv := semideriv)
        (xStar := xStar) (r := r) (β := β) (γ := γ) (δ := δ)
        h_assumptions h_unique (h_iterate_mem k) (method.selectedOperator_mem_at k)
  exact generalizedNewton_tendsto_of_contraction
    method.iterate xStar q h_assumptions.contraction_lt_one h_contraction

#print axioms generalizedNewtonStep
#print axioms generalizedNewtonLineSearchStep
#print axioms NonsmoothNewtonMethod
#print axioms GeneralizedNewtonLineSearchMethod

end
