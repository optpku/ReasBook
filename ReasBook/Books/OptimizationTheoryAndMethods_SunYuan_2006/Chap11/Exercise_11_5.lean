/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Interval.Set.ProjIcc

noncomputable section

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Semantic recall hits for this item: `Set.projIcc` and `Set.coe_projIcc` are the canonical
-- interval-projection owners in mathlib, so the box projection is modeled coordinatewise on
-- `EuclideanSpace ℝ (Fin n)` rather than through a wrapper around a generic nearest-point map.

/-- The feasible box `lower ≤ x ≤ upper` for the bound-constrained problem on `Point`. -/
def boxFeasibleSet (lower upper : Point) : Set Point :=
  {x | ∀ i, lower i ≤ x i ∧ x i ≤ upper i}

/-- Membership in `boxFeasibleSet lower upper` is exactly the coordinatewise bound condition
`lower ≤ x ≤ upper`. -/
theorem mem_boxFeasibleSet_iff
    (lower upper x : Point) :
    x ∈ boxFeasibleSet lower upper ↔ ∀ i, lower i ≤ x i ∧ x i ≤ upper i := by
  rfl

/-- The coordinatewise projection of `x` onto the box `lower ≤ y ≤ upper`. -/
def boxProjection
    (lower upper : Point) (h_bounds : ∀ i, lower i ≤ upper i) :
    Point → Point :=
  fun x ↦
    WithLp.toLp 2
      (fun i ↦ (Set.projIcc (lower i) (upper i) (h_bounds i) (x i)).1)

/-- Each coordinate of `boxProjection lower upper h_bounds x` is the interval clamp
`max (lower i) (min (upper i) (x i))`. -/
theorem boxProjection_apply
    (lower upper : Point) (h_bounds : ∀ i, lower i ≤ upper i)
    (x : Point) (i : Fin n) :
    boxProjection lower upper h_bounds x i =
      max (lower i) (min (upper i) (x i)) := by
  simp [boxProjection, Set.coe_projIcc]

/-- The coordinatewise box projection always lands in the box `lower ≤ y ≤ upper`. -/
theorem boxProjection_mem_boxFeasibleSet
    (lower upper : Point) (h_bounds : ∀ i, lower i ≤ upper i)
    (x : Point) :
    boxProjection lower upper h_bounds x ∈ boxFeasibleSet lower upper := by
  refine (mem_boxFeasibleSet_iff lower upper (boxProjection lower upper h_bounds x)).2 ?_
  intro i
  exact (Set.projIcc (lower i) (upper i) (h_bounds i) (x i)).2

section BoxProjectedGradientStepAPI

variable (objective : Point → ℝ) (lowerBound upperBound : Point)
  (h_bounds : ∀ i, lowerBound i ≤ upperBound i)

local notation "P_[" lowerBound ", " upperBound "]" =>
  boxProjection lowerBound upperBound h_bounds

/-- One projected-gradient step for the box constrained problem: move to
`x - α • ∇ objective x` and project back onto `lower ≤ y ≤ upper`. -/
def boxProjectedGradientStep
    (α : ℝ) (x : Point) : Point :=
  P_[lowerBound, upperBound] (x - α • gradient objective x)

/-- Unfolding `boxProjectedGradientStep` gives the textbook projected-gradient update
`P_[lower, upper] (x - α • ∇ objective x)`. -/
theorem boxProjectedGradientStep_eq
    (α : ℝ) (x : Point) :
    boxProjectedGradientStep objective lowerBound upperBound h_bounds α x =
      P_[lowerBound, upperBound] (x - α • gradient objective x) := rfl

end BoxProjectedGradientStepAPI

section BoxProjectedGradientAlgorithmAPI

variable (objective : Point → ℝ) (lowerBound upperBound : Point)
  (h_bounds : ∀ i, lowerBound i ≤ upperBound i)

local notation "P_[" lowerBound ", " upperBound "]" =>
  boxProjection lowerBound upperBound h_bounds

set_option linter.unusedVariables false in
/-- Chapter11 Exercise 11.5: the projected gradient algorithm for the box constrained problem
`min objective x` subject to `lowerBound ≤ x` and `x ≤ upperBound` is the iterate sequence
starting from `x₁ = initialPoint` and defined recursively by
`x_(k + 1) = P_[lowerBound, upperBound] (x_k - stepSize k • ∇ objective (x_k))`
for `k ≥ 1`. -/
def boxProjectedGradientAlgorithm
    (initialPoint : Point) (stepSize : ℕ → ℝ) : ℕ → Point :=
  fun
  | 0 => initialPoint
  | 1 => initialPoint
  | k + 2 =>
      boxProjectedGradientStep objective lowerBound upperBound h_bounds
        (stepSize (k + 1))
        (boxProjectedGradientAlgorithm
          objective lowerBound upperBound h_bounds initialPoint stepSize (k + 1))

set_option linter.unusedVariables false in
/-- The first iterate of `boxProjectedGradientAlgorithm` is the prescribed starting point
`x₁`. -/
theorem boxProjectedGradientAlgorithm_one_eq
    (initialPoint : Point) (stepSize : ℕ → ℝ) :
    boxProjectedGradientAlgorithm objective lowerBound upperBound h_bounds initialPoint stepSize 1 =
      initialPoint := rfl

set_option linter.unusedVariables false in
/-- If the starting point is feasible, then the first iterate of
`boxProjectedGradientAlgorithm` is feasible for the box constraints. -/
theorem boxProjectedGradientAlgorithm_one_mem_boxFeasibleSet
    (initialPoint : Point) (stepSize : ℕ → ℝ)
    (h_initial : initialPoint ∈ boxFeasibleSet lowerBound upperBound) :
    boxProjectedGradientAlgorithm objective lowerBound upperBound h_bounds initialPoint stepSize 1 ∈
      boxFeasibleSet lowerBound upperBound := by
  simpa [boxProjectedGradientAlgorithm] using h_initial

set_option linter.unusedVariables false in
/-- At each stage `k ≥ 1`, the next iterate of `boxProjectedGradientAlgorithm` is obtained by
the canonical projected-gradient step applied to `x_k`. -/
theorem boxProjectedGradientAlgorithm_succ_eq
    (initialPoint : Point) (stepSize : ℕ → ℝ)
    (k : ℕ) (hk : 1 ≤ k) :
    boxProjectedGradientAlgorithm
        objective lowerBound upperBound h_bounds initialPoint stepSize (k + 1) =
      boxProjectedGradientStep objective lowerBound upperBound h_bounds
        (stepSize k)
        (boxProjectedGradientAlgorithm
          objective lowerBound upperBound h_bounds initialPoint stepSize k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rfl

set_option linter.unusedVariables false in
/-- Unfolding the step owner in `boxProjectedGradientAlgorithm_succ_eq` recovers the textbook
projected-gradient update formula. -/
theorem boxProjectedGradientAlgorithm_succ_eq_projection
    (initialPoint : Point) (stepSize : ℕ → ℝ)
    (k : ℕ) (hk : 1 ≤ k) :
    boxProjectedGradientAlgorithm
        objective lowerBound upperBound h_bounds initialPoint stepSize (k + 1) =
      P_[lowerBound, upperBound]
        (boxProjectedGradientAlgorithm
            objective lowerBound upperBound h_bounds initialPoint stepSize k -
          stepSize k •
            gradient objective
              (boxProjectedGradientAlgorithm
                objective lowerBound upperBound h_bounds initialPoint stepSize k)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa [boxProjectedGradientAlgorithm] using
    (boxProjectedGradientStep_eq objective lowerBound upperBound h_bounds (stepSize (j + 1))
      (boxProjectedGradientAlgorithm
        objective lowerBound upperBound h_bounds initialPoint stepSize (j + 1)))

set_option linter.unusedVariables false in
/-- If the starting point is feasible, every iterate of `boxProjectedGradientAlgorithm` with
`k ≥ 1` remains in the box `lowerBound ≤ x_k ≤ upperBound`. -/
theorem boxProjectedGradientAlgorithm_mem_boxFeasibleSet
    (initialPoint : Point) (stepSize : ℕ → ℝ)
    (h_initial : initialPoint ∈ boxFeasibleSet lowerBound upperBound)
    (k : ℕ) (hk : 1 ≤ k) :
    boxProjectedGradientAlgorithm objective lowerBound upperBound h_bounds initialPoint stepSize k ∈
      boxFeasibleSet lowerBound upperBound := by
  rcases k with _ | k
  · cases Nat.not_succ_le_zero 0 hk
  rcases k with _ | k
  · simpa [boxProjectedGradientAlgorithm] using h_initial
  · simpa [boxProjectedGradientAlgorithm, boxProjectedGradientStep] using
      (boxProjection_mem_boxFeasibleSet _ _ _ _)

end BoxProjectedGradientAlgorithmAPI

#print axioms boxProjection
#print axioms boxProjectedGradientStep
#print axioms boxProjectedGradientAlgorithm

end
