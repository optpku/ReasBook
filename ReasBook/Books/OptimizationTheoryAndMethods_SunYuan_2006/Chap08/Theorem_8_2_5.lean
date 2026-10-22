/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_3_2

noncomputable section

section Chapter08Theorem825

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ
local notation "EPoint" => EuclideanSpace ℝ (Fin n)

/-- Helper for Chapter08 Theorem 8.2.5: the source pairing `dᵀg` is read through the Euclidean
transport `WithLp.toLp 2` on the chapter carrier `Fin n → ℝ`. -/
def pointInner (_ : Type*) (x y : Point) : ℝ :=
  inner ℝ (WithLp.toLp 2 x : EPoint) (WithLp.toLp 2 y : EPoint)

/-- Helper for Chapter08 Theorem 8.2.5: the source gradient at a chapter point is the Euclidean
gradient of the transported objective, viewed back as a coordinate function on `Fin n`. -/
def pointGradient (f : Point → ℝ) (x : Point) : Point :=
  (gradient (fun y : EPoint ↦ f y) (WithLp.toLp 2 x) : EPoint)

/-- Helper for Chapter08 Theorem 8.2.5: the descent directions are exactly the directions with
negative transported gradient pairing. -/
def pointDescentDirections (f : Point → ℝ) (xStar : Point) : Set Point :=
  {d | pointInner ℝ d (pointGradient f xStar) < 0}

local notation "inner" => pointInner
local notation "gradient" => pointGradient
local notation "descentDirections" => pointDescentDirections

/- This source-facing theorem file reuses the Chapter 8 owners
`ConstrainedOptimizationProblem`, `IsSequentialFeasibleDirectionAt`,
`sequentialFeasibleDirections`, and `descentDirections` from the existing repository API. -/

/-- Helper for Chapter08 Theorem 8.2.5: the source sequential feasible-direction set `SFD(xStar,
X)` is realized by the chapter's canonical positive tangent cone `posTangentConeAt X xStar`. -/
abbrev sequentialFeasibleDirections (xStar : Point) (X : Set Point) : Set Point :=
  posTangentConeAt X xStar

/-- Helper for Chapter08 Theorem 8.2.5: the predicate form of a sequential feasible direction is
membership in the source-facing set alias above. -/
abbrev IsSequentialFeasibleDirectionAt (X : Set Point) (xStar d : Point) : Prop :=
  d ∈ sequentialFeasibleDirections xStar X

/-- Helper for Chapter08 Theorem 8.2.5: on a sequential feasible direction, the derivative within
the feasible set agrees with the ambient derivative because both derivatives coincide on the
tangent cone. -/
lemma objective_fderivWithin_eq_fderiv_on_sequential_feasible_direction
    (problem : ConstrainedOptimizationProblem n m E I) (xStar d : Point)
    (hd : d ∈ sequentialFeasibleDirections xStar problem.feasibleSet)
    (h_objective : DifferentiableAt ℝ problem.objective xStar) :
    (fderivWithin ℝ problem.objective problem.feasibleSet xStar : Point → ℝ) d =
      fderiv ℝ problem.objective xStar d := by
  -- Route correction: use the tangent-cone uniqueness bridge directly, rather than rebuilding
  -- the source sequence expansion inside this theorem file.
  have hd_real : d ∈ tangentConeAt ℝ problem.feasibleSet xStar :=
    tangentConeAt_mono_field hd
  -- The within derivative and ambient derivative agree on every tangent direction.
  simpa using
    (h_objective.differentiableWithinAt.hasFDerivWithinAt).unique_on
      (h_objective.hasFDerivAt.hasFDerivWithinAt) hd_real

/-- Helper for Chapter08 Theorem 8.2.5: membership in the local source-facing descent-direction
set is exactly negativity of the transported gradient pairing. -/
lemma point_mem_descentDirections_iff (f : Point → ℝ) (xStar d : Point) :
    d ∈ descentDirections f xStar ↔ inner ℝ d (gradient f xStar) < 0 :=
  Iff.rfl

/-- Helper for Chapter08 Theorem 8.2.5: the transported pairing is symmetric because it is the
ordinary Euclidean inner product after applying `WithLp.toLp 2`. -/
lemma pointInner_comm (x y : Point) :
    inner ℝ x y = inner ℝ y x := by
  simp [pointInner, real_inner_comm]

/-- Helper for Chapter08 Theorem 8.2.5: the transported gradient pairing should agree with the
Fréchet derivative of the original objective on the chapter carrier. -/
lemma point_inner_gradient_left (f : Point → ℝ) (x y : Point) :
    inner ℝ (gradient f x) y = fderiv ℝ f x y := by
  let coordIso : EPoint ≃L[ℝ] Point :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)
  let g : EPoint → ℝ := f ∘ coordIso
  -- Rewrite the transported pairing as the Euclidean pairing for the objective viewed on `EPoint`.
  calc
    inner ℝ (gradient f x) y =
        inner ℝ (_root_.gradient g (WithLp.toLp 2 x) : EPoint) (WithLp.toLp 2 y : EPoint) := by
          rfl
    _ = fderiv ℝ g (WithLp.toLp 2 x) (WithLp.toLp 2 y) := by
      exact
        (_root_.inner_gradient_left (𝕜 := ℝ) (f := g) (x := WithLp.toLp 2 x)
          (y := WithLp.toLp 2 y))
    _ = ((fderiv ℝ f (coordIso (WithLp.toLp 2 x))).comp (coordIso : EPoint →L[ℝ] Point))
          (WithLp.toLp 2 y) := by
      rw [coordIso.comp_right_fderiv]
    _ = fderiv ℝ f x y := by
      have hx : coordIso (WithLp.toLp 2 x) = x := by
        rfl
      have hy : coordIso (WithLp.toLp 2 y) = y := by
        rfl
      simpa [hx, hy]

/-- Helper for Chapter08 Theorem 8.2.5: a nonnegative objective-gradient pairing rules out
membership in the descent-direction set. -/
lemma not_mem_descentDirections_of_nonneg_pairing
    (problem : ConstrainedOptimizationProblem n m E I) (xStar d : Point)
    (h_nonneg : 0 ≤ inner ℝ d (gradient problem.objective xStar)) :
    d ∉ descentDirections problem.objective xStar := by
  intro hd_descent
  -- Descent directions are exactly the directions with strictly negative gradient pairing.
  have hneg :
      inner ℝ d (gradient problem.objective xStar) < 0 :=
    (point_mem_descentDirections_iff problem.objective xStar d).1 hd_descent
  linarith

/-- Chapter08 Theorem 8.2.5: if `xStar` is a feasible local minimizer of `problem` and the
objective is differentiable at `xStar`, then every sequential feasible direction
`d ∈ SFD(xStar, problem.feasibleSet)` has nonnegative first-order objective pairing
`inner ℝ d (gradient problem.objective xStar) ≥ 0`. -/
theorem geometryOptimalityCondition_nonneg_pairing
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar) :
    ∀ d ∈ sequentialFeasibleDirections xStar problem.feasibleSet,
      0 ≤ inner ℝ d (gradient problem.objective xStar) := by
  intro d hd
  -- Route correction: follow the source proof through the local-minimum tangent-cone owner,
  -- then rewrite the resulting derivative as the gradient pairing.
  have hnonneg_within :
      0 ≤ (fderivWithin ℝ problem.objective problem.feasibleSet xStar : Point → ℝ) d :=
    h_localMin.fderivWithin_nonneg hd
  have hnonneg_fderiv : 0 ≤ fderiv ℝ problem.objective xStar d := by
    rw [← objective_fderivWithin_eq_fderiv_on_sequential_feasible_direction
      problem xStar d hd h_objective]
    exact hnonneg_within
  have hnonneg_pairing_right :
      0 ≤ inner ℝ (gradient problem.objective xStar) d := by
    simpa [point_inner_gradient_left] using hnonneg_fderiv
  simpa [pointInner_comm] using hnonneg_pairing_right

/-- Predicate-level form of Theorem 8.2.5 for direct reuse with a fixed sequential feasible
direction `d`. -/
theorem geometryOptimalityCondition_nonneg_pairing_of_isSequentialFeasibleDirection
    (problem : ConstrainedOptimizationProblem n m E I) (xStar d : Point)
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (hd : IsSequentialFeasibleDirectionAt problem.feasibleSet xStar d) :
    0 ≤ inner ℝ d (gradient problem.objective xStar) :=
  geometryOptimalityCondition_nonneg_pairing
    problem xStar h_localMin h_objective d hd

/-- Companion reformulation: under the same hypotheses, the sequential feasible directions at
`xStar` do not meet the descent-direction set of `problem.objective` at `xStar`. -/
theorem geometryOptimalityCondition_sequentialFeasibleDirections_inter_descentDirections_eq_empty
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar) :
    sequentialFeasibleDirections xStar problem.feasibleSet ∩
        descentDirections problem.objective xStar = (∅ : Set Point) := by
  ext d
  constructor
  · intro hd_inter
    have hd_feasible : d ∈ sequentialFeasibleDirections xStar problem.feasibleSet := hd_inter.1
    have hnonneg :
        0 ≤ inner ℝ d (gradient problem.objective xStar) :=
      geometryOptimalityCondition_nonneg_pairing
        problem xStar h_localMin h_objective d hd_feasible
    -- The main inequality excludes the strict negativity required for a descent direction.
    exact (not_mem_descentDirections_of_nonneg_pairing problem xStar d hnonneg) hd_inter.2
  · intro hd_empty
    exact False.elim hd_empty

end Chapter08Theorem825
