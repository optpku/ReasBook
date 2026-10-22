/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Remark_19_22

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators InnerProductSpace

universe u

namespace ERealFunction

section EqualityConstraints

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {m : ℕ}

local notation "ConstraintSpace" => EuclideanSpace ℝ (Fin m)

attribute [local instance] Classical.propDecidable

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

section Basic

/-- The continuous linear map `x ↦ (⟪x, u_i⟫)_i` attached to a finite family of equality
constraints. -/
def equalityCoordinateMap (u : Fin m → H) : H →L[ℝ] ConstraintSpace :=
  ((EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun i ↦ innerSL ℝ (u i))

-- Proof sketch: unfold `equalityCoordinateMap`, evaluate the `ContinuousLinearMap.pi` coordinate,
-- and rewrite `⟪u_i, x⟫` as `⟪x, u_i⟫` using symmetry of the real inner product.
/-- The `i`th coordinate of `equalityCoordinateMap u x` is `⟪x, u_i⟫`. -/
@[simp] theorem equalityCoordinateMap_apply
    (u : Fin m → H) (x : H) (i : Fin m) :
    equalityCoordinateMap u x i = ⟪x, u i⟫_ℝ := sorry

-- Proof sketch: specialize `equalityConstraintPerturbationFunction` to `equalityCoordinateMap u`,
-- then rewrite equality in `EuclideanSpace ℝ (Fin m)`
-- coordinatewise using `equalityCoordinateMap_apply`.
/-- Evaluating the perturbation function gives the piecewise formula from `(19.45)`. -/
@[simp] theorem coordinateEqualityConstraintPerturbation_apply
    (f : H → Set.Ioi (⊥ : EReal)) (u : Fin m → H) (ρ η : ConstraintSpace) (x : H) :
    (equalityConstraintPerturbationFunction f (equalityCoordinateMap u) ρ (x, η) : EReal) =
      if ∀ i : Fin m, ⟪x, u i⟫_ℝ = ρ i - η i then
        (f x : EReal)
      else
        ⊤ := sorry

-- Proof sketch: evaluate `perturbationPrimalObjective` at the zero perturbation and rewrite the
-- resulting coordinate equalities using `equalityCoordinateMap_apply`.
/-- The primal problem attached to the perturbation is the minimization of `f(x)` under the
equality constraints `⟪x, u_i⟫ = ρ_i`. -/
theorem perturbationPrimalObjective_coordinateEqualityConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (u : Fin m → H) (ρ : ConstraintSpace) :
    perturbationPrimalObjective
        (equalityConstraintPerturbationFunction f (equalityCoordinateMap u) ρ) =
      fun x : H ↦
        if ∀ i : Fin m, ⟪x, u i⟫_ℝ = ρ i then
          (f x : EReal)
        else
          ⊤ := sorry

-- Proof sketch: specialize Proposition 19.21 (4), rewrite `⟪equalityCoordinateMap u x - ρ, ν⟫`
-- as the finite sum `∑ i ν_i (⟪x, u_i⟫ - ρ_i)`, and keep the `x ∈ effectiveDomain f` branch
-- structure unchanged.
/-- The Lagrangian has the branch formula from `(19.48)`. -/
theorem lagrangian_coordinateEqualityConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (u : Fin m → H) (ρ : ConstraintSpace)
    (x : H) (ν : ConstraintSpace) :
    ℒ[equalityConstraintPerturbationFunction f (equalityCoordinateMap u) ρ] x ν =
      if hx : x ∈ effectiveDomain f then
        (f x : EReal) +
          (((∑ i : Fin m, ν i * (⟪x, u i⟫_ℝ - ρ i)) : ℝ) : EReal)
      else
        ⊤ := sorry

end Basic

section ProductL2Ambient

-- Proof sketch: specialize Proposition 19.21 (1) to the continuous linear map
-- `equalityCoordinateMap u`. The hypothesis `ρ ∈ equalityCoordinateMap u '' effectiveDomain f`
-- is exactly the coordinate version of the feasibility assumption in the corollary.
/-- Corollary 19.23: if `f ∈ Γ₀(H)` and the constraint vector `ρ` is attained by
`x ↦ (⟪x, u_i⟫)_i` on `effectiveDomain f`, then the perturbation function from `(19.45)` belongs
to `Γ₀(H × ℝ^m)`. -/
theorem coordinateEqualityConstraintPerturbation_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (u : Fin m → H) (ρ : ConstraintSpace)
    (hρ : ρ ∈ equalityCoordinateMap u '' effectiveDomain f) :
    equalityConstraintPerturbationFunction f (equalityCoordinateMap u) ρ ∈
      Γ₀(H × ConstraintSpace) := sorry

end ProductL2Ambient

section CompleteDuality

variable [CompleteSpace H]

-- Proof sketch: the adjoint of the coordinate map is the sum of the adjoints of its coordinate
-- functionals, and the adjoint of `x ↦ ⟪x, u_i⟫` is `t ↦ t • u_i`.
/-- The adjoint of the coordinate equality map is the finite linear combination
`ν ↦ ∑ i, ν_i u_i`. -/
theorem equalityCoordinateMap_adjoint_apply
    (u : Fin m → H) (ν : ConstraintSpace) :
    (equalityCoordinateMap u).adjoint ν = ∑ i : Fin m, ν i • u i := sorry

-- Proof sketch: apply Proposition 19.21 (3), compute the adjoint of `equalityCoordinateMap u`
-- using `equalityCoordinateMap_adjoint_apply`, and rewrite the Euclidean inner product with
-- `PiLp.inner_apply`.
/-- The dual problem is the minimization of the explicit finite-dimensional objective from
`(19.47)`. -/
theorem perturbationDualObjective_coordinateEqualityConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (u : Fin m → H) (ρ : ConstraintSpace) :
    perturbationDualObjective
        (equalityConstraintPerturbationFunction f (equalityCoordinateMap u) ρ) =
      fun ν : ConstraintSpace ↦
        conjugate (fun x : H ↦ (f x : EReal)) (-∑ i : Fin m, ν i • u i) +
          (((∑ i : Fin m, ν i * ρ i) : ℝ) : EReal) := sorry

-- Proof sketch: specialize Proposition 19.21 (5) to `L = equalityCoordinateMap u`, rewrite
-- `-L.adjoint ν̄` via `equalityCoordinateMap_adjoint_apply`, and expand the constraint
-- `L x̄ = ρ` coordinatewise using `equalityCoordinateMap_apply`.
/-- Under strong duality, a pair `(x̄, ν̄)` is a saddle point of the Lagrangian if and only if
`-∑ i ν̄_i u_i ∈ ∂ f(x̄)` and `⟪x̄, u_i⟫ = ρ_i` for every coordinate. -/
theorem isSaddlePointOn_lagrangian_coordinateEqualityConstraintPerturbation_iff
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (u : Fin m → H) (ρ : ConstraintSpace)
    (hρ : ρ ∈ equalityCoordinateMap u '' effectiveDomain f)
    (hμ :
      ∃ μ : ℝ,
        sInf
            (Set.range
              (perturbationPrimalObjective
                (equalityConstraintPerturbationFunction f (equalityCoordinateMap u) ρ))) = μ ∧
          sInf
              (Set.range
                (perturbationDualObjective
                  (equalityConstraintPerturbationFunction f (equalityCoordinateMap u) ρ))) =
            -μ)
    (xbar : H) (νbar : ConstraintSpace) :
    IsSaddlePointOn (Set.univ : Set H)
      (Set.univ : Set ConstraintSpace)
      (ℒ[equalityConstraintPerturbationFunction f (equalityCoordinateMap u) ρ]) xbar νbar ↔
      -∑ i : Fin m, νbar i • u i ∈ (∂ f) xbar ∧
        ∀ i : Fin m, ⟪xbar, u i⟫_ℝ = ρ i := sorry

-- Proof sketch: after specializing Proposition 19.21 to the coordinate map, apply the primal
-- solution conclusion for saddle points to the perturbation
-- `equalityConstraintPerturbationFunction f (equalityCoordinateMap u) ρ`.
/-- The primal component of a saddle point solves the constrained minimization problem `(19.46)`. -/
theorem
    mem_argmin_perturbationPrimalObjective_of_coordinateEqualityConstraintPerturbation_isSaddlePoint
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (u : Fin m → H) (ρ : ConstraintSpace)
    (hρ : ρ ∈ equalityCoordinateMap u '' effectiveDomain f)
    (hμ :
      ∃ μ : ℝ,
        sInf
            (Set.range
              (perturbationPrimalObjective
                (equalityConstraintPerturbationFunction f (equalityCoordinateMap u) ρ))) = μ ∧
          sInf
              (Set.range
                (perturbationDualObjective
                  (equalityConstraintPerturbationFunction f (equalityCoordinateMap u) ρ))) =
            -μ)
    {xbar : H} {νbar : ConstraintSpace}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H)
        (Set.univ : Set ConstraintSpace)
        (ℒ[equalityConstraintPerturbationFunction f (equalityCoordinateMap u) ρ]) xbar νbar) :
    xbar ∈
      Argmin
        (perturbationPrimalObjective
          (equalityConstraintPerturbationFunction f (equalityCoordinateMap u) ρ)) := sorry

-- Proof sketch: expand `equalityConstraintAffineObjective` for `L = equalityCoordinateMap u`,
-- then rewrite `⟪x, (equalityCoordinateMap u).adjoint ν⟫` with
-- `equalityCoordinateMap_adjoint_apply` and `inner_sum`.
/-- The chapter owner `equalityConstraintAffineObjective` specializes to the explicit finite-sum
affine objective from Corollary 19.23. -/
theorem equalityConstraintAffineObjective_equalityCoordinateMap
    (f : H → Set.Ioi (⊥ : EReal)) (u : Fin m → H) (ν : ConstraintSpace) :
    equalityConstraintAffineObjective f (equalityCoordinateMap u) ν =
      fun x : H ↦
        (f x : EReal) +
          (((∑ i : Fin m, ν i * ⟪x, u i⟫_ℝ) : ℝ) : EReal) := sorry

-- Proof sketch: apply `mem_argmin_of_isEqualityConstraintLagrangeMultiplier` from
-- Remark 19.22 to the coordinate map `equalityCoordinateMap u`, then rewrite the canonical owner
-- `equalityConstraintAffineObjective` via
-- `equalityConstraintAffineObjective_equalityCoordinateMap`.
/-- Corollary 19.23 `(19.50)`: the primal component of a saddle point minimizes the explicit
affine objective `x ↦ f(x) + ∑ i ν_i ⟪x, u_i⟫`. -/
theorem mem_argmin_coordinateAffineFormula_of_isSaddlePoint
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (u : Fin m → H) (ρ : ConstraintSpace)
    (hρ : ρ ∈ equalityCoordinateMap u '' effectiveDomain f)
    (hμ :
      ∃ μ : ℝ,
        sInf
            (Set.range
              (perturbationPrimalObjective
                (equalityConstraintPerturbationFunction f (equalityCoordinateMap u) ρ))) = μ ∧
          sInf
              (Set.range
                (perturbationDualObjective
                  (equalityConstraintPerturbationFunction f (equalityCoordinateMap u) ρ))) =
            -μ)
    {xbar : H} {νbar : ConstraintSpace}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H)
        (Set.univ : Set ConstraintSpace)
        (ℒ[equalityConstraintPerturbationFunction f (equalityCoordinateMap u) ρ]) xbar νbar) :
    xbar ∈ Argmin
      (fun x : H ↦
        (f x : EReal) +
          (((∑ i : Fin m, νbar i * ⟪x, u i⟫_ℝ) : ℝ) : EReal)) := sorry

end CompleteDuality

end EqualityConstraints

end ERealFunction
