/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_1_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open scoped CubicRegularizedDiagonalInvariants

/- Proposition 4.1.15 lies in the diagonal cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective` in `Theorem_4_1_11`, the chapter owner of the primal cubic
  model;
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Theorem_4_1_11`, the chapter owners of the scalar dual value and its effective domain;
* `cubicRegularizedDiagonalMinimum` in `Definition_4_1_15`, imported through
  `Theorem_4_1_11`, the chapter owner for the boundary value `-H_min`;
* `IsMinOn` and `IsMaxOn` in mathlib, the canonical owner predicates for primal and dual
  optimality.

Best owner abstraction:
* source-facing: the explicit two-dimensional counterexample itself, with the concrete data
  `g = (-1, 0)ᵀ`, `H = diag(0, -1)`, `M = 1`, the two minimizers `(1, ±√3)ᵀ`, and the boundary
  maximizer `λ* = -H_min[Hdiag] = 1`;
* core/canonical: `cubicRegularizedQuadraticObjective`, `cubicRegularizedQuadraticDualFunction`,
  `cubicRegularizedQuadraticDualDomain`, together with `IsMinOn` and `IsMaxOn`;
* bridge/view: the concrete specialization to `n = 2`.

Primitive data:
* the explicit example vectors/matrix `CubicRegularizedQuadraticCounterexample.g`,
  `CubicRegularizedQuadraticCounterexample.Hdiag`,
  `CubicRegularizedQuadraticCounterexample.H`,
  `CubicRegularizedQuadraticCounterexample.minimizerPos`, and
  `CubicRegularizedQuadraticCounterexample.minimizerNeg`.

Derived API:
* the optimality statements for the two explicit minimizers via `IsMinOn`;
* the identity `-H_min[Hdiag] = 1`;
* dual optimality of the same explicit boundary multiplier on
  `cubicRegularizedQuadraticDualDomain g H 1 ∩ Set.Ici (0 : ℝ)` via `IsMaxOn`.

Source/core/bridge triage:
* source-facing: the explicit counterexample data and witness optimality statements below;
* core/canonical: the chapter owner objective/dual/domain family and the order-owner predicates;
* bridge/view: the concrete `n = 2` specialization of those owners.

This file therefore removes the existential wrapper around “multiple minimizers”, keeps the
explicit textbook witnesses as public data, and reuses the canonical expression
`-H_min[Hdiag]` directly instead of introducing a second public owner for the boundary
multiplier. -/

namespace CubicRegularizedQuadraticCounterexample

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The example gradient `g = (-1, 0)ᵀ`. -/
def g : E :=
  WithLp.toLp 2 ![-(1 : ℝ), (0 : ℝ)]

/-- The diagonal entries of the example Hessian `H = diag(0, -1)`. -/
def Hdiag : Fin 2 → ℝ :=
  ![(0 : ℝ), (-1 : ℝ)]

/-- The example Hessian `H = diag(0, -1)`. -/
def H : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal Hdiag

/-- The positive-sign primal minimizer `(1, √3)ᵀ`. -/
def minimizerPos : E :=
  WithLp.toLp 2 ![(1 : ℝ), Real.sqrt 3]

/-- The negative-sign primal minimizer `(1, -√3)ᵀ`. -/
def minimizerNeg : E :=
  WithLp.toLp 2 ![(1 : ℝ), -(Real.sqrt 3)]

local notation "v" => cubicRegularizedQuadraticObjective g H 1
local notation "ψ" => cubicRegularizedQuadraticDualFunction g H 1
local notation "Dplus" => cubicRegularizedQuadraticDualDomain g H 1 ∩ Set.Ici (0 : ℝ)

/-- Helper for Proposition 4.1.15: in the two-dimensional example, the norm square is the sum of
its two coordinate squares. -/
lemma norm_sq_eq_coords (h : E) :
    ‖h‖ ^ (2 : ℕ) = (h 0)^2 + (h 1)^2 := by
  -- Expand the Euclidean norm in coordinates and collapse the two-point sum.
  calc
    ‖h‖ ^ (2 : ℕ) = (Real.sqrt (∑ i : Fin 2, ‖h i‖ ^ (2 : ℕ))) ^ (2 : ℕ) := by
      rw [EuclideanSpace.norm_eq]
    _ = ∑ i : Fin 2, ‖h i‖ ^ (2 : ℕ) := by
      have hnonneg : 0 ≤ ∑ i : Fin 2, ‖h i‖ ^ (2 : ℕ) := by
        positivity
      simpa [pow_two] using Real.sq_sqrt hnonneg
    _ = (h 0)^2 + (h 1)^2 := by
      simp [Fin.sum_univ_two, pow_two]

/-- Helper for Proposition 4.1.15: the diagonal Hessian sends `(x, y)` to `(0, -y)`. -/
lemma hessian_mulVec_eq (h : E) :
    H.mulVec h = WithLp.toLp 2 ![0, -(h 1)] := by
  -- Evaluate the diagonal matrix-vector product coordinatewise.
  ext i
  fin_cases i
  · simp [H, Hdiag, Matrix.mulVec]
  · simp [H, Hdiag, Matrix.mulVec]

/-- Helper for Proposition 4.1.15: after shifting by the boundary multiplier, the quadratic part
acts only on the first coordinate. -/
lemma boundary_shift_mulVec_eq (h : E) :
    (H + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).mulVec h = WithLp.toLp 2 ![h 0, 0] := by
  -- The shifted diagonal matrix is `diag(1, 0)`.
  ext i
  fin_cases i
  · simp [H, Hdiag, Matrix.mulVec]
  · simp [H, Hdiag, Matrix.mulVec]

/-- Helper for Proposition 4.1.15: the primal objective rewrites as a sum of nonnegative terms
plus the constant `-7/6`. -/
lemma objective_eq_normal_form (h : E) :
    v h = ((h 0 - 1)^2) / 2 + ((‖h‖ - 2)^2 * (‖h‖ + 1)) / 6 - (7 : ℝ) / 6 := by
  -- Rewrite the Hessian term through the norm and then complete the squares in `h 0` and `‖h‖`.
  rw [cubicRegularizedQuadraticObjective_apply, hessian_mulVec_eq]
  simp [g, dotProduct, pow_two]
  nlinarith [norm_sq_eq_coords h]

/-- Helper for Proposition 4.1.15: the positive witness has norm square `4`. -/
lemma minimizerPos_norm_sq :
    ‖minimizerPos‖ ^ (2 : ℕ) = 4 := by
  -- Compute the norm square from the explicit coordinates `(1, √3)`.
  rw [norm_sq_eq_coords]
  have hthree_nonneg : 0 ≤ (3 : ℝ) := by
    positivity
  have hsqrt_sq : (Real.sqrt 3)^2 = 3 := by
    nlinarith [Real.sq_sqrt hthree_nonneg]
  calc
    (minimizerPos 0)^2 + (minimizerPos 1)^2 = 1 + 3 := by
      simp [minimizerPos, hsqrt_sq]
    _ = 4 := by
      norm_num

/-- Helper for Proposition 4.1.15: the negative witness also has norm square `4`. -/
lemma minimizerNeg_norm_sq :
    ‖minimizerNeg‖ ^ (2 : ℕ) = 4 := by
  -- Compute the norm square from the explicit coordinates `(1, -√3)`.
  rw [norm_sq_eq_coords]
  have hthree_nonneg : 0 ≤ (3 : ℝ) := by
    positivity
  have hsqrt_sq : (Real.sqrt 3)^2 = 3 := by
    nlinarith [Real.sq_sqrt hthree_nonneg]
  calc
    (minimizerNeg 0)^2 + (minimizerNeg 1)^2 = 1 + 3 := by
      simp [minimizerNeg, hsqrt_sq]
    _ = 4 := by
      norm_num

/-- Helper for Proposition 4.1.15: the positive witness has norm `2`. -/
lemma minimizerPos_norm_eq_two :
    ‖minimizerPos‖ = 2 := by
  -- The norm is nonnegative, so the norm-square identity determines it uniquely.
  have hnonneg : 0 ≤ ‖minimizerPos‖ := norm_nonneg _
  nlinarith [minimizerPos_norm_sq]

/-- Helper for Proposition 4.1.15: the negative witness has norm `2`. -/
lemma minimizerNeg_norm_eq_two :
    ‖minimizerNeg‖ = 2 := by
  -- The same norm-square computation applies to the symmetric second witness.
  have hnonneg : 0 ≤ ‖minimizerNeg‖ := norm_nonneg _
  nlinarith [minimizerNeg_norm_sq]

/-- Helper for Proposition 4.1.15: any point with first coordinate `1` and norm `2` attains the
primal minimum value `-7/6`. -/
lemma isMinOn_of_firstCoord_eq_one_and_norm_eq_two {h : E}
    (h0 : h 0 = 1) (hnorm : ‖h‖ = 2) :
    IsMinOn v Set.univ h := by
  -- The normal form shows that every value is at least `-7/6`, with equality at such a point.
  rw [isMinOn_univ_iff]
  intro x
  rw [objective_eq_normal_form, objective_eq_normal_form]
  rw [h0, hnorm]
  have hsq : 0 ≤ (x 0 - 1)^2 := sq_nonneg _
  have hquad : 0 ≤ (‖x‖ - 2)^2 := sq_nonneg _
  have hlin : 0 ≤ ‖x‖ + 1 := by
    positivity
  have hrad : 0 ≤ ((‖x‖ - 2)^2 * (‖x‖ + 1)) / 6 := by
    positivity
  nlinarith

/-- Helper for Proposition 4.1.15: the explicit witness `(minimizerPos, 4)` makes every scalar
Lagrangian value equal to `-7/6`. -/
lemma lagrangian_at_example_eq (lam : ℝ) :
    cubicRegularizedQuadraticScalarLagrangian g H 1 minimizerPos 4 lam = -(7 : ℝ) / 6 := by
  -- The slack constraint is tight at `(minimizerPos, 4)`, so the `λ`-term vanishes identically.
  rw [cubicRegularizedQuadraticScalarLagrangian, minimizerPos_norm_sq]
  simp [g, H, Hdiag, minimizerPos, dotProduct, Matrix.mulVec]
  ring

/-- Helper for Proposition 4.1.15: at the boundary multiplier `λ = 1`, the shifted quadratic is
`(h₀ - 1)^2 / 2 - 1 / 2`. -/
lemma shifted_quadratic_boundary_eq (h : E) :
    quadraticObjective 0 g (H + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) h =
      (h 0 - 1)^2 / 2 - 1 / 2 := by
  -- After the shift, only the first coordinate remains in the quadratic term.
  rw [quadraticObjective_zero_eq_dotProduct, boundary_shift_mulVec_eq]
  simp [g, dotProduct, pow_two]
  ring

/-- Helper for Proposition 4.1.15: the dual value at the boundary multiplier is exactly `-7/6`.
-/
lemma dual_boundary_value_eq :
    ψ 1 = ((-7 : ℝ) / 6 : EReal) := by
  -- Sandwich the dual infimum between the explicit witness value and the universal lower bound.
  apply le_antisymm
  · have hsInf : ψ 1 ≤
        (cubicRegularizedQuadraticScalarLagrangian g H 1 minimizerPos 4 1 : EReal) := by
      rw [cubicRegularizedQuadraticDualFunction_eq_sInf]
      exact sInf_le ⟨(minimizerPos, 4), rfl⟩
    rw [lagrangian_at_example_eq] at hsInf
    exact hsInf
  · rw [cubicRegularizedQuadraticDualFunction_eq_sInf]
    refine le_sInf ?_
    rintro y ⟨⟨h, τ⟩, rfl⟩
    have hquad : (-1 : ℝ) / 2 ≤
        quadraticObjective 0 g (H + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) h := by
      -- The boundary quadratic is a completed square plus `-1/2`.
      rw [shifted_quadratic_boundary_eq]
      have hsq : 0 ≤ (h 0 - 1)^2 := sq_nonneg _
      nlinarith
    have hone_pos : 0 < (1 : ℝ) := by
      norm_num
    have htau_raw := cubicRegularizedQuadraticTauObjective_ge_minValue 1 1 hone_pos τ
    have htau : (-(2 : ℝ) / 3 : ℝ) ≤
        (1 / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (1 / 2 : ℝ) * τ := by
      nlinarith
    have hsum : (-(7 : ℝ) / 6 : ℝ) ≤
        quadraticObjective 0 g (H + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) h +
          ((1 / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (1 / 2 : ℝ) * τ) := by
      nlinarith
    change (((-7 : ℝ) / 6 : ℝ) : EReal) ≤
      (cubicRegularizedQuadraticScalarLagrangian g H 1 h τ 1 : EReal)
    rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term]
    exact EReal.coe_le_coe_iff.2 hsum

/-- Helper for Proposition 4.1.15: the explicit witness gives the uniform dual upper bound
`ψ(λ) ≤ -7/6`. -/
lemma dual_le_example_value (lam : ℝ) :
    ψ lam ≤ ((-7 : ℝ) / 6 : EReal) := by
  -- Evaluate the infimum at the primal witness whose slack constraint is tight.
  have hsInf : ψ lam ≤
      (cubicRegularizedQuadraticScalarLagrangian g H 1 minimizerPos 4 lam : EReal) := by
    rw [cubicRegularizedQuadraticDualFunction_eq_sInf]
    exact sInf_le ⟨(minimizerPos, 4), rfl⟩
  rw [lagrangian_at_example_eq] at hsInf
  exact hsInf

-- Proof sketch: the two vectors differ in their second coordinate, since `√3 ≠ -√3`.
/-- Proposition 4.1.15 (1): the two explicit minimizers in the counterexample are distinct. -/
theorem minimizerPos_ne_minimizerNeg :
    minimizerPos ≠ minimizerNeg := by
  -- Compare the second coordinates of the two witnesses.
  intro hEq
  have hcoord : minimizerPos 1 = minimizerNeg 1 := by
    exact congrArg (fun h : E ↦ h 1) hEq
  have hsqrt_ne_zero : Real.sqrt 3 ≠ 0 := by
    have hthree_pos : 0 < (3 : ℝ) := by
      norm_num
    exact Real.sqrt_ne_zero'.2 hthree_pos
  simp [minimizerPos, minimizerNeg] at hcoord
  apply hsqrt_ne_zero
  nlinarith [hcoord]

-- Proof sketch: compute the stationary equations for the explicit cubic model with
-- `g = (-1, 0)ᵀ`, `H = diag(0, -1)`, and `M = 1`, then verify that `(1, √3)ᵀ` globally minimizes
-- the primal objective.
/-- Proposition 4.1.15 (2): the point `(1, √3)ᵀ` is a global minimizer of the explicit
cubic-regularized quadratic counterexample. -/
theorem minimizerPos_isMinOn :
    IsMinOn v Set.univ minimizerPos := by
  -- The normal form collapses at the explicit witness because its first coordinate is `1`
  -- and its norm is `2`.
  have h0 : minimizerPos 0 = 1 := by
    simp [minimizerPos]
  exact isMinOn_of_firstCoord_eq_one_and_norm_eq_two h0 minimizerPos_norm_eq_two

-- Proof sketch: the same stationary-point computation gives the symmetric second minimizer
-- `(1, -√3)ᵀ`.
/-- Proposition 4.1.15 (3): the point `(1, -√3)ᵀ` is also a global minimizer of the explicit
cubic-regularized quadratic counterexample. -/
theorem minimizerNeg_isMinOn :
    IsMinOn v Set.univ minimizerNeg := by
  -- The same normal-form argument applies to the symmetric second witness.
  have h0 : minimizerNeg 0 = 1 := by
    simp [minimizerNeg]
  exact isMinOn_of_firstCoord_eq_one_and_norm_eq_two h0 minimizerNeg_norm_eq_two

-- Proof sketch: for `Hdiag = (0, -1)`, the minimum diagonal entry is `H_min = -1`.
/-- Proposition 4.1.15 (4): for the explicit Hessian `diag(0, -1)`, the boundary multiplier
`-H_min` equals `1`. -/
theorem boundaryMultiplier_eq_one :
    -H_min[Hdiag] = 1 := by
  -- The infimum of the two diagonal entries `{0, -1}` is `-1`.
  simp [cubicRegularizedDiagonalMinimum, Hdiag]

-- Proof sketch: evaluate the scalar dual function on `dom ψ ∩ ℝ₊` for the explicit data and
-- verify that the maximum is attained at the boundary multiplier `-H_min[Hdiag] = 1`.
/-- Proposition 4.1.15 (5): the scalar dual optimum for the explicit counterexample is attained
at the boundary multiplier `λ* = -H_min`. -/
theorem boundaryMultiplier_isMaxOn :
    IsMaxOn ψ Dplus (-H_min[Hdiag]) := by
  -- Rewrite the boundary multiplier to `1`, then compare every feasible dual value to `ψ 1`.
  rw [boundaryMultiplier_eq_one]
  rw [IsMaxOn, IsMaxFilter]
  change ∀ lam : ℝ, lam ∈ Dplus → ψ lam ≤ ψ 1
  intro lam hlam
  rw [dual_boundary_value_eq]
  exact dual_le_example_value lam

end CubicRegularizedQuadraticCounterexample
