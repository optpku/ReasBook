/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_24

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open WithLp (toLp)
open scoped BigOperators

section

variable {m n p : ℕ}
variable
  {f : (Fin n → ℝ) → EReal}
  {g : Fin m → (Fin n → ℝ) → EReal}
  {A : Matrix (Fin p) (Fin n) ℝ} {b : Fin p → ℝ}
  {xTilde : Fin n → ℝ}
  {fOpt rho1 rho2 delta : ℝ}

local notation "IneqSpace" => EuclideanSpace ℝ (Fin m)
local notation "EqSpace" => EuclideanSpace ℝ (Fin p)

/-- The explicit positive-part inequality residual associated to the `EReal` constraint vector
`g xTilde`, viewed as a real vector through `EReal.toReal`. -/
def positivePartIneqResidual
    (g : Fin m → (Fin n → ℝ) → EReal) (xTilde : Fin n → ℝ) :
    Fin m → ℝ :=
  fun i : Fin m ↦ max (EReal.toReal (g i xTilde)) 0

/-- The positive-part inequality residual at `xTilde`, viewed in the Euclidean space
`EuclideanSpace ℝ (Fin m)`. -/
abbrev positivePartIneqResidualVec
    (g : Fin m → (Fin n → ℝ) → EReal) (xTilde : Fin n → ℝ) : IneqSpace :=
  toLp 2 (positivePartIneqResidual g xTilde)

/-- The source-facing inequality-constraint vector `g xTilde`, viewed in the Euclidean space
`EuclideanSpace ℝ (Fin m)` through `EReal.toReal`. -/
abbrev inequalityConstraintVec
    (g : Fin m → (Fin n → ℝ) → EReal) (xTilde : Fin n → ℝ) : IneqSpace :=
  toLp 2 (fun i : Fin m ↦ EReal.toReal (g i xTilde))

/-- The affine equality residual `A xTilde + b`, viewed in the Euclidean space
`EuclideanSpace ℝ (Fin p)`. -/
abbrev equalityResidualVec
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) (xTilde : Fin n → ℝ) : EqSpace :=
  toLp 2 (A *ᵥ xTilde + b)

/-- The inequality-multiplier vector `y`, viewed in the Euclidean space
`EuclideanSpace ℝ (Fin m)`. -/
abbrev inequalityMultiplierVec (y : Fin m → ℝ) : IneqSpace :=
  toLp 2 y

/-- The equality-multiplier vector `z`, viewed in the Euclidean space
`EuclideanSpace ℝ (Fin p)`. -/
abbrev equalityMultiplierVec (z : Fin p → ℝ) : EqSpace :=
  toLp 2 z

variable
  {X : Set (Fin n → ℝ)}
  {yStar : Fin m → ℝ} {zStar : Fin p → ℝ}

/- Theorem 3.26 is `source-facing` in the affine-constrained perturbation/penalty API. Its
`core/canonical` owner abstraction is `IsDualOptimalSolution`; the chapter perturbation owner
`value_function` and the bridge theorem
`isDualOptimalSolution_iff_neg_pair_mem_subdifferential_valueFunction_zero` from
`Theorem_3_24` explain why this owner is canonical. This file keeps only the source-facing penalty
estimates and does not add a parallel local owner API on top of those declarations. -/
recall IsDualOptimalSolution
recall IsPrimalOptimalValue
recall isDualOptimalSolution_iff_neg_pair_mem_subdifferential_valueFunction_zero
recall is_convex_function
-- Leansearch only surfaced generic norm-dual bounds, not a more canonical penalty-bound theorem,
-- so this item stays on the local `IsDualOptimalSolution` / `value_function` chapter API.
-- The source display (3.68) writes `‖g(x̃)‖₂`; all label-associated clauses keep that explicit
-- Euclidean vector `inequalityConstraintVec g xTilde = toLp 2 (fun i ↦ (g i xTilde).toReal)` in
-- their public penalty hypothesis. The proof-side helper layer may still pass to the positive-part
-- residual `positivePartIneqResidualVec g xTilde`, matching the actual violation quantity
-- controlled by the proof.

/-- Objective-gap clause of Theorem 3.26: under the source strong-duality preamble and the
penalized estimate (3.68), the objective gap at `x̃` is bounded by `δ`. -/
theorem objective_gap_le_of_penalized_bound
    (hX_nonempty : X.Nonempty)
    (hX_convex : Convex ℝ X)
    (hf_convex : is_convex_function f)
    (hf_ne_bot : ∀ x : Fin n → ℝ, f x ≠ ⊥)
    (hg_convex : ∀ i : Fin m, is_convex_function (g i))
    (hg_ne_bot : ∀ i : Fin m, ∀ x : Fin n → ℝ, g i x ≠ ⊥)
    (hPrimal : IsPrimalOptimalValue X f g A b fOpt)
    (hDual : IsDualOptimalSolution X f g A b fOpt yStar zStar)
    (hxTilde : xTilde ∈ X)
    (hfTilde_ne_top : f xTilde ≠ ⊤)
    (hfTilde_ne_bot : f xTilde ≠ ⊥)
    (hgTilde_ne_top : ∀ i : Fin m, g i xTilde ≠ ⊤)
    (hgTilde_ne_bot : ∀ i : Fin m, g i xTilde ≠ ⊥)
    (hPenalty :
      (f xTilde).toReal - fOpt
        + rho1 * ‖inequalityConstraintVec g xTilde‖
        + rho2 * ‖equalityResidualVec A b xTilde‖ ≤ delta)
    (hDeltaPos : 0 < delta)
    (hRho1 : 2 * ‖inequalityMultiplierVec yStar‖ ≤ rho1)
    (hRho2 : 2 * ‖equalityMultiplierVec zStar‖ ≤ rho2) :
    (f xTilde).toReal - fOpt ≤ delta := by
  have _ := hX_nonempty
  have _ := hX_convex
  have _ := hf_convex
  have _ := hf_ne_bot
  have _ := hg_convex
  have _ := hg_ne_bot
  have _ := hPrimal
  have _ := hDual
  have _ := hxTilde
  have _ := hfTilde_ne_top
  have _ := hfTilde_ne_bot
  have _ := hgTilde_ne_top
  have _ := hgTilde_ne_bot
  have _ := hDeltaPos
  have hRho1Nonneg : 0 ≤ rho1 := by
    nlinarith [norm_nonneg (inequalityMultiplierVec yStar), hRho1]
  have hRho2Nonneg : 0 ≤ rho2 := by
    nlinarith [norm_nonneg (equalityMultiplierVec zStar), hRho2]
  -- Drop the two nonnegative penalty terms from the source penalized estimate.
  have hPenalty1 : 0 ≤ rho1 * ‖inequalityConstraintVec g xTilde‖ := by
    exact mul_nonneg hRho1Nonneg (norm_nonneg _)
  have hPenalty2 : 0 ≤ rho2 * ‖equalityResidualVec A b xTilde‖ := by
    exact mul_nonneg hRho2Nonneg (norm_nonneg _)
  nlinarith

/-- Helper for Theorem 3.26: the Euclidean norm of the coordinatewise positive part of the
constraint vector is bounded by the Euclidean norm of the full real constraint vector. -/
lemma positivePartIneqResidualVec_norm_le_constraintNorm
    (g : Fin m → (Fin n → ℝ) → EReal) (xTilde : Fin n → ℝ) :
    ‖positivePartIneqResidualVec g xTilde‖ ≤ ‖inequalityConstraintVec g xTilde‖ := by
  have hcoord :
      ∀ i : Fin m,
        ‖positivePartIneqResidualVec g xTilde i‖ ^ (2 : ℕ) ≤
          ‖inequalityConstraintVec g xTilde i‖ ^ (2 : ℕ) := by
    intro i
    have hcoordNorm :
        ‖positivePartIneqResidualVec g xTilde i‖ ≤ ‖inequalityConstraintVec g xTilde i‖ := by
      by_cases hi : 0 ≤ EReal.toReal (g i xTilde)
      · simp [positivePartIneqResidual, hi]
      · have hi' : EReal.toReal (g i xTilde) ≤ 0 := le_of_not_ge hi
        simp [positivePartIneqResidual, hi']
    nlinarith [hcoordNorm, norm_nonneg (positivePartIneqResidualVec g xTilde i),
      norm_nonneg (inequalityConstraintVec g xTilde i)]
  have hPosSq :
      ‖positivePartIneqResidualVec g xTilde‖ ^ (2 : ℕ) =
        ∑ i : Fin m, ‖positivePartIneqResidualVec g xTilde i‖ ^ (2 : ℕ) := by
    simpa using
      (PiLp.norm_sq_eq_of_L2 (fun _ : Fin m ↦ ℝ) (positivePartIneqResidualVec g xTilde))
  have hConstraintSq :
      ‖inequalityConstraintVec g xTilde‖ ^ (2 : ℕ) =
        ∑ i : Fin m, ‖inequalityConstraintVec g xTilde i‖ ^ (2 : ℕ) := by
    simpa using
      (PiLp.norm_sq_eq_of_L2 (fun _ : Fin m ↦ ℝ) (inequalityConstraintVec g xTilde))
  have hSq :
      ‖positivePartIneqResidualVec g xTilde‖ ^ (2 : ℕ) ≤
        ‖inequalityConstraintVec g xTilde‖ ^ (2 : ℕ) := by
    rw [hPosSq, hConstraintSq]
    exact Finset.sum_le_sum fun i _ ↦ hcoord i
  -- Compare the two nonnegative norms through their squares.
  nlinarith [hSq, norm_nonneg (positivePartIneqResidualVec g xTilde),
    norm_nonneg (inequalityConstraintVec g xTilde)]

/-- Proof-side helper: the source penalty term (3.68) controls the positive-part inequality
residual once `ρ₁` is known to be nonnegative. -/
theorem positive_part_penalized_bound_of_penalized_bound
    (hPenalty :
      (f xTilde).toReal - fOpt
        + rho1 * ‖inequalityConstraintVec g xTilde‖
        + rho2 * ‖equalityResidualVec A b xTilde‖ ≤ delta)
    (hRho1Nonneg : 0 ≤ rho1) :
    (f xTilde).toReal - fOpt
      + rho1 * ‖positivePartIneqResidualVec g xTilde‖
      + rho2 * ‖equalityResidualVec A b xTilde‖ ≤ delta := by
  have hNorm :
      ‖positivePartIneqResidualVec g xTilde‖ ≤ ‖inequalityConstraintVec g xTilde‖ :=
    positivePartIneqResidualVec_norm_le_constraintNorm g xTilde
  -- Replace the source penalty norm by the smaller positive-part norm.
  have hScaled :
      rho1 * ‖positivePartIneqResidualVec g xTilde‖ ≤
        rho1 * ‖inequalityConstraintVec g xTilde‖ := by
    exact mul_le_mul_of_nonneg_left hNorm hRho1Nonneg
  have hMonotone :
      (f xTilde).toReal - fOpt
          + rho1 * ‖positivePartIneqResidualVec g xTilde‖
          + rho2 * ‖equalityResidualVec A b xTilde‖
        ≤
          (f xTilde).toReal - fOpt
            + rho1 * ‖inequalityConstraintVec g xTilde‖
            + rho2 * ‖equalityResidualVec A b xTilde‖ := by
    nlinarith
  exact hMonotone.trans hPenalty

/-- Helper for Theorem 3.26: the perturbation slice built from the positive-part inequality
residual and the affine equality residual contains `xTilde` itself. -/
lemma xTilde_mem_valueFunctionFeasibleSet_positivePart
    (hxTilde : xTilde ∈ X)
    (hgTilde_ne_top : ∀ i : Fin m, g i xTilde ≠ ⊤)
    (hgTilde_ne_bot : ∀ i : Fin m, g i xTilde ≠ ⊥) :
    toLp 2 xTilde ∈
      value_function_feasible_set
        (toLp 2 '' X)
        (fun i x ↦ g i (WithLp.ofLp x))
        A.toEuclideanLin
        (toLp 2 b)
        (positivePartIneqResidualVec g xTilde)
        (equalityResidualVec A b xTilde) := by
  rw [mem_value_function_feasible_set]
  have hxImage : toLp 2 xTilde ∈ toLp 2 '' X := by
    have hxEq : toLp 2 xTilde = toLp 2 xTilde := rfl
    exact ⟨xTilde, hxTilde, hxEq⟩
  have hIneq :
      ∀ i : Fin m,
        g i (WithLp.ofLp (toLp 2 xTilde)) ≤ positivePartIneqResidualVec g xTilde i := by
    intro i
    have hgi :
        g i xTilde = ((((g i xTilde).toReal : ℝ)) : EReal) := by
      rw [EReal.coe_toReal (hgTilde_ne_top i) (hgTilde_ne_bot i)]
    have hle :
        g i xTilde ≤ ((((max (EReal.toReal (g i xTilde)) 0 : ℝ))) : EReal) := by
      rw [hgi]
      exact_mod_cast le_max_left (EReal.toReal (g i xTilde)) 0
    simpa [positivePartIneqResidualVec, positivePartIneqResidual] using hle
  have hEq :
      A.toEuclideanLin (toLp 2 xTilde) + toLp 2 b = equalityResidualVec A b xTilde := by
    simp [equalityResidualVec, Matrix.toLpLin_toLp]
  -- Repackage the primal point as a witness in the perturbation feasible slice.
  exact ⟨hxImage, hIneq, hEq⟩

/-- Proof-side shifted-coefficient estimate used in Theorem 3.26: combining the penalized upper
bound with the dual lower bound yields the residual inequality whose coefficients are shifted by
the Euclidean norms of the optimal multipliers. -/
theorem combined_residual_bound_of_penalized_bound
    (hDual : IsDualOptimalSolution X f g A b fOpt yStar zStar)
    (hxTilde : xTilde ∈ X)
    (hfTilde_ne_top : f xTilde ≠ ⊤)
    (hfTilde_ne_bot : f xTilde ≠ ⊥)
    (hgTilde_ne_top : ∀ i : Fin m, g i xTilde ≠ ⊤)
    (hgTilde_ne_bot : ∀ i : Fin m, g i xTilde ≠ ⊥)
    (hPenalty :
      (f xTilde).toReal - fOpt
        + rho1 * ‖positivePartIneqResidualVec g xTilde‖
        + rho2 * ‖equalityResidualVec A b xTilde‖ ≤ delta)
    :
    (rho1 - ‖inequalityMultiplierVec yStar‖) * ‖positivePartIneqResidualVec g xTilde‖
      + (rho2 - ‖equalityMultiplierVec zStar‖) * ‖equalityResidualVec A b xTilde‖ ≤ delta := by
  let _ := hfTilde_ne_bot
  let u : IneqSpace := positivePartIneqResidualVec g xTilde
  let t : EqSpace := equalityResidualVec A b xTilde
  have hFeasible :
      toLp 2 xTilde ∈
        value_function_feasible_set
          (toLp 2 '' X)
          (fun i x ↦ g i (WithLp.ofLp x))
          A.toEuclideanLin
          (toLp 2 b)
          u
          t := by
    simpa [u, t] using
      xTilde_mem_valueFunctionFeasibleSet_positivePart
        (X := X) (g := g) (A := A) (b := b) (xTilde := xTilde)
        hxTilde hgTilde_ne_top hgTilde_ne_bot
  have hLowerE :
      ((fOpt : EReal) + (((negPerturbationDualPair yStar zStar) (u, t) : ℝ) : EReal))
        ≤ f xTilde := by
    -- Apply the chapter lower-support inequality at the perturbation slice carried by `xTilde`.
    simpa using
      dualLowerBoundAtValueFunctionFeasiblePoint
        X f g A b fOpt yStar zStar hDual hFeasible
  have hLower :
      fOpt + ((negPerturbationDualPair yStar zStar) (u, t) : ℝ) ≤ (f xTilde).toReal := by
    have hLowerToReal :
        (((fOpt : EReal) + (((negPerturbationDualPair yStar zStar) (u, t) : ℝ) : EReal)).toReal)
          ≤ (f xTilde).toReal := by
      exact EReal.toReal_le_toReal hLowerE (by simp) hfTilde_ne_top
    simpa using hLowerToReal
  have hPairEval :
      ((negPerturbationDualPair yStar zStar) (u, t) : ℝ) =
        -(inner ℝ (inequalityMultiplierVec yStar) u) -
          inner ℝ (equalityMultiplierVec zStar) t := by
    have hIneqInner :
        inner ℝ (inequalityMultiplierVec yStar) u = ∑ i : Fin m, yStar i * u i := by
      simp [inequalityMultiplierVec, PiLp.inner_apply, mul_comm]
    have hEqInner :
        inner ℝ (equalityMultiplierVec zStar) t = ∑ j : Fin p, zStar j * t j := by
      simp [equalityMultiplierVec, PiLp.inner_apply, mul_comm]
    calc
      ((negPerturbationDualPair yStar zStar) (u, t) : ℝ)
          = -∑ i : Fin m, yStar i * u i - ∑ j : Fin p, zStar j * t j := by
              rw [negPerturbationDualPair_apply]
      _ = -(inner ℝ (inequalityMultiplierVec yStar) u) -
            inner ℝ (equalityMultiplierVec zStar) t := by
            rw [hIneqInner, hEqInner]
  have hPairLower :
      -(‖inequalityMultiplierVec yStar‖ * ‖u‖) - ‖equalityMultiplierVec zStar‖ * ‖t‖
        ≤ ((negPerturbationDualPair yStar zStar) (u, t) : ℝ) := by
    have hIneqInner :
        inner ℝ (inequalityMultiplierVec yStar) u ≤ ‖inequalityMultiplierVec yStar‖ * ‖u‖ := by
      simpa using real_inner_le_norm (inequalityMultiplierVec yStar) u
    have hEqInner :
        inner ℝ (equalityMultiplierVec zStar) t ≤ ‖equalityMultiplierVec zStar‖ * ‖t‖ := by
      simpa using real_inner_le_norm (equalityMultiplierVec zStar) t
    rw [hPairEval]
    nlinarith
  have hObjectiveLower :
      -(‖inequalityMultiplierVec yStar‖ * ‖u‖) - ‖equalityMultiplierVec zStar‖ * ‖t‖
        ≤ (f xTilde).toReal - fOpt := by
    nlinarith
  -- Combine the lower support estimate with the penalized upper bound.
  have hCombinedU :
      (rho1 - ‖inequalityMultiplierVec yStar‖) * ‖u‖
        + (rho2 - ‖equalityMultiplierVec zStar‖) * ‖t‖ ≤ delta := by
    nlinarith
  simpa [u, t] using hCombinedU

-- Proof sketch: first pass from the source penalty estimate on `‖inequalityConstraintVec g xTilde‖`
-- to the proof-side positive-part penalty estimate, then use the same dual-optimal affine lower
-- bound from Theorem 3.24 evaluated at the Euclidean bridge points
-- `u = positivePartIneqResidualVec g xTilde` and `t = equalityResidualVec A b xTilde`.
-- Combining that lower bound with the positive-part penalized estimate yields the proof-side
-- shifted-coefficient inequality
-- `(rho1 - ‖inequalityMultiplierVec yStar‖) * ‖positivePartIneqResidualVec g xTilde‖ +
--   (rho2 - ‖equalityMultiplierVec zStar‖) * ‖equalityResidualVec A b xTilde‖ ≤ delta`.
-- The extra assumption `2 * ‖equalityMultiplierVec zStar‖ ≤ rho2` makes the equality-residual
-- term nonnegative, so it may be discarded; the assumptions `0 < rho1` and
-- `2 * ‖inequalityMultiplierVec yStar‖ ≤ rho1` then give
-- the stated `2 / rho1` bound.
/-- Theorem 3.26 (2): under the source strong-duality preamble and the penalized estimate (3.68),
the positive-part inequality-residual vector `fun i ↦ max ((g i xTilde).toReal) 0` at `x̃`,
measured in the Euclidean norm on `WithLp 2 (Fin m → ℝ)`, is bounded by `(2 / ρ₁) δ` when the
penalty parameter `ρ₁` dominates the Euclidean norm of the inequality multiplier and `ρ₂` is at
least the Euclidean norm of the equality multiplier. -/
theorem positive_constraint_violation_le_two_div_rho1_of_penalized_bound
    (hX_nonempty : X.Nonempty)
    (hX_convex : Convex ℝ X)
    (hf_convex : is_convex_function f)
    (hf_ne_bot : ∀ x : Fin n → ℝ, f x ≠ ⊥)
    (hg_convex : ∀ i : Fin m, is_convex_function (g i))
    (hg_ne_bot : ∀ i : Fin m, ∀ x : Fin n → ℝ, g i x ≠ ⊥)
    (hPrimal : IsPrimalOptimalValue X f g A b fOpt)
    (hDual : IsDualOptimalSolution X f g A b fOpt yStar zStar)
    (hxTilde : xTilde ∈ X)
    (hfTilde_ne_top : f xTilde ≠ ⊤)
    (hfTilde_ne_bot : f xTilde ≠ ⊥)
    (hgTilde_ne_top : ∀ i : Fin m, g i xTilde ≠ ⊤)
    (hgTilde_ne_bot : ∀ i : Fin m, g i xTilde ≠ ⊥)
    (hPenalty :
      (f xTilde).toReal - fOpt
        + rho1 * ‖inequalityConstraintVec g xTilde‖
        + rho2 * ‖equalityResidualVec A b xTilde‖ ≤ delta)
    (hDeltaPos : 0 < delta)
    (hRho1 : 2 * ‖inequalityMultiplierVec yStar‖ ≤ rho1)
    (hRho2 : 2 * ‖equalityMultiplierVec zStar‖ ≤ rho2)
    (hRho1Pos : 0 < rho1)
    :
    ‖positivePartIneqResidualVec g xTilde‖ ≤ (2 / rho1) * delta := by
  have _ := hX_nonempty
  have _ := hX_convex
  have _ := hf_convex
  have _ := hf_ne_bot
  have _ := hg_convex
  have _ := hg_ne_bot
  have _ := hPrimal
  have _ := hDeltaPos
  have hRho1Nonneg : 0 ≤ rho1 := le_of_lt hRho1Pos
  have hPenaltyPositivePart :
      (f xTilde).toReal - fOpt
        + rho1 * ‖positivePartIneqResidualVec g xTilde‖
        + rho2 * ‖equalityResidualVec A b xTilde‖ ≤ delta := by
    exact positive_part_penalized_bound_of_penalized_bound hPenalty hRho1Nonneg
  have hCombined :
      (rho1 - ‖inequalityMultiplierVec yStar‖) * ‖positivePartIneqResidualVec g xTilde‖
        + (rho2 - ‖equalityMultiplierVec zStar‖) * ‖equalityResidualVec A b xTilde‖ ≤ delta := by
    exact combined_residual_bound_of_penalized_bound
      (X := X) (f := f) (g := g) (A := A) (b := b) (xTilde := xTilde)
      (fOpt := fOpt) (rho1 := rho1) (rho2 := rho2) (delta := delta)
      (yStar := yStar) (zStar := zStar)
      hDual hxTilde hfTilde_ne_top hfTilde_ne_bot hgTilde_ne_top hgTilde_ne_bot
      hPenaltyPositivePart
  have hEqCoeffNonneg : 0 ≤ rho2 - ‖equalityMultiplierVec zStar‖ := by
    nlinarith [hRho2, norm_nonneg (equalityMultiplierVec zStar)]
  have hEqTermNonneg :
      0 ≤ (rho2 - ‖equalityMultiplierVec zStar‖) * ‖equalityResidualVec A b xTilde‖ := by
    exact mul_nonneg hEqCoeffNonneg (norm_nonneg _)
  have hMain :
      (rho1 - ‖inequalityMultiplierVec yStar‖) * ‖positivePartIneqResidualVec g xTilde‖ ≤
        delta := by
    nlinarith
  have hCoeffHalf :
      rho1 / 2 ≤ rho1 - ‖inequalityMultiplierVec yStar‖ := by
    nlinarith
  have hHalfScaled :
      (rho1 / 2) * ‖positivePartIneqResidualVec g xTilde‖ ≤
        (rho1 - ‖inequalityMultiplierVec yStar‖) * ‖positivePartIneqResidualVec g xTilde‖ := by
    exact mul_le_mul_of_nonneg_right hCoeffHalf (norm_nonneg _)
  have hRhoHalf :
      (rho1 / 2) * ‖positivePartIneqResidualVec g xTilde‖ ≤ delta := by
    exact hHalfScaled.trans hMain
  -- The coefficient comparison `ρ₁ / 2 ≤ ρ₁ - ‖y*‖` turns the shifted estimate into the
  -- advertised `(2 / ρ₁) δ` bound.
  have hDiv :
      ‖positivePartIneqResidualVec g xTilde‖ ≤ delta / (rho1 / 2) := by
    have hHalfPos : 0 < rho1 / 2 := by
      positivity
    -- Rewrite the scaled estimate into the multiplication order expected by `le_div_iff₀`.
    have hRhoHalf' :
        ‖positivePartIneqResidualVec g xTilde‖ * (rho1 / 2) ≤ delta := by
      simpa [mul_comm] using hRhoHalf
    exact (le_div_iff₀ hHalfPos).2 hRhoHalf'
  have hRewrite : delta / (rho1 / 2) = (2 / rho1) * delta := by
    field_simp [hRho1Pos.ne']
  rw [← hRewrite]
  exact hDiv

-- Proof sketch: first pass from the source penalty estimate on `‖inequalityConstraintVec g xTilde‖`
-- to the proof-side positive-part penalty estimate, then use the same dual-optimal affine lower
-- bound with value `fOpt`, `u = positivePartIneqResidualVec g xTilde` and
-- `t = equalityResidualVec A b xTilde`.
-- This yields the proof-side shifted-coefficient inequality
-- `(rho1 - ‖inequalityMultiplierVec yStar‖) * ‖positivePartIneqResidualVec g xTilde‖ +
--   (rho2 - ‖equalityMultiplierVec zStar‖) * ‖equalityResidualVec A b xTilde‖ ≤ delta`.
-- The extra assumption `2 * ‖inequalityMultiplierVec yStar‖ ≤ rho1` makes the
-- inequality-violation term
-- nonnegative,
-- so it may be discarded; the assumptions `0 < rho2` and
-- `2 * ‖equalityMultiplierVec zStar‖ ≤ rho2` then give
-- the claimed residual bound.
/-- Equality-residual clause of Theorem 3.26: under the source strong-duality preamble and the
penalized estimate (3.68), the equality constraint residual at `x̃`, measured in the Euclidean
norm on `WithLp 2 (Fin p → ℝ)`, is bounded by `(2 / ρ₂) δ` when the penalty parameter `ρ₂`
dominates the Euclidean norm of the equality multiplier and `ρ₁` is at least the Euclidean norm
of the inequality multiplier. -/
theorem equality_constraint_residual_le_two_div_rho2_of_penalized_bound
    (hX_nonempty : X.Nonempty)
    (hX_convex : Convex ℝ X)
    (hf_convex : is_convex_function f)
    (hf_ne_bot : ∀ x : Fin n → ℝ, f x ≠ ⊥)
    (hg_convex : ∀ i : Fin m, is_convex_function (g i))
    (hg_ne_bot : ∀ i : Fin m, ∀ x : Fin n → ℝ, g i x ≠ ⊥)
    (hPrimal : IsPrimalOptimalValue X f g A b fOpt)
    (hDual : IsDualOptimalSolution X f g A b fOpt yStar zStar)
    (hxTilde : xTilde ∈ X)
    (hfTilde_ne_top : f xTilde ≠ ⊤)
    (hfTilde_ne_bot : f xTilde ≠ ⊥)
    (hgTilde_ne_top : ∀ i : Fin m, g i xTilde ≠ ⊤)
    (hgTilde_ne_bot : ∀ i : Fin m, g i xTilde ≠ ⊥)
    (hPenalty :
      (f xTilde).toReal - fOpt
        + rho1 * ‖inequalityConstraintVec g xTilde‖
        + rho2 * ‖equalityResidualVec A b xTilde‖ ≤ delta)
    (hDeltaPos : 0 < delta)
    (hRho1 : 2 * ‖inequalityMultiplierVec yStar‖ ≤ rho1)
    (hRho2 : 2 * ‖equalityMultiplierVec zStar‖ ≤ rho2)
    (hRho2Pos : 0 < rho2)
    :
    ‖equalityResidualVec A b xTilde‖ ≤ (2 / rho2) * delta := by
  have _ := hX_nonempty
  have _ := hX_convex
  have _ := hf_convex
  have _ := hf_ne_bot
  have _ := hg_convex
  have _ := hg_ne_bot
  have _ := hPrimal
  have _ := hDeltaPos
  have hRho1Nonneg : 0 ≤ rho1 := by
    nlinarith [norm_nonneg (inequalityMultiplierVec yStar), hRho1]
  have hPenaltyPositivePart :
      (f xTilde).toReal - fOpt
        + rho1 * ‖positivePartIneqResidualVec g xTilde‖
        + rho2 * ‖equalityResidualVec A b xTilde‖ ≤ delta := by
    exact positive_part_penalized_bound_of_penalized_bound hPenalty hRho1Nonneg
  have hCombined :
      (rho1 - ‖inequalityMultiplierVec yStar‖) * ‖positivePartIneqResidualVec g xTilde‖
        + (rho2 - ‖equalityMultiplierVec zStar‖) * ‖equalityResidualVec A b xTilde‖ ≤ delta := by
    exact combined_residual_bound_of_penalized_bound
      (X := X) (f := f) (g := g) (A := A) (b := b) (xTilde := xTilde)
      (fOpt := fOpt) (rho1 := rho1) (rho2 := rho2) (delta := delta)
      (yStar := yStar) (zStar := zStar)
      hDual hxTilde hfTilde_ne_top hfTilde_ne_bot hgTilde_ne_top hgTilde_ne_bot hPenaltyPositivePart
  have hIneqCoeffNonneg : 0 ≤ rho1 - ‖inequalityMultiplierVec yStar‖ := by
    nlinarith [hRho1, norm_nonneg (inequalityMultiplierVec yStar)]
  have hIneqTermNonneg :
      0 ≤ (rho1 - ‖inequalityMultiplierVec yStar‖) * ‖positivePartIneqResidualVec g xTilde‖ := by
    exact mul_nonneg hIneqCoeffNonneg (norm_nonneg _)
  have hMain :
      (rho2 - ‖equalityMultiplierVec zStar‖) * ‖equalityResidualVec A b xTilde‖ ≤ delta := by
    nlinarith
  have hCoeffHalf :
      rho2 / 2 ≤ rho2 - ‖equalityMultiplierVec zStar‖ := by
    nlinarith
  have hHalfScaled :
      (rho2 / 2) * ‖equalityResidualVec A b xTilde‖ ≤
        (rho2 - ‖equalityMultiplierVec zStar‖) * ‖equalityResidualVec A b xTilde‖ := by
    exact mul_le_mul_of_nonneg_right hCoeffHalf (norm_nonneg _)
  have hRhoHalf :
      (rho2 / 2) * ‖equalityResidualVec A b xTilde‖ ≤ delta := by
    exact hHalfScaled.trans hMain
  -- The same shifted-coefficient argument now isolates the equality residual.
  have hDiv :
      ‖equalityResidualVec A b xTilde‖ ≤ delta / (rho2 / 2) := by
    have hHalfPos : 0 < rho2 / 2 := by
      positivity
    -- Rewrite the scaled estimate into the multiplication order expected by `le_div_iff₀`.
    have hRhoHalf' :
        ‖equalityResidualVec A b xTilde‖ * (rho2 / 2) ≤ delta := by
      simpa [mul_comm] using hRhoHalf
    exact (le_div_iff₀ hHalfPos).2 hRhoHalf'
  have hRewrite : delta / (rho2 / 2) = (2 / rho2) * delta := by
    field_simp [hRho2Pos.ne']
  rw [← hRewrite]
  exact hDiv

end
