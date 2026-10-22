/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_8
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_11
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_68
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SoftThreshold
open scoped InnerProduct
open ContinuousLinearMap

universe u v

section

variable {X : Type u} {ι : Type v}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled from the nearby
Chapter 15 ADMM files together with the Chapter 6 soft-threshold owner.

This item is `source-facing`: Algorithm 15.12 gives explicit formulas for the linear solve
`x^(k+1)` and shifted soft-thresholding step `z^(k+1)`, together with the induced iterate
sequences.

- `source-facing`: the displayed linear-solve owner `admm_linear_composite_v2_x_update`;
- `core/canonical`: `admm_x_update_argmin`, `admm_z_update_argmin`, and
  `admm_multiplier_update` from Algorithm 15.3 for the per-step ADMM minimization and multiplier
  owners;
- `bridge/view`: `ContinuousLinearMap.adjoint` and `ContinuousLinearMap.inverse`;
- `bridge/view`: `admm_linear_composite_shifted_l1_regularizer` and
  `admm_linear_composite_shifted_l1_z_update` as the shared shifted `ℓ¹` owners for the
  linear-composite `z`-subproblem;
- `bridge/view`: `T_[·]`, `prox_euclidean_l1_eq_singleton_softThreshold`, and
  `proximal_mapping_scaling_translation` from Chapter 6 for the explicit soft-threshold formula;
- `source-facing`: the displayed resolvent and the recursive iterate sequences themselves.

Primitive data are therefore only the explicit formulas and iterate sequences. The `x`-solve lives
most canonically on the continuous operator owner `A : X →L[ℝ] E`; the canonical ADMM `arg min`
and multiplier clauses are derived API and should not be duplicated by a parallel owner.

Since the soft-thresholding formula is genuinely coordinatewise, the residual space is kept in the
canonical Euclidean finite-product model `EuclideanSpace ℝ ι`, specializing to the textbook
matrix-vector setting `ℝ^m` when `ι = Fin m`.

`lean_leansearch` was checked for generic recursive-iterate owners and only returned generic
iterate lemmas, so the public owner/API split here follows the local Chapter 15 ADMM precedent. -/

/-- The explicit Algorithm 15.12 `x`-update:
`x^(k+1) = (I + Aᵀ A)⁻¹ (Aᵀ (z^k - (1 / ρ) y₁^k) + x^k)`. -/
def admm_linear_composite_v2_x_update
    (ρ : PosReal) (A : X →L[ℝ] E) (zk y1k : E) (xk : X) : X :=
  ((1 + A† ∘L A).inverse) (A.adjoint (zk - (1 / (ρ : ℝ)) • y1k) + xk)

/-- Expanding `admm_linear_composite_v2_x_update` gives the displayed linear-solve formula for
Algorithm 15.12. -/
@[simp] theorem admm_linear_composite_v2_x_update_eq
    (ρ : PosReal) (A : X →L[ℝ] E) (zk y1k : E) (xk : X) :
    admm_linear_composite_v2_x_update ρ A zk y1k xk =
      ((1 + A† ∘L A).inverse) (A.adjoint (zk - (1 / (ρ : ℝ)) • y1k) + xk) :=
  rfl

/-- Helper for Algorithm 15.12: the normal operator `1 + A† ∘L A` is invertible, so the explicit
`x`-update resolvent is well-defined. -/
lemma admmLinearCompositeV2_xResolvent_isInvertible
    (A : X →L[ℝ] E) :
    (1 + A† ∘L A).IsInvertible := by
  -- The positive Gram shift gives the resolvent operator a bounded inverse.
  simpa [one_smul, add_comm] using
    (gram_shift_isInvertible_of_pos (A := A.adjoint) 1 zero_lt_one)

/-- Helper for Algorithm 15.12: the explicit resolvent point satisfies the normal equation
`u - xk + A† (A u - c) = 0`. -/
lemma admmLinearCompositeV2_xUpdate_normalEquationZero
    (A : X →L[ℝ] E) (c : E) (xk u : X)
    (hu : u = ((1 + A† ∘L A).inverse) (A.adjoint c + xk)) :
    u - xk + A.adjoint (A u - c) = 0 := by
  have hInv : (1 + A† ∘L A).IsInvertible :=
    admmLinearCompositeV2_xResolvent_isInvertible (A := A)
  -- Apply the inverse once, then rewrite the result into the cancellation-friendly form.
  have hu_apply :
      (1 + A† ∘L A) u = A.adjoint c + xk := by
    rw [hu]
    exact hInv.self_apply_inverse (A.adjoint c + xk)
  have hu' :
      u + A.adjoint (A u) = A.adjoint c + xk := by
    simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply] using hu_apply
  calc
    u - xk + A.adjoint (A u - c)
        = u - xk + (A.adjoint (A u) - A.adjoint c) := by
            rw [map_sub]
    _ = (u + A.adjoint (A u)) - (A.adjoint c + xk) := by
            module
    _ = 0 := by
            exact sub_eq_zero.mpr hu'

/-- Helper for Algorithm 15.12: centering the repaired quadratic `x`-objective at the explicit
resolvent point leaves only nonnegative quadratic error terms. -/
lemma admmLinearCompositeV2_xUpdate_crossTermZero
    (A : X →L[ℝ] E) (c : E) (xk u : X)
    (hu : u = ((1 + A† ∘L A).inverse) (A.adjoint c + xk))
    (δ : X) :
    inner ℝ (u - xk) δ + inner ℝ (A u - c) (A δ) = 0 := by
  -- Pair the normal equation with `δ` so the mixed term becomes a single inner-product identity.
  have hinner :
      inner ℝ (u - xk) δ + inner ℝ (A.adjoint (A u - c)) δ = 0 := by
    simpa [inner_add_left] using
      congrArg (fun w : X ↦ inner ℝ w δ)
        (admmLinearCompositeV2_xUpdate_normalEquationZero
          (A := A) (c := c) (xk := xk) (u := u) hu)
  -- Rewrite the adjoint term back to the residual form used in the quadratic expansion.
  calc
    inner ℝ (u - xk) δ + inner ℝ (A u - c) (A δ)
        = inner ℝ (u - xk) δ + inner ℝ (A.adjoint (A u - c)) δ := by
            rw [← A.adjoint_inner_left δ (A u - c)]
    _ = 0 := hinner

section

omit [CompleteSpace X]

/-- Helper for Algorithm 15.12: centering the repaired quadratic `x`-objective at the explicit
resolvent point leaves only nonnegative quadratic error terms. -/
lemma admmLinearCompositeV2_xUpdate_remainderNormalForm
    (A : X →L[ℝ] E) (c : E) (x u : X) :
    (A x - c) - (A u - c) = A (x - u) := by
  -- Route correction: normalize the residual difference directly before the quadratic expansion
  -- so the final arithmetic step does not have to guess the right operator normal form.
  calc
    (A x - c) - (A u - c) = A x - A u := by
      module
    _ = A (x - u) := by
      rw [map_sub]

end

/-- Helper for Algorithm 15.12: centering the repaired quadratic `x`-objective at the explicit
resolvent point leaves only nonnegative quadratic error terms. -/
lemma admmLinearCompositeV2_xUpdate_objective_center_add_error
    (A : X →L[ℝ] E) (c : E) (xk u x : X)
    (hu : u = ((1 + A† ∘L A).inverse) (A.adjoint c + xk)) :
    ((1 / 2 : ℝ) * ‖x - xk‖ ^ (2 : ℕ) +
        (1 / 2 : ℝ) * ‖A x - c‖ ^ (2 : ℕ)) =
      ((1 / 2 : ℝ) * ‖u - xk‖ ^ (2 : ℕ) +
          (1 / 2 : ℝ) * ‖A u - c‖ ^ (2 : ℕ)) +
        ((1 / 2 : ℝ) * ‖x - u‖ ^ (2 : ℕ) +
          (1 / 2 : ℝ) * ‖A (x - u)‖ ^ (2 : ℕ)) := by
  let δ : X := x - u
  have hx : x = u + δ := by
    -- Recenter `x` at the explicit resolvent point plus the displacement `δ`.
    dsimp [δ]
    calc
      x = x - u + u := by
        exact (sub_add_cancel x u).symm
      _ = u + (x - u) := by
        module
  have hxShift : x - xk = (u - xk) + δ := by
    -- Rewrite the primal displacement into the centered point plus the error term.
    calc
      x - xk = (u + δ) - xk := by
        rw [hx]
      _ = (u - xk) + δ := by
        module
  have hResidualDiff : (A x - c) - (A u - c) = A δ := by
    -- Use the directed residual bridge instead of broad normalization on the operator term.
    dsimp [δ]
    exact
      admmLinearCompositeV2_xUpdate_remainderNormalForm (A := A) (c := c) (x := x) (u := u)
  have hResidualShift : A x - c = (A u - c) + A δ := by
    -- Express the residual at `x` as the centered residual plus the transported displacement.
    calc
      A x - c = (A u - c) + ((A x - c) - (A u - c)) := by
        module
      _ = (A u - c) + A δ := by
        rw [hResidualDiff]
  have hcross :
      inner ℝ (u - xk) δ + inner ℝ (A u - c) (A δ) = 0 := by
    -- The normal equation kills the mixed term in the completed-square expansion.
    exact
      admmLinearCompositeV2_xUpdate_crossTermZero
        (A := A) (c := c) (xk := xk) (u := u) hu δ
  have hexpanded :
      ((1 / 2 : ℝ) * ‖(u - xk) + δ‖ ^ (2 : ℕ) +
          (1 / 2 : ℝ) * ‖(A u - c) + A δ‖ ^ (2 : ℕ)) =
        ((1 / 2 : ℝ) * ‖u - xk‖ ^ (2 : ℕ) +
            (1 / 2 : ℝ) * ‖A u - c‖ ^ (2 : ℕ)) +
          ((1 / 2 : ℝ) * ‖δ‖ ^ (2 : ℕ) +
            (1 / 2 : ℝ) * ‖A δ‖ ^ (2 : ℕ)) := by
    -- Expand both squared norms and cancel the mixed term with the normal equation.
    rw [norm_add_sq_real, norm_add_sq_real]
    nlinarith [hcross]
  calc
    ((1 / 2 : ℝ) * ‖x - xk‖ ^ (2 : ℕ) +
        (1 / 2 : ℝ) * ‖A x - c‖ ^ (2 : ℕ)) =
      ((1 / 2 : ℝ) * ‖(u - xk) + δ‖ ^ (2 : ℕ) +
          (1 / 2 : ℝ) * ‖(A u - c) + A δ‖ ^ (2 : ℕ)) := by
            rw [hxShift, hResidualShift]
    _ =
      ((1 / 2 : ℝ) * ‖u - xk‖ ^ (2 : ℕ) +
          (1 / 2 : ℝ) * ‖A u - c‖ ^ (2 : ℕ)) +
        ((1 / 2 : ℝ) * ‖δ‖ ^ (2 : ℕ) +
          (1 / 2 : ℝ) * ‖A δ‖ ^ (2 : ℕ)) := hexpanded
    _ =
      ((1 / 2 : ℝ) * ‖u - xk‖ ^ (2 : ℕ) +
          (1 / 2 : ℝ) * ‖A u - c‖ ^ (2 : ℕ)) +
        ((1 / 2 : ℝ) * ‖x - u‖ ^ (2 : ℕ) +
          (1 / 2 : ℝ) * ‖A (x - u)‖ ^ (2 : ℕ)) := by
            simp [δ]

/-- Helper for Algorithm 15.12: the explicit resolvent point globally minimizes the quadratic
`x`-subproblem from the specialized ADMM update. -/
lemma admmLinearCompositeV2_xUpdate_isMinOnCore
    (ρ : PosReal) (A : X →L[ℝ] E) (zk y1k : E) (xk : X) :
    IsMinOn
      (fun x : X ↦
        ((((1 / 2 : ℝ) * ‖x - xk‖ ^ (2 : ℕ) : ℝ) : EReal)) +
          ((((1 / 2 : ℝ) * ‖A x - zk + (1 / (ρ : ℝ)) • y1k‖ ^ (2 : ℕ) : ℝ) : EReal)))
      Set.univ
      (admm_linear_composite_v2_x_update ρ A zk y1k xk) := by
  let c : E := zk - (1 / (ρ : ℝ)) • y1k
  let u : X := admm_linear_composite_v2_x_update ρ A zk y1k xk
  have hu : u = ((1 + A† ∘L A).inverse) (A.adjoint c + xk) := by
    simp [u, c]
  rw [isMinOn_univ_iff]
  intro x
  rw [← EReal.coe_add, ← EReal.coe_add]
  have hcenter :=
    admmLinearCompositeV2_xUpdate_objective_center_add_error
      (A := A) (c := c) (xk := xk) (u := u) (x := x) hu
  have hnonneg :
      0 ≤
        (1 / 2 : ℝ) * ‖x - u‖ ^ (2 : ℕ) +
          (1 / 2 : ℝ) * ‖A (x - u)‖ ^ (2 : ℕ) := by
    have hquad₁ : 0 ≤ (1 / 2 : ℝ) * ‖x - u‖ ^ (2 : ℕ) := by
      positivity
    have hquad₂ : 0 ≤ (1 / 2 : ℝ) * ‖A (x - u)‖ ^ (2 : ℕ) := by
      positivity
    linarith
  -- Stay in the real-valued quadratic spelling until the final coercion to `EReal`.
  have hxResidual : A x - c = A x - zk + (1 / (ρ : ℝ)) • y1k := by
    simp [c, sub_eq_add_neg, add_assoc, add_comm]
  have huResidual : A u - c = A u - zk + (1 / (ρ : ℝ)) • y1k := by
    simp [c, sub_eq_add_neg, add_assoc, add_comm]
  have hrewrite :
      (1 / 2 : ℝ) * ‖x - xk‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖A x - zk + (1 / (ρ : ℝ)) • y1k‖ ^ (2 : ℕ) =
        ((1 / 2 : ℝ) * ‖u - xk‖ ^ (2 : ℕ) +
            (1 / 2 : ℝ) * ‖A u - zk + (1 / (ρ : ℝ)) • y1k‖ ^ (2 : ℕ)) +
          ((1 / 2 : ℝ) * ‖x - u‖ ^ (2 : ℕ) +
            (1 / 2 : ℝ) * ‖A (x - u)‖ ^ (2 : ℕ)) := by
    rw [← hxResidual, ← huResidual]
    exact hcenter
  rw [hrewrite]
  exact_mod_cast le_add_of_nonneg_right hnonneg

section

omit [CompleteSpace X]

/-- Helper for Algorithm 15.12: the specialized ADMM `x`-subproblem objective is exactly the
displayed quadratic tether centered at `xk`. -/
lemma admmLinearCompositeV2_xUpdate_argminObjective_eq
    (ρ : PosReal) (A : X →L[ℝ] E) (zk y1k : E) (xk : X) :
    (fun x : X ↦
      admm_primal_update_objective
        1
        (fun x : X ↦ ((((1 / 2 : ℝ) * ‖x - xk‖ ^ (2 : ℕ) : ℝ) : EReal)))
        (0 : E → EReal)
        A
        (-LinearMap.id)
        0
        ((1 / (ρ : ℝ)) • y1k)
        (x, zk)) =
      (fun x : X ↦
        ((((1 / 2 : ℝ) * ‖x - xk‖ ^ (2 : ℕ) : ℝ) : EReal)) +
          ((((1 / 2 : ℝ) * ‖A x - zk + (1 / (ρ : ℝ)) • y1k‖ ^ (2 : ℕ) : ℝ) : EReal))) := by
  -- Expand the one-block ADMM objective at a fixed `zk`; the remaining terms are the displayed
  -- quadratic tether.
  funext x
  simp [admm_primal_update_objective_apply, sub_eq_add_neg, add_left_comm, add_comm]

end

/-- The explicit Algorithm 15.12 specialization `w^k = x^k`, `y₂^k = 0` of the Chapter 15
version-2 `x`-solve realizes the canonical ADMM `x`-argmin step for the quadratic tether
`x ↦ (1 / 2) ‖x - x^k‖²`. -/
theorem admm_linear_composite_v2_x_update_mem_argmin_zero
    (ρ : PosReal) (A : X →L[ℝ] E) (zk y1k : E) (xk : X) :
    admm_linear_composite_v2_x_update ρ A zk y1k xk ∈
      admm_x_update_argmin
        1
        (fun x : X ↦ ((((1 / 2 : ℝ) * ‖x - xk‖ ^ (2 : ℕ) : ℝ) : EReal)))
        A
        (-LinearMap.id)
        0
        zk
        ((1 / (ρ : ℝ)) • y1k) := by
  -- Rewrite the ADMM `x`-argmin set to the specialized quadratic objective from the core lemma.
  rw [mem_admm_x_update_argmin_iff, admmLinearCompositeV2_xUpdate_argminObjective_eq]
  simpa
    using admmLinearCompositeV2_xUpdate_isMinOnCore
      (ρ := ρ) (A := A) (zk := zk) (y1k := y1k) (xk := xk)

/-- Algorithm 15.12: the specialized `x`-solve is exactly the displayed linear-composite ADMM
minimizer with the quadratic proximal tether centered at `x^k`. -/
theorem admm_linear_composite_v2_x_update_isMinOn_zero
    (ρ : PosReal) (A : X →L[ℝ] E) (zk y1k : E) (xk : X) :
    IsMinOn
      (fun x : X ↦
        ((((1 / 2 : ℝ) * ‖x - xk‖ ^ (2 : ℕ) : ℝ) : EReal)) +
          ((((1 / 2 : ℝ) * ‖A x - zk + (1 / (ρ : ℝ)) • y1k‖ ^ (2 : ℕ) : ℝ) : EReal)))
      Set.univ
      (admm_linear_composite_v2_x_update ρ A zk y1k xk) := by
  -- The public statement is exactly the specialized core minimization statement.
  simpa using
    admmLinearCompositeV2_xUpdate_isMinOnCore
      (ρ := ρ) (A := A) (zk := zk) (y1k := y1k) (xk := xk)

end

section

variable {X : Type u} {ι : Type v}
variable [AddCommMonoid X] [Module ℝ X]
variable [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/-- The shifted `ℓ¹` regularizer centered at `b`, viewed as the canonical `EReal`-valued owner for
the linear-composite ADMM `z`-subproblem. -/
def admm_linear_composite_shifted_l1_regularizer (b : E) : E → EReal :=
  fun z ↦ ((‖z - b‖₁ : ℝ) : EReal)

/-- Evaluating the shifted `ℓ¹` regularizer at `z` gives the translated Euclidean `ℓ¹` norm
`‖z - b‖₁`. -/
@[simp] theorem admm_linear_composite_shifted_l1_regularizer_apply (b z : E) :
    admm_linear_composite_shifted_l1_regularizer b z = ((‖z - b‖₁ : ℝ) : EReal) :=
  rfl

/-- Helper for Algorithm 15.12: scaling the shifted `ℓ¹` regularizer by `1 / ρ` gives the
pointwise translated penalty `z ↦ (1 / ρ) ‖z - b‖₁`. -/
lemma scaledShiftedL1Regularizer_eq_translatedPenalty
    (ρ : PosReal) (b : E) :
    ((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b)) =
      fun z : E ↦ (((1 / (ρ : ℝ)) * ‖z - b‖₁ : ℝ) : EReal) := by
  -- This is the pointwise scalar action on the translated `ℓ¹` penalty.
  funext z
  simp [admm_linear_composite_shifted_l1_regularizer, Pi.smul_apply, smul_eq_mul]

/-- The shared shifted `ℓ¹` soft-threshold `z`-update for the linear-composite split
`A x - z = 0`:
`z^(k+1) = T_[1 / ρ] (A x^(k+1) + (1 / ρ) y^k - b) + b`. -/
def admm_linear_composite_shifted_l1_z_update
    (ρ : PosReal) (A : X →ₗ[ℝ] E) (b : E) (xNext : X) (yk : E) : E :=
  T_[1 / (ρ : ℝ)] (A xNext + (1 / (ρ : ℝ)) • yk - b) + b

-- Proof sketch: unfold `admm_linear_composite_shifted_l1_z_update`; the right-hand side is
-- exactly the shifted soft-thresholding formula displayed for `z^(k+1)` in Algorithms 15.11,
-- 15.12, and 15.13.
/-- Expanding `admm_linear_composite_shifted_l1_z_update` gives the shifted soft-thresholding
formula for `z^(k+1)`. -/
@[simp] theorem admm_linear_composite_shifted_l1_z_update_eq
    (ρ : PosReal) (A : X →ₗ[ℝ] E) (b : E) (xNext : X) (yk : E) :
    admm_linear_composite_shifted_l1_z_update ρ A b xNext yk =
      T_[1 / (ρ : ℝ)] (A xNext + (1 / (ρ : ℝ)) • yk - b) + b :=
  rfl

/-- Helper for Algorithm 15.12: the specialized ADMM `z`-objective is the positive scalar
multiple `ρ` of the corresponding proximal objective. -/
lemma linearCompositeZObjective_eq_scaledProxObjective
    (ρ : PosReal)
    (A : X →ₗ[ℝ] E)
    (b : E)
    (xNext : X)
    (yk z : E) :
    admm_primal_update_objective
        ρ
        (0 : X → EReal)
        (admm_linear_composite_shifted_l1_regularizer b)
        A
        (-LinearMap.id)
        0
        yk
        (xNext, z) =
      (((ρ : ℝ)) : EReal) *
        proximal_objective
          ((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b))
          (A xNext + (1 / (ρ : ℝ)) • yk)
          z := by
  let center : E := A xNext + (1 / (ρ : ℝ)) • yk
  have hρ : (ρ : ℝ) ≠ 0 := ne_of_gt ρ.2
  have hreal :
      ‖z - b‖₁ + ((ρ : ℝ) / 2) * ‖center - z‖ ^ (2 : ℕ) =
        (ρ : ℝ) *
          (((1 / (ρ : ℝ)) * ‖z - b‖₁) + (1 / 2 : ℝ) * ‖z - center‖ ^ (2 : ℕ)) := by
    rw [norm_sub_rev]
    field_simp [hρ]
  have hscaledApply :
      ((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b) z) =
        (((1 / (ρ : ℝ)) * ‖z - b‖₁ : ℝ) : EReal) := by
    exact congrArg (fun f : E → EReal ↦ f z)
      (scaledShiftedL1Regularizer_eq_translatedPenalty (ρ := ρ) (b := b))
  -- Rewrite both objectives into the same explicit real normal form.
  calc
    admm_primal_update_objective
        ρ
        (0 : X → EReal)
        (admm_linear_composite_shifted_l1_regularizer b)
        A
        (-LinearMap.id)
        0
        yk
        (xNext, z)
        =
      (((‖z - b‖₁ + ((ρ : ℝ) / 2) * ‖center - z‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
            simp [admm_primal_update_objective_apply, admm_linear_composite_shifted_l1_regularizer,
              center, sub_eq_add_neg, add_left_comm, add_comm, EReal.coe_add]
    _ =
      ((((ρ : ℝ) *
          (((1 / (ρ : ℝ)) * ‖z - b‖₁) + (1 / 2 : ℝ) * ‖z - center‖ ^ (2 : ℕ)) : ℝ)) : EReal) := by
            exact_mod_cast hreal
    _ =
      (((ρ : ℝ)) : EReal) *
        proximal_objective
          ((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b))
          center
          z := by
            have hρ_nonneg : 0 ≤ (((ρ : ℝ)) : EReal) := by
              exact_mod_cast ρ.2.le
            have hρ_top : (((ρ : ℝ)) : EReal) ≠ ⊤ := EReal.coe_ne_top _
            rw [proximal_objective_apply, hscaledApply,
              EReal.left_distrib_of_nonneg_of_ne_top hρ_nonneg hρ_top]
            simp [EReal.coe_add, EReal.coe_mul, mul_add, center]

/-- The explicit thresholded `z`-update in Algorithm 15.12 is the canonical proximal point of the
shifted `ℓ¹` regularizer `z ↦ ‖z - b‖₁` at the ADMM center
`A x^(k+1) + (1 / ρ) y₁^k`. -/
theorem admm_linear_composite_shifted_l1_z_update_mem_prox
    (ρ : PosReal)
    (A : X →ₗ[ℝ] E)
    (b : E)
    (xNext : X)
    (yk : E) :
    admm_linear_composite_shifted_l1_z_update ρ A b xNext yk ∈
      prox[((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b))]
        (A xNext + (1 / (ρ : ℝ)) • yk) := by
  let center : E := A xNext + (1 / (ρ : ℝ)) • yk
  let g : E → EReal := fun z : E ↦ (((1 / (ρ : ℝ)) * ‖z‖₁ : ℝ) : EReal)
  have hshift :
      ((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b)) =
        fun y : E ↦ g (1 • y + (-b)) := by
    -- Normalize the shifted penalty into the translation form required by Theorem 6.11.
    funext y
    simp [g, sub_eq_add_neg]
  have htransport :
      prox[((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b))]
        center =
        (fun z : E ↦ z + b) '' prox[g] (center - b) := by
    rw [hshift]
    simpa [g, center, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      proximal_mapping_scaling_translation g 1 one_ne_zero (-b) center
  have hlam : 0 ≤ 1 / (ρ : ℝ) := one_div_nonneg.mpr ρ.2.le
  have hbase :
      T_[1 / (ρ : ℝ)] (center - b) ∈ prox[g] (center - b) := by
    rw [prox_euclidean_l1_eq_singleton_softThreshold hlam]
    simp
  -- Transport the standard soft-threshold proximal point through the translation map.
  rw [htransport]
  refine ⟨T_[1 / (ρ : ℝ)] (center - b), hbase, ?_⟩
  simp [admm_linear_composite_shifted_l1_z_update, center, sub_eq_add_neg, add_left_comm,
    add_comm]

/-- The explicit thresholded `z`-update from Algorithm 15.12 belongs to the canonical
linear-composite ADMM `z`-argmin set for the shifted `ℓ¹` block. -/
theorem admm_linear_composite_shifted_l1_z_update_mem_argmin
    (ρ : PosReal)
    (A : X →ₗ[ℝ] E)
    (b : E)
    (xNext : X)
    (yk : E) :
    admm_linear_composite_shifted_l1_z_update ρ A b xNext yk ∈
      admm_z_update_argmin
        ρ
        (admm_linear_composite_shifted_l1_regularizer b)
        A
        (-LinearMap.id)
        0
        xNext
        yk := by
  let center : E := A xNext + (1 / (ρ : ℝ)) • yk
  let zNext : E := admm_linear_composite_shifted_l1_z_update ρ A b xNext yk
  have hzprox :
      zNext ∈
        prox[((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b))]
          center := by
    simpa [center, zNext] using
      admm_linear_composite_shifted_l1_z_update_mem_prox
        (ρ := ρ) (A := A) (b := b) (xNext := xNext) (yk := yk)
  have hρ_nonneg : 0 ≤ (((ρ : ℝ)) : EReal) := by
    exact_mod_cast ρ.2.le
  rw [mem_admm_z_update_argmin_iff]
  rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hzprox
  rw [isMinOn_univ_iff]
  intro z
  have hz_scaled :
      (((ρ : ℝ)) : EReal) *
          proximal_objective
            ((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b))
            center
            zNext ≤
        (((ρ : ℝ)) : EReal) *
          proximal_objective
            ((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b))
            center
            z :=
    mul_le_mul_of_nonneg_left (hzprox z) hρ_nonneg
  -- Rewrite the ADMM objective as the positive scalar multiple of the proximal objective.
  rw [← linearCompositeZObjective_eq_scaledProxObjective
        (ρ := ρ) (A := A) (b := b) (xNext := xNext)
        (yk := yk) (z := zNext),
      ← linearCompositeZObjective_eq_scaledProxObjective
        (ρ := ρ) (A := A) (b := b) (xNext := xNext)
        (yk := yk) (z := z)] at hz_scaled
  simpa [zNext] using hz_scaled

end

section

variable {X : Type u} {ι : Type v}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

private structure IterateState (X' E' : Type*) where
  x : X'
  z : E'
  y1 : E'

private def initialState (x0 : X) (z0 y10 : E) : IterateState X E :=
  { x := x0
    z := z0
    y1 := y10 }

private def stateUpdate
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E)
    (state : IterateState X E) : IterateState X E :=
  let xNext := admm_linear_composite_v2_x_update ρ A state.z state.y1 state.x
  let zNext := admm_linear_composite_shifted_l1_z_update ρ A b xNext state.y1
  { x := xNext
    z := zNext
    y1 := admm_multiplier_update ρ A (-LinearMap.id) 0 state.y1 xNext zNext }

private def iterateState
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E)
    (x0 : X) (z0 y10 : E) :
    ℕ → IterateState X E
  | 0 => initialState x0 z0 y10
  | k + 1 => stateUpdate ρ A b (iterateState ρ A b x0 z0 y10 k)

/-- The Algorithm 15.12 (1) `x`-iterate sequence for the linear-composite ADMM version-2
recursion. -/
def admm_linear_composite_v2_x
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E)
    (x0 : X) (z0 y10 : E) :
    ℕ → X :=
  fun k ↦ (iterateState ρ A b x0 z0 y10 k).x

/-- The Algorithm 15.12 (2) `z`-iterate sequence for the linear-composite ADMM version-2
recursion. -/
def admm_linear_composite_v2_z
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E)
    (x0 : X) (z0 y10 : E) :
    ℕ → E :=
  fun k ↦ (iterateState ρ A b x0 z0 y10 k).z

/-- The Algorithm 15.12 (3) multiplier sequence `y₁^k` for the linear-composite ADMM version-2
recursion. -/
def admm_linear_composite_v2_y1
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E)
    (x0 : X) (z0 y10 : E) :
    ℕ → E :=
  fun k ↦ (iterateState ρ A b x0 z0 y10 k).y1

section

variable (ρ : PosReal) (A : X →L[ℝ] E) (b : E) (x0 : X) (z0 y10 : E)

local notation "x[" k "]" =>
  admm_linear_composite_v2_x ρ A b x0 z0 y10 k
local notation "z[" k "]" =>
  admm_linear_composite_v2_z ρ A b x0 z0 y10 k
local notation "y1[" k "]" =>
  admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k
local notation "f2" =>
  admm_linear_composite_shifted_l1_regularizer b

/-- The `x`-iterate sequence starts from the prescribed initial point `x⁰ = x0`. -/
theorem admm_linear_composite_v2_x_zero
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E) (x0 : X) (z0 y10 : E) :
    admm_linear_composite_v2_x ρ A b x0 z0 y10 0 = x0 :=
  rfl

/-- The `z`-iterate sequence starts from the prescribed initial point `z⁰ = z0`. -/
theorem admm_linear_composite_v2_z_zero
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E) (x0 : X) (z0 y10 : E) :
    admm_linear_composite_v2_z ρ A b x0 z0 y10 0 = z0 :=
  rfl

/-- The multiplier sequence starts from the prescribed initial point `y₁⁰ = y10`. -/
theorem admm_linear_composite_v2_y1_zero
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E) (x0 : X) (z0 y10 : E) :
    admm_linear_composite_v2_y1 ρ A b x0 z0 y10 0 = y10 :=
  rfl

/-- The Algorithm 15.12 (4) step: at every iteration `k`, the next `x`-iterate is given by the
explicit
linear solve. -/
theorem admm_linear_composite_v2_x_succ
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E) (x0 : X) (z0 y10 : E) (k : ℕ) :
    admm_linear_composite_v2_x ρ A b x0 z0 y10 (k + 1) =
      admm_linear_composite_v2_x_update
        ρ
        A
        (admm_linear_composite_v2_z ρ A b x0 z0 y10 k)
        (admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k)
        (admm_linear_composite_v2_x ρ A b x0 z0 y10 k) :=
  rfl

/-- The Algorithm 15.12 (5) step: at every iteration `k`, the next `z`-iterate is given by the
shifted
soft-thresholding formula. -/
theorem admm_linear_composite_v2_z_succ
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E) (x0 : X) (z0 y10 : E) (k : ℕ) :
    admm_linear_composite_v2_z ρ A b x0 z0 y10 (k + 1) =
      admm_linear_composite_shifted_l1_z_update
        ρ
        A
        b
        (admm_linear_composite_v2_x ρ A b x0 z0 y10 (k + 1))
        (admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k) :=
  rfl

/-- The Algorithm 15.12 (6) step: at every iteration `k`, the next multiplier iterate is the
canonical
ADMM affine update. -/
theorem admm_linear_composite_v2_y1_succ
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E) (x0 : X) (z0 y10 : E) (k : ℕ) :
    admm_linear_composite_v2_y1 ρ A b x0 z0 y10 (k + 1) =
      admm_multiplier_update
        ρ
        (A : X →ₗ[ℝ] E)
        (-LinearMap.id)
        0
        (admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k)
        (admm_linear_composite_v2_x ρ A b x0 z0 y10 (k + 1))
        (admm_linear_composite_v2_z ρ A b x0 z0 y10 (k + 1)) :=
  rfl

/-- At every iteration `k`, the `z`-iterate is the canonical proximal point of the shifted
`ℓ¹` block. -/
theorem admm_linear_composite_v2_z_succ_mem_prox
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E) (x0 : X) (z0 y10 : E) (k : ℕ) :
    admm_linear_composite_v2_z ρ A b x0 z0 y10 (k + 1) ∈
      prox[((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b))]
        (A (admm_linear_composite_v2_x ρ A b x0 z0 y10 (k + 1)) +
          (1 / (ρ : ℝ)) • admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k) := by
  -- The recursive `z`-iterate reduces definitionally to the base shifted soft-threshold update.
  rw [admm_linear_composite_v2_z_succ ρ A b x0 z0 y10 k]
  simpa using
    admm_linear_composite_shifted_l1_z_update_mem_prox
      (ρ := ρ)
      (A := (A : X →ₗ[ℝ] E))
      (b := b)
      (xNext := admm_linear_composite_v2_x ρ A b x0 z0 y10 (k + 1))
      (yk := admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k)

/-- At every iteration `k`, the `z`-iterate belongs to the canonical linear-composite ADMM
`z`-argmin set for the shifted `ℓ¹` block. -/
theorem admm_linear_composite_v2_z_succ_mem_argmin
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E) (x0 : X) (z0 y10 : E) (k : ℕ) :
    admm_linear_composite_v2_z ρ A b x0 z0 y10 (k + 1) ∈
      admm_z_update_argmin
        ρ
        (admm_linear_composite_shifted_l1_regularizer b)
        (A : X →ₗ[ℝ] E)
        (-LinearMap.id)
        0
        (admm_linear_composite_v2_x ρ A b x0 z0 y10 (k + 1))
        (admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k) := by
  -- The recursive `z`-iterate reduces definitionally to the base shifted `ℓ¹` argmin theorem.
  rw [admm_linear_composite_v2_z_succ ρ A b x0 z0 y10 k]
  simpa using
    admm_linear_composite_shifted_l1_z_update_mem_argmin
      (ρ := ρ)
      (A := (A : X →ₗ[ℝ] E))
      (b := b)
      (xNext := admm_linear_composite_v2_x ρ A b x0 z0 y10 (k + 1))
      (yk := admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k)

/-- At every iteration `k`, the `x`-iterate is the canonical linear-composite ADMM minimizer with
the quadratic tether centered at `x^k`. -/
theorem admm_linear_composite_v2_x_succ_mem_argmin
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E) (x0 : X) (z0 y10 : E) (k : ℕ) :
    admm_linear_composite_v2_x ρ A b x0 z0 y10 (k + 1) ∈
      admm_x_update_argmin
        1
        (fun xNext : X ↦
          ((((1 / 2 : ℝ) *
              ‖xNext - admm_linear_composite_v2_x ρ A b x0 z0 y10 k‖ ^ (2 : ℕ) : ℝ) : EReal)))
        A
        (-LinearMap.id)
        0
        (admm_linear_composite_v2_z ρ A b x0 z0 y10 k)
        ((1 / (ρ : ℝ)) • admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k) := by
  -- The recursive `x`-iterate reduces definitionally to the base explicit resolvent minimizer.
  rw [admm_linear_composite_v2_x_succ ρ A b x0 z0 y10 k]
  simpa using
    admm_linear_composite_v2_x_update_mem_argmin_zero
      (ρ := ρ)
      (A := A)
      (zk := admm_linear_composite_v2_z ρ A b x0 z0 y10 k)
      (y1k := admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k)
      (xk := admm_linear_composite_v2_x ρ A b x0 z0 y10 k)

/-- At every iteration `k`, the `x`-iterate globally minimizes the displayed quadratic-tethered
linear-composite ADMM objective from Algorithm 15.12. -/
theorem admm_linear_composite_v2_x_succ_isMinOn
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E) (x0 : X) (z0 y10 : E) (k : ℕ) :
    IsMinOn
      (fun xNext : X ↦
        ((((1 / 2 : ℝ) *
            ‖xNext - admm_linear_composite_v2_x ρ A b x0 z0 y10 k‖ ^ (2 : ℕ) : ℝ) : EReal)) +
          ((((1 / 2 : ℝ) *
              ‖A xNext - admm_linear_composite_v2_z ρ A b x0 z0 y10 k +
                  (1 / (ρ : ℝ)) • admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k‖ ^ (2 : ℕ) :
                ℝ) : EReal)))
      Set.univ
      (admm_linear_composite_v2_x ρ A b x0 z0 y10 (k + 1)) := by
  -- Transport the local `x`-argmin wrapper through the specialized objective identity.
  rw [admm_linear_composite_v2_x_succ ρ A b x0 z0 y10 k]
  simpa using
    admm_linear_composite_v2_x_update_isMinOn_zero
      (ρ := ρ)
      (A := A)
      (zk := admm_linear_composite_v2_z ρ A b x0 z0 y10 k)
      (y1k := admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k)
      (xk := admm_linear_composite_v2_x ρ A b x0 z0 y10 k)

/-- At every iteration `k`, the multiplier iterate satisfies the affine recursion
`y₁^(k+1) = y₁^k + ρ (A x^(k+1) - z^(k+1))`. -/
theorem admm_linear_composite_v2_y1_succ_eq
    (ρ : PosReal) (A : X →L[ℝ] E) (b : E) (x0 : X) (z0 y10 : E) (k : ℕ) :
    admm_linear_composite_v2_y1 ρ A b x0 z0 y10 (k + 1) =
      admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k +
        (ρ : ℝ) •
          (A (admm_linear_composite_v2_x ρ A b x0 z0 y10 (k + 1)) -
            admm_linear_composite_v2_z ρ A b x0 z0 y10 (k + 1)) := by
  -- The recursive multiplier step reduces definitionally to the canonical ADMM affine update.
  rw [admm_linear_composite_v2_y1_succ ρ A b x0 z0 y10 k]
  calc
    admm_multiplier_update
        ρ
        (A : X →ₗ[ℝ] E)
        (-LinearMap.id)
        0
        (admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k)
        (admm_linear_composite_v2_x ρ A b x0 z0 y10 (k + 1))
        (admm_linear_composite_v2_z ρ A b x0 z0 y10 (k + 1))
      =
        admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k +
          (ρ : ℝ) •
            ((A : X →ₗ[ℝ] E) (admm_linear_composite_v2_x ρ A b x0 z0 y10 (k + 1)) +
              (-LinearMap.id) (admm_linear_composite_v2_z ρ A b x0 z0 y10 (k + 1)) - (0 : E)) := by
            rw [admm_multiplier_update_eq]
    _ = admm_linear_composite_v2_y1 ρ A b x0 z0 y10 k +
          (ρ : ℝ) •
            (A (admm_linear_composite_v2_x ρ A b x0 z0 y10 (k + 1)) -
              admm_linear_composite_v2_z ρ A b x0 z0 y10 (k + 1)) := by
            simp [sub_eq_add_neg, smul_add]

end

end
