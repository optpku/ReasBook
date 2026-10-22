/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_8
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_55

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

recall composite_model_objective
recall composite_model_objective_apply

section

variable {m n p : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
  (D : Matrix (Fin p) (Fin n) ℝ) (lam : ℝ)

/- Definition 10.60 is `source-facing` in the concrete S-FISTA model layer.

Domain sampling identifies the canonical owners already present in the project:
- Chapter 6's `EuclideanSpace.l1Norm`, used on the theorem surface as `‖·‖₁`, for the Euclidean
  `ℓ¹` penalties;
- Chapter 10's `composite_model_objective` for additive objective assembly;
- Definition 10.55's S-FISTA three-term bridge, showing that the three-summand objective should be
  expressed by iterating `composite_model_objective` rather than by introducing a second local
  objective owner.

The primitive data are therefore only the least-squares data-fit term, the transformed `ℓ¹`
penalty, and the ambient `ℓ¹` penalty. Their sum is derived API from the chapter owner
`composite_model_objective`, so a parallel local wrapper definition is redundant. -/

/-- The least-squares data-fit term `x ↦ (1 / 2) ‖A x - b‖₂²` from Definition 10.60. -/
abbrev least_squares_loss : X → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * ‖A.toEuclideanLin x - b‖ ^ (2 : ℕ)

/-- The analysis `ℓ¹` penalty `x ↦ ‖D x‖₁` from Definition 10.60. -/
abbrev analysis_l1_penalty : X → ℝ :=
  fun x ↦ ‖D.toEuclideanLin x‖₁

/-- The ambient `ℓ¹` regularizer `x ↦ λ ‖x‖₁` from Definition 10.60. -/
abbrev ambient_l1_regularizer (n : ℕ) (lam : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x ↦ lam * ‖x‖₁

/- Definition 10.60: the least-squares analysis-`ℓ¹` objective is the specialized Chapter 10
three-term owner `H[least_squares_loss A b, analysis_l1_penalty D, ambient_l1_regularizer n lam]`.
-/
#check H[least_squares_loss A b, analysis_l1_penalty D, ambient_l1_regularizer n lam]

@[simp] theorem least_squares_loss_apply (x : X) :
    least_squares_loss A b x = (1 / 2 : ℝ) * ‖A.toEuclideanLin x - b‖ ^ (2 : ℕ) :=
  rfl

@[simp] theorem analysis_l1_penalty_apply (x : X) :
    analysis_l1_penalty D x = ‖D.toEuclideanLin x‖₁ :=
  rfl

@[simp] theorem ambient_l1_regularizer_apply (x : X) :
    ambient_l1_regularizer n lam x = lam * ‖x‖₁ :=
  rfl

/- Evaluating the Definition 10.60 objective at `x` is definitionally the textbook formula
`(1 / 2) ‖A x - b‖₂² + ‖D x‖₁ + λ ‖x‖₁`. -/
#check
  ((fun _ : X ↦ rfl) :
    ∀ x : X,
      H[least_squares_loss A b, analysis_l1_penalty D, ambient_l1_regularizer n lam] x =
        (1 / 2 : ℝ) * ‖A.toEuclideanLin x - b‖ ^ (2 : ℕ) + ‖D.toEuclideanLin x‖₁ +
          lam * ‖x‖₁)

end
