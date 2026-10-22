/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap15.Definition_15_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open InnerProductSpace (toDualMap)

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Z] [Module ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled from the nearby
Chapter 15 optimization declarations together with mathlib's inner-product duality API.

This item is `source-facing`: it introduces the augmented Lagrangian attached to the two-block
affine constraint `A x + B z = c`. The `core/canonical` owner for the affine pairing term is
already upstream as `admm_lagrangian` in Definition 15.2, and the inner-product multiplier view
is the standard Riesz-map bridge `toDualMap ℝ Y`. Accordingly, the only new primitive data here is
the quadratic penalty term; the augmented owner is defined by adding that penalty to the existing
Lagrangian rather than by restating a parallel full formula. -/

/-- Definition 15.3: the augmented Lagrangian associated with the ADMM problem is
`L_ρ(x, z; y) = h₁(x) + h₂(z) + ⟪y, A x + B z - c⟫ + (ρ / 2) ‖A x + B z - c‖²`. -/
def admm_augmented_lagrangian
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (ρ : ℝ)
    (x : X) (z : Z) (y : Y) : EReal :=
  admm_lagrangian h₁ h₂ A B c x z (toDualMap ℝ Y y) +
    (((ρ / 2) * ‖A x + B z - c‖ ^ (2 : ℕ) : ℝ) : EReal)

/- Textbook notation for the augmented Lagrangian `L_ρ`. -/
notation "L[" ρ "; " h₁ ", " h₂ "; " A ", " B ", " c "]" =>
  admm_augmented_lagrangian h₁ h₂ A B c ρ

/-- The augmented Lagrangian notation `L[ρ; h₁, h₂; A, B, c]` is the ADMM Lagrangian plus the
quadratic penalty term. -/
theorem admm_augmented_lagrangian_def
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (ρ : ℝ)
    (x : X) (z : Z) (y : Y) :
    L[ρ; h₁, h₂; A, B, c] x z y =
      admm_lagrangian h₁ h₂ A B c x z (toDualMap ℝ Y y) +
        (((ρ / 2) * ‖A x + B z - c‖ ^ (2 : ℕ) : ℝ) : EReal) :=
  rfl

-- Proof sketch: unfold `admm_augmented_lagrangian`; evaluation at `(x, z; y)` is exactly the
-- displayed defining formula for the augmented Lagrangian.
/-- Evaluating `L[ρ; h₁, h₂; A, B, c]` reproduces the textbook formula
`L_ρ(x, z; y) = h₁(x) + h₂(z) + ⟪y, A x + B z - c⟫ + (ρ / 2) ‖A x + B z - c‖²`. -/
@[simp] theorem admm_augmented_lagrangian_apply
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (ρ : ℝ)
    (x : X) (z : Z) (y : Y) :
    L[ρ; h₁, h₂; A, B, c] x z y =
      h₁ x + h₂ z +
        ((inner ℝ y (A x + B z - c) : ℝ) : EReal) +
          (((ρ / 2) * ‖A x + B z - c‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  simp [admm_augmented_lagrangian, add_assoc]

end
