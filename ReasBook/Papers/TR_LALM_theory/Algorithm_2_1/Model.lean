/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Assumption_2_1.Regularity

public section

open scoped InnerProductSpace

namespace LALM

variable {n m : ℕ}

/-- The quadratic model minimized by one fixed-penalty NR-LALM step. -/
@[expose] noncomputable def stepModel
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ρ β : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪gradient f x, p⟫_ℝ + ⟪multiplier, c x + fderiv ℝ c x p⟫_ℝ +
    (ρ / 2) * ‖c x + fderiv ℝ c x p‖ ^ 2 + (β / 2) * ‖p‖ ^ 2

/-- The LALM step model has the objective-gradient, linearized-constraint, penalty,
and proximal terms from its defining quadratic formula. -/
theorem stepModel_def
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ρ β : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n)) :
    stepModel f c ρ β x multiplier p =
      ⟪gradient f x, p⟫_ℝ + ⟪multiplier, c x + fderiv ℝ c x p⟫_ℝ +
        (ρ / 2) * ‖c x + fderiv ℝ c x p‖ ^ 2 + (β / 2) * ‖p‖ ^ 2 := rfl

/-- The fixed-penalty augmented Lagrangian for an equality-constrained problem. -/
@[expose] noncomputable def augmentedLagrangian
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ρ : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) : ℝ :=
  f x + ⟪multiplier, c x⟫_ℝ + (ρ / 2) * ‖c x‖ ^ 2

@[inherit_doc augmentedLagrangian]
scoped[LALM] notation "ℒ[" f ", " c "; " ρ "](" x ", " multiplier ")" =>
  augmentedLagrangian f c ρ x multiplier

open scoped LALM

/-- The augmented Lagrangian is the objective plus the multiplier pairing and
quadratic constraint penalty. -/
theorem augmentedLagrangian_def
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ρ : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) :
    ℒ[f, c; ρ](x, multiplier) =
      f x + ⟪multiplier, c x⟫_ℝ + (ρ / 2) * ‖c x‖ ^ 2 := rfl

end LALM

end
