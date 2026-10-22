/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Definition_15_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Z] [Module ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/- Domain sampling against the Chapter 15 ADMM files shows that this item is a `bridge/view`,
with a source-facing update-set owner, not a second dual-objective owner declaration:
- `admm_dual_objective_primal` from Definition 15.2 is the Chapter 15 primal-space owner for the
  dual term, and already places `X` and `Z` at the `AddCommGroup`/`Module ℝ` layer;
- `unconstrained_problem_solutions` from Definition 8.2 is the canonical whole-space argmin-set
  owner;
- `IsMinOn` remains the canonical membership characterization for that argmin set.

Accordingly, the public API keeps the source-facing dual-update objective as a thin bridge adding
the quadratic tether to the existing Chapter 15 owner, and defines the update set through the
Chapter 8 argmin-set owner rather than by restating the same `IsMinOn ... Set.univ` set builder
locally. -/

/-- The source-facing ADMM dual update objective from equation (15.4), expressed as the
minimization view of the Chapter 15 dual owner together with the proximal tether at `yᵏ`. -/
def admm_dual_update_objective
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk : Y) : Y → EReal :=
  fun y ↦
    -admm_dual_objective_primal h₁ h₂ A B c y +
      ((((1 / (2 * (ρ : ℝ)) : ℝ) * ‖y - yk‖ ^ (2 : ℕ)) : ℝ) : EReal)

/-- Evaluating the ADMM dual update objective expands the Chapter 15 dual owner together with the
quadratic tether centered at `yᵏ`. -/
@[simp] theorem admm_dual_update_objective_apply
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk y : Y) :
    admm_dual_update_objective ρ h₁ h₂ A B c yk y =
      -admm_dual_objective_primal h₁ h₂ A B c y +
        ((((1 / (2 * (ρ : ℝ)) : ℝ) * ‖y - yk‖ ^ (2 : ℕ)) : ℝ) : EReal) :=
  rfl

/-- Algorithm 15.1: given a positive parameter `ρ` and the current dual iterate `yᵏ`, the next
iterate `yᵏ⁺¹` is chosen from the `arg min` set of the ADMM dual objective
`h₁^*(-Aᵀ y) + h₂^*(-Bᵀ y) + ⟪c, y⟫ + (1 / (2ρ)) ‖y - yᵏ‖²`, realized through the canonical
Chapter 15 dual owner `admm_dual_objective` and the canonical whole-space argmin-set owner
`unconstrained_problem_solutions`. -/
abbrev admm_dual_update
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk : Y) : Set Y :=
  unconstrained_problem_solutions (admm_dual_update_objective ρ h₁ h₂ A B c yk)

/-- A point `yᵏ⁺¹` belongs to the ADMM dual update set exactly when it globally minimizes the
canonical ADMM dual-update objective. -/
@[simp] theorem mem_admm_dual_update_iff
    {ρ : PosReal}
    {h₁ : X → EReal} {h₂ : Z → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c yk yNext : Y} :
    yNext ∈ admm_dual_update ρ h₁ h₂ A B c yk ↔
      IsMinOn (admm_dual_update_objective ρ h₁ h₂ A B c yk) Set.univ yNext := by
  rw [admm_dual_update]
  exact mem_unconstrained_problem_solutions_iff

end

section

variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- Rewriting the Chapter 15 dual owner along the Riesz map gives the explicit equation-(15.4)
objective at a point where the two conjugate terms avoid `⊥`. -/
theorem admm_dual_update_objective_apply_eq_source_formula
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk y : Y)
    (h₁_ne_bot : (h₁∗) (-A.adjoint y) ≠ ⊥)
    (h₂_ne_bot : (h₂∗) (-B.adjoint y) ≠ ⊥) :
    admm_dual_update_objective ρ h₁ h₂ A B c yk y =
      (h₁∗) (-A.adjoint y) +
        (h₂∗) (-B.adjoint y) +
          ((inner ℝ c y : ℝ) : EReal) +
            ((((1 / (2 * (ρ : ℝ)) : ℝ) * ‖y - yk‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- Rewrite the dual owner to the source formula first, then append the finite quadratic tether.
  rw [admm_dual_update_objective]
  rw [← admm_dual_minimization_view_primal_apply_of_nonbot h₁ h₂ A B c y h₁_ne_bot h₂_ne_bot]

/-- Rewriting the Chapter 15 dual owner along the Riesz map gives the explicit equation-(15.4)
objective whenever both conjugate terms avoid `⊥` at every point. -/
theorem admm_dual_update_objective_eq_source_formula
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk : Y)
    (h₁_ne_bot : ∀ y, (h₁∗) (-A.adjoint y) ≠ ⊥)
    (h₂_ne_bot : ∀ y, (h₂∗) (-B.adjoint y) ≠ ⊥) :
    admm_dual_update_objective ρ h₁ h₂ A B c yk =
      fun y ↦
        (h₁∗) (-A.adjoint y) +
          (h₂∗) (-B.adjoint y) +
              ((inner ℝ c y : ℝ) : EReal) +
                ((((1 / (2 * (ρ : ℝ)) : ℝ) * ‖y - yk‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  funext y
  exact admm_dual_update_objective_apply_eq_source_formula ρ h₁ h₂ A B c yk y
    (h₁_ne_bot y) (h₂_ne_bot y)

/-- A point `yᵏ⁺¹` belongs to the ADMM dual update set exactly when it globally minimizes the
explicit equation-(15.4) source formula, provided the conjugate terms avoid `⊥` globally. -/
theorem mem_admm_dual_update_iff_source_formula
    {ρ : PosReal}
    {h₁ : X → EReal} {h₂ : Z → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c yk yNext : Y}
    (h₁_ne_bot : ∀ y, (h₁∗) (-A.adjoint y) ≠ ⊥)
    (h₂_ne_bot : ∀ y, (h₂∗) (-B.adjoint y) ≠ ⊥) :
    yNext ∈ admm_dual_update ρ h₁ h₂ A B c yk ↔
      IsMinOn
        (fun y ↦
          (h₁∗) (-A.adjoint y) +
          (h₂∗) (-B.adjoint y) +
              ((inner ℝ c y : ℝ) : EReal) +
                ((((1 / (2 * (ρ : ℝ)) : ℝ) * ‖y - yk‖ ^ (2 : ℕ)) : ℝ) : EReal))
        Set.univ yNext := by
  rw [mem_admm_dual_update_iff,
    admm_dual_update_objective_eq_source_formula ρ h₁ h₂ A B c yk h₁_ne_bot h₂_ne_bot]

end
end
