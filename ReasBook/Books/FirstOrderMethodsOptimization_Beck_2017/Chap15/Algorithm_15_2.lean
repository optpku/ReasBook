/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Definition_15_1
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Definition_15_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Z] [Module ℝ Z]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled from the nearby
optimization files. This item is `source-facing`: the algorithm specifies a nonunique joint
`arg min` step for `(x^(k+1), z^(k+1))` and then an explicit affine multiplier update for
`y^(k+1)`. The relevant declarations in this domain are:
- `PosReal` for the positive penalty parameter `ρ`;
- `IsMinOn` for the `arg min` clause;
- `unconstrained_problem_solutions` from Definition 8.2 as the canonical owner of unconstrained
  global argmin sets;
- `H[h₁, h₂]` from Definition 15.1 for the primitive two-block objective;
- `L[ρ; h₁, h₂; A, B, c] = admm_augmented_lagrangian h₁ h₂ A B c ρ` from Definition 15.3 as the
  Chapter 15 `core/canonical` owner of the augmented-Lagrangian term under stronger inner-product
  assumptions.

Accordingly, the public API keeps the displayed source-facing subproblem over a general
`NormedSpace`, while the inner-product section below adds the canonical bridge to
`L[ρ; h₁, h₂; A, B, c]`. The source-facing joint argmin set is a thin specialization of the
Chapter 8 solution-set owner, the affine multiplier update is owned separately at the additive
module level, and the trajectory owner is a Prop-valued class with atomic step fields, matching
the surrounding Chapter 15 algorithm files without choosing minimizers. -/

/-- The ADMM joint subproblem objective at the current multiplier iterate `y^k`, namely
`h₁(x) + h₂(z) + (ρ / 2) ‖A x + B z - c + (1 / ρ) y^k‖²`. -/
def admm_primal_update_objective
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk : Y) :
    X × Z → EReal :=
  fun xz ↦
    H[h₁, h₂] xz +
      ((((ρ : ℝ) / 2) * ‖A xz.1 + B xz.2 - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) : ℝ) : EReal)

-- Proof sketch: unfold `admm_primal_update_objective`; evaluation at `(x, z)` is exactly the
-- displayed augmented-Lagrangian objective from equation (15.9).
/-- Evaluating the ADMM joint update objective at `(x, z)` gives the textbook expression
`h₁(x) + h₂(z) + (ρ / 2) ‖A x + B z - c + (1 / ρ) y^k‖²`. -/
@[simp] theorem admm_primal_update_objective_apply
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk : Y) (x : X) (z : Z) :
    admm_primal_update_objective ρ h₁ h₂ A B c yk (x, z) =
      h₁ x + h₂ z +
        ((((ρ : ℝ) / 2) * ‖A x + B z - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  simp [admm_primal_update_objective]

/-- The ADMM `arg min` set of joint primal updates `(x^(k+1), z^(k+1))` at the current multiplier
iterate `y^k`. -/
abbrev admm_primal_update_argmin
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk : Y) :
    Set (X × Z) :=
  unconstrained_problem_solutions (admm_primal_update_objective ρ h₁ h₂ A B c yk)

/-- Definitionally, the ADMM joint update set is the Chapter 8 unconstrained solution set of the
current joint primal objective. -/
theorem admm_primal_update_argmin_def
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk : Y) :
    admm_primal_update_argmin ρ h₁ h₂ A B c yk =
      unconstrained_problem_solutions (admm_primal_update_objective ρ h₁ h₂ A B c yk) :=
  rfl

-- Proof sketch: rewrite membership in the Chapter 8 unconstrained solution-set owner.
/-- A pair `(x^(k+1), z^(k+1))` belongs to the ADMM primal update set exactly when it globally
minimizes the augmented-Lagrangian objective from equation (15.9). -/
@[simp] theorem mem_admm_primal_update_argmin_iff
    {ρ : PosReal}
    {h₁ : X → EReal} {h₂ : Z → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c yk : Y} {xNext : X} {zNext : Z} :
    (xNext, zNext) ∈ admm_primal_update_argmin ρ h₁ h₂ A B c yk ↔
      IsMinOn (admm_primal_update_objective ρ h₁ h₂ A B c yk) Set.univ (xNext, zNext) :=
  mem_unconstrained_problem_solutions_iff

end

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Z] [Module ℝ Z]
variable [AddCommGroup Y] [Module ℝ Y]

/-- The ADMM multiplier update
`y^(k+1) = y^k + ρ (A x^(k+1) + B z^(k+1) - c)`. -/
def admm_multiplier_update
    (ρ : PosReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk : Y)
    (xNext : X) (zNext : Z) : Y :=
  yk + (ρ : ℝ) • (A xNext + B zNext - c)

-- Proof sketch: unfold `admm_multiplier_update`; the right-hand side is exactly the affine ascent
-- formula from equation (15.10).
/-- Expanding the ADMM multiplier update gives `y^k + ρ (A x^(k+1) + B z^(k+1) - c)`. -/
@[simp] theorem admm_multiplier_update_eq
    (ρ : PosReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk : Y)
    (xNext : X) (zNext : Z) :
    admm_multiplier_update ρ A B c yk xNext zNext =
      yk + (ρ : ℝ) • (A xNext + B zNext - c) :=
  rfl

end

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Z] [Module ℝ Z]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Algorithm 15.2: given an initialization `y^0 = y0` and a positive penalty parameter `ρ`, the
sequences `x`, `z`, and `y` form an ADMM trajectory when, for every iteration `k`, the pair
`(x^(k+1), z^(k+1))` lies in the joint `arg min` set of
`h₁(x) + h₂(z) + (ρ / 2) ‖A x + B z - c + (1 / ρ) y^k‖²` and the multiplier update satisfies
`y^(k+1) = y^k + ρ (A x^(k+1) + B z^(k+1) - c)`. -/
class IsADMMTrajectory
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (x : ℕ → X) (z : ℕ → Z) (y : ℕ → Y) (y0 : Y) : Prop where
  y_zero : y 0 = y0
  primal_step (k : ℕ) :
    (x (k + 1), z (k + 1)) ∈ admm_primal_update_argmin ρ h₁ h₂ A B c (y k)
  multiplier_step (k : ℕ) :
    y (k + 1) =
      admm_multiplier_update ρ A B c (y k) (x (k + 1)) (z (k + 1))

/-- An Algorithm 15.2 trajectory predicate is a proposition, hence subsingleton. -/
instance
    {ρ : PosReal}
    {h₁ : X → EReal} {h₂ : Z → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c : Y}
    {x : ℕ → X} {z : ℕ → Z} {y : ℕ → Y} {y0 : Y}
    :
    Subsingleton (IsADMMTrajectory ρ h₁ h₂ A B c x z y y0) :=
  inferInstance

-- Proof sketch: read off the initialization equation from the `y_zero` field of
-- `IsADMMTrajectory`.
/-- An ADMM trajectory starts from the prescribed initialization `y^0 = y0`. -/
theorem is_admm_trajectory_zero
    {ρ : PosReal}
    {h₁ : X → EReal} {h₂ : Z → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c : Y}
    {x : ℕ → X} {z : ℕ → Z} {y : ℕ → Y} {y0 : Y}
    (h : IsADMMTrajectory ρ h₁ h₂ A B c x z y y0) :
    y 0 = y0 :=
  h.y_zero

-- Proof sketch: combine the `primal_step` and `multiplier_step` fields of `IsADMMTrajectory` at
-- the iteration index `k`.
/-- At every iteration `k`, an ADMM trajectory satisfies both the joint primal `arg min` condition
from equation (15.9) and the multiplier update formula from equation (15.10). -/
theorem is_admm_trajectory_step
    {ρ : PosReal}
    {h₁ : X → EReal} {h₂ : Z → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c : Y}
    {x : ℕ → X} {z : ℕ → Z} {y : ℕ → Y} {y0 : Y}
    (h : IsADMMTrajectory ρ h₁ h₂ A B c x z y y0) (k : ℕ) :
    (x (k + 1), z (k + 1)) ∈ admm_primal_update_argmin ρ h₁ h₂ A B c (y k) ∧
      y (k + 1) =
        admm_multiplier_update ρ A B c (y k) (x (k + 1)) (z (k + 1)) :=
  ⟨h.primal_step k, h.multiplier_step k⟩

end

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Z] [Module ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Completing the square rewrites the shifted ADMM penalty term as the quadratic penalty,
the linear multiplier pairing, and the standard `y`-dependent constant. -/
theorem admm_penalty_complete_square
    (ρ : PosReal) (r y : Y) :
    ((ρ : ℝ) / 2) * ‖r + (1 / (ρ : ℝ)) • y‖ ^ (2 : ℕ) =
      inner ℝ y r + ((ρ : ℝ) / 2) * ‖r‖ ^ (2 : ℕ) + ‖y‖ ^ (2 : ℕ) / (2 * (ρ : ℝ)) := by
  have hρ : (ρ : ℝ) ≠ 0 := by
    exact ne_of_gt ρ.2
  rw [norm_add_sq_real]
  rw [real_inner_smul_right, norm_smul, Real.norm_of_nonneg (one_div_nonneg.mpr ρ.2.le)]
  field_simp [hρ]
  rw [real_inner_comm]
  ring

-- Proof sketch: evaluate both sides, then use `admm_penalty_complete_square` on the residual
-- `A x + B z - c`.
/-- Under inner-product assumptions, the ADMM joint update objective equals the augmented
Lagrangian from Definition 15.3 plus the `y^k`-dependent constant obtained by completing the
square. -/
theorem admm_primal_update_objective_eq_admm_augmented_lagrangian_add_constant
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk : Y)
    (x : X) (z : Z) :
    admm_primal_update_objective ρ h₁ h₂ A B c yk (x, z) =
      L[(ρ : ℝ); h₁, h₂; A, B, c] x z yk +
        (((‖yk‖ ^ (2 : ℕ) / (2 * (ρ : ℝ)) : ℝ) : EReal)) := by
  let r : Y := A x + B z - c
  have hsquare := admm_penalty_complete_square ρ r yk
  simpa [admm_primal_update_objective_apply, admm_augmented_lagrangian_apply, r, add_assoc,
    add_left_comm, add_comm] using
    congrArg (fun t : ℝ ↦ h₁ x + h₂ z + (t : EReal)) hsquare

end
