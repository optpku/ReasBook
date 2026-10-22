/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Z] [Module ℝ Z]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled from the nearby
Chapter 15 ADMM files together with Chapter 8's unconstrained-optimization owner.

This item is `source-facing`: Algorithm 15.3 introduces the alternating one-block `x`- and
`z`-subproblem objectives and the resulting iterate recursion. Domain sampling identifies the owner
split:
- `source-facing`: the one-block objectives `admm_x_update_objective` and
  `admm_z_update_objective`;
- `core/canonical`: `admm_primal_update_objective` from Algorithm 15.2 for the shared
  augmented-Lagrangian objective, `unconstrained_problem_solutions` from Definition 8.2 for the
  whole-space argmin-set owner, and `admm_multiplier_update` from Algorithm 15.2 for the affine
  dual update;
- `bridge/view`: the membership lemmas rewriting the Chapter 8 argmin-set owner as `IsMinOn ...
  Set.univ`.

Primitive data are therefore the explicit one-block objectives, while the argmin sets are derived
API obtained by specializing the Chapter 8 owner to those objectives. The trajectory owner then
reuses the canonical multiplier update directly. -/

/-- The `x`-subproblem objective in Algorithm 15.3(a), obtained by freezing the `z`-variable in
the joint ADMM primal update objective. -/
def admm_x_update_objective
    (ρ : PosReal)
    (h₁ : X → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (c : Y) (zk : Z) (yk : Y) :
    X → EReal :=
  fun x ↦ admm_primal_update_objective ρ h₁ (0 : Z → EReal) A B c yk (x, zk)

/-- Evaluating the ADMM `x`-subproblem objective expands the one-block specialization of the joint
primal update objective. -/
@[simp] theorem admm_x_update_objective_apply
    (ρ : PosReal)
    (h₁ : X → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (c : Y) (zk : Z) (yk : Y) (x : X) :
    admm_x_update_objective ρ h₁ A B c zk yk x =
      admm_primal_update_objective ρ h₁ (0 : Z → EReal) A B c yk (x, zk) :=
  rfl

/-- The ADMM `arg min` set for the `x`-update in Algorithm 15.3(a). -/
abbrev admm_x_update_argmin
    (ρ : PosReal)
    (h₁ : X → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (c : Y) (zk : Z) (yk : Y) : Set X :=
  unconstrained_problem_solutions (admm_x_update_objective ρ h₁ A B c zk yk)

-- Proof sketch: unfold `admm_x_update_argmin`; membership is definitionally the global minimizer
-- condition for the `x`-update objective.
/-- A point `x^(k+1)` belongs to the ADMM `x`-update set exactly when it globally minimizes the
subproblem from Algorithm 15.3(a). -/
@[simp] theorem mem_admm_x_update_argmin_iff
    {ρ : PosReal}
    {h₁ : X → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y}
    {c : Y} {zk : Z} {yk : Y} {xNext : X} :
    xNext ∈ admm_x_update_argmin ρ h₁ A B c zk yk ↔
      IsMinOn
        (fun x ↦ admm_primal_update_objective ρ h₁ (0 : Z → EReal) A B c yk (x, zk))
        Set.univ
        xNext :=
  Iff.rfl

/-- The `z`-subproblem objective in Algorithm 15.3(b), obtained by freezing the `x`-variable in
the joint ADMM primal update objective. -/
def admm_z_update_objective
    (ρ : PosReal)
    (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (c : Y) (xNext : X) (yk : Y) :
    Z → EReal :=
  fun z ↦ admm_primal_update_objective ρ (0 : X → EReal) h₂ A B c yk (xNext, z)

/-- Evaluating the ADMM `z`-subproblem objective expands the one-block specialization of the joint
primal update objective. -/
@[simp] theorem admm_z_update_objective_apply
    (ρ : PosReal)
    (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (c : Y) (xNext : X) (yk : Y) (z : Z) :
    admm_z_update_objective ρ h₂ A B c xNext yk z =
      admm_primal_update_objective ρ (0 : X → EReal) h₂ A B c yk (xNext, z) :=
  rfl

/-- The ADMM `arg min` set for the `z`-update in Algorithm 15.3(b). -/
abbrev admm_z_update_argmin
    (ρ : PosReal)
    (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (c : Y) (xNext : X) (yk : Y) : Set Z :=
  unconstrained_problem_solutions (admm_z_update_objective ρ h₂ A B c xNext yk)

-- Proof sketch: unfold `admm_z_update_argmin`; membership is definitionally the global minimizer
-- condition for the `z`-update objective.
/-- A point `z^(k+1)` belongs to the ADMM `z`-update set exactly when it globally minimizes the
subproblem from Algorithm 15.3(b). -/
@[simp] theorem mem_admm_z_update_argmin_iff
    {ρ : PosReal}
    {h₂ : Z → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y}
    {c : Y} {xNext : X} {yk : Y} {zNext : Z} :
    zNext ∈ admm_z_update_argmin ρ h₂ A B c xNext yk ↔
      IsMinOn
        (fun z ↦ admm_primal_update_objective ρ (0 : X → EReal) h₂ A B c yk (xNext, z))
        Set.univ
        zNext :=
  Iff.rfl

/-- Algorithm 15.3: given initial iterates `x^0 = x0`, `z^0 = z0`, `y^0 = y0` and a positive
penalty parameter `ρ`, the sequences `x`, `z`, and `y` form an ADMM trajectory when, for every
iteration `k`, `x^(k+1)` lies in the `arg min` set from (a), `z^(k+1)` lies in the `arg min` set
from (b), and `y^(k+1) = y^k + ρ (A x^(k+1) + B z^(k+1) - c)` as in (c). -/
class IsADMMAlternatingTrajectory
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (x : ℕ → X) (z : ℕ → Z) (y : ℕ → Y)
    (x0 : X) (z0 : Z) (y0 : Y) : Prop where
  x_zero : x 0 = x0
  z_zero : z 0 = z0
  y_zero : y 0 = y0
  x_step (k : ℕ) :
    x (k + 1) ∈ admm_x_update_argmin ρ h₁ A B c (z k) (y k)
  z_step (k : ℕ) :
    z (k + 1) ∈ admm_z_update_argmin ρ h₂ A B c (x (k + 1)) (y k)
  y_step (k : ℕ) :
    y (k + 1) =
      admm_multiplier_update ρ A B c (y k) (x (k + 1)) (z (k + 1))

/-- An Algorithm 15.3 alternating ADMM trajectory predicate is a proposition, hence
subsingleton. -/
instance instSubsingletonIsADMMAlternatingTrajectory
    {ρ : PosReal}
    {h₁ : X → EReal} {h₂ : Z → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c : Y}
    {x : ℕ → X} {z : ℕ → Z} {y : ℕ → Y}
    {x0 : X} {z0 : Z} {y0 : Y} :
    Subsingleton (IsADMMAlternatingTrajectory ρ h₁ h₂ A B c x z y x0 z0 y0) :=
  inferInstance

end
