/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Z] [Module ℝ Z]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled from the nearby
optimization files. This item is `source-facing`: the algorithm specifies two nonunique proximal
`arg min` subproblems and then the standard ADMM affine multiplier update. The owner split is:
- `PosReal` for the positive penalty parameter `ρ`;
- `QuadraticForm ℝ X` and `QuadraticForm ℝ Z` for the displayed quadratic proximal penalties;
- `admm_primal_update_objective` from Algorithm 15.2 for the non-proximal ADMM
  augmented-Lagrangian term;
- `unconstrained_problem_solutions` from Definition 8.2 for the canonical global argmin-set owner;
- `admm_multiplier_update` from Algorithm 15.2 for the canonical affine dual update;
- a trajectory class on the three iterate sequences, since the minimizing points need not be
  canonically chosen.

The shifted quadratic penalties are genuinely new source-facing data here, so this file keeps only
that extra proximal layer on top of the Chapter 15 one-block ADMM owners. -/

/-- The `x`-subproblem objective in AD-PMM, namely
`h₁(x) + (ρ / 2) ‖A x + B zᵏ - c + (1 / ρ) yᵏ‖² + (1 / 2) G(x - xᵏ)`, where the
`G`-weighted squared norm is represented by the quadratic form `G`. -/
def ad_pmm_x_update_objective
    (ρ : PosReal)
    (h₁ : X → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (c : Y) (zk : Z) (yk : Y)
    (G : QuadraticForm ℝ X) (xk : X) :
    X → EReal :=
  fun x ↦
    admm_primal_update_objective ρ h₁ (0 : Z → EReal) A B c yk (x, zk) +
      ((((1 / 2 : ℝ) * G (x - xk) : ℝ) : EReal))

-- Proof sketch: unfold `ad_pmm_x_update_objective`; evaluation at `x` is exactly the displayed
-- proximal augmented-Lagrangian model in step (a) of Algorithm 15.4.
/-- Evaluating the AD-PMM `x`-subproblem objective at `x` gives the textbook step-(a) formula. -/
@[simp] theorem ad_pmm_x_update_objective_apply
    (ρ : PosReal)
    (h₁ : X → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (c : Y) (zk : Z) (yk : Y)
    (G : QuadraticForm ℝ X) (xk : X) (x : X) :
    ad_pmm_x_update_objective ρ h₁ A B c zk yk G xk x =
      h₁ x +
        ((((ρ : ℝ) / 2) * ‖A x + B zk - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) : ℝ) : EReal) +
          ((((1 / 2 : ℝ) * G (x - xk) : ℝ) : EReal)) :=
  by
    simp [ad_pmm_x_update_objective]

/-- The admissible `x`-updates in step (a) of AD-PMM are the global minimizers of the proximal
augmented-Lagrangian objective at the current iterates `xᵏ`, `zᵏ`, and `yᵏ`. -/
abbrev ad_pmm_x_update_argmin
    (ρ : PosReal)
    (h₁ : X → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (c : Y) (zk : Z) (yk : Y)
    (G : QuadraticForm ℝ X) (xk : X) :
    Set X :=
  unconstrained_problem_solutions (ad_pmm_x_update_objective ρ h₁ A B c zk yk G xk)

-- Proof sketch: unfold `ad_pmm_x_update_argmin`; membership is definitionally the global
-- minimizer condition for the step-(a) objective.
/-- A point belongs to the AD-PMM `x`-update set exactly when it globally minimizes the step-(a)
objective over all `x`. -/
@[simp] theorem mem_ad_pmm_x_update_argmin_iff
    {ρ : PosReal}
    {h₁ : X → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y}
    {c : Y} {zk : Z} {yk : Y}
    {G : QuadraticForm ℝ X} {xk : X} {xNext : X} :
    xNext ∈ ad_pmm_x_update_argmin ρ h₁ A B c zk yk G xk ↔
      IsMinOn (ad_pmm_x_update_objective ρ h₁ A B c zk yk G xk) Set.univ xNext :=
  mem_unconstrained_problem_solutions_iff

/-- The `z`-subproblem objective in AD-PMM, namely
`h₂(z) + (ρ / 2) ‖A xᵏ⁺¹ + B z - c + (1 / ρ) yᵏ‖² + (1 / 2) Q(z - zᵏ)`, where the
`Q`-weighted squared norm is represented by the quadratic form `Q`. -/
def ad_pmm_z_update_objective
    (ρ : PosReal)
    (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (c : Y) (xNext : X) (yk : Y)
    (Q : QuadraticForm ℝ Z) (zk : Z) :
    Z → EReal :=
  fun z ↦
    admm_primal_update_objective ρ (0 : X → EReal) h₂ A B c yk (xNext, z) +
      ((((1 / 2 : ℝ) * Q (z - zk) : ℝ) : EReal))

-- Proof sketch: unfold `ad_pmm_z_update_objective`; evaluation at `z` is exactly the displayed
-- proximal augmented-Lagrangian model in step (b) of Algorithm 15.4.
/-- Evaluating the AD-PMM `z`-subproblem objective at `z` gives the textbook step-(b) formula. -/
@[simp] theorem ad_pmm_z_update_objective_apply
    (ρ : PosReal)
    (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (c : Y) (xNext : X) (yk : Y)
    (Q : QuadraticForm ℝ Z) (zk : Z) (z : Z) :
    ad_pmm_z_update_objective ρ h₂ A B c xNext yk Q zk z =
      h₂ z +
        ((((ρ : ℝ) / 2) * ‖A xNext + B z - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) : ℝ) : EReal) +
          ((((1 / 2 : ℝ) * Q (z - zk) : ℝ) : EReal)) :=
  by
    simp [ad_pmm_z_update_objective]

/-- The admissible `z`-updates in step (b) of AD-PMM are the global minimizers of the proximal
augmented-Lagrangian objective at the current iterates `xᵏ⁺¹`, `zᵏ`, and `yᵏ`. -/
abbrev ad_pmm_z_update_argmin
    (ρ : PosReal)
    (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (c : Y) (xNext : X) (yk : Y)
    (Q : QuadraticForm ℝ Z) (zk : Z) :
    Set Z :=
  unconstrained_problem_solutions (ad_pmm_z_update_objective ρ h₂ A B c xNext yk Q zk)

-- Proof sketch: unfold `ad_pmm_z_update_argmin`; membership is definitionally the global
-- minimizer condition for the step-(b) objective.
/-- A point belongs to the AD-PMM `z`-update set exactly when it globally minimizes the step-(b)
objective over all `z`. -/
@[simp] theorem mem_ad_pmm_z_update_argmin_iff
    {ρ : PosReal}
    {h₂ : Z → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y}
    {c : Y} {xNext : X} {yk : Y}
    {Q : QuadraticForm ℝ Z} {zk : Z} {zNext : Z} :
    zNext ∈ ad_pmm_z_update_argmin ρ h₂ A B c xNext yk Q zk ↔
      IsMinOn (ad_pmm_z_update_objective ρ h₂ A B c xNext yk Q zk) Set.univ zNext :=
  mem_unconstrained_problem_solutions_iff

/-- Algorithm 15.4: given initial iterates `x^0 = x0`, `z^0 = z0`, `y^0 = y0`, a positive
penalty parameter `ρ`, and quadratic proximal penalties `G` and `Q`, the sequences `x`, `z`, and
`y` form an AD-PMM trajectory when, for every iteration `k`, `x^(k+1)` minimizes
`h₁(x) + (ρ / 2) ‖A x + B z^k - c + (1 / ρ) y^k‖² + (1 / 2) G(x - x^k)`, `z^(k+1)` minimizes
`h₂(z) + (ρ / 2) ‖A x^(k+1) + B z - c + (1 / ρ) y^k‖² + (1 / 2) Q(z - z^k)`, and
`y^(k+1) = y^k + ρ (A x^(k+1) + B z^(k+1) - c)`. -/
class IsADPMMTrajectory
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (G : QuadraticForm ℝ X) (Q : QuadraticForm ℝ Z)
    (x0 : X) (z0 : Z) (y0 : Y)
    (x : ℕ → X) (z : ℕ → Z) (y : ℕ → Y) : Prop where
  /-- The `x`-sequence starts from the prescribed initial point `x0`. -/
  x_zero : x 0 = x0
  /-- The `z`-sequence starts from the prescribed initial point `z0`. -/
  z_zero : z 0 = z0
  /-- The multiplier sequence starts from the prescribed initial point `y0`. -/
  y_zero : y 0 = y0
  /-- At each iteration `k`, the next primal block `x^(k+1)` is chosen from the step-(a) `arg min`
  set. -/
  x_step (k : ℕ) :
    x (k + 1) ∈ ad_pmm_x_update_argmin ρ h₁ A B c (z k) (y k) G (x k)
  /-- At each iteration `k`, the next primal block `z^(k+1)` is chosen from the step-(b) `arg min`
  set. -/
  z_step (k : ℕ) :
    z (k + 1) ∈ ad_pmm_z_update_argmin ρ h₂ A B c (x (k + 1)) (y k) Q (z k)
  /-- At each iteration `k`, the multiplier satisfies the affine step-(c) update. -/
  y_step (k : ℕ) :
    y (k + 1) = admm_multiplier_update ρ A B c (y k) (x (k + 1)) (z (k + 1))

namespace IsADPMMTrajectory

/-- An AD-PMM trajectory starts from the prescribed initial iterates
`x^0 = x0`, `z^0 = z0`, and `y^0 = y0`. -/
theorem zero
    {ρ : PosReal}
    {h₁ : X → EReal} {h₂ : Z → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c : Y}
    {G : QuadraticForm ℝ X} {Q : QuadraticForm ℝ Z}
    {x0 : X} {z0 : Z} {y0 : Y}
    {x : ℕ → X} {z : ℕ → Z} {y : ℕ → Y}
    (h : IsADPMMTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y) :
    x 0 = x0 ∧ z 0 = z0 ∧ y 0 = y0 :=
  ⟨h.x_zero, h.z_zero, h.y_zero⟩

/-- At each iteration `k`, an AD-PMM trajectory satisfies the two proximal `arg min` clauses and
the affine multiplier update from Algorithm 15.4. -/
theorem step
    {ρ : PosReal}
    {h₁ : X → EReal} {h₂ : Z → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c : Y}
    {G : QuadraticForm ℝ X} {Q : QuadraticForm ℝ Z}
    {x0 : X} {z0 : Z} {y0 : Y}
    {x : ℕ → X} {z : ℕ → Z} {y : ℕ → Y}
    (h : IsADPMMTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    (k : ℕ) :
    x (k + 1) ∈ ad_pmm_x_update_argmin ρ h₁ A B c (z k) (y k) G (x k) ∧
      z (k + 1) ∈ ad_pmm_z_update_argmin ρ h₂ A B c (x (k + 1)) (y k) Q (z k) ∧
      y (k + 1) =
        admm_multiplier_update ρ A B c (y k) (x (k + 1)) (z (k + 1)) :=
  ⟨h.x_step k, h.z_step k, h.y_step k⟩

end IsADPMMTrajectory

end
