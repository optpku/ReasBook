/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_15
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v

section

variable {ι : Type u} [Fintype ι]
variable {Y : Type v} [AddCommMonoid Y] [Module ℝ Y]

local notation "X" => EuclideanSpace ℝ ι

/- Semantic recall via `lean_leansearch` is unavailable in this runner, so the owner choice is
sampled from the nearby optimization files, the Chapter 3 constrained-objective owner, the
Chapter 6 Euclidean `ℓ¹` owner, and the Chapter 15 linear-map-based API.

This item is `source-facing`: it defines the basis-pursuit model `min ‖x‖₁` subject to `A x = b`.
The best `core/canonical` owner split already exists upstream:
- `constrained_problem_objective` owns the constrained extended-real objective;
- `EuclideanSpace.l1Norm`, written `‖x‖₁`, owns the Euclidean `ℓ¹` term on finite product spaces;
- Chapter 15 treats the forward operator canonically as a linear map `A : X →ₗ[ℝ] Y`.

Primitive data are therefore only the linear constraint fiber `A ⁻¹' {b}` and the `ℓ¹` objective.
The matrix presentation from the textbook is a `bridge/view` obtained by specializing `A` to
`Matrix.toEuclideanLin`. -/

/-- Definition 15.8: the basis-pursuit problem (15.28) is the constrained objective with `ℓ¹`
objective and affine feasible set `A x = b`. -/
def basis_pursuit_problem
    (A : X →ₗ[ℝ] Y) (b : Y) : X → EReal :=
  constrained_problem_objective (fun x ↦ ((‖x‖₁ : ℝ) : EReal))
    (A ⁻¹' ({b} : Set Y))

/-- Helper for Definition 15.8: on the affine feasible set `A x = b`, the basis-pursuit problem
agrees with the `ℓ¹` objective `‖x‖₁`. -/
@[simp] theorem basis_pursuit_problem_of_eq
    (A : X →ₗ[ℝ] Y) (b : Y) {x : X} (hx : A x = b) :
    basis_pursuit_problem A b x = ((‖x‖₁ : ℝ) : EReal) := by
  -- Translate the affine constraint into membership in the feasible fiber `A ⁻¹' {b}`.
  exact constrained_problem_objective_of_mem
    (fun x ↦ ((‖x‖₁ : ℝ) : EReal))
    (by simpa [Set.mem_preimage] using hx)

/-- Helper for Definition 15.8: outside the affine feasible set `A x = b`, the basis-pursuit
problem takes the infeasible value `⊤`. -/
@[simp] theorem basis_pursuit_problem_of_ne
    (A : X →ₗ[ℝ] Y) (b : Y) {x : X} (hx : A x ≠ b) :
    basis_pursuit_problem A b x = ⊤ := by
  -- Translate violation of the affine constraint into nonmembership in the feasible fiber.
  exact constrained_problem_objective_of_not_mem
    (fun x ↦ ((‖x‖₁ : ℝ) : EReal))
    (by simpa [Set.mem_preimage] using hx)

/-- Helper for Definition 15.8: evaluating the basis-pursuit problem at `x` gives `‖x‖₁` when
`A x = b`, and `⊤` otherwise. -/
@[simp] theorem basis_pursuit_problem_apply
    (A : X →ₗ[ℝ] Y) (b : Y) (x : X) :
    basis_pursuit_problem A b x =
      if A x = b then ((‖x‖₁ : ℝ) : EReal) else ⊤ := by
  -- Split on feasibility to expose the constrained-objective branch selected at `x`.
  by_cases hx : A x = b
  · rw [if_pos hx]
    exact basis_pursuit_problem_of_eq A b hx
  · rw [if_neg hx]
    exact basis_pursuit_problem_of_ne A b hx

end
