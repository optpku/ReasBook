/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_15
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

variable {X : Type u} {Z : Type v} {Y : Type w}

/- `prompt_add/` is absent in this workspace, so the owner selection is sampled directly from the
nearby optimization files.

This item is `source-facing`: it introduces the two-block objective `H(x, z) = h₁(x) + h₂(z)`
together with the affine equality constraint `A x + B z = c`. Domain sampling from the nearby
split-model files shows that the best owner abstraction for the product-space sum is already
upstream: Chapter 10's `composite_model_objective`. Accordingly, this file keeps the Chapter 15
surface owner `H[h₁, h₂]`, but refines it to a thin specialization of that canonical additive
owner on `X × Z`. The genuinely new source-facing data then remain the affine feasible set, the
constrained infimum value, and the Chapter 15 regularity bundle. The matrix notation from the text
is represented canonically by linear maps `A : X →ₗ[𝕜] Y` and `B : Z →ₗ[𝕜] Y`; only the later
regularity bundle remains specialized to `ℝ`, where convexity and lower-semicontinuity live. -/

/-- The two-block objective `H(x, z) = h₁(x) + h₂(z)` appearing in the ADMM primal problem. -/
abbrev admm_objective (h₁ : X → EReal) (h₂ : Z → EReal) : X × Z → EReal :=
  composite_model_objective (h₁ ∘ Prod.fst) (h₂ ∘ Prod.snd)

/- Textbook notation for the ADMM primal objective `H`. -/
notation "H[" h₁ ", " h₂ "]" => admm_objective h₁ h₂

-- Proof sketch: unfold `admm_objective`; evaluation at `(x, z)` is exactly the defining sum
-- `h₁ x + h₂ z`.
/-- Evaluating the ADMM objective at `(x, z)` gives `h₁(x) + h₂(z)`. -/
@[simp] theorem admm_objective_apply
    (h₁ : X → EReal) (h₂ : Z → EReal) (x : X) (z : Z) :
    H[h₁, h₂] (x, z) = h₁ x + h₂ z :=
  rfl

end

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable {𝕜 : Type*} [Semiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Z] [Module 𝕜 Z]
variable [AddCommMonoid Y] [Module 𝕜 Y]

/-- The affine feasible set for the ADMM constraint `A x + B z = c`. -/
def admm_feasible_set
    (A : X →ₗ[𝕜] Y) (B : Z →ₗ[𝕜] Y) (c : Y) : Set (X × Z) :=
  {xz | A xz.1 + B xz.2 = c}

-- Proof sketch: unfold `admm_feasible_set`; membership of `(x, z)` is exactly the affine
-- constraint equation `A x + B z = c`.
/-- A pair `(x, z)` is feasible for the ADMM problem exactly when `A x + B z = c`. -/
@[simp] theorem mem_admm_feasible_set
    (A : X →ₗ[𝕜] Y) (B : Z →ₗ[𝕜] Y) (c : Y) (x : X) (z : Z) :
    (x, z) ∈ admm_feasible_set A B c ↔ A x + B z = c :=
  Iff.rfl

/-- Definition 15.1: the ADMM primal problem
`H_opt = min { H(x, z) ≡ h₁(x) + h₂(z) : A x + B z = c }`, where `h₁` and `h₂` are proper
closed convex functions, is represented by the infimum of the canonical constrained objective on
`X × Z` built from `H[h₁, h₂]` and the affine feasible set `A x + B z = c`. -/
def admm_problem_value
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[𝕜] Y) (B : Z →ₗ[𝕜] Y) (c : Y) : EReal :=
  sInf (Set.range (constrained_problem_objective
    (H[h₁, h₂]) (admm_feasible_set A B c)))

/- Textbook notation for the ADMM primal optimal value `H_opt`. -/
notation "H_opt[" h₁ ", " h₂ "; " A ", " B ", " c "]" =>
  admm_problem_value h₁ h₂ A B c

/-- The ADMM primal optimal value is the infimum of the constrained objective values. -/
theorem admm_problem_value_eq_sInf
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[𝕜] Y) (B : Z →ₗ[𝕜] Y) (c : Y) :
    H_opt[h₁, h₂; A, B, c] =
      sInf (Set.range (constrained_problem_objective
        (H[h₁, h₂]) (admm_feasible_set A B c))) :=
  rfl

end

section

variable {X : Type u} {Z : Type v}
variable [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]
variable [TopologicalSpace Z] [AddCommMonoid Z] [Module ℝ Z]

/-- Auxiliary Chapter 15 assumption package: both ADMM block objectives are proper, closed, and
convex. This is used downstream as a reusable hypothesis bundle, not as the source-facing primal
problem owner from Definition 15.1. -/
class IsADMMConvexObjectivePair
    (h₁ : X → EReal) (h₂ : Z → EReal) : Prop
    extends IsProperExtendedRealFunction h₁ where
  h₂_proper : IsProperExtendedRealFunction h₂
  h₁_closed : LowerSemicontinuous h₁
  h₂_closed : LowerSemicontinuous h₂
  h₁_convex : is_convex_function h₁
  h₂_convex : is_convex_function h₂

end
