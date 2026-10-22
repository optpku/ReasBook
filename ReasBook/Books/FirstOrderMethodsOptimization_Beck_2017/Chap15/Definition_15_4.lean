/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_5
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Definition_15_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled directly from the
nearby Chapter 15 optimization files.

This item is `source-facing`: it records the standing assumptions for the convergence analysis of
the alternating-direction proximal method of multipliers. The existing owner abstraction
`IsADMMConvexObjectivePair` already packages clause (A), so the new public API extends that class
and adds only the extra data that are genuinely new here:
- the operator-valued quadratic penalties entering the one-block proximal subproblems from
  clause (D) and their argmin sets;
- the relative-interior qualification from clause (E);
- nonemptiness of the canonical primal optimal set from clause (F).

Domain sampling against Chapter 15 Definition 15.1 and Chapter 8's `arg min` owners shows no
upstream project owner for the operator-valued one-block objective
`u ↦ h(u) + (ρ / 2) ‖L u‖² + (1 / 2) ⟪u, P u⟫ + ⟪a, u⟫`. The duplicated `x`- and `z`-specific
definitions therefore refine to a single local owner on a real inner-product space, while the
source-facing class `IsADPMMProblem` remains the public owner for Definition 15.4 itself. -/

/-- The one-block proximal objective from Definition 15.4(D):
`u ↦ h(u) + (ρ / 2) ‖L u‖² + (1 / 2) ⟪u, P u⟫ + ⟪a, u⟫`. -/
def adpmm_proximal_objective
    (ρ : PosReal)
    (h : E → EReal) (L : E →ₗ[ℝ] F) (P : E →ₗ[ℝ] E) (a : E) :
    E → EReal :=
  fun u ↦
    h u +
      ((((ρ : ℝ) / 2) * ‖L u‖ ^ (2 : ℕ) : ℝ) : EReal) +
        ((((1 : ℝ) / 2) * inner ℝ u (P u) : ℝ) : EReal) +
          ((inner ℝ a u : ℝ) : EReal)

/-- Evaluating `adpmm_proximal_objective` gives
`h(u) + (ρ / 2) ‖L u‖² + (1 / 2) ⟪u, P u⟫ + ⟪a, u⟫`. -/
@[simp] theorem adpmm_proximal_objective_apply
    (ρ : PosReal)
    (h : E → EReal) (L : E →ₗ[ℝ] F) (P : E →ₗ[ℝ] E) (a : E) (u : E) :
    adpmm_proximal_objective ρ h L P a u =
      h u +
        ((((ρ : ℝ) / 2) * ‖L u‖ ^ (2 : ℕ) : ℝ) : EReal) +
          ((((1 : ℝ) / 2) * inner ℝ u (P u) : ℝ) : EReal) +
            ((inner ℝ a u : ℝ) : EReal) :=
  rfl

end

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Definition 15.4: Assumption 15.2 for the AD-PMM problem means that `h₁` and `h₂` form an
ADMM convex objective pair, the proximal operators `G` and `Q` are symmetric positive
semidefinite, every proximal one-block subproblem from clause (D) attains a minimizer, there exist
`x̂ ∈ ri(dom h₁)` and `ẑ ∈ ri(dom h₂)` with `A x̂ + B ẑ = c`, and the canonical primal optimal set
`constrained_problem_solutions (H[h₁, h₂]) (admm_feasible_set A B c)` is nonempty. The primal
optimal value remains the canonical owner `H_opt[h₁, h₂; A, B, c]`. -/
class IsADPMMProblem
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (G : X →ₗ[ℝ] X) (Q : Z →ₗ[ℝ] Z)
    (c : Y) : Prop
    extends IsADMMConvexObjectivePair h₁ h₂ where
  G_positive : LinearMap.IsPositive G
  Q_positive : LinearMap.IsPositive Q
  x_subproblem_argmin_nonempty (a : X) :
    (unconstrained_problem_solutions (adpmm_proximal_objective ρ h₁ A G a)).Nonempty
  z_subproblem_argmin_nonempty (b : Z) :
    (unconstrained_problem_solutions (adpmm_proximal_objective ρ h₂ B Q b)).Nonempty
  ri_qualification :
    ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
      ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
        A xHat + B zHat = c
  optimal_set_nonempty :
    (constrained_problem_solutions (H[h₁, h₂]) (admm_feasible_set A B c)).Nonempty

-- `lean_leansearch` was unavailable in this agent environment; the companion-instance choice
-- follows the local `Fact`-exposure pattern used in Chapter 10 assumption/problem owners.
/-- Companion instance exposing nonemptiness of the canonical primal optimal set to typeclass
search. -/
instance instFactOptimalSetNonemptyOfIsADPMMProblem
    {ρ : PosReal}
    {h₁ : X → EReal} {h₂ : Z → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y}
    {G : X →ₗ[ℝ] X} {Q : Z →ₗ[ℝ] Z}
    {c : Y}
    (h : IsADPMMProblem ρ h₁ h₂ A B G Q c) :
    Fact ((constrained_problem_solutions (H[h₁, h₂]) (admm_feasible_set A B c)).Nonempty) :=
  ⟨h.optimal_set_nonempty⟩

end
