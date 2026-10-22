/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

variable {E : Type u}
variable [NormedAddCommGroup E]

/- Definition 12.10 is `source-facing`: it introduces the denoising objective consisting of a
quadratic data-fidelity term together with a regularizer applied after the linear map `A`.

Domain sampling in the chapter/project gives the relevant owner split:
- `composite_model_objective` from Definition 10.2 is the canonical owner for two-term objectives;
- `dual_based_proximal_gradient_primal_optimal_value` from Definition 12.1 is already the chapter
  owner for the associated whole-space optimal value `sInf (Set.range ...)`;
- Definition 12.14 reuses `composite_model_objective` together with `finite_sum_objective` for the
  analogous block finite-sum primal objective, rather than rebuilding a separate Chapter 12 owner.

Primitive data here are only the datum `d`, the regularizer `R`, and the linear map `A`. The
quadratic fidelity term and denoising objective are source-facing data; the optimal-value API is
derived and should remain a thin denoising-level bridge to the existing Chapter 12.1 owner rather
than a parallel reconstruction of the same `sInf (Set.range ...)` definition. -/

/-- The quadratic data-fidelity term `x ↦ (1 / 2) ‖x - d‖^2` in the denoising problem. -/
def denoising_data_fidelity (d : E) : E → EReal :=
  fun x ↦ ((‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) : EReal)

-- Proof sketch: unfold `denoising_data_fidelity`; the value at `x` is exactly the half squared
-- norm distance from `x` to the datum `d`.
/-- Evaluating the denoising data-fidelity term gives `(1 / 2) ‖x - d‖^2`. -/
@[simp] theorem denoising_data_fidelity_apply (d x : E) :
    denoising_data_fidelity d x = ((‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) := rfl

end

section

variable {E : Type u} {Y : Type v}
variable [NormedAddCommGroup E]

/- Semantic search note: `lean_leansearch` was unavailable in this environment, so the repair
follows the nearby Chapter 12 precedent of using a labeled recall for the canonical composite
objective owner and a thin source-facing bridge abbreviation. -/
/- Definition 12.10: the denoising problem objective is
`x ↦ (1 / 2) ‖x - d‖^2 + R (A x)`, realized as the Chapter 10 composite objective with quadratic
data-fidelity term and regularizer `R` composed with the map `A`. -/
recall composite_model_objective
recall composite_model_objective_apply
recall dual_based_proximal_gradient_primal_optimal_value_eq_sInf

/-- The Chapter 12 source-facing denoising objective, realized as the composite objective with
quadratic data-fidelity term and regularizer `R` composed with the map `A`. -/
abbrev denoising_problem_objective
    (d : E) (R : Y → EReal) (A : E → Y) : E → EReal :=
  composite_model_objective (denoising_data_fidelity d) (R ∘ A)

-- Proof sketch: unfold `denoising_problem_objective` through `composite_model_objective` and then
-- evaluate the quadratic data-fidelity term at `x`.
/-- Evaluating the denoising problem objective at `x` gives `(1 / 2) ‖x - d‖^2 + R (A x)`. -/
@[simp] theorem denoising_problem_objective_apply
    (d : E) (R : Y → EReal) (A : E → Y) (x : E) :
    denoising_problem_objective d R A x =
      ((‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) + R (A x) := rfl

/- The associated optimal value is not a new owner: it is the Chapter 12.1 primal optimal value
specialized to the denoising fidelity term and regularizer composed with `A`. -/
/-- The optimal value `f_opt` of the denoising problem. -/
abbrev denoising_problem_optimal_value
    (d : E) (R : Y → EReal) (A : E → Y) : EReal :=
  dual_based_proximal_gradient_primal_optimal_value (denoising_data_fidelity d) R A

-- Proof sketch: unfold `denoising_problem_optimal_value`; by Definition 12.1 it is the infimum
-- of the attained values of `denoising_problem_objective d R A`.
/-- Expanding the denoising optimal value gives the infimum of the attained denoising objective
values. -/
theorem denoising_problem_optimal_value_eq_sInf
    (d : E) (R : Y → EReal) (A : E → Y) :
    denoising_problem_optimal_value d R A =
      sInf (Set.range (denoising_problem_objective d R A)) := rfl

end
