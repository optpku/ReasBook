/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_15
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_4
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

noncomputable section

section

variable {n l : ℕ}

local notation "E" => Fin n → ℝ

/- Definition 13.10 is `source-facing`: the item introduces a concrete quadratic program on
`ℝ^n` with feasible set the convex hull of finitely many points. The relevant `core/canonical`
owners already present in the project are:

- `quadratic_affine_function` from Definition 4.4 for the quadratic objective
  `x ↦ (1 / 2) xᵀ Q x + bᵀ x`;
- `constrained_problem_objective` from Definition 3.15 for the constrained optimization owner.

The primitive data for this owner are therefore only the matrix `Q`, the linear term `b`, and the
finite vertex family `a`. Positive-definiteness of `Q` is a later property used by downstream
algorithms and optimality statements, not part of the defining owner itself. The clean public API
is therefore a direct specialization of the constrained-problem owner, with separate source-facing
names for the feasible set `Ω`, the quadratic objective `f_q`, and the optimal value `f_opt`. The
only nontrivial bridge needed here is the canonical Chapter 9 lift `Function.toEReal`, which
replaces a raw lambda coercion in the constrained objective. -/

/- The objective and constrained-problem owners already exist upstream; Definition 13.10 only
specializes them to the finite-hull quadratic setting. -/
recall quadratic_affine_function
recall quadratic_affine_function_apply
recall constrained_problem_objective
recall constrained_problem_objective_of_mem
recall constrained_problem_objective_of_not_mem

/-- The feasible set `Ω = conv{a₁, …, a_l}` for the finite-hull quadratic problem. -/
def polytope_quadratic_feasible_set (a : Fin l → E) : Set E :=
  convexHull ℝ (Set.range a)

/-- The quadratic objective `f_q(x) = (1 / 2) xᵀ Q x + bᵀ x` attached to a matrix `Q` and linear
term `b`. -/
abbrev polytope_quadratic_objective
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) : E → ℝ :=
  quadratic_affine_function Q b 0

-- Proof sketch: specialize `quadratic_affine_function_apply` at constant term `0`; the final
-- `+ 0` disappears by simplification.
/-- Evaluating `polytope_quadratic_objective Q b` at `x` gives the textbook formula
`(1 / 2) xᵀ Q x + bᵀ x`. -/
@[simp] theorem polytope_quadratic_objective_apply
    (Q : Matrix (Fin n) (Fin n) ℝ) (b x : E) :
    polytope_quadratic_objective Q b x =
      (1 / 2 : ℝ) * dotProduct x (Q *ᵥ x) + dotProduct b x := by
  simp [polytope_quadratic_objective]

/-- Definition 13.10: the quadratic program (13.32) on `ℝ^n`, with matrix `Q`, linear term `b`,
and feasible set `Ω = conv{a₁, a₂, …, a_l}`, is the constrained objective obtained by restricting
`x ↦ (1 / 2) xᵀ Q x + bᵀ x` to `Ω`. In the textbook setting, later results further assume
`Q ∈ 𝕊_{++}^n`. -/
abbrev polytope_quadratic_problem
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) : E → EReal :=
  constrained_problem_objective
    (polytope_quadratic_objective Q b).toEReal
    (polytope_quadratic_feasible_set a)

-- Proof sketch: rewrite `polytope_quadratic_problem` as `constrained_problem_objective` on the
-- feasible set `polytope_quadratic_feasible_set a`, then apply
-- `constrained_problem_objective_of_mem`.
/-- On the feasible set `Ω`, the quadratic problem agrees with the quadratic objective `f_q`. -/
@[simp] theorem polytope_quadratic_problem_of_mem
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) {x : E}
    (hx : x ∈ polytope_quadratic_feasible_set a) :
    polytope_quadratic_problem Q b a x = polytope_quadratic_objective Q b x := by
  simpa [polytope_quadratic_problem] using
    constrained_problem_objective_of_mem (polytope_quadratic_objective Q b).toEReal hx

-- Proof sketch: rewrite `polytope_quadratic_problem` as `constrained_problem_objective` on the
-- feasible set `polytope_quadratic_feasible_set a`, then apply
-- `constrained_problem_objective_of_not_mem`.
/-- Outside the feasible set `Ω`, the quadratic problem takes the infeasible value `⊤`. -/
@[simp] theorem polytope_quadratic_problem_of_not_mem
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) {x : E}
    (hx : x ∉ polytope_quadratic_feasible_set a) :
    polytope_quadratic_problem Q b a x = ⊤ := by
  simpa [polytope_quadratic_problem] using
    constrained_problem_objective_of_not_mem (polytope_quadratic_objective Q b).toEReal hx

/-- The optimal value `f_opt` of the finite-hull quadratic problem is the infimum of the attained
values of its constrained objective. -/
def polytope_quadratic_optimal_value
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) : EReal :=
  sInf (Set.range (polytope_quadratic_problem Q b a))

-- Proof sketch: unfold `polytope_quadratic_optimal_value`; the result is exactly its defining
-- `sInf` expression over the constrained objective values.
/-- Expanding `polytope_quadratic_optimal_value Q b a` gives the `sInf` of the values of the
quadratic problem (13.32). -/
theorem polytope_quadratic_optimal_value_eq_sInf
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) :
    polytope_quadratic_optimal_value Q b a =
      sInf (Set.range (polytope_quadratic_problem Q b a)) :=
  rfl

end
