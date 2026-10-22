/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap13.Algorithm_13_5

-- The source-facing exact-line-search trajectory owner shared across the Lemma 13.19 files.

noncomputable section

open Matrix

section

variable {n l : ℕ}

local notation "E" => Fin n → ℝ

variable {Q : positiveDefiniteMatrices n} {b : Fin n → ℝ} {a : Fin l → Fin n → ℝ}
variable {x : ℕ → polytope_quadratic_feasible_set a} {i : ℕ → Fin l}

/-- The exact-line-search trajectory owner for the nonterminal branch of Algorithm 13.5. Each
step chooses a minimizing vertex index, has negative directional derivative, and updates by the
exact-line-search conditional-gradient step. -/
class is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory
    (Q : positiveDefiniteMatrices n) (b : E) (a : Fin l → E)
    (x : ℕ → polytope_quadratic_feasible_set a) (i : ℕ → Fin l) : Prop where
  /-- At each iteration, the chosen vertex index minimizes the vertex linearization. -/
  argmin_mem (k : ℕ) :
    i k ∈
      unconstrained_problem_solutions
        (polytope_quadratic_vertex_linear_objective Q b a (x k))
  /-- Every step lies on the nonterminal branch `⟪dᵏ, ∇ f_q(xᵏ)⟫ < 0`. -/
  directional_derivative_neg (k : ℕ) :
    polytope_quadratic_conditional_gradient_directional_derivative Q b a (x k) (i k) < 0
  /-- The next iterate is the exact-line-search update from Algorithm 13.5. -/
  step_eq (k : ℕ) :
    x (k + 1) = polytope_quadratic_conditional_gradient_update Q b a (x k) (i k)

end
