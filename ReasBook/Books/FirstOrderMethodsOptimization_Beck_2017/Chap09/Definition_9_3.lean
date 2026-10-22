/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Order.Filter.Extr
import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Gradient

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 9.3 is `source-facing`: the textbook specifies a recursive first-order procedure
through explicit iterates `x^k`, chosen positive stepsizes `t_k`, chosen Euclidean subgradients
`f'(x^k)`, and an argmin update over the feasible set `C`. The owner abstractions already present
in the project for these ingredients are the Euclidean subgradient bridge
`euclideanSubdifferentialAt`, the source-facing subdifferential domain
`subdifferential_domain` for the mirror map `ω.toEReal`, and mathlib's minimizer predicate
`IsMinOn` for the argmin step. Since no canonical minimizer has been chosen, the public object
here is a trajectory predicate on the iterate, stepsize, and selected-subgradient sequences,
together with the explicit one-step mirror-descent objective. -/

/-- The one-step mirror-descent objective obtained by linearizing `f` with the chosen
subgradient `g` at the current iterate `x` and keeping the mirror map `ω` explicit. This is the
textbook objective `y ↦ ⟪t • g - ∇ ω x, y⟫ + ω y`, equivalent to the Bregman-distance form from
Definition 9.2 when that auxiliary API is available. -/
def mirror_descent_update_objective (ω : E → ℝ) (x g : E) (t : ℝ) : E → ℝ :=
  fun y ↦ inner ℝ (t • g - ∇ ω x) y + ω y

/-- Evaluating `mirror_descent_update_objective ω x g t` at `y` gives the linearized term
`⟪t • g - ∇ ω x, y⟫` plus the mirror map value `ω y`. -/
@[simp] theorem mirror_descent_update_objective_apply
    (ω : E → ℝ) (x g y : E) (t : ℝ) :
    mirror_descent_update_objective ω x g t y =
      inner ℝ (t • g - ∇ ω x) y + ω y := rfl

/-- Definition 9.3: sequences of iterates `x`, stepsizes `t`, and chosen Euclidean subgradients
`g` follow the Mirror Descent Method for objective `f`, mirror map `ω`, and feasible set `C` when
for every iteration `k`, the current iterate lies in `C ∩ dom(∂ ω)`, the chosen vector `g k`
belongs to `∂ f(x^k)`, the stepsize `t k` is positive, and the next iterate `x^(k+1)` minimizes
the mirror-descent update objective
`y ↦ ⟪t_k g_k - ∇ ω(x^k), y⟫ + ω(y)` over `C`. -/
def is_mirror_descent_trajectory
    (f ω : E → ℝ) (C : Set E) (x g : ℕ → E) (t : ℕ → ℝ) : Prop :=
  ∀ k,
    x k ∈ C ∩ subdifferential_domain ω.toEReal ∧
      g k ∈ euclideanSubdifferentialAt f (x k) ∧
      0 < t k ∧
      IsMinOn (mirror_descent_update_objective ω (x k) (g k) (t k)) C (x (k + 1))

-- Proof sketch: specialize the defining universal clause in
-- `is_mirror_descent_trajectory f ω C x g t` at the iteration index `k`.
/-- A mirror-descent trajectory satisfies the feasible-domain, subgradient, positive-stepsize, and
one-step minimization conditions at each iteration. -/
theorem is_mirror_descent_trajectory_step
    {f ω : E → ℝ} {C : Set E} {x g : ℕ → E} {t : ℕ → ℝ}
    (h : is_mirror_descent_trajectory f ω C x g t) (k : ℕ) :
    x k ∈ C ∩ subdifferential_domain ω.toEReal ∧
      g k ∈ euclideanSubdifferentialAt f (x k) ∧
      0 < t k ∧
      IsMinOn (mirror_descent_update_objective ω (x k) (g k) (t k)) C (x (k + 1)) :=
  h k

/-- A mirror-descent trajectory keeps every iterate in the feasible set `C`. -/
theorem is_mirror_descent_trajectory.mem_feasible_set
    {f ω : E → ℝ} {C : Set E} {x g : ℕ → E} {t : ℕ → ℝ}
    (h : is_mirror_descent_trajectory f ω C x g t) (k : ℕ) :
    x k ∈ C :=
  (is_mirror_descent_trajectory_step h k).1.1

/-- A mirror-descent trajectory keeps every iterate in the subdifferential domain `dom(∂ ω)`. -/
theorem is_mirror_descent_trajectory.mem_subdifferential_domain
    {f ω : E → ℝ} {C : Set E} {x g : ℕ → E} {t : ℕ → ℝ}
    (h : is_mirror_descent_trajectory f ω C x g t) (k : ℕ) :
    x k ∈ subdifferential_domain ω.toEReal :=
  (is_mirror_descent_trajectory_step h k).1.2

/-- A mirror-descent trajectory chooses a Euclidean subgradient of `f` at each iterate. -/
theorem is_mirror_descent_trajectory.subgradient_mem
    {f ω : E → ℝ} {C : Set E} {x g : ℕ → E} {t : ℕ → ℝ}
    (h : is_mirror_descent_trajectory f ω C x g t) (k : ℕ) :
    g k ∈ euclideanSubdifferentialAt f (x k) :=
  (is_mirror_descent_trajectory_step h k).2.1

/-- A mirror-descent trajectory uses positive stepsizes. -/
theorem is_mirror_descent_trajectory.stepsize_pos
    {f ω : E → ℝ} {C : Set E} {x g : ℕ → E} {t : ℕ → ℝ}
    (h : is_mirror_descent_trajectory f ω C x g t) (k : ℕ) :
    0 < t k :=
  (is_mirror_descent_trajectory_step h k).2.2.1

/-- A mirror-descent trajectory makes the next iterate a minimizer of the one-step objective on
the feasible set `C`. -/
theorem is_mirror_descent_trajectory.isMinOn
    {f ω : E → ℝ} {C : Set E} {x g : ℕ → E} {t : ℕ → ℝ}
    (h : is_mirror_descent_trajectory f ω C x g t) (k : ℕ) :
    IsMinOn (mirror_descent_update_objective ω (x k) (g k) (t k)) C (x (k + 1)) :=
  (is_mirror_descent_trajectory_step h k).2.2.2

end
