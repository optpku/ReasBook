/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 9.6 is `source-facing`: the textbook gives an iterative composite mirror-descent
procedure through explicit iterates, chosen positive stepsizes, chosen subgradients of `f`, and
the explicit unconstrained argmin update (9.32). The owner abstractions already present in the
project for these ingredients are `effective_domain`, `subdifferential_domain`, `∂ₛ f(x)`, the
continuous-dual derivative `fderiv ℝ (fun y ↦ (ω y).toReal) xk`,
and mathlib's minimizer predicate `IsMinOn`, so this item is best recorded as the explicit
one-step objective together with a trajectory predicate. The later equation-(9.33) Bregman rewrite
belongs in a separate `bridge/view` file and should reuse this equation-(9.32) owner rather than
duplicate it. -/

/-- The continuous linear functional `t s - ω'(xk)` appearing in the one-step Mirror-C problem. -/
def mirror_c_problem_functional
    (ω : E → EReal) (xk : E) (s : StrongDual ℝ E) (t : ℝ) : StrongDual ℝ E :=
  t • s - fderiv ℝ (fun y ↦ (ω y).toReal) xk

-- Proof sketch: unfold `mirror_c_problem_functional`; evaluation at `x` is exactly the displayed
-- linear functional `t s x - ω'(xk)(x)`.
/-- Evaluating the Mirror-C problem functional at `x` gives the scalar linear term
`t s(x) - ω'(xk)(x)`. -/
@[simp] theorem mirror_c_problem_functional_apply
    (ω : E → EReal) (xk x : E) (s : StrongDual ℝ E) (t : ℝ) :
    mirror_c_problem_functional ω xk s t x =
      t * s x - fderiv ℝ (fun y ↦ (ω y).toReal) xk x :=
  rfl

/-- The one-step Mirror-C objective from equation (9.32), written as the extended-real-valued
function `x ↦ (t s - ω'(xk))(x) + t g(x) + ω(x)` using a chosen strong-dual subgradient
`s ∈ ∂ₛ f(xk)`. -/
def mirror_c_update_objective
    (g ω : E → EReal) (xk : E) (s : StrongDual ℝ E) (t : ℝ) : E → EReal :=
  fun x ↦
    (((mirror_c_problem_functional ω xk s t x : ℝ) : EReal) +
      (t : EReal) * g x) +
      ω x

-- Proof sketch: unfold `mirror_c_update_objective`; the displayed identity is exactly its
-- defining lambda expression.
/-- Evaluating the Mirror-C one-step objective at `x` gives the linear term
`(t s - ω'(xk))(x)` together with the composite penalty `t g(x) + ω(x)`. -/
@[simp] theorem mirror_c_update_objective_apply
    (g ω : E → EReal) (xk x : E) (s : StrongDual ℝ E) (t : ℝ) :
    mirror_c_update_objective g ω xk s t x =
      (((mirror_c_problem_functional ω xk s t x : ℝ) : EReal) +
        (t : EReal) * g x) +
        ω x := rfl

/-- Definition 9.6: sequences of iterates `x`, chosen subgradients `s`, and stepsizes `t`
follow the Mirror-C Method for the composite objective `f + g` with mirror map `ω` when at every
iteration `k` the current iterate lies in `dom(g) ∩ dom(∂ ω)`, the chosen functional `s k`
belongs to `∂ₛ f(x^k)`, the stepsize `t k` is positive, and the next iterate `x^(k+1)` minimizes
the explicit Mirror-C objective from equation (9.32) over all `x`. -/
def is_mirror_c_trajectory
    (f g ω : E → EReal) (x : ℕ → E) (s : ℕ → StrongDual ℝ E) (t : ℕ → ℝ) : Prop :=
  ∀ k,
    x k ∈ effective_domain g ∩ subdifferential_domain ω ∧
      s k ∈ ∂ₛ f(x k) ∧
      0 < t k ∧
      IsMinOn (mirror_c_update_objective g ω (x k) (s k) (t k)) Set.univ (x (k + 1))

-- Proof sketch: specialize the defining universal clause in
-- `is_mirror_c_trajectory f g ω x s t` at the iteration index `k`.
/-- A Mirror-C trajectory satisfies the domain, chosen-subgradient, positive-stepsize, and one-step
minimization conditions at each iteration. -/
theorem is_mirror_c_trajectory_step
    {f g ω : E → EReal} {x : ℕ → E} {s : ℕ → StrongDual ℝ E} {t : ℕ → ℝ}
    (h : is_mirror_c_trajectory f g ω x s t) (k : ℕ) :
    x k ∈ effective_domain g ∩ subdifferential_domain ω ∧
      s k ∈ ∂ₛ f(x k) ∧
      0 < t k ∧
      IsMinOn (mirror_c_update_objective g ω (x k) (s k) (t k)) Set.univ (x (k + 1)) :=
  h k

/-- A Mirror-C trajectory keeps every iterate in the effective domain of `g`. -/
theorem is_mirror_c_trajectory.mem_effective_domain
    {f g ω : E → EReal} {x : ℕ → E} {s : ℕ → StrongDual ℝ E} {t : ℕ → ℝ}
    (h : is_mirror_c_trajectory f g ω x s t) (k : ℕ) :
    x k ∈ effective_domain g :=
  (is_mirror_c_trajectory_step h k).1.1

/-- A Mirror-C trajectory keeps every iterate in the subdifferential domain `dom(∂ ω)`. -/
theorem is_mirror_c_trajectory.mem_subdifferential_domain
    {f g ω : E → EReal} {x : ℕ → E} {s : ℕ → StrongDual ℝ E} {t : ℕ → ℝ}
    (h : is_mirror_c_trajectory f g ω x s t) (k : ℕ) :
    x k ∈ subdifferential_domain ω :=
  (is_mirror_c_trajectory_step h k).1.2

/-- A Mirror-C trajectory chooses a strong-dual subgradient of `f` at each iterate. -/
theorem is_mirror_c_trajectory.subgradient_mem
    {f g ω : E → EReal} {x : ℕ → E} {s : ℕ → StrongDual ℝ E} {t : ℕ → ℝ}
    (h : is_mirror_c_trajectory f g ω x s t) (k : ℕ) :
    s k ∈ ∂ₛ f(x k) :=
  (is_mirror_c_trajectory_step h k).2.1

/-- A Mirror-C trajectory uses positive stepsizes. -/
theorem is_mirror_c_trajectory.stepsize_pos
    {f g ω : E → EReal} {x : ℕ → E} {s : ℕ → StrongDual ℝ E} {t : ℕ → ℝ}
    (h : is_mirror_c_trajectory f g ω x s t) (k : ℕ) :
    0 < t k :=
  (is_mirror_c_trajectory_step h k).2.2.1

/-- A Mirror-C trajectory makes the next iterate a global minimizer of the one-step objective. -/
theorem is_mirror_c_trajectory.isMinOn
    {f g ω : E → EReal} {x : ℕ → E} {s : ℕ → StrongDual ℝ E} {t : ℕ → ℝ}
    (h : is_mirror_c_trajectory f g ω x s t) (k : ℕ) :
    IsMinOn (mirror_c_update_objective g ω (x k) (s k) (t k)) Set.univ (x (k + 1)) :=
  (is_mirror_c_trajectory_step h k).2.2.2

end
