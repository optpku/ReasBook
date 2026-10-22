/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 10.1 is `source-facing`: the textbook specifies the proximal gradient method through
explicit iterates `x^k`, explicit positive curvature estimates `L_k`, and the canonical proximal
update for the scaled nonsmooth term. Since the chapter's proximal owner `prox[...]` is set-valued,
the faithful public API is a trajectory predicate rather than a recursively chosen iterate map. -/

/-- The admissible next iterates of one proximal-gradient step from `x` with curvature parameter
`L` are the proximal points of `(1 / L) g` at the forward gradient point
`x - (1 / L) ∇ (f.toReal)(x)`. -/
def proximal_gradient_step (f g : E → EReal) (x : E) (L : PosReal) : Set E :=
  prox[((((1 / L : PosReal) : EReal) • g))]
    (x - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) x)

-- Proof sketch: unfold `proximal_gradient_step`; membership is by definition membership in the
-- corresponding proximal set of `(1 / L) g` at the forward gradient point.
/-- A point belongs to `proximal_gradient_step f g x L` exactly when it is a proximal point of the
scaled function `(1 / L) g` at `x - (1 / L) ∇ (f.toReal)(x)`. -/
@[simp] theorem mem_proximal_gradient_step_iff
    {f g : E → EReal} {x xNext : E} {L : PosReal} :
    xNext ∈ proximal_gradient_step f g x L ↔
      xNext ∈ prox[((((1 / L : PosReal) : EReal) • g))]
        (x - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) x) := Iff.rfl

/-- Algorithm 10.1: a sequence `x^k` follows the proximal gradient method for the composite
objective `f + g` with positive parameters `L_k` when, at every iteration `k`, the current
iterate lies in `int(dom(f))` and the next iterate satisfies
`x^(k+1) ∈ prox_{(1 / L_k) g}(x^k - (1 / L_k) ∇ f(x^k))`. -/
def is_proximal_gradient_trajectory
    (f g : E → EReal) (x : ℕ → E) (L : ℕ → PosReal) : Prop :=
  ∀ k : ℕ,
    x k ∈ interior (effective_domain f) ∧
      x (k + 1) ∈ proximal_gradient_step f g (x k) (L k)

-- Proof sketch: specialize the defining universal clause in
-- `is_proximal_gradient_trajectory f g x L` at the iteration index `k`.
/-- A proximal-gradient trajectory satisfies the interior-domain requirement and the proximal
update rule at each iteration `k`. -/
theorem is_proximal_gradient_trajectory_step
    {f g : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}
    (h : is_proximal_gradient_trajectory f g x L) (k : ℕ) :
    x k ∈ interior (effective_domain f) ∧
      x (k + 1) ∈ proximal_gradient_step f g (x k) (L k) :=
  h k

/-- The current iterate of a proximal-gradient trajectory lies in `interior (effective_domain f)`.
-/
theorem proximal_gradient_trajectory_mem_interior_effective_domain
    {f g : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L) (k : ℕ) :
    x k ∈ interior (effective_domain f) :=
  (is_proximal_gradient_trajectory_step htraj k).1

/-- The iterate `x^k` of a proximal-gradient trajectory, viewed as a point of
`interior (effective_domain f)`. -/
def proximal_gradient_trajectory_iterate
    {f g : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L) (k : ℕ) :
    interior (effective_domain f) :=
  ⟨x k, proximal_gradient_trajectory_mem_interior_effective_domain htraj k⟩

end
