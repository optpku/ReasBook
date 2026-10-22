/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_67

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- `prompt_add/` is absent in this workspace, so the nearby Chapter 3, Chapter 9, and Chapter 10
files supply the relevant owner discipline.

Algorithm 10.68 is `source-facing`: it defines the iterate sequence for the non-Euclidean
proximal-gradient method. The domain-style sampling in this part of the project points to:
- `non_euclidean_proximal_gradient_step` from Algorithm 10.67 as the canonical one-step owner for
  the Chapter 3 differentiability condition and the Chapter 9 Mirror-C minimizer clause;
- `effective_domain` and `subdifferential_domain` for the source domain clause
  `x^k ∈ dom(g) ∩ dom(∂ω)`;
- `PosReal` for the positive curvature parameters `L_k`.

Primitive data:
- the source domain clause `x^k ∈ dom(g) ∩ dom(∂ω)`;
- the canonical one-step predicate for `x^(k+1)`.

Derived API:
- projection lemmas exposing the iterate-domain clause, the canonical one-step predicate, and its
  differentiability/minimizer consequences separately.

Semantic search note: `lean_leansearch` only surfaced generic differentiability lemmas, so the
repair below follows the local Chapter 10 owner `non_euclidean_proximal_gradient_step` and its
Chapter 3/Chapter 9 companions directly. -/

/-- Algorithm 10.68: a sequence `x^k` follows the non-Euclidean proximal-gradient method for the
composite objective `f + g` with mirror map `ω` and positive curvature parameters `L_k` when, at
every iteration `k`, the current iterate lies in `dom(g) ∩ dom(∂ω)` and the next iterate
`x^(k+1)` satisfies the canonical Algorithm 10.67 one-step predicate. -/
def is_non_euclidean_proximal_gradient_trajectory
    (f g ω : E → EReal) (x : ℕ → E) (L : ℕ → PosReal) : Prop :=
  ∀ k : ℕ,
    x k ∈ effective_domain g ∩ subdifferential_domain ω ∧
      non_euclidean_proximal_gradient_step f g ω (x k) (L k) (x (k + 1))

/-- Along a non-Euclidean proximal-gradient trajectory, the next iterate `x^(k+1)` satisfies the
canonical Algorithm 10.67 one-step predicate. -/
theorem is_non_euclidean_proximal_gradient_trajectory_step
    {f g ω : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}
    (h : is_non_euclidean_proximal_gradient_trajectory f g ω x L) (k : ℕ) :
    x k ∈ effective_domain g ∩ subdifferential_domain ω ∧
      non_euclidean_proximal_gradient_step f g ω (x k) (L k) (x (k + 1)) :=
  h k

/-- Along a non-Euclidean proximal-gradient trajectory, `f` is differentiable at every iterate
`x^k` in the Chapter 3 sense. -/
theorem is_non_euclidean_proximal_gradient_trajectory_differentiable_at
    {f g ω : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}
    (h : is_non_euclidean_proximal_gradient_trajectory f g ω x L) (k : ℕ) :
    is_differentiable_at f (x k) :=
  (is_non_euclidean_proximal_gradient_trajectory_step h k).2.differentiable_at

/-- Along a non-Euclidean proximal-gradient trajectory, every iterate `x^k` lies in
`dom(g) ∩ dom(∂ω)`. -/
theorem is_non_euclidean_proximal_gradient_trajectory_mem_domains
    {f g ω : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}
    (h : is_non_euclidean_proximal_gradient_trajectory f g ω x L) (k : ℕ) :
    x k ∈ effective_domain g ∩ subdifferential_domain ω :=
  (is_non_euclidean_proximal_gradient_trajectory_step h k).1

/-- Along a non-Euclidean proximal-gradient trajectory, the next iterate `x^(k+1)` satisfies the
canonical Algorithm 10.67 one-step predicate. -/
theorem is_non_euclidean_proximal_gradient_trajectory_mem_step
    {f g ω : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}
    (h : is_non_euclidean_proximal_gradient_trajectory f g ω x L) (k : ℕ) :
    non_euclidean_proximal_gradient_step f g ω (x k) (L k) (x (k + 1)) :=
  (is_non_euclidean_proximal_gradient_trajectory_step h k).2

/-- Along a non-Euclidean proximal-gradient trajectory, the next iterate `x^(k+1)` globally
minimizes the specialized Mirror-C update objective at step `k` on `finite_domain ω`. -/
theorem is_non_euclidean_proximal_gradient_trajectory_isMinOn
    {f g ω : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}
    (h : is_non_euclidean_proximal_gradient_trajectory f g ω x L) (k : ℕ) :
    IsMinOn
      (mirror_c_update_objective g ω (x k)
        (fderiv ℝ (fun y ↦ (f y).toReal) (x k)) ((L k : ℝ)⁻¹))
      (finite_domain ω) (x (k + 1)) :=
  (is_non_euclidean_proximal_gradient_trajectory_mem_step h k).isMinOn

end
