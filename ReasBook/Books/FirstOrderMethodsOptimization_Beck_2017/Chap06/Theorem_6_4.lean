/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Corollary_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u}
variable [NormedAddCommGroup E] [ProperSpace E]

/- Theorem 6.4 is `source-facing` for the Chapter 6 proximal-operator existence theory. Domain
sampling shows that the relevant owner abstractions for this statement already live upstream:

- `IsCoerciveExtendedRealFunction` and `attains_min_on_closed_set_of_coercive` from Chapter 2,
- `proximal_objective` and the set-valued proximal map `prox[f]` from Definition 6.1.

Accordingly, this file should only state the existence theorem for `prox[f] x`; it should not
duplicate local owners for coercivity, minimizer existence, or proximal-set membership. -/

-- Proof sketch: the quadratic penalty `u ↦ (1 / 2) ‖u - x‖²` is continuous, hence closed after
-- coercing to `EReal`. Adding it to the closed function `f` yields a closed proximal objective.
omit [ProperSpace E] in
/-- If `f` is lower semicontinuous, then its proximal objective at `x` is lower semicontinuous. -/
theorem lowerSemicontinuous_proximal_objective
    {f : E → EReal} (hf_closed : LowerSemicontinuous f) (x : E) :
    LowerSemicontinuous (proximal_objective f x) := by
  have hpenalty_closed : LowerSemicontinuous
      (fun u : E ↦ ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal)) :=
    continuous_real_isClosed (by fun_prop)
  simpa only [proximal_objective_apply] using
    hf_closed.add' hpenalty_closed <| fun u ↦
      EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))

-- Proof sketch: fix `x`. The function `proximal_objective f x` is coercive by `hcoercive`, hence
-- proper. It is also lower semicontinuous because `f` is lower semicontinuous and the quadratic
-- penalty `u ↦ (1 / 2) ‖u - x‖²` is continuous. Apply
-- `attains_min_on_closed_set_of_coercive` to `proximal_objective f x` on `Set.univ`; the
-- resulting minimizer belongs to `prox[f] x` by definition.
/-- Theorem 6.4: if `f` is closed and the proximal objective at `x`,
`u ↦ f u + (1 / 2) * ‖u - x‖^2`, is coercive, then the proximal set `prox[f] x` is nonempty. The
ambient assumption `[ProperSpace E]` is the canonical abstraction capturing the finite-dimensional
Euclidean setting used in the text, and the textbook properness hypothesis on `f` is redundant
once this proximal objective is assumed coercive. -/
theorem prox_nonempty_of_closed_and_proximal_objective_coercive
    (f : E → EReal) (hf_closed : LowerSemicontinuous f) (x : E)
    (hcoercive : IsCoerciveExtendedRealFunction (proximal_objective f x)) :
    (prox[f] x).Nonempty := by
  rcases attains_min_on_closed_set_of_coercive (proximal_objective f x)
      (lowerSemicontinuous_proximal_objective hf_closed x) hcoercive isClosed_univ
      (by simpa using hcoercive.effective_domain_nonempty) with ⟨u, -, hu⟩
  refine ⟨u, ?_⟩
  simpa [mem_proximal_mapping_iff] using hu

end
