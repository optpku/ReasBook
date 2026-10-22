/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {f : E → EReal}

/- Lemma 3.1 is a `bridge/view` item in the chapter convex-analysis API: the owner theorem is
`is_convex_function_of_subdifferentiable_on_convex_effective_domain`, whose owner hypothesis is the
inclusion `effective_domain f ⊆ subdifferential_domain f`. This file keeps the source wording
"there exists a subgradient" and rewrites it through the owner set `subdifferential f x`,
equivalently membership in the owner domain `subdifferential_domain f`. -/
recall effective_domain
recall is_convex_function
recall subdifferential
recall subdifferential_domain
recall mem_subdifferential_domain
recall is_convex_function_of_subdifferentiable_on_convex_effective_domain

-- Proof sketch: to prove convexity, fix `x, y ∈ effective_domain f` and `t ∈ [0, 1]`, and set
-- `z = t • x + (1 - t) • y`. The convexity hypothesis on `effective_domain f` gives
-- `z ∈ effective_domain f`, so `hsubgrad` yields some `g ∈ subdifferential f z`, hence
-- `z ∈ subdifferential_domain f`. Applying the resulting subgradient inequality first with `y` and
-- then with `x`, and combining the two inequalities with weights `t` and `1 - t`, gives the
-- Jensen inequality along the segment from `x` to `y`, hence `f` is convex.
/-- Lemma 3.1: if an extended-real-valued function has convex effective domain and admits a
subgradient at every point of its effective domain, then the function is convex. -/
lemma is_convex_function_of_subgradient_exists_on_effective_domain
    (hdom : Convex ℝ (effective_domain f))
    (hsubgrad : ∀ x ∈ effective_domain f, ∃ g : Module.Dual ℝ E, g ∈ subdifferential f x) :
    is_convex_function f :=
  is_convex_function_of_subdifferentiable_on_convex_effective_domain hdom
    (fun x hx ↦ by
      rw [mem_subdifferential_domain]
      simpa [Set.nonempty_def] using hsubgrad x hx)

end
