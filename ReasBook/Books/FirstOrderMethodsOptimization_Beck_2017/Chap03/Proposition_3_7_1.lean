/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 3.7.1 is a `bridge/view` item in the chapter convex-analysis API. The owner notions
`effective_domain`, `IsProperExtendedRealFunction`, `is_convex_function`, and
`subdifferential_domain` already live upstream; the chapter-level bridge theorem is
`relativeInterior_effective_domain_subset_subdifferential_domain`. This file combines that owner
theorem with the canonical convex-geometry nonemptiness theorem for `intrinsicInterior ℝ`. The
owner-level result therefore uses only the primitive data needed for the argument: convexity of
`f` and nonemptiness of `effective_domain f`. The textbook proper-convex formulation is kept only
as a thin source-facing corollary, since properness contributes here solely through
`hf.effective_domain_nonempty`. -/
recall effective_domain
recall IsProperExtendedRealFunction
recall is_convex_function
recall intrinsicInterior
recall subdifferential_domain
recall mem_subdifferential_domain
recall intrinsicInterior_nonempty
recall subdifferential_domain_subset_effective_domain

-- Proof sketch: `effective_domain f` is convex because `f` is convex, and it is nonempty by
-- hypothesis. Hence mathlib's owner theorem `intrinsicInterior_nonempty` gives nonemptiness of
-- `intrinsicInterior ℝ (effective_domain f)`, and Proposition 3.7 pushes that set into
-- `subdifferential_domain f`.
/-- Owner-level bridge: a convex extended-real-valued function with nonempty effective domain has
nonempty subdifferential domain. -/
theorem subdifferential_domain_nonempty_of_convex_of_effective_domain_nonempty
    (f : E → EReal) (hconv : is_convex_function f) (hdom : (effective_domain f).Nonempty) :
    (subdifferential_domain f).Nonempty := by
  exact
    ((intrinsicInterior_nonempty (effective_domain_convex_of_is_convex_function hconv)).2
      hdom).mono
      (relativeInterior_effective_domain_subset_subdifferential_domain f hconv)

/-- Proposition 3.7.1: any proper convex extended-real-valued function has a point where the
subdifferential is nonempty. Equivalently, `dom(∂ f)` is nonempty. -/
theorem subdifferential_domain_nonempty_of_proper_convex
    (f : E → EReal) (hf : IsProperExtendedRealFunction f) (hconv : is_convex_function f) :
    (subdifferential_domain f).Nonempty :=
  subdifferential_domain_nonempty_of_convex_of_effective_domain_nonempty f hconv
    hf.effective_domain_nonempty

-- Proof sketch: extract `x ∈ subdifferential_domain f` from the owner theorem, rewrite it as
-- `(subdifferential f x).Nonempty`, and recover `x ∈ effective_domain f` because the
-- subdifferential is empty off the effective domain.
/-- Owner-level companion: a convex extended-real-valued function with nonempty effective domain
has a point of its effective domain where the subdifferential is nonempty. -/
theorem exists_subdifferentiable_point_in_effective_domain_of_convex_of_effective_domain_nonempty
    (f : E → EReal) (hconv : is_convex_function f) (hdom : (effective_domain f).Nonempty) :
    ∃ x ∈ effective_domain f, (subdifferential f x).Nonempty := by
  rcases subdifferential_domain_nonempty_of_convex_of_effective_domain_nonempty f hconv hdom with
      ⟨x, hx⟩
  refine ⟨x, subdifferential_domain_subset_effective_domain hx, ?_⟩
  exact (mem_subdifferential_domain).1 hx

/-- Source-facing corollary: any proper convex extended-real-valued function has a point of its
effective domain where the subdifferential is nonempty. -/
theorem exists_subdifferentiable_point_in_effective_domain_of_proper_convex
    (f : E → EReal) (hf : IsProperExtendedRealFunction f) (hconv : is_convex_function f) :
    ∃ x ∈ effective_domain f, (subdifferential f x).Nonempty :=
  exists_subdifferentiable_point_in_effective_domain_of_convex_of_effective_domain_nonempty f
    hconv hf.effective_domain_nonempty

end
