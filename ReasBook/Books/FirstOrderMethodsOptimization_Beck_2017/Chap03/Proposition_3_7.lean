/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 3.7 is a `bridge/view` item in the chapter convex-analysis API: its source-facing
codomain is the owner set `subdifferential_domain`, and the proof is obtained pointwise from
`subdifferential_nonempty_at_relativeInterior_point`. Since the relative-interior hypothesis is
already vacuous when `effective_domain f` is empty and convexity itself handles any `⊥` values at
relative-interior points, this bridge theorem needs only the owner convexity hypothesis. -/
recall effective_domain
recall is_convex_function
recall intrinsicInterior
recall subdifferential_domain
recall subdifferential_nonempty_at_relativeInterior_point

-- Proof sketch: apply the owner theorem pointwise to each
-- `x ∈ intrinsicInterior ℝ (effective_domain f)`.
/-- Proposition 3.7: for a convex extended-real-valued function, the relative interior of `dom(f)`
is contained in the domain of the subdifferential. -/
theorem relativeInterior_effective_domain_subset_subdifferential_domain
    (f : E → EReal) (hconv : is_convex_function f) :
    intrinsicInterior ℝ (effective_domain f) ⊆ subdifferential_domain f :=
  fun _ hx ↦ subdifferential_nonempty_at_relativeInterior_point f _ hconv hx

end
