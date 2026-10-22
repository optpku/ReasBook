/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Corollary 3.29 is a `bridge/view` compactness upgrade in the chapter convex-analysis API. Its
owner abstractions are already Chapter 2's `effective_domain`, `is_convex_function`, and the
canonical real-valued owner `ConvexOn ℝ (effective_domain f) (fun x ↦ (f x).toReal)`. The
compact-set conclusion is derived from mathlib's owner-level local-Lipschitz API on the interior
of a convex domain and the standard compactness upgrade from `LocallyLipschitzOn` to
`LipschitzOnWith`.
-/
recall effective_domain
recall is_convex_function
recall convexOn_toReal_of_is_convex_function
recall ConvexOn.locallyLipschitzOn_interior
recall LocallyLipschitzOn.exists_lipschitzOnWith_of_compact

-- Proof sketch: transfer convexity of `f : E → EReal` to the canonical real-valued owner
-- `ConvexOn ℝ (effective_domain f) (fun x ↦ (f x).toReal)` using the no-`⊥` hypothesis on the
-- effective domain. Mathlib then gives local Lipschitz continuity on
-- `interior (effective_domain f)`, and compactness of `X` upgrades this to one global Lipschitz
-- constant on `X`. If the compactness lemma returns `L = 0`, replace it by `L + 1` to match the
-- strictly positive constant in the textbook phrasing.
/-- Corollary 3.29: if `f` is a convex extended-real-valued function that never takes the value
`-∞` on its effective domain and `X` is a compact subset of `interior (dom(f))`, then the
finite-valued restriction `x ↦ (f x).toReal` is Lipschitz on `X`; equivalently, there exists
`L > 0` such that `|(f x).toReal - (f y).toReal| ≤ L * ‖x - y‖` for all `x, y ∈ X`. -/
theorem convex_function_exists_pos_lipschitzOnWith_toReal_of_isCompact_subset_interior
    {f : E → EReal} (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥)
    (hconvex : is_convex_function f) {X : Set E}
    (hX_compact : IsCompact X) (hX_subset : X ⊆ interior (effective_domain f)) :
    ∃ L : NNReal, 0 < L ∧ LipschitzOnWith L (fun x ↦ (f x).toReal) X := by
  have hloc :
      LocallyLipschitzOn (interior (effective_domain f)) (fun x ↦ (f x).toReal) :=
    (convexOn_toReal_of_is_convex_function hconvex h_ne_bot).locallyLipschitzOn_interior
  obtain ⟨L, hL⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hX_compact (hloc.mono hX_subset)
  have hLpos : (0 : NNReal) < L + 1 :=
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left zero_le)
  refine ⟨L + 1, hLpos, hL.weaken ?_⟩
  · exact le_add_of_nonneg_right zero_le_one

end
