/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open scoped ConvexAnalysis SupportFunction

/- Theorem 3.17 lies in the chapter's support-function comparison domain.

Primary domain:
- support functions of closed convex subsets of a real Hilbert space.

Relevant sampled owner declarations:
- `supportFunction` in `Definition_3_9`, the chapter owner for `ξ[Q]`;
- `extendedRealEffectiveDomain` / `dom` in `Definition_3_1_1_2`, the owner of the finite-value
  domain of an `EReal`-valued function;
- `supportFunction_apply` in `Definition_3_9`, the evaluation bridge for `ξ[Q]`;
- mathlib `geometric_hahn_banach_closed_point`, the strict point-versus-closed-convex separation
  theorem whose dual functional is converted to a vector normal by Riesz representation.

Best owner abstraction:
- the pair `ξ[Q]` and `dom ξ[Q]`.

Primitive data:
- the sets `Q₁`, `Q₂`.

Derived API:
- the support-function comparison theorem `subset_of_supportFunction_le_on_domain`;
- the equality criterion `supportFunction_eq_on_common_domain_implies_eq`.

Source/core/bridge triage:
- source-facing: the textbook comparison and equality criteria for closed convex sets via support
  functions;
- core/canonical: the owner constructions `supportFunction` and `dom`;
- bridge/view: these two theorems, which express the source comparison statements directly in that
  owner language instead of introducing a parallel local wrapper.

The textbook states these results on `ℝⁿ`. The comparison theorems themselves still live directly
on the owner pair `ξ[Q]`, `dom ξ[Q]`, but their intrinsic ambient layer is a real Hilbert space:
the proof needs a separating continuous linear functional to be represented by a vector normal in
the same space. This completeness requirement is therefore mathematical owner data here, not mere
proof scaffolding. -/

/-- Theorem 3.17 (1): if `Q₂` is a nonempty closed convex subset of a real Hilbert space and
the support function of `Q₁` is bounded above by that of `Q₂` at every vector in `dom ξ[Q₂]`,
then `Q₁ ⊆ Q₂`. -/
-- Proof sketch: if `Q₁ = ∅`, the conclusion is immediate. Otherwise argue by contradiction. For
-- `x₀ ∈ Q₁ \\ Q₂`, use the separation theorem for the point `x₀` and the nonempty closed convex
-- set `Q₂` to produce a vector `g` with `supportFunction Q₂ g` finite and
-- `supportFunction Q₂ g < supportFunction Q₁ g`, contradicting the assumed pointwise inequality
-- on `dom ξ[Q₂]`.
theorem subset_of_supportFunction_le_on_domain
    (Q₁ Q₂ : Set E) (hQ₂_nonempty : Q₂.Nonempty)
    (hQ₂_closed : IsClosed Q₂) (hQ₂_convex : Convex ℝ Q₂)
    (hξ : ∀ g ∈ dom ξ[Q₂], ξ[Q₁] g ≤ ξ[Q₂] g) :
    Q₁ ⊆ Q₂ := by
  intro x hxQ₁
  by_contra hxQ₂
  obtain ⟨f, u, hQ₂_lt, hux⟩ :=
    geometric_hahn_banach_closed_point hQ₂_convex hQ₂_closed hxQ₂
  let g : E := (InnerProductSpace.toDual ℝ E).symm f
  have hQ₂_lt' : ∀ y ∈ Q₂, inner ℝ y g < u := by
    intro y hy
    have : inner ℝ g y < u := by
      simpa [g] using hQ₂_lt y hy
    simpa [real_inner_comm] using this
  have hux' : u < inner ℝ x g := by
    have : u < inner ℝ g x := by
      simpa [g] using hux
    simpa [real_inner_comm] using this
  have hξQ₂_le : ξ[Q₂] g ≤ (u : EReal) := by
    rw [supportFunction_apply]
    refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    change ((inner ℝ y g : ℝ) : EReal) ≤ (u : EReal)
    exact_mod_cast (hQ₂_lt' y hy).le
  have hg_dom : g ∈ dom ξ[Q₂] := by
    rw [mem_extendedRealEffectiveDomain_iff]
    constructor
    · exact ne_top_of_le_ne_top (EReal.coe_ne_top u) hξQ₂_le
    · intro hbot
      rcases hQ₂_nonempty with ⟨y, hy⟩
      have hy_le : ((inner ℝ y g : ℝ) : EReal) ≤ ξ[Q₂] g := by
        rw [supportFunction_apply]
        exact le_sSup ⟨y, hy, rfl⟩
      have hy_le_bot : ((inner ℝ y g : ℝ) : EReal) ≤ (⊥ : EReal) := by
        rw [hbot] at hy_le
        exact hy_le
      exact (not_le_of_gt (EReal.bot_lt_coe _)) hy_le_bot
  have hu_lt : (u : EReal) < ξ[Q₁] g := by
    have hx_le : ((inner ℝ x g : ℝ) : EReal) ≤ ξ[Q₁] g := by
      rw [supportFunction_apply]
      exact le_sSup ⟨x, hxQ₁, rfl⟩
    have huxE : (u : EReal) < ((inner ℝ x g : ℝ) : EReal) := by
      exact_mod_cast hux'
    exact huxE.trans_le hx_le
  exact (not_le_of_gt hu_lt) ((hξ g hg_dom).trans hξQ₂_le)

/-- Theorem 3.17 (2): if two closed convex sets in a real Hilbert space have the same
effective domain for their support functions and those support functions agree on that common
domain, then the sets are equal. -/
-- Proof sketch: equality of effective domains rules out the mixed empty/nonempty case for `Q₁`
-- and `Q₂`. If both sets are empty, the conclusion is immediate. Otherwise the common domain is
-- nonempty, so both sets are nonempty; apply `subset_of_supportFunction_le_on_domain` in both
-- directions. The domain equality transports the equality hypothesis from one set to the other,
-- giving both inclusions and hence equality.
theorem supportFunction_eq_on_common_domain_implies_eq
    (Q₁ Q₂ : Set E) (hQ₁_closed : IsClosed Q₁) (hQ₂_closed : IsClosed Q₂)
    (hQ₁_convex : Convex ℝ Q₁) (hQ₂_convex : Convex ℝ Q₂)
    (hdom : dom ξ[Q₁] = dom ξ[Q₂])
    (hξ : Set.EqOn ξ[Q₁] ξ[Q₂] (dom ξ[Q₁])) :
    Q₁ = Q₂ := by
  have hdom_empty : dom ξ[(∅ : Set E)] = (∅ : Set E) := by
    ext g
    rw [mem_extendedRealEffectiveDomain_iff, supportFunction_apply]
    simp
  by_cases hQ₁_nonempty : Q₁.Nonempty
  · have hQ₂_nonempty : Q₂.Nonempty := by
      by_contra hQ₂_nonempty
      have hQ₂_empty : Q₂ = ∅ := Set.not_nonempty_iff_eq_empty.mp hQ₂_nonempty
      have hzero_mem : (0 : E) ∈ dom ξ[Q₁] := by
        rw [mem_extendedRealEffectiveDomain_iff, supportFunction_apply]
        constructor <;> simp [hQ₁_nonempty]
      have : (0 : E) ∈ dom ξ[Q₂] := by
        simpa [hdom] using hzero_mem
      simp [hQ₂_empty] at this
    apply Set.Subset.antisymm
    · exact
        subset_of_supportFunction_le_on_domain Q₁ Q₂ hQ₂_nonempty hQ₂_closed hQ₂_convex
          fun g hg ↦ by
            have hg' : g ∈ dom ξ[Q₁] := by
              simpa [hdom] using hg
            exact (hξ hg').le
    · exact
        subset_of_supportFunction_le_on_domain Q₂ Q₁ hQ₁_nonempty hQ₁_closed hQ₁_convex
          fun g hg ↦ (hξ hg).symm.le
  · have hQ₁_empty : Q₁ = ∅ := Set.not_nonempty_iff_eq_empty.mp hQ₁_nonempty
    have hQ₂_empty : Q₂ = ∅ := by
      by_cases hQ₂_nonempty : Q₂.Nonempty
      · have hdomQ₂_empty : dom ξ[Q₂] = (∅ : Set E) := by
          calc
            dom ξ[Q₂] = dom ξ[Q₁] := hdom.symm
            _ = dom ξ[(∅ : Set E)] := by simp [hQ₁_empty]
            _ = ∅ := hdom_empty
        have hzero_mem : (0 : E) ∈ dom ξ[Q₂] := by
          rw [mem_extendedRealEffectiveDomain_iff, supportFunction_apply]
          constructor <;> simp [hQ₂_nonempty]
        simp [hdomQ₂_empty] at hzero_mem
      · exact Set.not_nonempty_iff_eq_empty.mp hQ₂_nonempty
    simp [hQ₁_empty, hQ₂_empty]

end
