/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_5
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_27
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Metric
open Bornology

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper for Theorem 8.1: compactness of `C` gives one closed ball that contains the union of all
continuous-dual subdifferentials over `C`. -/
lemma subgradient_biUnion_subset_closedBall_of_isCompact
    (f : E → EReal) (C : Set E) (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f) (hC_compact : IsCompact C)
    (hC_subset : C ⊆ interior (effective_domain f)) :
    ∃ R : ℝ,
      (⋃ x ∈ C, strongDualSubdifferential f x) ⊆ closedBall (0 : StrongDual ℝ E) R := by
  -- Apply the Chapter 3 compact-union theorem to the global subdifferential union.
  have hYbounded :=
    subdifferential_biUnion_isBounded_of_isCompact_subset_interior
      (f := f) (X := C) (fun x _ ↦ hf_proper.ne_bot x) hf_convex hC_compact hC_subset
  -- Convert boundedness into containment in a single closed ball.
  exact hYbounded.subset_closedBall (0 : StrongDual ℝ E)

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 8.1: a closed-ball bound on the union of subdifferentials yields the
pointwise norm estimate needed for the Chapter 8 packaged hypothesis. -/
lemma norm_le_of_mem_subgradient_biUnion_closedBall
    (f : E → EReal) (C : Set E) {R : ℝ}
    (hR : (⋃ x ∈ C, strongDualSubdifferential f x) ⊆ closedBall (0 : StrongDual ℝ E) R) :
    ∀ ⦃x : E⦄ ⦃g : StrongDual ℝ E⦄,
      x ∈ C → g ∈ strongDualSubdifferential f x → ‖g‖ ≤ max R 1 := by
  intro x g hx hg
  have hg_union : g ∈ ⋃ x ∈ C, strongDualSubdifferential f x := by
    -- Place `g` into the global union using its base point `x ∈ C`.
    simp only [Set.mem_iUnion]
    exact ⟨x, hx, hg⟩
  have hg_ball : g ∈ closedBall (0 : StrongDual ℝ E) R := hR hg_union
  have hnorm : ‖g‖ ≤ R := by
    -- Read closed-ball membership back as a norm bound at the origin.
    simpa [mem_closedBall_iff_norm''] using hg_ball
  exact hnorm.trans (le_max_left R 1)

/- Theorem 8.1 is a `bridge/view` item. Its first clause is the Chapter 8 specialization of the
canonical Chapter 3 owner theorem `lipschitzOnWith_toReal_of_subdifferential_norm_le_on`, with the
bounded-subgradient hypothesis packaged by `SubgradientNormBoundOn`. Its compactness clause is the
converse existence bridge from the compact-union boundedness theorem of Chapter 3 back to the
Chapter 8 assumption package. -/

-- Proof sketch: apply `lipschitzOnWith_toReal_of_subdifferential_norm_le_on` to `f` and `C`.
-- The properness hypothesis supplies the no-`⊥` condition on the effective domain, the convexity
-- hypothesis is exactly the owner convexity assumption, and `hbound` is already the pointwise
-- subgradient norm estimate required by Theorem 3.27.
/-- Theorem 8.1: if a proper convex extended-real-valued function has uniformly bounded
subgradients on a set `C` contained in `interior (effective_domain f)`, then `x ↦ (f x).toReal`
is Lipschitz on `C` with Lipschitz constant `L_f`. -/
theorem lipschitzOnWith_toReal_of_subgradientNormBoundOn
    (f : E → EReal) (C : Set E) (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f)
    (hC_subset : C ⊆ interior (effective_domain f))
    (hbound : SubgradientNormBoundOn f C) :
    LipschitzOnWith (Real.toNNReal hbound.L_f) (fun x ↦ (f x).toReal) C := by
  -- Keep the textbook hypotheses visible in this Chapter 8 bridge theorem.
  let _ := hf_proper
  let _ := hf_convex
  -- Specialize the Chapter 3 owner theorem with the packaged Chapter 8 norm bound.
  refine lipschitzOnWith_toReal_of_subdifferential_norm_le_on
      f C (Real.toNNReal hbound.L_f) (fun x _ ↦ hf_proper.ne_bot x) hf_convex hC_subset ?_
  intro x g hx hg
  simpa [Real.toNNReal_of_nonneg hbound.L_f_pos.le] using hbound.norm_le hx hg

-- Proof sketch: apply
-- `subdifferential_biUnion_isBounded_of_isCompact_subset_interior` to the compact
-- feasible set `C`. Use the resulting boundedness of `⋃ x ∈ C, strongDualSubdifferential f x` to
-- obtain a common radius controlling all subgradients over `C`, and then enlarge that radius if
-- necessary so the final bound constant is strictly positive.
/-- A compact set contained in `interior (effective_domain f)` admits a uniform positive bound on
the norms of all subgradients of a proper convex extended-real-valued function. -/
theorem exists_pos_subgradient_norm_bound_of_isCompact_subset_interior
    (f : E → EReal) (C : Set E) (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f) (hC_compact : IsCompact C)
    (hC_subset : C ⊆ interior (effective_domain f)) :
    ∃ L_f : ℝ, 0 < L_f ∧
      ∀ ⦃x : E⦄ ⦃g : StrongDual ℝ E⦄,
        x ∈ C → g ∈ strongDualSubdifferential f x → ‖g‖ ≤ L_f := by
  -- First control the global union of subdifferentials over the compact feasible set.
  rcases subgradient_biUnion_subset_closedBall_of_isCompact
      f C hf_proper hf_convex hC_compact hC_subset with ⟨R, hR⟩
  refine ⟨max R 1, ?_, ?_⟩
  · -- Enlarge the radius to `max R 1` so the final bound is automatically strictly positive.
    exact lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  · -- Convert the global closed-ball control back into the desired pointwise norm estimate.
    exact norm_le_of_mem_subgradient_biUnion_closedBall f C hR

end
