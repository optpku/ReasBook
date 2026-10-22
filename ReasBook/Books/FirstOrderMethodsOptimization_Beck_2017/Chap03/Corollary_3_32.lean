/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_31

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Corollary 3.32 is a `bridge/view` reformulation in the chapter convex-analysis API. The
`core/canonical` owner theorem is
`isMinOn_iff_exists_subgradient_neg_mem_normal_cone` from Theorem 3.31, and the textbook
feasible-displacement inequality is the owner normal-cone membership criterion `mem_normal_cone`.
This file keeps only the source-facing variational-inequality restatement. -/
recall effective_domain
recall IsProperExtendedRealFunction
recall is_convex_function
recall subdifferential
recall normal_cone
recall mem_normal_cone
recall isMinOn_iff_exists_subgradient_neg_mem_normal_cone
recall isMinOn_iff_exists_subgradient_neg_mem_normal_cone_of_proper

-- Proof sketch: replace the constrained problem by the extended-real objective obtained by adding
-- the indicator of `C`, so minimization on `C` becomes unconstrained minimization on `E`. Under the
-- qualification `ri(dom f) ∩ ri(C) ≠ ∅`, apply the convex subdifferential sum rule together with
-- the identification of the indicator subdifferential with the normal cone. Fermat's criterion for
-- the constrained objective then gives `0 ∈ ∂f(xStar) + N_C(xStar)`, which is equivalent to the
-- existence of a subgradient whose pairing with every feasible displacement `x - xStar` is
-- nonnegative, and the converse runs the same implications in reverse.
/-- Corollary 3.32: for a proper convex extended-real-valued function on a finite-dimensional real
normed space and a convex feasible set `C` satisfying `ri(dom f) ∩ ri(C) ≠ ∅`, a feasible point
`xStar` minimizes `f` on `C` if and only if there exists a subgradient at `xStar` whose pairing
with every feasible displacement `x - xStar` is nonnegative. -/
theorem isMinOn_iff_exists_subgradient_nonneg_on_convex_set
    {f : E → EReal} (hf : IsProperExtendedRealFunction f) (hconv : is_convex_function f)
    {C : Set E} (hC : Convex ℝ C)
    (hri : (intrinsicInterior ℝ (effective_domain f) ∩ intrinsicInterior ℝ C).Nonempty)
    {xStar : E} (hxStar : xStar ∈ C) :
    IsMinOn f C xStar ↔
      ∃ g : Module.Dual ℝ E,
        g ∈ ∂ f(xStar) ∧ ∀ x ∈ C, 0 ≤ g (x - xStar) := by
  rw [isMinOn_iff_exists_subgradient_neg_mem_normal_cone_of_proper
    (f := f) hf hconv hC hri hxStar]
  constructor
  · rintro ⟨g, hg, hgcone⟩
    refine ⟨g, hg, ?_⟩
    simpa using (mem_normal_cone C hxStar (-g)).1 hgcone
  · rintro ⟨g, hg, hgineq⟩
    refine ⟨g, hg, ?_⟩
    exact (mem_normal_cone C hxStar (-g)).2 (by simpa using hgineq)

end
