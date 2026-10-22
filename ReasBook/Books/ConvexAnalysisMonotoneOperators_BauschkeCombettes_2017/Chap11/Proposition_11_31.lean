/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_8

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

namespace Set

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A set `C` is uniformly convex when it admits a monotone modulus, vanishing only at `0`, such
that for any two points of `C`, the closed ball centered at their midpoint with radius determined
by the distance between them is still contained in `C`. -/
def UniformlyConvex (C : Set H) : Prop :=
  ∃ φ : NNReal → NNReal,
    Monotone φ ∧
    (∀ r : NNReal, φ r = 0 ↔ r = 0) ∧
    ∀ ⦃x y : H⦄, x ∈ C → y ∈ C →
      Metric.closedBall (midpoint ℝ x y) (φ ‖x - y‖₊) ⊆ C

/-- The midpoint of two points of a uniformly convex set remains in the set. -/
theorem UniformlyConvex.midpoint_mem {C : Set H} (hC : UniformlyConvex C) {x y : H}
    (hx : x ∈ C) (hy : y ∈ C) :
    midpoint ℝ x y ∈ C := by
  rcases hC with ⟨φ, _, _, hφ⟩
  exact hφ hx hy <|
    Metric.mem_closedBall_self
      (show 0 ≤ ((φ ‖x - y‖₊ : NNReal) : ℝ) from (φ ‖x - y‖₊).2)

/-- Distinct points of a uniformly convex set have midpoint in the interior. This is the atomic
bridge from the source-facing midpoint-ball condition to the canonical convexity API. -/
theorem UniformlyConvex.midpoint_mem_interior {C : Set H} (hC : UniformlyConvex C) {x y : H}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    midpoint ℝ x y ∈ interior C := by
  rcases hC with ⟨φ, _, hφ_zero, hφ⟩
  rw [mem_interior_iff_mem_nhds]
  have hφ_pos : 0 < φ ‖x - y‖₊ := by
    refine pos_iff_ne_zero.mpr fun hφr ↦ ?_
    exact hxy <| sub_eq_zero.mp <| by
      rw [← nnnorm_eq_zero, ← (hφ_zero _).mp hφr]
  refine mem_of_superset (Metric.ball_mem_nhds _ (by exact_mod_cast hφ_pos)) ?_
  intro z hz
  exact hφ hx hy (Metric.ball_subset_closedBall hz)

/-- A closed uniformly convex set is convex. -/
theorem UniformlyConvex.convex_of_isClosed {C : Set H} (hC : UniformlyConvex C)
    (hC_closed : IsClosed C) :
    Convex ℝ C := sorry

/-- A closed uniformly convex set is strictly convex. -/
theorem UniformlyConvex.strictConvex_of_isClosed {C : Set H} (hC : UniformlyConvex C)
    (hC_closed : IsClosed C) :
    StrictConvex ℝ C := sorry

end

end Set

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem mem_constraint_inter_effectiveDomain_of_add_indicator
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {xₙ : ℕ → H}
    (hxₙ : IsMinimizingSequence (f.asEReal + (ι[C]).asEReal) xₙ) (n : ℕ) :
    xₙ n ∈ C ∩ effectiveDomain f := by
  have hxdom : xₙ n ∈ dom (f.asEReal + (ι[C]).asEReal) := hxₙ.mem_dom n
  rw [mem_dom_iff_ne_top] at hxdom
  by_cases hxC : xₙ n ∈ C
  · refine ⟨hxC, ?_⟩
    rw [mem_effectiveDomain_iff, lt_top_iff_ne_top]
    simpa [hxC] using hxdom
  · have hbot : (f (xₙ n) : EReal) ≠ ⊥ := ne_of_gt (f (xₙ n)).2
    exact (hxdom (by simp [hxC, hbot])).elim

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem nonempty_constraint_inter_effectiveDomain_of_add_indicator
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {xₙ : ℕ → H}
    (hxₙ : IsMinimizingSequence (f.asEReal + (ι[C]).asEReal) xₙ) :
    (C ∩ effectiveDomain f).Nonempty :=
  ⟨xₙ 0, mem_constraint_inter_effectiveDomain_of_add_indicator hxₙ 0⟩

-- Proof sketch: Proposition 11.15 gives existence of a minimizer on the bounded closed convex set
-- `C`, with convexity coming from the midpoint-ball uniform convexity hypothesis and feasibility
-- coming from the minimizing sequence itself. Proposition 11.8 upgrades the disjointness from
-- `Argmin f` and the induced strict convexity to uniqueness over `C`. Proposition 11.29 yields
-- weak convergence of the minimizing sequence to that unique minimizer, and the midpoint-ball
-- modulus then upgrades weak convergence to norm convergence.
/-- Proposition 11.31: if `f ∈ Γ₀(H)`, `C` is bounded, closed, disjoint from `Argmin f`, and
uniformly convex in the source-facing midpoint-ball sense (11.13), then every minimizing sequence
of `f + ι_C` converges strongly to the unique minimizer of `f` over `C`. -/
theorem existsUnique_mem_argminOn_and_tendsto_of_isMinimizingSequence_add_indicator
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {C : Set H}
    (hC_bounded : Bornology.IsBounded C) (hC_closed : IsClosed C)
    (hC_disjoint : Disjoint C (Argmin f.asEReal))
    (hC_uniformlyConvex : Set.UniformlyConvex C) {xₙ : ℕ → H}
    (hxₙ : IsMinimizingSequence (f.asEReal + (ι[C]).asEReal) xₙ) :
    ∃! x : H, x ∈ Argmin[C] f.asEReal ∧ Tendsto xₙ atTop (𝓝 x) := sorry

end ERealFunction
