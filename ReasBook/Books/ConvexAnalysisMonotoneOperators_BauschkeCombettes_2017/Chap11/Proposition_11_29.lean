/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Corollary_3_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_21

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section CompleteSpace

variable [CompleteSpace H]

-- Proof sketch: `hxₙ.tendsto` makes the minimizing sequence eventually enter every lower level set
-- strictly above `sInf (Set.range f)`. Once the tail lies in the bounded set `lowerLevelSet f ξ`,
-- put that set inside a closed ball and apply
-- `exists_subsequence_tendsto_weakly_mem_of_bounded_isClosed_convex` to obtain a weakly
-- convergent subsequence, hence a weak sequential cluster point.
/-- Proposition 11.29 (1): clause (i). If some lower level set strictly above the infimum of `f`
is bounded, then every minimizing sequence of `f` has a weak sequential cluster point. -/
theorem IsMinimizingSequence.exists_weakSequentialClusterPoint_of_bounded_lowerLevelSet
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hlevel_bounded : Bornology.IsBounded (lowerLevelSet f ξ)) :
    ∃ x : H,
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x) := sorry

end CompleteSpace

-- Proof sketch: `hx.exists_subseq_tendsto` supplies a weakly convergent subsequence. A
-- subsequence of a minimizing sequence is still minimizing, so
-- `mem_argmin_of_isMinimizingSequence_of_tendsto_weakly_of_quasiconvexOn_univ` from Proposition
-- 11.21 applies to that subsequence.
/-- Proposition 11.29 (2): clause (i). Every weak sequential cluster point of a minimizing
sequence of a lower semicontinuous quasiconvex function is a global minimizer. -/
theorem IsSequentialClusterPt.mem_argmin_of_isMinimizingSequence_of_quasiconvexOn_univ
    {f : H → EReal} {xₙ : ℕ → H} {x : H}
    (hx : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x))
    (hf_quasi : QuasiconvexOn ℝ Set.univ f) (hf_lsc : LowerSemicontinuous f)
    (hxₙ : IsMinimizingSequence f xₙ) :
    x ∈ Argmin f := sorry

section CompleteSpace

variable [CompleteSpace H]

-- Proof sketch: choose an arbitrary minimizing sequence of `f`. Part (1) supplies a weak
-- sequential cluster point. Apply Proposition 11.21 to the indicator-augmented objective
-- `f + (ι[lowerLevelSet f ξ]).asEReal`, whose strict quasiconvexity already gives the needed
-- quasiconvexity, and then use that this objective agrees with `f` on `lowerLevelSet f ξ`.
-- Uniqueness comes from `argminOn_subsingleton_of_indicator_strictlyQuasiconvex`.
/-- Proposition 11.29 (3): clause (ii). If `f + ι_C` is strictly quasiconvex for
`C = lowerLevelSet f ξ`, then `f` has a unique global minimizer. -/
theorem existsUnique_mem_argmin_of_strictlyQuasiconvex_indicator_lowerLevelSet
    {f : H → EReal} (hf_lsc : LowerSemicontinuous f) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hlevel_bounded : Bornology.IsBounded (lowerLevelSet f ξ))
    (hstrict : StrictlyQuasiconvex (f + (ι[lowerLevelSet f ξ]).asEReal)) :
    ∃! x : H, x ∈ Argmin f := sorry

-- Proof sketch: part (1) yields boundedness of the weak-image sequence through a weakly
-- convergent subsequence, and Proposition 11.21 applied to
-- `f + (ι[lowerLevelSet f ξ]).asEReal` shows that
-- every weak sequential cluster point is a minimizer. Part (3) makes that minimizer unique, so
-- `weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint` upgrades the bounded
-- sequence to weak convergence of the whole minimizing sequence.
/-- Proposition 11.29 (4): clause (ii). Under the same strict quasiconvexity hypothesis, the
minimizing sequence converges weakly to a global minimizer of `f`. -/
theorem IsMinimizingSequence.exists_mem_argmin_and_tendsto_toWeakSpace_of_strictlyQuasiconvex_indicator_lowerLevelSet
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ)
    (hf_lsc : LowerSemicontinuous f) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hlevel_bounded : Bornology.IsBounded (lowerLevelSet f ξ))
    (hstrict : StrictlyQuasiconvex (f + (ι[lowerLevelSet f ξ]).asEReal)) :
    ∃ x ∈ Argmin f,
      Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x)) := sorry

-- Proof sketch: choose an arbitrary minimizing sequence of `f`. Uniform quasiconvexity of
-- `f + (ι[lowerLevelSet f ξ]).asEReal` already provides the relevant quasiconvexity and the same
-- uniqueness mechanism as in clause (ii), while part (1) and Proposition 11.21 again provide
-- existence of a minimizer through weak sequential cluster points.
/-- Proposition 11.29 (5): clause (iii). If `f + ι_C` is uniformly quasiconvex for
`C = lowerLevelSet f ξ`, then `f` has a unique global minimizer. -/
theorem existsUnique_mem_argmin_of_uniformlyQuasiconvex_indicator_lowerLevelSet
    {f : H → EReal} (hf_lsc : LowerSemicontinuous f) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hlevel_bounded : Bornology.IsBounded (lowerLevelSet f ξ))
    {φ : NNReal → EReal}
    (huniform : UniformlyQuasiconvex (f + (ι[lowerLevelSet f ξ]).asEReal) φ) :
    ∃! x : H, x ∈ Argmin f := sorry

-- Proof sketch: after clause (iii) gives uniqueness of the minimizer, the uniform quasiconvexity
-- inequality for `f + ι_{lev≤ξ f}` controls `φ ‖xₙ - x‖₊` by `f (xₙ) - f x`; since the right-hand
-- side tends to `0` along the minimizing sequence, the modulus forces `‖xₙ - x‖ → 0`.
/-- Proposition 11.29 (6): clause (iii). Under the same uniform quasiconvexity hypothesis, the
minimizing sequence converges strongly to a global minimizer of `f`. -/
theorem IsMinimizingSequence.exists_mem_argmin_and_tendsto_of_uniformlyQuasiconvex_indicator_lowerLevelSet
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ)
    (hf_lsc : LowerSemicontinuous f) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hlevel_bounded : Bornology.IsBounded (lowerLevelSet f ξ))
    {φ : NNReal → EReal}
    (huniform : UniformlyQuasiconvex (f + (ι[lowerLevelSet f ξ]).asEReal) φ) :
    ∃ x ∈ Argmin f, Tendsto xₙ atTop (𝓝 x) := sorry

end CompleteSpace

end ERealFunction
