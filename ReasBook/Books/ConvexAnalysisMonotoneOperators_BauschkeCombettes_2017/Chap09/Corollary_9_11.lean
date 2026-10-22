/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_32
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Theorem_9_9

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

namespace ERealFunction

variable {H : Type u}

-- Proof sketch: this is the pointwise implication `f x < 0 → f x ≤ 0`, rewritten in terms of the
-- strict and closed lower level sets at height `0`.
/-- Corollary 9.11 (1): the strict negative level set of `f` is contained in its nonpositive level
set. -/
theorem strictLowerLevelSet_zero_subset_lowerLevelSet_zero (f : H → EReal) :
    strictLowerLevelSet f 0 ⊆ lowerLevelSet f 0 := by
  intro x hx
  -- Unfolding both level sets turns the claim into the scalar implication `f x < 0 → f x ≤ 0`.
  rw [mem_strictLowerLevelSet_iff] at hx
  rw [mem_lowerLevelSet_iff]
  exact le_of_lt hx

section LowerSemicontinuousHull

variable [TopologicalSpace H]

-- Proof sketch: the lower semicontinuous hull is the greatest lower semicontinuous minorant of
-- `f`, so it lies pointwise below `f`; rewriting that inequality at height `0` gives the subset.
/-- Corollary 9.11 (2): the nonpositive level set of `f` is contained in the nonpositive level set
of its lower semicontinuous hull `\check f`. -/
theorem lowerLevelSet_zero_subset_lowerLevelSet_zero_lowerSemicontinuousHull
    (f : H → EReal) :
    lowerLevelSet f 0 ⊆ lowerLevelSet (lowerSemicontinuousEnvelope f) 0 := by
  intro x hx
  -- The hull is the greatest lower semicontinuous minorant, hence it lies pointwise below `f`.
  rw [mem_lowerLevelSet_iff] at hx ⊢
  exact le_trans ((lowerSemicontinuousHull_isGreatest f).1.2 x) hx

end LowerSemicontinuousHull

section Hilbert

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: use the epigraph description of the lower semicontinuous hull as
-- `closure (epigraph f)`, approximate a point of `lev<₀ \check f` by epigraph points of `f`, and
-- then take convex combinations with a fixed point of `lev<₀ f` to produce nearby points that
-- still lie in `lev<₀ f`.
/-- Corollary 9.11 (3): if `f` has convex epigraph and a nonempty strict negative level set, then
the strict negative level set of its lower semicontinuous hull `\check f` lies in the closure of
the strict negative level set of `f`. -/
theorem strictLowerLevelSet_zero_lowerSemicontinuousHull_subset_closure_strictLowerLevelSet_zero_of_convex_epigraph
    (f : H → EReal) (hconv : Convex ℝ (epigraph f))
    (hneg : (strictLowerLevelSet f 0).Nonempty) :
    strictLowerLevelSet (lowerSemicontinuousEnvelope f) 0 ⊆
      closure (strictLowerLevelSet f 0) := by
  intro x hx
  -- Route correction: the old strict-set equality target is false; for the repaired statement we
  -- only need a closure argument from `epi \check f = closure (epi f)`.
  rw [mem_strictLowerLevelSet_iff] at hx
  obtain ⟨r, hxr, hr0⟩ := EReal.lt_iff_exists_real_btwn.mp hx
  have hr_neg : r < 0 := by
    simpa using hr0
  have hxr_le : lowerSemicontinuousEnvelope f x ≤ (r : EReal) := le_of_lt hxr
  have hxr_epi : (x, r) ∈ epigraph (lowerSemicontinuousEnvelope f) := by
    -- The chosen real height lies strictly above the hull value, so `(x, r)` is a hull epigraph
    -- point.
    rw [mem_epigraph_iff]
    exact hxr_le
  have hxr_closure : (x, r) ∈ closure (epigraph f) := by
    simpa [epi_lowerSemicontinuousHull_eq_closure_epi (f := f)] using hxr_epi
  rcases mem_closure_iff_seq_limit.mp hxr_closure with ⟨p, hp_mem, hp_tendsto⟩
  have hp_tendsto_fst :
      Filter.Tendsto (fun n ↦ (p n).1) Filter.atTop (nhds x) :=
    hp_tendsto.fst_nhds
  have hp_tendsto_snd :
      Filter.Tendsto (fun n ↦ (p n).2) Filter.atTop (nhds r) :=
    hp_tendsto.snd_nhds
  have hEventually_neg : ∀ᶠ n in Filter.atTop, (p n).2 < 0 := by
    -- Since the second coordinates converge to a negative real number, they are eventually
    -- negative.
    exact hp_tendsto_snd (Iio_mem_nhds hr_neg)
  have hEventually_mem :
      ∀ᶠ n in Filter.atTop, (p n).1 ∈ strictLowerLevelSet f 0 := by
    -- Real-height epigraph membership plus eventual negativity forces eventual membership in the
    -- strict negative level set.
    filter_upwards [hEventually_neg] with n hn
    rw [mem_strictLowerLevelSet_iff]
    exact lt_of_le_of_lt ((mem_epigraph_iff f (p n).1 (p n).2).mp (hp_mem n)) (by simpa using hn)
  -- Projecting the epigraph sequence to the first coordinate gives a convergent sequence in the
  -- strict negative level set, so the limit lies in its closure.
  exact mem_closure_of_tendsto hp_tendsto_fst hEventually_mem

-- Proof sketch: combine the inclusion `lev<₀ f ⊆ lev<₀ \check f` coming from `\check f ≤ f`
-- with the previous clause, which gives `lev<₀ \check f ⊆ closure (lev<₀ f)`.
/-- Corollary 9.11 (4): if `f` has convex epigraph and a nonempty strict negative level set, then
taking the lower semicontinuous hull `\check f` does not change the closure of the strict negative
level set. -/
theorem strictLowerLevelSet_zero_eq_strictLowerLevelSet_zero_lowerSemicontinuousHull_of_convex_epigraph
    (f : H → EReal) (hconv : Convex ℝ (epigraph f))
    (hneg : (strictLowerLevelSet f 0).Nonempty) :
    closure (strictLowerLevelSet f 0) =
      closure (strictLowerLevelSet (lowerSemicontinuousEnvelope f) 0) := by
  have hsubset :
      strictLowerLevelSet f 0 ⊆ strictLowerLevelSet (lowerSemicontinuousEnvelope f) 0 := by
    intro x hx
    -- The hull lies below `f`, so strict negativity for `f` propagates to the hull.
    rw [mem_strictLowerLevelSet_iff] at hx ⊢
    exact lt_of_le_of_lt ((lowerSemicontinuousHull_isGreatest f).1.2 x) hx
  apply le_antisymm
  · -- Monotonicity of closure gives the forward inclusion.
    exact closure_mono hsubset
  · -- Clause (3) already places the hull strict level set inside the closure of the original one.
    exact closure_minimal
      (strictLowerLevelSet_zero_lowerSemicontinuousHull_subset_closure_strictLowerLevelSet_zero_of_convex_epigraph
        f hconv hneg)
      isClosed_closure

-- Proof sketch: for convex `f`, Theorem 9.9 identifies the epigraph of the lower semicontinuous
-- convex envelope `\bar f` with `closure (epigraph f)`, while the lower semicontinuous hull has
-- the same epigraph by Lemma 1.32; reduce to the previous clause.
/-- Corollary 9.11 (5): if `f` has convex epigraph and a nonempty strict negative level set, then
taking the convex lower semicontinuous hull `\bar f` does not change the closure of the strict
negative level set. -/
theorem strictLowerLevelSet_zero_eq_strictLowerLevelSet_zero_lowerSemicontinuousConvexEnvelope_of_convex_epigraph
    (f : H → EReal) (hconv : Convex ℝ (epigraph f))
    (hneg : (strictLowerLevelSet f 0).Nonempty) :
    closure (strictLowerLevelSet f 0) =
      closure (strictLowerLevelSet (lowerSemicontinuousConvexEnvelope f) 0) := by
  have hsubset :
      strictLowerLevelSet f 0 ⊆ strictLowerLevelSet (lowerSemicontinuousConvexEnvelope f) 0 := by
    intro x hx
    -- The convex lower semicontinuous envelope also lies pointwise below `f`.
    rw [mem_strictLowerLevelSet_iff] at hx ⊢
    exact lt_of_le_of_lt (lowerSemicontinuousConvexEnvelope_le f x) hx
  have hclosure_subset :
      strictLowerLevelSet (lowerSemicontinuousConvexEnvelope f) 0 ⊆
        closure (strictLowerLevelSet f 0) := by
    intro x hx
    rw [mem_strictLowerLevelSet_iff] at hx
    obtain ⟨r, hxr, hr0⟩ := EReal.lt_iff_exists_real_btwn.mp hx
    have hr_neg : r < 0 := by
      simpa using hr0
    have hxr_epi : (x, r) ∈ epigraph (lowerSemicontinuousConvexEnvelope f) := by
      -- As in clause (3), choose a negative real height strictly above the envelope value.
      rw [mem_epigraph_iff]
      exact le_of_lt hxr
    have hxr_closure : (x, r) ∈ closure (epigraph f) := by
      -- Convexity collapses `closure (convexHull (epigraph f))` to `closure (epigraph f)`.
      simpa [hconv.convexHull_eq] using
        (show (x, r) ∈ closure (convexHull ℝ (epigraph f)) from by
          simpa [epigraph_lowerSemicontinuousConvexEnvelope_eq_closure_convexHull_epigraph
            (f := f)] using hxr_epi)
    rcases mem_closure_iff_seq_limit.mp hxr_closure with ⟨p, hp_mem, hp_tendsto⟩
    have hp_tendsto_fst :
        Filter.Tendsto (fun n ↦ (p n).1) Filter.atTop (nhds x) :=
      hp_tendsto.fst_nhds
    have hp_tendsto_snd :
        Filter.Tendsto (fun n ↦ (p n).2) Filter.atTop (nhds r) :=
      hp_tendsto.snd_nhds
    have hEventually_neg : ∀ᶠ n in Filter.atTop, (p n).2 < 0 := by
      -- The ordinates converge to a negative real number, so they are eventually negative.
      exact hp_tendsto_snd (Iio_mem_nhds hr_neg)
    have hEventually_mem :
        ∀ᶠ n in Filter.atTop, (p n).1 ∈ strictLowerLevelSet f 0 := by
      -- Each eventually negative epigraph point projects to a strict negative level-set point.
      filter_upwards [hEventually_neg] with n hn
      rw [mem_strictLowerLevelSet_iff]
      exact
        lt_of_le_of_lt ((mem_epigraph_iff f (p n).1 (p n).2).mp (hp_mem n)) (by simpa using hn)
    exact mem_closure_of_tendsto hp_tendsto_fst hEventually_mem
  apply le_antisymm
  · -- The original strict negative level set is contained in the convex-envelope one.
    exact closure_mono hsubset
  · -- The reverse inclusion follows from the same epigraph-closure approximation argument.
    exact closure_minimal hclosure_subset isClosed_closure

end Hilbert

end ERealFunction
