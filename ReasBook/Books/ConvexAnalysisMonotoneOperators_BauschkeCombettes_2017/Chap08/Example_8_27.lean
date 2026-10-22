/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Example_8_26

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

namespace ERealFunction

/-- The scalar generator `t ↦ t log t` on `]0, +∞[` extended by `+∞` outside the positive
half-line. -/
noncomputable def relativeEntropyGenerator : ℝ → EReal :=
  fun t ↦ if 0 < t then ((t * Real.log t : ℝ) : EReal) else ⊤

/-- Helper for Example 8.27: real-height epigraph membership for the scalar entropy generator is
exactly strict positivity together with the logarithmic height bound. -/
private lemma mem_epigraph_relativeEntropyGenerator_iff {t r : ℝ} :
    (t, r) ∈ epigraph relativeEntropyGenerator ↔ 0 < t ∧ t * Real.log t ≤ r := by
  constructor
  · intro h
    rw [mem_epigraph_iff] at h
    by_cases ht : 0 < t
    · constructor
      · exact ht
      · have h' : ((t * Real.log t : ℝ) : EReal) ≤ (r : EReal) := by
          simpa [relativeEntropyGenerator, ht] using h
        exact_mod_cast h'
    · have htop := h
      simp [relativeEntropyGenerator, ht] at htop
  · rintro ⟨ht, htr⟩
    rw [mem_epigraph_iff]
    have h' : ((t * Real.log t : ℝ) : EReal) ≤ (r : EReal) := by
      exact_mod_cast htr
    simpa [relativeEntropyGenerator, ht] using h'

/-- Helper for Example 8.27: the scalar entropy generator never takes the value `-∞`. -/
private lemma relativeEntropyGenerator_ne_bot (t : ℝ) :
    relativeEntropyGenerator t ≠ ⊥ := by
  -- Both branches are finite-above: the positive branch is a real value and the other branch is
  -- `⊤`.
  by_cases ht : 0 < t
  · simpa [relativeEntropyGenerator, ht] using (EReal.coe_ne_bot (t * Real.log t))
  · simp [relativeEntropyGenerator, ht]

-- Proof sketch: apply Proposition 8.14 to the real-valued function `t ↦ t * Real.log t` on the
-- open interval `Set.Ioi 0`, using the strict increase of its derivative `t ↦ Real.log t + 1`;
-- then identify the real-height epigraph of the extended-valued completion by `+∞` outside
-- `Set.Ioi 0`.
/-- The scalar entropy generator has convex real-height epigraph. -/
theorem convex_epigraph_relativeEntropyGenerator :
    Convex ℝ (epigraph relativeEntropyGenerator) := by
  -- Work directly with real-height epigraph points and expose the positivity branch at both
  -- endpoints.
  refine (convex_iff_forall_pos).2 ?_
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, ξ⟩
  rcases q with ⟨y, η⟩
  rw [mem_epigraph_relativeEntropyGenerator_iff] at hp hq
  rw [mem_epigraph_relativeEntropyGenerator_iff]
  constructor
  · -- Strict positivity is preserved by convex combinations with positive coefficients.
    simpa [Prod.smul_mk, smul_eq_mul] using add_pos (mul_pos ha hp.1) (mul_pos hb hq.1)
  · have hmulLog :
        (a * x + b * y) * Real.log (a * x + b * y) ≤
          a * (x * Real.log x) + b * (y * Real.log y) :=
      Real.convexOn_mul_log.2
        (show x ∈ Set.Ici (0 : ℝ) from hp.1.le)
        (show y ∈ Set.Ici (0 : ℝ) from hq.1.le)
        ha.le hb.le hab
    have hheight :
        a * (x * Real.log x) + b * (y * Real.log y) ≤ a * ξ + b * η := by
      -- The endpoint epigraph bounds scale and add because the coefficients are nonnegative.
      exact add_le_add (mul_le_mul_of_nonneg_left hp.2 ha.le)
        (mul_le_mul_of_nonneg_left hq.2 hb.le)
    -- The scalar convexity inequality and the endpoint height bounds give the desired epigraph
    -- inequality at the barycenter.
    exact le_trans hmulLog hheight

/-- The relative entropy function on the canonical `Fin N → ℝ` model of `ℝ^N × ℝ^N`, obtained as
the coordinate perspective sum associated with `relativeEntropyGenerator`. -/
noncomputable def relativeEntropyFunction (N : ℕ) :
    ((Fin N → ℝ) × (Fin N → ℝ)) → EReal :=
  coordinatePerspectiveSum (Fin N) relativeEntropyGenerator

-- Proof sketch: unfold `relativeEntropyFunction` into `coordinatePerspectiveSum`, use the positive
-- branch from Example 8.26, and then simplify each coordinate term with
-- `ηᵢ * ((ξᵢ / ηᵢ) * log (ξᵢ / ηᵢ)) = ξᵢ * log (ξᵢ / ηᵢ)` under the positivity assumptions.
/-- On the strictly positive orthant, the relative entropy function is the finite sum
`∑ i, ξᵢ log (ξᵢ / ηᵢ)`. -/
theorem relativeEntropyFunction_apply_of_pos (N : ℕ) (x y : Fin N → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    relativeEntropyFunction N (x, y) =
      ∑ i, ((x i * Real.log (x i / y i) : ℝ) : EReal) := by
  -- Example 8.26 gives the positive-orthant branch as a weighted coordinate sum.
  rw [relativeEntropyFunction]
  rw [coordinatePerspectiveSum_apply_of_pos (Fin N) relativeEntropyGenerator x y hy]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hdiv_pos : 0 < x i / y i := div_pos (hx i) (hy i)
  -- Each coordinate stays on the positive branch of the scalar generator.
  rw [relativeEntropyGenerator, if_pos hdiv_pos, EReal.coe_mul]
  have hcoord :
      y i * ((x i / y i) * Real.log (x i / y i)) = x i * Real.log (x i / y i) := by
    -- Clearing the positive denominator reduces the coordinate identity to a ring normalization.
    field_simp [(hy i).ne']
  exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hcoord

-- Proof sketch: apply Example 8.26 to `relativeEntropyGenerator`. The required convexity of the
-- scalar epigraph is `convex_epigraph_relativeEntropyGenerator`, so the induced coordinate
-- perspective sum has convex epigraph on the product space.
/-- Example 8.27: on the canonical `Fin N → ℝ` model of `ℝ^N × ℝ^N`, the function that equals
`∑ i, ξᵢ log (ξᵢ / ηᵢ)` on the strictly positive orthant and `+∞` otherwise has convex real-height
epigraph. -/
theorem convex_epigraph_relativeEntropyFunction (N : ℕ) :
    Convex ℝ (epigraph (relativeEntropyFunction N)) := by
  have hscalar :
      Convex ℝ {p : ℝ × ℝ | relativeEntropyGenerator p.1 ≤ (p.2 : EReal)} := by
    -- Repackage the scalar result in the set form expected by Example 8.26.
    simpa [epigraph] using convex_epigraph_relativeEntropyGenerator
  let lift :
      (∀ t, relativeEntropyGenerator t ≠ ⊥) →
      Convex ℝ {p : ℝ × ℝ | relativeEntropyGenerator p.1 ≤ (p.2 : EReal)} →
      Convex ℝ {p : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) |
        coordinatePerspectiveSum (Fin N) relativeEntropyGenerator p.1 ≤ (p.2 : EReal)} :=
    ERealFunction.convex_coordinatePerspectiveSum (Fin N) relativeEntropyGenerator
  let hsum :
      Convex ℝ {p : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) |
        coordinatePerspectiveSum (Fin N) relativeEntropyGenerator p.1 ≤ (p.2 : EReal)} :=
    lift relativeEntropyGenerator_ne_bot hscalar
  -- Example 8.26 lifts scalar epigraph convexity to the coordinate perspective sum.
  simpa [relativeEntropyFunction, epigraph] using hsum

end ERealFunction
