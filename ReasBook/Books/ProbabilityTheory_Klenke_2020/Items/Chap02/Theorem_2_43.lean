/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_41

-- Declarations for this item will be appended below by the statement pipeline.

open Set MeasureTheory

universe u

variable {Ω : Type u} {d : ℕ}

/-- The event that the origin lies in an infinite open cluster is contained in the event that
percolation occurs somewhere in the lattice. -/
theorem originInInfiniteClusterEvent_subset_percolationOccurs
    (cluster : LatticePoint d → Ω → Set (LatticePoint d)) :
    originInInfiniteClusterEvent cluster ⊆ percolationOccurs cluster := by
  intro ω hω
  exact ⟨0, by simpa [originInInfiniteClusterEvent] using hω⟩

variable [MeasurableSpace Ω]

/-- The origin-percolation probability is bounded above by the percolation probability. -/
theorem originPercolationProbability_le_percolationProbability
    (μ : ProbabilityMeasure Ω) (cluster : LatticePoint d → Ω → Set (LatticePoint d)) :
    originPercolationProbability μ cluster ≤ percolationProbability μ cluster := by
  simpa [ProbabilityMeasure.coeFn_def, originPercolationProbability, percolationProbability] using
    (measure_mono (originInInfiniteClusterEvent_subset_percolationOccurs cluster) :
      (μ : Measure Ω) (originInInfiniteClusterEvent cluster) ≤
        (μ : Measure Ω) (percolationOccurs cluster))

/-- If the origin-percolation probability vanishes and the infinite-cluster marginals are
translation invariant, then the percolation probability also vanishes. -/
theorem percolationProbability_eq_zero_of_originPercolationProbability_eq_zero
    (μ : ProbabilityMeasure Ω) (cluster : LatticePoint d → Ω → Set (LatticePoint d))
    [HasTranslationInvariantInfiniteClusterMarginals μ cluster]
    (h_origin : originPercolationProbability μ cluster = 0) :
    percolationProbability μ cluster = 0 := by
  have h_origin_toNNReal :
      ((μ : Measure Ω) (originInInfiniteClusterEvent cluster)).toNNReal = 0 := by
    simpa [ProbabilityMeasure.coeFn_def, originPercolationProbability] using h_origin
  have h_origin_measure : (μ : Measure Ω) (originInInfiniteClusterEvent cluster) = 0 := by
    rcases (ENNReal.toNNReal_eq_zero_iff _).1 h_origin_toNNReal with h_zero | h_top
    · exact h_zero
    · exact False.elim
        ((measure_ne_top (μ : Measure Ω) (originInInfiniteClusterEvent cluster)) h_top)
  have h_site_zero :
      ∀ y : LatticePoint d, (μ : Measure Ω) {ω | Set.Infinite (cluster y ω)} = 0 := by
    intro y
    have h_site_measure :
        (μ : Measure Ω) {ω | Set.Infinite (cluster y ω)} =
          (μ : Measure Ω) (originInInfiniteClusterEvent cluster) := by
      simpa [ProbabilityMeasure.coeFn_def, originPercolationProbability,
        ENNReal.toNNReal_eq_toNNReal_iff, measure_ne_top] using
          (originPercolationProbability_eq_site μ cluster y).symm
    rw [h_site_measure]
    exact h_origin_measure
  have h_union :
      percolationOccurs cluster = ⋃ y : LatticePoint d, {ω | Set.Infinite (cluster y ω)} := by
    ext ω
    simp [percolationOccurs]
  have h_perc_measure : (μ : Measure Ω) (percolationOccurs cluster) = 0 := by
    rw [h_union]
    exact measure_iUnion_null h_site_zero
  simpa [ProbabilityMeasure.coeFn_def, percolationProbability] using
    congrArg ENNReal.toNNReal h_perc_measure

/-- Theorem 2.43: under translation invariance of the infinite-cluster marginals, the percolation
probability vanishes when the origin-percolation probability vanishes, and it equals `1` when the
origin-percolation probability is strictly positive. -/
theorem percolationProbability_zero_or_one_of_originPercolationProbability
    (μ : ProbabilityMeasure Ω) (cluster : LatticePoint d → Ω → Set (LatticePoint d))
    [HasTranslationInvariantInfiniteClusterMarginals μ cluster]
    (h_zero_or_one :
      percolationProbability μ cluster = 0 ∨ percolationProbability μ cluster = 1) :
    (originPercolationProbability μ cluster = 0 →
        percolationProbability μ cluster = 0) ∧
      (0 < originPercolationProbability μ cluster →
        percolationProbability μ cluster = 1) := by
  constructor
  · -- The vanishing branch is exactly the previously established zero-transfer lemma.
    intro h_origin_zero
    exact percolationProbability_eq_zero_of_originPercolationProbability_eq_zero
      μ cluster h_origin_zero
  · -- Positive origin-percolation forces positive percolation via the monotonicity comparison.
    intro h_origin_pos
    have h_perc_pos : 0 < percolationProbability μ cluster := by
      exact lt_of_lt_of_le h_origin_pos
        (originPercolationProbability_le_percolationProbability μ cluster)
    -- The assumed `0 ∨ 1` dichotomy leaves only the value `1`.
    cases h_zero_or_one with
    | inl h_perc_zero =>
        exact False.elim ((ne_of_gt h_perc_pos) h_perc_zero)
    | inr h_perc_one =>
        exact h_perc_one
