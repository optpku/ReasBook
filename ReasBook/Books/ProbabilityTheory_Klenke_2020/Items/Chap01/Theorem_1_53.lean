/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open Set

open scoped ENNReal

namespace MeasureTheory

universe u

/-- Helper for Theorem 1.53: any extension measure that agrees with the semiring content is finite
on the prescribed covering sets. -/
lemma extension_cover_sets_lt_top
    {α : Type u} {A : Set (Set α)} (m : AddContent ℝ≥0∞ A) (s : ℕ → Set α)
    (hs_mem : ∀ n, s n ∈ A) (hs_finite : ∀ n, m (s n) < ∞)
    {μ : @Measure α (MeasurableSpace.generateFrom A)}
    (hμ : ∀ t ∈ A, μ t = m t) :
    ∀ n, μ (s n) < ∞ := by
  intro n
  -- Rewrite the measure of each covering set through the assumed agreement on `A`.
  rw [hμ (s n) (hs_mem n)]
  exact hs_finite n

/-- Helper for Theorem 1.53: the semiring covering family yields finite spanning sets for any
extension measure that agrees with the original content on the semiring. -/
def finiteSpanningSetsIn_of_semiring_cover
    {α : Type u} {A : Set (Set α)} (m : AddContent ℝ≥0∞ A) (s : ℕ → Set α)
    (hs_mem : ∀ n, s n ∈ A) (hs_finite : ∀ n, m (s n) < ∞)
    (hs_spanning : (⋃ n, s n) = Set.univ)
    {μ : @Measure α (MeasurableSpace.generateFrom A)}
    (hμ : ∀ t ∈ A, μ t = m t) :
    μ.FiniteSpanningSetsIn A :=
  -- Package the textbook covering sequence into mathlib's `FiniteSpanningSetsIn` structure.
  .mk s hs_mem (extension_cover_sets_lt_top m s hs_mem hs_finite hμ) hs_spanning

/-- Helper for Theorem 1.53: two extension measures on `generateFrom A` that agree with the same
semiring content coincide. -/
lemma eq_of_eq_on_semiring_of_spanning_cover
    {α : Type u} {A : Set (Set α)} (hA : IsSetSemiring A) (m : AddContent ℝ≥0∞ A)
    (s : ℕ → Set α) (hs_mem : ∀ n, s n ∈ A) (hs_finite : ∀ n, m (s n) < ∞)
    (hs_spanning : (⋃ n, s n) = Set.univ)
    {μ ν : @Measure α (MeasurableSpace.generateFrom A)}
    (hμ : ∀ t ∈ A, μ t = m t) (hν : ∀ t ∈ A, ν t = m t) :
    μ = ν := by
  -- Uniqueness reduces to the standard π-system extensionality theorem with a common finite cover.
  exact
    (finiteSpanningSetsIn_of_semiring_cover (μ := μ) m s hs_mem hs_finite hs_spanning hμ).ext
      rfl hA.isPiSystem fun t ht ↦ by
        rw [hμ t ht, hν t ht]

/-- Theorem 1.53: a sigma-subadditive additive content on a set semiring that admits a countable
cover by semiring sets of finite mass extends uniquely to a sigma-finite measure on the generated
sigma-algebra. -/
-- Proof sketch: construct the canonical extension on `MeasurableSpace.generateFrom A` using
-- `AddContent.measure`. The countable cover by sets in `A` with finite `m`-mass gives
-- sigma-finiteness of the extension. For uniqueness, any two such extensions agree on the
-- generating π-system `A` and are finite on the same spanning sequence, so
-- `Measure.ext_of_generateFrom_of_iUnion` applies.
theorem existsUnique_sigmaFinite_measure_generateFrom_eq_of_semiring_addContent
    {α : Type u} {A : Set (Set α)} (hA : IsSetSemiring A) (m : AddContent ℝ≥0∞ A)
    (hm_sigma : m.IsSigmaSubadditive)
    (s : ℕ → Set α) (hs_mem : ∀ n, s n ∈ A) (hs_finite : ∀ n, m (s n) < ∞)
    (hs_spanning : (⋃ n, s n) = Set.univ) :
    ∃! μ : @Measure α (MeasurableSpace.generateFrom A),
      (∀ t ∈ A, μ t = m t) ∧ SigmaFinite μ := by
  letI : MeasurableSpace α := MeasurableSpace.generateFrom A
  let μ0 : Measure α := m.measure hA le_rfl hm_sigma
  have hμ0_eq : ∀ t ∈ A, μ0 t = m t := by
    intro t ht
    -- The canonical Carathéodory extension agrees with the original content on the semiring.
    simpa [μ0] using AddContent.measure_eq (m := m) (hC := hA) (hC_gen := rfl)
      (m_sigma_subadd := hm_sigma) ht
  refine ⟨μ0, ?_, ?_⟩
  · constructor
    · exact hμ0_eq
    · -- The given semiring cover provides sigma-finiteness of the canonical extension.
      exact
        (finiteSpanningSetsIn_of_semiring_cover (μ := μ0) m s hs_mem hs_finite hs_spanning
          hμ0_eq).sigmaFinite
  · intro ν hν
    rcases hν with ⟨hν_eq, _hν_sigma⟩
    -- Any other extension agrees with `μ0` on the generating π-system, hence equals `μ0`.
    exact
      eq_of_eq_on_semiring_of_spanning_cover (μ := μ0) (ν := ν) hA m s hs_mem hs_finite
        hs_spanning hμ0_eq hν_eq |>.symm

end MeasureTheory
