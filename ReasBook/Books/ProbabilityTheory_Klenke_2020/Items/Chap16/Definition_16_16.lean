/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- The primitive data of a real Lévy--Khintchine triple: Gaussian coefficient, drift, and Lévy
measure. -/
structure LevyKhinchinTriple where
  sigma2 : ℝ
  b : ℝ
  ν : Measure ℝ

/-- Definition 16.16 (1): a canonical measure on `ℝ` has no atom at `0` and finite integral of
`x ↦ min (x^2, 1)`; for Lévy measures on `ℝ`, these side conditions already imply
σ-finiteness. -/
class IsCanonicalMeasure (ν : Measure ℝ) : Prop where
  measure_singleton_zero : ν ({0} : Set ℝ) = 0
  integrable_sq_min_one : Integrable (fun x : ℝ ↦ min (x ^ (2 : ℕ)) 1) ν

namespace IsCanonicalMeasure

/-- Helper for Definition 16.16: the `n`th positive level set of the truncated second-moment
integrand. -/
def canonicalMeasureCoverSet (n : ℕ) : Set ℝ :=
  {x : ℝ | ((n + 1 : ℝ)⁻¹) < min (x ^ (2 : ℕ)) 1}

/-- Helper for Definition 16.16: every positive level set of the canonical integrand has finite
measure. -/
lemma canonicalMeasure_levelSet_lt_top {ν : Measure ℝ} (hν : IsCanonicalMeasure ν) {ε : ℝ}
    (hε : 0 < ε) : ν {x : ℝ | ε < min (x ^ (2 : ℕ)) 1} < ⊤ := by
  -- Apply the standard integrable-level-set estimate to the canonical integrand.
  simpa using hν.integrable_sq_min_one.measure_gt_lt_top hε

/-- Helper for Definition 16.16: every nonzero real belongs to one of the canonical cover sets. -/
lemma mem_canonicalMeasureCover_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    ∃ n : ℕ, x ∈ canonicalMeasureCoverSet n := by
  have hx_sq_pos : 0 < x ^ (2 : ℕ) := by
    simpa [pow_two] using sq_pos_of_ne_zero hx
  have hmin_pos : 0 < min (x ^ (2 : ℕ)) 1 := by
    exact lt_min hx_sq_pos zero_lt_one
  -- Use the Archimedean reciprocal estimate at the positive value `min (x^2) 1`.
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hmin_pos
  refine ⟨n, ?_⟩
  dsimp [canonicalMeasureCoverSet]
  simpa [one_div] using hn

/-- Helper for Definition 16.16: the singleton `{0}` together with the canonical cover sets spans
`ℝ`. -/
lemma canonicalMeasureCover_spanning :
    ({0} : Set ℝ) ∪ ⋃ n : ℕ, canonicalMeasureCoverSet n = Set.univ := by
  ext x
  constructor
  · -- Any point in the displayed union is, tautologically, a real number.
    intro _
    simp
  · -- Split off the origin, then cover every nonzero point by a positive level set.
    intro _
    by_cases hx : x = 0
    · simp [hx]
    · obtain ⟨n, hn⟩ := mem_canonicalMeasureCover_of_ne_zero hx
      exact Or.inr <| Set.mem_iUnion.2 ⟨n, hn⟩

/-- For a canonical measure on `ℝ`, σ-finiteness is a derived consequence of the no-atom and
truncated-second-moment conditions. -/
theorem sigmaFinite {ν : Measure ℝ} (hν : IsCanonicalMeasure ν) : SigmaFinite ν := by
  let cover : Set (Set ℝ) :=
    Set.insert ({0} : Set ℝ) (Set.range canonicalMeasureCoverSet)
  have hcount : cover.Countable := by
    -- The cover is the singleton `{0}` plus a countable range indexed by `ℕ`.
    exact (Set.countable_range canonicalMeasureCoverSet).insert ({0} : Set ℝ)
  have hfinite : ∀ s ∈ cover, ν s < ⊤ := by
    intro s hs
    dsimp [cover] at hs
    rcases hs with rfl | hs
    · -- The singleton `{0}` has measure zero by the canonical-measure hypothesis.
      simp [hν.measure_singleton_zero]
    · rcases hs with ⟨n, rfl⟩
      -- Each level set has finite measure because the defining integrand is integrable.
      exact canonicalMeasure_levelSet_lt_top hν (by positivity)
  have hcover : ⋃₀ cover = Set.univ := by
    -- Witness each real either by `{0}` or by one canonical positive level set.
    ext x
    constructor
    · intro _
      simp
    · intro _
      by_cases hx : x = 0
      · refine Set.mem_sUnion.2 ?_
        refine ⟨({0} : Set ℝ), ?_, by simp [hx]⟩
        dsimp [cover]
        exact Or.inl rfl
      · obtain ⟨n, hn⟩ := mem_canonicalMeasureCover_of_ne_zero hx
        refine Set.mem_sUnion.2 ?_
        refine ⟨canonicalMeasureCoverSet n, ?_, hn⟩
        dsimp [cover]
        exact Or.inr ⟨n, rfl⟩
  exact Measure.sigmaFinite_of_countable hcount hfinite hcover

instance (ν : Measure ℝ) [hν : IsCanonicalMeasure ν] : SigmaFinite ν :=
  hν.sigmaFinite

end IsCanonicalMeasure

/-- The zero measure on `ℝ` is canonical. -/
instance : IsCanonicalMeasure (0 : Measure ℝ) where
  -- The zero measure gives no mass to any singleton.
  measure_singleton_zero := by
    simp
  -- Every function is integrable against the zero measure.
  integrable_sq_min_one := by
    -- Use the zero-measure integrability theorem in its current argument order.
    exact
      (integrable_zero_measure :
        Integrable (fun x : ℝ ↦ min (x ^ (2 : ℕ)) 1) (0 : Measure ℝ))

/-- Definition 16.16 (2): a canonical triple `(σ², b, ν)` consists of a nonnegative Gaussian
coefficient, an arbitrary drift term, and a canonical measure on `ℝ`. -/
class IsCanonicalTriple (τ : LevyKhinchinTriple) : Prop where
  sigma2_nonneg : 0 ≤ τ.sigma2
  isCanonicalMeasure : IsCanonicalMeasure τ.ν

attribute [instance] IsCanonicalTriple.isCanonicalMeasure

/-- Any triple with zero Gaussian coefficient and zero jump measure is canonical. -/
instance (b : ℝ) : IsCanonicalTriple { sigma2 := 0, b := b, ν := 0 } where
  -- The Gaussian coefficient is exactly zero here.
  sigma2_nonneg := by
    simp
  -- The jump measure component is the canonical zero measure.
  isCanonicalMeasure := by
    infer_instance

end MeasureTheory.ProbabilityMeasure
