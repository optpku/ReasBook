/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Theorem_13_11

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped CompactlySupported

universe u

variable {E : Type u}

-- Proof sketch: weak convergence is the canonical convergence `Tendsto` on `FiniteMeasure E`.
-- Uniqueness is therefore just the ambient Hausdorff uniqueness of limits in the weak topology on
-- `FiniteMeasure E`.
/-- Helper for Remark 13.13: weak convergence of finite measures determines the finite limit measure
uniquely. In particular, the textbook metric Borel statement is an immediate special case. -/
theorem weak_limit_unique [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [T2Space (FiniteMeasure E)]
    {μ ν : FiniteMeasure E} {μs : ℕ → FiniteMeasure E}
    (hμ : Tendsto μs atTop (nhds μ)) (hν : Tendsto μs atTop (nhds ν)) :
    μ = ν :=
  tendsto_nhds_unique hμ hν

/-- Helper for Remark 13.13: two vague limits force the same integral for every compactly
supported continuous real-valued test function. -/
lemma twoVagueLimits_eq_integral_compactlySupported [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [LocallyCompactSpace E] {μ ν : Measure E} {μs : ℕ → Measure E}
    (hμ : radonMeasureVaguelyConvergesTo μs μ)
    (hν : radonMeasureVaguelyConvergesTo μs ν) :
    ∀ g : C_c(E, ℝ), ∫ x, g x ∂μ = ∫ x, g x ∂ν := by
  -- Proof comment: unpack vague convergence into the Radon side conditions and the scalar
  -- convergence of every compactly supported test integral.
  rw [radonMeasureVaguelyConvergesTo_iff] at hμ hν
  intro g
  -- Proof comment: both vague convergence hypotheses describe the same real sequence of
  -- integrals, so Hausdorff uniqueness of limits identifies the two candidate limits.
  exact tendsto_nhds_unique (hμ.2.2 g) (hν.2.2 g)

/-- Helper for Remark 13.13: the compactly supported unit-interval Lipschitz separating family has
equal integrals against any two vague limits of the same sequence. -/
lemma twoVagueLimits_eq_integral_onSeparatingFamily [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [LocallyCompactSpace E] {μ ν : Measure E} {μs : ℕ → Measure E}
    (hμ : radonMeasureVaguelyConvergesTo μs μ)
    (hν : radonMeasureVaguelyConvergesTo μs ν) :
    ∀ ⦃f : E → ℝ⦄,
      f ∈ (((↑) : C_c(E, ℝ) → E → ℝ) '' compactlySupportedUnitIntervalLipschitzRealMapSpace E) →
        Integrable f μ → Integrable f ν → ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
  intro f hf _ _
  -- Proof comment: membership in the separating family means `f` comes from some `g : C_c(E, ℝ)`,
  -- so the previous compactly supported bridge applies immediately.
  rcases hf with ⟨g, -, rfl⟩
  exact twoVagueLimits_eq_integral_compactlySupported hμ hν g

-- Proof sketch: use the source-facing owner predicate `radonMeasureVaguelyConvergesTo`. If the
-- same sequence converges vaguely to both `μ` and `ν`, then the compactly supported continuous
-- test integrals agree for both candidates, and Theorem 13.11 (2) separates Radon measures on a
-- locally compact metric space.
/-- Remark 13.13 (2): on a locally compact metric space, a sequence of Radon measures has at most
one vague limit, in the sense that convergence of all compactly supported continuous test
integrals determines the Radon limit measure uniquely. -/
theorem vague_limit_unique_of_locallyCompact [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [LocallyCompactSpace E] {μ ν : Measure E} {μs : ℕ → Measure E}
    (hμ : radonMeasureVaguelyConvergesTo μs μ)
    (hν : radonMeasureVaguelyConvergesTo μs ν) :
    μ = ν := by
  -- Proof comment: recover the Radon side conditions from the source-facing vague convergence
  -- predicate before invoking the separating-family theorem from Theorem 13.11 (2).
  rw [radonMeasureVaguelyConvergesTo_iff] at hμ hν
  let hsep :=
    compactlySupportedUnitIntervalLipschitzRealFunctionSpace_isSeparatingFamilyFor_radonMeasureSpace
      (E := E)
  -- Proof comment: the separating family theorem reduces equality of the measures to equality of
  -- all integrals against tests in the compactly supported unit-interval Lipschitz family.
  exact IsSeparatingFamilyFor.eq_of_forall_integral_eq hsep hμ.1 hν.1
    (twoVagueLimits_eq_integral_onSeparatingFamily
      (μ := μ) (ν := ν) (μs := μs) hμ hν)
