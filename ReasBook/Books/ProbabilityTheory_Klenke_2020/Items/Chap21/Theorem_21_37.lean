/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_38

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

noncomputable section

/-- In this item, the continuous Brownian path space is equipped with its Borel `σ`-algebra. -/
local instance brownianPathSpaceMeasurableSpace : MeasurableSpace BrownianPathSpace :=
  borel BrownianPathSpace

/-- The Brownian path space carries the canonical Borel-space structure coming from its topology. -/
local instance brownianPathSpaceBorelSpace : BorelSpace BrownianPathSpace :=
  ⟨rfl⟩

-- Proof sketch: this is the source-facing one-way implication extracted from the canonical
-- finite-dimensional-distribution API of Theorem 21.38.
/-- Theorem 21.37: weak convergence of probability laws on `C([0, ∞), ℝ)` implies convergence of
all finite-dimensional marginal laws. -/
theorem brownianPathSpace_tendsto_finiteDimensionalMarginals
    (μs : ℕ → ProbabilityMeasure BrownianPathSpace) (μ : ProbabilityMeasure BrownianPathSpace)
    (hμ : Tendsto μs atTop (𝓝 μ)) (n : ℕ) (times : Fin (n + 1) → NNReal) :
    Tendsto
      (fun m ↦ continuousPathFiniteDimensionalDistribution (μs m) times)
      atTop
      (𝓝 (continuousPathFiniteDimensionalDistribution μ times)) := by
  -- The imported equivalence packages weak convergence into finite-dimensional convergence plus
  -- tightness, so we first extract the universal finite-dimensional convergence statement.
  have hFiniteDimensional :
      ∀ n : ℕ, ∀ times : Fin (n + 1) → NNReal,
        Tendsto
          (fun k ↦ continuousPathFiniteDimensionalDistribution (μs k) times)
          atTop
          (𝓝 (continuousPathFiniteDimensionalDistribution μ times)) :=
    ((ProbabilityTheory.tendsto_iff_finiteDimensionalDistribution_tendsto_and_isTight μ μs).mpr
      hμ).1
  -- Specializing that universal statement at the requested dimension and time tuple yields the
  -- target marginal convergence.
  simpa using hFiniteDimensional n times
