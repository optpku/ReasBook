/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_38
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_51

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

local notation "PathSpace" => ContinuousMap NNReal ℝ

local instance pathSpaceMeasurableSpace : MeasurableSpace PathSpace := borel _
local instance pathSpaceBorelSpace : BorelSpace PathSpace := ⟨rfl⟩

/-- Helper for Example 26.31: reindexing a `ℕ+`-sequence along `Nat.succPNat` preserves its
`atTop` limit. -/
private theorem tendstoPnatAtTopIffSuccPNat {β : Type*} [TopologicalSpace β]
    {f : ℕ+ → β} {l : Filter β} :
    Tendsto f atTop l ↔ Tendsto (fun n : ℕ ↦ f (Nat.succPNat n)) atTop l := by
  constructor
  · intro hf
    -- Proof comment: compose the `ℕ+`-indexed limit with the canonical order isomorphism
    -- `ℕ ≃o ℕ+` to obtain the shifted `ℕ`-indexed sequence.
    simpa [OrderIso.pnatIsoNat_symm_apply] using hf.comp OrderIso.pnatIsoNat.symm.tendsto_atTop
  · intro hf
    -- Proof comment: compose back with `PNat.natPred` and simplify the resulting reindexing.
    have hcomp := hf.comp OrderIso.pnatIsoNat.tendsto_atTop
    convert hcomp using 1
    ext n
    simp [OrderIso.pnatIsoNat_apply]

/-- Helper for Example 26.31: the shifted `ℕ`-range obtained from `Nat.succPNat` is contained in
the original `ℕ+`-range. -/
private lemma rangeCompSuccPNatSubset {α : Type*} {f : ℕ+ → α} :
    Set.range (fun n : ℕ ↦ f (Nat.succPNat n)) ⊆ Set.range f := by
  -- Proof comment: every shifted value is visibly one value of the original `ℕ+`-indexed family.
  rintro _ ⟨n, rfl⟩
  exact ⟨Nat.succPNat n, rfl⟩

-- Proof sketch: this is Theorem 21.51 specialized to the unit initial state corresponding to the
-- rescaling `N⁻¹ Z₀ᴺ = 1`; the rescaled path law already encodes the textbook linear
-- interpolation of `N⁻¹ Z^N_{⌊Nt⌋}`.
/-- Example 26.31: for the critical geometric Galton--Watson family with initial masses `N`, once
Lindvall's finite-dimensional convergence and tightness hypotheses are verified for the linearly
interpolated rescaled paths, those path laws converge weakly to a Feller branching diffusion
started from `1`. -/
theorem rescaledGaltonWatsonPathLaw_tendsto_fellerBranchingDiffusion_startedAtOne
    {ΩN : ℕ+ → Type u} [∀ N : ℕ+, MeasurableSpace (ΩN N)]
    {Ω : Type v} [MeasurableSpace Ω]
    (PZ : (N : ℕ+) → ProbabilityMeasure (ΩN N))
    (Z : (N : ℕ+) → ℕ → ΩN N → ℕ)
    (hZ_meas : ∀ N : ℕ+, ∀ k : ℕ, Measurable (Z N k))
    (PY : ProbabilityMeasure Ω)
    (Y : Ω → PathSpace)
    (hY_meas : Measurable Y)
    (hY : HasFellerBranchingDiffusionPathLaw PY Y 1)
    (hfdd :
      ∀ m : ℕ, ∀ times : Fin (m + 1) → NNReal,
        Tendsto
          (fun N : ℕ+ ↦
            continuousPathFiniteDimensionalDistribution
              (rescaledGaltonWatsonPathLaw (PZ N) (Z N) (hZ_meas N) (N : ℕ)) times)
          atTop
          (nhds
            (continuousPathFiniteDimensionalDistribution
              (continuousPathLaw PY Y hY_meas) times)))
    (htight :
      IsTightMeasureSet
        (Set.range fun N : ℕ+ ↦
          (rescaledGaltonWatsonPathLaw (PZ N) (Z N) (hZ_meas N) (N : ℕ) : Measure PathSpace))) :
    Tendsto
      (fun N : ℕ+ ↦ rescaledGaltonWatsonPathLaw (PZ N) (Z N) (hZ_meas N) (N : ℕ))
      atTop
      (nhds (continuousPathLaw PY Y hY_meas)) := by
  -- Proof comment: the abstract convergence criterion only uses the target path law, but we keep
  -- the Feller-branching witness in scope to record the textbook identification of that limit.
  have _ : HasFellerBranchingDiffusionPathLaw PY Y 1 := hY
  let μ : ℕ+ → ProbabilityMeasure PathSpace := fun N ↦
    rescaledGaltonWatsonPathLaw (PZ N) (Z N) (hZ_meas N) (N : ℕ)
  have htightμ : IsTightMeasureSet (Set.range fun N : ℕ+ ↦ (μ N : Measure PathSpace)) := by
    simpa [μ] using htight
  have hfddNat :
      ∀ m : ℕ, ∀ times : Fin (m + 1) → NNReal,
        Tendsto
          (fun n : ℕ ↦ continuousPathFiniteDimensionalDistribution (μ (Nat.succPNat n)) times)
          atTop
          (nhds
            (continuousPathFiniteDimensionalDistribution
              (continuousPathLaw PY Y hY_meas) times)) := by
    intro m times
    -- Proof comment: each finite-dimensional convergence hypothesis is transported from `ℕ+`
    -- to `ℕ` by the reindexing lemma.
    simpa [μ] using
      (tendstoPnatAtTopIffSuccPNat.1 (hfdd m times))
  have htightNat :
      IsTightMeasureSet
        (Set.range fun n : ℕ ↦ (μ (Nat.succPNat n) : Measure PathSpace)) := by
    -- Proof comment: tightness survives after restricting to the shifted subsequence because its
    -- range sits inside the original tight family.
    exact htightμ.subset
      (rangeCompSuccPNatSubset (f := fun N : ℕ+ ↦ (μ N : Measure PathSpace)))
  have hNat :
      Tendsto (fun n : ℕ ↦ μ (Nat.succPNat n)) atTop
        (nhds (continuousPathLaw PY Y hY_meas)) := by
    -- Proof comment: Chapter 21's weak-convergence criterion now applies directly to the shifted
    -- `ℕ`-indexed family of path laws.
    exact
      (ProbabilityTheory.tendsto_iff_finiteDimensionalDistribution_tendsto_and_isTight
        (P := continuousPathLaw PY Y hY_meas)
        (Pn := fun n : ℕ ↦ μ (Nat.succPNat n))).mp
        ⟨hfddNat, htightNat⟩
  -- Proof comment: transport the `ℕ`-indexed weak convergence back to the original `ℕ+` family.
  simpa [μ] using (tendstoPnatAtTopIffSuccPNat.2 hNat)

end ProbabilityTheory
