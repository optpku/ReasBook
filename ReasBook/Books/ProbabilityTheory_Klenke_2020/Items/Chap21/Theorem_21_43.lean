/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_38
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_42

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal

noncomputable section

universe u v

local instance brownianPathSpaceMeasurableSpace : MeasurableSpace BrownianPathSpace :=
  borel BrownianPathSpace

local instance brownianPathSpaceBorelSpace : BorelSpace BrownianPathSpace :=
  ⟨rfl⟩

-- Proof sketch: Theorem 21.42 supplies tightness of the interpolated path laws from the initial
-- value control and the Kolmogorov moment bounds, and then Theorem 21.38 upgrades that tightness
-- plus the finite-dimensional convergence to weak convergence on path space.
/-- Helper for Theorem 21.43: Theorem 21.42 provides tightness of the interpolated path laws, and
Theorem 21.38 upgrades this together with finite-dimensional convergence to weak convergence on
path space. -/
theorem donskerPathLaw_tendsto_of_fdd_and_kolmogorovCriterion
    {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : ProbabilityMeasure Ω)
    (Sbar : ℕ → Ω → BrownianPathSpace)
    (hSbar : ∀ n, Measurable (Sbar n))
    (PW : ProbabilityMeasure Ω')
    (W : Ω' → BrownianPathSpace)
    (hW : Measurable W)
    (hfdd :
      ∀ m : ℕ, ∀ times : Fin (m + 1) → NNReal,
        Tendsto
          (fun n ↦
            ProbabilityTheory.continuousPathFiniteDimensionalDistribution
              (P.map (hSbar n).aemeasurable) times)
          atTop
          (𝓝
            (ProbabilityTheory.continuousPathFiniteDimensionalDistribution
              (PW.map hW.aemeasurable) times)))
    (h0_tight :
      initial_value_laws_tight (fun n ↦ P.map (hSbar n).aemeasurable))
    (hmoment :
      ∀ N : NNReal, 0 < N →
        ∃ α β C : NNReal,
          ∀ n,
            IsKolmogorovProcessOnIcc
              (P : Measure Ω) (fun t ω ↦ Sbar n ω t) N α β C) :
    Tendsto
      (fun n ↦ P.map (hSbar n).aemeasurable)
      atTop
      (𝓝 (PW.map hW.aemeasurable)) := by
  let μ : ℕ → ProbabilityMeasure BrownianPathSpace := fun n ↦ P.map (hSbar n).aemeasurable
  let ν : ProbabilityMeasure BrownianPathSpace := PW.map hW.aemeasurable
  have hCompact :
      IsCompact (closure (Set.range μ)) := by
    simpa [μ] using
      isCompact_closure_range_pathLaw_of_tight_initialLaws_of_kolmogorovCriterion
        (P := P)
        (X := Sbar)
        hSbar
        h0_tight
        hmoment
  have hTightClosure :
      IsTightMeasureSet
        (((↑) : ProbabilityMeasure BrownianPathSpace → Measure BrownianPathSpace) ''
          closure (Set.range μ)) := by
    simpa [MeasureTheory.probabilityMeasureView] using
      (MeasureTheory.compactProbabilityMeasureViewIsTight
        (C := closure (Set.range μ)) hCompact)
  have hTightImage :
      IsTightMeasureSet
        (((↑) : ProbabilityMeasure BrownianPathSpace → Measure BrownianPathSpace) ''
          Set.range μ) := by
    refine hTightClosure.subset ?_
    rintro ρ ⟨σ, hσ, rfl⟩
    exact ⟨σ, subset_closure hσ, rfl⟩
  have hRangeEq :
      (((↑) : ProbabilityMeasure BrownianPathSpace → Measure BrownianPathSpace) '' Set.range μ) =
        Set.range fun n ↦ (μ n : Measure BrownianPathSpace) := by
    ext ρ
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      rcases hσ with ⟨n, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨μ n, ⟨n, rfl⟩, rfl⟩
  have hTightRange :
      IsTightMeasureSet (Set.range fun n ↦ (μ n : Measure BrownianPathSpace)) := by
    rwa [← hRangeEq]
  have hWeak :
      Tendsto μ atTop (𝓝 ν) :=
    (ProbabilityTheory.tendsto_iff_finiteDimensionalDistribution_tendsto_and_isTight ν μ).mp
      ⟨hfdd, hTightRange⟩
  simpa [μ, ν] using hWeak

namespace ProbabilityTheory

/-- Theorem 21.43: once the linearly interpolated path laws in Donsker's theorem have the Brownian
finite-dimensional limits and satisfy the tightness hypotheses from Theorem 21.42, the full path
laws converge weakly in `C([0, ∞), ℝ)`. -/
theorem donskerInterpolatedPathLaw_tendsto_brownianPathLaw
    {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : ProbabilityMeasure Ω)
    (Sbar : ℕ → Ω → BrownianPathSpace)
    (hSbar : ∀ n, Measurable (Sbar n))
    (PW : ProbabilityMeasure Ω')
    (W : Ω' → BrownianPathSpace)
    (hW : Measurable W)
    (hfdd :
      ∀ m : ℕ, ∀ times : Fin (m + 1) → NNReal,
        Tendsto
          (fun n ↦
            ProbabilityTheory.continuousPathFiniteDimensionalDistribution
              (P.map (hSbar n).aemeasurable) times)
          atTop
          (𝓝
            (ProbabilityTheory.continuousPathFiniteDimensionalDistribution
              (PW.map hW.aemeasurable) times)))
    (h0_tight :
      initial_value_laws_tight (fun n ↦ P.map (hSbar n).aemeasurable))
    (hmoment :
      ∀ N : NNReal, 0 < N →
        ∃ α β C : NNReal,
          ∀ n,
            IsKolmogorovProcessOnIcc
              (P : Measure Ω) (fun t ω ↦ Sbar n ω t) N α β C) :
    Tendsto
      (fun n ↦ P.map (hSbar n).aemeasurable)
      atTop
      (𝓝 (PW.map hW.aemeasurable)) := by
  -- Proof comment: this is the labeled Donsker wrapper around the local criterion theorem above.
  exact
    donskerPathLaw_tendsto_of_fdd_and_kolmogorovCriterion
      P
      Sbar
      hSbar
      PW
      W
      hW
      hfdd
      h0_tight
      hmoment

end ProbabilityTheory
