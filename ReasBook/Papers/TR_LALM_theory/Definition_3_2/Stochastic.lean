/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Definition_2_2.KKT
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace KKT.Stochastic

universe u

variable {n m : ℕ} {Ω : Type u} [MeasurableSpace Ω]

/-- The expected squared extended norm of the stochastic stationarity vector. -/
@[expose] noncomputable def stationarityMeanSquare
    (ℙ : Measure Ω) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : Ω → EuclideanSpace ℝ (Fin n))
    (multiplier : Ω → EuclideanSpace ℝ (Fin m)) : ℝ≥0∞ :=
  ∫⁻ ω, ‖KKT.stationarity f c (x ω) (multiplier ω)‖ₑ ^ 2 ∂ℙ

/-- The stationarity mean square is the extended integral of the squared stationarity norm. -/
theorem stationarityMeanSquare_def
    (ℙ : Measure Ω) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : Ω → EuclideanSpace ℝ (Fin n))
    (multiplier : Ω → EuclideanSpace ℝ (Fin m)) :
    stationarityMeanSquare ℙ f c x multiplier =
      ∫⁻ ω, ‖KKT.stationarity f c (x ω) (multiplier ω)‖ₑ ^ 2 ∂ℙ := rfl

/-- The expected squared extended norm of the stochastic feasibility vector. -/
@[expose] noncomputable def feasibilityMeanSquare
    (ℙ : Measure Ω) (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : Ω → EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ∫⁻ ω, ‖c (x ω)‖ₑ ^ 2 ∂ℙ

/-- The feasibility mean square is the extended integral of the squared feasibility norm. -/
theorem feasibilityMeanSquare_def
    (ℙ : Measure Ω) (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : Ω → EuclideanSpace ℝ (Fin n)) :
    feasibilityMeanSquare ℙ c x = ∫⁻ ω, ‖c (x ω)‖ₑ ^ 2 ∂ℙ := rfl

/-- The expected square of the aggregate stochastic KKT residual. -/
@[expose] noncomputable def residualMeanSquare
    (ℙ : Measure Ω) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : Ω → EuclideanSpace ℝ (Fin n))
    (multiplier : Ω → EuclideanSpace ℝ (Fin m)) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (KKT.residual f c (x ω) (multiplier ω) ^ 2) ∂ℙ

/-- The residual mean square is the extended integral of the squared aggregate residual. -/
theorem residualMeanSquare_def
    (ℙ : Measure Ω) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : Ω → EuclideanSpace ℝ (Fin n))
    (multiplier : Ω → EuclideanSpace ℝ (Fin m)) :
    residualMeanSquare ℙ f c x multiplier =
      ∫⁻ ω, ENNReal.ofReal (KKT.residual f c (x ω) (multiplier ω) ^ 2) ∂ℙ := rfl

/-- A stochastic approximate KKT pair on a fixed probability space. -/
structure IsApproximatePair
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ε : ℝ≥0) (x : Ω → EuclideanSpace ℝ (Fin n))
    (multiplier : Ω → EuclideanSpace ℝ (Fin m)) : Prop where
  /-- The stochastic point is a random variable up to `ℙ`-null sets. -/
  aemeasurable_point : AEMeasurable x ℙ
  /-- The stochastic multiplier is a random variable up to `ℙ`-null sets. -/
  aemeasurable_multiplier : AEMeasurable multiplier ℙ
  /-- The stationarity mean square is at most `ε ^ 2`. -/
  stationarityMeanSquare_le :
    stationarityMeanSquare ℙ f c x multiplier ≤ ε ^ 2
  /-- The feasibility mean square is at most `ε ^ 2`. -/
  feasibilityMeanSquare_le : feasibilityMeanSquare ℙ c x ≤ ε ^ 2

namespace IsApproximatePair

/-- Construct a stochastic approximate KKT pair from measurability and its two bounds. -/
theorem ofBounds
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {ε : ℝ≥0}
    {x : Ω → EuclideanSpace ℝ (Fin n)}
    {multiplier : Ω → EuclideanSpace ℝ (Fin m)}
    (aemeasurable_point : AEMeasurable x ℙ)
    (aemeasurable_multiplier : AEMeasurable multiplier ℙ)
    (stationarityMeanSquare_le :
      stationarityMeanSquare ℙ f c x multiplier ≤ ε ^ 2)
    (feasibilityMeanSquare_le : feasibilityMeanSquare ℙ c x ≤ ε ^ 2) :
    IsApproximatePair ℙ f c ε x multiplier :=
  ⟨aemeasurable_point, aemeasurable_multiplier, stationarityMeanSquare_le,
    feasibilityMeanSquare_le⟩

end IsApproximatePair

/-- A stochastic approximate KKT pair is characterized by randomness and its two bounds. -/
theorem isApproximatePair_iff
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ε : ℝ≥0) (x : Ω → EuclideanSpace ℝ (Fin n))
    (multiplier : Ω → EuclideanSpace ℝ (Fin m)) :
    IsApproximatePair ℙ f c ε x multiplier ↔
      (AEMeasurable x ℙ ∧ AEMeasurable multiplier ℙ) ∧
        (stationarityMeanSquare ℙ f c x multiplier ≤ ε ^ 2 ∧
          feasibilityMeanSquare ℙ c x ≤ ε ^ 2) :=
  ⟨fun h ↦ ⟨⟨h.aemeasurable_point, h.aemeasurable_multiplier⟩,
      ⟨h.stationarityMeanSquare_le, h.feasibilityMeanSquare_le⟩⟩,
    fun h ↦ ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩⟩

/-- A stochastic approximate KKT point has a random multiplier on the same probability space. -/
def IsApproximatePoint
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ε : ℝ≥0) (x : Ω → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ multiplier : Ω → EuclideanSpace ℝ (Fin m),
    IsApproximatePair ℙ f c ε x multiplier

/-- The stochastic approximate KKT point predicate exposes its random multiplier. -/
theorem isApproximatePoint_iff
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ε : ℝ≥0) (x : Ω → EuclideanSpace ℝ (Fin n)) :
    IsApproximatePoint ℙ f c ε x ↔
      ∃ multiplier : Ω → EuclideanSpace ℝ (Fin m),
        IsApproximatePair ℙ f c ε x multiplier := Iff.rfl

/-- Helper for Definition 3.2: the squared aggregate residual is the sum of the
squared extended norms of its stationarity and feasibility components. -/
lemma ofReal_residual_sq
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (multiplier : EuclideanSpace ℝ (Fin m)) :
    ENNReal.ofReal (KKT.residual f c x multiplier ^ 2) =
      ‖KKT.stationarity f c x multiplier‖ₑ ^ 2 + ‖c x‖ₑ ^ 2 := by
  -- First remove the square root using nonnegativity of both squared components.
  rw [KKT.residual_def, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  -- The extended-real embedding then preserves the component sum and squares.
  rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm, ofReal_norm]

namespace IsApproximatePair

/-- Stochastic approximate KKT pairs are invariant under a.e.-equal representatives. -/
theorem congr
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {ε : ℝ≥0}
    {x x' : Ω → EuclideanSpace ℝ (Fin n)}
    {multiplier multiplier' : Ω → EuclideanSpace ℝ (Fin m)}
    (h : IsApproximatePair ℙ f c ε x multiplier)
    (hx : x =ᵐ[ℙ] x') (hmultiplier : multiplier =ᵐ[ℙ] multiplier') :
    IsApproximatePair ℙ f c ε x' multiplier' := by
  -- Transport randomness to the chosen a.e.-equal representatives.
  refine ofBounds (h.aemeasurable_point.congr hx)
    (h.aemeasurable_multiplier.congr hmultiplier) ?_ ?_
  · -- Transport the stationarity integrand using both representative equalities.
    calc
      stationarityMeanSquare ℙ f c x' multiplier' =
          ∫⁻ ω, ‖KKT.stationarity f c (x' ω) (multiplier' ω)‖ₑ ^ 2 ∂ℙ :=
        stationarityMeanSquare_def ℙ f c x' multiplier'
      _ = ∫⁻ ω, ‖KKT.stationarity f c (x ω) (multiplier ω)‖ₑ ^ 2 ∂ℙ := by
        exact lintegral_congr_ae
          (hx.comp₂ (fun point dual ↦ ‖KKT.stationarity f c point dual‖ₑ ^ 2)
            hmultiplier).symm
      _ = stationarityMeanSquare ℙ f c x multiplier :=
        (stationarityMeanSquare_def ℙ f c x multiplier).symm
      _ ≤ ε ^ 2 := h.stationarityMeanSquare_le
  · -- Transport the feasibility integrand using the point equality alone.
    calc
      feasibilityMeanSquare ℙ c x' = ∫⁻ ω, ‖c (x' ω)‖ₑ ^ 2 ∂ℙ :=
        feasibilityMeanSquare_def ℙ c x'
      _ = ∫⁻ ω, ‖c (x ω)‖ₑ ^ 2 ∂ℙ := by
        exact lintegral_congr_ae
          (hx.fun_comp (fun point ↦ ‖c point‖ₑ ^ 2)).symm
      _ = feasibilityMeanSquare ℙ c x :=
        (feasibilityMeanSquare_def ℙ c x).symm
      _ ≤ ε ^ 2 := h.feasibilityMeanSquare_le

end IsApproximatePair

namespace IsApproximatePoint

/-- Stochastic approximate KKT points are invariant under a.e.-equal representatives. -/
theorem congr
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {ε : ℝ≥0}
    {x x' : Ω → EuclideanSpace ℝ (Fin n)}
    (h : IsApproximatePoint ℙ f c ε x) (hx : x =ᵐ[ℙ] x') :
    IsApproximatePoint ℙ f c ε x' := by
  -- Reuse the same multiplier and transport its pair certificate along `hx`.
  obtain ⟨multiplier, hpair⟩ := h
  refine ⟨multiplier, hpair.congr hx ae_eq_rfl⟩

end IsApproximatePoint

end KKT.Stochastic

end
