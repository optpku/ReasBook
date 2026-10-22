/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap22.Theorem_22_5

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

/-- Corollary 22.7: the common law of a centered square-integrable iid real sequence admits a
Skorohod embedding on a suitable probability space. -/
theorem exists_centered_iid_skorohod_embedding
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_memLp : MemLp (X 1) 2 P) :
    ∃ (Ω' : Type) (_mΩ' : MeasurableSpace Ω') (Q : ProbabilityMeasure Ω')
      (Ξ : Ω' → ℝ) (B : NNReal → Ω' → ℝ) (τ : Ω' → NNReal),
      Ξ ⟂ᵢ[(Q : Measure Ω')] (fun ω t ↦ B t ω) ∧
      IsBrownianMotion (Q : Measure Ω') B ∧
      IsStoppingTime (processFiltration (fun s ω ↦ (Ξ ω, B s ω)))
        (fun ω ↦ (τ ω : WithTop NNReal)) ∧
      HasLaw (stoppedValue B (fun ω ↦ (τ ω : WithTop NNReal))) (P.map (X 1))
        (Q : Measure Ω') ∧
      (Q : Measure Ω')[fun ω ↦ (τ ω : ℝ)] = Var[X 1; P] := by
  have hX1_ae : AEMeasurable (X 1) P := (hX_iid.identDistrib 0 0).aemeasurable_fst
  haveI : IsProbabilityMeasure (P.map (X 1)) := Measure.isProbabilityMeasure_map hX1_ae
  let μ : ProbabilityMeasure ℝ := ⟨P.map (X 1), inferInstance⟩
  have hμ_mean_zero : ∫ x, x ∂(μ : Measure ℝ) = 0 := by
    change ∫ x, id x ∂(P.map (X 1)) = 0
    -- Proof comment: the pushforward expectation of `id` is the original expectation of `X 1`.
    rw [integral_map hX1_ae aestronglyMeasurable_id]
    simpa using hX_mean
  have hμ_memLp : MemLp id 2 (μ : Measure ℝ) := by
    change MemLp id 2 (P.map (X 1))
    -- Proof comment: the square-integrability of `X 1` transfers directly to its law.
    simpa using (memLp_map_measure_iff aestronglyMeasurable_id hX1_ae).2 hX_memLp
  have hμ_var :
      Var[id; (μ : Measure ℝ)] = Var[X 1; P] := by
    change Var[id; P.map (X 1)] = Var[X 1; P]
    -- Proof comment: variance is invariant under passing to the pushforward law.
    simpa [Function.comp] using
      (variance_map (X := id) (μ := P) (Y := X 1) aemeasurable_id hX1_ae)
  rcases exists_skorohod_embedding μ hμ_mean_zero hμ_memLp with
    ⟨Ω', mΩ', Q, Ξ, B, τ, hIndep, hBrownian, hStop, hLaw, hMean⟩
  refine ⟨Ω', mΩ', Q, Ξ, B, τ, hIndep, hBrownian, hStop, ?_, ?_⟩
  · simpa [μ] using hLaw
  · simpa [hμ_var] using hMean

end ProbabilityTheory
