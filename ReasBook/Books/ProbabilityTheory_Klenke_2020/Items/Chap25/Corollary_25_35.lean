/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Corollary_25_35.Ito

open Filter MeasureTheory ProbabilityTheory
open Laplacian InnerProductSpace
open scoped BigOperators ENNReal ProbabilityTheory Topology InnerProductSpace

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {d : ℕ}

/-- Corollary 25.35 (Time-dependent Ito formula): if `F ∈ C^{2,1}(ℝ^d × ℝ)` and `W` is a standard
`d`-dimensional Brownian motion, then for each deterministic horizon `T` the fixed-time identity
for `W` itself holds almost surely. -/
theorem corollary_25_35_owner_entry
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hF : IsTimeSpaceC21 F)
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) :
    (fun ω ↦
      F (W T ω, (T : ℝ)) - F (W 0 ω, 0)) =ᵐ[μ]
      (fun ω ↦
        (∑ i : Fin d, standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω) +
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            (∂ₜ F) (W s.toNNReal ω, s) +
              ((1 : ℝ) / 2) *
                Δ (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                  (W s.toNNReal ω))) := by
  -- Route correction: the owner file should expose the labelled corollary entry and reuse the
  -- already-proved support theorem instead of carrying a placeholder statement.
  -- Proof comment: the support theorem already has the exact fixed-time Ito formula, so the owner
  -- entry closes by re-exporting that theorem with the same parameters.
  simpa using brownian_time_dependent_ito_formula_ae_eq
    (μ := μ) (d := d) (F := F) (W := W) hF hW T

end ProbabilityTheory
