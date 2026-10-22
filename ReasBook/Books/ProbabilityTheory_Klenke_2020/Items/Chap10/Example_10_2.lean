/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Definition_10_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} {m0 : MeasurableSpace Ω}
variable {μ : Measure Ω} {ℱ : Filtration ℕ m0}

section

variable {X : ℕ → Ω → ℝ}

local notation "squareProcess" => fun n ω ↦ (X n ω) ^ 2

-- Proof sketch: apply the canonical Doob decomposition construction to the squared process
-- `n ↦ X n ^ 2`. Its predictable part is predictable and starts at `0`, while the compensated
-- process `X_n^2 - ⟨X⟩_n` is the canonical martingale part of the squared process.
/-- For a square-integrable discrete-time martingale `X`, subtracting the canonical square
variation `⟨X⟩` from the squared process yields a martingale. -/
theorem square_sub_squareVariation_martingale [SigmaFiniteFiltration μ ℱ]
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) :
    Martingale (fun n ω ↦ X n ω ^ 2 - (⟨X⟩[ℱ, μ]) n ω) ℱ μ := by
  have hSquare_adapted : Adapted ℱ squareProcess := by
    change Adapted ℱ (fun n ω ↦ (X n ω) ^ 2)
    simpa [pow_two] using
      (hX.stronglyAdapted.mul hX.stronglyAdapted).adapted
  rcases canonical_doobDecomposition hSquare_adapted hXsq with
    ⟨-, -, hMartingale, -⟩
  simpa [martingalePart] using hMartingale

-- Proof sketch: combine the canonical owner facts `squareVariation_zero`,
-- `squareVariation_predictable`, and `square_sub_squareVariation_martingale`.
/-- Example 10.2: for a square-integrable discrete-time martingale `X`, the canonical square
variation `⟨X⟩` realizes the textbook square-variation process of `X`. -/
theorem squareVariation_isSquareVariationProcess [SigmaFiniteFiltration μ ℱ]
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) :
    IsSquareVariationProcess ℱ μ X (⟨X⟩[ℱ, μ]) := by
  exact ⟨squareVariation_zero, squareVariation_predictable,
    square_sub_squareVariation_martingale hX hXsq⟩

end
