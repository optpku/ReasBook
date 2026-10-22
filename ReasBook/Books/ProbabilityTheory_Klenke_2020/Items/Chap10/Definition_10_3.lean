/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-
Definition 10.3 is `source-facing`: for a square-integrable discrete-time real martingale `X`,
its square variation is the canonical predictable compensator of the squared process. The
`core/canonical` owner layer is mathlib's `predictablePart`; the predicate
`IsSquareVariationProcess` below is only a thin `bridge/view` for source-style witness statements.
-/
scoped notation "⟨" X "⟩[" ℱ ", " μ "]" =>
  predictablePart (fun n ω ↦ X n ω ^ 2) ℱ μ

variable {ℱ : Filtration ℕ mΩ} {μ : Measure Ω} {X A : ℕ → Ω → ℝ}

/-- The canonical square variation starts at `0`. -/
@[simp] theorem squareVariation_zero : ⟨X⟩[ℱ, μ] 0 = 0 :=
  predictablePart_zero

/-- The canonical square variation is predictable. -/
theorem squareVariation_predictable : IsPredictable ℱ ⟨X⟩[ℱ, μ] := by
  refine isPredictable_of_measurable_add_one ?_ ?_
  · simpa using
      (stronglyMeasurable_zero : StronglyMeasurable[ℱ 0] (0 : Ω → ℝ)).measurable
  · intro n
    simpa using
      ((stronglyAdapted_predictablePart :
          StronglyAdapted ℱ
            (fun k ↦ predictablePart (fun m ω ↦ X m ω ^ 2) ℱ μ (k + 1))) n).measurable

/-- A process `A` is a source-style square-variation witness for `X` if it starts at `0`, is
predictable, and its compensated square process is a martingale. The canonical square variation
itself is `⟨X⟩[ℱ, μ]`. -/
def IsSquareVariationProcess (ℱ : Filtration ℕ mΩ) (μ : Measure Ω)
    (X A : ℕ → Ω → ℝ) : Prop :=
  A 0 = 0 ∧
    IsPredictable ℱ A ∧
    Martingale (fun n ω ↦ X n ω ^ 2 - A n ω) ℱ μ

namespace IsSquareVariationProcess

/-- A square-variation process starts at `0`. -/
theorem zero (hA : IsSquareVariationProcess ℱ μ X A) : A 0 = 0 := by
  rcases hA with ⟨h0, -, -⟩
  exact h0

/-- A square-variation process is predictable. -/
theorem predictable (hA : IsSquareVariationProcess ℱ μ X A) : IsPredictable ℱ A := by
  rcases hA with ⟨-, hpred, -⟩
  exact hpred

/-- For a square-variation process, the compensated square process is a martingale. -/
theorem martingale_sq_sub (hA : IsSquareVariationProcess ℱ μ X A) :
    Martingale (fun n ω ↦ X n ω ^ 2 - A n ω) ℱ μ := by
  rcases hA with ⟨-, -, hm⟩
  exact hm

-- Proof sketch: write `X_n^2` as the sum of the compensated square martingale and the
-- predictable process `A`, then apply the uniqueness of the canonical predictable part from the
-- Doob decomposition machinery.
/-- Any square-variation witness agrees almost everywhere at each fixed time with the canonical
square variation `⟨X⟩[ℱ, μ]`. This is the owner-bridge from the source-style witness predicate to
mathlib's `predictablePart`. -/
theorem predictablePart_sq_ae_eq [SigmaFiniteFiltration μ ℱ]
    (hA : IsSquareVariationProcess ℱ μ X A)
    (hXsq : ∀ n, Integrable (fun ω ↦ X n ω ^ 2) μ) :
    ∀ n, ⟨X⟩[ℱ, μ] n =ᵐ[μ] A n := by
  let M : ℕ → Ω → ℝ := fun n ω ↦ X n ω ^ 2 - A n ω
  have hM : Martingale M ℱ μ := hA.martingale_sq_sub
  have hA_adapted : Adapted ℱ fun n ↦ A (n + 1) :=
    fun n ↦ IsPredictable.measurable_add_one hA.predictable n
  have hA_stronglyAdapted : StronglyAdapted ℱ fun n ↦ A (n + 1) :=
    hA_adapted.stronglyAdapted
  have hA_int : ∀ n, Integrable (A n) μ := by
    intro n
    have hA_eq : A n = fun ω ↦ X n ω ^ 2 - M n ω := by
      ext ω
      simp [M]
    rw [hA_eq]
    exact (hXsq n).sub (hM.integrable n)
  intro n
  have h_predictable :
      A n =ᵐ[μ] predictablePart (M + A) ℱ μ n :=
    (predictablePart_add_ae_eq hM hA_stronglyAdapted hA.zero hA_int n).symm
  have hMA : M + A = fun n ω ↦ X n ω ^ 2 := by
    ext k ω
    simp [M]
  simpa [hMA] using h_predictable.symm

end IsSquareVariationProcess

end ProbabilityTheory
