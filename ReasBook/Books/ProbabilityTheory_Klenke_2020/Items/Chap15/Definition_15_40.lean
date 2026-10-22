/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_39

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

namespace RealRandomVariableArray

/-- The Lindeberg quantity `Lₙ(ε)` attached to the `n`-th row of a real random-variable array. -/
def lindebergFunction (A : RealRandomVariableArray Ω) (μ : Measure Ω) (ε : ℝ) (n : ℕ) : ℝ :=
  (Var[A.rowSum n; μ])⁻¹ *
    ∑ i : Fin (A.rowLength n),
      μ[Set.indicator
        {ω | ε ^ 2 * Var[A.rowSum n; μ] < (A n i ω) ^ 2}
        (fun ω ↦ (A n i ω) ^ 2)]

-- Proof sketch: unfold `lindebergFunction`; this is exactly the defining normalized truncated
-- second-moment sum.
/-- The Lindeberg quantity is the variance-normalized sum of the truncated second moments in the
`n`-th row. -/
theorem lindebergFunction_def (A : RealRandomVariableArray Ω) (μ : Measure Ω) (ε : ℝ) (n : ℕ) :
    A.lindebergFunction μ ε n =
      (Var[A.rowSum n; μ])⁻¹ *
        ∑ i : Fin (A.rowLength n),
          μ[Set.indicator
            {ω | ε ^ 2 * Var[A.rowSum n; μ] < (A n i ω) ^ 2}
            (fun ω ↦ (A n i ω) ^ 2)] := rfl

/-- The Lyapunov quantity attached to the `n`-th row and exponent `δ` of a real random-variable
array, written in the canonical extended-real form so nonintegrable `(2 + δ)`-moments contribute
`∞` rather than collapsing to `0`. -/
def lyapunovFunction (A : RealRandomVariableArray Ω) (μ : Measure Ω) (δ : ℝ) (n : ℕ) : ENNReal :=
  (ENNReal.ofReal (Real.rpow (Var[A.rowSum n; μ]) (1 + δ / 2)))⁻¹ *
    ∑ i : Fin (A.rowLength n),
      ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂μ

-- Proof sketch: unfold `lyapunovFunction`; this is exactly the defining normalized
-- `(2 + δ)`-moment sum in its extended-real form.
/-- The Lyapunov quantity is the variance-normalized sum of the absolute `(2 + δ)`-moments in the
`n`-th row, expressed as extended moments. -/
theorem lyapunovFunction_def (A : RealRandomVariableArray Ω) (μ : Measure Ω) (δ : ℝ) (n : ℕ) :
    A.lyapunovFunction μ δ n =
      (ENNReal.ofReal (Real.rpow (Var[A.rowSum n; μ]) (1 + δ / 2)))⁻¹ *
        ∑ i : Fin (A.rowLength n),
          ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂μ := rfl

/-- Definition 15.40 (1): a centered real random-variable array with square-integrable entries
satisfies the Lindeberg condition if for every `ε > 0` the normalized truncated second-moment
quantities `Lₙ(ε)` tend to `0`. -/
class SatisfiesLindebergCondition
    (A : RealRandomVariableArray Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Prop extends A.IsCentered μ where
  memLp_two : ∀ n i, MemLp (A n i) 2 μ
  lindeberg_tendsto :
    ∀ ⦃ε : ℝ⦄, 0 < ε →
      Tendsto (fun n ↦ A.lindebergFunction μ ε n) atTop (nhds 0)

/-- Definition 15.40 (2): a centered real random-variable array satisfies the Lyapunov condition
if there exists `δ > 0` such that every entry has finite absolute moment of order `2 + δ` and the
normalized absolute `(2 + δ)`-moment quantities tend to `0`. -/
class SatisfiesLyapunovCondition
    (A : RealRandomVariableArray Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Prop extends A.IsCentered μ where
  exists_delta :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ n i, MemLp (A n i) (ENNReal.ofReal (2 + δ)) μ) ∧
      Tendsto (fun n ↦ A.lyapunovFunction μ δ n) atTop (nhds 0)

namespace SatisfiesLyapunovCondition

/-- The Lyapunov condition carries rowwise finite `(2 + δ)`-moments for one exponent `δ > 0`. -/
theorem exists_finite_moment
    {A : RealRandomVariableArray Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hA : RealRandomVariableArray.SatisfiesLyapunovCondition A μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n i, MemLp (A n i) (ENNReal.ofReal (2 + δ)) μ := by
  rcases hA.exists_delta with ⟨δ, hδ, hMoment, _⟩
  exact ⟨δ, hδ, hMoment⟩

/-- In a probability space, the finite `(2 + δ)`-moment from the Lyapunov condition implies the
square-integrability required elsewhere in the chapter. -/
theorem memLp_two
    {A : RealRandomVariableArray Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hA : RealRandomVariableArray.SatisfiesLyapunovCondition A μ)
    (n : ℕ) (i : Fin (A.rowLength n)) :
    MemLp (A n i) 2 μ := by
  rcases hA.exists_finite_moment with ⟨δ, hδ, hMoment⟩
  refine (hMoment n i).mono_exponent ?_
  simpa using ENNReal.ofReal_le_ofReal (show (2 : ℝ) ≤ 2 + δ by linarith)

end SatisfiesLyapunovCondition

end RealRandomVariableArray
