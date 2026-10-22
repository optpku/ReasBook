/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Theorem_4_26
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Exercise_5_3_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_28

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- Helper for Theorem 5.32: the weighted complete-convergence series from the Baum--Katz
criterion for the textbook sequence `X₁, X₂, …`. -/
def baumKatzSeries (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (γ : ℝ) : Prop :=
  ∀ ⦃ε : ℝ⦄, 0 < ε →
    Summable fun n : ℕ ↦
      Real.rpow (((n + 1 : ℕ) : ℝ)) (γ - 2) *
        (P {ω | ε < |partialSum (fun k ↦ X (k + 1)) (n + 1) ω| / (n + 1 : ℝ)}).toReal

/-- Helper for Theorem 5.32: the `γ`-moment and centering condition on the common law of the
textbook i.i.d. sequence `X₁, X₂, …`. -/
def baumKatzMomentCondition
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (γ : ℝ) : Prop :=
  MemLp (X 1) (ENNReal.ofReal γ) P ∧ P[X 1] = 0

/-- Theorem 5.32: Baum and Katz (1965). For a textbook i.i.d. real sequence `X₁, X₂, …`, this is
the chapter-level proposition asserting that the weighted complete-convergence series
`∑ n^(γ - 2) P[|Sₙ| / n > ε]` is finite for every `ε > 0` exactly when `X₁` has finite `γ`th
absolute moment and mean `0`. -/
def baum_katz_complete_convergence_iff_integrable_abs_rpow_and_mean_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (γ : ℝ) : Prop :=
  (1 < γ ∧ IsIID (fun n ↦ X (n + 1)) P) →
    (baumKatzSeries P X γ ↔ baumKatzMomentCondition P X γ)
