/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Theorem_23_11Shim

open Filter MeasureTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Theorem 23.11: an i.i.d. family is almost everywhere measurable in each
coordinate. -/
private theorem aemeasurable_of_isIID
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX_iid : IsIID X P) :
    ∀ n, AEMeasurable (X n) P := by
  -- Proof comment: each coordinate has the same law as `X 0`, so a.e.-measurability transfers
  -- from the first projection along the identical-distribution witnesses.
  intro n
  exact (hX_iid.identDistrib n 0).aemeasurable_fst

/-- Helper for Theorem 23.11: the empirical-mean speed at index `n` is `(n + 1)⁻¹`. -/
private theorem empiricalMeanSpeed_pos (n : ℕ) : 0 < (n + 1 : ℝ)⁻¹ := by
  have hn : 0 < (n + 1 : ℝ) := by
    positivity
  simpa using inv_pos.mpr hn

/-- Helper for Theorem 23.11: the empirical-mean speed family used in the textbook statement. -/
private noncomputable def empiricalMeanSpeed : ℕ → PositiveParameter :=
  fun n ↦ ⟨((n + 1 : ℝ)⁻¹), empiricalMeanSpeed_pos n⟩

/-- Theorem 23.11: if `X₁, X₂, …` are i.i.d. real random variables, then the empirical-mean laws
satisfy a large deviations principle with rate function `Λ*`. -/
theorem empiricalMean_hasLargeDeviationsPrinciple
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) :
    HasLargeDeviationsPrincipleAlong
      (empiricalMeanLaw X P (aemeasurable_of_isIID hX_iid))
      empiricalMeanSpeed
      atTop
      (fun x ↦ (legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal) := by
  -- Proof comment: the full Cramér proof is provided by the shim owner theorem; this wrapper
  -- restores the label-bearing textbook declaration in the chapter file.
  simpa [empiricalMeanSpeed] using
    cramer_empiricalMean_largeDeviationPrinciple (P := P) (X := X) hX_iid

end ProbabilityTheory
