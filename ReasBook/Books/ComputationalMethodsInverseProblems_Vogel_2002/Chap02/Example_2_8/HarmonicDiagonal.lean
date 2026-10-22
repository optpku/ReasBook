/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_3.Diagonal
import Mathlib.Analysis.PSeries

public section

open scoped ENNReal

noncomputable section

namespace RealL2

/-- The harmonic coefficient sequence `n ↦ 1 / ((n : ℝ) + 1)` as an element of `lp ... ∞`. -/
def harmonicWeights : lp (fun _ : ℕ ↦ ℝ) ∞ :=
  ⟨fun n ↦ 1 / ((n : ℝ) + 1), by
    refine memℓp_infty ?_
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    change ‖(1 / ((n : ℝ) + 1) : ℝ)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith
    simpa using
      (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hden)⟩

/-- The harmonic coefficient sequence has coordinate `1 / ((n : ℝ) + 1)` at `n`. -/
theorem harmonicWeights_apply (n : ℕ) :
    harmonicWeights n = 1 / ((n : ℝ) + 1) := by
  simp [harmonicWeights]

/-- The harmonic diagonal operator from Example 2.8. -/
noncomputable def harmonicDiagonal :
    lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  diagonal harmonicWeights

/-- The diagonal operator from Example 2.8 acts by multiplying the `n`th coordinate by
`1 / ((n : ℝ) + 1)`. -/
theorem harmonicDiagonal_apply (f : lp (fun _ : ℕ ↦ ℝ) 2) (n : ℕ) :
    harmonicDiagonal f n = (1 / ((n : ℝ) + 1)) * f n := by
  simpa [harmonicDiagonal, harmonicWeights_apply] using diagonal_apply harmonicWeights f n

/-- The explicit datum `g = (1, 1 / 2, 1 / 3, ...)` as an element of real `ℓ²`. -/
def harmonicDatum : lp (fun _ : ℕ ↦ ℝ) 2 :=
  ⟨fun n ↦ 1 / ((n : ℝ) + 1), by
    refine memℓp_gen ?_
    have hsAbs : Summable (fun n : ℕ ↦ 1 / |(n : ℝ) + 1| ^ (2 : ℝ)) :=
      (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
    refine hsAbs.congr ?_
    intro n
    have hden_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
    simp [Real.norm_eq_abs, abs_of_nonneg hden_nonneg]⟩

/-- The explicit datum `harmonicDatum` has coordinate `1 / ((n : ℝ) + 1)` at `n`. -/
theorem harmonicDatum_apply (n : ℕ) :
    harmonicDatum n = 1 / ((n : ℝ) + 1) := by
  simp [harmonicDatum]

/-- The basis-vector sequence `n ↦ δ_n` in real `ℓ²`. -/
def deltaSequence (n : ℕ) : lp (fun _ : ℕ ↦ ℝ) 2 :=
  lp.single 2 n (1 : ℝ)

/-- The basis-vector sequence has coordinate `1` at its index and `0` elsewhere. -/
theorem deltaSequence_apply (n j : ℕ) :
    deltaSequence n j = if j = n then 1 else 0 := by
  by_cases h : j = n
  · subst h
    simp [deltaSequence]
  · simp [deltaSequence, h]

/-- The harmonic diagonal sends `deltaSequence n` to the correspondingly scaled basis vector. -/
theorem harmonicDiagonal_deltaSequence (n : ℕ) :
    harmonicDiagonal (deltaSequence n) = lp.single 2 n (1 / ((n : ℝ) + 1)) := by
  simpa [harmonicDiagonal, deltaSequence, harmonicWeights_apply] using
    diagonal_single harmonicWeights n (1 : ℝ)

end RealL2
