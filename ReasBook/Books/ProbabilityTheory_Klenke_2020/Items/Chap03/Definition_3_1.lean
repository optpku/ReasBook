/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

/-- The real-valued power-series extension of the probability generating function of a law on
`ℕ`. -/
noncomputable abbrev probabilityGeneratingFunctionReal (p : PMF ℕ) (z : ℝ) : ℝ :=
  ∑' n : ℕ, (p n).toReal * z ^ n

/-- The real-valued pgf evaluates to its defining power series. -/
theorem probabilityGeneratingFunctionReal_apply (p : PMF ℕ) (z : ℝ) :
    probabilityGeneratingFunctionReal p z = ∑' n : ℕ, (p n).toReal * z ^ n := by
  rfl

/-- The real-valued pgf takes nonnegative values on the unit interval. -/
theorem probabilityGeneratingFunctionReal_nonneg (p : PMF ℕ) (z : Set.Icc (0 : ℝ) 1) :
    0 ≤ probabilityGeneratingFunctionReal p z := by
  refine tsum_nonneg ?_
  intro n
  exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg z.2.1 n)

/-- The real-valued pgf is bounded above by `1` on the unit interval. -/
theorem probabilityGeneratingFunctionReal_le_one (p : PMF ℕ) (z : Set.Icc (0 : ℝ) 1) :
    probabilityGeneratingFunctionReal p z ≤ 1 := by
  have hp_summable : Summable (fun n : ℕ ↦ (p n).toReal) := by
    simpa using ENNReal.summable_toReal p.tsum_coe_ne_top
  have hpgf_summable : Summable (fun n : ℕ ↦ (p n).toReal * (z : ℝ) ^ n) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ ↦ (p n).toReal) ?_ ?_ hp_summable
    · intro n
      exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg z.2.1 n)
    · intro n
      exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ z.2.1 z.2.2)
  have hp_tsum : ∑' n : ℕ, (p n).toReal = 1 := by
    rw [← ENNReal.toReal_one, ← p.tsum_coe, ENNReal.tsum_toReal_eq]
    intro n
    exact p.apply_ne_top n
  calc
    probabilityGeneratingFunctionReal p z = ∑' n : ℕ, (p n).toReal * (z : ℝ) ^ n := rfl
    _ ≤ ∑' n : ℕ, (p n).toReal :=
      hpgf_summable.tsum_le_tsum
        (fun n ↦ mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ z.2.1 z.2.2))
        hp_summable
    _ = 1 := hp_tsum

/-- The real-valued pgf maps the unit interval into itself. -/
theorem probabilityGeneratingFunctionReal_mem_unitInterval (p : PMF ℕ) (z : Set.Icc (0 : ℝ) 1) :
    probabilityGeneratingFunctionReal p z ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨probabilityGeneratingFunctionReal_nonneg p z, probabilityGeneratingFunctionReal_le_one p z⟩

/-- Definition 3.1: For an `ℕ`-valued law `p`, its probability generating function is the map
`z ↦ ∑' n, P[X = n] z^n` from `[0,1]` to `[0,1]`, with the convention `0^0 = 1`. -/
noncomputable def probabilityGeneratingFunction (p : PMF ℕ) :
    Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 :=
  fun z ↦
    ⟨probabilityGeneratingFunctionReal p z, probabilityGeneratingFunctionReal_mem_unitInterval p z⟩

/-- On `[0,1]`, the subtype-valued pgf is the real-valued pgf with its range restricted back to
`[0,1]`. -/
theorem probabilityGeneratingFunction_coe_eq_real (p : PMF ℕ) (z : Set.Icc (0 : ℝ) 1) :
    (probabilityGeneratingFunction p z : ℝ) = probabilityGeneratingFunctionReal p z := by
  rfl

/-- The probability generating function evaluates to the defining power series of the law. -/
theorem probabilityGeneratingFunction_apply (p : PMF ℕ) (z : Set.Icc (0 : ℝ) 1) :
    (probabilityGeneratingFunction p z : ℝ) =
      ∑' n : ℕ, (p n).toReal * (z : ℝ) ^ n := by
  rw [probabilityGeneratingFunction_coe_eq_real, probabilityGeneratingFunctionReal_apply]
