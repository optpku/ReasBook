/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped ENNReal BigOperators

private def volume_finiteSpanningSetsIn_ioc :
    (volume : Measure ℝ).FiniteSpanningSetsIn {S : Set ℝ | ∃ l u, l < u ∧ Ioc l u = S} := by
  refine ⟨fun n ↦ Ioc (-((n : ℝ) + 1)) ((n : ℝ) + 1), ?_, ?_, ?_⟩
  · intro n
    refine ⟨-((n : ℝ) + 1), (n : ℝ) + 1, ?_, rfl⟩
    linarith
  · intro n
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  · ext x
    simp only [mem_iUnion, mem_Ioc, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    refine ⟨n, ?_, ?_⟩
    · have hx : -|x| ≤ x := neg_abs_le x
      linarith
    · have hx : x ≤ |x| := le_abs_self x
      linarith

-- Proof sketch: `MeasureTheory.volume` is the canonical witness, and `Real.volume_pi_Ioc`
-- supplies the rectangle formula. For uniqueness, identify `volume` with the product measure
-- `Measure.pi (fun _ ↦ volume)` via `MeasureTheory.volume_pi`, then apply
-- `Measure.pi_eq_generateFrom` on the generating `π`-system of half-open intervals in each
-- coordinate, using explicit finite spanning intervals for the one-dimensional volume measure.
/-- Theorem 1.55: There exists a unique measure on `ℝ^n`, represented as `Fin n → ℝ`, whose value
on each half-open rectangle `(a, b]` is the product of the side lengths. This is the Lebesgue
measure on `(ℝ^n, B(ℝ^n))`. -/
theorem existsUnique_lebesgue_measure (n : ℕ) :
    ∃! μ : Measure (Fin n → ℝ),
      ∀ a b : Fin n → ℝ, (∀ i, a i < b i) →
        μ (univ.pi fun i ↦ Ioc (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i) := by
  refine ⟨volume, ?_, ?_⟩
  · intro a b hab
    simpa using
      (Real.volume_pi_Ioc :
        volume (univ.pi fun i ↦ Ioc (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i))
  · intro μ hμ
    have hpi : Measure.pi (fun _ : Fin n ↦ (volume : Measure ℝ)) = μ := by
      refine Measure.pi_eq_generateFrom
        (fun _ ↦ ?_) (fun _ ↦ ?_) (fun _ ↦ volume_finiteSpanningSetsIn_ioc) ?_
      · simpa using (borel_eq_generateFrom_Ioc ℝ).symm
      · simpa using (isPiSystem_Ioc (fun x : ℝ ↦ x) fun x : ℝ ↦ x)
      · intro s hs
        choose a b hab hEq using hs
        have hrect : univ.pi s = univ.pi (fun i ↦ Ioc (a i) (b i)) := by
          ext x
          simp [hEq]
        rw [hrect]
        calc
          μ (univ.pi fun i ↦ Ioc (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i) := hμ a b hab
          _ = ∏ i, volume (s i) := by
            congr with i
            rw [← hEq i, Real.volume_Ioc]
    calc
      μ = Measure.pi (fun _ : Fin n ↦ (volume : Measure ℝ)) := hpi.symm
      _ = volume := volume_pi.symm
