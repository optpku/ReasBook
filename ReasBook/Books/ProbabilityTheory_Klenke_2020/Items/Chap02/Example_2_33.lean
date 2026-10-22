/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

-- Proof sketch: realize the sum of two independent Poisson random variables via
-- `IndepFun.hasLaw_add`, so its law is the additive convolution `poissonMeasure r ∗
-- poissonMeasure s`. Then identify the point masses of that convolution with the textbook
-- binomial expansion and compare them with the point masses of `poissonMeasure (r + s)`.
/-- Helper for Example 2.33: the singleton mass of `poissonMeasure r` is the explicit Poisson
weight `poissonPMFReal r n`. -/
private lemma poissonMeasure_apply_singleton (r : ℝ≥0) (n : ℕ) :
    poissonMeasure r ({n} : Set ℕ) = ENNReal.ofReal (poissonPMFReal r n) := by
  -- Rewrite the Poisson measure as the measure of its underlying probability mass function.
  simpa [poissonMeasure, poissonPMFReal_ofReal_eq_poissonPMF] using
    (PMF.toMeasure_apply_singleton (poissonPMF r) n (measurableSet_singleton n))

/-- Helper for Example 2.33: the singleton mass of a convolution on `ℕ` is the finite
antidiagonal sum of the singleton masses of the two factors. -/
private lemma conv_apply_singleton_eq_sum_antidiagonal
    {μ ν : Measure ℕ} [SFinite μ] [SFinite ν] (n : ℕ) :
    (μ ∗ ν) ({n} : Set ℕ) =
      Finset.sum (Finset.antidiagonal n) fun p ↦ μ ({p.1} : Set ℕ) * ν ({p.2} : Set ℕ) := by
  -- Unfold convolution and identify the addition fiber over `{n}` with `Finset.antidiagonal n`.
  rw [Measure.conv, Measure.map_apply measurable_add (measurableSet_singleton n)]
  have hpreimage :
      (fun z : ℕ × ℕ ↦ z.1 + z.2) ⁻¹' ({n} : Set ℕ) = ↑(Finset.antidiagonal n) := by
    ext z
    simp [Finset.mem_antidiagonal]
  rw [hpreimage, ← MeasureTheory.sum_measure_singleton (μ := μ.prod ν)
    (s := Finset.antidiagonal n)]
  -- Each singleton mass under the product measure splits as the product of singleton masses.
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hsingleton :
      ({p} : Set (ℕ × ℕ)) = ({p.1} : Set ℕ) ×ˢ ({p.2} : Set ℕ) := by
    ext z
    rcases z with ⟨a, b⟩
    cases p
    simp
  rw [hsingleton]
  exact Measure.prod_prod (μ := μ) (ν := ν) ({p.1} : Set ℕ) ({p.2} : Set ℕ)

/-- Helper for Example 2.33: the antidiagonal Poisson mass sum collapses to the Poisson mass with
parameter `r + s`. -/
private lemma sum_antidiagonal_poissonPMFReal_eq (r s : ℝ≥0) (n : ℕ) :
    Finset.sum (Finset.antidiagonal n) (fun p ↦ poissonPMFReal r p.1 * poissonPMFReal s p.2) =
      poissonPMFReal (r + s) n := by
  -- Convert the antidiagonal sum to the standard binomial sum indexed by `0, ..., n`.
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [poissonPMFReal]
  have hterm :
      ∀ m ∈ Finset.range (n + 1),
        ((r : ℝ) ^ m / ↑m.factorial) * ((s : ℝ) ^ (n - m) / ↑(n - m).factorial) =
          ((n.choose m : ℝ) * ((r : ℝ) ^ m * (s : ℝ) ^ (n - m))) / ↑n.factorial := by
    intro m hm
    have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hmfact : (↑m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hnmfact : (↑(n - m).factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - m))
    have hnfact : (↑n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [Nat.cast_choose ℝ hm']
    field_simp [hmfact, hnmfact, hnfact]
  calc
    ∑ m ∈ Finset.range (n + 1),
        (Real.exp (-↑r) * (r : ℝ) ^ m / ↑m.factorial) *
          (Real.exp (-↑s) * (s : ℝ) ^ (n - m) / ↑(n - m).factorial)
      = ∑ m ∈ Finset.range (n + 1),
          (Real.exp (-↑r) * Real.exp (-↑s)) *
            (((r : ℝ) ^ m / ↑m.factorial) * ((s : ℝ) ^ (n - m) / ↑(n - m).factorial)) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          ring
    _ = (Real.exp (-↑r) * Real.exp (-↑s)) *
          ∑ m ∈ Finset.range (n + 1),
            (((r : ℝ) ^ m / ↑m.factorial) * ((s : ℝ) ^ (n - m) / ↑(n - m).factorial)) := by
          rw [← Finset.mul_sum]
    _ = (Real.exp (-↑r) * Real.exp (-↑s)) *
          ∑ m ∈ Finset.range (n + 1),
            (((n.choose m : ℝ) * ((r : ℝ) ^ m * (s : ℝ) ^ (n - m))) / ↑n.factorial) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [hterm m hm]
    _ = (Real.exp (-↑r) * Real.exp (-↑s)) *
          ((∑ m ∈ Finset.range (n + 1),
              ((n.choose m : ℝ) * ((r : ℝ) ^ m * (s : ℝ) ^ (n - m)))) / ↑n.factorial) := by
          congr 1
          simp_rw [div_eq_mul_inv]
          rw [Finset.sum_mul]
    _ = (Real.exp (-↑r) * Real.exp (-↑s)) * (((r : ℝ) + s) ^ n / ↑n.factorial) := by
          have hpow :
              ∑ m ∈ Finset.range (n + 1),
                ((n.choose m : ℝ) * ((r : ℝ) ^ m * (s : ℝ) ^ (n - m))) =
                  ((r : ℝ) + s) ^ n := by
                rw [show
                    ∑ m ∈ Finset.range (n + 1),
                      ((n.choose m : ℝ) * ((r : ℝ) ^ m * (s : ℝ) ^ (n - m))) =
                        ∑ m ∈ Finset.range (n + 1),
                          ((r : ℝ) ^ m * (s : ℝ) ^ (n - m) * (n.choose m : ℝ)) by
                      refine Finset.sum_congr rfl ?_
                      intro m hm
                      ring]
                simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using
                  (add_pow (r : ℝ) (s : ℝ) n).symm
          exact congrArg
            (fun x : ℝ => (Real.exp (-↑r) * Real.exp (-↑s)) * (x / ↑n.factorial)) hpow
    _ = poissonPMFReal (r + s) n := by
          rw [← Real.exp_add]
          simp [poissonPMFReal, div_eq_mul_inv, add_comm, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Example 2.33: after rewriting singleton masses, the convolution antidiagonal sum is
exactly the Poisson singleton mass with parameter `r + s`. -/
private lemma sum_antidiagonal_poissonMeasure_apply_eq (r s : ℝ≥0) (n : ℕ) :
    Finset.sum (Finset.antidiagonal n)
        (fun p ↦ poissonMeasure r ({p.1} : Set ℕ) * poissonMeasure s ({p.2} : Set ℕ)) =
      poissonMeasure (r + s) ({n} : Set ℕ) := by
  -- Rewrite every singleton mass through `poissonPMFReal` and collapse the resulting real sum.
  calc
    Finset.sum (Finset.antidiagonal n)
        (fun p ↦ poissonMeasure r ({p.1} : Set ℕ) * poissonMeasure s ({p.2} : Set ℕ))
      = Finset.sum (Finset.antidiagonal n)
          (fun p ↦ ENNReal.ofReal (poissonPMFReal r p.1 * poissonPMFReal s p.2)) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [poissonMeasure_apply_singleton, poissonMeasure_apply_singleton,
            ENNReal.ofReal_mul (poissonPMFReal_nonneg : 0 ≤ poissonPMFReal r p.1)]
    _ = ENNReal.ofReal
          (Finset.sum (Finset.antidiagonal n)
            (fun p ↦ poissonPMFReal r p.1 * poissonPMFReal s p.2)) := by
          symm
          exact ENNReal.ofReal_sum_of_nonneg fun p hp ↦
            mul_nonneg (poissonPMFReal_nonneg : 0 ≤ poissonPMFReal r p.1)
              (poissonPMFReal_nonneg : 0 ≤ poissonPMFReal s p.2)
    _ = ENNReal.ofReal (poissonPMFReal (r + s) n) := by
          rw [sum_antidiagonal_poissonPMFReal_eq]
    _ = poissonMeasure (r + s) ({n} : Set ℕ) := by
          exact (poissonMeasure_apply_singleton (r + s) n).symm

/-- Example 2.33: The additive convolution of two Poisson laws on `ℕ` is again Poisson, with
parameter equal to the sum of the parameters. -/
theorem poissonMeasure_conv_poissonMeasure (r s : ℝ≥0) :
    poissonMeasure r ∗ poissonMeasure s = poissonMeasure (r + s) := by
  -- Compare the two measures on singleton sets.
  -- These singleton masses determine measures on the countable space `ℕ`.
  refine Measure.ext_of_singleton fun n ↦ ?_
  -- The convolution singleton mass is the Poisson antidiagonal sum, which collapses binomially.
  rw [conv_apply_singleton_eq_sum_antidiagonal, sum_antidiagonal_poissonMeasure_apply_eq]
