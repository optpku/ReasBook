/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Example_1_105

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped BigOperators

/-- The negative-binomial mass function gives an `ENNReal`-valued probability mass function on
`ℕ` for positive shape parameter `r` and success parameter `p ∈ (0,1]`, using the real-valued
mass function `negativeBinomialMass` from Example 1.105. -/
theorem negativeBinomialMass_hasSum_ennreal (r p : ℝ) (hr : 0 < r) (hp : 0 < p)
    (hp_le_one : p ≤ 1) :
    HasSum
      (fun k : ℕ ↦ ENNReal.ofReal (negativeBinomialMass r p k))
      1 := by
  apply ENNReal.hasSum_coe.mpr
  simpa using (negativeBinomialMass_hasSum hr hp hp_le_one).toNNReal
    (fun k ↦ negativeBinomialMass_nonneg hr hp hp_le_one k)

/-- The negative-binomial law with parameters `r` and `p`, realized as a probability mass
function on `ℕ`, built from the canonical real-valued mass function `negativeBinomialMass`. -/
noncomputable def negativeBinomialPMF (r p : ℝ) (hr : 0 < r) (hp : 0 < p)
    (hp_le_one : p ≤ 1) : PMF ℕ :=
  ⟨fun k ↦
      ENNReal.ofReal (negativeBinomialMass r p k),
    negativeBinomialMass_hasSum_ennreal r p hr hp hp_le_one⟩

/-- The point masses of `negativeBinomialPMF` are given by the textbook negative-binomial mass
formula from `negativeBinomialMass`. -/
theorem negativeBinomialPMF_apply (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (hp_le_one : p ≤ 1)
    (k : ℕ) :
    negativeBinomialPMF r p hr hp hp_le_one k =
      ENNReal.ofReal (negativeBinomialMass r p k) := rfl

/-- The negative-binomial law with parameters `r` and `p`, viewed as a measure on `ℕ`. -/
noncomputable abbrev negativeBinomialMeasure (r p : ℝ) (hr : 0 < r) (hp : 0 < p)
    (hp_le_one : p ≤ 1) : Measure ℕ :=
  (negativeBinomialPMF r p hr hp hp_le_one).toMeasure

/-- Helper for Exercise 3.1.1: the singleton mass of `negativeBinomialMeasure r p hr hp hp_le_one`
is the explicit textbook mass `negativeBinomialMass r p n`. -/
private lemma negativeBinomialMeasure_apply_singleton (r p : ℝ) (hr : 0 < r) (hp : 0 < p)
    (hp_le_one : p ≤ 1) (n : ℕ) :
    negativeBinomialMeasure r p hr hp hp_le_one ({n} : Set ℕ) =
      ENNReal.ofReal (negativeBinomialMass r p n) := by
  -- Rewrite the measure as the `toMeasure` of the underlying PMF and evaluate that PMF on `{n}`.
  simpa [negativeBinomialMeasure, negativeBinomialPMF_apply] using
    (PMF.toMeasure_apply_singleton (negativeBinomialPMF r p hr hp hp_le_one) n
      (measurableSet_singleton n))

/-- Helper for Exercise 3.1.1: the singleton mass of a convolution on `ℕ` is the finite
antidiagonal sum of the singleton masses of the two factors. -/
private lemma conv_apply_singleton_eq_sum_antidiagonal
    {μ ν : Measure ℕ} [SFinite μ] [SFinite ν] (n : ℕ) :
    (μ ∗ ν) ({n} : Set ℕ) =
      Finset.sum (Finset.antidiagonal n) fun ij ↦ μ ({ij.1} : Set ℕ) * ν ({ij.2} : Set ℕ) := by
  -- Unfold convolution and identify the addition fiber over `{n}` with `Finset.antidiagonal n`.
  rw [Measure.conv, Measure.map_apply measurable_add (measurableSet_singleton n)]
  have hpreimage :
      (fun z : ℕ × ℕ ↦ z.1 + z.2) ⁻¹' ({n} : Set ℕ) = ↑(Finset.antidiagonal n) := by
    ext z
    simp [Finset.mem_antidiagonal]
  rw [hpreimage, ← MeasureTheory.sum_measure_singleton (μ := μ.prod ν)
    (s := Finset.antidiagonal n)]
  -- Each product singleton splits into the product of the two singleton masses.
  refine Finset.sum_congr rfl ?_
  intro ij hij
  have hsingleton :
      ({ij} : Set (ℕ × ℕ)) = ({ij.1} : Set ℕ) ×ˢ ({ij.2} : Set ℕ) := by
    ext z
    rcases z with ⟨a, b⟩
    cases ij
    simp
  rw [hsingleton]
  exact Measure.prod_prod (μ := μ) (ν := ν) ({ij.1} : Set ℕ) ({ij.2} : Set ℕ)

/-- Helper for Exercise 3.1.1: the negative-binomial antidiagonal mass sum collapses to the
negative-binomial mass with parameter `r + s`. -/
private lemma sum_antidiagonal_negativeBinomialMass_eq (r s p : ℝ) (hp : 0 < p) (n : ℕ) :
    Finset.sum (Finset.antidiagonal n)
      (fun ij ↦ negativeBinomialMass r p ij.1 * negativeBinomialMass s p ij.2) =
        negativeBinomialMass (r + s) p n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hterm :
      ∀ m ∈ Finset.range (n + 1),
        negativeBinomialMass r p m * negativeBinomialMass s p (n - m) =
          (Ring.choose (-r) m * Ring.choose (-s) (n - m)) *
            (((-1 : ℝ) ^ n) * p ^ (r + s) * (1 - p) ^ n) := by
    intro m hm
    have hm_le : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    -- Expand the two masses and merge the common powers using `m + (n - m) = n`.
    calc
      negativeBinomialMass r p m * negativeBinomialMass s p (n - m)
          = (Ring.choose (-r) m * (-1 : ℝ) ^ m * p ^ r * (1 - p) ^ m) *
              (Ring.choose (-s) (n - m) * (-1 : ℝ) ^ (n - m) * p ^ s * (1 - p) ^ (n - m)) := by
              simp [negativeBinomialMass]
      _ = (Ring.choose (-r) m * Ring.choose (-s) (n - m)) *
            (((-1 : ℝ) ^ m * (-1 : ℝ) ^ (n - m)) * (p ^ r * p ^ s) *
              ((1 - p) ^ m * (1 - p) ^ (n - m))) := by
            ring
      _ = (Ring.choose (-r) m * Ring.choose (-s) (n - m)) *
            (((-1 : ℝ) ^ n) * p ^ (r + s) * (1 - p) ^ n) := by
            rw [← pow_add, Nat.add_sub_of_le hm_le, ← Real.rpow_add hp r s,
              ← pow_add, Nat.add_sub_of_le hm_le]
  have hchoose :
      ∑ m ∈ Finset.range (n + 1), Ring.choose (-r) m * Ring.choose (-s) (n - m) =
        Ring.choose (-(r + s)) n := by
    have h :=
      Ring.add_choose_eq (R := ℝ) (r := -r) (s := -s) n (Commute.all (-r) (-s))
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    calc
      ∑ m ∈ Finset.range (n + 1), Ring.choose (-r) m * Ring.choose (-s) (n - m)
          = Ring.choose (-r + -s) n := h.symm
      _ = Ring.choose (-(r + s)) n := by
            congr 1
            ring
  -- Factor out the common weight and then apply Chu-Vandermonde to the binomial coefficients.
  calc
    ∑ m ∈ Finset.range (n + 1),
        negativeBinomialMass r p m * negativeBinomialMass s p (n - m)
      = ∑ m ∈ Finset.range (n + 1),
          (Ring.choose (-r) m * Ring.choose (-s) (n - m)) *
            (((-1 : ℝ) ^ n) * p ^ (r + s) * (1 - p) ^ n) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            rw [hterm m hm]
    _ = (∑ m ∈ Finset.range (n + 1),
          Ring.choose (-r) m * Ring.choose (-s) (n - m)) *
            (((-1 : ℝ) ^ n) * p ^ (r + s) * (1 - p) ^ n) := by
            rw [Finset.sum_mul]
    _ = Ring.choose (-(r + s)) n * (((-1 : ℝ) ^ n) * p ^ (r + s) * (1 - p) ^ n) := by
            rw [hchoose]
    _ = negativeBinomialMass (r + s) p n := by
            simp [negativeBinomialMass, mul_assoc]

/-- Helper for Exercise 3.1.1: after rewriting singleton masses, the convolution antidiagonal sum
is exactly the singleton mass of `negativeBinomialMeasure (r + s) p`. -/
private lemma sum_antidiagonal_negativeBinomialMeasure_apply_eq (r s p : ℝ) (hr : 0 < r)
    (hs : 0 < s) (hp : 0 < p) (hp_le_one : p ≤ 1) (n : ℕ) :
    Finset.sum (Finset.antidiagonal n)
        (fun ij ↦
          negativeBinomialMeasure r p hr hp hp_le_one ({ij.1} : Set ℕ) *
            negativeBinomialMeasure s p hs hp hp_le_one ({ij.2} : Set ℕ)) =
      negativeBinomialMeasure (r + s) p (add_pos hr hs) hp hp_le_one ({n} : Set ℕ) := by
  -- Rewrite each singleton through the real-valued mass formula, then collapse that finite sum.
  calc
    Finset.sum (Finset.antidiagonal n)
        (fun ij ↦
          negativeBinomialMeasure r p hr hp hp_le_one ({ij.1} : Set ℕ) *
            negativeBinomialMeasure s p hs hp hp_le_one ({ij.2} : Set ℕ))
      = Finset.sum (Finset.antidiagonal n)
          (fun ij ↦
            ENNReal.ofReal
              (negativeBinomialMass r p ij.1 * negativeBinomialMass s p ij.2)) := by
            refine Finset.sum_congr rfl ?_
            intro ij hij
            rw [negativeBinomialMeasure_apply_singleton, negativeBinomialMeasure_apply_singleton,
              ENNReal.ofReal_mul (negativeBinomialMass_nonneg hr hp hp_le_one ij.1)]
    _ = ENNReal.ofReal
          (Finset.sum (Finset.antidiagonal n)
            (fun ij ↦ negativeBinomialMass r p ij.1 * negativeBinomialMass s p ij.2)) := by
          symm
          exact ENNReal.ofReal_sum_of_nonneg fun ij hij ↦
            mul_nonneg (negativeBinomialMass_nonneg hr hp hp_le_one ij.1)
              (negativeBinomialMass_nonneg hs hp hp_le_one ij.2)
    _ = ENNReal.ofReal (negativeBinomialMass (r + s) p n) := by
          rw [sum_antidiagonal_negativeBinomialMass_eq r s p hp n]
    _ = negativeBinomialMeasure (r + s) p (add_pos hr hs) hp hp_le_one ({n} : Set ℕ) := by
          rw [negativeBinomialMeasure_apply_singleton (r + s) p (add_pos hr hs) hp hp_le_one n]

-- Proof sketch: identify the probability generating function of `negativeBinomialMeasure r p hr hp
-- hp_le_one` as `z ↦ (p / (1 - (1 - p) * z)) ^ r`, multiply the generating functions for the two
-- factors, and use uniqueness of probability generating functions on `ℕ`-valued laws.
/-- Exercise 3.1.1: The convolution of the negative-binomial laws with common success parameter
`p ∈ (0,1]` and shape parameters `r,s > 0` is the negative-binomial law with shape parameter
`r + s`. -/
theorem negativeBinomialMeasure_conv (r s p : ℝ) (hr : 0 < r) (hs : 0 < s) (hp : 0 < p)
    (hp_le_one : p ≤ 1) :
    negativeBinomialMeasure r p hr hp hp_le_one ∗
        negativeBinomialMeasure s p hs hp hp_le_one =
      negativeBinomialMeasure (r + s) p (add_pos hr hs) hp hp_le_one := by
  -- Route correction: on the discrete state space `ℕ`, singleton masses reduce convolution to a
  -- finite antidiagonal sum, so no later pgf uniqueness machinery is needed here.
  refine Measure.ext_of_singleton fun n ↦ ?_
  -- Compare the singleton mass of the convolution with the collapsed antidiagonal mass formula.
  rw [conv_apply_singleton_eq_sum_antidiagonal,
    sum_antidiagonal_negativeBinomialMeasure_apply_eq r s p hr hs hp hp_le_one]
