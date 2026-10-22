/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Finset
open scoped BigOperators

/- Example 1.105: the canonical Bernoulli distribution is `PMF.bernoulli`; the Bernoulli law on
`ℝ` used below is its pushforward along `cond · (1 : ℝ) 0`. -/
recall PMF.bernoulli

/- The textbook binomial point-mass formula is the canonical theorem `PMF.binomial_apply`. -/
recall PMF.binomial_apply

/- The textbook geometric distribution is the canonical pmf `geometricPMF`. -/
recall ProbabilityTheory.geometricPMF

/- The textbook Poisson point-mass formula is the canonical theorem
`poissonPMFReal_ofReal_eq_poissonPMF`. -/
recall ProbabilityTheory.poissonPMFReal_ofReal_eq_poissonPMF

/- The Gaussian mean and variance formulas are the canonical theorems
`integral_id_gaussianReal` and `variance_id_gaussianReal`. -/
recall ProbabilityTheory.integral_id_gaussianReal
recall ProbabilityTheory.variance_id_gaussianReal

/- The exponential cdf formula is the canonical theorem `cdf_expMeasure_eq`. -/
recall ProbabilityTheory.cdf_expMeasure_eq

/- The multivariate Gaussian mean and covariance formulas are the canonical theorems
`integral_id_multivariateGaussian` and `covariance_eval_multivariateGaussian`. -/
recall ProbabilityTheory.integral_id_multivariateGaussian
recall ProbabilityTheory.covariance_eval_multivariateGaussian

/-- The point-mass formula for the negative binomial distribution with parameters `r` and `p`. -/
noncomputable def negativeBinomialMass (r p : ℝ) (k : ℕ) : ℝ :=
  Ring.choose (-r) k * (-1 : ℝ) ^ k * p ^ r * (1 - p) ^ k

/-- The point-mass formula for the hypergeometric distribution with parameters `B`, `W`, and
`n`. -/
noncomputable def hypergeometricMass (B W n : ℕ) (b : Fin (n + 1)) : ℝ :=
  ((Nat.choose B b : ℝ) * Nat.choose W (n - b)) / Nat.choose (B + W) n

/-- The point-mass formula for the generalized hypergeometric distribution on color-count vectors.
It vanishes unless the total number of drawn balls is `n`. -/
noncomputable def generalizedHypergeometricMass {k : ℕ} (B : Fin k → ℕ) (n : ℕ)
    (b : Fin k → ℕ) : ℝ :=
  if _h : ∑ i, b i = n then
    ((∏ i, (Nat.choose (B i) (b i) : ℝ)) / Nat.choose (∑ i, B i) n)
  else
    0

/-- The negative-binomial mass formula is nonnegative for admissible parameters. -/
theorem negativeBinomialMass_nonneg {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (hp_le_one : p ≤ 1)
    (k : ℕ) :
    0 ≤ negativeBinomialMass r p k := sorry

/-- The negative-binomial mass formula sums to one for admissible parameters. -/
theorem negativeBinomialMass_hasSum {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (hp_le_one : p ≤ 1) :
    HasSum (negativeBinomialMass r p) 1 := sorry

/-- The hypergeometric mass formula is nonnegative. -/
theorem hypergeometricMass_nonneg {B W n : ℕ} (hn : n ≤ B + W) (b : Fin (n + 1)) :
    0 ≤ hypergeometricMass B W n b := sorry

/-- The hypergeometric mass formula sums to one. -/
theorem hypergeometricMass_sum {B W n : ℕ} (hn : n ≤ B + W) :
    (∑ b : Fin (n + 1), hypergeometricMass B W n b) = 1 := sorry

/-- The generalized hypergeometric mass formula is nonnegative. -/
theorem generalizedHypergeometricMass_nonneg {k : ℕ} {B : Fin k → ℕ} (n : ℕ)
    (b : Fin k → ℕ) :
    0 ≤ generalizedHypergeometricMass B n b := sorry

/-- On the canonical antidiagonal `piAntidiag univ n`, the generalized hypergeometric mass is given
by the expected product-of-binomial-coefficients formula. -/
theorem generalizedHypergeometricMass_of_sum_eq {k : ℕ} {B : Fin k → ℕ} {n : ℕ}
    {b : Fin k → ℕ} (hb : ∑ i, b i = n) :
    generalizedHypergeometricMass B n b =
      ((∏ i, (Nat.choose (B i) (b i) : ℝ)) / Nat.choose (∑ i, B i) n) := by
  simp [generalizedHypergeometricMass, hb]

/-- Outside the canonical antidiagonal `piAntidiag univ n`, the generalized hypergeometric mass
vanishes. -/
theorem generalizedHypergeometricMass_eq_zero_of_sum_ne {k : ℕ} {B : Fin k → ℕ} {n : ℕ}
    {b : Fin k → ℕ} (hb : ∑ i, b i ≠ n) :
    generalizedHypergeometricMass B n b = 0 := by
  simp [generalizedHypergeometricMass, hb]

/-- The generalized hypergeometric mass formula sums to one on the canonical finite support
`piAntidiag univ n`. -/
theorem generalizedHypergeometricMass_sum {k : ℕ} {B : Fin k → ℕ} {n : ℕ}
    (hn : n ≤ ∑ i, B i) :
    (∑ b ∈ piAntidiag univ n, generalizedHypergeometricMass B n b) = 1 := sorry
