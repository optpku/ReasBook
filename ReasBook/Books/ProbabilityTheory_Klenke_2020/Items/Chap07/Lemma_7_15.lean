/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 7.15: Young's inequality for nonnegative real numbers is the canonical theorem
`Real.young_inequality_of_nonneg`. The textbook assumptions `p, q ∈ (1, ∞)` and
`1 / p + 1 / q = 1` are the standard `Real.HolderConjugate` condition, via
`Real.holderConjugate_iff`. -/
recall Real.young_inequality_of_nonneg

-- Proof sketch: convert the textbook reciprocal relation to `p.HolderConjugate q` using
-- `Real.holderConjugate_iff`, then apply `Real.young_inequality_of_nonneg`.
/-- Compatibility form of Lemma 7.15 using the textbook reciprocal identity
`1 / p + 1 / q = 1` together with `1 < p`. -/
theorem young_inequality_of_inv_add_inv_eq_one {x y p q : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    x * y ≤ x ^ p / p + y ^ q / q := by
  simpa using Real.young_inequality_of_nonneg hx hy (Real.holderConjugate_iff.mpr ⟨hp, hpq⟩)
