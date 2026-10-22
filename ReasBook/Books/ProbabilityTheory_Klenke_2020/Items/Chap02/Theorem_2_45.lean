/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_44

open scoped unitInterval
open unitInterval

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Theorem 2.45: positivity of `θ` at a parameter `q` forces the critical value to lie
at most at `q`. -/
theorem criticalPercolationValue_le_of_positive
    (θ : unitInterval → NNReal) {q : unitInterval} (hq : 0 < θ q) :
    criticalPercolationValue θ ≤ q := by
  -- Any positive parameter belongs to the defining threshold set.
  rw [criticalPercolationValue_def]
  exact sInf_le hq

/-- Helper for Theorem 2.45: if `θ` vanishes strictly below `a`, then the critical value lies at
least at `a`. -/
theorem subcriticalPoint_le_criticalPercolationValue
    (θ : unitInterval → NNReal) (a : unitInterval)
    (h_subcritical : ∀ p : unitInterval, p < a → θ p = 0) :
    a ≤ criticalPercolationValue θ := by
  -- Every positive parameter must sit on or above the subcritical cutoff.
  rw [criticalPercolationValue_def]
  refine le_sInf fun p hp ↦ ?_
  by_contra h_not_le
  have hp_lt : p < a := lt_of_not_ge h_not_le
  have h_zero : θ p = 0 := h_subcritical p hp_lt
  have hp_pos : 0 < θ p := hp
  exact hp_pos.ne' h_zero

/-- Helper for Theorem 2.45: the real number `2 / 3` belongs to `unitInterval`. -/
theorem twoThirds_mem_unitInterval : ((2 : ℝ) / 3) ∈ I := by
  norm_num

/-- Helper for Theorem 2.45: the point `2 / 3` viewed inside `unitInterval`. -/
noncomputable def twoThirdsUnitInterval : unitInterval :=
  ⟨(2 : ℝ) / 3, twoThirds_mem_unitInterval⟩

/-- Helper for Theorem 2.45: the real number `1 / 2` belongs to `unitInterval`. -/
theorem oneHalf_mem_unitInterval : ((1 : ℝ) / 2) ∈ I := by
  norm_num

/-- Helper for Theorem 2.45: the midpoint coefficient `1 / 2` in `unitInterval`. -/
noncomputable def oneHalfUnitInterval : unitInterval :=
  ⟨(1 : ℝ) / 2, oneHalf_mem_unitInterval⟩

/-- Helper for Theorem 2.45: the lower comparison point `(2d - 1)⁻¹` lies in `unitInterval` for
every `d ≥ 2`. -/
theorem lowerThreshold_mem_unitInterval {d : ℕ} (hd : 2 ≤ d) :
    ((1 : ℝ) / (2 * d - 1)) ∈ I := by
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast hd
  have h_den_nonneg : 0 ≤ 2 * (d : ℝ) - 1 := by
    nlinarith
  have h_den_ge_one : (1 : ℝ) ≤ 2 * (d : ℝ) - 1 := by
    nlinarith
  constructor
  · exact one_div_nonneg.mpr h_den_nonneg
  · have h_inv : 1 / (2 * (d : ℝ) - 1) ≤ 1 / (1 : ℝ) :=
      one_div_le_one_div_of_le zero_lt_one h_den_ge_one
    simpa using h_inv

/-- Helper for Theorem 2.45: package `(2d - 1)⁻¹` as a point of `unitInterval` when `d ≥ 2`. -/
noncomputable def lowerThresholdUnitInterval (d : ℕ) (hd : 2 ≤ d) : unitInterval :=
  ⟨(1 : ℝ) / (2 * d - 1), lowerThreshold_mem_unitInterval hd⟩

/-- Helper for Theorem 2.45: if `x` lies strictly above `2 / 3`, then there is a
`unitInterval` point strictly between `2 / 3` and `x`. -/
theorem exists_unitInterval_between_twoThirds_and
    (x : unitInterval) (hx : twoThirdsUnitInterval < x) :
    ∃ q : unitInterval, twoThirdsUnitInterval < q ∧ q < x := by
  -- Use the midpoint between `2 / 3` and `x`.
  let q : unitInterval := Set.Icc.convexCombo twoThirdsUnitInterval x oneHalfUnitInterval
  have hx_real : (2 : ℝ) / 3 < (x : ℝ) := by
    simpa [twoThirdsUnitInterval] using hx
  have hq_formula : (q : ℝ) = (((2 : ℝ) / 3) + x) / 2 := by
    rw [Set.Icc.coe_convexCombo]
    norm_num [q, twoThirdsUnitInterval, oneHalfUnitInterval]
    ring
  refine ⟨q, ?_, ?_⟩
  · change
      (2 : ℝ) / 3 <
        ((Set.Icc.convexCombo twoThirdsUnitInterval x oneHalfUnitInterval : unitInterval) : ℝ)
    simpa [q] using show (2 : ℝ) / 3 < (q : ℝ) by
      nlinarith [hx_real, hq_formula]
  · change
      (((Set.Icc.convexCombo twoThirdsUnitInterval x oneHalfUnitInterval : unitInterval) : ℝ) <
        x)
    simpa [q] using show (q : ℝ) < (x : ℝ) by
      nlinarith [hx_real, hq_formula]

/-- Helper for Theorem 2.45: the two-dimensional supercritical estimate implies
`criticalPercolationValue (θ 2) ≤ 2 / 3`. -/
theorem criticalPercolationValue_two_le_twoThirds
    (θ : ℕ → unitInterval → NNReal)
    (h_two_dim_supercritical :
      ∀ p : unitInterval, (2 : ℝ) / 3 < (p : ℝ) → 0 < θ 2 p) :
    criticalPercolationValue (θ 2) ≤ twoThirdsUnitInterval := by
  -- Route correction: the Lean target already packages the contour argument into a positivity
  -- hypothesis above `2 / 3`, so we argue by infimum contradiction instead of rebuilding contours.
  by_contra h_not_le
  have h_lt : twoThirdsUnitInterval < criticalPercolationValue (θ 2) := lt_of_not_ge h_not_le
  obtain ⟨q, hq_lower, hq_upper⟩ :=
    exists_unitInterval_between_twoThirds_and (criticalPercolationValue (θ 2)) h_lt
  -- The intermediate point is supercritical, so the infimum cannot stay above it.
  have hq_pos : 0 < θ 2 q := h_two_dim_supercritical q <| by
    simpa [twoThirdsUnitInterval] using hq_lower
  have h_crit_le_q : criticalPercolationValue (θ 2) ≤ q :=
    criticalPercolationValue_le_of_positive (θ 2) hq_pos
  exact hq_upper.not_ge h_crit_le_q

/-- In dimension `1`, the critical percolation value is `1`. -/
theorem criticalPercolationProbability_eq_one
    (θ : ℕ → unitInterval → NNReal)
    (h_dim_one_subcritical :
      ∀ p : unitInterval, (p : ℝ) < 1 → θ 1 p = 0)
    (h_dim_one_open : 0 < θ 1 (1 : unitInterval)) :
    criticalPercolationValue (θ 1) = 1 := by
  -- Every point strictly below `1` is subcritical, so the threshold is at least `1`.
  have h_one_le : (1 : unitInterval) ≤ criticalPercolationValue (θ 1) :=
    subcriticalPoint_le_criticalPercolationValue (θ 1) 1 fun p hp ↦
      h_dim_one_subcritical p (by simpa using hp)
  -- Positivity at `p = 1` gives the matching upper bound from the defining infimum.
  have h_crit_le_one : criticalPercolationValue (θ 1) ≤ (1 : unitInterval) :=
    criticalPercolationValue_le_of_positive (θ 1) h_dim_one_open
  exact le_antisymm h_crit_le_one h_one_le

-- Proof sketch: use the one-dimensional subcritical vanishing assumption to show that no
-- parameter below `1` belongs to the positive-probability set, use positivity at `p = 1` to show
-- that `1` does belong to that set, and then combine the lower bound
-- `(1 : ℝ) / (2 * d - 1) ≤ criticalPercolationValue (θ d)` from the subcritical estimate with the
-- upper bound `(criticalPercolationValue (θ d) : ℝ) ≤ 2 / 3` obtained from the two-dimensional
-- supercritical estimate and antitonicity in the dimension.
/-- For dimensions `d ≥ 2`, the underlying real number of the critical percolation value lies in
`[(2d - 1)⁻¹, 2 / 3]`. -/
theorem criticalPercolationProbability_mem_Icc
    (θ : ℕ → unitInterval → NNReal)
    (h_subcritical :
      ∀ ⦃d : ℕ⦄, 2 ≤ d →
        ∀ p : unitInterval, (p : ℝ) < (1 : ℝ) / (2 * d - 1) → θ d p = 0)
    (h_two_dim_supercritical :
      ∀ p : unitInterval, (2 : ℝ) / 3 < (p : ℝ) → 0 < θ 2 p)
    (h_antitone : Antitone (fun d ↦ criticalPercolationValue (θ d)))
    {d : ℕ} (hd : 2 ≤ d) :
    (criticalPercolationValue (θ d) : ℝ) ∈
      Set.Icc ((1 : ℝ) / (2 * d - 1)) ((2 : ℝ) / 3) := by
  -- The subcritical estimate gives the lower endpoint of the interval.
  have h_lower_unit :
      lowerThresholdUnitInterval d hd ≤ criticalPercolationValue (θ d) :=
    subcriticalPoint_le_criticalPercolationValue (θ d) (lowerThresholdUnitInterval d hd) fun p hp ↦
      h_subcritical hd p (by simpa [lowerThresholdUnitInterval] using hp)
  -- Antitonicity reduces the upper endpoint to the two-dimensional estimate.
  have h_two_dim_upper : criticalPercolationValue (θ 2) ≤ twoThirdsUnitInterval :=
    criticalPercolationValue_two_le_twoThirds θ h_two_dim_supercritical
  have h_upper_unit : criticalPercolationValue (θ d) ≤ twoThirdsUnitInterval :=
    le_trans (h_antitone hd) h_two_dim_upper
  -- Convert the `unitInterval` bounds into the claimed real interval membership.
  refine ⟨?_, ?_⟩
  · simpa [lowerThresholdUnitInterval] using h_lower_unit
  · simpa [twoThirdsUnitInterval] using h_upper_unit

/-- Theorem 2.45: the critical percolation probability equals `1` in dimension `1`, and for
dimensions `d ≥ 2` its underlying real value lies in the interval `[(2d - 1)⁻¹, 2/3]`. -/
theorem criticalPercolationProbability_eq_one_and_mem_Icc
    (θ : ℕ → unitInterval → NNReal)
    (h_dim_one_subcritical :
      ∀ p : unitInterval, (p : ℝ) < 1 → θ 1 p = 0)
    (h_dim_one_open : 0 < θ 1 (1 : unitInterval))
    (h_subcritical :
      ∀ ⦃d : ℕ⦄, 2 ≤ d →
        ∀ p : unitInterval, (p : ℝ) < (1 : ℝ) / (2 * d - 1) → θ d p = 0)
    (h_two_dim_supercritical :
      ∀ p : unitInterval, (2 : ℝ) / 3 < (p : ℝ) → 0 < θ 2 p)
    (h_antitone : Antitone (fun d ↦ criticalPercolationValue (θ d)))
    :
    criticalPercolationValue (θ 1) = 1 ∧
      ∀ ⦃d : ℕ⦄, 2 ≤ d →
        (criticalPercolationValue (θ d) : ℝ) ∈
          Set.Icc ((1 : ℝ) / (2 * d - 1)) ((2 : ℝ) / 3) := by
  constructor
  · exact criticalPercolationProbability_eq_one θ h_dim_one_subcritical h_dim_one_open
  · intro d hd
    exact criticalPercolationProbability_mem_Icc θ h_subcritical h_two_dim_supercritical
      h_antitone hd
