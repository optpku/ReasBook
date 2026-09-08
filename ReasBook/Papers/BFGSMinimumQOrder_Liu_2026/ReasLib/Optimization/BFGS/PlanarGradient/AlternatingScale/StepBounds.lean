module

public import ReasLib.Optimization.BFGS.PlanarGradient.Recurrence

public section

universe u

namespace PlanarGradient

/-- A nonzero affine expression can be made arbitrarily small by choosing a nonzero
target value and solving for the perturbation. -/
theorem exists_nearCancellation (P D ε : ℝ) (hP : P ≠ 0) (hD : D ≠ 0)
    (hε : 0 < ε) :
    ∃ τ δ : ℝ, 0 < |τ| ∧ |τ| < min ε (|P| / 2) ∧
      δ = (τ - P) / D ∧ P + D * δ = τ := by
  -- Halving the smaller of the two positive bounds gives the target radius.
  have hPabs : 0 < |P| := abs_pos.mpr hP
  have hHalfP : 0 < |P| / 2 := by linarith
  have hMin : 0 < min ε (|P| / 2) := lt_min hε hHalfP
  refine ⟨min ε (|P| / 2) / 2, (min ε (|P| / 2) / 2 - P) / D, ?_, ?_, rfl, ?_⟩
  · rw [abs_of_pos]
    · exact half_pos hMin
    · exact half_pos hMin
  · rw [abs_of_pos (half_pos hMin)]
    linarith
  -- The chosen quotient solves the affine equation because its denominator is nonzero.
  · field_simp [hD]
    ring

/-- Solving for a near-cancelling perturbation places its magnitude between one half
and three halves of the cancellation scale. -/
theorem nearCancellation_abs_mem_Icc (P D τ : ℝ) (hP : P ≠ 0) (hD : D ≠ 0)
    (hτ : |τ| ≤ |P| / 2) :
    |(τ - P) / D| ∈
      Set.Icc ((1 / 2 : ℝ) * |P / D|) ((3 / 2 : ℝ) * |P / D|) := by
  -- Triangle inequalities first bound the numerator independently of the denominator.
  have hNumeratorLower : |P| / 2 ≤ |τ - P| := by
    have hTriangle : |P| ≤ |τ - P| + |τ| := by
      calc
        |P| = |(P - τ) + τ| := by
          congr 1
          ring
        _ ≤ |P - τ| + |τ| := abs_add_le (P - τ) τ
        _ = |τ - P| + |τ| := by rw [abs_sub_comm]
    linarith
  have hNumeratorUpper : |τ - P| ≤ (3 / 2 : ℝ) * |P| := by
    have hTriangle : |τ - P| ≤ |τ| + |P| := abs_sub τ P
    linarith
  have hDabs : 0 < |D| := abs_pos.mpr hD
  -- Dividing both numerator estimates by the common positive denominator preserves order.
  rw [abs_div, abs_div]
  constructor
  · calc
      (1 / 2 : ℝ) * (|P| / |D|) = (|P| / 2) / |D| := by ring
      _ ≤ |τ - P| / |D| := (div_le_div_iff_of_pos_right hDabs).2 hNumeratorLower
  · calc
      |τ - P| / |D| ≤ ((3 / 2 : ℝ) * |P|) / |D| :=
        (div_le_div_iff_of_pos_right hDabs).2 hNumeratorUpper
      _ = (3 / 2 : ℝ) * (|P| / |D|) := by ring

section OrientedPlane

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- A nonzero preceding perturbation and positive angular separation make the next
parallel coefficient nonzero. -/
theorem parallelCoefficient_ne_zero_of_perturbation (o : Orientation ℝ E (Fin 2))
    (gPrev g : E) (δPrev : ℝ) (hPrev : gPrev ≠ 0) (hg : g ≠ 0)
    (hDistinct : g ≠ gPrev)
    (hPre : inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev))
    (hSeparation : 0 < angularSeparation o gPrev g) (hδPrev : δPrev ≠ 0) :
    parallelCoefficient gPrev g ≠ 0 := by
  -- Positive angular separation supplies the nonzero oriented-area factor.
  have hArea :
      o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g) ≠ 0 := by
    rw [angularSeparation_apply] at hSeparation
    exact abs_pos.mp hSeparation
  have hNorm : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  have hSecantNorm : ‖g - gPrev‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero_of_ne hDistinct)
  -- The recurrence formula is a quotient whose four scalar factors are nonzero.
  rw [parallelCoefficient_eq_of_preStep o gPrev g δPrev hPrev hg hDistinct hPre]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hδPrev hNorm) hArea) hSecantNorm

end OrientedPlane

/-- A nonzero affine leading term admits an arbitrarily small nonzero perturbation
whose correction cannot cancel more than half of it. -/
theorem exists_retainingPerturbation (P D ε : ℝ) (hP : P ≠ 0) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < |δ| ∧ |δ| < ε ∧ |D * δ| ≤ |P| / 2 := by
  -- A zero correction coefficient permits any sufficiently small positive perturbation.
  by_cases hD : D = 0
  · refine ⟨ε / 2, ?_, ?_, ?_⟩
    · rw [abs_of_pos (half_pos hε)]
      exact half_pos hε
    · rw [abs_of_pos (half_pos hε)]
      linarith
    · simp only [hD, zero_mul, abs_zero]
      positivity
  -- Otherwise cap the perturbation by the quotient that spends half the leading term.
  · have hPabs : 0 < |P| := abs_pos.mpr hP
    have hDabs : 0 < |D| := abs_pos.mpr hD
    have hTwoPos : (0 : ℝ) < 2 := by norm_num
    have hChoice : 0 < min (ε / 2) (|P| / (2 * |D|)) :=
      lt_min (half_pos hε) (div_pos hPabs (mul_pos hTwoPos hDabs))
    refine ⟨min (ε / 2) (|P| / (2 * |D|)), ?_, ?_, ?_⟩
    · rw [abs_of_pos hChoice]
      exact hChoice
    · rw [abs_of_pos hChoice]
      exact (min_le_left _ _).trans_lt (half_lt_self hε)
    · rw [abs_mul, abs_of_pos hChoice]
      calc
        |D| * min (ε / 2) (|P| / (2 * |D|)) ≤
            |D| * (|P| / (2 * |D|)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg D)
        _ = |P| / 2 := by field_simp [abs_ne_zero.mpr hD]

/-- A correction bounded by half of the leading term retains between one half and
three halves of its magnitude. -/
theorem retainingPerturbation_abs_mem_Icc (P D δ : ℝ) (hP : P ≠ 0)
    (hδ : |D * δ| ≤ |P| / 2) :
    |P + D * δ| ∈ Set.Icc (|P| / 2) ((3 / 2 : ℝ) * |P|) := by
  constructor
  · -- Reconstructing `P` from the perturbed term gives the lower estimate.
    have hTriangle : |P| ≤ |P + D * δ| + |D * δ| := by
      calc
        |P| = |(P + D * δ) + (-(D * δ))| := by
          congr 1
          ring
        _ ≤ |P + D * δ| + |-(D * δ)| := abs_add_le _ _
        _ = |P + D * δ| + |D * δ| := by rw [abs_neg]
    linarith
  · -- The direct triangle inequality and the correction budget give the upper estimate.
    have hTriangle : |P + D * δ| ≤ |P| + |D * δ| := abs_add_le _ _
    linarith

/-- The perturbation and coefficient bounds propagate the cancellation-scale invariant
to the next even index. -/
theorem nextCancellationScale_le_min (j : ℕ) (η c T rCurrent rNext δ : ℝ)
    (hCurrent : 0 < rCurrent) (hNext : 0 < rNext) (hTnonneg : 0 ≤ T)
    (hTnext : T ≤ 2 * rNext) (hTlt : T < 1)
    (hδ : |δ| ≤ c * rCurrent * T ^ (j + 3)) (hc : 0 ≤ c)
    (hcBound : c ≤ min (((2 : ℝ) ^ (j + 3))⁻¹) ((4 / 9 : ℝ) * η)) :
    |δ| * rNext / rCurrent ≤
      min (rNext ^ (j + 4)) ((4 / 9 : ℝ) * η * rNext) := by
  -- Cancel the current positive radius, leaving the coefficient-power expression.
  have hScaled := mul_le_mul_of_nonneg_right hδ hNext.le
  have hCore : |δ| * rNext / rCurrent ≤ c * T ^ (j + 3) * rNext := by
    rw [div_le_iff₀ hCurrent]
    calc
      |δ| * rNext ≤ (c * rCurrent * T ^ (j + 3)) * rNext := hScaled
      _ = (c * T ^ (j + 3) * rNext) * rCurrent := by ring
  have hcPower : c ≤ ((2 : ℝ) ^ (j + 3))⁻¹ :=
    hcBound.trans (min_le_left _ _)
  have hcBudget : c ≤ (4 / 9 : ℝ) * η :=
    hcBound.trans (min_le_right _ _)
  have hTPower : T ^ (j + 3) ≤ (2 * rNext) ^ (j + 3) :=
    pow_le_pow_left₀ hTnonneg hTnext _
  have hTOne : T ^ (j + 3) ≤ 1 := pow_le_one₀ hTnonneg hTlt.le
  -- The inverse dyadic bound cancels the power of two in the radius comparison.
  have hTwo : (2 : ℝ) ≠ 0 := by norm_num
  have hTwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hPowerNormalization :
      ((2 : ℝ) ^ (j + 3))⁻¹ * (2 * rNext) ^ (j + 3) * rNext =
        rNext ^ (j + 4) := by
    rw [mul_pow, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hTwo), one_mul, ← pow_succ]
  have hPowerBranch : c * T ^ (j + 3) * rNext ≤ rNext ^ (j + 4) := by
    calc
      c * T ^ (j + 3) * rNext ≤
          ((2 : ℝ) ^ (j + 3))⁻¹ * T ^ (j + 3) * rNext :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcPower (pow_nonneg hTnonneg _)) hNext.le
      _ ≤ ((2 : ℝ) ^ (j + 3))⁻¹ * (2 * rNext) ^ (j + 3) * rNext :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hTPower (inv_nonneg.mpr (pow_nonneg hTwoNonneg _)))
          hNext.le
      _ = rNext ^ (j + 4) := hPowerNormalization
  -- The second coefficient bound and `T < 1` give the summability-budget branch.
  have hBudgetBranch :
      c * T ^ (j + 3) * rNext ≤ (4 / 9 : ℝ) * η * rNext := by
    apply mul_le_mul_of_nonneg_right _ hNext.le
    calc
      c * T ^ (j + 3) ≤ c * 1 := mul_le_mul_of_nonneg_left hTOne hc
      _ = c := mul_one c
      _ ≤ (4 / 9 : ℝ) * η := hcBudget
  exact le_min (hCore.trans hPowerBranch) (hCore.trans hBudgetBranch)

end PlanarGradient
