module

public import ReasLib.Optimization.DFP.Polar.General.Recurrence

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.Polar.General.AngularBounds

/-- Helper for eq:polar-angles: a normalized angular factor between one half
and two preserves uniform coefficient bounds after multiplication by scale. -/
theorem scaledFactor_bounds {a b c F t : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c)
    (ha : a ≤ c / 2) (hb : 2 * c ≤ b) (hF : 1 / 2 ≤ F ∧ F ≤ 2) :
    a * t ≤ (c * F) * t ∧ (c * F) * t ≤ b * t := by
  have hlo := mul_le_mul_of_nonneg_left hF.1 hc
  have hhi := mul_le_mul_of_nonneg_left hF.2 hc
  have hlo' : a ≤ c * F := by linarith
  have hhi' : c * F ≤ b := by linarith
  exact ⟨mul_le_mul_of_nonneg_right hlo' ht, mul_le_mul_of_nonneg_right hhi' ht⟩

/-- Helper for eq:polar-angles and lem:polar-geometry: the actual source
angle increments have fixed positive lower and upper scale bounds and remain
strictly below π. All constants and the common threshold precede the final
starting index choice. -/
theorem existsAngleBounds (p : Parameters) (hβ : 0 < p.beta) :
    ∃ a > 0, ∃ b > 0, ∃ J : ℕ, 0 < J ∧ ∀ j0 : ℕ, J ≤ j0 → ∀ k : ℕ,
      a * scale p.beta j0 (k / 2) ≤ (p.withStartIndex j0).angleIncrement k ∧
        (p.withStartIndex j0).angleIncrement k ≤ b * scale p.beta j0 (k / 2) ∧
          (p.withStartIndex j0).angleIncrement k < Real.pi := by
  let a := min p.deltaEven p.deltaOdd / 2
  let b := 2 * max p.deltaEven p.deltaOdd
  have hmin : 0 < min p.deltaEven p.deltaOdd := lt_min p.deltaEven_pos p.deltaOdd_pos
  have hmax : 0 < max p.deltaEven p.deltaOdd :=
    p.deltaEven_pos.trans_le (le_max_left _ _)
  have ha : 0 < a := half_pos hmin
  have hb : 0 < b := mul_pos zero_lt_two hmax
  have hInv : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun n : ℕ ↦ angleFactor p.beta ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, angleFactor_zero hβ] using
      (analyticAt_angleFactor_zero p.beta).continuousAt.tendsto.comp hInv
  have hhalf : (1 / 2 : ℝ) < 1 := by norm_num
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hFactors := hF.eventually (Ioo_mem_nhds hhalf htwo)
  have hpi : 0 < Real.pi / b := div_pos Real.pi_pos hb
  have hSmall := (scale_tendsto_zero hβ 0).eventually (Iio_mem_nhds hpi)
  obtain ⟨J, hJall⟩ := eventually_atTop.mp
    ((eventually_ge_atTop 1).and (hFactors.and hSmall))
  have hJ : 0 < J := by
    have h := (hJall J le_rfl).1
    omega
  refine ⟨a, ha, b, hb, J, hJ, ?_⟩
  intro j0 hj0
  have hstart : 0 < j0 := hJ.trans_le hj0
  let q := p.withStartIndex j0
  have hqβ : 0 < q.beta := by simpa only [q, p.withStartIndex_beta] using hβ
  have hqstart : 0 < q.startIndex := by
    simpa only [q, p.withStartIndex_startIndex] using hstart
  have hScalar (c : ℝ) (hcmin : min p.deltaEven p.deltaOdd ≤ c)
      (hcmax : c ≤ max p.deltaEven p.deltaOdd) (j : ℕ) :
      a * scale p.beta j0 j ≤
          (c * angleFactor p.beta ((((j0 + j : ℕ) : ℝ))⁻¹)) * scale p.beta j0 j ∧
        (c * angleFactor p.beta ((((j0 + j : ℕ) : ℝ))⁻¹)) * scale p.beta j0 j ≤
          b * scale p.beta j0 j ∧
        (c * angleFactor p.beta ((((j0 + j : ℕ) : ℝ))⁻¹)) * scale p.beta j0 j < Real.pi := by
    have hindex : J ≤ j0 + j := hj0.trans (Nat.le_add_right j0 j)
    have hdata := (hJall (j0 + j) hindex).2
    have ht := scale_nonneg p.beta j0 j
    have hc : 0 ≤ c := (hmin.trans_le hcmin).le
    have ha' : a ≤ c / 2 := div_le_div_of_nonneg_right hcmin zero_le_two
    have hb' : 2 * c ≤ b := mul_le_mul_of_nonneg_left hcmax zero_le_two
    have hbound := scaledFactor_bounds ht hc ha' hb' ⟨hdata.1.1.le, hdata.1.2.le⟩
    have hsmall : scale p.beta j0 j < Real.pi / b := by
      simpa only [scale_def, Nat.zero_add] using hdata.2
    have hpiBound : b * scale p.beta j0 j < Real.pi := by
      have h := (lt_div_iff₀ hb).mp hsmall
      simpa only [mul_comm] using h
    exact ⟨hbound.1, hbound.2, hbound.2.trans_lt hpiBound⟩
  intro k
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have hAngle : q.angleIncrement (2 * j) =
        (p.deltaEven * angleFactor p.beta ((((j0 + j : ℕ) : ℝ))⁻¹)) * scale p.beta j0 j := by
      simpa only [Normalized.stageAngle_def, Parameters.evenAngleFactor_def,
        Parameters.inverseIndex_def, Parameters.scale_def, q, p.withStartIndex_beta,
        p.withStartIndex_deltaEven, p.withStartIndex_startIndex] using
        q.angleIncrement_even hqβ hqstart j
    have hhalfIndex : 2 * j / 2 = j := by omega
    have hbounds := hScalar p.deltaEven (min_le_left _ _) (le_max_left _ _) j
    rw [← hAngle] at hbounds
    simpa only [hhalfIndex, q] using hbounds
  · have hAngle : q.angleIncrement (2 * j + 1) =
        (p.deltaOdd * angleFactor p.beta ((((j0 + j : ℕ) : ℝ))⁻¹)) * scale p.beta j0 j := by
      simpa only [Normalized.stageAngle_def, Parameters.oddAngleFactor_def,
        Parameters.inverseIndex_def, Parameters.scale_def, q, p.withStartIndex_beta,
        p.withStartIndex_deltaOdd, p.withStartIndex_startIndex] using
        q.angleIncrement_odd hqβ hqstart j
    have hhalfIndex : (2 * j + 1) / 2 = j := by omega
    have hbounds := hScalar p.deltaOdd (min_le_right _ _) (le_max_right _ _) j
    rw [← hAngle] at hbounds
    simpa only [hhalfIndex, q] using hbounds


/-- Helper for eq:polar-physical-step: the same uniform angular bounds give
strict positivity of the sine at every physical source step. -/
theorem existsAngleBoundsWithSin (p : Parameters) (hβ : 0 < p.beta) :
    ∃ a > 0, ∃ b > 0, ∃ J : ℕ, 0 < J ∧ ∀ j0 : ℕ, J ≤ j0 → ∀ k : ℕ,
      (a * scale p.beta j0 (k / 2) ≤ (p.withStartIndex j0).angleIncrement k ∧
        (p.withStartIndex j0).angleIncrement k ≤ b * scale p.beta j0 (k / 2) ∧
          (p.withStartIndex j0).angleIncrement k < Real.pi) ∧
        0 < Real.sin ((p.withStartIndex j0).angleIncrement k) := by
  obtain ⟨a, ha, b, hb, J, hJ, hbounds⟩ := existsAngleBounds p hβ
  refine ⟨a, ha, b, hb, J, hJ, ?_⟩
  intro j0 hj0 k
  have hbound := hbounds j0 hj0 k
  have hpositive : 0 < (p.withStartIndex j0).angleIncrement k :=
    (mul_pos ha (scale_pos p.beta (hJ.trans_le hj0) (k / 2))).trans_le hbound.1
  exact ⟨hbound, Real.sin_pos_of_pos_of_lt_pi hpositive hbound.2.2⟩

end DFP.Polar.General.AngularBounds
