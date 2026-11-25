/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.CompactRemainder
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.CoercivityInterpolation

@[expose] public section

open scoped ComplexOrder

namespace ADMM.UnitCircle

/-- Weakening a real scalar lower bound preserves positive semidefiniteness. -/
theorem posSemidef_weaken_scalar {A : Matrix (Fin 2) (Fin 2) ℂ} {a b : ℝ}
    (hA : (A - (a : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef)
    (hab : b ≤ a) :
    (A - (b : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef := by
  have hI := (Matrix.PosDef.one (n := Fin 2) (R := ℂ)).posSemidef.smul
    (Complex.zero_le_real.mpr (sub_nonneg.mpr hab))
  convert! hA.add hI using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- A lower bound for each term of the exact radial expansion gives a lower
bound for the actual discounted supply. -/
theorem supplySymbol_radial_lower_bound {ℓ : ℕ} (c : LagWeights ℓ)
    {α γ a b : ℝ} (ha : α ≤ 1) (z : ℂ)
    (hQ : (supplySymbol c 1 γ z -
      (a : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef)
    (hR : (supplyRadialRemainder c γ α z -
      (b : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef) :
    (supplySymbol c α γ z -
      ((a + (1 - α) * b : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef := by
  have h := hQ.add (hR.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr ha)))
  convert! h using 1
  rw [supplySymbol_radial_identity]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- On the circle, the zero-discount difference measures distance from the
zero-frequency point exactly. -/
theorem normSq_delaySymbol_one_eq_dist_sq {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.normSq (delaySymbol 1 z) = dist z 1 ^ 2 := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have h : delaySymbol 1 z = (z - 1) / z := by
    simp only [delaySymbol, Complex.ofReal_one, one_mul]
    field_simp
  rw [Complex.normSq_eq_norm_sq, h, norm_div, hz, div_one, dist_eq_norm]

/-- The full discounted matrix estimate from Appendix C.1. Its constants
are obtained from the actual symbol's balanced radial derivative, local
positivity and compactness on the entire unit circle. -/
theorem supplySymbol_discounted_coercivity {ℓ : ℕ} (c : LagWeights ℓ)
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) (hbalance : BalancedMoments c)
    (hcircle : HasCoercivityBound c γ κ) :
    ∃ c₀ ε : ℝ, 0 < c₀ ∧ 0 < ε ∧ ∀ α : ℝ, 1 - ε < α → α < 1 →
      ∀ z : ℂ, ‖z‖ = 1 →
        (supplySymbol c α γ z -
          ((c₀ * (Complex.normSq (delaySymbol α z) + 1 - α) : ℝ) : ℂ) •
            (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef := by
  obtain ⟨η, hη, hlocal⟩ := supplyRadialRemainder_locally_coercive c hγ hbalance
  obtain ⟨δ, hδ, hlocal⟩ := Metric.eventually_nhds_iff.mp hlocal
  obtain ⟨M, hM, hglobal⟩ := supplyRadialRemainder_uniform_lower_bound c γ
  let c₀ := min κ η / 4
  let ε := min (1 / 2 : ℝ) (min δ (min (δ ^ 2) (κ * δ ^ 2 / (4 * M))))
  have hc₀ : 0 < c₀ := div_pos (lt_min hκ hη) (by norm_num)
  have hcκ : 4 * c₀ ≤ κ := by
    dsimp [c₀]
    linarith [min_le_left κ η]
  have hcη : 4 * c₀ ≤ η := by
    dsimp [c₀]
    linarith [min_le_right κ η]
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by norm_num) (lt_min hδ
      (lt_min (sq_pos_of_pos hδ) (div_pos (mul_pos hκ (sq_pos_of_pos hδ))
        (mul_pos (by norm_num) hM))))
  have hεhalf : ε ≤ 1 / 2 := min_le_left _ _
  have hεδ : ε ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hεδ2 : ε ≤ δ ^ 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεM : ε ≤ κ * δ ^ 2 / (4 * M) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c₀, ε, hc₀, hε, ?_⟩
  intro α hαε hα1 z hz
  have hh0 : 0 ≤ 1 - α := sub_nonneg.mpr hα1.le
  have hhε : 1 - α < ε := by linarith
  have hαhalf : 1 / 2 ≤ α := by linarith
  have hh1 : 1 - α ≤ 1 := by linarith
  let D := Complex.normSq (delaySymbol 1 z)
  have hD : 0 ≤ D := Complex.normSq_nonneg _
  have hgeometry : Complex.normSq (delaySymbol α z) + 1 - α ≤ D + 2 * (1 - α) := by
    rw [normSq_delaySymbol hz]
    have hαD : α * D ≤ D := by nlinarith [mul_nonneg hh0 hD]
    nlinarith [mul_nonneg hh0 (sub_nonneg.mpr hh1)]
  have htarget : c₀ * (Complex.normSq (delaySymbol α z) + 1 - α) ≤
      c₀ * (D + 2 * (1 - α)) := mul_le_mul_of_nonneg_left hgeometry hc₀.le
  by_cases hnear : dist z 1 < δ
  · have hdist : dist (α, z) ((1 : ℝ), (1 : ℂ)) < δ := by
      rw [Prod.dist_eq]
      apply max_lt_iff.mpr
      refine ⟨?_, hnear⟩
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hα1)]
      linarith [hhε.trans_le hεδ]
    have hR := (hlocal hdist hα1.ne).posSemidef
    have hQ := supplySymbol_radial_lower_bound c hα1.le z (hcircle z hz) hR
    apply posSemidef_weaken_scalar hQ
    change c₀ * _ ≤ κ * D + (1 - α) * η
    have hcoeff1 : 0 ≤ κ - c₀ := by linarith
    have hcoeff2 : 0 ≤ η - 2 * c₀ := by linarith
    nlinarith [mul_nonneg hcoeff1 hD, mul_nonneg hcoeff2 hh0]
  · have hδD : δ ^ 2 ≤ D := by
      dsimp [D]
      rw [normSq_delaySymbol_one_eq_dist_sq hz]
      nlinarith [le_of_not_gt hnear, dist_nonneg (x := z) (y := 1)]
    have hhD : 1 - α ≤ D := (hhε.trans_le hεδ2).le.trans hδD
    have hhM' : (1 - α) * (4 * M) < κ * δ ^ 2 :=
      (lt_div_iff₀ (mul_pos (by norm_num) hM)).mp (hhε.trans_le hεM)
    have hhM : M * (1 - α) ≤ κ * D / 4 := by
      have hκD := mul_le_mul_of_nonneg_left hδD hκ.le
      nlinarith
    have hR : (supplyRadialRemainder c γ α z -
        ((-M : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef := by
      simpa using hglobal α hαhalf hα1 z hz
    have hQ := supplySymbol_radial_lower_bound c hα1.le z (hcircle z hz) hR
    apply posSemidef_weaken_scalar hQ
    change c₀ * _ ≤ κ * D + (1 - α) * (-M)
    have hcoeff : 0 ≤ 3 * κ / 4 - 3 * c₀ := by linarith
    nlinarith [mul_nonneg hcoeff hD,
      mul_nonneg hc₀.le (sub_nonneg.mpr hhD)]

end ADMM.UnitCircle
