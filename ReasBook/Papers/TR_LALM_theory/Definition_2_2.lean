/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Definition_2_2.KKT

public section

open scoped NNReal

/- Definition 2.2 (1): an `ε`-KKT point has a multiplier certifying both
stationarity and feasibility to tolerance `ε`. -/

/- Definition 2.2 (2): a specified point-multiplier pair satisfying both bounds is
an `ε`-KKT pair. -/

/- Definition 2.2 (3): a KKT point is an approximate KKT point with tolerance zero. -/

/- Definition 2.2 (4): a KKT pair is an approximate KKT pair with tolerance zero. -/

/- Definition 2.2 (5): the aggregate residual is the square root of the sum of the
squared stationarity and feasibility residuals. -/

/- Definition 2.2 (6): an aggregate residual at most `ε` certifies an `ε`-KKT pair. -/

/-- Definition 2.2 (7): every `ε`-KKT pair has aggregate residual at most `√2 * ε`. -/
theorem KKT.IsApproximatePair.residual_le
    {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ε : ℝ≥0} {x : EuclideanSpace ℝ (Fin n)}
    {multiplier : EuclideanSpace ℝ (Fin m)}
    (h : KKT.IsApproximatePair f c ε x multiplier) :
    KKT.residual f c x multiplier ≤ Real.sqrt 2 * ε := by
  -- Square the component bounds and add them before taking the monotone square root.
  have stationarity_sq_le :
      ‖KKT.stationarity f c x multiplier‖ ^ 2 ≤ (ε : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) ε.coe_nonneg).mpr h.stationarity_le
  have feasibility_sq_le : ‖c x‖ ^ 2 ≤ (ε : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) ε.coe_nonneg).mpr h.feasibility_le
  have component_sq_sum_le :
      ‖KKT.stationarity f c x multiplier‖ ^ 2 + ‖c x‖ ^ 2 ≤
        (ε : ℝ) ^ 2 + (ε : ℝ) ^ 2 :=
    add_le_add stationarity_sq_le feasibility_sq_le
  -- Normalize the doubled tolerance square as `sqrt 2 * ε`.
  calc
    KKT.residual f c x multiplier =
        Real.sqrt (‖KKT.stationarity f c x multiplier‖ ^ 2 + ‖c x‖ ^ 2) :=
      KKT.residual_def f c x multiplier
    _ ≤ Real.sqrt ((ε : ℝ) ^ 2 + (ε : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt component_sq_sum_le
    _ = Real.sqrt (2 * (ε : ℝ) ^ 2) :=
      congrArg Real.sqrt (two_mul ((ε : ℝ) ^ 2)).symm
    _ = Real.sqrt 2 * Real.sqrt ((ε : ℝ) ^ 2) :=
      Real.sqrt_mul zero_le_two ((ε : ℝ) ^ 2)
    _ = Real.sqrt 2 * (ε : ℝ) :=
      congrArg (fun t : ℝ ↦ Real.sqrt 2 * t) (Real.sqrt_sq ε.coe_nonneg)

end
