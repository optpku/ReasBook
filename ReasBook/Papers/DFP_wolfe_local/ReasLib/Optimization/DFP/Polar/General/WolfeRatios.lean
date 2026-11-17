module

public import ReasLib.Optimization.DFP.Polar.General.Objective
public import ReasLib.Optimization.DFP.Polar.General.RadiusBounds
public import ReasLib.Optimization.DFP.Polar.WolfeRatios
public import ReasLib.Optimization.DFP.StrongWolfeCounterexample

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.Polar.General.WolfeRatios

/-- Helper for eq:polar-wolfe-asymptotics: the actual raw phase slope is the common
cycle scale times its canceled phase slope. -/
theorem omega_phase_eq (p : Parameters) (j : ℕ) (i : Fin 2) :
    DFP.Polar.omegaOf (p.matrix (2 * j + (i : ℕ))) =
      p.scale j * RadiusBounds.phaseSlope p i (p.scale j) (p.inverseIndex j)
        (p.normalizedEvenState j) := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · simp only [Fin.val_zero, Nat.add_zero]
    rw [p.matrix_even, p.evenMatrix_eq_recoverMatrix,
      PhysicalRecurrence.omega_recoverMatrix, RadiusBounds.phaseSlope_def,
      RadiusBounds.phaseInput_zero]
  · simp only [Fin.val_one]
    rw [p.matrix_odd, p.oddMatrix_eq_recoverMatrix,
      PhysicalRecurrence.omega_recoverMatrix, RadiusBounds.phaseSlope_def,
      RadiusBounds.phaseInput_one, ← p.normalizedOddState_apply]

/-- Helper for eq:polar-wolfe-asymptotics: the exact source angle increment at each phase
is its analytic angle coefficient times the original common cycle scale. -/
theorem angleIncrement_phase_eq (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (j : ℕ) (i : Fin 2) :
    p.angleIncrement (2 * j + (i : ℕ)) =
      RadiusBounds.phaseAngle p i (p.inverseIndex j) * p.scale j := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · simpa only [Fin.val_zero, Nat.add_zero, RadiusBounds.phaseAngle_zero,
      Normalized.stageAngle_def] using p.angleIncrement_even hβ hstart j
  · simpa only [Fin.val_one, RadiusBounds.phaseAngle_one, Normalized.stageAngle_def] using
      p.angleIncrement_odd hβ hstart j

/-- Helper for eq:polar-wolfe-asymptotics: the current and next gradient multipliers are
the canceled multipliers of the same actual normalized phase. -/
theorem phaseMultipliers_eq_zeta (p : Parameters) (j : ℕ) (i : Fin 2) :
    RadiusBounds.phaseMultipliers p i (p.inverseIndex j) (p.normalizedEvenState j) =
      (p.zeta (2 * j + (i : ℕ)), p.zeta (2 * j + (i : ℕ) + 1)) := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · simp only [Fin.val_zero, Nat.add_zero, RadiusBounds.phaseMultipliers_zero,
      p.zeta_even, p.zeta_odd, p.oddMultiplier_def]
  · have hindex : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
    simp only [Fin.val_one, hindex, RadiusBounds.phaseMultipliers_one,
      p.zeta_odd, p.zeta_even, p.oddMultiplier_def]

/-- Helper for thm:main: the directional pairing at the current actual source endpoint. -/
def sourceStartSlope (p : Parameters) (k : ℕ) : ℝ :=
  inner ℝ (p.gradients k) (p.point (k + 1) - p.point k)

/-- Helper for thm:main: the actual current-endpoint directional pairing formula. -/
theorem sourceStartSlope_def (p : Parameters) (k : ℕ) :
    sourceStartSlope p k = inner ℝ (p.gradients k) (p.point (k + 1) - p.point k) := by
  rfl

/-- Helper for thm:main: the directional pairing at the next actual source endpoint. -/
def sourceEndSlope (p : Parameters) (k : ℕ) : ℝ :=
  inner ℝ (p.gradients (k + 1)) (p.point (k + 1) - p.point k)

/-- Helper for thm:main: the actual accepted-endpoint directional pairing formula. -/
theorem sourceEndSlope_def (p : Parameters) (k : ℕ) :
    sourceEndSlope p k = inner ℝ (p.gradients (k + 1)) (p.point (k + 1) - p.point k) := by
  rfl

/-- Helper for eq:polar-wolfe-ratios: the exact source Armijo quotient. -/
def sourceArmijoQuotient (p : Parameters) (k : ℕ) : ℝ :=
  (p.radiusRatio k ^ 2 - 1) /
    (2 * p.zeta k * DFP.Polar.omegaOf (p.matrix k) *
      Real.sin (p.angleIncrement k) * p.radiusRatio k)

/-- Helper for eq:polar-wolfe-ratios: the exact rational source Armijo formula. -/
theorem sourceArmijoQuotient_def (p : Parameters) (k : ℕ) :
    sourceArmijoQuotient p k = (p.radiusRatio k ^ 2 - 1) /
      (2 * p.zeta k * DFP.Polar.omegaOf (p.matrix k) *
        Real.sin (p.angleIncrement k) * p.radiusRatio k) := by
  rfl

/-- Helper for eq:polar-wolfe-ratios: the exact source strong-curvature quotient. -/
def sourceCurvatureQuotient (p : Parameters) (k : ℕ) : ℝ :=
  (p.zeta (k + 1) / p.zeta k) *
    |DFP.Polar.omegaOf (p.matrix k) * Real.cos (p.angleIncrement k) -
      Real.sin (p.angleIncrement k)| /
      (DFP.Polar.omegaOf (p.matrix k) * p.radiusRatio k)

/-- Helper for eq:polar-wolfe-ratios: the exact rational source strong-curvature formula. -/
theorem sourceCurvatureQuotient_def (p : Parameters) (k : ℕ) :
    sourceCurvatureQuotient p k = (p.zeta (k + 1) / p.zeta k) *
      |DFP.Polar.omegaOf (p.matrix k) * Real.cos (p.angleIncrement k) -
        Real.sin (p.angleIncrement k)| / (DFP.Polar.omegaOf (p.matrix k) * p.radiusRatio k) := by
  rfl

/-- Helper for eq:polar-wolfe-ratios: the true source endpoint pairings have the exact
radial formulas with their common current radius. -/
theorem sourceSlope_formulas (p : Parameters) (k : ℕ)
    (hbalance : p.radius k = p.radiusRatio k * p.radius (k + 1))
    (hW : p.radiusRatio k ≠ 0) :
    -sourceStartSlope p k = p.zeta k * p.radius k ^ 2 * DFP.Polar.omegaOf (p.matrix k) *
        Real.sin (p.angleIncrement k) / p.radiusRatio k ∧
      sourceEndSlope p k = p.zeta (k + 1) * p.radius k ^ 2 * Real.sin (p.angleIncrement k) /
        p.radiusRatio k ^ 2 *
          (Real.sin (p.angleIncrement k) -
            DFP.Polar.omegaOf (p.matrix k) * Real.cos (p.angleIncrement k)) := by
  have hmul : p.radius (k + 1) * p.radiusRatio k = p.radius k := by
    rw [mul_comm]
    exact hbalance.symm
  have hnext : p.radius (k + 1) = p.radius k / p.radiusRatio k := (eq_div_iff hW).mpr hmul
  have hraw : p.radius (k + 1) *
      DFP.Polar.radiusRatioOf (p.matrix k) (p.angleIncrement k) = p.radius k := by
    rwa [← p.radiusRatio_def]
  constructor
  · rw [sourceStartSlope]
    simp only [p.gradients_def, p.point_def, p.angle_succ]
    rw [DFP.Polar.WolfeRatios.radial_start_pairing _ _ _ _ _ _ hraw, hnext]
    field_simp
  · rw [sourceEndSlope]
    simp only [p.gradients_def, p.point_def, p.angle_succ]
    rw [DFP.Polar.WolfeRatios.radial_end_pairing _ _ _ _ _ _ hraw, hnext]
    field_simp

/-- Helper for thm:main: positive definiteness and a positive off-diagonal entry make the
actual normalized source slope positive. -/
theorem sourceOmega_pos (p : Parameters) (k : ℕ) (hZ : (p.matrix k).PosDef)
    (hC : 0 < p.matrix k 0 1) : 0 < DFP.Polar.omegaOf (p.matrix k) := by
  rw [DFP.Polar.omegaOf_def]
  exact div_pos hZ.diag_pos hC

/-- Helper for thm:main: physical source feasibility makes every actual source chord
a descent step. -/
theorem sourceStartSlope_neg (p : Parameters) (k : ℕ)
    (hbalance : p.radius k = p.radiusRatio k * p.radius (k + 1))
    (hZ : (p.matrix k).PosDef) (hC : 0 < p.matrix k 0 1)
    (hSin : 0 < Real.sin (p.angleIncrement k)) (hW : 0 < p.radiusRatio k)
    (hr : 0 < p.radius k) : sourceStartSlope p k < 0 := by
  have hformula := (sourceSlope_formulas p k hbalance hW.ne').1
  have hpositive : 0 < -sourceStartSlope p k := by
    rw [hformula]
    exact div_pos (mul_pos (mul_pos (mul_pos (p.zeta_pos k) (sq_pos_of_pos hr))
      (sourceOmega_pos p k hZ hC)) hSin) hW
  exact neg_pos.mp hpositive

/-- Helper for eq:polar-wolfe-ratios: exact cancellation identifies the actual endpoint
ratios with the source raw quotients for every feasible stage. -/
theorem sourceSlope_ratios (p : Parameters) (k : ℕ)
    (hbalance : p.radius k = p.radiusRatio k * p.radius (k + 1))
    (hZ : (p.matrix k).PosDef) (hC : 0 < p.matrix k 0 1)
    (hSin : 0 < Real.sin (p.angleIncrement k)) (hW : 0 < p.radiusRatio k)
    (hr : 0 < p.radius k) :
    (p.radius k ^ 2 / 2 - p.radius (k + 1) ^ 2 / 2) / (-sourceStartSlope p k) =
        sourceArmijoQuotient p k ∧
      |sourceEndSlope p k| / |sourceStartSlope p k| = sourceCurvatureQuotient p k := by
  have hω := sourceOmega_pos p k hZ hC
  have hnext : p.radius (k + 1) = p.radius k / p.radiusRatio k := by
    apply (eq_div_iff hW.ne').mpr
    rw [mul_comm]
    exact hbalance.symm
  have hstart : sourceStartSlope p k =
      -(p.zeta k * p.radius k ^ 2 * DFP.Polar.omegaOf (p.matrix k) *
        Real.sin (p.angleIncrement k) / p.radiusRatio k) := by
    linarith [(sourceSlope_formulas p k hbalance hW.ne').1]
  constructor
  · rw [(sourceSlope_formulas p k hbalance hW.ne').1, hnext, sourceArmijoQuotient]
    exact DFP.Polar.WolfeRatios.armijo_scalar _ _ _ _ _ hr.ne' hω.ne'
      (p.zeta_pos k).ne' hSin.ne' hW.ne'
  · rw [hstart, (sourceSlope_formulas p k hbalance hW.ne').2, sourceCurvatureQuotient]
    exact DFP.Polar.WolfeRatios.curvature_scalar _ _ _ _ _ _ hr hω
      (p.zeta_pos k) (p.zeta_pos (k + 1)) hSin hW

/-- Helper for thm:main: exact interpolation and source raw quotient margins give the
standard strong Wolfe conditions for the actual explicit source objective. -/
theorem sourceStrongWolfe_of_rawQuotients (p : Parameters) (κ δ H : ℝ)
    (hc1 : 0 < p.c1) (hc12 : p.c1 < p.c2) (hc2 : p.c2 < 1)
    (hobjective : Objective.ObjectiveEstimates p κ δ H)
    (hZ : ∀ k, (p.matrix k).PosDef) (hC : ∀ k, 0 < p.matrix k 0 1)
    (hSin : ∀ k, 0 < Real.sin (p.angleIncrement k)) (hW : ∀ k, 0 < p.radiusRatio k)
    (hr : ∀ k, 0 < p.radius k)
    (hlog : Summable (fun j ↦ Real.log (p.radiusRatio (2 * j) * p.radiusRatio (2 * j + 1))))
    (hquotients : ∀ k, p.c1 ≤ sourceArmijoQuotient p k ∧ sourceCurvatureQuotient p k ≤ p.c2)
    (k : ℕ) :
    LineSearch.IsStrongWolfe p.c1 p.c2 (p.objective κ) (p.point k)
      (p.point (k + 1) - p.point k) := by
  have hbalance := p.radius_recurrence hW hlog k
  have hratios := sourceSlope_ratios p k hbalance (hZ k) (hC k) (hSin k) (hW k) (hr k)
  have hdescent := sourceStartSlope_neg p k hbalance (hZ k) (hC k) (hSin k) (hW k) (hr k)
  have hdecrease : p.c1 * (-sourceStartSlope p k) ≤
      p.radius k ^ 2 / 2 - p.radius (k + 1) ^ 2 / 2 := by
    apply (le_div_iff₀ (neg_pos.mpr hdescent)).mp
    rw [hratios.1]
    exact (hquotients k).1
  have hcurvature : |sourceEndSlope p k| ≤ p.c2 * |sourceStartSlope p k| := by
    apply (div_le_iff₀ (abs_pos.mpr hdescent.ne)).mp
    rw [hratios.2]
    exact (hquotients k).2
  have hnext : p.point k + (p.point (k + 1) - p.point k) = p.point (k + 1) := by abel
  have hgradientNext : HasGradientAt (p.objective κ) (p.gradients (k + 1))
      (p.point k + (p.point (k + 1) - p.point k)) := by
    rw [hnext]
    exact p.hasGradientAt_objective_center κ hobjective.geometry _
  apply LineSearch.IsStrongWolfe.ofHasGradientAt hc1 hc12 hc2
    (p.hasGradientAt_objective_center κ hobjective.geometry k) hgradientNext
  · rw [hnext, (hobjective.endpoints k).1, (hobjective.endpoints (k + 1)).1]
    dsimp [sourceStartSlope] at hdecrease
    linarith
  · exact hcurvature

/-- Helper for eq:polar-wolfe-asymptotics: the canceled phase observables are exactly the
actual source endpoint quotients on the same recursive trajectory. -/
theorem sourceQuotients_eq_phase (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (j : ℕ) (i : Fin 2) :
    sourceArmijoQuotient p (2 * j + (i : ℕ)) =
        RadiusBounds.phaseArmijo p i (p.scale j) (p.inverseIndex j) (p.normalizedEvenState j) ∧
      sourceCurvatureQuotient p (2 * j + (i : ℕ)) =
        RadiusBounds.phaseCurvature p i (p.scale j) (p.inverseIndex j)
          (p.normalizedEvenState j) := by
  have ht : 0 < p.scale j := by
    rw [p.scale_def]
    exact scale_pos p.beta hstart j
  constructor
  · rw [RadiusBounds.phaseArmijo_eq_raw p i ht.ne', phaseMultipliers_eq_zeta]
    simp only [sourceArmijoQuotient, omega_phase_eq p j i,
      angleIncrement_phase_eq p hβ hstart j i,
      RadiusBounds.radiusRatio_eq_phaseRadius p hβ hstart j i]
  · rw [RadiusBounds.phaseCurvature_eq_raw p i ht, phaseMultipliers_eq_zeta]
    simp only [sourceCurvatureQuotient, omega_phase_eq p j i,
      angleIncrement_phase_eq p hβ hstart j i,
      RadiusBounds.radiusRatio_eq_phaseRadius p hβ hstart j i]

/-- Helper for thm:main: the strict phase margins proved for the actual tube imply the
standard strong Wolfe inequalities for the interpolated source objective at every index. -/
theorem sourceStrongWolfe_of_phaseMargins (p : Parameters) (κ δ H : ℝ)
    (hβ : 0 < p.beta) (hstart : 0 < p.startIndex)
    (hc1 : 0 < p.c1) (hc12 : p.c1 < p.c2) (hc2 : p.c2 < 1)
    (hobjective : Objective.ObjectiveEstimates p κ δ H)
    (hZ : ∀ k, (p.matrix k).PosDef) (hC : ∀ k, 0 < p.matrix k 0 1)
    (hSin : ∀ k, 0 < Real.sin (p.angleIncrement k)) (hW : ∀ k, 0 < p.radiusRatio k)
    (hr : ∀ k, 0 < p.radius k)
    (hlog : Summable (fun j ↦ Real.log (p.radiusRatio (2 * j) * p.radiusRatio (2 * j + 1))))
    (hphase : ∀ j : ℕ, ∀ i : Fin 2,
      p.c1 < RadiusBounds.phaseArmijo p i (p.scale j) (p.inverseIndex j) (p.normalizedEvenState j) ∧
        RadiusBounds.phaseCurvature p i (p.scale j) (p.inverseIndex j)
          (p.normalizedEvenState j) < p.c2)
    (k : ℕ) :
    LineSearch.IsStrongWolfe p.c1 p.c2 (p.objective κ) (p.point k)
      (p.point (k + 1) - p.point k) := by
  apply sourceStrongWolfe_of_rawQuotients p κ δ H hc1 hc12 hc2 hobjective
    hZ hC hSin hW hr hlog
  intro k
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have h := hphase j 0
    have hquot := sourceQuotients_eq_phase p hβ hstart j 0
    rw [← hquot.1, ← hquot.2] at h
    simpa only [Fin.val_zero, Nat.add_zero] using And.intro h.1.le h.2.le
  · have h := hphase j 1
    have hquot := sourceQuotients_eq_phase p hβ hstart j 1
    rw [← hquot.1, ← hquot.2] at h
    simpa only [Fin.val_one] using And.intro h.1.le h.2.le

end DFP.Polar.General.WolfeRatios
