/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Assumption_2_1.Regularity

public section

open scoped NNReal

namespace KKT

variable {n m : ℕ}

/-- The stationarity vector for an equality-constrained optimization problem. -/
@[expose] noncomputable def stationarity
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (multiplier : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin n) :=
  gradient f x + EqualityConstrained.constraintGradient c x multiplier

/-- The stationarity vector is the objective gradient plus the constraint-gradient
operator applied to the multiplier. -/
theorem stationarity_def
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (multiplier : EuclideanSpace ℝ (Fin m)) :
    stationarity f c x multiplier =
      gradient f x + EqualityConstrained.constraintGradient c x multiplier := rfl

/-- The two componentwise bounds certifying an approximate KKT pair. -/
structure IsApproximatePair
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ε : ℝ≥0) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) : Prop where
  /-- The stationarity residual is at most `ε`. -/
  stationarity_le : ‖stationarity f c x multiplier‖ ≤ ε
  /-- The feasibility residual is at most `ε`. -/
  feasibility_le : ‖c x‖ ≤ ε

namespace IsApproximatePair

/-- Construct an approximate KKT pair certificate from its two componentwise bounds. -/
theorem ofBounds
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ε : ℝ≥0} {x : EuclideanSpace ℝ (Fin n)}
    {multiplier : EuclideanSpace ℝ (Fin m)}
    (stationarity_le : ‖stationarity f c x multiplier‖ ≤ ε)
    (feasibility_le : ‖c x‖ ≤ ε) :
    IsApproximatePair f c ε x multiplier :=
  ⟨stationarity_le, feasibility_le⟩

end IsApproximatePair

/-- An approximate KKT pair is equivalent to its stationarity and feasibility bounds. -/
theorem isApproximatePair_iff
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ε : ℝ≥0) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) :
    IsApproximatePair f c ε x multiplier ↔
      ‖stationarity f c x multiplier‖ ≤ ε ∧ ‖c x‖ ≤ ε :=
  ⟨fun h ↦ ⟨h.stationarity_le, h.feasibility_le⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- A point is approximately KKT when some multiplier certifies an approximate KKT pair. -/
def IsApproximatePoint
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ε : ℝ≥0) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ multiplier : EuclideanSpace ℝ (Fin m), IsApproximatePair f c ε x multiplier

/-- The approximate KKT point predicate exposes its multiplier certificate. -/
theorem isApproximatePoint_iff
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ε : ℝ≥0) (x : EuclideanSpace ℝ (Fin n)) :
    IsApproximatePoint f c ε x ↔
      ∃ multiplier : EuclideanSpace ℝ (Fin m), IsApproximatePair f c ε x multiplier := Iff.rfl

/-- An exact KKT pair is an approximate KKT pair with zero tolerance. -/
def IsPair
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (multiplier : EuclideanSpace ℝ (Fin m)) : Prop :=
  IsApproximatePair f c 0 x multiplier

/-- An exact KKT pair is characterized by zero stationarity and feasibility vectors. -/
theorem isPair_iff
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (multiplier : EuclideanSpace ℝ (Fin m)) :
    IsPair f c x multiplier ↔ stationarity f c x multiplier = 0 ∧ c x = 0 := by
  -- At zero tolerance, each norm bound is equivalent to vanishing of its vector.
  simp only [IsPair, isApproximatePair_iff, NNReal.coe_zero, norm_le_zero_iff]

/-- An exact KKT point is an approximate KKT point with zero tolerance. -/
def IsPoint
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  IsApproximatePoint f c 0 x

/-- An exact KKT point has a multiplier with zero stationarity and feasibility vectors. -/
theorem isPoint_iff
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) :
    IsPoint f c x ↔ ∃ multiplier : EuclideanSpace ℝ (Fin m),
      stationarity f c x multiplier = 0 ∧ c x = 0 := by
  -- Transport the multiplier witness through the exact-pair characterization.
  rw [IsPoint, isApproximatePoint_iff]
  constructor
  · rintro ⟨multiplier, hpair⟩
    refine Exists.intro multiplier ?_
    exact (isPair_iff f c x multiplier).mp hpair
  · rintro ⟨multiplier, hzero⟩
    refine Exists.intro multiplier ?_
    exact (isPair_iff f c x multiplier).mpr hzero

/-- The aggregate Euclidean residual of stationarity and feasibility. -/
@[expose] noncomputable def residual
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (multiplier : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Real.sqrt (‖stationarity f c x multiplier‖ ^ 2 + ‖c x‖ ^ 2)

/-- The aggregate residual is the square root of the sum of squared component residuals. -/
theorem residual_def
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (multiplier : EuclideanSpace ℝ (Fin m)) :
    residual f c x multiplier =
      Real.sqrt (‖stationarity f c x multiplier‖ ^ 2 + ‖c x‖ ^ 2) := rfl

/-- Primal--multiplier pairs whose primal coordinate lies in a regularity region. -/
def regularityPairRegion
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (h : EqualityConstrained.Regularity f c) :
    Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
  Prod.fst ⁻¹' h.region

/-- The regularity pair region is open. -/
theorem isOpen_regularityPairRegion
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (h : EqualityConstrained.Regularity f c) :
    IsOpen (regularityPairRegion h) :=
  h.isOpen_region.preimage continuous_fst

/-- Stationarity is continuous while the primal coordinate stays in the regularity region. -/
theorem continuousOn_stationarity
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (h : EqualityConstrained.Regularity f c) :
    ContinuousOn
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        stationarity f c z.1 z.2)
      (regularityPairRegion h) := by
  intro z hz
  change z.1 ∈ h.region at hz
  have hGradient : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        gradient f z.1) z :=
    (h.continuousAt_gradient hz).comp continuous_fst.continuousAt
  have hConstraintGradient : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        EqualityConstrained.constraintGradient c z.1) z :=
    (h.continuousAt_constraintGradient hz).comp continuous_fst.continuousAt
  have hStationarity : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        gradient f z.1 + EqualityConstrained.constraintGradient c z.1 z.2) z :=
    hGradient.add (hConstraintGradient.clm_apply continuous_snd.continuousAt)
  simpa only [stationarity_def] using hStationarity.continuousWithinAt

/-- The aggregate KKT residual is continuous while the primal coordinate stays regular. -/
theorem continuousOn_residual
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (h : EqualityConstrained.Regularity f c) :
    ContinuousOn
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        residual f c z.1 z.2)
      (regularityPairRegion h) := by
  intro z hz
  have hStationarity : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        stationarity f c z.1 z.2) z :=
    (continuousOn_stationarity h).continuousAt
      ((isOpen_regularityPairRegion h).mem_nhds hz)
  change z.1 ∈ h.region at hz
  have hConstraint : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦ c z.1) z :=
    (h.continuousAt_constraint hz).comp continuous_fst.continuousAt
  have hResidualSquare : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        ‖stationarity f c z.1 z.2‖ ^ 2 + ‖c z.1‖ ^ 2) z :=
    (hStationarity.norm.pow 2).add (hConstraint.norm.pow 2)
  have hResidual : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        Real.sqrt (‖stationarity f c z.1 z.2‖ ^ 2 + ‖c z.1‖ ^ 2)) z :=
    Real.continuous_sqrt.continuousAt.comp hResidualSquare
  simpa only [residual_def] using hResidual.continuousWithinAt

/-- Stationarity extended by zero outside the regularity pair region. -/
noncomputable def stationarityExtension
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (h : EqualityConstrained.Regularity f c) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin n) :=
  @Set.piecewise _ _ (regularityPairRegion h)
    (fun z ↦ stationarity f c z.1 z.2) (fun _ ↦ 0)
    (fun z ↦ Classical.propDecidable (z ∈ regularityPairRegion h))

/-- The stationarity extension agrees with stationarity at every regular primal point. -/
theorem stationarityExtension_eq
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (h : EqualityConstrained.Regularity f c)
    {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)}
    (hz : z.1 ∈ h.region) :
    stationarityExtension h z = stationarity f c z.1 z.2 := by
  classical
  have hzPair : z ∈ regularityPairRegion h := hz
  simp only [stationarityExtension, Set.piecewise, if_pos hzPair]

/-- The zero extension of stationarity is globally measurable. -/
theorem measurable_stationarityExtension
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (h : EqualityConstrained.Regularity f c) :
    Measurable (stationarityExtension h) := by
  classical
  simpa only [stationarityExtension] using
    (continuousOn_stationarity h).measurable_piecewise
      continuous_const.continuousOn (isOpen_regularityPairRegion h).measurableSet

/-- The aggregate KKT residual extended by zero outside the regularity pair region. -/
noncomputable def residualExtension
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (h : EqualityConstrained.Regularity f c) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ :=
  @Set.piecewise _ _ (regularityPairRegion h)
    (fun z ↦ residual f c z.1 z.2) (fun _ ↦ 0)
    (fun z ↦ Classical.propDecidable (z ∈ regularityPairRegion h))

/-- The residual extension agrees with the aggregate residual at every regular primal point. -/
theorem residualExtension_eq
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (h : EqualityConstrained.Regularity f c)
    {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)}
    (hz : z.1 ∈ h.region) :
    residualExtension h z = residual f c z.1 z.2 := by
  classical
  have hzPair : z ∈ regularityPairRegion h := hz
  simp only [residualExtension, Set.piecewise, if_pos hzPair]

/-- The zero extension of the aggregate KKT residual is globally measurable. -/
theorem measurable_residualExtension
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (h : EqualityConstrained.Regularity f c) :
    Measurable (residualExtension h) := by
  classical
  simpa only [residualExtension] using
    (continuousOn_residual h).measurable_piecewise
      continuous_const.continuousOn (isOpen_regularityPairRegion h).measurableSet

namespace IsApproximatePair

/-- An aggregate residual bound implies both componentwise approximate KKT bounds. -/
theorem of_residual_le
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ε : ℝ≥0} {x : EuclideanSpace ℝ (Fin n)}
    {multiplier : EuclideanSpace ℝ (Fin m)}
    (h : residual f c x multiplier ≤ ε) :
    IsApproximatePair f c ε x multiplier := by
  -- Expose the aggregate square root once, then compare each squared component to its sum.
  rw [residual_def] at h
  refine ofBounds ?_ ?_
  · calc
      ‖stationarity f c x multiplier‖ =
          Real.sqrt (‖stationarity f c x multiplier‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt
          (‖stationarity f c x multiplier‖ ^ 2 + ‖c x‖ ^ 2) :=
        Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
      _ ≤ (ε : ℝ) := h
  · calc
      ‖c x‖ = Real.sqrt (‖c x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt
          (‖stationarity f c x multiplier‖ ^ 2 + ‖c x‖ ^ 2) :=
        Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
      _ ≤ (ε : ℝ) := h

end IsApproximatePair

end KKT

end
