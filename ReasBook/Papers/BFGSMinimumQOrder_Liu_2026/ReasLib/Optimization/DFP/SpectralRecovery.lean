module

public import ReasLib.Optimization.DFP.CycleBoundaryState

public section

namespace CycleBoundaryState

/-- The canonical radius determined by ordered spectral values and oriented gradient
coordinates. -/
noncomputable def recoveryRadius
    (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ) : ℝ :=
  lambdaMinus * gammaMinus / (lambdaPlus * gammaPlus)

/-- The canonical shape parameter determined by ordered spectral values and oriented gradient
coordinates. -/
noncomputable def recoveryShape
    (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ) : ℝ :=
  lambdaPlus * gammaPlus ^ 2 / (lambdaMinus * gammaMinus ^ 2)

/-- The recovered radius is positive for positive ordered spectral values and positive oriented
gradient coordinates. -/
theorem recoveryRadius_pos (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ)
    (lambdaMinus_pos : 0 < lambdaMinus) (lambda_order : lambdaMinus < lambdaPlus)
    (gammaMinus_pos : 0 < gammaMinus) (gammaPlus_pos : 0 < gammaPlus) :
    0 < recoveryRadius lambdaMinus lambdaPlus gammaMinus gammaPlus := by
  -- The spectral ordering first makes the high spectral value positive.
  have lambdaPlus_pos : 0 < lambdaPlus := lambdaMinus_pos.trans lambda_order
  -- Positivity is preserved by each product in the recovery quotient.
  have numerator_pos : 0 < lambdaMinus * gammaMinus :=
    mul_pos lambdaMinus_pos gammaMinus_pos
  have denominator_pos : 0 < lambdaPlus * gammaPlus :=
    mul_pos lambdaPlus_pos gammaPlus_pos
  -- Unfold the recovery formula and apply positivity of division.
  simpa only [recoveryRadius] using div_pos numerator_pos denominator_pos

/-- The recovered shape is positive for positive ordered spectral values and positive oriented
gradient coordinates. -/
theorem recoveryShape_pos (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ)
    (lambdaMinus_pos : 0 < lambdaMinus) (lambda_order : lambdaMinus < lambdaPlus)
    (gammaMinus_pos : 0 < gammaMinus) (gammaPlus_pos : 0 < gammaPlus) :
    0 < recoveryShape lambdaMinus lambdaPlus gammaMinus gammaPlus := by
  -- The ordering makes the high spectral value positive.
  have lambdaPlus_pos : 0 < lambdaPlus := lambdaMinus_pos.trans lambda_order
  -- Both products in the recovery quotient are positive.
  have numerator_pos : 0 < lambdaPlus * gammaPlus ^ 2 :=
    mul_pos lambdaPlus_pos (pow_pos gammaPlus_pos 2)
  have denominator_pos : 0 < lambdaMinus * gammaMinus ^ 2 :=
    mul_pos lambdaMinus_pos (pow_pos gammaMinus_pos 2)
  -- Division of these positive products proves positivity of the shape.
  simpa only [recoveryShape] using div_pos numerator_pos denominator_pos

/-- The product of the recovered shape and radius is the ratio of the oriented gradient
coordinates. -/
theorem recoveryShape_mul_radius (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ)
    (lambdaMinus_pos : 0 < lambdaMinus) (lambda_order : lambdaMinus < lambdaPlus)
    (gammaMinus_pos : 0 < gammaMinus) (gammaPlus_pos : 0 < gammaPlus) :
    recoveryShape lambdaMinus lambdaPlus gammaMinus gammaPlus *
        recoveryRadius lambdaMinus lambdaPlus gammaMinus gammaPlus =
      gammaPlus / gammaMinus := by
  -- Positivity supplies every nonvanishing denominator in the recovery formulas.
  have lambdaPlus_ne : lambdaPlus ≠ 0 := (lambdaMinus_pos.trans lambda_order).ne'
  have lambdaMinus_ne : lambdaMinus ≠ 0 := lambdaMinus_pos.ne'
  have gammaPlus_ne : gammaPlus ≠ 0 := gammaPlus_pos.ne'
  have gammaMinus_ne : gammaMinus ≠ 0 := gammaMinus_pos.ne'
  -- Clearing those denominators reduces the invariant to a polynomial identity.
  unfold recoveryShape recoveryRadius
  field_simp

/-- The high spectral value times the recovered shape and squared radius is the low spectral
value. -/
theorem recoveryHigh_mul_shape_mul_radius_sq
    (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ)
    (lambdaMinus_pos : 0 < lambdaMinus) (lambda_order : lambdaMinus < lambdaPlus)
    (gammaMinus_pos : 0 < gammaMinus) (gammaPlus_pos : 0 < gammaPlus) :
    lambdaPlus * recoveryShape lambdaMinus lambdaPlus gammaMinus gammaPlus *
        recoveryRadius lambdaMinus lambdaPlus gammaMinus gammaPlus ^ 2 =
      lambdaMinus := by
  -- Positivity supplies every nonvanishing denominator in the recovery formulas.
  have lambdaPlus_ne : lambdaPlus ≠ 0 := (lambdaMinus_pos.trans lambda_order).ne'
  have lambdaMinus_ne : lambdaMinus ≠ 0 := lambdaMinus_pos.ne'
  have gammaPlus_ne : gammaPlus ≠ 0 := gammaPlus_pos.ne'
  have gammaMinus_ne : gammaMinus ≠ 0 := gammaMinus_pos.ne'
  -- Clearing those denominators reduces the invariant to a polynomial identity.
  unfold recoveryShape recoveryRadius
  field_simp

/-- Positive canonical parameters satisfy the spectral and oriented-gradient coordinate
equations exactly when they are given by the recovery formulas. -/
theorem recovery_iff (lambdaMinus lambdaPlus gammaMinus gammaPlus G h r p : ℝ)
    (lambdaMinus_pos : 0 < lambdaMinus) (lambda_order : lambdaMinus < lambdaPlus)
    (gammaMinus_pos : 0 < gammaMinus) (gammaPlus_pos : 0 < gammaPlus)
    (G_pos : 0 < G) (h_pos : 0 < h) (r_pos : 0 < r) (p_pos : 0 < p) :
    (lambdaMinus = h * p * r ^ 2 ∧ lambdaPlus = h ∧ gammaMinus = G ∧
        gammaPlus = G * p * r) ↔
      (G = gammaMinus ∧ h = lambdaPlus ∧
        r = recoveryRadius lambdaMinus lambdaPlus gammaMinus gammaPlus ∧
        p = recoveryShape lambdaMinus lambdaPlus gammaMinus gammaPlus) := by
  constructor
  · rintro ⟨hlambdaMinus, hlambdaPlus, hgammaMinus, hgammaPlus⟩
    -- Substitute the four coordinate equations before normalizing the quotients.
    subst lambdaMinus
    subst lambdaPlus
    subst gammaMinus
    subst gammaPlus
    refine ⟨rfl, rfl, ?_, ?_⟩
    · -- The recovered radius cancels all positive canonical parameters.
      unfold recoveryRadius
      field_simp [G_pos.ne', h_pos.ne', r_pos.ne', p_pos.ne']
    · -- The recovered shape cancels all positive canonical parameters.
      unfold recoveryShape
      field_simp [G_pos.ne', h_pos.ne', r_pos.ne', p_pos.ne']
  · rintro ⟨hG, hh, hr, hp⟩
    -- Replace the canonical parameters by their recovered formulas.
    subst G
    subst h
    subst r
    subst p
    refine ⟨?_, rfl, rfl, ?_⟩
    · -- The second recovery invariant reconstructs the low spectral value.
      exact (recoveryHigh_mul_shape_mul_radius_sq lambdaMinus lambdaPlus gammaMinus gammaPlus
        lambdaMinus_pos lambda_order gammaMinus_pos gammaPlus_pos).symm
    · -- The first recovery invariant reconstructs the high gradient coordinate.
      rw [mul_assoc, recoveryShape_mul_radius lambdaMinus lambdaPlus gammaMinus gammaPlus
        lambdaMinus_pos lambda_order gammaMinus_pos gammaPlus_pos]
      field_simp [gammaMinus_pos.ne']

/-- Construct the canonical cycle-boundary state determined by positive ordered spectral values,
positive oriented gradient coordinates, and an oriented unit low direction. -/
noncomputable def ofSpectral (e : EuclideanSpace ℝ (Fin 2))
    (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ) (e_norm : ‖e‖ = 1)
    (lambdaMinus_pos : 0 < lambdaMinus) (lambda_order : lambdaMinus < lambdaPlus)
    (gammaMinus_pos : 0 < gammaMinus) (gammaPlus_pos : 0 < gammaPlus) :
    CycleBoundaryState :=
  -- Route correction: the imported `ofParams` body is opaque here, so construct the same record
  -- directly to expose the four projection equations to this module.
  { e := e
    r := recoveryRadius lambdaMinus lambdaPlus gammaMinus gammaPlus
    p := recoveryShape lambdaMinus lambdaPlus gammaMinus gammaPlus
    h := lambdaPlus
    amplitude := gammaMinus
    e_norm := e_norm
    r_pos := recoveryRadius_pos lambdaMinus lambdaPlus gammaMinus gammaPlus lambdaMinus_pos
      lambda_order gammaMinus_pos gammaPlus_pos
    p_pos := recoveryShape_pos lambdaMinus lambdaPlus gammaMinus gammaPlus lambdaMinus_pos
      lambda_order gammaMinus_pos gammaPlus_pos
    h_pos := lambdaMinus_pos.trans lambda_order
    amplitude_pos := gammaMinus_pos }

/-- The radius projection of a spectrally recovered state is its recovery formula. -/
theorem ofSpectral_r (e : EuclideanSpace ℝ (Fin 2))
    (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ) (e_norm : ‖e‖ = 1)
    (lambdaMinus_pos : 0 < lambdaMinus) (lambda_order : lambdaMinus < lambdaPlus)
    (gammaMinus_pos : 0 < gammaMinus) (gammaPlus_pos : 0 < gammaPlus) :
    (ofSpectral e lambdaMinus lambdaPlus gammaMinus gammaPlus e_norm lambdaMinus_pos lambda_order
      gammaMinus_pos gammaPlus_pos).r =
      recoveryRadius lambdaMinus lambdaPlus gammaMinus gammaPlus := by
  -- The constructor stores the recovery radius without further transformation.
  rfl

/-- The shape projection of a spectrally recovered state is its recovery formula. -/
theorem ofSpectral_p (e : EuclideanSpace ℝ (Fin 2))
    (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ) (e_norm : ‖e‖ = 1)
    (lambdaMinus_pos : 0 < lambdaMinus) (lambda_order : lambdaMinus < lambdaPlus)
    (gammaMinus_pos : 0 < gammaMinus) (gammaPlus_pos : 0 < gammaPlus) :
    (ofSpectral e lambdaMinus lambdaPlus gammaMinus gammaPlus e_norm lambdaMinus_pos lambda_order
      gammaMinus_pos gammaPlus_pos).p =
      recoveryShape lambdaMinus lambdaPlus gammaMinus gammaPlus := by
  -- The constructor stores the recovery shape without further transformation.
  rfl

/-- The high-metric projection of a spectrally recovered state is its high spectral value. -/
theorem ofSpectral_h (e : EuclideanSpace ℝ (Fin 2))
    (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ) (e_norm : ‖e‖ = 1)
    (lambdaMinus_pos : 0 < lambdaMinus) (lambda_order : lambdaMinus < lambdaPlus)
    (gammaMinus_pos : 0 < gammaMinus) (gammaPlus_pos : 0 < gammaPlus) :
    (ofSpectral e lambdaMinus lambdaPlus gammaMinus gammaPlus e_norm lambdaMinus_pos lambda_order
      gammaMinus_pos gammaPlus_pos).h = lambdaPlus := by
  -- The constructor stores the high spectral value as its high metric parameter.
  rfl

/-- The amplitude projection of a spectrally recovered state is its low oriented gradient
coordinate. -/
theorem ofSpectral_amplitude (e : EuclideanSpace ℝ (Fin 2))
    (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ) (e_norm : ‖e‖ = 1)
    (lambdaMinus_pos : 0 < lambdaMinus) (lambda_order : lambdaMinus < lambdaPlus)
    (gammaMinus_pos : 0 < gammaMinus) (gammaPlus_pos : 0 < gammaPlus) :
    (ofSpectral e lambdaMinus lambdaPlus gammaMinus gammaPlus e_norm lambdaMinus_pos lambda_order
      gammaMinus_pos gammaPlus_pos).amplitude = gammaMinus := by
  -- The constructor stores the low oriented coordinate as its amplitude.
  rfl

/-- Scaling the canonical recovered coordinate vector by its low coordinate gives the prescribed
oriented coordinates. -/
private lemma smul_recoveryCoordinates
    (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ)
    (lambdaMinus_pos : 0 < lambdaMinus) (lambda_order : lambdaMinus < lambdaPlus)
    (gammaMinus_pos : 0 < gammaMinus) (gammaPlus_pos : 0 < gammaPlus) :
    gammaMinus •
        (!₂[(1 : ℝ), recoveryShape lambdaMinus lambdaPlus gammaMinus gammaPlus *
          recoveryRadius lambdaMinus lambdaPlus gammaMinus gammaPlus] :
          EuclideanSpace ℝ (Fin 2)) =
      !₂[gammaMinus, gammaPlus] := by
  -- Equality is checked on the low and high oriented coordinates separately.
  ext i
  fin_cases i
  · simp
  · -- The product recovery invariant identifies the high coordinate.
    simp [recoveryShape_mul_radius lambdaMinus lambdaPlus gammaMinus gammaPlus
      lambdaMinus_pos lambda_order gammaMinus_pos gammaPlus_pos]
    field_simp [gammaMinus_pos.ne']

/-- A spectrally recovered state has the prescribed ordered spectrum in its oriented frame. -/
theorem ofSpectral_metric (e : EuclideanSpace ℝ (Fin 2))
    (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ) (e_norm : ‖e‖ = 1)
    (lambdaMinus_pos : 0 < lambdaMinus) (lambda_order : lambdaMinus < lambdaPlus)
    (gammaMinus_pos : 0 < gammaMinus) (gammaPlus_pos : 0 < gammaPlus) :
    let s := ofSpectral e lambdaMinus lambdaPlus gammaMinus gammaPlus e_norm lambdaMinus_pos
      lambda_order gammaMinus_pos gammaPlus_pos
    s.metric =
      s.frame * Matrix.diagonal ![lambdaMinus, lambdaPlus] * s.frame.transpose := by
  -- Start from the exported metric interface, leaving the frame products opaque.
  dsimp only
  have metric_formula :=
    (CycleBoundaryState.spec
      (ofSpectral e lambdaMinus lambdaPlus gammaMinus gammaPlus e_norm lambdaMinus_pos
        lambda_order gammaMinus_pos gammaPlus_pos)).1
  rw [ofSpectral_h, ofSpectral_p, ofSpectral_r] at metric_formula
  -- The second recovery invariant replaces the low diagonal weight.
  rw [recoveryHigh_mul_shape_mul_radius_sq lambdaMinus lambdaPlus gammaMinus gammaPlus
    lambdaMinus_pos lambda_order gammaMinus_pos gammaPlus_pos] at metric_formula
  exact metric_formula

/-- A spectrally recovered state has the prescribed positive oriented gradient coordinates in
its frame. -/
theorem ofSpectral_gradient (e : EuclideanSpace ℝ (Fin 2))
    (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ) (e_norm : ‖e‖ = 1)
    (lambdaMinus_pos : 0 < lambdaMinus) (lambda_order : lambdaMinus < lambdaPlus)
    (gammaMinus_pos : 0 < gammaMinus) (gammaPlus_pos : 0 < gammaPlus) :
    let s := ofSpectral e lambdaMinus lambdaPlus gammaMinus gammaPlus e_norm lambdaMinus_pos
      lambda_order gammaMinus_pos gammaPlus_pos
    s.gradient =
      (Matrix.toEuclideanCLM : Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
        (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) s.frame
          !₂[gammaMinus, gammaPlus] := by
  -- Start from the exported gradient interface and normalize the stored scalar parameters.
  dsimp only
  have gradient_formula :=
    (CycleBoundaryState.spec
      (ofSpectral e lambdaMinus lambdaPlus gammaMinus gammaPlus e_norm lambdaMinus_pos
        lambda_order gammaMinus_pos gammaPlus_pos)).2
  rw [ofSpectral_amplitude, ofSpectral_p, ofSpectral_r] at gradient_formula
  -- Move the amplitude through the frame action, then use the coordinate bridge.
  rw [← map_smul,
    smul_recoveryCoordinates lambdaMinus lambdaPlus gammaMinus gammaPlus lambdaMinus_pos
      lambda_order gammaMinus_pos gammaPlus_pos] at gradient_formula
  exact gradient_formula

/-- Spectral recovery produces positive canonical parameters with the prescribed projections,
metric spectrum, and oriented gradient coordinates. -/
theorem ofSpectral_spec (e : EuclideanSpace ℝ (Fin 2))
    (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ) (e_norm : ‖e‖ = 1)
    (lambdaMinus_pos : 0 < lambdaMinus) (lambda_order : lambdaMinus < lambdaPlus)
    (gammaMinus_pos : 0 < gammaMinus) (gammaPlus_pos : 0 < gammaPlus) :
    let s := ofSpectral e lambdaMinus lambdaPlus gammaMinus gammaPlus e_norm lambdaMinus_pos
      lambda_order gammaMinus_pos gammaPlus_pos
    0 < s.amplitude ∧ 0 < s.h ∧ 0 < s.r ∧ 0 < s.p ∧
      s.amplitude = gammaMinus ∧ s.h = lambdaPlus ∧
      s.r = recoveryRadius lambdaMinus lambdaPlus gammaMinus gammaPlus ∧
      s.p = recoveryShape lambdaMinus lambdaPlus gammaMinus gammaPlus ∧
      s.metric = s.frame * Matrix.diagonal ![lambdaMinus, lambdaPlus] * s.frame.transpose ∧
      s.gradient =
        (Matrix.toEuclideanCLM : Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
          (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) s.frame
            !₂[gammaMinus, gammaPlus] := by
  -- Normalize the four stored projections throughout the specification.
  dsimp only
  rw [ofSpectral_amplitude, ofSpectral_h, ofSpectral_r, ofSpectral_p]
  have lambdaPlus_pos : 0 < lambdaPlus := lambdaMinus_pos.trans lambda_order
  -- Assemble positivity, projection identities, and the two representation theorems.
  exact ⟨gammaMinus_pos, lambdaPlus_pos,
    recoveryRadius_pos lambdaMinus lambdaPlus gammaMinus gammaPlus lambdaMinus_pos lambda_order
      gammaMinus_pos gammaPlus_pos,
    recoveryShape_pos lambdaMinus lambdaPlus gammaMinus gammaPlus lambdaMinus_pos lambda_order
      gammaMinus_pos gammaPlus_pos,
    rfl, rfl, rfl, rfl,
    ofSpectral_metric e lambdaMinus lambdaPlus gammaMinus gammaPlus e_norm lambdaMinus_pos
      lambda_order gammaMinus_pos gammaPlus_pos,
    ofSpectral_gradient e lambdaMinus lambdaPlus gammaMinus gammaPlus e_norm lambdaMinus_pos
      lambda_order gammaMinus_pos gammaPlus_pos⟩

end CycleBoundaryState
