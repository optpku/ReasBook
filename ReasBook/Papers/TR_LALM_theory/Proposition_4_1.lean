/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Proposition_4_1.Parameters
public import TR_LALM_theory.Proposition_4_1.SourceWitness

public section

open scoped NNReal

namespace LALM

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- The base sufficient-parameter region at fixed `β` and `ρ`.

Its varying coordinates are the positive step radius `Δ` and multiplier bound `Λ`,
and membership means that the four initialization-independent inequalities of
Assumption 2.3 hold. -/
def parameterRegion (h : EqualityConstrained.Regularity f c)
    (beta rho : NNRealˣ) : Set (NNRealˣ × NNRealˣ) :=
  {values | ∃ params : AdmissibleParameters h,
    params.beta = beta ∧ params.rho = rho ∧
      params.delta = values.1 ∧ params.multiplierBound = values.2}

/-- Membership in the base parameter region exposes its admissible parameter
certificate and fixed coordinates. -/
theorem mem_parameterRegion
    (h : EqualityConstrained.Regularity f c)
    (beta rho : NNRealˣ) (values : NNRealˣ × NNRealˣ) :
    values ∈ parameterRegion h beta rho ↔
      ∃ params : AdmissibleParameters h,
        params.beta = beta ∧ params.rho = rho ∧
          params.delta = values.1 ∧ params.multiplierBound = values.2 := Iff.rfl

/-- The NR-LALM sufficient-parameter region at fixed proximal and penalty
parameters and fixed initialization. -/
def initializedParameterRegion (h : EqualityConstrained.Regularity f c)
    (beta rho : NNRealˣ) (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m)) : Set (NNRealˣ × NNRealˣ) :=
  {values | ∃ params : Parameters h x₀ multiplier₀,
    params.beta = beta ∧ params.rho = rho ∧
      params.delta = values.1 ∧ params.multiplierBound = values.2}

/-- Membership in the initialized NR-LALM parameter region exposes one
certificate with the prescribed common data. -/
theorem mem_initializedParameterRegion
    (h : EqualityConstrained.Regularity f c)
    (beta rho : NNRealˣ) (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m))
    (values : NNRealˣ × NNRealˣ) :
    values ∈ initializedParameterRegion h beta rho x₀ multiplier₀ ↔
      ∃ params : Parameters h x₀ multiplier₀,
        params.beta = beta ∧ params.rho = rho ∧
          params.delta = values.1 ∧ params.multiplierBound = values.2 := Iff.rfl

/-- Forgetting the initialization bounds maps the initialized NR-LALM region
into its auxiliary parameter region. -/
theorem initializedParameterRegion_subset_parameterRegion
    (h : EqualityConstrained.Regularity f c)
    (beta rho : NNRealˣ) (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m)) :
    initializedParameterRegion h beta rho x₀ multiplier₀ ⊆
      parameterRegion h beta rho := by
  intro values hvalues
  rw [mem_initializedParameterRegion] at hvalues
  obtain ⟨params, hbeta, hrho, hdelta, hmultiplierBound⟩ := hvalues
  rw [mem_parameterRegion]
  exact ⟨params.toAdmissibleParameters, hbeta, hrho, hdelta,
    hmultiplierBound⟩

namespace Correction

/-- Helper for Proposition 4.1: the constraint gradient of the identity map is the
identity continuous linear map. -/
private lemma constraintGradient_id
    (x : EuclideanSpace ℝ (Fin 1)) :
    EqualityConstrained.constraintGradient
        (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) x =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) := by
  -- Reduce the constraint gradient to the adjoint of the derivative of `id`.
  rw [EqualityConstrained.constraintGradient_def, fderiv_id,
    ContinuousLinearMap.adjoint_id]

/-- Helper for Proposition 4.1: the identity constraint gradient has operator norm
at most one at every point. -/
private lemma norm_constraintGradient_id_le_one
    (x : EuclideanSpace ℝ (Fin 1)) :
    ‖EqualityConstrained.constraintGradient
      (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) x‖ ≤
        (1 : ℝ≥0) := by
  -- Rewrite to the identity continuous linear map and use its canonical norm bound.
  rw [constraintGradient_id]
  exact ContinuousLinearMap.norm_id_le

/-- Helper for Proposition 4.1: the identity constraint gradient is one-Lipschitz
on every subset of the scalar Euclidean space. -/
private lemma constraintGradient_id_lipschitzOn
    (s : Set (EuclideanSpace ℝ (Fin 1))) :
    LipschitzOnWith (1 : ℝ≥0)
      (EqualityConstrained.constraintGradient
        (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))) s := by
  -- Both endpoint gradients are the same identity map, so their distance vanishes.
  intro x hx y hy
  rw [constraintGradient_id, constraintGradient_id]
  simp

/-- Helper for Proposition 4.1: the zero objective and identity constraint admit
the fixed global regularity constants used in the strictness witness. -/
private lemma existsRegularityForZeroObjectiveIdentityConstraint :
    ∃ h : EqualityConstrained.Regularity
        (fun _ : EuclideanSpace ℝ (Fin 1) => 0)
        (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)),
      h.region = Set.univ ∧
        h.gradientBound = 4 / 25 ∧
        h.gradientLipschitz = 1 / 100 ∧
        h.constraintGradientBound = 1 ∧
        h.constraintGradientLipschitz = 1 ∧
        h.licqModulus = 1 := by
  -- Establish each analytic field before assembling the regularity record.
  have objectiveLower_le :
      ∀ x : EuclideanSpace ℝ (Fin 1), x ∈ Set.univ → (0 : ℝ) ≤ 0 := by
    intro x hx
    norm_num
  have norm_gradient_le :
      ∀ x : EuclideanSpace ℝ (Fin 1), x ∈ Set.univ →
        ‖gradient (fun _ : EuclideanSpace ℝ (Fin 1) => (0 : ℝ)) x‖ ≤
          (4 / 25 : ℝ≥0) := by
    intro x hx
    norm_num
  have lipschitzOn_gradient :
      LipschitzOnWith (1 / 100 : ℝ≥0)
        (gradient (fun _ : EuclideanSpace ℝ (Fin 1) => (0 : ℝ))) Set.univ := by
    intro x hx y hy
    simp
  have differentiableOn_objective :
      DifferentiableOn ℝ (fun _ : EuclideanSpace ℝ (Fin 1) => (0 : ℝ)) Set.univ := by
    apply Differentiable.differentiableOn
    exact differentiable_const 0
  have differentiableOn_constraint :
      DifferentiableOn ℝ
        (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) Set.univ := by
    apply Differentiable.differentiableOn
    exact differentiable_id
  have gradientBound_pos : (0 : ℝ≥0) < 4 / 25 := by
    norm_num
  have gradientLipschitz_pos : (0 : ℝ≥0) < 1 / 100 := by
    norm_num
  have constraintGradientBound_pos : (0 : ℝ≥0) < 1 := by
    norm_num
  have constraintGradientLipschitz_pos : (0 : ℝ≥0) < 1 := by
    norm_num
  have norm_constraintGradient_le :
      ∀ x : EuclideanSpace ℝ (Fin 1), x ∈ Set.univ →
        ‖EqualityConstrained.constraintGradient
          (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) x‖ ≤
            (1 : ℝ≥0) := by
    intro x hx
    exact norm_constraintGradient_id_le_one x
  have licqLowerBound :
      ∀ x : EuclideanSpace ℝ (Fin 1), x ∈ Set.univ →
        ∀ u : EuclideanSpace ℝ (Fin 1),
          (1 : NNRealˣ) * ‖u‖ ≤
            ‖EqualityConstrained.constraintGradient
              (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) x u‖ := by
    intro x hx u
    rw [constraintGradient_id]
    norm_num
  let h : EqualityConstrained.Regularity
      (fun _ : EuclideanSpace ℝ (Fin 1) => 0)
      (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) :=
    { region := Set.univ
      objectiveLower := 0
      gradientBound := 4 / 25
      gradientLipschitz := 1 / 100
      constraintGradientBound := 1
      constraintGradientLipschitz := 1
      licqModulus := 1
      nonempty_region := Set.univ_nonempty
      isOpen_region := isOpen_univ
      gradientBound_pos
      gradientLipschitz_pos
      constraintGradientBound_pos
      constraintGradientLipschitz_pos
      differentiableOn_objective
      differentiableOn_constraint
      objectiveLower_le
      norm_gradient_le
      lipschitzOn_gradient
      norm_constraintGradient_le
      lipschitzOn_constraintGradient := constraintGradient_id_lipschitzOn Set.univ
      licqLowerBound }
  -- The constructor stores the six chosen constants without further transport.
  refine ⟨h, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Helper for Proposition 4.1: the first two scalar base-parameter inequalities
with `β = 1` and `ρ = 128` are inconsistent. -/
private lemma baseFirstTwoParameterBoundsInconsistent
    (delta multiplierBound : ℝ)
    (parameterBound : 4 / 25 + delta + 64 * delta ^ 2 ≤ multiplierBound)
    (comparisonBound : 4 / 25 + 3 * multiplierBound / 129 ≤ delta) : False := by
  -- The discriminant obstruction is exposed by the square centered at `21 / 64`.
  nlinarith [sq_nonneg (64 * delta - 21)]

/-- Helper for Proposition 4.1: the fixed scalar regularity constants make the base
parameter region empty at `β = 1` and `ρ = 128`. -/
private lemma baseParameterRegion_eq_empty_of_scalarIdentityBounds
    {f : EuclideanSpace ℝ (Fin 1) → ℝ}
    {c : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)}
    (h : EqualityConstrained.Regularity f c) (beta rho : NNRealˣ)
    (gradientBound_eq : h.gradientBound = 4 / 25)
    (constraintGradientBound_eq : h.constraintGradientBound = 1)
    (constraintGradientLipschitz_eq : h.constraintGradientLipschitz = 1)
    (licqModulus_eq : h.licqModulus = 1)
    (beta_eq : (beta : ℝ) = 1) (rho_eq : (rho : ℝ) = 128) :
    LALM.parameterRegion h beta rho = ∅ := by
  -- Expose a hypothetical base certificate and normalize only its first two bounds.
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro values values_mem
  rw [LALM.mem_parameterRegion] at values_mem
  obtain ⟨params, params_beta, params_rho, params_delta, params_multiplierBound⟩ :=
    values_mem
  have params_beta_eq : (params.beta : ℝ) = 1 := by
    rw [params_beta, beta_eq]
  have params_rho_eq : (params.rho : ℝ) = 128 := by
    rw [params_rho, rho_eq]
  have parameterBound :
      4 / 25 + (params.delta : ℝ) + 64 * (params.delta : ℝ) ^ 2 ≤
        (params.multiplierBound : ℝ) := by
    have parameterBound_le := params.parameterBound_le
    norm_num [LALM.linearizationConstant_def, gradientBound_eq,
      constraintGradientBound_eq, constraintGradientLipschitz_eq, licqModulus_eq,
      params_beta_eq, params_rho_eq] at parameterBound_le ⊢
    exact parameterBound_le
  have comparisonBound :
      4 / 25 + 3 * (params.multiplierBound : ℝ) / 129 ≤
        (params.delta : ℝ) := by
    have comparisonBound_le := params.comparisonBound_le
    norm_num [gradientBound_eq, constraintGradientBound_eq, licqModulus_eq,
      params_beta_eq, params_rho_eq] at comparisonBound_le ⊢
    exact comparisonBound_le
  -- The normalized pair is ruled out by the scalar polynomial obstruction.
  exact baseFirstTwoParameterBoundsInconsistent _ _ parameterBound comparisonBound

/- Proposition 4.1 (1): the NR-LALM+SOC trial point, residual, correction, primal update,
and multiplier update are the concrete one-step data. -/

/- Proposition 4.1 (2): the correction is the minimum-norm solution of the adjoint
constraint-gradient equation. -/

/- Proposition 4.1 (3): corrected-step admissibility is containment of both successive
segments in the regularity region. -/

/- Proposition 4.1 (4): the base linearization residual obeys its quadratic bound. -/

/- Proposition 4.1 (5): the correction obeys its quadratic norm bound. -/

/- Proposition 4.1 (6): the corrected constraint error obeys its fourth-order and
step-radius-dependent quadratic bounds. -/

/- Proposition 4.1 (7): the full corrected displacement obeys its linear bound. -/

/- Proposition 4.1 (8): base-model minimization yields the perturbed multiplier
identity for the corrected point. -/

/- Proposition 4.1 (9): the corrected analysis uses the stated correction, error,
displacement, model, primal, multiplier-primal, and stationarity constants. -/

/- Proposition 4.1 (10): corrected admissible parameters bundle the positive tuple
and four corrected inequalities; initialized parameters add the two initial bounds. -/

/- Proposition 4.1 (11): on a nonempty regularity region, when `0 < m`, the four base
admissibility inequalities imply the four corrected inequalities for the same numerical
tuple, independently of any initialization data. -/

/-- The corrected sufficient-parameter region at fixed `β` and `ρ`.

Its varying coordinates are the positive step radius `Δ` and multiplier bound `Λ`,
and membership means that the four corrected initialization-independent inequalities
hold. -/
def parameterRegion (h : EqualityConstrained.Regularity f c)
    (beta rho : NNRealˣ) : Set (NNRealˣ × NNRealˣ) :=
  {values | ∃ params : AdmissibleParameters h,
    params.beta = beta ∧ params.rho = rho ∧
      params.delta = values.1 ∧ params.multiplierBound = values.2}

/-- Membership in the corrected parameter region exposes its admissible parameter
certificate and fixed coordinates. -/
theorem mem_parameterRegion
    (h : EqualityConstrained.Regularity f c)
    (beta rho : NNRealˣ) (values : NNRealˣ × NNRealˣ) :
    values ∈ parameterRegion h beta rho ↔
      ∃ params : AdmissibleParameters h,
        params.beta = beta ∧ params.rho = rho ∧
          params.delta = values.1 ∧ params.multiplierBound = values.2 := Iff.rfl

/-- The NR-LALM+SOC sufficient-parameter region at fixed proximal and penalty
parameters and fixed initialization. -/
def initializedParameterRegion (h : EqualityConstrained.Regularity f c)
    (beta rho : NNRealˣ) (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m)) : Set (NNRealˣ × NNRealˣ) :=
  {values | ∃ params : Parameters h x₀ multiplier₀,
    params.beta = beta ∧ params.rho = rho ∧
      params.delta = values.1 ∧ params.multiplierBound = values.2}

/-- Membership in the initialized NR-LALM+SOC parameter region exposes one
certificate with the prescribed common data. -/
theorem mem_initializedParameterRegion
    (h : EqualityConstrained.Regularity f c)
    (beta rho : NNRealˣ) (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m))
    (values : NNRealˣ × NNRealˣ) :
    values ∈ initializedParameterRegion h beta rho x₀ multiplier₀ ↔
      ∃ params : Parameters h x₀ multiplier₀,
        params.beta = beta ∧ params.rho = rho ∧
          params.delta = values.1 ∧ params.multiplierBound = values.2 := Iff.rfl

/-- For at least one constraint, the four NR-LALM inequalities imply the
NR-LALM+SOC inequalities for the same tuple. -/
theorem parameterRegion_mono (h : EqualityConstrained.Regularity f c)
    (hm : 0 < m) (beta rho : NNRealˣ) :
    LALM.parameterRegion h beta rho ⊆ parameterRegion h beta rho := by
  intro values hvalues
  rw [LALM.mem_parameterRegion] at hvalues
  obtain ⟨base, hbeta, hrho, hdelta, hmultiplierBound⟩ := hvalues
  rw [mem_parameterRegion]
  exact ⟨AdmissibleParameters.ofBase hm base, hbeta, hrho, hdelta,
    hmultiplierBound⟩

/-- Under common initialization, the derived deterministic NR-LALM region is
contained in the NR-LALM+SOC region. -/
theorem initializedParameterRegion_mono
    (h : EqualityConstrained.Regularity f c)
    (hm : 0 < m) (beta rho : NNRealˣ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m)) :
    LALM.initializedParameterRegion h beta rho x₀ multiplier₀ ⊆
      initializedParameterRegion h beta rho x₀ multiplier₀ := by
  intro values hvalues
  rw [LALM.mem_initializedParameterRegion] at hvalues
  obtain ⟨base, hbeta, hrho, hdelta, hmultiplierBound⟩ := hvalues
  rw [mem_initializedParameterRegion]
  exact ⟨Parameters.ofBase hm base, hbeta, hrho, hdelta,
    hmultiplierBound⟩

/-- Helper for Proposition 4.1: the corrected parameter region is nonempty exactly
when an admissible certificate has the prescribed proximal and penalty parameters. -/
theorem parameterRegion_nonempty_iff
    (h : EqualityConstrained.Regularity f c) (beta rho : NNRealˣ) :
    (parameterRegion h beta rho).Nonempty ↔
      ∃ params : AdmissibleParameters h,
        params.beta = beta ∧ params.rho = rho := by
  constructor
  · -- Forget the varying coordinates of a point already in the region.
    rintro ⟨values, values_mem⟩
    rw [mem_parameterRegion] at values_mem
    obtain ⟨params, params_beta, params_rho, params_delta, params_multiplierBound⟩ :=
      values_mem
    exact ⟨params, params_beta, params_rho⟩
  · -- Use the certificate's own radius and multiplier bound as a region point.
    rintro ⟨params, params_beta, params_rho⟩
    refine ⟨(params.delta, params.multiplierBound), ?_⟩
    rw [mem_parameterRegion]
    exact ⟨params, params_beta, params_rho, rfl, rfl⟩

/-- Helper for Proposition 4.1: the fixed scalar regularity constants admit the
corrected parameter pair `Δ = 1 / 4`, `Λ = 1 / 2` at `β = 1`, `ρ = 128`. -/
private lemma correctedParameterRegion_nonempty_of_scalarIdentityBounds
    {f : EuclideanSpace ℝ (Fin 1) → ℝ}
    {c : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)}
    (h : EqualityConstrained.Regularity f c)
    (gradientBound_eq : h.gradientBound = 4 / 25)
    (gradientLipschitz_eq : h.gradientLipschitz = 1 / 100)
    (constraintGradientBound_eq : h.constraintGradientBound = 1)
    (constraintGradientLipschitz_eq : h.constraintGradientLipschitz = 1)
    (licqModulus_eq : h.licqModulus = 1) :
    ∃ beta rho : NNRealˣ,
      (beta : ℝ) = 1 ∧ (rho : ℝ) = 128 ∧
        (parameterRegion h beta rho).Nonempty := by
  -- Build the three nontrivial positive unit values from named nonzero facts.
  have delta_ne : (1 / 4 : ℝ≥0) ≠ 0 := by
    norm_num
  have rho_ne : (128 : ℝ≥0) ≠ 0 := by
    norm_num
  have multiplierBound_ne : (1 / 2 : ℝ≥0) ≠ 0 := by
    norm_num
  let delta : NNRealˣ := Units.mk0 (1 / 4 : ℝ≥0) delta_ne
  let beta : NNRealˣ := 1
  let rho : NNRealˣ := Units.mk0 (128 : ℝ≥0) rho_ne
  let multiplierBound : NNRealˣ := Units.mk0 (1 / 2 : ℝ≥0) multiplierBound_ne
  have delta_eq : (delta : ℝ) = 1 / 4 := by
    simp [delta]
  have beta_eq : (beta : ℝ) = 1 := by
    norm_num [beta]
  have rho_eq : (rho : ℝ) = 128 := by
    simp [rho]
  have multiplierBound_eq : (multiplierBound : ℝ) = 1 / 2 := by
    simp [multiplierBound]
  -- Normalize each corrected constant once before using it in the four rational bounds.
  have stepConstant_eq : stepConstant h = 1 / 2 := by
    rw [stepConstant_def, constraintGradientLipschitz_eq, licqModulus_eq]
    norm_num
  have errorConstant_eq : errorConstant h = 1 / 8 := by
    rw [errorConstant_def, constraintGradientLipschitz_eq, licqModulus_eq]
    norm_num
  have errorFactor_eq : errorFactor h delta = 1 / 128 := by
    rw [errorFactor_def, errorConstant_eq, delta_eq]
    norm_num
  have displacementFactor_eq : displacementFactor h delta = 9 / 8 := by
    rw [displacementFactor_def, stepConstant_eq, delta_eq]
    norm_num
  have primalConstant_eq : primalConstant h delta beta rho = 5 / 4 := by
    rw [primalConstant_def, constraintGradientBound_eq, errorFactor_eq,
      delta_eq, beta_eq, rho_eq]
    norm_num
  have primalComparisonConstant_eq :
      primalComparisonConstant h delta beta rho multiplierBound = 1459 / 800 := by
    rw [primalComparisonConstant_def, primalConstant_eq, gradientLipschitz_eq,
      constraintGradientLipschitz_eq, multiplierBound_eq, displacementFactor_eq]
    norm_num
  have parameterBound_le :
      ((h.gradientBound + beta * delta +
        rho * h.constraintGradientBound * errorFactor h delta * delta ^ 2) /
          h.licqModulus : ℝ) ≤ multiplierBound := by
    rw [gradientBound_eq, constraintGradientBound_eq, licqModulus_eq, errorFactor_eq,
      delta_eq, beta_eq, rho_eq, multiplierBound_eq]
    norm_num
  have comparisonBound_le :
      (h.gradientBound / beta +
        3 * h.constraintGradientBound * multiplierBound /
          (beta + rho * h.licqModulus ^ 2) : ℝ) ≤ delta := by
    rw [gradientBound_eq, constraintGradientBound_eq, licqModulus_eq,
      delta_eq, beta_eq, rho_eq, multiplierBound_eq]
    norm_num
  have modelConstant_le :
      modelConstant h delta rho multiplierBound ≤ 3 * beta / 8 := by
    rw [modelConstant_def, gradientBound_eq, gradientLipschitz_eq,
      constraintGradientBound_eq, stepConstant_eq, errorFactor_eq, displacementFactor_eq,
      delta_eq, beta_eq, rho_eq, multiplierBound_eq]
    norm_num
  have max_branch : ((5 : ℝ) / 4) ^ 2 ≤ ((1459 : ℝ) / 800) ^ 2 := by
    norm_num
  have multiplierPrimalConstant_le :
      8 * multiplierPrimalConstant h delta beta rho multiplierBound / beta ≤ rho := by
    rw [multiplierPrimalConstant_def, licqModulus_eq, primalConstant_eq,
      primalComparisonConstant_eq, max_eq_right max_branch, beta_eq, rho_eq]
    norm_num
  let params : AdmissibleParameters h :=
    { delta
      beta
      rho
      multiplierBound
      parameterBound_le
      comparisonBound_le
      modelConstant_le
      multiplierPrimalConstant_le }
  -- The nonemptiness companion packages the certificate at its own varying coordinates.
  refine ⟨beta, rho, beta_eq, rho_eq, ?_⟩
  rw [parameterRegion_nonempty_iff]
  exact ⟨params, rfl, rfl⟩

/-- The auxiliary, initialization-independent sufficient regions can already be
strictly separated for a globally regular scalar problem. -/
theorem strictAuxiliaryParameterRegion :
    ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ)
      (c : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
      (h : EqualityConstrained.Regularity f c)
      (beta rho : NNRealˣ),
      h.region = Set.univ ∧
        LALM.parameterRegion h beta rho = ∅ ∧
          (parameterRegion h beta rho).Nonempty := by
  -- Obtain the global scalar regularity witness and expose its fixed constants.
  obtain ⟨h, hregion, hgradientBound, hgradientLipschitz,
    hconstraintGradientBound, hconstraintGradientLipschitz, hlicqModulus⟩ :=
      existsRegularityForZeroObjectiveIdentityConstraint
  -- Use the explicit corrected certificate, then rule out every base pair at the same `β, ρ`.
  obtain ⟨beta, rho, beta_eq, rho_eq, corrected_nonempty⟩ :=
    correctedParameterRegion_nonempty_of_scalarIdentityBounds h hgradientBound
      hgradientLipschitz hconstraintGradientBound hconstraintGradientLipschitz
      hlicqModulus
  have base_empty :=
    baseParameterRegion_eq_empty_of_scalarIdentityBounds h beta rho hgradientBound
      hconstraintGradientBound hconstraintGradientLipschitz hlicqModulus beta_eq rho_eq
  -- Assemble the scalar problem and its strict region comparison.
  exact ⟨fun _ : EuclideanSpace ℝ (Fin 1) => 0, id, h, beta, rho,
    hregion, base_empty, corrected_nonempty⟩

/-- Proposition 4.1: the source problem `f(x) = sin x`, `c(x) = 2x - cos x`
with its unique feasible initialization realizes strict containment at
`Δ = 1 / 20`, `Λ = 4`, `β = 50`, and `ρ = 2200`. -/
theorem sourceStrictParameterRegion :
    SourceWitness.regularity.region = Set.univ ∧
      (∃! x : EuclideanSpace ℝ (Fin 1), SourceWitness.constraint x = 0) ∧
      SourceWitness.constraint SourceWitness.initialPoint = 0 ∧
      ‖SourceWitness.initialMultiplier‖ = 4 ∧
      (SourceWitness.sourceDelta : ℝ) = 1 / 20 ∧
      (SourceWitness.sourceBeta : ℝ) = 50 ∧
      (SourceWitness.sourceRho : ℝ) = 2200 ∧
      (SourceWitness.sourceMultiplierBound : ℝ) = 4 ∧
      LALM.initializedParameterRegion SourceWitness.regularity
        SourceWitness.sourceBeta SourceWitness.sourceRho SourceWitness.initialPoint
        SourceWitness.initialMultiplier = ∅ ∧
      (SourceWitness.sourceDelta, SourceWitness.sourceMultiplierBound) ∈
        initializedParameterRegion SourceWitness.regularity SourceWitness.sourceBeta
          SourceWitness.sourceRho SourceWitness.initialPoint
          SourceWitness.initialMultiplier := by
  obtain ⟨hregion, hunique, hfeasible, hnorm, _, _, _, _⟩ :=
    SourceWitness.sourceWitness_spec
  have hbaseEmpty :
      LALM.initializedParameterRegion SourceWitness.regularity
        SourceWitness.sourceBeta SourceWitness.sourceRho SourceWitness.initialPoint
        SourceWitness.initialMultiplier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro values hvalues
    rw [LALM.mem_initializedParameterRegion] at hvalues
    obtain ⟨base, hbeta, hrho, _, _⟩ := hvalues
    exact SourceWitness.noBaseParametersAtSource base hbeta hrho
  obtain ⟨hdelta, hbeta, hrho, hmultiplierBound⟩ :=
    SourceWitness.correctedParameters_coordinates
  have hcorrectedMem :
      (SourceWitness.sourceDelta, SourceWitness.sourceMultiplierBound) ∈
        initializedParameterRegion SourceWitness.regularity SourceWitness.sourceBeta
          SourceWitness.sourceRho SourceWitness.initialPoint
          SourceWitness.initialMultiplier := by
    rw [mem_initializedParameterRegion]
    exact ⟨SourceWitness.correctedParameters, hbeta, hrho, hdelta,
      hmultiplierBound⟩
  exact ⟨hregion, hunique, hfeasible, hnorm, SourceWitness.sourceDelta_eq,
    SourceWitness.sourceBeta_eq, SourceWitness.sourceRho_eq,
    SourceWitness.sourceMultiplierBound_eq, hbaseEmpty, hcorrectedMem⟩

/-- Proposition 4.1: under regularity on the chosen region and common initialization, the
derived deterministic NR-LALM parameter region is strictly contained in the
corresponding NR-LALM+SOC region, witnessed by the source scalar problem. -/
theorem strictParameterRegion :
    ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ)
      (c : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
      (h : EqualityConstrained.Regularity f c)
      (beta rho : NNRealˣ)
      (x₀ : EuclideanSpace ℝ (Fin 1))
      (multiplier₀ : EuclideanSpace ℝ (Fin 1)),
      h.region = Set.univ ∧
        LALM.initializedParameterRegion h beta rho x₀ multiplier₀ = ∅ ∧
          (initializedParameterRegion h beta rho x₀ multiplier₀).Nonempty := by
  obtain ⟨hregion, _, _, _, _, _, _, _, hbaseEmpty, hcorrectedMem⟩ :=
    sourceStrictParameterRegion
  exact ⟨SourceWitness.objective, SourceWitness.constraint, SourceWitness.regularity,
    SourceWitness.sourceBeta, SourceWitness.sourceRho, SourceWitness.initialPoint,
    SourceWitness.initialMultiplier, hregion, hbaseEmpty,
    ⟨(SourceWitness.sourceDelta, SourceWitness.sourceMultiplierBound), hcorrectedMem⟩⟩

end Correction

end LALM

end
