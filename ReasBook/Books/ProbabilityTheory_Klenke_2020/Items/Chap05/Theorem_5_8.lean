/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X Y : Ω → ℝ}

noncomputable section

private lemma centered_linear_combo_memLp (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (a b : ℝ) :
    MemLp (fun ω ↦ a * (X ω - μ[X]) + b * (Y ω - μ[Y])) 2 μ := by
  -- Centering preserves `L²`, and scalar multiples and sums stay in `L²`.
  simpa [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] using
    (hX.sub (memLp_const (μ[X]))).const_mul a |>.add
      ((hY.sub (memLp_const (μ[Y]))).const_mul b)

omit [IsProbabilityMeasure μ] in
private lemma covariance_congr_ae {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  -- Rewrite both expectations by almost-sure equality, then rewrite the integrand pointwise.
  have hIntX : μ[X] = μ[X'] := MeasureTheory.integral_congr_ae hX
  have hIntY : μ[Y] = μ[Y'] := MeasureTheory.integral_congr_ae hY
  rw [ProbabilityTheory.covariance, ProbabilityTheory.covariance]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY, hIntX, hIntY]

private lemma integral_centered_linear_combo_eq_zero (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (a b : ℝ) :
    μ[fun ω ↦ a * (X ω - μ[X]) + b * (Y ω - μ[Y])] = 0 := by
  -- Expand the integral and use that each centered variable has expectation `0`.
  have hXint : Integrable X μ := hX.integrable (by simp)
  have hYint : Integrable Y μ := hY.integrable (by simp)
  rw [integral_add]
  · rw [integral_const_mul, integral_const_mul]
    rw [integral_sub hXint (integrable_const _), integral_sub hYint (integrable_const _)]
    simp
  · exact ((hX.sub (memLp_const (μ[X]))).const_mul a).integrable (by simp)
  · exact ((hY.sub (memLp_const (μ[Y]))).const_mul b).integrable (by simp)

/-- Helper for Theorem 5.8: the variance of a centered linear combination is the associated
quadratic form in the covariance matrix. -/
private lemma variance_centered_linear_combo (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (a b : ℝ) :
    Var[fun ω ↦ a * (X ω - μ[X]) + b * (Y ω - μ[Y]); μ]
      = a ^ 2 * Var[X; μ] + 2 * a * b * cov[X, Y; μ] + b ^ 2 * Var[Y; μ] := by
  -- Apply the variance-of-a-sum identity to the centered summands and then remove the centering.
  have hXc : MemLp (fun ω ↦ X ω - μ[X]) 2 μ := hX.sub (memLp_const _)
  have hYc : MemLp (fun ω ↦ Y ω - μ[Y]) 2 μ := hY.sub (memLp_const _)
  calc
    Var[fun ω ↦ a * (X ω - μ[X]) + b * (Y ω - μ[Y]); μ]
        = Var[fun ω ↦ a * (X ω - μ[X]); μ]
          + 2 * cov[fun ω ↦ a * (X ω - μ[X]), fun ω ↦ b * (Y ω - μ[Y]); μ]
          + Var[fun ω ↦ b * (Y ω - μ[Y]); μ] := by
            simpa [Pi.add_apply] using variance_add (hXc.const_mul a) (hYc.const_mul b)
    _ = a ^ 2 * Var[fun ω ↦ X ω - μ[X]; μ]
          + 2 * (a * (b * cov[fun ω ↦ X ω - μ[X], fun ω ↦ Y ω - μ[Y]; μ]))
          + b ^ 2 * Var[fun ω ↦ Y ω - μ[Y]; μ] := by
            rw [variance_const_mul, covariance_const_mul_left, covariance_const_mul_right,
              variance_const_mul]
    _ = a ^ 2 * Var[X; μ] + 2 * (a * (b * cov[X, Y; μ])) + b ^ 2 * Var[Y; μ] := by
            simp [variance_sub_const, covariance_sub_const_left, covariance_sub_const_right,
              hX.aestronglyMeasurable, hY.aestronglyMeasurable,
              hX.integrable (by simp), hY.integrable (by simp)]
    _ = a ^ 2 * Var[X; μ] + 2 * a * b * cov[X, Y; μ] + b ^ 2 * Var[Y; μ] := by ring

/-- Helper for Theorem 5.8: a centered linear combination has variance `0` exactly when it
vanishes almost surely. -/
private lemma variance_eq_zero_iff_ae_zero_centered_linear_combo
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (a b : ℝ) :
    Var[fun ω ↦ a * (X ω - μ[X]) + b * (Y ω - μ[Y]); μ] = 0 ↔
      (fun ω ↦ a * (X ω - μ[X]) + b * (Y ω - μ[Y])) =ᵐ[μ] fun _ ↦ (0 : ℝ) := by
  let Z : Ω → ℝ := fun ω ↦ a * (X ω - μ[X]) + b * (Y ω - μ[Y])
  have hZ : MemLp Z 2 μ := centered_linear_combo_memLp hX hY a b
  constructor
  · intro hVar
    have hAeConst : Z =ᵐ[μ] fun _ ↦ μ[Z] := ae_eq_integral_of_variance_eq_zero hZ hVar
    have hIntZero : μ[Z] = 0 := integral_centered_linear_combo_eq_zero hX hY a b
    filter_upwards [hAeConst] with ω hω
    simpa [Z, hIntZero] using hω
  · intro hAeZero
    rw [variance_congr hAeZero]
    exact variance_zero μ

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 5.8: the centered linear relation and the affine relation are equivalent
pointwise after expanding the centered variables. -/
private lemma ae_centered_relation_iff_ae_affine_relation (a b : ℝ) :
    ((fun ω ↦ a * (X ω - μ[X]) + b * (Y ω - μ[Y])) =ᵐ[μ] fun _ ↦ (0 : ℝ)) ↔
      ((fun ω ↦ a * X ω + b * Y ω) =ᵐ[μ] fun _ ↦ a * μ[X] + b * μ[Y]) := by
  constructor
  · intro h
    -- Move the expectation terms to the right-hand side.
    filter_upwards [h] with ω hω
    linarith
  · intro h
    -- Move the constant term back to recover the centered relation.
    filter_upwards [h] with ω hω
    linarith

-- Proof sketch: apply the nonnegativity of `Var[fun ω ↦ X ω + θ * Y ω; μ]` with the optimizing
-- choice `θ = -cov[X, Y; μ] / Var[Y; μ]` when `Var[Y; μ] ≠ 0`; if `Var[Y; μ] = 0`, the claim is
-- immediate from the variance-zero case.
/-- Theorem 5.8 (1): Cauchy--Schwarz inequality for the covariance of square-integrable real random
variables. -/
theorem covariance_sq_le_variance_mul_variance (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] ^ 2 ≤ Var[X; μ] * Var[Y; μ] := by
  by_cases hVarY : Var[Y; μ] = 0
  · -- If `Y` is almost surely constant, then the covariance vanishes.
    have hAeY : ∀ᵐ ω ∂μ, Y ω = μ[Y] := ae_eq_integral_of_variance_eq_zero hY hVarY
    have hCovZero : cov[X, Y; μ] = 0 := by
      rw [ProbabilityTheory.covariance]
      calc
        ∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ = ∫ ω, (0 : ℝ) ∂μ := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hAeY] with ω hω
          simp [hω]
        _ = 0 := by simp
    simp [hVarY, hCovZero]
  · -- Otherwise, use the textbook optimizing coefficient `θ = -cov[X,Y] / Var[Y]`.
    let θ : ℝ := -cov[X, Y; μ] / Var[Y; μ]
    have hNonneg : 0 ≤ Var[fun ω ↦ X ω + θ * Y ω; μ] := variance_nonneg _ _
    have hExpand :
        Var[fun ω ↦ X ω + θ * Y ω; μ]
          = Var[X; μ] + 2 * θ * cov[X, Y; μ] + θ ^ 2 * Var[Y; μ] := by
      calc
        Var[fun ω ↦ X ω + θ * Y ω; μ]
            = Var[X; μ] + 2 * cov[X, fun ω ↦ θ * Y ω; μ] + Var[fun ω ↦ θ * Y ω; μ] := by
              simpa [Pi.smul_apply] using variance_add hX (hY.const_mul θ)
        _ = Var[X; μ] + 2 * (θ * cov[X, Y; μ]) + Var[fun ω ↦ θ * Y ω; μ] := by
              rw [covariance_const_mul_right]
        _ = Var[X; μ] + 2 * (θ * cov[X, Y; μ]) + θ ^ 2 * Var[Y; μ] := by
              rw [variance_const_mul]
        _ = Var[X; μ] + 2 * θ * cov[X, Y; μ] + θ ^ 2 * Var[Y; μ] := by ring
    have hMulNonneg : 0 ≤ Var[fun ω ↦ X ω + θ * Y ω; μ] * Var[Y; μ] := by
      exact mul_nonneg hNonneg (variance_nonneg _ _)
    rw [hExpand] at hMulNonneg
    have hEval :
        (Var[X; μ] + 2 * θ * cov[X, Y; μ] + θ ^ 2 * Var[Y; μ]) * Var[Y; μ]
          = Var[X; μ] * Var[Y; μ] - cov[X, Y; μ] ^ 2 := by
      -- Clearing the denominator turns the quadratic expression into the desired difference.
      dsimp [θ]
      field_simp [hVarY]
      ring_nf
    rw [hEval] at hMulNonneg
    linarith

-- Proof sketch: analyze the equality case in the quadratic-variance argument from part (1); this
-- reduces equality to the vanishing of the variance of a suitable linear combination of the
-- centered variables, and then Theorem 5.6 identifies variance zero with almost-sure constancy.
/-- Theorem 5.8 (2): Equality in the covariance Cauchy--Schwarz inequality holds exactly when the
centered random variables `X - μ[X]` and `Y - μ[Y]` are almost surely linearly dependent. -/
theorem covariance_sq_eq_variance_mul_variance_iff_ae_linear_relation_centered
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] ^ 2 = Var[X; μ] * Var[Y; μ] ↔
      ∃ a b : ℝ,
        0 < |a| + |b| ∧
          (fun ω ↦ a * (X ω - μ[X]) + b * (Y ω - μ[Y])) =ᵐ[μ] fun _ ↦ (0 : ℝ) := by
  constructor
  · intro hEq
    by_cases hVarY : Var[Y; μ] = 0
    · -- If `Y` has variance `0`, the centered relation is witnessed by `(a,b) = (0,1)`.
      have hAeY : ∀ᵐ ω ∂μ, Y ω = μ[Y] := ae_eq_integral_of_variance_eq_zero hY hVarY
      refine ⟨0, 1, by norm_num, ?_⟩
      filter_upwards [hAeY] with ω hω
      simp [hω]
    · -- In the nondegenerate branch, equality forces the minimizing centered combination to have
      -- variance `0`.
      let θ : ℝ := -cov[X, Y; μ] / Var[Y; μ]
      have hVarZero : Var[fun ω ↦ (X ω - μ[X]) + θ * (Y ω - μ[Y]); μ] = 0 := by
        have hVar :
            Var[fun ω ↦ (X ω - μ[X]) + θ * (Y ω - μ[Y]); μ]
              = 1 ^ 2 * Var[X; μ] + 2 * 1 * θ * cov[X, Y; μ] + θ ^ 2 * Var[Y; μ] := by
          simpa using variance_centered_linear_combo hX hY 1 θ
        rw [hVar]
        dsimp [θ]
        field_simp [hVarY]
        rw [hEq]
        ring
      refine ⟨1, θ, by positivity, ?_⟩
      simpa using
        (variance_eq_zero_iff_ae_zero_centered_linear_combo hX hY 1 θ).1
          (by simpa using hVarZero)
  · rintro ⟨a, b, hab, hRel⟩
    by_cases hb : b = 0
    · -- If `b = 0`, then the relation forces the centered version of `X` to vanish a.s.
      have ha : a ≠ 0 := by
        intro ha0
        rw [ha0, hb] at hab
        norm_num at hab
      have hAeXScaled : (fun ω ↦ a * (X ω - μ[X])) =ᵐ[μ] fun _ ↦ (0 : ℝ) := by
        simpa [hb] using hRel
      have hAeX : (fun ω ↦ X ω - μ[X]) =ᵐ[μ] fun _ ↦ (0 : ℝ) := by
        filter_upwards [hAeXScaled] with ω hω
        have : X ω - μ[X] = 0 := (mul_eq_zero.mp hω).resolve_left ha
        simpa using this
      have hVarXCentered : Var[fun ω ↦ X ω - μ[X]; μ] = 0 := by
        rw [variance_congr hAeX]
        exact variance_zero μ
      have hVarX : Var[X; μ] = 0 := by
        simpa [variance_sub_const hX.aestronglyMeasurable] using hVarXCentered
      have hIneq := covariance_sq_le_variance_mul_variance hX hY
      have hCovSq : cov[X, Y; μ] ^ 2 = 0 := by
        have hLeZero : cov[X, Y; μ] ^ 2 ≤ 0 := by
          simpa [hVarX] using hIneq
        exact le_antisymm hLeZero (sq_nonneg _)
      simp [hVarX, hCovSq]
    · -- If `b ≠ 0`, solve the relation for the centered version of `Y` and compute variance and
      -- covariance from the scalar-multiple formulas.
      have hAeY :
          (fun ω ↦ Y ω - μ[Y]) =ᵐ[μ] fun ω ↦ (-a / b) * (X ω - μ[X]) := by
        filter_upwards [hRel] with ω hω
        field_simp [hb] at hω ⊢
        linarith
      have hVarY' : Var[Y; μ] = (-a / b) ^ 2 * Var[X; μ] := by
        calc
          Var[Y; μ] = Var[fun ω ↦ Y ω - μ[Y]; μ] := by
            rw [variance_sub_const hY.aestronglyMeasurable]
          _ = Var[fun ω ↦ (-a / b) * (X ω - μ[X]); μ] := by
            rw [variance_congr hAeY]
          _ = (-a / b) ^ 2 * Var[fun ω ↦ X ω - μ[X]; μ] := by
            rw [variance_const_mul]
          _ = (-a / b) ^ 2 * Var[X; μ] := by
            rw [variance_sub_const hX.aestronglyMeasurable]
      have hCov : cov[X, Y; μ] = (-a / b) * Var[X; μ] := by
        calc
          cov[X, Y; μ] = cov[fun ω ↦ X ω - μ[X], fun ω ↦ Y ω - μ[Y]; μ] := by
            rw [← covariance_sub_const_left (hX.integrable (by simp)) (μ[X])]
            rw [← covariance_sub_const_right (hY.integrable (by simp)) (μ[Y])]
          _ = cov[fun ω ↦ X ω - μ[X], fun ω ↦ (-a / b) * (X ω - μ[X]); μ] := by
            exact covariance_congr_ae (Filter.EventuallyEq.rfl) hAeY
          _ = (-a / b) * cov[fun ω ↦ X ω - μ[X], fun ω ↦ X ω - μ[X]; μ] := by
            rw [covariance_const_mul_right]
          _ = (-a / b) * Var[fun ω ↦ X ω - μ[X]; μ] := by
            rw [covariance_self]
            exact (hX.sub (memLp_const _)).aemeasurable
          _ = (-a / b) * Var[X; μ] := by
            rw [variance_sub_const hX.aestronglyMeasurable]
      calc
        cov[X, Y; μ] ^ 2 = ((-a / b) * Var[X; μ]) ^ 2 := by rw [hCov]
        _ = Var[X; μ] * ((-a / b) ^ 2 * Var[X; μ]) := by ring
        _ = Var[X; μ] * Var[Y; μ] := by rw [hVarY']

-- Proof sketch: rewrite the centered linear relation from the previous theorem by expanding the
-- centered variables and moving the constant term to the right-hand side; conversely, subtract the
-- expectation-determined constant to recover the centered form.
/-- Textbook affine reformulation of Theorem 5.8 (2): equality holds exactly when `X` and `Y`
satisfy a nontrivial almost-sure affine relation, with the constant determined canonically by the
expectations. -/
theorem covariance_sq_eq_variance_mul_variance_iff_ae_affine_relation
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] ^ 2 = Var[X; μ] * Var[Y; μ] ↔
      ∃ a b : ℝ,
        0 < |a| + |b| ∧
          (fun ω ↦ a * X ω + b * Y ω) =ᵐ[μ] fun _ ↦ a * μ[X] + b * μ[Y] := by
  constructor
  · intro hEq
    -- Convert the centered equality criterion from part (2) into the affine form.
    rcases (covariance_sq_eq_variance_mul_variance_iff_ae_linear_relation_centered hX hY).1 hEq with
      ⟨a, b, hab, hCentered⟩
    exact ⟨a, b, hab, (ae_centered_relation_iff_ae_affine_relation a b).1 hCentered⟩
  · rintro ⟨a, b, hab, hAffine⟩
    -- Recenter the affine relation and apply the equality criterion from part (2).
    exact
      (covariance_sq_eq_variance_mul_variance_iff_ae_linear_relation_centered hX hY).2
        ⟨a, b, hab, (ae_centered_relation_iff_ae_affine_relation a b).2 hAffine⟩
