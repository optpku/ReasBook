/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Helper for Theorem 15.21: the image set of characteristic functions coming from a family of
probability measures is the range of the corresponding family-valued map. -/
lemma charFunFamily_range_eq (ℱ : Set (ProbabilityMeasure E)) :
    Set.range (fun μ : ℱ ↦ charFun ((μ : ProbabilityMeasure E) : Measure E)) =
      charFun '' ((↑) '' ℱ : Set (Measure E)) := by
  ext f
  constructor
  · rintro ⟨μ, rfl⟩
    exact ⟨((μ : ProbabilityMeasure E) : Measure E), ⟨(μ : ProbabilityMeasure E), μ.property, rfl⟩,
      rfl⟩
  · rintro ⟨ν, ⟨μ, hμ, rfl⟩, rfl⟩
    exact ⟨⟨μ, hμ⟩, rfl⟩

/-- Helper for Theorem 15.21: the oscillatory kernel is Lipschitz in the frequency variable with
constant `‖x‖`. -/
lemma dist_innerProbChar_le_norm_mul_dist (t s x : E) :
    dist (BoundedContinuousFunction.innerProbChar t x)
        (BoundedContinuousFunction.innerProbChar s x) ≤
      ‖x‖ * dist t s := by
  have hphase :
      Complex.exp (inner ℝ x t * Complex.I) - Complex.exp (inner ℝ x s * Complex.I) =
        (Complex.exp (inner ℝ x (t - s) * Complex.I) - 1) *
          Complex.exp (inner ℝ x s * Complex.I) := by
    have hmul :
        Complex.exp (inner ℝ x t * Complex.I) =
          Complex.exp (inner ℝ x (t - s) * Complex.I) * Complex.exp (inner ℝ x s * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      rw [inner_sub_right]
      have hsub :
          (((inner ℝ x t - inner ℝ x s : ℝ) : ℂ)) =
            (inner ℝ x t : ℂ) - (inner ℝ x s : ℂ) := by
        norm_num
      rw [hsub, sub_mul]
      ring
    rw [hmul]
    ring
  -- Normalize the phase difference so the standard exponential bound applies.
  calc
    dist (BoundedContinuousFunction.innerProbChar t x) (BoundedContinuousFunction.innerProbChar s x)
      = ‖Complex.exp (inner ℝ x t * Complex.I) - Complex.exp (inner ℝ x s * Complex.I)‖ := by
          simp [BoundedContinuousFunction.innerProbChar_apply, dist_eq_norm]
    _ = ‖(Complex.exp (inner ℝ x (t - s) * Complex.I) - 1) *
          Complex.exp (inner ℝ x s * Complex.I)‖ := by
          rw [hphase]
    _ = ‖Complex.exp (inner ℝ x (t - s) * Complex.I) - 1‖ *
          ‖Complex.exp (inner ℝ x s * Complex.I)‖ := by
          rw [norm_mul]
    _ = ‖Complex.exp (inner ℝ x (t - s) * Complex.I) - 1‖ := by
          rw [Complex.norm_exp_ofReal_mul_I, mul_one]
    _ ≤ ‖inner ℝ x (t - s)‖ := by
          simpa [mul_comm] using
            (Real.norm_exp_I_mul_ofReal_sub_one_le (x := inner ℝ x (t - s)))
    _ ≤ ‖x‖ * ‖t - s‖ := norm_inner_le_norm _ _
    _ = ‖x‖ * dist t s := by
          simp [dist_eq_norm]

/-- Helper for Theorem 15.21: the increment of a characteristic function is the integral of the
pointwise increment of the oscillatory kernel. -/
lemma charFun_sub_eq_integral_innerProbChar_sub
    (μ : Measure E) [IsFiniteMeasure μ] (t s : E) :
    charFun μ t - charFun μ s =
      ∫ x, ((BoundedContinuousFunction.innerProbChar t x : ℂ) -
        BoundedContinuousFunction.innerProbChar s x) ∂μ := by
  -- Rewrite the difference of characteristic functions as one integral difference.
  rw [charFun_eq_integral_innerProbChar, charFun_eq_integral_innerProbChar,
    ← integral_sub (BoundedContinuousFunction.integrable μ _)
      (BoundedContinuousFunction.integrable μ _)]

/-- Theorem 15.21: if `ℱ` is a tight family of probability measures on `ℝ^d`, then the set of
their characteristic functions is uniformly equicontinuous on `ℝ^d`. -/
-- Proof sketch: use tightness to choose a common compact cube carrying almost all mass for every
-- `μ ∈ ℱ`; on that compact set the oscillatory kernel `x ↦ exp (⟪x, t⟫ * I)` varies uniformly in
-- `t`, which gives a uniform bound on `|1 - charFun μ (t - s)|`; then combine this with the
-- translation identity from the preceding lemma to deduce a common modulus of continuity.
theorem tight_probabilityMeasureFamily_charFunSet_uniformEquicontinuous
    (ℱ : Set (ProbabilityMeasure E))
    (hℱ : IsTightMeasureSet ((↑) '' ℱ : Set (Measure E))) :
    (charFun '' ((↑) '' ℱ : Set (Measure E))).UniformEquicontinuous := by
  let F : ℱ → E → ℂ := fun μ t ↦ charFun ((μ : ProbabilityMeasure E) : Measure E) t
  rw [← charFunFamily_range_eq (ℱ := ℱ)]
  change UniformEquicontinuous ((↑) : Set.range F → E → ℂ)
  rw [← uniformEquicontinuous_iff_range]
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  obtain ⟨K, hKcompact, hKtail⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hℱ)
      (ENNReal.ofReal (ε / 4)) (by positivity)
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  obtain ⟨R, hRpos, hRsub⟩ := hKcompact.isBounded.subset_closedBall_lt (a := 0) (c := (0 : E))
  let δ : ℝ := ε / (4 * R)
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδpos, ?_⟩
  intro t s hts μ
  let ν : Measure E := ((μ : ProbabilityMeasure E) : Measure E)
  let g : BoundedContinuousFunction E ℂ :=
    BoundedContinuousFunction.innerProbChar t - BoundedContinuousFunction.innerProbChar s
  have hν_mem : ν ∈ ((↑) '' ℱ : Set (Measure E)) := by
    exact ⟨(μ : ProbabilityMeasure E), μ.property, rfl⟩
  have htail_real : ν.real Kᶜ ≤ ε / 4 := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    simpa [ν] using hKtail ν hν_mem
  have hRδ : R * δ = ε / 4 := by
    dsimp [δ]
    field_simp [hRpos.ne']
  have hgK : Integrable g (ν.restrict K) := g.integrable _
  have hgKc : Integrable g (ν.restrict Kᶜ) := g.integrable _
  have hboundK :
      ∀ᵐ x ∂(ν.restrict K), ‖g x‖ ≤ R * dist t s := by
    filter_upwards [ae_restrict_mem hKmeas] with x hx
    have hxR : ‖x‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hRsub hx
    -- On the tight compact set, the oscillatory kernel shares a uniform Lipschitz bound.
    calc
      ‖g x‖ =
          dist (BoundedContinuousFunction.innerProbChar t x)
            (BoundedContinuousFunction.innerProbChar s x) := by
            simp [g, dist_eq_norm]
      _ ≤ ‖x‖ * dist t s := dist_innerProbChar_le_norm_mul_dist t s x
      _ ≤ R * dist t s := by
            exact mul_le_mul_of_nonneg_right hxR dist_nonneg
  have hboundKc :
      ∀ᵐ x ∂(ν.restrict Kᶜ), ‖g x‖ ≤ 2 := by
    refine Filter.Eventually.of_forall fun x => ?_
    -- Outside the compact set, we only use the trivial bound `|e^{iθ} - e^{iφ}| ≤ 2`.
    calc
      ‖g x‖ =
          ‖(BoundedContinuousFunction.innerProbChar t x : ℂ) -
            BoundedContinuousFunction.innerProbChar s x‖ := by
            simp [g]
      _ ≤ ‖BoundedContinuousFunction.innerProbChar t x‖ +
            ‖BoundedContinuousFunction.innerProbChar s x‖ := by
            exact norm_sub_le _ _
      _ = 2 := by
            norm_num [BoundedContinuousFunction.innerProbChar_apply, Complex.norm_exp_ofReal_mul_I]
  have hmeasureK_le_one : (ν.restrict K).real Set.univ ≤ 1 := by
    simpa using (MeasureTheory.measureReal_le_one (μ := ν) (s := K))
  have hIntK :
      ‖∫ x, g x ∂(ν.restrict K)‖ ≤ R * dist t s := by
    calc
      ‖∫ x, g x ∂(ν.restrict K)‖ ≤
          (R * dist t s) * (ν.restrict K).real Set.univ := by
            exact norm_integral_le_of_norm_le_const hboundK
      _ ≤ (R * dist t s) * 1 := by
            exact mul_le_mul_of_nonneg_left hmeasureK_le_one (by positivity)
      _ = R * dist t s := by ring
  have hIntKc :
      ‖∫ x, g x ∂(ν.restrict Kᶜ)‖ ≤ 2 * ν.real Kᶜ := by
    calc
      ‖∫ x, g x ∂(ν.restrict Kᶜ)‖ ≤ 2 * (ν.restrict Kᶜ).real Set.univ := by
            exact norm_integral_le_of_norm_le_const hboundKc
      _ = 2 * ν.real Kᶜ := by
            simp
  have hfirst : R * dist t s < ε / 4 := by
    have hmul : R * dist t s < R * δ := mul_lt_mul_of_pos_left hts hRpos
    rwa [hRδ] at hmul
  have hsecond : 2 * ν.real Kᶜ ≤ ε / 2 := by
    nlinarith
  have hsplit :
      charFun ν t - charFun ν s =
        ∫ x, g x ∂(ν.restrict K) + ∫ x, g x ∂(ν.restrict Kᶜ) := by
    calc
      charFun ν t - charFun ν s = ∫ x, g x ∂ν := by
        simpa [g] using charFun_sub_eq_integral_innerProbChar_sub (μ := ν) (t := t) (s := s)
      _ = ∫ x, g x ∂(ν.restrict K + ν.restrict Kᶜ) := by
        rw [Measure.restrict_add_restrict_compl hKmeas]
      _ = ∫ x, g x ∂(ν.restrict K) + ∫ x, g x ∂(ν.restrict Kᶜ) := by
        rw [integral_add_measure hgK hgKc]
  -- Combine the compact-part bound and the tight tail estimate into one common modulus.
  calc
    dist (F μ t) (F μ s) = ‖charFun ν t - charFun ν s‖ := by
      simp [F, ν, dist_eq_norm]
    _ = ‖∫ x, g x ∂(ν.restrict K) + ∫ x, g x ∂(ν.restrict Kᶜ)‖ := by
      rw [hsplit]
    _ ≤ ‖∫ x, g x ∂(ν.restrict K)‖ + ‖∫ x, g x ∂(ν.restrict Kᶜ)‖ := norm_add_le _ _
    _ ≤ R * dist t s + 2 * ν.real Kᶜ := add_le_add hIntK hIntKc
    _ < ε := by
      have hsum : R * dist t s + 2 * ν.real Kᶜ < ε / 4 + ε / 2 := by
        exact add_lt_add_of_lt_of_le hfirst hsecond
      nlinarith

/-- Every characteristic function of a probability measure on `ℝ^d` is uniformly continuous. -/
-- Proof sketch: apply the uniform equicontinuity theorem to the singleton family `{μ}`; singleton
-- families are tight, and then extract uniform continuity of the unique member from
-- `Set.UniformEquicontinuous.uniformContinuous_of_mem`.
theorem probabilityMeasure_charFun_uniformContinuous (μ : ProbabilityMeasure E) :
    UniformContinuous (charFun (μ : Measure E)) := by
  have hsingleton :
      IsTightMeasureSet
        (((↑) : ProbabilityMeasure E → Measure E) '' ({μ} : Set (ProbabilityMeasure E))) := by
    simpa using (MeasureTheory.isTightMeasureSet_singleton (μ := (μ : Measure E)))
  have heq :=
    tight_probabilityMeasureFamily_charFunSet_uniformEquicontinuous
      ({μ} : Set (ProbabilityMeasure E)) hsingleton
  -- The singleton family contributes exactly one characteristic function to the equicontinuous set.
  exact heq.uniformContinuous_of_mem ⟨(μ : Measure E), ⟨μ, by simp, rfl⟩, rfl⟩

end
