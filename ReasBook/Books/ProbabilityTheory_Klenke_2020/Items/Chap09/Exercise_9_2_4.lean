/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory unitInterval

universe u

variable {Ω : Type u} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ m0}

/-- Helper for Exercise 9.2.4: clip `(x + 1) / 2` into the unit interval. -/
noncomputable def signedThreshold (x : ℝ) : I :=
  ⟨max 0 (min 1 ((x + 1) / 2)), by
    constructor
    · exact le_max_left _ _
    · exact max_le (show (0 : ℝ) ≤ 1 by norm_num) (min_le_left _ _)⟩

/-- Helper for Exercise 9.2.4: the explicit `{-1,1}`-valued sampler driven by a unit-interval
coordinate. -/
noncomputable def signedAuxMap (z : ℝ × I) : ℝ :=
  if z.2 ≤ signedThreshold z.1 then 1 else -1

/-- Helper for Exercise 9.2.4: the clipping map is measurable. -/
lemma measurable_signedThreshold : Measurable signedThreshold := by
  let f : ℝ → ℝ := fun x ↦ max 0 (min 1 ((x + 1) / 2))
  have hf : Measurable f := by
    fun_prop
  have hmem : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    dsimp [f]
    constructor
    · exact le_max_left _ _
    · exact max_le (show (0 : ℝ) ≤ 1 by norm_num) (min_le_left _ _)
  simpa [signedThreshold, f] using (hf.subtype_mk (h := hmem))

/-- Helper for Exercise 9.2.4: the measurable `{-1,1}`-valued kernel with conditional mean `x`
on `[-1,1]`. -/
noncomputable def signedTwoPointKernel : Kernel ℝ ℝ :=
  (((Kernel.id : Kernel ℝ ℝ) ×ₖ Kernel.const ℝ (volume : Measure I)).map signedAuxMap)

/-- Helper for Exercise 9.2.4: `signedAuxMap` is jointly measurable. -/
lemma measurable_signedAuxMap : Measurable signedAuxMap := by
  -- The sampler is piecewise constant on the measurable comparison event.
  refine measurable_const.piecewise ?_ measurable_const
  refine measurableSet_le (measurable_subtype_coe.comp measurable_snd) ?_
  exact (measurable_signedThreshold.subtype_val).comp measurable_fst

/-- Helper for Exercise 9.2.4: the explicit two-point kernel is Markov. -/
instance signedTwoPointKernel_isMarkovKernel : IsMarkovKernel signedTwoPointKernel := by
  simpa [signedTwoPointKernel] using
    (Kernel.IsMarkovKernel.map
      (((Kernel.id : Kernel ℝ ℝ) ×ₖ Kernel.const ℝ (volume : Measure I)))
      measurable_signedAuxMap)

/-- Helper for Exercise 9.2.4: on each fiber `x`, the kernel is the pushforward of uniform
measure on `I` by `u ↦ signedAuxMap (x, u)`. -/
lemma signedTwoPointKernel_apply (x : ℝ) :
    signedTwoPointKernel x = (volume : Measure I).map (fun u : I ↦ signedAuxMap (x, u)) := by
  -- Unfold the product kernel at `x` and collapse the deterministic first coordinate.
  rw [signedTwoPointKernel, Kernel.map_apply _ measurable_signedAuxMap, Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod]
  simpa [Function.comp_def] using
    (Measure.map_map (μ := (volume : Measure I)) (f := Prod.mk x) (g := signedAuxMap)
      measurable_signedAuxMap measurable_prodMk_left)

/-- Helper for Exercise 9.2.4: under `ν.prod volume`, the joint law of the first coordinate and the
explicit sampler is `ν ⊗ₘ signedTwoPointKernel`. -/
lemma signedAuxSampler_pairLaw_eq_compProd (ν : Measure ℝ) [IsFiniteMeasure ν] :
    (ν.prod (volume : Measure I)).map (fun z : ℝ × I ↦ (z.1, signedAuxMap z)) =
      ν ⊗ₘ signedTwoPointKernel := by
  -- Compare both sides on measurable rectangles and identify each fiber with
  -- the defining pushforward measure of `signedTwoPointKernel`.
  refine Measure.ext_prod ?_
  intro s t hs ht
  have hF_meas : Measurable (fun z : ℝ × I ↦ (z.1, signedAuxMap z)) := by
    exact measurable_fst.prodMk measurable_signedAuxMap
  rw [Measure.map_apply hF_meas (hs.prod ht), Measure.compProd_apply_prod hs ht]
  rw [Measure.prod_apply (hF_meas (hs.prod ht))]
  have hslice :
      (fun x : ℝ ↦
        (volume : Measure I)
          (Prod.mk x ⁻¹' ((fun z : ℝ × I ↦ (z.1, signedAuxMap z)) ⁻¹' (s ×ˢ t)))) =
        s.indicator (fun x ↦ signedTwoPointKernel x t) := by
    funext x
    by_cases hx : x ∈ s
    · have hpre :
          Prod.mk x ⁻¹' ((fun z : ℝ × I ↦ (z.1, signedAuxMap z)) ⁻¹' (s ×ˢ t)) =
            (fun u : I ↦ signedAuxMap (x, u)) ⁻¹' t := by
        ext u
        simp [hx]
      rw [hpre, Set.indicator_of_mem hx, signedTwoPointKernel_apply]
      rw [Measure.map_apply (μ := (volume : Measure I)) (f := fun u : I ↦ signedAuxMap (x, u))
        (measurable_signedAuxMap.comp measurable_prodMk_left) ht]
    · have hpre :
          Prod.mk x ⁻¹' ((fun z : ℝ × I ↦ (z.1, signedAuxMap z)) ⁻¹' (s ×ˢ t)) = ∅ := by
        ext u
        simp [hx]
      simp [hpre, Set.indicator, hx]
  rw [hslice, lintegral_indicator hs]

/-- Helper for Exercise 9.2.4: the kernel is supported on `{-1,1}` for every parameter. -/
lemma signedTwoPointKernel_support (x : ℝ) :
    signedTwoPointKernel x (({-1} : Set ℝ) ∪ {1}) = 1 := by
  -- The sampler only outputs the two endpoint values, so the pushforward mass of that set is `1`.
  rw [signedTwoPointKernel_apply x]
  have hs : MeasurableSet ((({-1} : Set ℝ) ∪ {1}) : Set ℝ) :=
    measurableSet_singleton (-1) |>.union (measurableSet_singleton 1)
  have hpre :
      (fun u : I ↦ signedAuxMap (x, u)) ⁻¹' ((({-1} : Set ℝ) ∪ {1}) : Set ℝ) = Set.univ := by
    ext u
    by_cases hu : u ≤ signedThreshold x
    · simp [signedAuxMap, hu]
    · simp [signedAuxMap, hu]
  have hmap :=
    Measure.map_apply (μ := (volume : Measure I)) (f := fun u : I ↦ signedAuxMap (x, u))
      (measurable_signedAuxMap.comp measurable_prodMk_left) hs
  rw [hmap, hpre, measure_univ]

/-- Helper for Exercise 9.2.4: on `[-1,1]`, the clipping map is inactive. -/
lemma signedThreshold_coe_eq_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    ((signedThreshold x : I) : ℝ) = (x + 1) / 2 := by
  have hx' := abs_le.mp hx
  have hx_left : -1 ≤ x := hx'.1
  have hx_right : x ≤ 1 := hx'.2
  have hnonneg : 0 ≤ (x + 1) / 2 := by linarith
  have hone : (x + 1) / 2 ≤ 1 := by linarith
  simp [signedThreshold, hnonneg, hone]

/-- Helper for Exercise 9.2.4: the kernel mean is `2 * signedThreshold x - 1`. -/
lemma integral_signedTwoPointKernel (x : ℝ) :
    ∫ y, y ∂signedTwoPointKernel x = 2 * ((signedThreshold x : I) : ℝ) - 1 := by
  let q : I := signedThreshold x
  have hrepr :
      (fun u : I ↦ signedAuxMap (x, u)) =
        fun u : I ↦ 2 * Set.indicator (Set.Iic q) (fun _ : I ↦ (1 : ℝ)) u - 1 := by
    funext u
    by_cases hu : u ≤ q
    · simp [signedAuxMap, hu, Set.indicator, q]
      norm_num
    · simp [signedAuxMap, hu, Set.indicator, q]
  have hIic : MeasurableSet (Set.Iic q : Set I) := measurableSet_Iic
  have hmap :
      ∫ y, y ∂((volume : Measure I).map (fun u : I ↦ signedAuxMap (x, u))) =
        ∫ u, signedAuxMap (x, u) ∂(volume : Measure I) := by
    simpa using
      (integral_map_of_stronglyMeasurable (μ := (volume : Measure I))
        (φ := fun u : I ↦ signedAuxMap (x, u)) (f := fun y : ℝ ↦ y)
        (measurable_signedAuxMap.comp measurable_prodMk_left)
        stronglyMeasurable_id)
  rw [signedTwoPointKernel_apply x]
  rw [hmap, hrepr]
  have hconst : Integrable (fun _ : I ↦ (1 : ℝ)) (volume : Measure I) := integrable_const 1
  rw [integral_sub ((hconst.indicator hIic).const_mul 2) hconst]
  rw [integral_const_mul, integral_indicator hIic, integral_const, smul_eq_mul, integral_const]
  have hvol : (volume : Measure I).real (Set.Iic q) = (q : ℝ) := by
    rw [Measure.real, unitInterval.volume_Iic]
    exact ENNReal.toReal_ofReal q.2.1
  simp [hvol, q, two_mul, sub_eq_add_neg]

/-- Helper for Exercise 9.2.4: on `[-1,1]`, the kernel mean is exactly `x`. -/
lemma integral_signedTwoPointKernel_eq_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    ∫ y, y ∂signedTwoPointKernel x = x := by
  -- Once the clipping is inactive, the mean simplifies to the affine identity
  -- `2 * ((x + 1)/2) - 1`.
  rw [integral_signedTwoPointKernel, signedThreshold_coe_eq_of_abs_le_one hx]
  ring

/-- Helper for Exercise 9.2.4: if `|x| ≤ 1`, then `exp (t * x)` is bounded by the secant line of
`exp` through `±t`. -/
lemma exp_mul_le_cosh_add_mul_sinh_of_abs_le_one {x t : ℝ} (hx : |x| ≤ 1) :
    Real.exp (t * x) ≤ Real.cosh t + x * Real.sinh t := by
  simpa [mul_comm, add_comm, add_left_comm, add_assoc] using
    Real.exp_mul_le_cosh_add_mul_sinh hx t

/- Clause (1) is `source-facing` through the conditional-law owner abstraction: the corrected main
statement is the existence of a `{-1,1}`-valued Markov kernel with conditional mean `x`, defined
over the law of `X`. The `Ω × I` realization is kept only as a `bridge/view` consequence. -/
/-- Clause (1) of Exercise 9.2.4: if a real random variable `X` satisfies `|X| ≤ 1` almost surely,
then its
law admits a `{-1,1}`-valued conditional kernel with mean `x`. -/
theorem exists_signed_kernel_with_mean_of_abs_le_one {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_bdd : ∀ᵐ ω ∂μ, |X ω| ≤ 1) :
    ∃ κ : Kernel ℝ ℝ, IsMarkovKernel κ ∧
      (∀ᵐ x ∂(μ.map X), κ x (({-1} : Set ℝ) ∪ {1}) = (1 : ENNReal)) ∧
      (fun x ↦ ∫ y, y ∂κ x) =ᵐ[μ.map X] fun x ↦ x := by
  refine ⟨signedTwoPointKernel, inferInstance, ?_, ?_⟩
  · -- The explicit kernel is supported on `{-1,1}` for every parameter, hence certainly a.e.
    exact Filter.Eventually.of_forall signedTwoPointKernel_support
  · -- The mean identity holds on `μ.map X`-almost every `x` because those
    -- `x` still lie in `[-1,1]`.
    have habs_meas : MeasurableSet {x : ℝ | |x| ≤ 1} := by
      exact measurableSet_le continuous_abs.measurable measurable_const
    have hX_bdd_map : ∀ᵐ x ∂(μ.map X), |x| ≤ 1 := by
      rw [ae_map_iff hX_meas.aemeasurable habs_meas]
      simpa using hX_bdd
    filter_upwards [hX_bdd_map] with x hx
    exact integral_signedTwoPointKernel_eq_of_abs_le_one hx

-- Proof sketch: realize the kernel from `exists_signed_kernel_with_mean_of_abs_le_one` on the
-- product extension `Ω × I`; the resulting random variable has that kernel as its conditional law
-- given `X ∘ Prod.fst`, hence its conditional expectation is `X ∘ Prod.fst`.
/-- Bridge for Exercise 9.2.4 (1): after adjoining an auxiliary unit-interval coordinate, the
canonical two-point conditional law can be realized by a `{-1, 1}`-valued random variable whose
conditional expectation with respect to `X ∘ Prod.fst` is `X ∘ Prod.fst`. -/
theorem exists_signed_condexp_eq_of_abs_le_one_prod_extension {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_bdd : ∀ᵐ ω ∂μ, |X ω| ≤ 1) :
    ∃ Y : Ω × I → ℝ, Measurable Y ∧ Set.range Y ⊆ ({-1, 1} : Set ℝ) ∧
      (μ.prod (volume : Measure I))[Y |
          MeasurableSpace.comap (X ∘ Prod.fst) (borel ℝ)] =ᵐ[μ.prod (volume : Measure I)]
        X ∘ Prod.fst :=
by
  let ρ : Measure (Ω × I) := μ.prod (volume : Measure I)
  let Y : Ω × I → ℝ := fun p ↦ signedAuxMap (X p.1, p.2)
  refine ⟨Y, ?_, ?_, ?_⟩
  · -- The product-extension sampler is measurable because it is the explicit sampler composed with
    -- `(ω, u) ↦ (X ω, u)`.
    simpa [Y] using measurable_signedAuxMap.comp (hX_meas.prodMap measurable_id)
  · -- The sampler only returns the values `-1` and `1`.
    intro y hy
    rcases hy with ⟨p, rfl⟩
    by_cases hp : p.2 ≤ signedThreshold (X p.1)
    · simp [Y, signedAuxMap, hp]
    · simp [Y, signedAuxMap, hp]
  · have hY_meas : Measurable Y := by
      simpa [Y] using measurable_signedAuxMap.comp (hX_meas.prodMap measurable_id)
    have hXfst_meas : Measurable (X ∘ (Prod.fst : Ω × I → Ω)) := hX_meas.comp measurable_fst
    have hmapX :
        ρ.map (X ∘ Prod.fst) = μ.map X := by
      -- The auxiliary unit-interval coordinate is independent noise, so forgetting it recovers `μ`.
      calc
        ρ.map (X ∘ Prod.fst) = (ρ.map (Prod.fst : Ω × I → Ω)).map X := by
          simpa [Function.comp_def] using
            (Measure.map_map (μ := ρ) (f := (Prod.fst : Ω × I → Ω)) (g := X)
              hX_meas measurable_fst).symm
        _ = μ.map X := by
          simp [ρ]
    have hY_norm_le : ∀ p : Ω × I, ‖Y p‖ ≤ 1 := by
      intro p
      by_cases hp : p.2 ≤ signedThreshold (X p.1)
      · simp [Y, signedAuxMap, hp]
      · simp [Y, signedAuxMap, hp]
    have hY_int : Integrable Y ρ :=
      Integrable.of_bound hY_meas.aestronglyMeasurable 1 <|
        Filter.Eventually.of_forall hY_norm_le
    have hpair :
        ρ.map (fun p ↦ ((X ∘ Prod.fst) p, Y p)) =
          ρ.map (X ∘ Prod.fst) ⊗ₘ signedTwoPointKernel := by
      have hmapProd :
          ρ.map (Prod.map X (fun u : I ↦ u)) = (μ.map X).prod (volume : Measure I) := by
        simpa [ρ] using
          (Measure.map_prod_map (μa := μ) (μc := (volume : Measure I))
            (f := X) (g := fun u : I ↦ u) hX_meas measurable_id).symm
      -- First push `(ω, u)` to `(X ω, u)`, then apply the already identified pair law on `ℝ × I`.
      calc
        ρ.map (fun p ↦ ((X ∘ Prod.fst) p, Y p)) =
            ρ.map (((fun z : ℝ × I ↦ (z.1, signedAuxMap z)) ∘ Prod.map X (fun u : I ↦ u))) := by
          rfl
        _ = (ρ.map (Prod.map X (fun u : I ↦ u))).map (fun z : ℝ × I ↦ (z.1, signedAuxMap z)) := by
          symm
          exact AEMeasurable.map_map_of_aemeasurable
            ((measurable_fst.prodMk measurable_signedAuxMap).aemeasurable)
            ((hX_meas.prodMap measurable_id).aemeasurable)
        _ = ((μ.map X).prod (volume : Measure I)).map
            (fun z : ℝ × I ↦ (z.1, signedAuxMap z)) := by
          rw [hmapProd]
        _ = (μ.map X) ⊗ₘ signedTwoPointKernel := signedAuxSampler_pairLaw_eq_compProd (μ.map X)
        _ = ρ.map (X ∘ Prod.fst) ⊗ₘ signedTwoPointKernel := by
          rw [hmapX]
    have hcond :
        condDistrib Y (X ∘ Prod.fst) ρ =ᵐ[ρ.map (X ∘ Prod.fst)] signedTwoPointKernel :=
      condDistrib_ae_eq_of_measure_eq_compProd (X ∘ Prod.fst) hY_meas.aemeasurable hpair
    have hX_bdd_map : ∀ᵐ x ∂ρ.map (X ∘ Prod.fst), |x| ≤ 1 := by
      rw [hmapX]
      have habs_meas : MeasurableSet {x : ℝ | |x| ≤ 1} := by
        exact measurableSet_le continuous_abs.measurable measurable_const
      rw [ae_map_iff hX_meas.aemeasurable habs_meas]
      simpa using hX_bdd
    have hmean_map :
        (fun x ↦ ∫ y, y ∂condDistrib Y (X ∘ Prod.fst) ρ x) =ᵐ[ρ.map (X ∘ Prod.fst)] fun x ↦ x := by
      -- Route correction: after identifying the joint law once, work on the pushed-forward law of
      -- `X ∘ Prod.fst` instead of transporting kernels back through the product space.
      filter_upwards [hcond, hX_bdd_map] with x hxcond hxbdd
      rw [hxcond]
      exact integral_signedTwoPointKernel_eq_of_abs_le_one hxbdd
    have hmean :
        (fun p ↦ ∫ y, y ∂condDistrib Y (X ∘ Prod.fst) ρ ((X ∘ Prod.fst) p)) =ᵐ[ρ]
          X ∘ Prod.fst :=
      ae_eq_comp hXfst_meas.aemeasurable hmean_map
    -- The conditional expectation is the mean of the conditional law, and that mean is exactly
    -- `X ∘ Prod.fst`.
    calc
      ρ[Y | MeasurableSpace.comap (X ∘ Prod.fst) (borel ℝ)] =ᵐ[ρ]
          fun p ↦ ∫ y, y ∂condDistrib Y (X ∘ Prod.fst) ρ ((X ∘ Prod.fst) p) := by
        simpa [ρ] using
          (condExp_ae_eq_integral_condDistrib' (μ := ρ) (X := X ∘ Prod.fst) hXfst_meas hY_int)
      _ =ᵐ[ρ] X ∘ Prod.fst := hmean

-- Proof sketch: use the product-extension conditional-Bernoulli bridge above,
-- or equivalently apply the owner theorem
-- `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` to the interval `[-1,1]`. The additional
-- `cosh` bound is the textbook refinement preceding the Gaussian estimate
-- `Real.cosh_le_exp_half_sq`.
/-- Clause (2) of Exercise 9.2.4: if `|X| ≤ 1` almost surely and `X` has mean zero, then
`E[e^{t X}] ≤ cosh t ≤ e^{t^2 / 2}` for every real `t`. -/
theorem mgf_le_cosh_and_cosh_le_exp_half_sq_of_abs_le_one {X : Ω → ℝ}
    (hX_meas : AEMeasurable X μ) (hX_bdd : ∀ᵐ ω ∂μ, |X ω| ≤ 1) (hX_mean : μ[X] = 0) :
    ∀ t : ℝ,
      mgf X μ t ≤ Real.cosh t ∧
        Real.cosh t ≤ Real.exp (t ^ 2 / 2) := by
  intro t
  have hX_mem : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-1 : ℝ) 1 := by
    filter_upwards [hX_bdd] with ω hω
    exact abs_le.mp hω
  have hX_int : Integrable X μ :=
    Integrable.of_bound hX_meas.aestronglyMeasurable 1 <|
      by simpa [Real.norm_eq_abs] using hX_bdd
  have hmgf_int : Integrable (fun ω ↦ Real.exp (t * X ω)) μ :=
    integrable_exp_mul_of_mem_Icc hX_meas hX_mem
  have hupper_int : Integrable (fun ω ↦ Real.cosh t + X ω * Real.sinh t) μ :=
    (integrable_const (Real.cosh t)).add (hX_int.mul_const (Real.sinh t))
  have hpoint :
      (fun ω ↦ Real.exp (t * X ω)) ≤ᵐ[μ]
        fun ω ↦ Real.cosh t + X ω * Real.sinh t := by
    filter_upwards [hX_bdd] with ω hω
    exact exp_mul_le_cosh_add_mul_sinh_of_abs_le_one hω
  constructor
  · -- Integrate the pointwise secant-line bound and use the zero-mean hypothesis to remove the
    -- `sinh` term.
    calc
      mgf X μ t = ∫ ω, Real.exp (t * X ω) ∂μ := rfl
      _ ≤ ∫ ω, (Real.cosh t + X ω * Real.sinh t) ∂μ :=
        integral_mono_ae hmgf_int hupper_int hpoint
      _ = Real.cosh t + μ[X] * Real.sinh t := by
        rw [integral_add (integrable_const _) (hX_int.mul_const _), integral_const, smul_eq_mul,
          integral_mul_const]
        simp
      _ = Real.cosh t := by simp [hX_mean]
  · -- The Gaussian envelope for `cosh` is the textbook endpoint of Hoeffding's lemma.
    simpa [mul_comm, mul_left_comm, mul_assoc] using Real.cosh_le_exp_half_sq t

/-- Helper for Exercise 9.2.4: martingale increments have conditional expectation zero with respect
to the present filtration level. -/
lemma martingaleIncrement_condExp_eq_zero {M : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (n : ℕ) :
    μ[(fun ω ↦ M (n + 1) ω - M n ω) | ℱ n] =ᵐ[μ] 0 := by
  -- Rewrite the increment conditional expectation by linearity and collapse each term with the
  -- martingale property.
  calc
    μ[(fun ω ↦ M (n + 1) ω - M n ω) | ℱ n] =ᵐ[μ]
        μ[M (n + 1) | ℱ n] - μ[M n | ℱ n] := by
      exact condExp_sub (hM.integrable (n + 1)) (hM.integrable n) (ℱ n)
    _ =ᵐ[μ] M n - M n := by
      exact (hM.condExp_ae_eq (show n ≤ n + 1 by omega)).sub (hM.condExp_ae_eq le_rfl)
    _ =ᵐ[μ] 0 := by
      simp

/-- Helper for Exercise 9.2.4: a bounded martingale increment lies in the symmetric interval
`[-c (n + 1), c (n + 1)]` almost surely. -/
lemma martingaleIncrement_mem_Icc {M : ℕ → Ω → ℝ} (c : ℕ → NNReal)
    (hinc : ∀ n, ∀ᵐ ω ∂μ, |M (n + 1) ω - M n ω| ≤ c (n + 1)) (n : ℕ) :
    ∀ᵐ ω ∂μ, M (n + 1) ω - M n ω ∈ Set.Icc (-(c (n + 1) : ℝ)) (c (n + 1) : ℝ) := by
  -- Rewrite the absolute-value bound as the standard two-sided interval membership needed later for
  -- exponential integrability.
  filter_upwards [hinc n] with ω hω
  simpa [Set.mem_Icc] using (abs_le.mp hω)

/-- Helper for Exercise 9.2.4: a centered increment in `[-C, C]` has conditional exponential moment
bounded by `cosh (t C)`. -/
lemma condExp_exp_mul_le_cosh_of_mem_Icc_of_condExp_eq_zero
    {m : MeasurableSpace Ω} (hm : m ≤ m0) {Z : Ω → ℝ} (C : NNReal) (t : ℝ)
    (hZ_int : Integrable Z μ) (hZ_mean : μ[Z | m] =ᵐ[μ] 0)
    (hZ_mem : ∀ᵐ ω ∂μ, Z ω ∈ Set.Icc (-(C : ℝ)) (C : ℝ)) :
    μ[fun ω ↦ Real.exp (t * Z ω) | m] ≤ᵐ[μ] fun _ ↦ Real.cosh (t * (C : ℝ)) := by
  by_cases hC : C = 0
  · -- In the degenerate branch the increment is almost surely zero, so the conditional expectation
    -- reduces to the constant `1 = cosh 0`.
    have hZ_zero : Z =ᵐ[μ] 0 := by
      filter_upwards [hZ_mem] with ω hω
      rcases hω with ⟨hlo, hhi⟩
      have hω0 : Z ω = 0 := by
        have hlo' : 0 ≤ Z ω := by simpa [hC] using hlo
        have hhi' : Z ω ≤ 0 := by simpa [hC] using hhi
        exact le_antisymm hhi' hlo'
      simp [hω0]
    have hExp_zero :
        (fun ω ↦ Real.exp (t * Z ω)) =ᵐ[μ] fun _ : Ω ↦ 1 := by
      filter_upwards [hZ_zero] with ω hω
      simp [hω]
    have hcond_congr :
        μ[fun ω ↦ Real.exp (t * Z ω) | m] =ᵐ[μ] μ[fun _ : Ω ↦ (1 : ℝ) | m] :=
      condExp_congr_ae (m := m) hExp_zero
    have hcond_one : μ[fun _ : Ω ↦ (1 : ℝ) | m] = fun _ : Ω ↦ 1 := condExp_const hm 1
    filter_upwards [hcond_congr] with ω hω
    rw [hcond_one] at hω
    simpa [hC] using hω.le
  · -- Route correction: work in the `Set.Icc`/`NNReal` normal form, then use linearity of
    -- conditional expectation to remove the centered term after the secant-line bound.
    let V : Ω → ℝ := fun ω ↦ Z ω / (C : ℝ)
    let U : Ω → ℝ := fun ω ↦ Real.cosh (t * (C : ℝ)) + (Real.sinh (t * (C : ℝ))) • V ω
    have hCpos : 0 < C := bot_lt_iff_ne_bot.mpr hC
    have hCpos_real : 0 < (C : ℝ) := by
      exact_mod_cast hCpos
    have hCne_real : (C : ℝ) ≠ 0 := ne_of_gt hCpos_real
    have hExp_int : Integrable (fun ω ↦ Real.exp (t * Z ω)) μ :=
      integrable_exp_mul_of_mem_Icc hZ_int.aestronglyMeasurable.aemeasurable hZ_mem
    have hV_int : Integrable V μ := by
      simpa [V, div_eq_mul_inv] using hZ_int.mul_const (1 / (C : ℝ))
    have hU_int : Integrable U μ := by
      exact (integrable_const (Real.cosh (t * (C : ℝ)))).add
        ((hV_int).smul (Real.sinh (t * (C : ℝ))))
    have hpoint : (fun ω ↦ Real.exp (t * Z ω)) ≤ᵐ[μ] U := by
      filter_upwards [hZ_mem] with ω hω
      have hVabs : |V ω| ≤ 1 := by
        have habs : |Z ω| ≤ (C : ℝ) := by
          exact abs_le.mpr hω
        have hdiv : |Z ω| / (C : ℝ) ≤ (C : ℝ) / (C : ℝ) :=
          div_le_div_of_nonneg_right habs C.2
        have hdiv' : |Z ω| / (C : ℝ) ≤ 1 := by
          simpa [hCne_real] using hdiv
        simpa [V, abs_div, abs_of_nonneg C.2] using hdiv'
      have hsec :=
        exp_mul_le_cosh_add_mul_sinh_of_abs_le_one (x := V ω) (t := t * (C : ℝ)) hVabs
      have hmul : (t * (C : ℝ)) * V ω = t * Z ω := by
        dsimp [V]
        field_simp [hCne_real]
      rw [hmul] at hsec
      simpa [U, V, mul_comm, mul_left_comm, mul_assoc] using hsec
    have hV_zero : μ[V | m] =ᵐ[μ] 0 := by
      have hV_smul : V = (1 / (C : ℝ)) • Z := by
        funext ω
        simp [V, div_eq_mul_inv, smul_eq_mul, mul_comm]
      calc
        μ[V | m] =ᵐ[μ] μ[(1 / (C : ℝ)) • Z | m] := by simpa [hV_smul]
        _ =ᵐ[μ] (1 / (C : ℝ)) • μ[Z | m] := condExp_smul (1 / (C : ℝ)) Z m
        _ =ᵐ[μ] 0 := by
          filter_upwards [hZ_mean] with ω hω
          simp [hω]
    have hU_eq : μ[U | m] =ᵐ[μ] fun _ : Ω ↦ Real.cosh (t * (C : ℝ)) := by
      have hadd := condExp_add (integrable_const (Real.cosh (t * (C : ℝ))))
        ((hV_int).smul (Real.sinh (t * (C : ℝ)))) m
      have hsmul :
          μ[(Real.sinh (t * (C : ℝ))) • V | m] =ᵐ[μ]
            (Real.sinh (t * (C : ℝ))) • μ[V | m] :=
        condExp_smul (μ := μ) (m₀ := m0) (Real.sinh (t * (C : ℝ))) V m
      have hconst : μ[fun _ : Ω ↦ Real.cosh (t * (C : ℝ)) | m] =
          fun _ : Ω ↦ Real.cosh (t * (C : ℝ)) := condExp_const hm _
      filter_upwards [hadd, hsmul, hV_zero] with ω haddω hsmulω hzeroω
      change μ[(fun x : Ω ↦ Real.cosh (t * (C : ℝ)) +
          (Real.sinh (t * (C : ℝ))) • V x) | m] ω = Real.cosh (t * (C : ℝ))
      have haddω' :
          μ[(fun x : Ω ↦ Real.cosh (t * (C : ℝ)) +
              (Real.sinh (t * (C : ℝ))) • V x) | m] ω =
            μ[fun x : Ω ↦ Real.cosh (t * (C : ℝ)) | m] ω +
              μ[(Real.sinh (t * (C : ℝ))) • V | m] ω := by
        simpa using haddω
      rw [haddω', hconst, hsmulω]
      simpa [hzeroω]
    have hmono :
        μ[fun ω ↦ Real.exp (t * Z ω) | m] ≤ᵐ[μ] μ[U | m] :=
      condExp_mono (m := m) hExp_int hU_int hpoint
    filter_upwards [hmono, hU_eq] with ω hω hωeq
    rw [hωeq] at hω
    exact hω

/-- Helper for Exercise 9.2.4: one martingale step satisfies the conditional Gaussian exponential
recursion. -/
lemma expMartingaleStepCondExpLe {M : ℕ → Ω → ℝ} (hM : Martingale M ℱ μ) (c : ℕ → NNReal)
    (hinc : ∀ n, ∀ᵐ ω ∂μ, |M (n + 1) ω - M n ω| ≤ c (n + 1)) (n : ℕ) (t : ℝ)
    (hExpMn_int : Integrable (fun ω ↦ Real.exp (t * M n ω)) μ) :
    Integrable (fun ω ↦ Real.exp (t * M (n + 1) ω)) μ ∧
      μ[fun ω ↦ Real.exp (t * M (n + 1) ω) | ℱ n] ≤ᵐ[μ]
        fun ω ↦ Real.exp (t * M n ω) *
          Real.exp ((t ^ 2 / 2) * ((c (n + 1) : ℝ) ^ 2)) := by
  let Δ : Ω → ℝ := fun ω ↦ M (n + 1) ω - M n ω
  have hΔ_int : Integrable Δ μ := (hM.integrable (n + 1)).sub (hM.integrable n)
  have hΔ_zero : μ[Δ | ℱ n] =ᵐ[μ] 0 := by
    simpa [Δ] using martingaleIncrement_condExp_eq_zero hM n
  have hΔ_mem : ∀ᵐ ω ∂μ, Δ ω ∈ Set.Icc (-(c (n + 1) : ℝ)) (c (n + 1) : ℝ) := by
    simpa [Δ] using martingaleIncrement_mem_Icc c hinc n
  have hExpΔ_int : Integrable (fun ω ↦ Real.exp (t * Δ ω)) μ :=
    integrable_exp_mul_of_mem_Icc hΔ_int.aestronglyMeasurable.aemeasurable hΔ_mem
  have hExpΔ_sm : AEStronglyMeasurable (fun ω ↦ Real.exp (t * Δ ω)) μ :=
    hExpΔ_int.aestronglyMeasurable
  have hExpΔ_bdd :
      ∀ᵐ ω ∂μ, ‖Real.exp (t * Δ ω)‖ ≤ Real.exp (|t| * (c (n + 1) : ℝ)) := by
    filter_upwards [hΔ_mem] with ω hω
    have hbound : t * Δ ω ≤ |t| * (c (n + 1) : ℝ) := by
      have habs : |Δ ω| ≤ (c (n + 1) : ℝ) := abs_le.mpr hω
      calc
        t * Δ ω ≤ |t * Δ ω| := le_abs_self _
        _ = |t| * |Δ ω| := by rw [abs_mul]
        _ ≤ |t| * (c (n + 1) : ℝ) := by gcongr
    have hexp : Real.exp (t * Δ ω) ≤ Real.exp (|t| * (c (n + 1) : ℝ)) :=
      Real.exp_le_exp.mpr hbound
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using hexp
  have hProd_int :
      Integrable (fun ω ↦ Real.exp (t * M n ω) * Real.exp (t * Δ ω)) μ :=
    hExpMn_int.mul_bdd hExpΔ_sm hExpΔ_bdd
  have hsplit :
      (fun ω ↦ Real.exp (t * M (n + 1) ω)) =
        fun ω ↦ Real.exp (t * M n ω) * Real.exp (t * Δ ω) := by
    funext ω
    dsimp [Δ]
    have hrewrite : t * M (n + 1) ω = t * M n ω + t * (M (n + 1) ω - M n ω) := by ring
    rw [hrewrite, Real.exp_add]
  have hExpMn1_int : Integrable (fun ω ↦ Real.exp (t * M (n + 1) ω)) μ := by
    simpa [hsplit] using hProd_int
  have hFactor_sm : StronglyMeasurable[ℱ n] (fun ω ↦ Real.exp (t * M n ω)) := by
    exact Real.continuous_exp.comp_stronglyMeasurable ((hM.stronglyMeasurable n).const_mul t)
  have hpull :
      μ[fun ω ↦ Real.exp (t * M n ω) * Real.exp (t * Δ ω) | ℱ n] =ᵐ[μ]
        (fun ω ↦ Real.exp (t * M n ω)) * μ[fun ω ↦ Real.exp (t * Δ ω) | ℱ n] := by
    exact condExp_mul_of_stronglyMeasurable_left hFactor_sm hProd_int hExpΔ_int
  have hΔ_cond :
      μ[fun ω ↦ Real.exp (t * Δ ω) | ℱ n] ≤ᵐ[μ] fun _ : Ω ↦ Real.cosh (t * (c (n + 1) : ℝ)) :=
    condExp_exp_mul_le_cosh_of_mem_Icc_of_condExp_eq_zero (m := ℱ n) (ℱ.le n) (c (n + 1)) t
      hΔ_int hΔ_zero hΔ_mem
  have hGaussian :
      Real.cosh (t * (c (n + 1) : ℝ)) ≤
        Real.exp ((t ^ 2 / 2) * ((c (n + 1) : ℝ) ^ 2)) := by
    convert Real.cosh_le_exp_half_sq (t * (c (n + 1) : ℝ)) using 1 <;> ring
  refine ⟨hExpMn1_int, ?_⟩
  have hcongr :
      μ[fun ω ↦ Real.exp (t * M (n + 1) ω) | ℱ n] =ᵐ[μ]
        μ[fun ω ↦ Real.exp (t * M n ω) * Real.exp (t * Δ ω) | ℱ n] := by
    apply condExp_congr_ae
    exact Filter.Eventually.of_forall fun ω ↦ by rw [hsplit]
  filter_upwards [hcongr, hpull, hΔ_cond] with ω hωcongr hωpull hωΔ
  rw [hωcongr, hωpull]
  have hfac_nonneg : 0 ≤ Real.exp (t * M n ω) := by positivity
  exact mul_le_mul_of_nonneg_left (hωΔ.trans hGaussian) hfac_nonneg

/-- Helper for Exercise 9.2.4: bounded-difference martingales have integrable exponentials and the
corresponding Gaussian mgf bound at every time. -/
lemma integrableExpMulAndMgfLeOfBoundedMartingaleIncrements {M : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hM0 : M 0 = 0) (c : ℕ → NNReal)
    (hinc : ∀ n, ∀ᵐ ω ∂μ, |M (n + 1) ω - M n ω| ≤ c (n + 1)) :
    ∀ n : ℕ,
      ∀ t : ℝ,
        Integrable (fun ω ↦ Real.exp (t * M n ω)) μ ∧
          mgf (M n) μ t ≤
            Real.exp ((t ^ 2 / 2) * ∑ k ∈ Finset.Icc 1 n, ((c k : ℝ)) ^ 2) := by
  intro n
  induction n with
  | zero =>
      intro t
      constructor
      · -- The initial value is identically zero, so the exponential moment is the constant `1`.
        simpa [hM0] using (integrable_const (1 : ℝ))
      · -- The base variance sum is empty, so the mgf bound is exact.
        simp [mgf, hM0]
  | succ n ihn =>
      intro t
      rcases ihn t with ⟨hExpMn_int, hmgfMn⟩
      rcases expMartingaleStepCondExpLe hM c hinc n t hExpMn_int with
        ⟨hExpMn1_int, hcond_step⟩
      have hright_int :
          Integrable (fun ω ↦ Real.exp (t * M n ω) *
            Real.exp ((t ^ 2 / 2) * ((c (n + 1) : ℝ) ^ 2))) μ :=
        hExpMn_int.mul_const _
      constructor
      · exact hExpMn1_int
      · -- Integrate the one-step conditional inequality and append the new variance term.
        calc
          mgf (M (n + 1)) μ t = ∫ ω, Real.exp (t * M (n + 1) ω) ∂μ := rfl
          _ = ∫ ω, μ[fun ω ↦ Real.exp (t * M (n + 1) ω) | ℱ n] ω ∂μ := by
            symm
            exact integral_condExp (ℱ.le n)
          _ ≤ ∫ ω, Real.exp (t * M n ω) *
              Real.exp ((t ^ 2 / 2) * ((c (n + 1) : ℝ) ^ 2)) ∂μ :=
            integral_mono_ae integrable_condExp hright_int hcond_step
          _ = mgf (M n) μ t * Real.exp ((t ^ 2 / 2) * ((c (n + 1) : ℝ) ^ 2)) := by
            rw [mgf, integral_mul_const]
          _ ≤ Real.exp ((t ^ 2 / 2) * ∑ k ∈ Finset.Icc 1 n, ((c k : ℝ)) ^ 2) *
              Real.exp ((t ^ 2 / 2) * ((c (n + 1) : ℝ) ^ 2)) := by
            gcongr
          _ = Real.exp
              (((t ^ 2 / 2) * ∑ k ∈ Finset.Icc 1 n, ((c k : ℝ)) ^ 2) +
                ((t ^ 2 / 2) * ((c (n + 1) : ℝ) ^ 2))) := by
            rw [← Real.exp_add]
          _ = Real.exp ((t ^ 2 / 2) * ∑ k ∈ Finset.Icc 1 (n + 1), ((c k : ℝ)) ^ 2) := by
            congr 1
            rw [Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega)]
            ring

/-- Helper for Exercise 9.2.4: combine the upper tails of `X` and `-X` into a two-sided
exponential-Markov bound for `|X|`. -/
lemma measure_abs_ge_le_exp_mul_mgf_add_mgf_neg {X : Ω → ℝ} {ε t : ℝ}
    (ht : 0 ≤ t) (hXt : Integrable (fun ω ↦ Real.exp (t * X ω)) μ)
    (hXneg_t : Integrable (fun ω ↦ Real.exp (t * (-X ω))) μ) :
    μ.real {ω | ε ≤ |X ω|} ≤ Real.exp (-t * ε) * (mgf X μ t + mgf (-X) μ t) := by
  let A : Set Ω := {ω | ε ≤ X ω}
  let B : Set Ω := {ω | ε ≤ -X ω}
  have hsub : {ω | ε ≤ |X ω|} ⊆ A ∪ B := by
    intro ω hω
    by_cases hx : 0 ≤ X ω
    · left
      simpa [A, abs_of_nonneg hx, hx] using hω
    · right
      have hx' : X ω < 0 := lt_of_not_ge hx
      simpa [B, abs_of_neg hx', hx'.le] using hω
  have hA :
      μ.real A ≤ Real.exp (-t * ε) * mgf X μ t := by
    simpa [A] using measure_ge_le_exp_mul_mgf (X := X) (μ := μ) (t := t) ε ht hXt
  have hB :
      μ.real B ≤ Real.exp (-t * ε) * mgf (-X) μ t := by
    simpa [B] using measure_ge_le_exp_mul_mgf (X := -X) (μ := μ) (t := t) ε ht hXneg_t
  calc
    μ.real {ω | ε ≤ |X ω|} ≤ μ.real (A ∪ B) := MeasureTheory.measureReal_mono hsub
    _ ≤ μ.real A + μ.real B := MeasureTheory.measureReal_union_le A B
    _ ≤ Real.exp (-t * ε) * mgf X μ t + Real.exp (-t * ε) * mgf (-X) μ t := by
      gcongr
    _ = Real.exp (-t * ε) * (mgf X μ t + mgf (-X) μ t) := by ring

-- Proof sketch: this is the source-facing mgf consequence of the owner theorem
-- `HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF`, applied to the martingale increments
-- `M (k + 1) - M k`, whose boundedness yields conditional sub-Gaussian parameters `c k ^ 2`.
/-- Clause (3) of Exercise 9.2.4: a martingale starting at `0` and with almost surely bounded
increments
has Gaussian moment-generating-function bounds. -/
theorem martingale_mgf_le_exp_half_mul_sum_sq_of_bounded_increments {M : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hM0 : M 0 = 0) (c : ℕ → NNReal)
    (hinc : ∀ n, ∀ᵐ ω ∂μ, |M (n + 1) ω - M n ω| ≤ c (n + 1)) :
    ∀ n : ℕ,
      ∀ t : ℝ,
        mgf (M n) μ t ≤
          Real.exp ((t ^ 2 / 2) * ∑ k ∈ Finset.Icc 1 n, ((c k : ℝ)) ^ 2) :=
by
  -- Route correction: instead of the unavailable `condExpKernel` route, iterate the explicit
  -- conditional-Hoeffding step proved above and then forget the auxiliary integrability output.
  intro n t
  exact (integrableExpMulAndMgfLeOfBoundedMartingaleIncrements hM hM0 c hinc n t).2

-- Proof sketch: combine the source-facing mgf bound from clause (3), or directly the owner lemma
-- `measure_sum_ge_le_of_hasCondSubgaussianMGF`, with the standard two-sided exponential-Markov
-- argument.
/-- Exercise 9.2.4 (4): Under the bounded-increment hypotheses, the martingale satisfies Azuma's
inequality. -/
theorem azuma_inequality_of_bounded_martingale_increments {M : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hM0 : M 0 = 0) (c : ℕ → NNReal)
    (hinc : ∀ n, ∀ᵐ ω ∂μ, |M (n + 1) ω - M n ω| ≤ c (n + 1)) :
    ∀ n : ℕ,
      ∀ ε : ℝ,
        0 ≤ ε →
          μ.real {ω | ε ≤ |M n ω|} ≤
            2 * Real.exp (-ε ^ 2 / (2 * ∑ k ∈ Finset.Icc 1 n, ((c k : ℝ)) ^ 2)) :=
by
  intro n ε hε
  let S : ℝ := ∑ k ∈ Finset.Icc 1 n, ((c k : ℝ)) ^ 2
  by_cases hS : S = 0
  · -- In the zero-variance branch, the right-hand side is exactly `2`, so the trivial
    -- probability bound is enough.
    calc
      μ.real {ω | ε ≤ |M n ω|} ≤ μ.real (Set.univ : Set Ω) := by
        refine MeasureTheory.measureReal_mono ?_
        intro ω _
        simp
      _ = 1 := by simp
      _ ≤ 2 := by norm_num
      _ = 2 * Real.exp (-ε ^ 2 / (2 * S)) := by simp [S, hS]
  · have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg fun k hk ↦ sq_nonneg (c k : ℝ)
    have hinc_neg : ∀ k, ∀ᵐ ω ∂μ, |(-M) (k + 1) ω - (-M) k ω| ≤ c (k + 1) := by
      intro k
      filter_upwards [hinc k] with ω hω
      have hω' : |M k ω - M (k + 1) ω| ≤ c (k + 1) := by
        simpa [abs_sub_comm] using hω
      simpa [Pi.neg_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hω'
    let t : ℝ := ε / S
    have ht : 0 ≤ t := by
      exact div_nonneg hε hS_nonneg
    have hpos :=
      integrableExpMulAndMgfLeOfBoundedMartingaleIncrements hM hM0 c hinc n t
    have hneg :=
      integrableExpMulAndMgfLeOfBoundedMartingaleIncrements (M := -M) hM.neg
        (by simpa [Pi.neg_apply, hM0]) c hinc_neg n t
    have htail :
        μ.real {ω | ε ≤ |M n ω|} ≤
          Real.exp (-t * ε) * (mgf (M n) μ t + mgf (-M n) μ t) :=
      measure_abs_ge_le_exp_mul_mgf_add_mgf_neg (X := M n) (μ := μ) ht hpos.1
        (by simpa using hneg.1)
    have hmul :
        Real.exp (-t * ε) *
            (Real.exp ((t ^ 2 / 2) * S) + Real.exp ((t ^ 2 / 2) * S)) =
          2 * Real.exp (-t * ε + (t ^ 2 / 2) * S) := by
      rw [Real.exp_add]
      ring
    have hopt : -t * ε + (t ^ 2 / 2) * S = -ε ^ 2 / (2 * S) := by
      dsimp [t]
      field_simp [hS]
      ring
    -- Apply the mgf bound to both `M n` and `-M n`, then optimize the free parameter.
    calc
      μ.real {ω | ε ≤ |M n ω|} ≤
          Real.exp (-t * ε) * (mgf (M n) μ t + mgf (-M n) μ t) := htail
      _ ≤ Real.exp (-t * ε) *
          (Real.exp ((t ^ 2 / 2) * S) + Real.exp ((t ^ 2 / 2) * S)) := by
        gcongr
        · exact hpos.2
        · simpa [S] using hneg.2
      _ = 2 * Real.exp (-t * ε + (t ^ 2 / 2) * S) := hmul
      _ = 2 * Real.exp (-ε ^ 2 / (2 * S)) := by rw [hopt]
