/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_33
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

/- Theorem 7.1 lies in the chapter's sublinear / asphericity domain.

Sampled owner-style declarations:
- project `SatisfiesAsphericityCondition` in `Definition_7_7`
- project
  `isGreatest_pairing_image_subdifferential_zero_of_convex_posHomogeneous`
  in `Chap03/Proposition_3_19`
- project `StrongConvexOn.norm_sub_le_two_mul_lipschitzOnWith_div_of_isMinOn_of_mem`
  in `Chap03/Proposition_3_41`
- mathlib `IsMinOn`

Best owner abstraction:
- source-facing: the consequences of the Chapter 7 asphericity sandwich for a convex positively
  homogeneous function
- core/canonical: `SatisfiesAsphericityCondition`
- bridge/view: the Chapter 3 max formula over `∂f(0)` and mathlib's minimizing owner `IsMinOn`

Primitive data:
- a real normed space `E`
- a seminorm `p : Seminorm ℝ E`
- a convex function `f : E → ℝ`
- the Chapter 3 positive-homogeneity owner `IsPositivelyHomogeneousOn 1 Set.univ f`
- radii `γ₀ ≤ γ₁` encoded canonically by `SatisfiesAsphericityCondition f p γ₀ γ₁`
- for the optimization companions: a set `Q₁`, a feasible `p`-minimizer `x₀ ∈ Q₁`, and a
  feasible `f`-minimizer `xStar ∈ Q₁`

Derived API:
- the pointwise comparison between `f` and `p`
- the `γ₁`-Lipschitz estimate for `f` with respect to `p`
- the source-faithful value bounds between a norm-minimizer `x₀` and an optimal point `xStar`
- the source-faithful distance bounds between a norm-minimizer `x₀` and an optimal point `xStar`
- the sharper factor-`1` distance estimate in the inner-product-induced norm case

Source/core/bridge triage:
- source-facing: the generic consequences of the asphericity sandwich
- core/canonical: `SatisfiesAsphericityCondition`
- bridge/view: the Chapter 3 max formula and mathlib's minimizing owner `IsMinOn`

This file keeps the source-facing theorem family on the chapter's canonical asphericity owner.
The pointwise and Lipschitz consequences are organized around the existing Chapter 3
subdifferential/max-formula owner. The generic seminorm consequences remain available as auxiliary
helpers, while the optimization clauses are restated on the ambient norm, matching the source
theorem's `ℝ^n` norm formulation and its Euclidean sharpening.
-/

section AsphericityConsequences

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {p : Seminorm ℝ E} {f : E → ℝ} {γ₀ γ₁ : ℝ}

section

omit [FiniteDimensional ℝ E] in
/-- Convexity together with degree-one positive homogeneity makes `f` subadditive on the whole
space. -/
lemma subadditive_of_convex_pos_homogeneous
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f) :
    ∀ x y : E, f (x + y) ≤ f x + f y := by
  intro x y
  -- Compare the midpoint value with the average of the endpoint values.
  have hmid :
      f ((1 / 2 : ℝ) • (x + y)) ≤ (1 / 2 : ℝ) * f x + (1 / 2 : ℝ) * f y := by
    simpa [smul_add, smul_eq_mul] using
      (hf_convex.2 (by simp) (by simp)
        (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        (by norm_num : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1))
  -- Positive homogeneity rescales the midpoint back to `x + y`.
  have hhalf :
      f ((1 / 2 : ℝ) • (x + y)) = (1 / 2 : ℝ) * f (x + y) := by
    simpa [Real.rpow_one, NNReal.smul_def, smul_eq_mul] using
      (hf_hom.map_smul (show x + y ∈ Set.univ by simp) (1 / 2 : NNReal))
  nlinarith [hmid, hhalf]

/-- Hahn-Banach produces a continuous linear functional in
`dualClosedBall p 1` that attains the seminorm value at `x`. -/
lemma exists_mem_dualClosedBall_one_apply_eq
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (x : E) :
    ∃ g : StrongDual ℝ E, g ∈ dualClosedBall p 1 ∧ g x = p x := by
  have hlinear :
      ∃ gLinear : E →ₗ[ℝ] ℝ, (∀ y : E, |gLinear y| ≤ p y) ∧ gLinear x = p x := by
    let pNorm : Norm E := ⟨p⟩
    let pCore : NormedSpace.Core ℝ E := {
      norm_nonneg := fun y ↦ apply_nonneg p y
      norm_smul := fun c y ↦ by
        simpa [Real.norm_eq_abs] using map_smul_eq_mul p c y
      norm_triangle := fun y z ↦ map_add_le_add p y z
      norm_eq_zero_iff := fun y ↦ by
        constructor
        · exact Seminorm.IsNorm.eq_zero_of_map_eq_zero
        · intro hy
          change p y = 0
          rw [hy]
          exact map_zero p
    }
    letI : Norm E := pNorm
    letI : Module ℝ E := by infer_instance
    letI : FiniteDimensional ℝ E := by infer_instance
    letI : NormedAddCommGroup E := NormedAddCommGroup.ofCore pCore
    letI : NormedSpace ℝ E := NormedSpace.ofCore pCore
    -- Work in the normed-space structure defined by `p`.
    obtain ⟨g, hg_norm, hg_eval⟩ := exists_dual_vector'' ℝ x
    refine ⟨g.toLinearMap, ?_, ?_⟩
    · intro y
      have hy : ‖g y‖ ≤ ‖g‖ * ‖y‖ := g.le_opNorm y
      calc
        |g y| = ‖g y‖ := by simp
        _ ≤ ‖g‖ * ‖y‖ := hy
        _ ≤ 1 * ‖y‖ := by
          exact mul_le_mul_of_nonneg_right hg_norm (norm_nonneg y)
        _ = ‖y‖ := by ring
        _ = p y := rfl
    · simpa [pNorm] using hg_eval
  rcases hlinear with ⟨gLinear, hg_ball, hg_eval⟩
  let gStrong : StrongDual ℝ E := ⟨gLinear, LinearMap.continuous_of_finiteDimensional gLinear⟩
  refine ⟨gStrong, ?_, ?_⟩
  · rw [mem_dualClosedBall_iff]
    simpa [gStrong] using hg_ball
  · simpa [gStrong] using hg_eval

/-- A convex degree-one positively homogeneous function has a continuous
supporting functional at the origin that attains the value at a nonzero point `x`. -/
lemma exists_affineSupportAtOrigin_apply_eq_of_ne_zero
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    {x : E} (hx : x ≠ 0) :
    ∃ g : StrongDual ℝ E, (∀ y : E, f 0 + g y ≤ f y) ∧ g x = f x := by
  have hzero : f 0 = 0 := by
    simpa [Real.rpow_one, NNReal.smul_def, smul_eq_mul] using
      (hf_hom.map_smul (show (0 : E) ∈ Set.univ by simp) (0 : NNReal))
  have hsubadd := subadditive_of_convex_pos_homogeneous hf_convex hf_hom
  -- Extend the line functional `c • x ↦ c * f x` while keeping it dominated by `f`.
  have hline_zero : ∀ c : ℝ, c • x = 0 → c • f x = 0 := by
    intro c hc
    rcases smul_eq_zero.mp hc with hc0 | hx0
    · simp [hc0]
    · exact (hx hx0).elim
  let lineMap : E →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' x (f x) hline_zero
  have hneg : -f x ≤ f (-x) := by
    have hsum : 0 ≤ f x + f (-x) := by
      simpa [hzero] using hsubadd x (-x)
    linarith
  have hline_le : ∀ z : lineMap.domain, lineMap z ≤ f z := by
    intro z
    rcases Submodule.mem_span_singleton.mp z.property with ⟨c, hc⟩
    have hmem : c • x ∈ lineMap.domain := by
      exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
    have hz : z = ⟨c • x, hmem⟩ := Subtype.ext hc.symm
    have happly :
        lineMap ⟨c • x, hmem⟩ = c * f x := by
      simpa [smul_eq_mul] using
        (LinearPMap.mkSpanSingleton'_apply x (f x) hline_zero c hmem)
    by_cases hc_nonneg : 0 ≤ c
    · -- Nonnegative scalars are handled directly by positive homogeneity.
      have hhom : f (c • x) = c * f x := by
        let t : NNReal := ⟨c, hc_nonneg⟩
        simpa [t, Real.rpow_one, NNReal.smul_def, smul_eq_mul] using
          (hf_hom.map_smul (show x ∈ Set.univ by simp) t)
      calc
        lineMap z = lineMap ⟨c • x, hmem⟩ := by rw [hz]
        _ = c * f x := happly
        _ = f (c • x) := hhom.symm
        _ ≤ f z := by
          rw [hz]
    · -- Negative scalars are controlled by subadditivity at `x` and `-x`.
      have hnegc : 0 ≤ -c := by linarith
      let t : NNReal := ⟨-c, hnegc⟩
      have hhom_neg : f (c • x) = -(c * f (-x)) := by
        have ht : (t : ℝ) = -c := rfl
        have htmp0 : f (t • (-x)) = (t : ℝ) * f (-x) := by
          simpa [Real.rpow_one, NNReal.smul_def, smul_eq_mul] using
            (hf_hom.map_smul (show -x ∈ Set.univ by simp) t)
        have htmp0' : f (-((t : ℝ) • x)) = (t : ℝ) * f (-x) := by
          simpa [NNReal.smul_def, smul_neg] using htmp0
        have hsmul : c • x = -((t : ℝ) • x) := by
          rw [ht]
          simp
        calc
          f (c • x) = f (-((t : ℝ) • x)) := by
            rw [hsmul]
          _ = (t : ℝ) * f (-x) := htmp0'
          _ = (-c) * f (-x) := by rw [ht]
          _ = -(c * f (-x)) := by ring
      have hscaled : c * f x ≤ -(c * f (-x)) := by
        have := mul_le_mul_of_nonneg_left hneg hnegc
        simpa [neg_mul, mul_assoc, mul_left_comm, mul_comm] using this
      calc
        lineMap z = lineMap ⟨c • x, hmem⟩ := by rw [hz]
        _ = c * f x := happly
        _ ≤ -(c * f (-x)) := hscaled
        _ = f (c • x) := hhom_neg.symm
        _ ≤ f z := by
          rw [hz]
  obtain ⟨g, hg_ext, hg_le⟩ :=
    exists_extension_of_le_sublinear lineMap f
      (fun c hc y ↦ by
        let t : NNReal := ⟨c, hc.le⟩
        simpa [t, Real.rpow_one, NNReal.smul_def, smul_eq_mul] using
          (hf_hom.map_smul (show y ∈ Set.univ by simp) t))
      hsubadd
      hline_le
  let gStrong : StrongDual ℝ E := ⟨g, LinearMap.continuous_of_finiteDimensional g⟩
  have hg_support : ∀ y : E, f 0 + gStrong y ≤ f y := by
    intro y
    simpa [gStrong, hzero] using hg_le y
  have hx_eq : gStrong x = f x := by
    have hmem : x ∈ lineMap.domain := Submodule.mem_span_singleton_self x
    calc
      gStrong x = g x := rfl
      _ = lineMap ⟨x, hmem⟩ := hg_ext ⟨x, hmem⟩
      _ = f x := by
        simpa using LinearPMap.mkSpanSingleton'_apply_self x (f x) hline_zero hmem
  exact ⟨gStrong, hg_support, hx_eq⟩

/-- A convex degree-one positively homogeneous function has a continuous
supporting functional at the origin that attains the value at `x`. -/
lemma exists_affineSupportAtOrigin_apply_eq
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    (x : E) :
    ∃ g : StrongDual ℝ E, (∀ y : E, f 0 + g y ≤ f y) ∧ g x = f x := by
  have hzero : f 0 = 0 := by
    simpa [Real.rpow_one, NNReal.smul_def, smul_eq_mul] using
      (hf_hom.map_smul (show (0 : E) ∈ Set.univ by simp) (0 : NNReal))
  by_cases hx : x = 0
  · by_cases hsub : Subsingleton E
    · refine ⟨0, ?_, ?_⟩
      · intro y
        have hy : y = 0 := Subsingleton.elim _ _
        simp [hy, hzero]
      · simp [hx, hzero]
    · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨z, hz⟩ := exists_ne (0 : E)
      obtain ⟨g, hg_support, -⟩ :=
        exists_affineSupportAtOrigin_apply_eq_of_ne_zero hf_convex hf_hom hz
      exact ⟨g, hg_support, by simp [hx, hzero]⟩
  · exact exists_affineSupportAtOrigin_apply_eq_of_ne_zero hf_convex hf_hom hx

-- Proof sketch: apply the lower and upper dual-ball inclusions from
-- `h_asphericity` to the affine supports of the convex positively homogeneous function `f` at
-- the origin, then evaluate the resulting support inequalities at `x`.
/-- Auxiliary pointwise comparison showing that the asphericity sandwich implies
`γ₀ * p x ≤ f x ≤ γ₁ * p x` for a seminorm that is genuinely a norm. -/
theorem SatisfiesAsphericityCondition.pointwise_bounds
    [Seminorm.IsNorm p]
    (h_asphericity : SatisfiesAsphericityCondition f p γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    (x : E) :
    γ₀ * p x ≤ f x ∧ f x ≤ γ₁ * p x := by
  rcases h_asphericity with ⟨hγ₀, -, hlower, hupper⟩
  have hzero : f 0 = 0 := by
    simpa [Real.rpow_one, NNReal.smul_def, smul_eq_mul] using
      (hf_hom.map_smul (show (0 : E) ∈ Set.univ by simp) (0 : NNReal))
  obtain ⟨gLower, hgLower_ball, hgLower_x⟩ := exists_mem_dualClosedBall_one_apply_eq p x
  have hgLower_scaled : γ₀ • gLower ∈ dualClosedBall p γ₀ := by
    rw [mem_dualClosedBall_iff] at hgLower_ball ⊢
    intro y
    have hy := hgLower_ball y
    simpa [smul_eq_mul, abs_mul, abs_of_nonneg hγ₀.le] using
      mul_le_mul_of_nonneg_left hy hγ₀.le
  have hlower_x : f 0 + (γ₀ • gLower) x ≤ f x := hlower hgLower_scaled x
  have hlower_bound : γ₀ * p x ≤ f x := by
    simpa [hzero, hgLower_x, smul_eq_mul] using hlower_x
  obtain ⟨gUpper, hgUpper_support, hgUpper_x⟩ :=
    exists_affineSupportAtOrigin_apply_eq hf_convex hf_hom x
  have hgUpper_ball : gUpper ∈ dualClosedBall p γ₁ := hupper hgUpper_support
  rw [mem_dualClosedBall_iff] at hgUpper_ball
  have hupper_abs : |f x| ≤ γ₁ * p x := by
    simpa [hgUpper_x] using hgUpper_ball x
  have hupper_bound : f x ≤ γ₁ * p x := le_trans (le_abs_self (f x)) hupper_abs
  exact ⟨hlower_bound, hupper_bound⟩

-- Proof sketch: combine the upper bound from `pointwise_bounds` with convexity and positive
-- homogeneity to control the increment `f x - f y` by the seminorm of `x - y`, then symmetrize.
/-- Auxiliary Lipschitz estimate: the asphericity sandwich implies the `γ₁`-Lipschitz bound for
`f` with respect to a seminorm that is genuinely a norm. -/
theorem SatisfiesAsphericityCondition.lipschitz
    [Seminorm.IsNorm p]
    (h_asphericity : SatisfiesAsphericityCondition f p γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    (x y : E) :
    |f x - f y| ≤ γ₁ * p (x - y) := by
  -- Control each one-sided difference by the upper sandwich applied to a difference vector.
  have hsub_xy :
      f x ≤ f (x - y) + f y := by
    simpa [sub_eq_add_neg, add_assoc] using
      subadditive_of_convex_pos_homogeneous hf_convex hf_hom (x - y) y
  have hsub_yx :
      f y ≤ f (y - x) + f x := by
    simpa [sub_eq_add_neg, add_assoc] using
      subadditive_of_convex_pos_homogeneous hf_convex hf_hom (y - x) x
  have hup_xy :
      f (x - y) ≤ γ₁ * p (x - y) :=
    (SatisfiesAsphericityCondition.pointwise_bounds h_asphericity hf_convex hf_hom (x - y)).2
  have hup_yx :
      f (y - x) ≤ γ₁ * p (x - y) := by
    have hyx_eq : y - x = -(x - y) := by
      abel_nf
    have hyx :
        f (y - x) ≤ γ₁ * p (y - x) :=
      (SatisfiesAsphericityCondition.pointwise_bounds h_asphericity hf_convex hf_hom (y - x)).2
    have hp_eq : γ₁ * p (y - x) = γ₁ * p (x - y) := by
      rw [hyx_eq, map_neg_eq_map]
    exact hp_eq ▸ hyx
  have hright : f x - f y ≤ γ₁ * p (x - y) := by
    linarith
  have hleft : -(γ₁ * p (x - y)) ≤ f x - f y := by
    linarith
  exact abs_le.2 ⟨hleft, hright⟩

-- `lean_leansearch` did not surface a closer existing owner theorem for these Chapter 7
-- comparisons, so this file states the source clauses directly on the asphericity owner together
-- with the canonical minimizing surface `IsMinOn`.
-- Theorem 7.1 is exposed as an atomic family matching the source clauses `(7.1.7)` through
-- `(7.1.10)`.
/-- Pointwise norm comparison from Theorem 7.1 (1): for every `x`, the asphericity condition
yields the source comparison `(7.1.7)` given by `γ₀ * ‖x‖ ≤ f x ≤ γ₁ * ‖x‖`. -/
theorem SatisfiesAsphericityCondition.pointwise_norm_bounds
    (h_asphericity : SatisfiesAsphericityCondition f (normSeminorm ℝ E) γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    (x : E) :
    γ₀ * ‖x‖ ≤ f x ∧ f x ≤ γ₁ * ‖x‖ := by
  -- Specialize the seminorm sandwich to the ambient norm seminorm.
  simpa [coe_normSeminorm] using
    (SatisfiesAsphericityCondition.pointwise_bounds h_asphericity hf_convex hf_hom x)

/-- Norm-Lipschitz corollary: in particular, `f` is `γ₁`-Lipschitz with respect to the ambient
norm. -/
theorem SatisfiesAsphericityCondition.norm_lipschitz
    (h_asphericity : SatisfiesAsphericityCondition f (normSeminorm ℝ E) γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    (x y : E) :
    |f x - f y| ≤ γ₁ * ‖x - y‖ := by
  -- This is the seminorm Lipschitz bound specialized to `normSeminorm`.
  simpa [coe_normSeminorm] using
    (SatisfiesAsphericityCondition.lipschitz h_asphericity hf_convex hf_hom x y)

/-- Optimal value chain from Theorem 7.1 (2): for any scalar `α > 0` satisfying the source
premise `(7.1.8)` written as `α * f x₀ ≤ γ₀ * ‖x₀‖`, the point `xStar` realizing the textbook
value `f*` yields the full source chain. -/
theorem SatisfiesAsphericityCondition.optimal_value_chain
    (h_asphericity : SatisfiesAsphericityCondition f (normSeminorm ℝ E) γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    {Q₁ : Set E} {x₀ xStar : E} {α : ℝ}
    (_hα_pos : 0 < α)
    (hx₀_mem : x₀ ∈ Q₁)
    (hx₀_min : IsMinOn (fun x ↦ ‖x‖) Q₁ x₀)
    (hxStar_mem : xStar ∈ Q₁)
    (hxStar_min : IsMinOn f Q₁ xStar)
    (hα_le : α * f x₀ ≤ γ₀ * ‖x₀‖) :
    List.IsChain (· ≤ ·)
      [α * f x₀, γ₀ * ‖x₀‖, f xStar, f x₀, γ₁ * ‖x₀‖] := by
  have hγ₀ : 0 < γ₀ := h_asphericity.1
  -- Compare the norm minimizer `x₀` with the optimizer `xStar` through the lower sandwich.
  have hnorm_min : ‖x₀‖ ≤ ‖xStar‖ := (isMinOn_iff.mp hx₀_min) xStar hxStar_mem
  have hpointwise :
      γ₀ * ‖xStar‖ ≤ f xStar :=
    (SatisfiesAsphericityCondition.pointwise_norm_bounds h_asphericity hf_convex hf_hom xStar).1
  have hlower :
      γ₀ * ‖x₀‖ ≤ f xStar := by
    nlinarith [hγ₀, hnorm_min, hpointwise]
  -- The optimizer comparison and upper sandwich provide the final two links.
  have hfxStar_le : f xStar ≤ f x₀ := (isMinOn_iff.mp hxStar_min) x₀ hx₀_mem
  have hfx₀_le :
      f x₀ ≤ γ₁ * ‖x₀‖ :=
    (SatisfiesAsphericityCondition.pointwise_norm_bounds h_asphericity hf_convex hf_hom x₀).2
  -- The source chain is exactly the conjunction of the four adjacent inequalities.
  simpa [List.isChain_cons_cons, List.isChain_pair] using
    ⟨hα_le, hlower, hfxStar_le, hfx₀_le⟩

/-- Helper for Theorem 7.1 (7.1.8): the lower middle comparison in the source chain, with
`f xStar` realizing `f*`. -/
theorem SatisfiesAsphericityCondition.optimal_value_lower_bound
    (h_asphericity : SatisfiesAsphericityCondition f (normSeminorm ℝ E) γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    {Q₁ : Set E} {x₀ xStar : E}
    (hx₀_mem : x₀ ∈ Q₁)
    (hx₀_min : IsMinOn (fun x ↦ ‖x‖) Q₁ x₀)
    (hxStar_mem : xStar ∈ Q₁)
    (hxStar_min : IsMinOn f Q₁ xStar) :
    γ₀ * ‖x₀‖ ≤ f xStar := by
  have hγ₀ : 0 < γ₀ := h_asphericity.1
  have hx₀_self : ‖x₀‖ ≤ ‖x₀‖ := (isMinOn_iff.mp hx₀_min) x₀ hx₀_mem
  have hnorm_min : ‖x₀‖ ≤ ‖xStar‖ := (isMinOn_iff.mp hx₀_min) xStar hxStar_mem
  have hpointwise :
      γ₀ * ‖xStar‖ ≤ f xStar :=
    (SatisfiesAsphericityCondition.pointwise_norm_bounds h_asphericity hf_convex hf_hom xStar).1
  have hxStar_self : f xStar ≤ f xStar := (isMinOn_iff.mp hxStar_min) xStar hxStar_mem
  -- Compare the minimizing norm at `x₀` with the lower pointwise bound at the optimizer.
  nlinarith [hγ₀, hnorm_min, hpointwise, hx₀_self, hxStar_self]

/-- Helper for Theorem 7.1 (7.1.8): the upper middle comparison in the source chain, with
`f xStar` realizing `f*`. -/
theorem SatisfiesAsphericityCondition.optimal_value_upper_bound
    (h_asphericity : SatisfiesAsphericityCondition f (normSeminorm ℝ E) γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    {Q₁ : Set E} {x₀ xStar : E}
    (hx₀_mem : x₀ ∈ Q₁)
    (hxStar_mem : xStar ∈ Q₁)
    (hxStar_min : IsMinOn f Q₁ xStar) :
    f xStar ≤ f x₀ ∧ f x₀ ≤ γ₁ * ‖x₀‖ := by
  have hxStar_self : f xStar ≤ f xStar := (isMinOn_iff.mp hxStar_min) xStar hxStar_mem
  have hmin : f xStar ≤ f x₀ := (isMinOn_iff.mp hxStar_min) x₀ hx₀_mem
  have hupper :
      f x₀ ≤ γ₁ * ‖x₀‖ :=
    (SatisfiesAsphericityCondition.pointwise_norm_bounds h_asphericity hf_convex hf_hom x₀).2
  -- The optimizer minimizes `f`, and the upper half of the sandwich controls `f x₀`.
  exact ⟨hxStar_self.trans hmin, hupper⟩

-- Proof sketch: take the upper half of `pointwise_bounds` at the chosen point `x`.
/-- Auxiliary upper bound: the upper half of the asphericity sandwich gives
`f x ≤ γ₁ * p x` for a seminorm that is genuinely a norm. -/
theorem SatisfiesAsphericityCondition.pointwise_upper_bound
    [Seminorm.IsNorm p]
    (h_asphericity : SatisfiesAsphericityCondition f p γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    (x : E) :
    f x ≤ γ₁ * p x := by
  -- This is the upper half of the already established sandwich.
  exact (SatisfiesAsphericityCondition.pointwise_bounds h_asphericity hf_convex hf_hom x).2

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Theorem 7.1: a norm minimizer on `Q` lies within `2 * ‖x‖` of every feasible
point `x`. -/
lemma norm_sub_le_two_mul_norm_of_isMinOn_norm
    {Q : Set E} {x₀ x : E}
    (hx₀_min : IsMinOn (fun z ↦ ‖z‖) Q x₀)
    (hx : x ∈ Q) :
    ‖x₀ - x‖ ≤ 2 * ‖x‖ := by
  -- The norm minimizer is no farther from the origin than any feasible point.
  have hmin : ‖x₀‖ ≤ ‖x‖ := (isMinOn_iff.mp hx₀_min) x hx
  -- Combine the triangle inequality with the minimizing property to obtain the factor-`2` bound.
  calc
    ‖x₀ - x‖ ≤ ‖x₀‖ + ‖x‖ := by
      simpa [sub_eq_add_neg] using norm_add_le x₀ (-x)
    _ ≤ ‖x‖ + ‖x‖ := add_le_add hmin le_rfl
    _ = 2 * ‖x‖ := by ring

/-- Distance chain from Theorem 7.1 (3): the source distance estimate `(7.1.9)` as the full
comparison chain between `‖x₀ - xStar‖`, the optimal value term, and the comparison-point term. -/
theorem SatisfiesAsphericityCondition.optimal_solution_distance
    (h_asphericity : SatisfiesAsphericityCondition f (normSeminorm ℝ E) γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    {Q₁ : Set E} {x₀ xStar : E}
    (hx₀_mem : x₀ ∈ Q₁)
    (hx₀_min : IsMinOn (fun x ↦ ‖x‖) Q₁ x₀)
    (hxStar_mem : xStar ∈ Q₁)
    (hxStar_min : IsMinOn f Q₁ xStar) :
    List.IsChain (· ≤ ·)
      [‖x₀ - xStar‖, (2 / γ₀) * f xStar, (2 / γ₀) * f x₀] := by
  have hγ₀ : 0 < γ₀ := h_asphericity.1
  -- First normalize the geometry using the norm-minimality of `x₀`.
  have hdist :
      ‖x₀ - xStar‖ ≤ 2 * ‖xStar‖ :=
    norm_sub_le_two_mul_norm_of_isMinOn_norm hx₀_min hxStar_mem
  have hpointwise :
      γ₀ * ‖xStar‖ ≤ f xStar :=
    (SatisfiesAsphericityCondition.pointwise_norm_bounds h_asphericity hf_convex hf_hom xStar).1
  have hnorm_le :
      ‖xStar‖ ≤ f xStar / γ₀ := by
    -- Move the lower sandwich across the positive scalar `γ₀`.
    rw [le_div_iff₀ hγ₀]
    simpa [mul_comm] using hpointwise
  have hdouble_le :
      2 * ‖xStar‖ ≤ (2 / γ₀) * f xStar := by
    -- Scale the norm estimate by `2` and normalize the right-hand side.
    have hmul :=
      mul_le_mul_of_nonneg_left hnorm_le (show 0 ≤ (2 : ℝ) by norm_num)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hscaled :
      ‖x₀ - xStar‖ ≤ (2 / γ₀) * f xStar := by
    -- Combine the geometric bound with the scaled lower pointwise estimate.
    exact le_trans hdist hdouble_le
  -- Then scale the optimizer inequality by the positive factor `2 / γ₀`.
  have hmin_value : f xStar ≤ f x₀ := (isMinOn_iff.mp hxStar_min) x₀ hx₀_mem
  have hscaled_min : (2 / γ₀) * f xStar ≤ (2 / γ₀) * f x₀ := by
    exact mul_le_mul_of_nonneg_left hmin_value (by positivity)
  -- The distance statement is the 3-term chain formed by these two adjacent inequalities.
  simpa [List.isChain_cons_cons, List.isChain_pair] using
    ⟨hscaled, hscaled_min⟩

end

end AsphericityConsequences

section InnerProductCase

variable {E : Type u} [NormedAddCommGroup E]
variable {f : E → ℝ} {γ₀ γ₁ : ℝ}

section

/-- Minimizing `‖x‖` on `Q` is exactly projecting the origin onto `Q`. -/
lemma isProjectionPointOn_zero_of_isMinOn_norm {F : Type u} [NormedAddCommGroup F]
    {Q : Set F} {x₀ : F}
    (hx₀_mem : x₀ ∈ Q) (hx₀_min : IsMinOn (fun x ↦ ‖x‖) Q x₀) :
    IsProjectionPointOn Q (0 : F) x₀ := by
  -- Rewrite the minimizing problem into the distance-to-origin form expected by the projection
  -- owner.
  refine (IsProjectionPointOn.iff_isMinOn).2 ?_
  simpa using ⟨hx₀_mem, hx₀_min⟩

/-- In the Euclidean case, a projection of the origin onto a convex set
is no farther from any feasible point than that feasible point is from the origin. -/
lemma norm_sub_le_norm_of_isProjectionPointOn_zero {F : Type u}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {Q : Set F} (hQ_convex : Convex ℝ Q) {x₀ x : F}
    (hproj : IsProjectionPointOn Q (0 : F) x₀) (hx : x ∈ Q) :
    ‖x₀ - x‖ ≤ ‖x‖ := by
  -- Apply the Pythagorean inequality at the origin and discard the nonnegative projection term.
  have hpyth :=
    IsProjectionPointOn.pythagorean_ineq hQ_convex hproj hx
  have hsq : ‖x₀ - x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    calc
      ‖x₀ - x‖ ^ 2 = ‖x - x₀‖ ^ 2 := by rw [norm_sub_rev]
      _ ≤ ‖x - x₀‖ ^ 2 + ‖x₀ - 0‖ ^ 2 := by
        nlinarith [sq_nonneg ‖x₀ - 0‖]
      _ ≤ ‖x - 0‖ ^ 2 := hpyth
      _ = ‖x‖ ^ 2 := by simp
  nlinarith [hsq, norm_nonneg (x₀ - x), norm_nonneg x]

/-- Theorem 7.1 (4): specializing the global convex-set setup of problem `(7.1.1)`, the
Euclidean norm case sharpens the source distance estimate `(7.1.10)` to the factor-`1 / γ₀`
comparison chain. -/
theorem SatisfiesAsphericityCondition.optimal_solution_distance_of_inner_product
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (h_asphericity : SatisfiesAsphericityCondition f (normSeminorm ℝ E) γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    {Q₁ : Set E} {x₀ xStar : E}
    (hQ₁_convex : Convex ℝ Q₁)
    (hx₀_mem : x₀ ∈ Q₁)
    (hx₀_min : IsMinOn (fun x ↦ ‖x‖) Q₁ x₀)
    (hxStar_mem : xStar ∈ Q₁)
    (hxStar_min : IsMinOn f Q₁ xStar) :
    List.IsChain (· ≤ ·)
      [‖x₀ - xStar‖, (1 / γ₀) * f xStar, (1 / γ₀) * f x₀] := by
  -- Route correction: use the existing projection lemmas directly instead of introducing a
  -- separate `Convex` transport theorem for the Euclidean API boundary.
  have hγ₀ : 0 < γ₀ := h_asphericity.1
  -- Convert norm minimality at `x₀` into the Euclidean projection geometry of the origin.
  have hproj : IsProjectionPointOn Q₁ (0 : E) x₀ :=
    isProjectionPointOn_zero_of_isMinOn_norm hx₀_mem hx₀_min
  -- The Euclidean projection inequality sharpens the generic factor-`2` geometric estimate.
  have hdist : ‖x₀ - xStar‖ ≤ ‖xStar‖ :=
    norm_sub_le_norm_of_isProjectionPointOn_zero hQ₁_convex hproj hxStar_mem
  have hpointwise :
      γ₀ * ‖xStar‖ ≤ f xStar :=
    (SatisfiesAsphericityCondition.pointwise_norm_bounds h_asphericity hf_convex hf_hom xStar).1
  have hnorm_le : ‖xStar‖ ≤ f xStar / γ₀ := by
    -- Move the lower sandwich across the positive scalar `γ₀`.
    rw [le_div_iff₀ hγ₀]
    simpa [mul_comm] using hpointwise
  have hscaled : ‖x₀ - xStar‖ ≤ (1 / γ₀) * f xStar := by
    -- Combine the Euclidean geometric bound with the lower pointwise sandwich at the optimizer.
    have hbound : ‖x₀ - xStar‖ ≤ f xStar / γ₀ := le_trans hdist hnorm_le
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbound
  have hscaled' : ‖x₀ - xStar‖ ≤ γ₀⁻¹ * f xStar := by
    simpa [one_div] using hscaled
  have hmin_value : f xStar ≤ f x₀ := (isMinOn_iff.mp hxStar_min) x₀ hx₀_mem
  have hscaled_min : (1 / γ₀) * f xStar ≤ (1 / γ₀) * f x₀ := by
    -- Scale the optimality inequality by the nonnegative factor `1 / γ₀`.
    exact mul_le_mul_of_nonneg_left hmin_value (by positivity)
  have hscaled_min' : γ₀⁻¹ * f xStar ≤ γ₀⁻¹ * f x₀ := by
    simpa [one_div] using hscaled_min
  -- The source inequality `(7.1.10)` is the resulting 3-term comparison chain.
  simpa [List.isChain_cons_cons, List.isChain_pair, one_div] using
    ⟨hscaled', hscaled_min'⟩

end

end InnerProductCase

end
