/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_58
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_62

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient WithTopConvexAnalysis

universe u

/- Lemma 7.14 lies in the Chapter 7 logarithmic barrier / concave-subgradient domain.

Mandatory domain-style sampling before refinement:
- `subdifferentialWithin` and the real-valued notation `∂[Q] f(x)` in `Chap03/Theorem_3_44`, the
  canonical constrained lower-support owner for real-valued functions;
- `barrierSubgradientClass` in `Chap07/Definition_7_58`, the chapter owner for the bounded
  constrained-subgradient conclusion;
- `logarithmicTransform` in `Chap07/Definition_7_62`, the chapter owner for `x ↦ log (ψ x)`;
- mathlib `ConcaveOn.comp` together with `strictConcaveOn_log_Ioi`, the canonical concavity API
  for composing a positive concave function with `Real.log`.

Best owner abstraction:
- source-facing: the explicit gradient witness for the constrained subgradient of
  `y ↦ -logarithmicTransform ψ y` on `interior Q`, together with the bounded barrier-subgradient
  class conclusion and concavity of `logarithmicTransform ψ`;
- core/canonical: `∂[interior Q]`, `barrierSubgradientClass`, `Seminorm.dualNorm`,
  `logarithmicTransform`, and `ConcaveOn`;
- bridge/view: the sign flip from the concave logarithmic transform to the convex function
  `y ↦ -logarithmicTransform ψ y`.

Primitive data:
- the set `Q`;
- the point-indexed seminorm family `pointNorm : interior Q → Seminorm ℝ E`;
- the witnesses `hpointNorm`;
- the function `ψ`;
- the gradient existence, positivity, concavity, and canonical dual-norm bound of `ψ` on
  `interior Q`.

Derived API:
- the constrained subgradient statement together with the witness-level dual-norm bound
  `-∇ (logarithmicTransform ψ) x ∈ ∂[interior Q] (-logarithmicTransform ψ) (x)` and
  `‖-∇ (logarithmicTransform ψ) x‖ₓ* ≤ 1`;
- the bounded barrier-subgradient-class statement for `y ↦ -logarithmicTransform ψ y`;
- the concavity of `logarithmicTransform ψ` on `interior Q`.

Source/core/bridge triage:
- source-facing: the explicit logarithmic-gradient witness and the bounded barrier-subgradient
  conclusion below;
- core/canonical: `∂[interior Q]` and `barrierSubgradientClass` applied to the negated
  logarithmic transform;
- bridge/view: the sign-flip passage from the concave logarithmic transform to the constrained
  real-valued subdifferential owner.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- Helper for Lemma 7.14: the logarithmic transform of a positive concave function is concave on
the same feasible interior set. -/
lemma logarithmic_transform_concave_on
    {Q : Set E} {ψ : E → ℝ}
    (hψ_concave : ConcaveOn ℝ (interior Q) ψ)
    (hψ_pos : ∀ x : interior Q, 0 < ψ x) :
    ConcaveOn ℝ (interior Q) (logarithmicTransform ψ) := by
  refine ⟨hψ_concave.1, ?_⟩
  intro x hx y hy a b ha hb hab
  -- First compare `ψ` at the convex combination with the affine average from concavity.
  have hψ_avg :
      a * ψ x + b * ψ y ≤ ψ (a • x + b • y) := by
    simpa [smul_eq_mul] using hψ_concave.2 hx hy ha hb hab
  have hx_pos : 0 < ψ x := hψ_pos ⟨x, hx⟩
  have hy_pos : 0 < ψ y := hψ_pos ⟨y, hy⟩
  have havg_pos : 0 < a * ψ x + b * ψ y := by
    have hax : 0 ≤ a * ψ x := mul_nonneg ha hx_pos.le
    have hby : 0 ≤ b * ψ y := mul_nonneg hb hy_pos.le
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      subst ha0 hb1
      simpa using hy_pos
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hx_pos) hby
  -- Then use monotonicity of `log` and scalar concavity of `log` on positive reals.
  calc
    logarithmicTransform ψ (a • x + b • y)
        = Real.log (ψ (a • x + b • y)) := by simp [logarithmicTransform]
    _ ≥ Real.log (a * ψ x + b * ψ y) := by
      exact Real.strictMonoOn_log.monotoneOn
        (show a * ψ x + b * ψ y ∈ Set.Ioi (0 : ℝ) from havg_pos)
        (show ψ (a • x + b • y) ∈ Set.Ioi (0 : ℝ) from by
          exact hψ_pos ⟨a • x + b • y, hψ_concave.1 hx hy ha hb hab⟩) hψ_avg
    _ ≥ a * Real.log (ψ x) + b * Real.log (ψ y) := by
      simpa [logarithmicTransform, smul_eq_mul] using
        (strictConcaveOn_log_Ioi.concaveOn.2
          (show ψ x ∈ Set.Ioi (0 : ℝ) from hx_pos)
          (show ψ y ∈ Set.Ioi (0 : ℝ) from hy_pos)
          ha hb hab)

/-- Helper for Lemma 7.14: differentiating `x ↦ log (ψ x)` multiplies the gradient of `ψ` by
`ψ x` inverse. -/
lemma has_gradient_at_logarithmic_transform
    {Q : Set E} {ψ : E → ℝ}
    (hψ_grad : ∀ x : interior Q, HasGradientAt ψ (∇ ψ x) x)
    (hψ_pos : ∀ x : interior Q, 0 < ψ x)
    (x : interior Q) :
    HasGradientAt (logarithmicTransform ψ) (((ψ x)⁻¹) • ∇ ψ x) x := by
  -- The logarithmic transform is `Real.log ∘ ψ`, so the chain rule gives the scaled gradient.
  simpa [logarithmicTransform] using
    (((hψ_grad x).hasFDerivAt).log (ne_of_gt (hψ_pos x))).hasGradientAt

/-- Helper for Lemma 7.14: concavity of the logarithmic transform yields the affine upper-support
inequality at each interior point. -/
lemma logarithmic_transform_upper_support
    {Q : Set E} {ψ : E → ℝ}
    (hψ_grad : ∀ x : interior Q, HasGradientAt ψ (∇ ψ x) x)
    (hψ_concave : ConcaveOn ℝ (interior Q) ψ)
    (hψ_pos : ∀ x : interior Q, 0 < ψ x)
    (x : interior Q) {y : E} (hy : y ∈ interior Q) :
    logarithmicTransform ψ y ≤
      logarithmicTransform ψ x + inner ℝ (∇ (logarithmicTransform ψ) x) (y - x) := by
  let seg : ℝ →ᵃ[ℝ] E := AffineMap.lineMap (x : E) y
  have hconcave := logarithmic_transform_concave_on hψ_concave hψ_pos
  have hmaps : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) (interior Q) :=
    hconcave.1.mapsTo_lineMap x.2 hy
  have hseg_concave :
      ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (logarithmicTransform ψ ∘ seg) := by
    -- Restrict the multivariate concavity statement to the segment from `x` to `y`.
    refine (hconcave.comp_affineMap seg).subset ?_ (convex_Icc (0 : ℝ) 1)
    intro t ht
    exact hmaps ht
  have hline : HasDerivAt seg (y - x) 0 := by
    simpa [seg] using (AffineMap.hasDerivAt_lineMap (a := (x : E)) (b := y) (x := (0 : ℝ)))
  have hlog0 :
      HasGradientAt (logarithmicTransform ψ) (((ψ x)⁻¹) • ∇ ψ x) (seg 0) := by
    simpa [seg] using has_gradient_at_logarithmic_transform hψ_grad hψ_pos x
  have hderiv_raw :
      HasDerivAt (logarithmicTransform ψ ∘ seg)
        (((ψ x)⁻¹) * inner ℝ (∇ ψ x) (y - x)) 0 := by
    -- Compose the logarithmic-gradient formula with the affine segment parameterization.
    simpa [seg, Function.comp, real_inner_smul_left, mul_comm, mul_left_comm, mul_assoc] using
      HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hlog0.hasFDerivAt hline
  have hslope :
      slope (logarithmicTransform ψ ∘ seg) 0 1 ≤
        ((ψ x)⁻¹) * inner ℝ (∇ ψ x) (y - x) :=
    hseg_concave.slope_le_of_hasDerivAt (by simp) (by simp) zero_lt_one hderiv_raw
  have hslope' :
      logarithmicTransform ψ y - logarithmicTransform ψ x ≤
        ((ψ x)⁻¹) * inner ℝ (∇ ψ x) (y - x) := by
    -- On `[0,1]`, the secant slope is exactly the endpoint difference.
    simpa [seg, slope, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using hslope
  have hgrad_eq :
      ∇ (logarithmicTransform ψ) x = ((ψ x)⁻¹) • ∇ ψ x :=
    (has_gradient_at_logarithmic_transform hψ_grad hψ_pos x).gradient
  have hinner_eq :
      inner ℝ (∇ (logarithmicTransform ψ) x) (y - x) =
        ((ψ x)⁻¹) * inner ℝ (∇ ψ x) (y - x) := by
    rw [hgrad_eq, real_inner_smul_left]
  linarith

/-- Helper for Lemma 7.14: the negated logarithmic gradient has pointwise dual norm at most `1`
under the source bound `‖∇ ψ x‖ₓ* ≤ ψ x`. -/
lemma dual_norm_neg_gradient_logarithmic_transform_le_one
    {Q : Set E} {ψ : E → ℝ} {pointNorm : interior Q → Seminorm ℝ E}
    (hpointNorm : ∀ x : interior Q, Seminorm.IsNorm (pointNorm x))
    (hψ_grad : ∀ x : interior Q, HasGradientAt ψ (∇ ψ x) x)
    (hψ_pos : ∀ x : interior Q, 0 < ψ x)
    (hψ_dual_bound : ∀ x : interior Q,
      let _ : Seminorm.IsNorm (pointNorm x) := hpointNorm x
      (pointNorm x).dualNorm (∇ ψ x) ≤ ψ x)
    (x : interior Q) :
    let _ : Seminorm.IsNorm (pointNorm x) := hpointNorm x
    (pointNorm x).dualNorm (-∇ (logarithmicTransform ψ) x) ≤ 1 := by
  let _ : Seminorm.IsNorm (pointNorm x) := hpointNorm x
  have hgrad_eq :
      ∇ (logarithmicTransform ψ) x = ((ψ x)⁻¹) • ∇ ψ x :=
    (has_gradient_at_logarithmic_transform hψ_grad hψ_pos x).gradient
  have hrewrite :
      -∇ (logarithmicTransform ψ) x = ((ψ x)⁻¹) • (-∇ ψ x) := by
    simpa [hgrad_eq] using (smul_neg ((ψ x)⁻¹) (∇ ψ x)).symm
  -- Use the support-function definition of `dualNorm` and bound every unit-ball pairing by `1`.
  change (pointNorm x).dualNorm (-∇ (logarithmicTransform ψ) x) ≤ 1
  rw [Seminorm.dualNorm_apply]
  refine csSup_le ?_ ?_
  · refine ⟨0, ⟨0, by simp, by simp⟩⟩
  · rintro z ⟨u, hu, rfl⟩
    have hu_le : (pointNorm x) u ≤ 1 := hu
    have hpair_base :
        inner ℝ (-∇ ψ x) u ≤ (pointNorm x).dualNorm (∇ ψ x) * (pointNorm x) u := by
      calc
        inner ℝ (-∇ ψ x) u = inner ℝ (∇ ψ x) (-u) := by simp
        _ ≤ (pointNorm x).dualNorm (∇ ψ x) * (pointNorm x) (-u) :=
          Seminorm.inner_le_dualNorm_mul (pointNorm x) (-u) (∇ ψ x)
        _ = (pointNorm x).dualNorm (∇ ψ x) * (pointNorm x) u := by
          rw [map_neg_eq_map]
    have hpair :
        inner ℝ (-∇ (logarithmicTransform ψ) x) u ≤
          (ψ x)⁻¹ * ((pointNorm x).dualNorm (∇ ψ x) * (pointNorm x) u) := by
      rw [hrewrite, real_inner_smul_left]
      exact mul_le_mul_of_nonneg_left hpair_base (inv_pos.mpr (hψ_pos x)).le
    have hscaled :
        (pointNorm x).dualNorm (∇ ψ x) * (pointNorm x) u ≤ ψ x := by
      calc
        (pointNorm x).dualNorm (∇ ψ x) * (pointNorm x) u
            ≤ ψ x * (pointNorm x) u := by
              gcongr
              exact hψ_dual_bound x
        _ ≤ ψ x * 1 := by
          gcongr
          exact (hψ_pos x).le
        _ = ψ x := by ring
    calc
      inner ℝ (-∇ (logarithmicTransform ψ) x) u
          ≤ (ψ x)⁻¹ * ((pointNorm x).dualNorm (∇ ψ x) * (pointNorm x) u) := hpair
      _ ≤ (ψ x)⁻¹ * ψ x := by
        exact mul_le_mul_of_nonneg_left hscaled (inv_pos.mpr (hψ_pos x)).le
      _ = 1 := by field_simp [ne_of_gt (hψ_pos x)]

-- Proof sketch: differentiate `x ↦ log (ψ x)` on `interior Q`, use
-- `∇ log(ψ x) = ψ(x)⁻¹ ∇ ψ(x)`, divide the assumed dual-norm bound
-- `‖∇ ψ(x)‖ₓ* ≤ ψ(x)` by the positive value `ψ(x)`, and record the resulting witness-level bound
-- `‖-∇ (logarithmicTransform ψ) x‖ₓ* ≤ 1` for the same constrained subgradient of
-- `y ↦ -logarithmicTransform ψ y`; the barrier-subgradient-class conclusion is then the derived
-- existential corollary. For concavity, compose the concave map `ψ` on
-- `interior Q` with the concave increasing function `log` on `(0, ∞)`.
/-- Lemma 7.14: if `ψ` is concave and strictly positive on `interior Q`, and its gradient has
pointwise `pointNorm`-dual norm at most `ψ x`, then at every `x ∈ interior Q` the gradient of
`x ↦ ln (ψ x)` yields, after the standard sign flip, a constrained subgradient of
`y ↦ - ln (ψ y)` over `interior Q`, written on the chapter notation
`-∇ (logarithmicTransform ψ) x ∈
∂[interior Q] (-logarithmicTransform ψ) (x)`, and this same canonical witness has
`pointNorm`-dual norm at most `1`; equivalently the negated logarithmic transform belongs to the
barrier subgradient class with bound `1`; moreover
`x ↦ ln (ψ x)` is concave on `interior Q`. -/
theorem logarithmicTransform_has_constrained_subgradient_norm_le_one_and_concaveOn
    {Q : Set E} {ψ : E → ℝ} {pointNorm : interior Q → Seminorm ℝ E}
    (hpointNorm : ∀ x : interior Q, Seminorm.IsNorm (pointNorm x))
    (hψ_grad : ∀ x : interior Q, HasGradientAt ψ (∇ ψ x) x)
    (hψ_concave : ConcaveOn ℝ (interior Q) ψ)
    (hψ_pos : ∀ x : interior Q, 0 < ψ x)
    (hψ_dual_bound : ∀ x : interior Q,
      let _ : Seminorm.IsNorm (pointNorm x) := hpointNorm x
      (pointNorm x).dualNorm (∇ ψ x) ≤ ψ x) :
    (∀ x : interior Q,
        -∇ (logarithmicTransform ψ) x ∈
          ∂[interior Q] (-logarithmicTransform ψ) (x) ∧
          (let _ : Seminorm.IsNorm (pointNorm x) := hpointNorm x
           (pointNorm x).dualNorm (-∇ (logarithmicTransform ψ) x) ≤ 1)) ∧
      (fun y ↦ -logarithmicTransform ψ y) ∈
        barrierSubgradientClass (interior Q) (interior Q) pointNorm hpointNorm 1 ∧
      ConcaveOn ℝ (interior Q) (logarithmicTransform ψ) := by
  let hconcave : ConcaveOn ℝ (interior Q) (logarithmicTransform ψ) :=
    logarithmic_transform_concave_on hψ_concave hψ_pos
  have hpointwise :
      ∀ x : interior Q,
        -∇ (logarithmicTransform ψ) x ∈
            ∂[interior Q] (-logarithmicTransform ψ) (x) ∧
          (let _ : Seminorm.IsNorm (pointNorm x) := hpointNorm x
           (pointNorm x).dualNorm (-∇ (logarithmicTransform ψ) x) ≤ 1) := by
    intro x
    constructor
    · -- Negating the affine upper-support inequality turns it into a constrained subgradient.
      rw [mem_subdifferentialWithin_iff]
      refine ⟨x.2, ?_⟩
      intro y hy
      have hup :
          logarithmicTransform ψ y ≤
            logarithmicTransform ψ x + inner ℝ (∇ (logarithmicTransform ψ) x) (y - x) :=
        logarithmic_transform_upper_support hψ_grad hψ_concave hψ_pos x hy
      have hy' :
          -logarithmicTransform ψ y ≥
            -logarithmicTransform ψ x + inner ℝ (-∇ (logarithmicTransform ψ) x) (y - x) := by
        simpa [add_comm, add_left_comm, add_assoc, inner_neg_left] using neg_le_neg hup
      exact hy'
    · -- The same explicit logarithmic gradient satisfies the normalized dual-norm bound.
      exact dual_norm_neg_gradient_logarithmic_transform_le_one
        hpointNorm hψ_grad hψ_pos hψ_dual_bound x
  refine ⟨hpointwise, ?_, hconcave⟩
  -- Package the pointwise witness into the Chapter 7 barrier-subgradient class owner.
  rw [mem_barrierSubgradientClass_iff]
  intro x
  refine ⟨-∇ (logarithmicTransform ψ) x, ?_⟩
  exact hpointwise x
