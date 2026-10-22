/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Assumption_6_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_25

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin ConvexAnalysis Gradient StrongConvex

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/- This file lies in the chapter's attained dual-objective / constrained-minimization domain.

Mandatory domain-style sampling before refinement:
- `smoothedDualObjectiveMinimand` and `smoothedDualObjective` in `Chap06/Proposition_6_25`, the
  chapter owners for the constrained `EReal` dual value and its primal slice;
- the canonical `argmin[Q₁]` owner surface for pointwise minimizer data;
- `StructuredObjectiveModel.adjointObjective` in `Chap06/Definition_6_6`, the more general
  chapter owner for the same dual-value construction;
- `StructuredObjectiveModel.adjointObjective_eq_of_isMinOn` in
  `Chap06/Text_6_1_2_Adjoint_Problem_Tractability_Caveat`, the attained-infimum bridge from the
  canonical owner to the textbook pointwise formula.

Best owner abstraction:
- source-facing: the unsmoothed dual objective of this item and its selected minimizer
  surface;
- core/canonical: the zero-smoothing specialization
  `smoothedDualObjective A Q₁ hatf hatφ 0 0` together with
  `∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)`;
- bridge/view: the vector-gradient formula obtained from the dual-valued owner through the Hilbert
  space Riesz equivalence.

Primitive data:
- the dual-valued linear map `A : E₁ →L[ℝ] StrongDual ℝ E₂`;
- the feasible set `Q₁`;
- the functions `hatf` and `hatφ`;
- a pointwise minimizer witness in the canonical argmin surface
  `∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)`.

Derived API:
- the zero-smoothing dual owner `smoothedDualObjective A Q₁ hatf hatφ 0 0`;
- its effective-domain and gradient consequences below;
- the chapter-local uniqueness, concavity, and Lipschitz-gradient statements attached to
  this item.

The previous version depended on a broken recall chain through `Definition_6_33` and used a
parallel selector wrapper that is not part of the available chapter API. This refinement keeps
only the actual zero-smoothing owners from `Proposition_6_25` together with the canonical
pointwise `argmin[Q₁]` surface.
-/

/- The source defines `\tilde φ(u) = min_{x ∈ Q₁} (...)`, selects
`x₀(u) ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)`, and sets
`φ(u) = \tilde φ(u) - \hat φ(u)`. In the zero-smoothing owner
`smoothedDualObjective A Q₁ hatf hatφ 0 0`, the source convexity of `Q₁` is already bundled by
`hhatf : hatf ∈ 𝒮^0_σ(Q₁)`, and the selector surface is recorded explicitly below. -/

section OwnerLayer

/-- The minimizer of the zero-smoothing primal slice is unique when the primal smooth part
satisfies the chapter's source-facing strong-convexity owner `hatf ∈ 𝒮^0_σ(Q₁)`. -/
-- Proof sketch: `hhatf.strongConvexOn` gives the canonical owner `StrongConvexOn Q₁ σ hatf`,
-- which already includes convexity of `Q₁`; adding the affine term `x ↦ A x u` preserves
-- `σ`-strong convexity, and a strongly convex function has at most one minimizer.
theorem dualObjectiveMinimand_minimizer_unique
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {hatf : E₁ → ℝ} {σ : ℝ}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    {u : E₂} {x y : E₁}
    (hx_mem : x ∈ Q₁) (hy_mem : y ∈ Q₁)
    (hx : IsMinOn (smoothedDualObjectiveMinimand A hatf 0 0 u) Q₁ x)
    (hy : IsMinOn (smoothedDualObjectiveMinimand A hatf 0 0 u) Q₁ y) :
    x = y := by
  -- This owner-layer file shares the chapter-wide Hilbert context used later in the file.
  let _ := (inferInstance : CompleteSpace E₂)
  -- The strong-convexity owner makes `hatf` strictly convex on `Q₁`.
  have hhatf_strict : StrictConvexOn ℝ Q₁ hatf :=
    hhatf.2.strictConvexOn hhatf.1
  -- The linear slice `x ↦ A x u` is convex on the same feasible set.
  have hlinear_convex : ConvexOn ℝ Q₁ (fun z : E₁ ↦ A z u) := by
    simpa using ((A.flip u).toLinearMap.convexOn hhatf.2.1)
  have hstrict' : StrictConvexOn ℝ Q₁ (fun z : E₁ ↦ hatf z + A z u) :=
    hhatf_strict.add_convexOn hlinear_convex
  have hstrict :
      StrictConvexOn ℝ Q₁ (smoothedDualObjectiveMinimand A hatf 0 0 u) := by
    -- Adding the affine perturbation preserves strict convexity of the primal slice.
    convert hstrict' using 1
    ext z
    simp [smoothedDualObjectiveMinimand, add_comm, add_left_comm]
  -- A strictly convex slice has at most one feasible minimizer.
  exact hstrict.eq_of_isMinOn hx hy hx_mem hy_mem

/-- If `x₀ ∈ argmin[Q₁] (...)` at a fixed dual point `u`, then every other feasible argmin of
that zero-smoothing primal slice coincides with `x₀`. -/
-- LeanSearch check for the uniqueness layer: `StrongConvexOn.strictConvexOn` confirms that this
-- file should record single-valuedness of a supplied selector, not unconditional existence.
theorem dualObjectiveMinimand_argmin_unique
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {hatf : E₁ → ℝ} {σ : ℝ}
    (hQ₁_nonempty : Q₁.Nonempty)
    (hQ₁_closed : IsClosed Q₁)
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    {u : E₂} {x₀ x : E₁}
    (hx₀ : x₀ ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)) :
    x ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u) →
      x = x₀ := by
  -- Keep the shared Hilbert context visible so this local uniqueness wrapper matches the
  -- surrounding chapter API.
  let _ := (inferInstance : CompleteSpace E₂)
  -- The closed/nonempty hypotheses belong to the textbook statement even though uniqueness only
  -- uses strong convexity of the slice.
  let _ := hQ₁_nonempty
  let _ := hQ₁_closed
  intro hx
  -- The two argmin witnesses give the same feasible minimizer on the strongly convex slice.
  rcases mem_constrainedArgmin_iff.mp hx₀ with ⟨hx₀_mem, hx₀_min⟩
  rcases mem_constrainedArgmin_iff.mp hx with ⟨hx_mem, hx_min⟩
  exact dualObjectiveMinimand_minimizer_unique A hhatf hx_mem hx₀_mem hx_min hx₀_min

/- Owner-sign note: `smoothedDualObjective A Q₁ hatf hatφ 0 0 = -hatφ + sInf (...)`, so the
zero-smoothing concavity statement is compatible with convex, not concave, input `hatφ`. The
chapter's downstream users already follow this convention. -/
/-- Concavity companion for the zero-smoothing dual objective. -/
theorem dualObjective_concave
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    {x₀ : E₂ → E₁}
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u))
    (hhatφ_convex : ConvexOn ℝ Set.univ hatφ) :
    ConcaveOn ℝ Set.univ
      (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)) := by
  -- Route correction: prove concavity from the supplied selector at the convex-combination point
  -- instead of working directly with a selector-free infimum surface.
  refine concaveOn_iff_forall_pos.mpr ?_
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  let φ : E₂ → ℝ := extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)
  let w : E₂ := a • u + b • v
  rcases mem_constrainedArgmin_iff.mp (hx₀ u) with ⟨hxu_mem, hxu_min⟩
  rcases mem_constrainedArgmin_iff.mp (hx₀ v) with ⟨hxv_mem, hxv_min⟩
  rcases mem_constrainedArgmin_iff.mp (hx₀ w) with ⟨hxw_mem, _⟩
  have hφu : φ u = -hatφ u + A (x₀ u) u + hatf (x₀ u) := by
    simpa [φ] using
      smoothedDualObjective_value_at_selected_argmin
        (A := A) (hatφ := hatφ) (d₁ := 0) (μ₁ := 0) (hx := hx₀ u)
  have hφv : φ v = -hatφ v + A (x₀ v) v + hatf (x₀ v) := by
    simpa [φ] using
      smoothedDualObjective_value_at_selected_argmin
        (A := A) (hatφ := hatφ) (d₁ := 0) (μ₁ := 0) (hx := hx₀ v)
  have hφw : φ w = -hatφ w + A (x₀ w) w + hatf (x₀ w) := by
    simpa [φ] using
      smoothedDualObjective_value_at_selected_argmin
        (A := A) (hatφ := hatφ) (d₁ := 0) (μ₁ := 0) (hx := hx₀ w)
  have hφu_le : φ u ≤ -hatφ u + A (x₀ w) u + hatf (x₀ w) := by
    -- Evaluate the attained value at `x₀ u`, then compare it with the feasible point `x₀ w`.
    rw [hφu]
    have hslice_u :
        A (x₀ u) u + hatf (x₀ u) ≤ A (x₀ w) u + hatf (x₀ w) := by
      simpa [smoothedDualObjectiveMinimand_apply] using hxu_min hxw_mem
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      add_le_add_left hslice_u (-hatφ u)
  have hφv_le : φ v ≤ -hatφ v + A (x₀ w) v + hatf (x₀ w) := by
    -- The same comparison at `v` uses the shared feasible point `x₀ w`.
    rw [hφv]
    have hslice_v :
        A (x₀ v) v + hatf (x₀ v) ≤ A (x₀ w) v + hatf (x₀ w) := by
      simpa [smoothedDualObjectiveMinimand_apply] using hxv_min hxw_mem
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      add_le_add_left hslice_v (-hatφ v)
  have hweighted :
      a * φ u + b * φ v ≤
        -(a * hatφ u + b * hatφ v) + A (x₀ w) w + hatf (x₀ w) := by
    -- Weight the two slice bounds and collapse the affine `A`-term at the convex combination.
    have hscaled_u := mul_le_mul_of_nonneg_left hφu_le ha.le
    have hscaled_v := mul_le_mul_of_nonneg_left hφv_le hb.le
    have hadd := add_le_add hscaled_u hscaled_v
    have hA :
        A (x₀ w) w = a * A (x₀ w) u + b * A (x₀ w) v := by
      dsimp [w]
      simp [map_add]
    have hrepack :
        a * (-hatφ u + A (x₀ w) u + hatf (x₀ w)) +
            b * (-hatφ v + A (x₀ w) v + hatf (x₀ w)) =
          -(a * hatφ u + b * hatφ v) + A (x₀ w) w + hatf (x₀ w) := by
      calc
        a * (-hatφ u + A (x₀ w) u + hatf (x₀ w)) +
            b * (-hatφ v + A (x₀ w) v + hatf (x₀ w)) =
          -(a * hatφ u + b * hatφ v) + (a * A (x₀ w) u + b * A (x₀ w) v) +
            (a + b) * hatf (x₀ w) := by
              ring
        _ = -(a * hatφ u + b * hatφ v) + A (x₀ w) w + hatf (x₀ w) := by
              rw [hA, hab]
              ring
    rw [hrepack] at hadd
    exact hadd
  have hhatφ_bound : hatφ w ≤ a * hatφ u + b * hatφ v :=
    hhatφ_convex.2 (by simp) (by simp) ha.le hb.le hab
  have hneg_hatφ :
      -(a * hatφ u + b * hatφ v) ≤ -hatφ w := by
    linarith
  have hfinal :
      a * φ u + b * φ v ≤ -hatφ w + A (x₀ w) w + hatf (x₀ w) := by
    linarith
  have hfinal' : a * φ u + b * φ v ≤ φ w := by
    rw [hφw]
    exact hfinal
  simpa [φ, w, smul_eq_mul] using hfinal'

/-- The canonical zero-smoothing dual objective is finite everywhere, so its effective domain is
all of `E₂`. -/
-- Proof sketch: `smoothedDualObjective A Q₁ hatf hatφ 0 0` is defined by coercing a real-valued
-- expression into `EReal`, so every point lies in its effective domain.
theorem dualObjective_dom_eq_univ
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} :
    dom (smoothedDualObjective A Q₁ hatf hatφ 0 0) = Set.univ := by
  -- Every dual point is finite because the owner is a real expression coerced into `EReal`.
  refine Set.eq_univ_iff_forall.mpr ?_
  intro u
  rw [mem_extendedRealEffectiveDomain_iff, smoothedDualObjective_apply]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

/-- Helper: evaluating the zero-smoothing dual objective at a selected feasible
argmin replaces the infimum by the attained slice value. -/
private theorem dualObjective_value_at_selected_argmin
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁}
    {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {u : E₂} {x : E₁}
    (hx : x ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)) :
    extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0) u =
      -hatφ u + A x u + hatf x := by
  -- This is exactly the attained-value bridge from Proposition 6.25 specialized to `μ₁ = 0`.
  simpa using
    smoothedDualObjective_value_at_selected_argmin A hx

/-- Helper: scaling `hatf` by `1 / σ` converts the source-facing
`σ`-strong convexity owner into the unit-modulus prox term expected by Proposition 6.25. -/
private theorem scaledHatf_strongConvexOn_one
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {σ : ℝ}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁)) :
    StrongConvexOn Q₁ 1 (fun x : E₁ ↦ (1 / σ) * hatf x) := by
  have hσ_ne : σ ≠ 0 := hhatf.1.ne'
  refine ⟨hhatf.2.1, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Scale the Jensen inequality by `1 / σ` to normalize the modulus.
  have hscaled :=
    mul_le_mul_of_nonneg_left (hhatf.2.2 hx hy ha hb hab) (one_div_nonneg.mpr hhatf.1.le)
  convert hscaled using 1
  field_simp [hσ_ne]
  simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  field_simp [hσ_ne]

/-- Helper: the Proposition 6.25 minimand with
`hatf := 0`, `d₁ := (1 / σ) • hatf`, and `μ₁ := σ` is exactly the zero-smoothing minimand. -/
private theorem scaledHatfMinimand_eq_zeroSmoothingMinimand
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {σ : ℝ}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (u : E₂) (x : E₁) :
    smoothedDualObjectiveMinimand
        A (fun _ : E₁ ↦ 0) (fun z : E₁ ↦ (1 / σ) * hatf z) σ u x =
      smoothedDualObjectiveMinimand A hatf 0 0 u x := by
  have hσ_ne : σ ≠ 0 := hhatf.1.ne'
  -- Normalize the scaled prox term `σ * ((1 / σ) * hatf x)` back to `hatf x`.
  simp only [smoothedDualObjectiveMinimand_apply, Pi.zero_apply, zero_mul, add_zero]
  calc
    A x u + σ * ((1 / σ) * hatf x) = A x u + (σ * (1 / σ)) * hatf x := by ring
    _ = A x u + hatf x := by simp [hσ_ne]

/-- Helper: the Proposition 6.25 objective specialized with the scaled prox term
coincides pointwise with the zero-smoothing dual objective. -/
private theorem scaledHatfObjective_eq_zeroSmoothingObjective
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁}
    {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {σ : ℝ}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁)) :
    smoothedDualObjective
        A Q₁ (fun _ : E₁ ↦ 0) hatφ (fun x : E₁ ↦ (1 / σ) * hatf x) σ =
      smoothedDualObjective A Q₁ hatf hatφ 0 0 := by
  funext u
  have himage :
      smoothedDualObjectiveMinimand
          A (fun _ : E₁ ↦ 0) (fun x : E₁ ↦ (1 / σ) * hatf x) σ u '' Q₁ =
      smoothedDualObjectiveMinimand A hatf 0 0 u '' Q₁ := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨x, hx, (scaledHatfMinimand_eq_zeroSmoothingMinimand
        A hhatf u x).symm⟩
    · intro hy
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨x, hx, scaledHatfMinimand_eq_zeroSmoothingMinimand
        A hhatf u x⟩
  -- Rewrite the image set once so both objective owners become syntactically identical.
  rw [smoothedDualObjective_apply, smoothedDualObjective_apply, himage]

/-- Helper: an argmin selector for the zero-smoothing minimand is also an argmin
selector for the normalized Proposition 6.25 minimand. -/
private theorem selectedArgmin_scaledHatf
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁}
    {hatf : E₁ → ℝ} {x₀ : E₂ → E₁} {σ : ℝ}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u))
    (u : E₂) :
    x₀ u ∈ argmin[Q₁]
      (smoothedDualObjectiveMinimand
        A (fun _ : E₁ ↦ 0) (fun x : E₁ ↦ (1 / σ) * hatf x) σ u) := by
  rcases mem_constrainedArgmin_iff.mp (hx₀ u) with ⟨hx_mem, hx_min⟩
  refine mem_constrainedArgmin_iff.mpr ⟨hx_mem, ?_⟩
  intro y hy
  -- Rewrite both minimand evaluations to the zero-smoothing owner and reuse the given optimality.
  suffices hmin_scaled :
      smoothedDualObjectiveMinimand
          A (fun _ : E₁ ↦ 0) (fun x : E₁ ↦ (1 / σ) * hatf x) σ u (x₀ u) ≤
        smoothedDualObjectiveMinimand
          A (fun _ : E₁ ↦ 0) (fun x : E₁ ↦ (1 / σ) * hatf x) σ u y by
    exact hmin_scaled
  rw [scaledHatfMinimand_eq_zeroSmoothingMinimand
      A hhatf u (x₀ u),
    scaledHatfMinimand_eq_zeroSmoothingMinimand
      A hhatf u y]
  exact hx_min hy

end OwnerLayer

section GradientLayer

-- LeanSearch verification for the gradient owner surface: `HasGradientWithinAt`, `gradientWithin`.

/-- Helper: on `Set.univ`, the within-set gradient notation is the global
gradient notation. -/
private theorem gradientWithin_univ_eq_gradient
    {f : E₂ → ℝ} (u : E₂) :
    gradientWithin f Set.univ u = ∇ f u := by
  -- On the whole space, `fderivWithin` and `fderiv` agree definitionally.
  simp [gradientWithin, gradient, fderivWithin_univ]

/-- Helper for Lemma 6.2.5: specializing Proposition 6.25 on `Set.univ` gives the global
gradient formula for the zero-smoothing dual objective. -/
private theorem dualObjectiveHasGradientAtCore
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {σ : ℝ}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (hhatφ_diff : Differentiable ℝ hatφ)
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u))
    (u : E₂) :
    HasGradientAt
      (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0))
      (-∇ hatφ u + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u))) u := by
  -- Route correction: specialize Proposition 6.25 on `Set.univ` and transport the normalized
  -- objective back to the zero-smoothing owner.
  have hhatφ_on : DifferentiableOn ℝ hatφ Set.univ := by
    simpa [differentiableOn_univ] using hhatφ_diff
  have hzero_convex : ConvexOn ℝ Q₁ (fun _ : E₁ ↦ (0 : ℝ)) := by
    simpa using (convexOn_const (s := Q₁) (c := (0 : ℝ)) hhatf.2.1)
  have hxScaled :
      ∀ ⦃v : E₂⦄, v ∈ Set.univ →
        x₀ v ∈ argmin[Q₁]
          (smoothedDualObjectiveMinimand
            A (fun _ : E₁ ↦ (0 : ℝ)) (fun x : E₁ ↦ (1 / σ) * hatf x) σ v) := by
    intro v hv
    simpa using selectedArgmin_scaledHatf A hhatf hx₀ v
  have hgradWithin :
      HasGradientWithinAt
        (extendedRealRealPart
          (smoothedDualObjective
            A Q₁ (fun _ : E₁ ↦ (0 : ℝ)) hatφ (fun x : E₁ ↦ (1 / σ) * hatf x) σ))
        (-gradientWithin hatφ Set.univ u + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u)))
        Set.univ u :=
    (smoothedDualObjective_argmin_unique_and_hasGradientWithinAt
      (A := A) (Q₁ := Q₁) (Q₂ := Set.univ)
      (hatf := fun _ : E₁ ↦ (0 : ℝ)) (hatφ := hatφ)
      (d₁ := fun x : E₁ ↦ (1 / σ) * hatf x) (μ₁ := σ)
      hhatf.1 hzero_convex (scaledHatf_strongConvexOn_one hhatf) hhatφ_on hxScaled).2 (by simp)
  rw [hasGradientWithinAt_univ] at hgradWithin
  have hgradAtScaled :
      HasGradientAt
        (extendedRealRealPart
          (smoothedDualObjective
            A Q₁ (fun _ : E₁ ↦ (0 : ℝ)) hatφ (fun x : E₁ ↦ (1 / σ) * hatf x) σ))
        (-∇ hatφ u + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u))) u := by
    simpa [gradientWithin_univ_eq_gradient] using hgradWithin
  have hobjective :
      extendedRealRealPart
          (smoothedDualObjective
            A Q₁ (fun _ : E₁ ↦ (0 : ℝ)) hatφ (fun x : E₁ ↦ (1 / σ) * hatf x) σ) =
        extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0) := by
    simpa [one_div] using
      congrArg extendedRealRealPart (scaledHatfObjective_eq_zeroSmoothingObjective A hhatf)
  exact hobjective ▸ hgradAtScaled

/-- Differentiability companion for the zero-smoothing dual objective. -/
theorem dualObjective_differentiable
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {σ : ℝ}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (hhatφ_diff : Differentiable ℝ hatφ)
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)) :
    Differentiable ℝ (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)) := by
  -- Pointwise gradient witnesses give global differentiability immediately.
  intro u
  exact (dualObjectiveHasGradientAtCore
    (A := A) (Q₁ := Q₁) (hatf := hatf) (hatφ := hatφ) (x₀ := x₀) (σ := σ)
    hhatf hhatφ_diff hx₀ u).differentiableAt

/- Every pointwise feasible argmin
`x ∈ argmin[Q₁] (...)` yields the gradient formula
`-\nabla \hat φ(u) + (InnerProductSpace.toDual ℝ E₂).symm (A x)` for the Chapter 6
zero-smoothing dual objective. -/
theorem dualObjective_hasGradientAt_of_mem_argmin
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {σ : ℝ}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (hhatφ_diff : Differentiable ℝ hatφ)
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u))
    {u : E₂} {x : E₁}
    (hx : x ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)) :
    HasGradientAt
      (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0))
      (-∇ hatφ u + (InnerProductSpace.toDual ℝ E₂).symm (A x)) u := by
  -- Compare the arbitrary feasible argmin with the chosen selector `x₀ u`.
  rcases mem_constrainedArgmin_iff.mp hx with ⟨hx_mem, hx_min⟩
  rcases mem_constrainedArgmin_iff.mp (hx₀ u) with ⟨hx₀_mem, hx₀_min⟩
  have hx_eq : x = x₀ u :=
    dualObjectiveMinimand_minimizer_unique A hhatf hx_mem hx₀_mem hx_min hx₀_min
  simpa [hx_eq] using
    dualObjectiveHasGradientAtCore
      (A := A) (Q₁ := Q₁) (hatf := hatf) (hatφ := hatφ) (x₀ := x₀) (σ := σ)
      hhatf hhatφ_diff hx₀ u

/-- For a selector `x₀` of the zero-smoothing primal argmin, the finite real part of the
canonical dual objective has gradient
`-\nabla \hat φ(u) + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u))` at every `u`. -/
theorem dualObjective_hasGradientAt
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {σ : ℝ}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (hhatφ_diff : Differentiable ℝ hatφ)
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u))
    (u : E₂) :
    HasGradientAt
      (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0))
      (-∇ hatφ u + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u))) u := by
  -- The public theorem is the zero-smoothing wrapper around the private specialization above.
  simpa using dualObjectiveHasGradientAtCore
    (A := A) (Q₁ := Q₁) (hatf := hatf) (hatφ := hatφ) (x₀ := x₀) (σ := σ)
    hhatf hhatφ_diff hx₀ u

/-- For a selector `x₀` of the zero-smoothing primal argmin, the chosen point is the unique
feasible minimizer at every dual point `u`. -/
theorem dualObjective_argmin_existsUnique
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {x₀ : E₂ → E₁} {σ : ℝ}
    (hQ₁_nonempty : Q₁.Nonempty)
    (hQ₁_closed : IsClosed Q₁)
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u))
    (u : E₂) :
    ∃! x : E₁, x ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u) := by
  -- The selector gives existence, and slice uniqueness upgrades it to `∃!`.
  refine ⟨x₀ u, hx₀ u, ?_⟩
  intro x hx
  exact dualObjectiveMinimand_argmin_unique A hQ₁_nonempty hQ₁_closed hhatf (hx₀ := hx₀ u) hx

/-- Gradient-formula companion at a fixed dual point `u` for a supplied selector `x₀`. -/
theorem dualObjective_gradient_eq
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {x₀ : E₂ → E₁}
    {σ : ℝ}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (hhatφ_diff : Differentiable ℝ hatφ)
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u))
    (u : E₂) :
    ∇ (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)) u =
      -∇ hatφ u + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u)) := by
  -- The pointwise `HasGradientAt` witness determines the canonical gradient.
  simpa using
    HasGradientAt.gradient
      (dualObjective_hasGradientAt
        (A := A) (Q₁ := Q₁) (hatf := hatf) (hatφ := hatφ) (x₀ := x₀) (σ := σ)
        hhatf hhatφ_diff hx₀ u)

/-- Lipschitz-gradient companion for the zero-smoothing dual objective. -/
theorem dualObjective_gradient_lipschitz
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {x₀ : E₂ → E₁}
    {σ : ℝ} {Lhatφ : NNReal}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (hhatφ_diff : Differentiable ℝ hatφ)
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u))
    (hhatφ_lipschitz : LipschitzWith Lhatφ (∇ hatφ)) :
    LipschitzWith
      (Lhatφ + Real.toNNReal ((1 / σ) * ‖A‖ ^ (2 : ℕ)))
      (∇ (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0))) := by
  -- Route correction: reuse the Chapter 6 Lipschitz theorem on `Set.univ` and then rewrite
  -- from `gradientWithin` back to the global gradient.
  have hhatφ_on : DifferentiableOn ℝ hatφ Set.univ := by
    simpa [differentiableOn_univ] using hhatφ_diff
  have hzero_convex : ConvexOn ℝ Q₁ (fun _ : E₁ ↦ (0 : ℝ)) := by
    simpa using (convexOn_const (s := Q₁) (c := (0 : ℝ)) hhatf.2.1)
  have hxScaled :
      ∀ ⦃v : E₂⦄, v ∈ Set.univ →
        x₀ v ∈ argmin[Q₁]
          (smoothedDualObjectiveMinimand
            A (fun _ : E₁ ↦ (0 : ℝ)) (fun x : E₁ ↦ (1 / σ) * hatf x) σ v) := by
    intro v hv
    simpa using selectedArgmin_scaledHatf A hhatf hx₀ v
  have hhatφ_lipschitzOn :
      LipschitzOnWith Lhatφ (fun v ↦ gradientWithin hatφ Set.univ v) Set.univ := by
    simpa [lipschitzOnWith_univ, gradientWithin_univ_eq_gradient] using hhatφ_lipschitz
  have hgradLipOn :
      LipschitzOnWith
        (Lhatφ + Real.toNNReal ((1 / σ) * ‖A‖ ^ (2 : ℕ)))
        (fun v ↦
          gradientWithin
            (extendedRealRealPart
              (smoothedDualObjective
                A Q₁ (fun _ : E₁ ↦ (0 : ℝ)) hatφ (fun x : E₁ ↦ (1 / σ) * hatf x) σ))
            Set.univ v)
        Set.univ :=
    smoothedDualObjective_gradientWithin_lipschitzOn
      (A := A) (Q₁ := Q₁) (Q₂ := Set.univ)
      (hatf := fun _ : E₁ ↦ (0 : ℝ)) (hatφ := hatφ)
      (d₁ := fun x : E₁ ↦ (1 / σ) * hatf x) (μ₁ := σ) (Lhatφ := Lhatφ)
      hhatf.1 hzero_convex (scaledHatf_strongConvexOn_one hhatf) hhatφ_on uniqueDiffOn_univ
      hxScaled hhatφ_lipschitzOn
  have hgradLip :
      LipschitzWith
        (Lhatφ + Real.toNNReal ((1 / σ) * ‖A‖ ^ (2 : ℕ)))
        (fun v ↦
          gradientWithin
            (extendedRealRealPart
              (smoothedDualObjective
                A Q₁ (fun _ : E₁ ↦ (0 : ℝ)) hatφ (fun x : E₁ ↦ (1 / σ) * hatf x) σ))
            Set.univ v) := by
    simpa [lipschitzOnWith_univ] using hgradLipOn
  have hobjective :
      extendedRealRealPart
          (smoothedDualObjective
            A Q₁ (fun _ : E₁ ↦ (0 : ℝ)) hatφ (fun x : E₁ ↦ (1 / σ) * hatf x) σ) =
        extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0) := by
    simpa [one_div] using
      congrArg extendedRealRealPart (scaledHatfObjective_eq_zeroSmoothingObjective A hhatf)
  have hgradient :
      (fun v ↦
        gradientWithin
          (extendedRealRealPart
            (smoothedDualObjective
              A Q₁ (fun _ : E₁ ↦ (0 : ℝ)) hatφ (fun x : E₁ ↦ (1 / σ) * hatf x) σ))
          Set.univ v) =
        ∇ (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)) := by
    funext v
    rw [gradientWithin_univ_eq_gradient]
    rw [hobjective]
  exact hgradient ▸ hgradLip

/-- Lemma 6.2.5 (1): if `Q₁` is nonempty and closed, if `\hat f ∈ 𝒮^0_σ(Q₁)`, if `x₀` selects
the pointwise zero-smoothing primal argmin, and if `\hat φ` is convex, differentiable, and has
Lipschitz-continuous gradient, then the zero-smoothing dual objective is concave on `E₂`. -/
theorem dualObjective_zeroSmoothing_properties
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {σ : ℝ} {Lhatφ : NNReal}
    (hQ₁_nonempty : Q₁.Nonempty)
    (hQ₁_closed : IsClosed Q₁)
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (hhatφ_convex : ConvexOn ℝ Set.univ hatφ)
    (hhatφ_diff : Differentiable ℝ hatφ)
    (hhatφ_lipschitz : LipschitzWith Lhatφ (∇ hatφ))
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)) :
    ConcaveOn ℝ Set.univ
      (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)) := by
  -- These source-level assumptions are carried by the split statement, but concavity only
  -- depends on the selector and convexity input.
  let _ := hQ₁_nonempty
  let _ := hQ₁_closed
  let _ := hhatf
  let _ := hhatφ_diff
  let _ := hhatφ_lipschitz
  -- The split textbook statement reuses the selector-based concavity companion.
  simpa using
    dualObjective_concave
      (A := A) (Q₁ := Q₁) (hatf := hatf) (hatφ := hatφ) (x₀ := x₀)
      hx₀ hhatφ_convex

/-- Lemma 6.2.5 (2): under the same hypotheses, the zero-smoothing dual objective is
differentiable on `E₂`. -/
theorem dualObjective_zeroSmoothing_properties_differentiable
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {σ : ℝ} {Lhatφ : NNReal}
    (hQ₁_nonempty : Q₁.Nonempty)
    (hQ₁_closed : IsClosed Q₁)
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (hhatφ_convex : ConvexOn ℝ Set.univ hatφ)
    (hhatφ_diff : Differentiable ℝ hatφ)
    (hhatφ_lipschitz : LipschitzWith Lhatφ (∇ hatφ))
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)) :
    Differentiable ℝ
      (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)) := by
  -- The wrapper keeps the full textbook hypothesis list, although only the differentiability
  -- route is used here.
  let _ := hQ₁_nonempty
  let _ := hQ₁_closed
  let _ := hhatφ_convex
  let _ := hhatφ_lipschitz
  -- Differentiability is the global form of the pointwise gradient theorem.
  simpa using
    dualObjective_differentiable
      (A := A) (Q₁ := Q₁) (hatf := hatf) (hatφ := hatφ) (x₀ := x₀) (σ := σ)
      hhatf hhatφ_diff hx₀

/-- Lemma 6.2.5 (3): under the same hypotheses, the gradient of the zero-smoothing dual
objective is `-\nabla \hat φ(u) + A x₀(u)`. -/
theorem dualObjective_zeroSmoothing_properties_gradient
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {σ : ℝ} {Lhatφ : NNReal}
    (hQ₁_nonempty : Q₁.Nonempty)
    (hQ₁_closed : IsClosed Q₁)
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (hhatφ_convex : ConvexOn ℝ Set.univ hatφ)
    (hhatφ_diff : Differentiable ℝ hatφ)
    (hhatφ_lipschitz : LipschitzWith Lhatφ (∇ hatφ))
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u))
    (u : E₂) :
    ∇ (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)) u =
      -∇ hatφ u + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u)) := by
  -- The split statement keeps the full source hypothesis list, while the gradient identity only
  -- uses the differentiability and selector data.
  let _ := hQ₁_nonempty
  let _ := hQ₁_closed
  let _ := hhatφ_convex
  let _ := hhatφ_lipschitz
  -- This is exactly the selector-based gradient identity at the chosen dual point.
  simpa using
    dualObjective_gradient_eq
      (A := A) (Q₁ := Q₁) (hatf := hatf) (hatφ := hatφ) (x₀ := x₀) (σ := σ)
      hhatf hhatφ_diff hx₀ u

/-- Lemma 6.2.5 (4): under the same hypotheses, the gradient of the zero-smoothing dual
objective is Lipschitz with constant `(1 / σ) * ‖A‖² + L₂(\hat φ)`. -/
theorem dualObjective_zeroSmoothing_properties_gradient_lipschitz
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {σ : ℝ} {Lhatφ : NNReal}
    (hQ₁_nonempty : Q₁.Nonempty)
    (hQ₁_closed : IsClosed Q₁)
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (hhatφ_convex : ConvexOn ℝ Set.univ hatφ)
    (hhatφ_diff : Differentiable ℝ hatφ)
    (hhatφ_lipschitz : LipschitzWith Lhatφ (∇ hatφ))
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)) :
    LipschitzWith
      (Lhatφ + Real.toNNReal ((1 / σ) * ‖A‖ ^ (2 : ℕ)))
      (∇ (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0))) := by
  -- The wrapper preserves the full textbook assumptions, although the Lipschitz step only needs
  -- the differentiability, selector, and gradient-Lipschitz inputs.
  let _ := hQ₁_nonempty
  let _ := hQ₁_closed
  let _ := hhatφ_convex
  -- The split textbook statement reuses the selector-based Lipschitz theorem directly.
  simpa using
    dualObjective_gradient_lipschitz
      (A := A) (Q₁ := Q₁) (hatf := hatf) (hatφ := hatφ) (x₀ := x₀) (σ := σ)
      hhatf hhatφ_diff hx₀ hhatφ_lipschitz

end GradientLayer

end
