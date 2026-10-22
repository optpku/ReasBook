/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Assumption_12_6_1

noncomputable section

open Filter

section

variable {Point Multiplier : Type*}
variable [NormedAddCommGroup Point] [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
variable [NormedAddCommGroup Multiplier] [InnerProductSpace ℝ Multiplier]
variable [FiniteDimensional ℝ Multiplier]

-- Domain sampling for this file:
-- * primary domain: Section 12.6 second-order-correction residual coercivity in finite-dimensional
--   real inner-product spaces, i.e. the Euclidean matrix setting of the source lemma;
-- * sampled owner declarations:
--   `secondOrderCorrectionJacobianHasFullColumnRankAt`,
--   `secondOrderCorrectionUniformModelBounds`,
--   `LinearMap.injective_iff_antilipschitz`,
--   `ContinuousLinearMap.isOpen_injective`,
--   and `Submodule.starProjection`;
-- * source-facing layer: the eventual lower bound `(12.6.12)` for the stacked residual
--   `((P_k (B_k d)), A(x_k)ᵀ d)`;
-- * core/canonical layer: the Chapter 12 owner
--   `secondOrderCorrectionJacobianHasFullColumnRankAt A xStar` for full column rank and the
--   orthogonal projection owner `Submodule.starProjection`;
-- * bridge/view layer: finite-dimensional injectivity-to-antilipschitz control via
--   `LinearMap.injective_iff_antilipschitz`, plus openness of injectivity through
--   `ContinuousLinearMap.isOpen_injective`;
-- * the canonical `L²`-product owner `WithLp 2 (Point × Multiplier)` packages the stacked
--   residual norm without adding a second owner abstraction;
-- * primitive data vs derived API: `x`, `xStar`, `A`, `B`, convergence of `x k`, continuity of
--   `A` at `xStar`, full column rank of `A xStar` in the finite-dimensional Euclidean sense, and
--   the uniform nullspace-curvature bounds are
--   primitive, while the uniform lower bound for the stacked residual is derived.

/-- Helper for Chapter12 Lemma 12.6.2: a small operator-norm perturbation preserves half of a
uniform lower norm bound. -/
lemma small_operator_perturbation_preserves_uniform_lower_bound
    (S T : Multiplier →L[ℝ] Point)
    {γ0 : ℝ}
    (hγ0_pos : 0 < γ0)
    (hT : ∀ y : Multiplier, γ0 * ‖y‖ ≤ ‖T y‖)
    (hclose : ‖S - T‖ ≤ γ0 / 2) :
    ∀ y : Multiplier, (γ0 / 2) * ‖y‖ ≤ ‖S y‖ := by
  intro y
  -- The perturbation term is controlled by the operator norm of `S - T`.
  have hpert :
      ‖(S - T) y‖ ≤ (γ0 / 2) * ‖y‖ := by
    calc
      ‖(S - T) y‖ ≤ ‖S - T‖ * ‖y‖ := (S - T).le_opNorm y
      _ ≤ (γ0 / 2) * ‖y‖ := by
        gcongr
  -- Rewrite `T y` through `S y` and the perturbation, then absorb the error.
  have htri :
      ‖T y‖ ≤ ‖S y‖ + ‖(S - T) y‖ := by
    calc
      ‖T y‖ = ‖S y - (S - T) y‖ := by
        simp
      _ ≤ ‖S y‖ + ‖(S - T) y‖ := norm_sub_le _ _
  nlinarith [hT y, hpert, hγ0_pos]

/-- Helper for Chapter12 Lemma 12.6.2: the Jacobians `A (x k)` inherit one fixed lower singular
value bound from the injective limit map `A xStar` once `k` is large. -/
lemma eventually_uniform_jacobian_norm_lower_bound
    (x : ℕ → Point)
    (xStar : Point)
    (A : Point → Multiplier →L[ℝ] Point)
    (hx : secondOrderCorrectionIteratesConverge x xStar)
    (hAcont : ContinuousAt A xStar)
    (hAstar : secondOrderCorrectionJacobianHasFullColumnRankAt A xStar) :
    ∃ γ : ℝ,
      0 < γ ∧
        ∃ K : ℕ,
          ∀ ⦃k : ℕ⦄, K ≤ k → ∀ y : Multiplier, γ * ‖y‖ ≤ ‖A (x k) y‖ := by
  -- Route correction: the earlier draft stopped at injectivity; here we convert the injective
  -- limit Jacobian into an explicit lower norm bound and then keep half of it under perturbation.
  rcases (LinearMap.injective_iff_antilipschitz (A xStar : Multiplier →ₗ[ℝ] Point)).mp hAstar with
    ⟨K0, hK0_pos, hanti⟩
  let γ0 : ℝ := ((K0 : ℝ)⁻¹)
  have hγ0_pos : 0 < γ0 := by
    dsimp [γ0]
    exact inv_pos.mpr (by exact_mod_cast hK0_pos)
  have hAstar_lower : ∀ y : Multiplier, γ0 * ‖y‖ ≤ ‖A xStar y‖ := by
    intro y
    -- The anti-Lipschitz estimate at the limit point becomes a lower singular-value bound.
    simpa [γ0, dist_eq_norm, map_zero] using hanti.mul_le_dist y 0
  have hAx :
      Tendsto (fun k : ℕ ↦ A (x k)) atTop (nhds (A xStar)) :=
    hAcont.tendsto.comp hx
  have hclose :
      ∀ᶠ k in atTop, ‖A (x k) - A xStar‖ ≤ γ0 / 2 := by
    have hclose_lt :
        ∀ᶠ k in atTop, ‖A (x k) - A xStar‖ < γ0 / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using
        hAx.eventually (Metric.ball_mem_nhds (A xStar) (half_pos hγ0_pos))
    filter_upwards [hclose_lt] with k hk
    exact le_of_lt hk
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hclose
  refine ⟨γ0 / 2, half_pos hγ0_pos, ?_⟩
  refine ⟨K, ?_⟩
  intro k hk y
  exact small_operator_perturbation_preserves_uniform_lower_bound
    (S := A (x k)) (T := A xStar) hγ0_pos hAstar_lower (hK k hk) y

/-- Helper for Chapter12 Lemma 12.6.2: on the range of a uniformly injective map, the adjoint has
the same lower norm control up to the source-faithful Cauchy-Schwarz estimate. -/
lemma adjoint_lower_bound_on_range_of_antilipschitz_map
    (A : Multiplier →L[ℝ] Point)
    {γ : ℝ}
    (hγ_pos : 0 < γ)
    (hγ : ∀ y : Multiplier, γ * ‖y‖ ≤ ‖A y‖) :
    ∀ ⦃w : Point⦄, w ∈ A.range → γ * ‖w‖ ≤ ‖A.adjoint w‖ := by
  intro w hw
  obtain ⟨y, rfl⟩ := A.mem_range.mp hw
  by_cases hy0 : y = 0
  · simp [hy0]
  have hy_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  -- The lower norm bound provides the first factor needed for the Cauchy-Schwarz comparison.
  have hmul :
      γ * ‖y‖ * ‖A y‖ ≤ ‖A y‖ ^ (2 : ℕ) := by
    nlinarith [hγ y, norm_nonneg (A y), hγ_pos]
  -- The adjoint identity rewrites `‖A y‖²` into an inner product controlled by Cauchy-Schwarz.
  have hsq :
      ‖A y‖ ^ (2 : ℕ) ≤ ‖y‖ * ‖A.adjoint (A y)‖ := by
    calc
      ‖A y‖ ^ (2 : ℕ) = inner ℝ y (A.adjoint (A y)) := by
        simpa using A.apply_norm_sq_eq_inner_adjoint_right y
      _ ≤ ‖y‖ * ‖A.adjoint (A y)‖ := real_inner_le_norm _ _
  have hcompare :
      γ * ‖y‖ * ‖A y‖ ≤ ‖y‖ * ‖A.adjoint (A y)‖ :=
    hmul.trans hsq
  have hscaled :
      ‖y‖ * (γ * ‖A y‖) ≤ ‖y‖ * ‖A.adjoint (A y)‖ := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcompare
  exact le_of_mul_le_mul_left hscaled hy_pos

/-- Helper for Chapter12 Lemma 12.6.2: the adjoint controls the component orthogonal to
`ker (A†)` whenever `A` has a uniform lower norm bound. -/
lemma eventually_adjoint_controls_kernel_orthogonal_component
    (A : Multiplier →L[ℝ] Point)
    {γ : ℝ}
    (hγ_pos : 0 < γ)
    (hγ : ∀ y : Multiplier, γ * ‖y‖ ≤ ‖A y‖) :
    ∀ d : Point,
      γ * ‖d - ((A.adjoint.ker).starProjection d)‖ ≤ ‖A.adjoint d‖ := by
  -- Route correction: the missing bridge is the closed-range identity
  -- `(ker A†)ᗮ = range A`, after which the adjoint-range estimate closes the component bound.
  let Kanti : NNReal := ⟨γ⁻¹, inv_nonneg.mpr hγ_pos.le⟩
  have hKanti : ((Kanti : NNReal) : ℝ) = γ⁻¹ := rfl
  have hanti : AntilipschitzWith Kanti A := by
    refine ContinuousLinearMap.antilipschitz_of_bound A fun y ↦ ?_
    have hscaled : γ * ‖y‖ ≤ γ * (((Kanti : NNReal) : ℝ) * ‖A y‖) := by
      calc
        γ * ‖y‖ ≤ ‖A y‖ := hγ y
        _ = γ * (((Kanti : NNReal) : ℝ) * ‖A y‖) := by
          rw [hKanti]
          field_simp [hγ_pos.ne']
    exact le_of_mul_le_mul_left hscaled hγ_pos
  let K : Submodule ℝ Point := A.adjoint.ker
  intro d
  let w : Point := d - K.starProjection d
  have hw_orth : w ∈ Kᗮ := by
    simpa [K, w] using (Submodule.sub_starProjection_mem_orthogonal (K := K) d)
  have horth_eq_range : Kᗮ = A.range := by
    -- The orthogonal complement of `ker A†` is the closed range of `A`.
    simpa [K, ContinuousLinearMap.closed_range_of_antilipschitz hanti] using
      (ContinuousLinearMap.orthogonal_ker A.adjoint)
  have hw_range : w ∈ A.range := by
    simpa [horth_eq_range] using hw_orth
  have hproj_zero : A.adjoint (K.starProjection d) = 0 := by
    exact LinearMap.mem_ker.mp (by simpa [K] using K.starProjection_apply_mem d)
  have hw_adjoint : A.adjoint w = A.adjoint d := by
    simp [w, hproj_zero]
  -- Once the orthogonal component is recognized as a range vector, the range-level lower bound
  -- transfers directly to `A† d`.
  have hw_bound :
      γ * ‖w‖ ≤ ‖A.adjoint w‖ :=
    adjoint_lower_bound_on_range_of_antilipschitz_map A hγ_pos hγ hw_range
  simpa [K, w, hw_adjoint] using hw_bound

/-- Helper for Chapter12 Lemma 12.6.2: the nullspace curvature hypothesis yields a lower bound on
the projected model term along `ker ((A (x k))†)`. -/
lemma projected_curvature_lower_bound
    (x : ℕ → Point)
    (A : Point → Multiplier →L[ℝ] Point)
    (B : ℕ → Point →L[ℝ] Point)
    {mBar : ℝ}
    (hmBar_pos : 0 < mBar)
    (hCurvature :
      ∀ k : ℕ, ∀ d : Point,
        (A (x k)).adjoint d = 0 →
          mBar * ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (B k d))
    (k : ℕ) (z : Point)
    (hz : (A (x k)).adjoint z = 0) :
    mBar * ‖z‖ ≤ ‖(((A (x k)).adjoint.ker).starProjection (B k z))‖ := by
  let K : Submodule ℝ Point := (A (x k)).adjoint.ker
  have hz_mem : z ∈ K := by
    simpa [K, LinearMap.mem_ker] using hz
  -- The kernel component can be pushed through the projection using symmetry.
  have hinner :
      inner ℝ z (K.starProjection (B k z)) = inner ℝ z (B k z) := by
    rw [← K.inner_starProjection_left_eq_right z (B k z),
      K.starProjection_eq_self_iff.mpr hz_mem]
  have hcurv' :
      mBar * ‖z‖ ^ (2 : ℕ) ≤ inner ℝ z (K.starProjection (B k z)) := by
    rw [hinner]
    exact hCurvature k z hz
  by_cases hz0 : z = 0
  · simp [hz0]
  -- Cauchy-Schwarz converts the curvature inequality into a norm lower bound.
  have hproj :
      inner ℝ z (K.starProjection (B k z)) ≤ ‖z‖ * ‖K.starProjection (B k z)‖ :=
    real_inner_le_norm _ _
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  nlinarith [hcurv', hproj, hmBar_pos]

/-- Helper for Chapter12 Lemma 12.6.2: after splitting `d` into the kernel and orthogonal
components of `(A (x k))†`, the projected residual satisfies the textbook lower bound
`mBar ‖z‖ - MBar ‖w‖`. -/
lemma projected_model_residual_lower_bound
    (x : ℕ → Point)
    (A : Point → Multiplier →L[ℝ] Point)
    (B : ℕ → Point →L[ℝ] Point)
    {mBar MBar : ℝ}
    (hNorm : ∀ k : ℕ, ‖B k‖ ≤ MBar)
    (hmBar_pos : 0 < mBar)
    (hCurvature :
      ∀ k : ℕ, ∀ d : Point,
        (A (x k)).adjoint d = 0 →
          mBar * ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (B k d))
    (k : ℕ) (d : Point) :
    mBar * ‖(((A (x k)).adjoint.ker).starProjection d)‖ -
        MBar * ‖d - (((A (x k)).adjoint.ker).starProjection d)‖ ≤
      ‖(((A (x k)).adjoint.ker).starProjection (B k d))‖ := by
  let K : Submodule ℝ Point := (A (x k)).adjoint.ker
  let z : Point := K.starProjection d
  let w : Point := d - z
  have hz : (A (x k)).adjoint z = 0 := by
    have hz_mem : z ∈ K := K.starProjection_apply_mem d
    exact LinearMap.mem_ker.mp (by simpa [K, z] using hz_mem)
  have hz_lower :
      mBar * ‖z‖ ≤ ‖K.starProjection (B k z)‖ :=
    projected_curvature_lower_bound x A B hmBar_pos hCurvature k z hz
  have hw_upper :
      ‖K.starProjection (B k w)‖ ≤ MBar * ‖w‖ := by
    calc
      ‖K.starProjection (B k w)‖ ≤ ‖B k w‖ :=
        K.norm_starProjection_apply_le _
      _ ≤ ‖B k‖ * ‖w‖ := (B k).le_opNorm w
      _ ≤ MBar * ‖w‖ := by
        gcongr
        exact hNorm k
  -- The split `d = z + w` reduces the estimate to the triangle inequality.
  have hd_split : d = z + w := by
    simp [z, w]
  have hz_rewrite :
      K.starProjection (B k z) =
        K.starProjection (B k d) - K.starProjection (B k w) := by
    rw [hd_split, map_add, map_add]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have htri :
      ‖K.starProjection (B k z)‖ ≤
        ‖K.starProjection (B k d)‖ + ‖K.starProjection (B k w)‖ := by
    rw [hz_rewrite]
    exact norm_sub_le _ _
  nlinarith [hz_lower, hw_upper]

/-- Chapter12 Lemma 12.6.2: under `secondOrderCorrectionIteratesConverge x xStar`,
`ContinuousAt A xStar`, `secondOrderCorrectionJacobianHasFullColumnRankAt A xStar`, and
`secondOrderCorrectionUniformModelBounds x A B`, there exist constants `η > 0` and `K` such that
for every `k ≥ K` and every direction `d`, the stacked residual
`‖WithLp.toLp 2 (P_k (B_k d), A(x_k)ᵀ d)‖`, with
`P_k = ((A (x k)).adjoint.ker).starProjection`, is bounded below by `η * ‖d‖`,
matching `(12.6.12)` in the finite-dimensional Euclidean setting on the canonical `L²`-product
surface `WithLp 2 (Point × Multiplier)`. -/
theorem exists_eventually_uniform_lowerBound_stackedSecondOrderCorrectionResidual
    (x : ℕ → Point)
    (xStar : Point)
    (A : Point → Multiplier →L[ℝ] Point)
    (B : ℕ → Point →L[ℝ] Point)
    (hx : secondOrderCorrectionIteratesConverge x xStar)
    (hAcont : ContinuousAt A xStar)
    (hAstar : secondOrderCorrectionJacobianHasFullColumnRankAt A xStar)
    (hBounds : secondOrderCorrectionUniformModelBounds x A B) :
    ∃ η : ℝ,
      0 < η ∧
        ∃ K : ℕ,
          ∀ ⦃k : ℕ⦄ (_hk : K ≤ k) (d : Point),
            η * ‖d‖ ≤
              ‖WithLp.toLp 2
                  ((((A (x k)).adjoint.ker).starProjection (B k d),
                    (A (x k)).adjoint d))‖ := by
  -- Route correction: the proof now follows the textbook kernel/orthogonal decomposition all the
  -- way through, with the two missing analytic bridge lemmas inserted explicitly.
  rcases secondOrderCorrectionUniformModelBounds.exists_spec hBounds with
    ⟨mBar, MBar, hmBar_pos, hMBar_pos, hNorm, hCurvature⟩
  rcases eventually_uniform_jacobian_norm_lower_bound x xStar A hx hAcont hAstar with
    ⟨γ, hγ_pos, K, hγ⟩
  let α : ℝ := mBar / (2 * MBar)
  let βAdj : ℝ := γ * α / (1 + α)
  let βProj : ℝ := (mBar / 2) / (1 + α)
  let η : ℝ := min βAdj βProj
  have hα_pos : 0 < α := by
    dsimp [α]
    positivity
  have hden_pos : 0 < 1 + α := by
    positivity
  have hβAdj_pos : 0 < βAdj := by
    dsimp [βAdj]
    positivity
  have hβProj_pos : 0 < βProj := by
    dsimp [βProj]
    positivity
  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min hβAdj_pos hβProj_pos
  have hMalpha : MBar * α = mBar / 2 := by
    dsimp [α]
    field_simp [hMBar_pos.ne']
  refine ⟨η, hη_pos, K, ?_⟩
  intro k hk d
  let Ksub : Submodule ℝ Point := (A (x k)).adjoint.ker
  let z : Point := Ksub.starProjection d
  let w : Point := d - z
  let u : Point := Ksub.starProjection (B k d)
  let v : Multiplier := (A (x k)).adjoint d
  have hu_stack : ‖u‖ ≤ ‖WithLp.toLp 2 (u, v)‖ := by
    simpa using WithLp.norm_fst_le (p := 2) (x := WithLp.toLp 2 (u, v))
  have hv_stack : ‖v‖ ≤ ‖WithLp.toLp 2 (u, v)‖ := by
    simpa using WithLp.norm_snd_le (p := 2) (x := WithLp.toLp 2 (u, v))
  have hd_split : d = z + w := by
    simp [z, w]
  have hd_norm :
      ‖d‖ ≤ ‖z‖ + ‖w‖ := by
    calc
      ‖d‖ = ‖z + w‖ := by rw [hd_split]
      _ ≤ ‖z‖ + ‖w‖ := norm_add_le _ _
  have hw_adjoint :
      γ * ‖w‖ ≤ ‖v‖ := by
    simpa [Ksub, z, w, v] using
      eventually_adjoint_controls_kernel_orthogonal_component
        (A := A (x k)) hγ_pos (hγ hk) d
  have hz_projected :
      mBar * ‖z‖ - MBar * ‖w‖ ≤ ‖u‖ := by
    simpa [Ksub, z, w, u] using
      projected_model_residual_lower_bound x A B hNorm hmBar_pos hCurvature k d
  -- The two-case split matches the source proof: either the orthogonal component dominates, or
  -- the projected model term dominates.
  by_cases hcase : α * ‖z‖ ≤ ‖w‖
  · have hα_norm :
        α * ‖d‖ ≤ (1 + α) * ‖w‖ := by
      calc
        α * ‖d‖ ≤ α * (‖z‖ + ‖w‖) := by
          gcongr
        _ = α * ‖z‖ + α * ‖w‖ := by ring
        _ ≤ ‖w‖ + α * ‖w‖ := by
          gcongr
        _ = (1 + α) * ‖w‖ := by ring
    have hβAdj_norm :
        βAdj * ‖d‖ ≤ γ * ‖w‖ := by
      have hdiv : (α * ‖d‖) / (1 + α) ≤ ‖w‖ := by
        rw [div_le_iff₀ hden_pos]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hα_norm
      calc
        βAdj * ‖d‖ = γ * ((α * ‖d‖) / (1 + α)) := by
          dsimp [βAdj]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
        _ ≤ γ * ‖w‖ := by
          gcongr
    calc
      η * ‖d‖ ≤ βAdj * ‖d‖ := by
        have hη_le : η ≤ βAdj := by
          dsimp [η]
          exact min_le_left _ _
        gcongr
      _ ≤ γ * ‖w‖ := hβAdj_norm
      _ ≤ ‖v‖ := hw_adjoint
      _ ≤ ‖WithLp.toLp 2 (u, v)‖ := hv_stack
  · have hcase_lt : ‖w‖ < α * ‖z‖ := lt_of_not_ge hcase
    have hMw :
        MBar * ‖w‖ ≤ (mBar / 2) * ‖z‖ := by
      have hw_le : ‖w‖ ≤ α * ‖z‖ := le_of_lt hcase_lt
      calc
        MBar * ‖w‖ ≤ MBar * (α * ‖z‖) := by
          gcongr
        _ = (MBar * α) * ‖z‖ := by ring
        _ = (mBar / 2) * ‖z‖ := by rw [hMalpha]
    have hz_half :
        (mBar / 2) * ‖z‖ ≤ ‖u‖ := by
      nlinarith [hz_projected, hMw]
    have hz_norm :
        ‖d‖ ≤ (1 + α) * ‖z‖ := by
      have hw_le : ‖w‖ ≤ α * ‖z‖ := le_of_lt hcase_lt
      calc
        ‖d‖ ≤ ‖z‖ + ‖w‖ := hd_norm
        _ ≤ ‖z‖ + α * ‖z‖ := by
          gcongr
        _ = (1 + α) * ‖z‖ := by ring
    have hβProj_norm :
        βProj * ‖d‖ ≤ (mBar / 2) * ‖z‖ := by
      have hdiv : ‖d‖ / (1 + α) ≤ ‖z‖ := by
        rw [div_le_iff₀ hden_pos]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hz_norm
      calc
        βProj * ‖d‖ = (mBar / 2) * (‖d‖ / (1 + α)) := by
          dsimp [βProj]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
        _ ≤ (mBar / 2) * ‖z‖ := by
          gcongr
    calc
      η * ‖d‖ ≤ βProj * ‖d‖ := by
        have hη_le : η ≤ βProj := by
          dsimp [η]
          exact min_le_right _ _
        gcongr
      _ ≤ (mBar / 2) * ‖z‖ := hβProj_norm
      _ ≤ ‖u‖ := hz_half
      _ ≤ ‖WithLp.toLp 2 (u, v)‖ := hu_stack

end
