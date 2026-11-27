/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12.SingularSystem
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_6.EstimationError
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Exercise 7.12: verify equation (7.48)

For TSVD, the source condition `fTrue = K.adjoint z` gives a squared bias bound
`α * ‖z‖ ^ 2`, and the noise amplification estimate gives `σ ^ 2 / α` when
`E ‖η‖ ^ 2 ≤ σ ^ 2`. Choosing `α = σ / ‖z‖` balances these terms and gives
`E ‖e_α‖ ^ 2 ≤ ‖f_{Null(K)}‖ ^ 2 + 2 * σ * ‖z‖`.

The noise bound is stated explicitly for the chosen data-space norm: `σ` here
bounds total root mean square noise, rather than each unnormalized coordinate.
-/

public section

noncomputable section

open scoped BigOperators Topology
open Filter MeasureTheory

namespace TsvdEstimation

universe u v

variable {H : Type u} {F : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace H] [CompleteSpace F] in
private lemma norm_sq_of_hasSum_le {ι : Type*} {v : ι → H} {u : ι → F}
    (hv : Orthonormal ℝ v) (hu : Orthonormal ℝ u) (a : ι → ℝ) (z : F)
    {C : ℝ} (hC : 0 ≤ C) (hcoeff : ∀ j, a j ^ 2 ≤ C * (inner ℝ (u j) z) ^ 2)
    {x : H} (hsum : HasSum (fun j ↦ a j • v j) x) : ‖x‖ ^ 2 ≤ C * ‖z‖ ^ 2 := by
  have hfinite : ∀ s : Finset ι, ‖∑ j ∈ s, a j • v j‖ ^ 2 ≤ C * ‖z‖ ^ 2 := by
    intro s
    calc
      _ = ∑ j ∈ s, a j ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, hv.inner_sum]
        simp [pow_two]
      _ ≤ ∑ j ∈ s, C * (inner ℝ (u j) z) ^ 2 := Finset.sum_le_sum (fun j _ ↦ hcoeff j)
      _ = C * ∑ j ∈ s, (inner ℝ (u j) z) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ C * ‖z‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hC
        simpa only [Real.norm_eq_abs, sq_abs] using hu.sum_inner_products_le z (s := s)
  exact le_of_tendsto (hsum.norm.pow 2) (Filter.Eventually.of_forall hfinite)

/-- TSVD amplification is bounded by the inverse cutoff in squared norm. -/
private lemma tsvd_noise_sq {K : H →L[ℝ] F} (S : ContinuousLinearMap.SingularSystem K)
    {α : ℝ} (hα : 0 < α) {R : F →L[ℝ] H}
    (hR : S.HasFilterRepresentation (SpectralFilter.tsvd α) R) (g : F) :
    ‖R g‖ ^ 2 ≤ ‖g‖ ^ 2 / α := by
  have hv : Orthonormal ℝ (fun j ↦ (S.rightBasis j : H)) :=
    S.rightBasis.orthonormal.comp_linearIsometry K.kerᗮ.subtypeₗᵢ
  have hu : Orthonormal ℝ (fun j ↦ (S.leftBasis j : F)) :=
    S.leftBasis.orthonormal.comp_linearIsometry K.range.topologicalClosure.subtypeₗᵢ
  have hc : ∀ j : S.Index,
      ((SpectralFilter.tsvd α (S.singularValue j ^ 2) / S.singularValue j) *
        inner ℝ (S.leftBasis j : F) g) ^ 2 ≤ (1 / α) * (inner ℝ (S.leftBasis j : F) g) ^ 2 := by
    intro j
    have hs := S.singularValue_pos j
    by_cases hcut : α ≤ S.singularValue j ^ 2
    · simp only [SpectralFilter.tsvd, if_pos hcut, mul_pow, div_pow, one_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact one_div_le_one_div_of_le hα hcut
    · simp [SpectralFilter.tsvd, hcut]
      positivity
  simpa only [one_div_mul_eq_div] using
    norm_sq_of_hasSum_le hv hu _ g (by positivity : 0 ≤ 1 / α) hc (hR g)

/-- The source condition turns the TSVD bias into a bounded singular-system multiplier. -/
private lemma tsvd_source_bias_sq {K : H →L[ℝ] F} (S : ContinuousLinearMap.SingularSystem K)
    {α : ℝ} (hα : 0 < α) {R : F →L[ℝ] H}
    (hR : S.HasFilterRepresentation (SpectralFilter.tsvd α) R) (z : F) :
    ‖R (K (K.adjoint z)) - K.adjoint z‖ ^ 2 ≤ α * ‖z‖ ^ 2 := by
  have hmem : K.adjoint z ∈ K.kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    change K y = 0 at hy
    rw [K.adjoint_inner_right, hy]
    simp
  let f : K.kerᗮ := ⟨K.adjoint z, hmem⟩
  have hcoeff (j : S.Index) : S.rightBasis.repr f j =
      S.singularValue j * inner ℝ (S.leftBasis j : F) z := by
    rw [HilbertBasis.repr_apply_apply]
    change inner ℝ (S.rightBasis j : H) (K.adjoint z) = _
    rw [K.adjoint_inner_right, S.map_right, real_inner_smul_left]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
  have hmapcoeff (j : S.Index) : inner ℝ (S.leftBasis j : F) (K (K.adjoint z)) =
      S.singularValue j ^ 2 * inner ℝ (S.leftBasis j : F) z := by
    rw [← K.adjoint_inner_left, S.adjoint_map_left, real_inner_smul_left]
    have := hcoeff j
    rw [HilbertBasis.repr_apply_apply] at this
    change inner ℝ (S.rightBasis j : H) (K.adjoint z) = _ at this
    rw [this]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    ring
  have hsf : HasSum (fun j ↦ S.rightBasis.repr f j • (S.rightBasis j : H)) (K.adjoint z) := by
    simpa using (S.rightBasis.hasSum_repr f).mapL K.kerᗮ.subtypeL
  let a : S.Index → ℝ := fun j ↦
    (SpectralFilter.tsvd α (S.singularValue j ^ 2) - 1) * S.singularValue j *
      inner ℝ (S.leftBasis j : F) z
  have hsum : HasSum (fun j ↦ a j • (S.rightBasis j : H))
      (R (K (K.adjoint z)) - K.adjoint z) := by
    refine HasSum.congr_fun ((hR _).sub hsf) ?_
    intro j
    rw [S.filterSeries_apply, ← sub_smul, hmapcoeff, hcoeff]
    congr 1
    dsimp [a]
    field_simp [(S.singularValue_pos j).ne']
  have ha : ∀ j, a j ^ 2 ≤ α * (inner ℝ (S.leftBasis j : F) z) ^ 2 := by
    intro j
    dsimp [a]
    by_cases hcut : α ≤ S.singularValue j ^ 2
    · simp [SpectralFilter.tsvd, hcut]
      positivity
    · simp only [SpectralFilter.tsvd, if_neg hcut]
      calc
        _ = S.singularValue j ^ 2 * (inner ℝ (S.leftBasis j : F) z) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_of_not_ge hcut) (sq_nonneg _)
  exact norm_sq_of_hasSum_le
    (S.rightBasis.orthonormal.comp_linearIsometry K.kerᗮ.subtypeₗᵢ)
    (S.leftBasis.orthonormal.comp_linearIsometry K.range.topologicalClosure.subtypeₗᵢ)
    a z hα.le ha hsum

/-- Zero-mean noise removes the cross term in the expected squared estimation error. -/
private lemma expected_error_eq_bias_add_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : H →L[ℝ] F) (R : F →L[ℝ] H)
    (fTrue : H) {η : Ω → F} (hη : MemLp η 2 μ) (hmean : ∫ ω, η ω ∂μ = 0) :
    FilterRegularization.expectedSqEstimationError μ R K fTrue η =
      ‖R (K fTrue) - fTrue‖ ^ 2 + ∫ ω, ‖R (η ω)‖ ^ 2 ∂μ := by
  let b := R (K fTrue) - fTrue
  have hLp : MemLp (fun ω ↦ R (η ω)) 2 μ := hη.continuousLinearMap_comp R
  have hi := hLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hsq := hLp.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hcross : Integrable (fun ω ↦ 2 * inner ℝ b (R (η ω))) μ :=
    (hi.const_inner b).const_mul 2
  have hzero : ∫ ω, 2 * inner ℝ b (R (η ω)) ∂μ = 0 := by
    rw [integral_const_mul, integral_inner hi, R.integral_comp_comm
      (hη.integrable (by norm_num : (1 : ENNReal) ≤ 2)), hmean]
    simp
  have heq : (fun ω ↦ ‖FilterRegularization.estimationError R K fTrue (η ω)‖ ^ 2) =
      fun ω ↦ (‖b‖ ^ 2 + 2 * inner ℝ b (R (η ω))) + ‖R (η ω)‖ ^ 2 := by
    funext ω
    rw [FilterRegularization.estimationError_def, map_add]
    have h : R (K fTrue) + R (η ω) - fTrue = b + R (η ω) := by dsimp [b]; abel
    rw [h, norm_add_sq_real]
  rw [FilterRegularization.expectedSqEstimationError_def, heq,
    integral_add (f := fun ω ↦ ‖b‖ ^ 2 + 2 * inner ℝ b (R (η ω)))
      (g := fun ω ↦ ‖R (η ω)‖ ^ 2) ((integrable_const _).add hcross) hsq,
    integral_add (f := fun _ : Ω ↦ ‖b‖ ^ 2) (g := fun ω ↦ 2 * inner ℝ b (R (η ω)))
      (integrable_const _) hcross, hzero]
  simp [b]

/-- The two estimates preceding equation `(7.48)`: under the adjoint source condition,
TSVD has expected squared error at most `α * ‖z‖ ^ 2 + σ ^ 2 / α`. Here `σ ^ 2`
bounds the total expected squared noise norm in the chosen data-space normalization. -/
theorem expectedSqEstimationError_le_of_sourceCondition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K : H →L[ℝ] F}
    (S : ContinuousLinearMap.SingularSystem K) {α σ : ℝ} (hα : 0 < α)
    {R : F →L[ℝ] H} (hR : S.HasFilterRepresentation (SpectralFilter.tsvd α) R)
    (fTrue : H) (z : F) (hsource : fTrue = K.adjoint z)
    {η : Ω → F} (hη : MemLp η 2 μ) (hmean : ∫ ω, η ω ∂μ = 0)
    (henergy : ∫ ω, ‖η ω‖ ^ 2 ∂μ ≤ σ ^ 2) :
    FilterRegularization.expectedSqEstimationError μ R K fTrue η ≤
      α * ‖z‖ ^ 2 + σ ^ 2 / α := by
  have hLp : MemLp (fun ω ↦ R (η ω)) 2 μ := hη.continuousLinearMap_comp R
  have hvar : ∫ ω, ‖R (η ω)‖ ^ 2 ∂μ ≤ σ ^ 2 / α := by
    calc
      _ ≤ ∫ ω, ‖η ω‖ ^ 2 / α ∂μ :=
        integral_mono (hLp.integrable_norm_pow (by decide))
          ((hη.integrable_norm_pow (by decide)).div_const α)
          (fun ω ↦ tsvd_noise_sq S hα hR (η ω))
      _ = (∫ ω, ‖η ω‖ ^ 2 ∂μ) / α := integral_div α _
      _ ≤ _ := div_le_div_of_nonneg_right henergy hα.le
  rw [expected_error_eq_bias_add_variance μ K R fTrue hη hmean]
  exact add_le_add (by simpa only [hsource] using tsvd_source_bias_sq S hα hR z) hvar

/-- Exercise 7.12, equation `(7.48)`. With `fTrue = K.adjoint z` and the TSVD
choice `α = σ / ‖z‖`, the expected squared estimation error is bounded by the
nullspace floor plus `2 * σ * ‖z‖`. The side conditions `σ > 0` and `z ≠ 0`
ensure a positive cutoff. The noise is square-integrable, has mean zero, and
has total expected squared norm at most `σ ^ 2`. -/
theorem expectedSqEstimationError_le_of_aPrioriAlpha {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K : H →L[ℝ] F}
    (S : ContinuousLinearMap.SingularSystem K) {σ : ℝ} (hσ : 0 < σ)
    (fTrue : H) (z : F) (hz : z ≠ 0) (hsource : fTrue = K.adjoint z)
    {R : F →L[ℝ] H} (hR : S.HasFilterRepresentation (SpectralFilter.tsvd (σ / ‖z‖)) R)
    {η : Ω → F} (hη : MemLp η 2 μ) (hmean : ∫ ω, η ω ∂μ = 0)
    (henergy : ∫ ω, ‖η ω‖ ^ 2 ∂μ ≤ σ ^ 2) :
    FilterRegularization.expectedSqEstimationError μ R K fTrue η ≤
      ‖FilterRegularization.nullspaceComponent K fTrue‖ ^ 2 + 2 * σ * ‖z‖ := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hbound := expectedSqEstimationError_le_of_sourceCondition μ S (div_pos hσ hzn) hR fTrue z hsource hη hmean henergy
  have hbalance : σ / ‖z‖ * ‖z‖ ^ 2 + σ ^ 2 / (σ / ‖z‖) = 2 * σ * ‖z‖ := by
    field_simp [hzn.ne', hσ.ne']
    ring
  rw [hbalance] at hbound
  exact hbound.trans (le_add_of_nonneg_left (sq_nonneg _))

end TsvdEstimation
