/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.DomainRegularity
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.KernelApproximation
public import Mathlib.Analysis.LocallyConvex.Bounded

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Convolution Topology

namespace VariationalRegularization
namespace BVCompactness

variable {d : ℕ}

/-- Helper for Theorem 8.16: a metric set is totally bounded once every `ε`-neighborhood is
captured by one compact approximation set. -/
lemma totallyBounded_of_compactApproximation
    {α : Type*}
    [PseudoMetricSpace α]
    {s : Set α}
    (happrox :
      ∀ ε > 0, ∃ K : Set α, IsCompact K ∧ ∀ ⦃x : α⦄, x ∈ s → ∃ y ∈ K, dist x y < ε) :
    TotallyBounded s := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hε_half : 0 < ε / 2 := by positivity
  rcases happrox (ε / 2) hε_half with ⟨K, hK_compact, hKapprox⟩
  rcases
      Metric.finite_approx_of_totallyBounded
        hK_compact.totallyBounded (ε / 2) hε_half with
    ⟨t, _ht_subset, ht_finite, ht_cover⟩
  refine ⟨t, ht_finite, ?_⟩
  intro x hx
  rcases hKapprox hx with ⟨y, hyK, hxy⟩
  rcases Set.mem_iUnion.1 (ht_cover hyK) with ⟨z, hz⟩
  rcases Set.mem_iUnion.1 hz with ⟨hzT, hyz⟩
  refine Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hzT, ?_⟩⟩
  calc
    dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hxy hyz
    _ = ε := by ring

/-- The `L¹` compactness step for a bounded BV extension domain. A bounded
ambient extension and the BV translation estimate give uniform mollification
error; Arzelà–Ascoli supplies finite nets for the fixed mollification. -/
lemma toL1ClosedBall_finiteApprox
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    [HasBoundedBVExtension Ω]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (R : ℝ) :
    ∀ ε > 0,
      ∃ t : Set (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)),
        t.Finite ∧
        ∀ ⦃u : BV Ω⦄, u ∈ Metric.closedBall (0 : BV Ω) R →
          ∃ v ∈ t, dist u.toL1 v < ε := by
  obtain ⟨E, K, C, hK, hC, hext, hsupp, hE⟩ :=
    HasBoundedBVExtension.exists_extension_with_bound Ω
  let B : ℝ := C * max R 0
  have hB : 0 ≤ B := mul_nonneg hC (le_max_right _ _)
  intro ε hε
  let r : ℝ := ε / (2 * (B + 1))
  have hr : 0 < r := div_pos hε (by positivity)
  have hrB : r * B < ε / 2 := by
    have heq : r * (2 * (B + 1)) = ε := by
      dsimp [r]
      exact div_mul_cancel₀ _ (by positivity)
    nlinarith
  let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
    ⟨r / 2, r, by positivity, by linarith⟩
  let ρ : EuclideanSpace ℝ (Fin d) → ℝ := φ.normed volume
  have hρs : ContDiff ℝ 1 ρ := φ.contDiff_normed
  have hρc : HasCompactSupport ρ := φ.hasCompactSupport_normed
  have hρi : Integrable ρ := φ.integrable_normed
  obtain ⟨t, ht, hnet⟩ := KernelApproximation.finiteApprox Ω hΩ hρc hρs B (half_pos hε)
  refine ⟨t, ht, ?_⟩
  intro u hu
  have huR : ‖u‖ ≤ max R 0 := by
    exact (show ‖u‖ ≤ R by simpa [Metric.mem_closedBall, dist_zero_right] using hu).trans (le_max_left _ _)
  have hEu : ‖E u‖ ≤ B := (hE u).trans (mul_le_mul_of_nonneg_left huR hC)
  have hf : Integrable ((E u).toL1 : EuclideanSpace ℝ (Fin d) → ℝ) := Mollification.ambient_integrable (E u)
  have hfB : (∫ x, ‖(E u).toL1 x‖) ≤ B := by
    have heq : (∫ x, ‖(E u).toL1 x‖) = ‖(E u).toL1‖ := by
      simpa only [domainMeasure_top_eq_volume] using (L1.norm_eq_integral_norm (E u).toL1).symm
    rw [heq]
    exact (BV.normToL1_le (E u)).trans hEu
  obtain ⟨v, hvt, hv⟩ := hnet ((E u).toL1 : EuclideanSpace ℝ (Fin d) → ℝ) hf hfB
  refine ⟨v, hvt, ?_⟩
  have hsupport : ∀ᵐ x ∂volume, x ∉ K → (E u).toL1 x = 0 := by
    simpa only [domainMeasure_top_eq_volume] using hsupp u
  have herr := Mollification.integral_norm_sub_convolution_le (E u) hK hsupport hρc hρs
    φ.nonneg_normed φ.integral_normed (by
      simpa only [ρ, φ.support_normed_eq] using
        (Metric.ball_subset_closedBall : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r ⊆ Metric.closedBall 0 r))
  have hdist := KernelApproximation.dist_restrictLp_le_integral Ω u.toL1 hf
    (hρi.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf) (hext u).symm
  calc
    dist u.toL1 v ≤ dist u.toL1
        (KernelApproximation.restrictLp Ω (ρ ⋆ ((E u).toL1 : EuclideanSpace ℝ (Fin d) → ℝ))
          (hρi.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf)) +
      dist (KernelApproximation.restrictLp Ω (ρ ⋆ ((E u).toL1 : EuclideanSpace ℝ (Fin d) → ℝ))
          (hρi.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf)) v := dist_triangle _ _ _
    _ ≤ r * B + dist (KernelApproximation.restrictLp Ω
        (ρ ⋆ ((E u).toL1 : EuclideanSpace ℝ (Fin d) → ℝ))
        (hρi.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf)) v := by
      exact add_le_add (hdist.trans (herr.trans (mul_le_mul_of_nonneg_left hEu hr.le))) le_rfl
    _ < ε / 2 + ε / 2 := add_lt_add hrB hv
    _ = ε := add_halves ε

/-- Helper for Theorem 8.16: one compact approximation wrapper is recovered immediately from the
finite `ε`-net owner by viewing a finite set as compact. -/
lemma toL1ClosedBall_compactApproximation
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    [HasBoundedBVExtension Ω]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (R : ℝ) :
    ∀ ε > 0,
      ∃ K : Set (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)),
        IsCompact K ∧
        ∀ ⦃u : BV Ω⦄, u ∈ Metric.closedBall (0 : BV Ω) R →
          ∃ v ∈ K, dist u.toL1 v < ε := by
  intro ε hε
  rcases toL1ClosedBall_finiteApprox (d := d) (Ω := Ω) hΩ R ε hε with ⟨t, ht_finite, ht_cover⟩
  refine ⟨t, ht_finite.isCompact, ?_⟩
  intro u hu
  exact ht_cover hu

/-- The image of a BV closed ball in `L¹(Ω)` is totally bounded on a bounded
BV extension domain. -/
lemma toL1ClosedBall_totallyBounded
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    [HasBoundedBVExtension Ω]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (R : ℝ) :
    TotallyBounded (BV.toL1 '' Metric.closedBall (0 : BV Ω) R) := by
  by_cases hR : R < 0
  · -- A negative-radius closed ball is empty, so its `L¹` image is trivially totally bounded.
    simp [Metric.closedBall_eq_empty.2 hR]
  · have hR_nonneg : 0 ≤ R := le_of_not_gt hR
    -- The finite-net theorem supplies compact approximations on the `L¹` image.
    let _ := hR_nonneg
    refine
      totallyBounded_of_compactApproximation
        (s := BV.toL1 '' Metric.closedBall (0 : BV Ω) R) ?_
    intro ε hε
    rcases toL1ClosedBall_compactApproximation (d := d) (Ω := Ω) hΩ R ε hε with
      ⟨K, hK_compact, hKapprox⟩
    refine ⟨K, hK_compact, ?_⟩
    intro x hx
    rcases hx with ⟨u, hu, rfl⟩
    exact hKapprox hu

/-- The `L¹` image of a BV closed ball has compact closure on a bounded
BV extension domain. -/
lemma toL1ClosedBall_compact
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    [HasBoundedBVExtension Ω]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (R : ℝ) :
    IsCompact (closure (BV.toL1 '' Metric.closedBall (0 : BV Ω) R)) := by
  -- Completeness of `L¹` turns total boundedness into compactness of the closure.
  exact
    isCompact_closure_of_totallyBounded_quasiComplete
      (𝕜 := ℝ)
      (s := BV.toL1 '' Metric.closedBall (0 : BV Ω) R)
      (toL1ClosedBall_totallyBounded (d := d) (Ω := Ω) hΩ R)


end BVCompactness
end VariationalRegularization
