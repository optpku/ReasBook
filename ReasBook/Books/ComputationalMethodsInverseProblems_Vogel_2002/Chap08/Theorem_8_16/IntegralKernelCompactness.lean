/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Compact integral regularization on an enclosing compact set

This is the compact-operator step in the bounded-extension approach to BV
compactness.  The domain of the original functions may be infinite
dimensional.  A fixed kernel, bounded and uniformly Lipschitz in its output
variable, sends an `L¹` ball to a relatively compact continuous-function
family.  In the convolution application the kernel is `ρ(x-y)` restricted to
an enclosing compact ball; the hypotheses below are its pointwise kernel
estimates, not a compactness or finite-approximation assumption.
-/

public section

noncomputable section

open MeasureTheory
open scoped NNReal BoundedContinuousFunction

namespace VariationalRegularization.BVCompactness.IntegralKernel

variable {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X]
variable [MeasurableSpace Y] (μ : Measure Y)
variable (k : X → Y → ℝ) (M L : ℝ≥0)
variable (hmeas : ∀ x, AEStronglyMeasurable (k x) μ)
variable (hbound : ∀ x y, ‖k x y‖ ≤ M)
variable (hlip : ∀ y, LipschitzWith L (fun x ↦ k x y))

omit [PseudoMetricSpace X] [CompactSpace X] in
include hmeas hbound in
lemma integrable (u : Lp ℝ 1 μ) (x : X) :
    Integrable (fun y ↦ k x y * u y) μ :=
  (memLp_one_iff_integrable.mp (Lp.memLp u)).bdd_mul (hmeas x) (Filter.Eventually.of_forall (hbound x))

omit [PseudoMetricSpace X] [CompactSpace X] in
include hbound in
lemma integral_norm_le (u : Lp ℝ 1 μ) (x : X) :
    ‖∫ y, k x y * u y ∂μ‖ ≤ (M : ℝ) * ‖u‖ := by
  calc
    _ ≤ ∫ y, (M : ℝ) * ‖u y‖ ∂μ :=
      norm_integral_le_of_norm_le ((memLp_one_iff_integrable.mp (Lp.memLp u)).norm.const_mul M)
        (Filter.Eventually.of_forall fun y ↦ by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hbound x y) (norm_nonneg _))
    _ = _ := by rw [integral_const_mul, ← L1.norm_eq_integral_norm]

omit [CompactSpace X] in
include hmeas hbound hlip in
lemma integral_dist_le (u : Lp ℝ 1 μ) (x x' : X) :
    dist (∫ y, k x y * u y ∂μ) (∫ y, k x' y * u y ∂μ) ≤
      (L : ℝ) * ‖u‖ * dist x x' := by
  rw [dist_eq_norm, ← integral_sub
    (integrable μ k M hmeas hbound u x) (integrable μ k M hmeas hbound u x')]
  calc
    _ ≤ ∫ y, ((L : ℝ) * dist x x') * ‖u y‖ ∂μ :=
      norm_integral_le_of_norm_le ((memLp_one_iff_integrable.mp (Lp.memLp u)).norm.const_mul _)
        (Filter.Eventually.of_forall fun y ↦ by
          rw [← sub_mul, norm_mul]
          exact mul_le_mul_of_nonneg_right
            (by simpa [dist_eq_norm] using (hlip y).dist_le_mul x x') (norm_nonneg _))
    _ = _ := by rw [integral_const_mul, ← L1.norm_eq_integral_norm]; ring

omit [CompactSpace X] in
include hmeas hbound hlip in
lemma integral_lipschitz (u : Lp ℝ 1 μ) :
    LipschitzWith (L * ‖u‖₊) (fun x ↦ ∫ y, k x y * u y ∂μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x x'
  simpa using integral_dist_le μ k M L hmeas hbound hlip u x x'

/-- The genuine integral regularization, bundled as a bounded continuous
function on the compact output space. -/
@[expose] def regularize (u : Lp ℝ 1 μ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ ∫ y, k x y * u y ∂μ,
      (integral_lipschitz μ k M L hmeas hbound hlip u).continuous⟩

@[simp] lemma regularize_apply (u : Lp ℝ 1 μ) (x : X) :
    regularize μ k M L hmeas hbound hlip u x = ∫ y, k x y * u y ∂μ := rfl

/-- Arzelà–Ascoli compactness of one fixed integral regularization of an
`L¹` ball.  Both the uniform bound and equicontinuity are proved from the
kernel inequalities. -/
lemma regularize_closedBall_relativelyCompact (R : ℝ) :
    IsCompact (closure
      (regularize μ k M L hmeas hbound hlip '' Metric.closedBall (0 : Lp ℝ 1 μ) R)) := by
  let A := regularize μ k M L hmeas hbound hlip '' Metric.closedBall (0 : Lp ℝ 1 μ) R
  apply BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0 : ℝ) ((M : ℝ) * R)) (isCompact_closedBall _ _) A
  · intro f x hf
    obtain ⟨u, hu, rfl⟩ := hf
    have hu' : ‖u‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hu
    rw [Metric.mem_closedBall, dist_zero_right, regularize_apply]
    exact (integral_norm_le μ k M hbound u x).trans
      (mul_le_mul_of_nonneg_left hu' M.coe_nonneg)
  · apply Metric.equicontinuous_of_continuity_modulus
      (fun r : ℝ ↦ ((L : ℝ) * R) * r)
      (by
        have hc : Continuous (fun r : ℝ ↦ ((L : ℝ) * R) * r) := by fun_prop
        simpa using hc.tendsto (0 : ℝ))
      ((↑) : A → X → ℝ)
    intro x x' f
    obtain ⟨u, hu, hfu⟩ := f.property
    have hu' : ‖u‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hu
    change dist (f.val x) (f.val x') ≤ _
    rw [← hfu, regularize_apply, regularize_apply]
    exact (integral_dist_le μ k M L hmeas hbound hlip u x x').trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu' L.coe_nonneg)
        (dist_nonneg))

/-- In particular every fixed regularization has finite `L¹` nets on a
finite Borel output measure.  The net is constructed from the compact
Arzelà–Ascoli image, not assumed as an input. -/
lemma regularize_closedBall_finiteApprox
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Set (Lp ℝ 1 ν), t.Finite ∧
      ∀ u ∈ Metric.closedBall (0 : Lp ℝ 1 μ) R,
        ∃ v ∈ t,
          dist (BoundedContinuousFunction.toLp 1 ν ℝ
            (regularize μ k M L hmeas hbound hlip u)) v < ε := by
  let A := regularize μ k M L hmeas hbound hlip '' Metric.closedBall (0 : Lp ℝ 1 μ) R
  let T : (X →ᵇ ℝ) →L[ℝ] Lp ℝ 1 ν := BoundedContinuousFunction.toLp 1 ν ℝ
  have hcompact : IsCompact (T '' closure A) :=
    (regularize_closedBall_relativelyCompact μ k M L hmeas hbound hlip R).image T.continuous
  obtain ⟨t, _, ht, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded hcompact.totallyBounded ε hε
  refine ⟨t, ht, ?_⟩
  intro u hu
  have huT : T (regularize μ k M L hmeas hbound hlip u) ∈ T '' closure A :=
    ⟨_, subset_closure ⟨u, hu, rfl⟩, rfl⟩
  have hc := hcover huT
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hc
  obtain ⟨hvt, huv⟩ := Set.mem_iUnion.mp hv
  exact ⟨v, hvt, huv⟩

end VariationalRegularization.BVCompactness.IntegralKernel
