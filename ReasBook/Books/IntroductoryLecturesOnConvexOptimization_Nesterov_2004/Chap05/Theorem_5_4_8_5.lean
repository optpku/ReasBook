/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_3_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_4_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.RealProdL2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProdProd

open scoped Gradient HessianLocalNorm PowerCone SecondOrderCone

/- Theorem 5.4.8.5 lies in the Chapter 5 self-concordant-barrier / power-cone-slice domain.

Sampled owner declarations:
* `constrainedEpigraph` and `mem_constrainedEpigraph_abs_pow_iff` from
  `Definition_5_4_8_11`, the source-facing owner/view for the epigraph `Q₄`;
* `separableLogBarrierF4` and `separableLogBarrierF4_apply` from `Definition_5_4_8_12`, the
  source-facing owner/view for the barrier `F₄`;
* `powerCone` from `Definition_5_4_7_1`, the earlier chapter owner for the symmetric power
  cone;
* `power_cone_barrier` and `power_cone_barrier_is_four_self_concordant_barrier` from
  `Theorem_5_4_7_3`, the upstream Chapter 5 owner reused by the affine slice here.
* `negLog_isSelfConcordantBarrierOnWith_nonnegativeRay`,
  `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap`, and
  `IsSelfConcordantBarrierOnWith.add`, the chapter owner tools for the explicit endpoint
  `p = 1`, where the epigraph of `|x|` is cut out by affine slack maps.

Best owner abstraction:
* source-facing: the textbook epigraph/barrier pair `Q₄`, `F₄`;
* core/canonical: `constrainedEpigraph`, `IsSelfConcordantBarrierOnWith`, and the earlier
  power-cone barrier owner `power_cone_barrier`;
* bridge/view: the slice-identification theorems below relating the canonical specialized
  epigraph/barrier surface to that upstream power-cone owner for `p > 1`, together with the
  endpoint `p = 1` reduction to affine `-log` slack barriers.

Primitive data:
* the canonical epigraph owner specialized to `x ↦ |x| ^ p`;
* the canonical source-facing barrier owner `separableLogBarrierF4 p`.

Derived API:
* the interior-membership theorem for `Q₄`;
* the slice-identification bridge theorems;
* the endpoint `p = 1` barrier theorem obtained from affine `-log` slacks;
* the resulting `4`-self-concordant barrier theorem for `F₄` on `interior Q₄`, stated on the
  canonical `L²` product owner `Z = WithLp 2 (ℝ × ℝ)` through `z ↦ z.ofLp`.

This file therefore keeps the source-facing theorem, but removes the impression of a second
independent barrier construction by connecting `Q₄` and `F₄` directly to the earlier
power-cone owner while exposing the same canonical `WithLp 2` ambient owner used by the nearby
barrier files instead of relying on hidden raw-product inner-product data. -/

variable {p : ℝ}

local notation "Z" => WithLp 2 (ℝ × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → ℝ × ℝ)
local notation "Q₄[" p "]" =>
  constrainedEpigraph (Set.univ : Set ℝ)
    (fun y : ℝ ↦ ((|y| ^ p : ℝ) : WithTop ℝ))

local notation "F₄" => separableLogBarrierF4 p

namespace IsSelfConcordantOnWith

/-- Self-concordance on an open domain depends only on the restriction of the function to that
domain. -/
theorem congr
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {dom : Set E} {Mf : NNReal} {F G : E → ℝ}
    (h : IsSelfConcordantOnWith dom Mf F) (hEq : Set.EqOn F G dom) :
    IsSelfConcordantOnWith dom Mf G := by
  refine
    { isOpen_domain := h.isOpen_domain
      contDiffOn := (contDiffOn_congr fun x hx ↦ (hEq hx).symm).2 h.contDiffOn
      convexOn := h.convexOn.congr hEq
      third_deriv_bound := ?_ }
  intro x hx u
  have hEqAt : G =ᶠ[nhds x] F := by
    refine Filter.mem_of_superset (h.isOpen_domain.mem_nhds hx) ?_
    intro y hy
    exact (hEq hy).symm
  have hFcontAt : ContDiffAt ℝ 3 F x :=
    h.contDiffOn.contDiffAt (h.isOpen_domain.mem_nhds hx)
  have hGcontAt : ContDiffAt ℝ 3 G x := hFcontAt.congr_of_eventuallyEq hEqAt
  -- Rewrite the cubic derivative and the Hessian local norm through neighborhood equality.
  have hthird :
      thirdDirectionalDerivative G x u = thirdDirectionalDerivative F x u := by
    have hiter : iteratedFDeriv ℝ 3 G x = iteratedFDeriv ℝ 3 F x :=
      (Filter.EventuallyEq.iteratedFDeriv ℝ hEqAt 3).eq_of_nhds
    simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hGcontAt,
      thirdDirectionalDerivative_eq_iteratedFDeriv hFcontAt] using
      congrArg (fun A ↦ A fun _ ↦ u) hiter
  have hhess : hessian G x = hessian F x := by
    simpa [hessian] using (hEqAt.gradient.fderiv_eq (𝕜 := ℝ))
  have hnorm : ‖u‖[G; x] = ‖u‖[F; x] := by
    simp [hessianLocalNorm_def, hhess]
  calc
    |thirdDirectionalDerivative G x u| = |thirdDirectionalDerivative F x u| := by
      rw [hthird]
    _ ≤ 2 * (Mf : ℝ) * ‖u‖[F; x] ^ (3 : ℕ) := h.third_deriv_bound hx u
    _ = 2 * (Mf : ℝ) * ‖u‖[G; x] ^ (3 : ℕ) := by
      rw [hnorm]

end IsSelfConcordantOnWith

namespace IsSelfConcordantBarrierOnWith

/-- A self-concordant barrier can be transferred across functions that agree on the open barrier
domain. -/
theorem congr
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {dom : Set E} {ν : NNReal} {F G : E → ℝ}
    (h : IsSelfConcordantBarrierOnWith dom ν F) (hEq : Set.EqOn F G dom) :
    IsSelfConcordantBarrierOnWith dom ν G := by
  refine
    { toIsStandardSelfConcordantOn := h.toIsStandardSelfConcordantOn.congr hEq
      barrier_parameter_bound := ?_ }
  intro x hx u
  have hEqAt : G =ᶠ[nhds x] F := by
    refine Filter.mem_of_superset (h.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds hx) ?_
    intro y hy
    exact (hEq hy).symm
  -- Route correction: the slice barrier identity for `F₄` is only valid on the open domain, so
  -- transfer the barrier structure by comparing gradients and Hessians there.
  have hgrad : ∇ G x = ∇ F x := hEqAt.gradient_eq
  have hhess : hessian G x = hessian F x := by
    simpa [hessian] using (hEqAt.gradient.fderiv_eq (𝕜 := ℝ))
  simpa [hgrad, hhess] using h.barrier_parameter_bound hx u

end IsSelfConcordantBarrierOnWith

/-- The affine unit slice `z ↦ (((ofZ z).2, 1), (ofZ z).1)` used to compare `Q₄` with the
earlier symmetric power cone. -/
private def powerConeUnitSliceAffine : Z →ᴬ[ℝ] ((ℝ × ℝ) × ℝ) :=
  ((((WithLp.sndL 2 ℝ ℝ ℝ).prod
      (0 : Z →L[ℝ] ℝ)).prod
    (WithLp.fstL 2 ℝ ℝ ℝ)).toContinuousAffineMap) +ᵥ
      ContinuousAffineMap.const ℝ Z (((0 : ℝ), (1 : ℝ)), (0 : ℝ))

/-- Evaluating the affine slice map recovers the textbook unit slice `((t, 1), x)`. -/
@[simp] private theorem powerConeUnitSliceAffine_apply (z : Z) :
    powerConeUnitSliceAffine z = (((ofZ z).2, 1), (ofZ z).1) := by
  simpa [powerConeUnitSliceAffine, WithLp.ofLp]

-- Proof sketch: rewrite `powerCone (1 / p)` at the affine slice `((t, 1), x)` and use
-- `Real.le_rpow_inv_iff_of_pos` / `Real.rpow_le_rpow_iff` to convert
-- `|x| ≤ t^(1 / p)` into the epigraph inequality `t ≥ |x|^p`.
/-- On the affine slice `((t, 1), x)`, the symmetric power cone `K_{1 / p}` is exactly the
canonical epigraph `Q₄` of `x ↦ |x|^p`. -/
theorem mem_powerCone_one_div_p_unitSlice_iff {x t : ℝ} (hp0 : 0 < p) :
    ((t, 1), x) ∈ K_[(1 / p)] ↔ (x, t) ∈ Q₄[p] := by
  rw [mem_powerCone_iff, mem_constrainedEpigraph_abs_pow_iff]
  constructor
  · rintro ⟨ht, -, hx⟩
    have hx' : |x| ≤ Real.rpow t (1 / p) := by
      simpa [powerConeGeometricMean_apply] using hx
    have hpow : |x| ^ p ≤ (Real.rpow t (1 / p)) ^ p := by
      exact (Real.rpow_le_rpow_iff (abs_nonneg x) (Real.rpow_nonneg ht _) hp0).2 hx'
    have ht' : (Real.rpow t (1 / p)) ^ p = t := by
      simpa [one_div] using (Real.rpow_inv_rpow ht hp0.ne' : (t ^ p⁻¹) ^ p = t)
    rw [ht'] at hpow
    simpa [ge_iff_le] using hpow
  · intro hxt
    have hxt' : |x| ^ p ≤ t := by
      simpa [ge_iff_le] using hxt
    have hxt_nonneg : 0 ≤ |x| ^ p := Real.rpow_nonneg (abs_nonneg x) _
    have ht : 0 ≤ t := le_trans hxt_nonneg hxt'
    have hx : |x| ≤ Real.rpow t (1 / p) := by
      simpa [one_div] using (Real.le_rpow_inv_iff_of_pos (abs_nonneg x) ht hp0).2 hxt'
    refine ⟨ht, by norm_num, ?_⟩
    simpa [powerConeGeometricMean_apply] using hx

-- Proof sketch: for `t ≥ 0`, evaluate both sides using `separableLogBarrierF4_apply` and
-- `power_cone_barrier_apply`, then simplify the fixed slice coordinate `1`.
/-- On the affine slice `((t, 1), x)`, the source-facing barrier `F₄` is exactly the Chapter 5
power-cone barrier with parameter `α = 1 / p`. -/
theorem separableLogBarrierF4_eq_power_cone_barrier_unitSlice
    (p x t : ℝ) (ht : 0 ≤ t) :
    separableLogBarrierF4 p (x, t) = power_cone_barrier (1 / p) ((t, 1), x) := by
  rw [separableLogBarrierF4_apply, power_cone_barrier_apply (1 / p) t 1 x ht (by norm_num)]
  simp [div_eq_mul_inv, sub_eq_add_neg, add_comm, mul_comm]

-- Proof sketch: for `p > 0`, the function `x ↦ |x| ^ p` is continuous, so the interior of its
-- closed epigraph is obtained by replacing `t ≥ |x| ^ p` with the strict inequality
-- `t > |x| ^ p`.
/-- A pair `(x, t)` lies in the canonical epigraph interior for Definition 5.4.8.11 exactly when
`t > |x| ^ p`. -/
theorem mem_interior_constrainedEpigraph_abs_pow_iff {x t : ℝ} (hp0 : 0 < p) :
    (x, t) ∈ interior Q₄[p] ↔ t > |x| ^ p := by
  constructor
  · intro h
    have hQ : (x, t) ∈ Q₄[p] := interior_subset h
    rw [mem_constrainedEpigraph_abs_pow_iff] at hQ
    have hxt : |x| ^ p ≤ t := by
      simpa [ge_iff_le] using hQ
    -- Strictify the epigraph boundary by perturbing only the scalar coordinate downward.
    by_contra hnot
    have hle : t ≤ |x| ^ p := le_of_not_gt hnot
    have heq : t = |x| ^ p := le_antisymm hle hxt
    let γ : ℝ → ℝ × ℝ := fun s ↦ (x, s)
    have hγ : Continuous γ := by
      fun_prop
    have hpre : γ ⁻¹' interior Q₄[p] ∈ nhds t := by
      exact hγ.continuousAt.preimage_mem_nhds
        (IsOpen.mem_nhds isOpen_interior (by simpa [γ] using h))
    rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
    have hdown : t - ε / 2 ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hneg : t - ε / 2 - t < 0 := by
        linarith
      rw [abs_of_neg hneg]
      linarith
    have hmem : γ (t - ε / 2) ∈ interior Q₄[p] := hεsub hdown
    have hQdown : γ (t - ε / 2) ∈ Q₄[p] := interior_subset hmem
    rw [mem_constrainedEpigraph_abs_pow_iff] at hQdown
    have hbound : t - ε / 2 ≥ |x| ^ p := by
      simpa [γ] using hQdown
    rw [heq] at hbound
    linarith
  · intro h
    let φ : ℝ × ℝ → ℝ := fun q ↦ |q.1| ^ p - q.2
    -- Use continuity of `q ↦ |q.1| ^ p` to build an open neighborhood from the strict gap.
    have hφ_cont : ContinuousAt φ (x, t) := by
      have hfstAbs : ContinuousAt (fun q : ℝ × ℝ ↦ |q.1|) (x, t) := by
        simpa using (continuousAt_fst : ContinuousAt (fun q : ℝ × ℝ ↦ q.1) (x, t)).abs
      have habs_pow : ContinuousAt (fun q : ℝ × ℝ ↦ |q.1| ^ p) (x, t) := by
        simpa using hfstAbs.rpow_const (p := p) (Or.inr hp0.le)
      simpa [φ] using habs_pow.sub continuousAt_snd
    have hφ_neg : φ (x, t) < 0 := by
      simpa [φ] using sub_neg.mpr h
    have hgap : φ ⁻¹' Set.Iio (0 : ℝ) ∈ nhds (x, t) :=
      hφ_cont.preimage_mem_nhds (isOpen_Iio.mem_nhds hφ_neg)
    have hnhds : Q₄[p] ∈ nhds (x, t) := by
      refine Filter.mem_of_superset hgap ?_
      rintro y hy
      rw [mem_constrainedEpigraph_abs_pow_iff]
      have hylt : |y.1| ^ p - y.2 < 0 := by
        simpa [φ] using hy
      linarith
    exact mem_interior_iff_mem_nhds.mpr hnhds

/-- On the affine slice `((t, 1), x)`, interior points of the symmetric power cone are exactly
the interior points of the epigraph `Q₄`. -/
theorem mem_interior_powerCone_one_div_p_unitSlice_iff {x t : ℝ} (hp0 : 0 < p) :
    ((t, 1), x) ∈ interior K_[(1 / p)] ↔ (x, t) ∈ interior Q₄[p] := by
  rw [mem_interior_constrainedEpigraph_abs_pow_iff (p := p) hp0]
  constructor
  · intro h
    have hK : ((t, 1), x) ∈ K_[(1 / p)] := interior_subset h
    simp [mem_powerCone_iff, powerConeGeometricMean_apply] at hK
    rcases hK with ⟨ht, hx⟩
    have ht_strict : 0 < t := by
      by_contra ht_nonpos
      have ht_zero : t = 0 := le_antisymm (le_of_not_gt ht_nonpos) ht
      let γ : ℝ → ((ℝ × ℝ) × ℝ) := fun s ↦ ((s, 1), x)
      have hγ : Continuous γ := by
        fun_prop
      have hpre : γ ⁻¹' interior K_[(1 / p)] ∈ nhds t := by
        exact hγ.continuousAt.preimage_mem_nhds
          (IsOpen.mem_nhds isOpen_interior (by simpa [γ] using h))
      rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
      have hneg : -ε / 2 ∈ Metric.ball t ε := by
        have hhalf_neg : (-ε / 2 : ℝ) < 0 := by
          linarith
        have habs : |(-ε / 2 : ℝ) - 0| = ε / 2 := by
          rw [sub_zero, abs_of_neg hhalf_neg]
          ring
        rw [ht_zero, Metric.mem_ball, Real.dist_eq, habs]
        linarith
      have hmem : γ (-ε / 2) ∈ interior K_[(1 / p)] := hεsub hneg
      have hcone : γ (-ε / 2) ∈ K_[(1 / p)] := interior_subset hmem
      simp [γ, mem_powerCone_iff, powerConeGeometricMean_apply] at hcone
      linarith
    have hx_strict : |x| < t ^ p⁻¹ := by
      by_contra hx_not
      have hx_eq : |x| = t ^ p⁻¹ := le_antisymm hx (not_lt.mp hx_not)
      let γ : ℝ → ((ℝ × ℝ) × ℝ) := fun s ↦ ((t, 1), s)
      have hγ : Continuous γ := by
        fun_prop
      have hpre : γ ⁻¹' interior K_[(1 / p)] ∈ nhds x := by
        exact hγ.continuousAt.preimage_mem_nhds
          (IsOpen.mem_nhds isOpen_interior (by simpa [γ] using h))
      rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
      rcases le_or_gt 0 x with hx_nonneg | hx_neg
      · have hup : x + ε / 2 ∈ Metric.ball x ε := by
          have hhalf_nonneg : 0 ≤ x + ε / 2 - x := by
            linarith
          have hdist : x + ε / 2 - x = ε / 2 := by
            ring
          rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg hhalf_nonneg]
          rw [hdist]
          linarith
        have hmem : γ (x + ε / 2) ∈ interior K_[(1 / p)] := hεsub hup
        have hcone : γ (x + ε / 2) ∈ K_[(1 / p)] := interior_subset hmem
        simp [γ, mem_powerCone_iff, powerConeGeometricMean_apply] at hcone
        have hx_eq' : x = t ^ p⁻¹ := by
          simpa [abs_of_nonneg hx_nonneg] using hx_eq
        have hxplus_nonneg : 0 ≤ x + ε / 2 := by
          linarith
        have hbound : x + ε / 2 ≤ t ^ p⁻¹ := by
          simpa [abs_of_nonneg hxplus_nonneg] using hcone.2
        rw [← hx_eq'] at hbound
        linarith
      · have hdown : x - ε / 2 ∈ Metric.ball x ε := by
          have hhalf_nonpos : x - ε / 2 - x ≤ 0 := by
            linarith
          have hdist : x - ε / 2 - x = -(ε / 2) := by
            ring
          rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos hhalf_nonpos]
          rw [hdist]
          linarith
        have hmem : γ (x - ε / 2) ∈ interior K_[(1 / p)] := hεsub hdown
        have hcone : γ (x - ε / 2) ∈ K_[(1 / p)] := interior_subset hmem
        simp [γ, mem_powerCone_iff, powerConeGeometricMean_apply] at hcone
        have hx_eq' : -x = t ^ p⁻¹ := by
          simpa [abs_of_neg hx_neg] using hx_eq
        have hxminus_neg : x - ε / 2 < 0 := by
          linarith
        have hbound_raw : -(x - ε / 2) ≤ t ^ p⁻¹ := by
          simpa [abs_of_neg hxminus_neg] using hcone.2
        have hbound : -x + ε / 2 ≤ t ^ p⁻¹ := by
          linarith
        rw [← hx_eq'] at hbound
        linarith
    -- Convert the strict slice inequality back to the strict epigraph inequality.
    simpa [one_div] using
      (Real.lt_rpow_inv_iff_of_pos (abs_nonneg x) ht_strict.le hp0).1 hx_strict
  · intro h
    have ht_strict : 0 < t := by
      have hpow_nonneg : 0 ≤ |x| ^ p := Real.rpow_nonneg (abs_nonneg x) p
      linarith
    have hx_strict : |x| < t ^ p⁻¹ := by
      simpa [one_div] using
        (Real.lt_rpow_inv_iff_of_pos (abs_nonneg x) ht_strict.le hp0).2 h
    let q : ((ℝ × ℝ) × ℝ) := ((t, 1), x)
    let φ : ((ℝ × ℝ) × ℝ) → ℝ := fun y ↦ powerConeGeometricMean (1 / p) y.1 - |y.2|
    -- Build an interior neighborhood from positivity of the slice coordinates and of the slack.
    have hφ_pos : 0 < φ q := by
      simpa [q, φ, powerConeGeometricMean_apply] using sub_pos.mpr hx_strict
    have hφ_cont : ContinuousAt φ q := by
      have hfst :
          ContinuousAt (fun y : ((ℝ × ℝ) × ℝ) ↦ Real.rpow y.1.1 (1 / p)) q := by
        simpa using continuousAt_fst.fst.rpow_const (Or.inl ht_strict.ne')
      have hsnd :
          ContinuousAt (fun y : ((ℝ × ℝ) × ℝ) ↦ Real.rpow y.1.2 (1 - 1 / p)) q := by
        simpa using continuousAt_fst.snd.rpow_const (Or.inl one_ne_zero)
      have hmul :
          ContinuousAt
            (fun y : ((ℝ × ℝ) × ℝ) ↦
              Real.rpow y.1.1 (1 / p) * Real.rpow y.1.2 (1 - 1 / p))
            q :=
        hfst.mul hsnd
      simpa [φ, powerConeGeometricMean_apply] using hmul.sub continuousAt_snd.abs
    have hfirst :
        (fun y : ((ℝ × ℝ) × ℝ) ↦ y.1.1) ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds q :=
      continuousAt_fst.fst.preimage_mem_nhds (isOpen_Ioi.mem_nhds ht_strict)
    have hsecond :
        (fun y : ((ℝ × ℝ) × ℝ) ↦ y.1.2) ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds q :=
      continuousAt_fst.snd.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by norm_num : 0 < (1 : ℝ)))
    have hslack : φ ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds q :=
      hφ_cont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hφ_pos)
    have hnhds : K_[(1 / p)] ∈ nhds q := by
      refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem hfirst hsecond) hslack) ?_
      rintro y ⟨⟨hy1, hy2⟩, hy3⟩
      rw [mem_powerCone_iff, powerConeGeometricMean_apply]
      refine ⟨le_of_lt hy1, le_of_lt hy2, ?_⟩
      have hy3' : 0 < powerConeGeometricMean (1 / p) y.1 - |y.2| := by
        simpa [φ] using hy3
      have hylt : |y.2| < powerConeGeometricMean (1 / p) y.1 := by
        linarith
      exact le_of_lt hylt
    exact mem_interior_iff_mem_nhds.mpr hnhds

/-- On the epigraph interior, the source-facing barrier `F₄` agrees with the symmetric power-cone
barrier pulled back along the affine unit slice. -/
theorem power_cone_barrier_unitSlice_eqOn (hp0 : 0 < p) :
    Set.EqOn
      (power_cone_barrier (1 / p) ∘ powerConeUnitSliceAffine)
      (F₄ ∘ ofZ)
      (ofZ ⁻¹' interior Q₄[p]) := by
  intro z hz
  have hzQ : ofZ z ∈ interior Q₄[p] := hz
  have ht_mem : (ofZ z).2 > |(ofZ z).1| ^ p :=
    (mem_interior_constrainedEpigraph_abs_pow_iff (p := p) hp0).1 hzQ
  have ht_nonneg : 0 ≤ (ofZ z).2 := by
    have hpow_nonneg : 0 ≤ |(ofZ z).1| ^ p := Real.rpow_nonneg (abs_nonneg _) p
    linarith
  -- Evaluate both barriers on the open slice, where the scalar coordinate is nonnegative.
  simpa [Function.comp, powerConeUnitSliceAffine_apply] using
    (separableLogBarrierF4_eq_power_cone_barrier_unitSlice
      p (ofZ z).1 (ofZ z).2 ht_nonneg).symm

-- Proof sketch: at the endpoint `p = 1`, the domain `t > |x|` is exactly the intersection of the
-- three affine slack regions `t > 0`, `t - x > 0`, and `t + x > 0`. Pull back the scalar owner
-- `negLog_isSelfConcordantBarrierOnWith_nonnegativeRay` along those affine maps, sum the three
-- resulting barriers using `IsSelfConcordantBarrierOnWith.add`, and compare with the source-facing
-- formula `F₄(x, t) = -log t - log (t^2 - x^2)` on the same open domain.
/-- Endpoint case `p = 1`: the barrier
`F₄(x, t) = -\log t - \log (t^2 - x^2)` is a `3`-self-concordant barrier for the epigraph of
`|x|`, viewed on the canonical `L²` product owner `Z = WithLp 2 (ℝ × ℝ)` through
`z ↦ z.ofLp`. -/
theorem separableLogBarrierF4_one_is_three_selfConcordantBarrier :
    IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' interior Q₄[(1 : ℝ)])
      (3 : NNReal)
      (separableLogBarrierF4 1 ∘ ofZ) := by
  let sndMap : Z →ᴬ[ℝ] ℝ :=
    (WithLp.sndL 2 ℝ ℝ ℝ).toContinuousAffineMap
  let hsnd :
      IsSelfConcordantBarrierOnWith
        (ofZ ⁻¹' {q : ℝ × ℝ | 0 < q.2})
        1
        (fun z : Z ↦ -Real.log (ofZ z).2) := by
      -- Pull back the scalar nonnegative-ray barrier along the second-coordinate projection.
      simpa [sndMap, Function.comp, WithLp.ofLp] using
        (negLog_isSelfConcordantBarrierOnWith_nonnegativeRay.comp_continuousAffineMap sndMap)
  let hcone :
      IsSelfConcordantBarrierOnWith
        (ofZ ⁻¹' interior K₂[ℝ])
        2
        (secondOrderConeBarrier ∘ ofZ) :=
    secondOrderConeBarrier_isSelfConcordantBarrierOnWith (E := ℝ)
  let hsum :
      IsSelfConcordantBarrierOnWith
        ((ofZ ⁻¹' {q : ℝ × ℝ | 0 < q.2}) ∩ (ofZ ⁻¹' interior K₂[ℝ]))
        (1 + 2)
        ((fun z : Z ↦ -Real.log (ofZ z).2) + (secondOrderConeBarrier ∘ ofZ)) :=
    hsnd.add hcone
  have hν : (1 : NNReal) + 2 = 3 := by
    norm_num
  have hdom :
      ((ofZ ⁻¹' {q : ℝ × ℝ | 0 < q.2}) ∩ (ofZ ⁻¹' interior K₂[ℝ])) =
        (ofZ ⁻¹' interior Q₄[(1 : ℝ)]) := by
    ext z
    change (0 < (ofZ z).2 ∧ ofZ z ∈ interior K₂[ℝ]) ↔ ofZ z ∈ interior Q₄[(1 : ℝ)]
    rw [mem_interior_secondOrderCone_iff, Real.norm_eq_abs,
      mem_interior_constrainedEpigraph_abs_pow_iff (p := (1 : ℝ)) zero_lt_one]
    constructor
    · rintro ⟨_, hcone⟩
      simpa using hcone
    · intro hQ
      refine ⟨?_, ?_⟩
      · have habs_nonneg : 0 ≤ |(ofZ z).1| ^ (1 : ℝ) := by
          simpa using Real.rpow_nonneg (abs_nonneg ((ofZ z).1)) (1 : ℝ)
        linarith
      · simpa using hQ
  have hfun :
      ((fun z : Z ↦ -Real.log (ofZ z).2) + (secondOrderConeBarrier ∘ ofZ)) =
        (separableLogBarrierF4 (1 : ℝ) ∘ ofZ) := by
    funext z
    -- Rewrite the second-order-cone factor to the endpoint formula `-log (t^2 - x^2)`.
    calc
      ((fun z : Z ↦ -Real.log (ofZ z).2) + (secondOrderConeBarrier ∘ ofZ)) z =
          -Real.log (ofZ z).2 -
            Real.log ((ofZ z).2 ^ (2 : ℕ) - (ofZ z).1 ^ (2 : ℕ)) := by
              simp [secondOrderConeBarrier_apply, Real.norm_eq_abs, sq_abs, sub_eq_add_neg]
      _ = (separableLogBarrierF4 (1 : ℝ) ∘ ofZ) z := by
        symm
        simpa [Function.comp] using
          (separableLogBarrierF4_apply (1 : ℝ) (ofZ z).1 (ofZ z).2)
  have hsum' :
      IsSelfConcordantBarrierOnWith
        ((ofZ ⁻¹' {q : ℝ × ℝ | 0 < q.2}) ∩ (ofZ ⁻¹' interior K₂[ℝ]))
        (3 : NNReal)
        ((fun z : Z ↦ -Real.log (ofZ z).2) + (secondOrderConeBarrier ∘ ofZ)) := by
    simpa [hν] using hsum
  have hsum'' := hsum'
  rw [hdom] at hsum''
  have hsum_final :
      IsSelfConcordantBarrierOnWith
        (ofZ ⁻¹' interior Q₄[(1 : ℝ)])
        (3 : NNReal)
        ((fun z : Z ↦ -Real.log (ofZ z).2) + (secondOrderConeBarrier ∘ ofZ)) :=
    hsum''
  have hfunEq :
      Set.EqOn
        ((fun z : Z ↦ -Real.log (ofZ z).2) + (secondOrderConeBarrier ∘ ofZ))
        (separableLogBarrierF4 (1 : ℝ) ∘ ofZ)
        (ofZ ⁻¹' interior Q₄[(1 : ℝ)]) := by
    intro z hz
    simpa [hfun] using congrArg (fun f : Z → ℝ ↦ f z) hfun
  exact hsum_final.congr hfunEq

-- Proof sketch: split into the endpoint `p = 1` and the genuine power-cone range `p > 1`. In
-- the endpoint case, use `separableLogBarrierF4_one_is_three_selfConcordantBarrier` and enlarge
-- the barrier parameter from `3` to `4`. For `p > 1`, identify the interior of the canonical
-- closed epigraph from Definition 5.4.8.11 with the affine slice of `interior (powerCone
-- (1 / p))`, rewrite the barrier through `separableLogBarrierF4_eq_power_cone_barrier_unitSlice`,
-- and apply `power_cone_barrier_is_four_self_concordant_barrier`.
/-- Theorem 5.4.8.5: for `p ≥ 1`, the function
`F₄(x, t) = -\log t - \log (t^(2 / p) - x^2)` is a `4`-self-concordant barrier for the canonical
epigraph of `x ↦ |x|^p`, viewed on the canonical `L²` product owner `Z = WithLp 2 (ℝ × ℝ)`
through `z ↦ z.ofLp`. -/
theorem separableLogBarrierF4_is_four_selfConcordantBarrier
    (hp : 1 ≤ p) :
    IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' interior Q₄[p])
      (4 : NNReal)
      (F₄ ∘ ofZ) := by
  rcases lt_or_eq_of_le hp with hp1 | rfl
  · have hp0 : 0 < p := lt_trans zero_lt_one hp1
    have hα₀ : 0 < 1 / p := one_div_pos.mpr hp0
    have hα₁ : 1 / p < 1 := by
      simpa [one_div] using inv_lt_one_of_one_lt₀ hp1
    let hbase :
        IsSelfConcordantBarrierOnWith
          (interior K_[(1 / p)])
          (4 : NNReal)
          (power_cone_barrier (1 / p)) :=
      power_cone_barrier_is_four_self_concordant_barrier hα₀ hα₁
    let hslice :
        IsSelfConcordantBarrierOnWith
          (powerConeUnitSliceAffine ⁻¹' interior K_[(1 / p)])
          (4 : NNReal)
          (power_cone_barrier (1 / p) ∘ powerConeUnitSliceAffine) :=
      hbase.comp_continuousAffineMap powerConeUnitSliceAffine
    have hdom :
        ((powerConeUnitSliceAffine : Z → ((ℝ × ℝ) × ℝ)) ⁻¹' interior K_[(1 / p)]) =
          ofZ ⁻¹' interior Q₄[p] := by
      ext z
      change powerConeUnitSliceAffine z ∈ interior K_[(1 / p)] ↔ ofZ z ∈ interior Q₄[p]
      rw [powerConeUnitSliceAffine_apply]
      simpa using mem_interior_powerCone_one_div_p_unitSlice_iff (p := p) hp0
    have hfun :
        Set.EqOn
          (power_cone_barrier (1 / p) ∘ powerConeUnitSliceAffine)
          (F₄ ∘ ofZ)
          (ofZ ⁻¹' interior Q₄[p]) :=
      power_cone_barrier_unitSlice_eqOn (p := p) hp0
    -- Pull back the canonical cone barrier, then transfer it across the domain-local identity.
    have hslice' := hslice
    rw [hdom] at hslice'
    have hslice'' :
        IsSelfConcordantBarrierOnWith
          (ofZ ⁻¹' interior Q₄[p])
          (4 : NNReal)
          (power_cone_barrier (1 / p) ∘ powerConeUnitSliceAffine) :=
      hslice'
    exact hslice''.congr hfun
  · let h3 := separableLogBarrierF4_one_is_three_selfConcordantBarrier
    refine
      { toIsStandardSelfConcordantOn := h3.toIsStandardSelfConcordantOn
        barrier_parameter_bound := ?_ }
    intro x hx u
    exact le_trans (h3.barrier_parameter_bound hx u) (by norm_num)
