/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_6

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set Topology
open scoped Gradient Pointwise

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 5.4.3.2 lies in the Chapter 5 logarithmic-homogeneity / self-concordant-barrier domain.

Sampled owner declarations in this domain:
* `IsLogarithmicallyHomogeneousOnWith` in `Definition_5_4_3_3`, the source-facing owner for the
  logarithmic scaling law on a cone interior;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for `ν`-self-
  concordant barriers on a domain;
* mathlib `ConvexCone.Salient`, the canonical owner for the source's "no straight lines" / no
  nontrivial lineality condition on a cone;
* `HasPositiveDefiniteHessianOn` and
  `HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem` in `Definition_5_0_23`, the canonical
  Chapter 5 owner and bridge for pointwise Hessian nondegeneracy on a domain;
* `hessian` in `Chap01/Definition_1_4_16` and `ContinuousLinearMap.inverse`, the canonical
  operator-level Hessian and inverse-Hessian surface.

Best owner abstraction:
* source-facing: the six logarithmic-homogeneity identities and their barrier consequence under
  the full logarithmic-homogeneity / barrier / salience hypotheses;
* core/canonical: `HasPositiveDefiniteHessianOn (interior (K : Set E)) F` together with the
  operator owner `hessian F x`, and the cone owner `K.Salient`;
* bridge/view: the textbook "no straight lines" phrasing
  `∀ u, u ∈ K → -u ∈ K → u = 0`, the determinant-nonzero consequence, and the inverse-Hessian
  pairing formula.

Primitive data:
* a cone owner `K : ConvexCone ℝ E`;
* logarithmic homogeneity of `F` on `K`;
* a self-concordant barrier hypothesis on `interior K`;
* the salience condition on `K`.

Derived API:
* pointwise positive-definite Hessian on `interior K` under the full barrier hypotheses;
* Hessian nondegeneracy at each interior point;
* the canonical inverse-Hessian expression `((hessian F x).inverse ...)`.

This refinement keeps the textbook source-facing statements, deletes the unused local salience
repackaging, and keeps the supporting Hessian-nondegeneracy bridge on the chapter owner
`HasPositiveDefiniteHessianOn`. The bridge now carries the closed logarithmic-homogeneity
hypothesis actually needed to match the cone geometry used later in the file, while the main
gradient/Hessian identities continue to use the canonical cone owner `K.Salient` together with the
canonical `hessian` / inverse surface instead of raw `fderiv` terms. -/

section BarrierCone

variable {K : ConvexCone ℝ E} {ν : NNReal} {μ : ℝ} {F : E → ℝ}

/-- Helper for Lemma 5.4.3.2: positive scalar multiplication preserves the interior of a
logarithmically homogeneous cone. -/
private lemma pos_smul_mem_interior_cone
    (hFlog : IsLogarithmicallyHomogeneousOnWith K μ F)
    {x : E} (hx : x ∈ interior (K : Set E)) {τ : ℝ} (hτ : 0 < τ) :
    τ • x ∈ interior (K : Set E) := by
  -- Transport the interior through the positive-scalar action and rewrite `τ • K = K`.
  have hτ_ne : τ ≠ 0 := ne_of_gt hτ
  have hsmul_eq : τ • (K : Set E) = (K : Set E) := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hτ_ne] at hy
      simpa [smul_smul, mul_inv_cancel₀ hτ_ne] using hFlog.smul_mem hy (le_of_lt hτ)
    · intro hy
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hτ_ne]
      simpa [one_div, smul_smul] using hFlog.smul_mem hy (le_of_lt (inv_pos.mpr hτ))
  have hmem : τ • x ∈ τ • interior (K : Set E) := Set.smul_mem_smul_set hx
  have hmem' : τ • x ∈ interior (τ • (K : Set E)) := by
    rw [interior_smul₀ hτ_ne]
    exact hmem
  rwa [hsmul_eq] at hmem'

/-- Helper for Lemma 5.4.3.2: a salient cone has no nontrivial affine line inside its interior. -/
private lemma interior_cone_has_no_affine_line_of_salient
    (hFlog : IsLogarithmicallyHomogeneousOnWith K μ F) (hK : K.Salient)
    {x h : E} (hh : h ≠ 0) :
    ¬ ∀ τ : ℝ, x + τ • h ∈ interior (K : Set E) := by
  intro hline
  have hclosed : IsClosed (K : Set E) := hFlog.isClosed
  have hh_mem : h ∈ (K : Set E) := by
    let a : ℕ → E := fun n ↦ (((n : ℝ) + 1)⁻¹) • x + h
    have ha_mem : ∀ n, a n ∈ (K : Set E) := by
      intro n
      have hpos : 0 < ((n : ℝ) + 1)⁻¹ := inv_pos.mpr (by positivity)
      have hline_mem : x + ((n : ℝ) + 1) • h ∈ interior (K : Set E) := hline ((n : ℝ) + 1)
      have hscaled :
          (((n : ℝ) + 1)⁻¹) • (x + ((n : ℝ) + 1) • h) ∈ (K : Set E) := by
        exact interior_subset (pos_smul_mem_interior_cone hFlog hline_mem hpos)
      have hcoeff : (((n : ℝ) + 1)⁻¹) * ((n : ℝ) + 1) = 1 := by
        field_simp
      simpa [a, smul_add, smul_smul, hcoeff] using hscaled
    have ha_tendsto : Tendsto a atTop (nhds h) := by
      have hcoeff :
          Tendsto (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹ : ℝ)) atTop (nhds 0) := by
        have hnat : Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ))) atTop atTop :=
          tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
        simpa [one_div] using (tendsto_inv_atTop_zero.comp hnat)
      simpa [a] using (hcoeff.smul_const x).add tendsto_const_nhds
    exact hclosed.mem_of_tendsto ha_tendsto (Filter.Eventually.of_forall ha_mem)
  have hneg_mem : -h ∈ (K : Set E) := by
    let b : ℕ → E := fun n ↦ (((n : ℝ) + 1)⁻¹) • x - h
    have hb_mem : ∀ n, b n ∈ (K : Set E) := by
      intro n
      have hpos : 0 < ((n : ℝ) + 1)⁻¹ := inv_pos.mpr (by positivity)
      have hline_mem : x + (-((n : ℝ) + 1)) • h ∈ interior (K : Set E) := hline (-((n : ℝ) + 1))
      have hscaled :
          (((n : ℝ) + 1)⁻¹) • (x + (-((n : ℝ) + 1)) • h) ∈ (K : Set E) := by
        exact interior_subset (pos_smul_mem_interior_cone hFlog hline_mem hpos)
      have hcoeff : (((n : ℝ) + 1)⁻¹) * (-((n : ℝ) + 1)) = (-1 : ℝ) := by
        field_simp
      have hb_eq :
          (((n : ℝ) + 1)⁻¹) • (x + (-((n : ℝ) + 1)) • h) = b n := by
        calc
          (((n : ℝ) + 1)⁻¹) • (x + (-((n : ℝ) + 1)) • h)
              = (((n : ℝ) + 1)⁻¹) • x +
                  ((((n : ℝ) + 1)⁻¹) * (-((n : ℝ) + 1))) • h := by
                  simp [smul_add, smul_smul]
          _ = (((n : ℝ) + 1)⁻¹) • x + (-1 : ℝ) • h := by rw [hcoeff]
          _ = b n := by simp [b, sub_eq_add_neg]
      exact hb_eq ▸ hscaled
    have hb_tendsto : Tendsto b atTop (nhds (-h)) := by
      have hcoeff :
          Tendsto (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹ : ℝ)) atTop (nhds 0) := by
        have hnat : Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ))) atTop atTop :=
          tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
        simpa [one_div] using (tendsto_inv_atTop_zero.comp hnat)
      have hsum :
          Tendsto (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹) • x + (-h))
            atTop (nhds (((0 : ℝ) • x) + -h)) :=
        (hcoeff.smul_const x).add tendsto_const_nhds
      simpa [b, sub_eq_add_neg] using hsum
    exact hclosed.mem_of_tendsto hb_tendsto (Filter.Eventually.of_forall hb_mem)
  exact (hK h hh_mem hh hneg_mem).elim

variable [FiniteDimensional ℝ E]

local instance barrierConePosDefFiniteDimensionalComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

/-- Helper for Lemma 5.4.3.2: the constrained epigraph over the cone interior is closed because
barrier blow-up excludes finite-height boundary limits. -/
private lemma constrainedEpigraph_isClosed_of_logHomogeneousBarrier
    (hFlog : IsLogarithmicallyHomogeneousOnWith K (ν : ℝ) F)
    (hbarrier : IsSelfConcordantBarrierOnWith (interior (K : Set E)) ν F) :
    IsClosed (constrainedEpigraph (interior (K : Set E)) (fun y ↦ (F y : WithTop ℝ))) := by
  -- Check sequential closedness and split on whether the base limit stays interior or hits the
  -- frontier.
  apply (isSeqClosed_iff_isClosed).mp
  intro y p hy hp
  have hy_dom : ∀ n, (y n).1 ∈ interior (K : Set E) := fun n ↦ (mem_constrainedEpigraph_iff.mp (hy n)).1
  have hy_ineq : ∀ n, F (y n).1 ≤ (y n).2 := fun n ↦ by
    exact_mod_cast (mem_constrainedEpigraph_iff.mp (hy n)).2
  have hp₁ : Tendsto (fun n ↦ (y n).1) atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hp
  have hp₂ : Tendsto (fun n ↦ (y n).2) atTop (nhds p.2) :=
    (continuous_snd.tendsto p).comp hp
  by_cases hpint : p.1 ∈ interior (K : Set E)
  · -- Inside the open cone, continuity of `F` lets us pass the epigraph inequality to the limit.
    have hcontAt : ContinuousAt F p.1 := by
      have hnhds : interior (K : Set E) ∈ nhds p.1 := by
        simpa [mem_interior_iff_mem_nhds] using hpint
      exact (hFlog.contDiffOn.contDiffAt hnhds).continuousAt
    have hF : Tendsto (fun n ↦ F (y n).1) atTop (nhds (F p.1)) :=
      hcontAt.tendsto.comp hp₁
    have hpair :
        Tendsto (fun n ↦ (F (y n).1, (y n).2)) atTop (nhds (F p.1, p.2)) :=
      hF.prodMk_nhds hp₂
    have hle :
        ∀ᶠ n in atTop, (F (y n).1, (y n).2) ∈ {q : ℝ × ℝ | q.1 ≤ q.2} :=
      Filter.Eventually.of_forall hy_ineq
    refine mem_constrainedEpigraph_iff.mpr ⟨hpint, ?_⟩
    exact_mod_cast (isClosed_le continuous_fst continuous_snd).mem_of_tendsto hpair hle
  · -- On the boundary, barrier blow-up forces the heights to diverge, contradicting convergence.
    exfalso
    have hpcl : p.1 ∈ closure (interior (K : Set E)) := by
      exact isClosed_closure.mem_of_tendsto hp₁
        (Filter.Eventually.of_forall fun n ↦ subset_closure (hy_dom n))
    have hpfront : p.1 ∈ frontier (interior (K : Set E)) := by
      rw [frontier, interior_interior]
      exact ⟨hpcl, hpint⟩
    have hself : IsSelfConcordantOn (interior (K : Set E)) F :=
      ⟨1, hbarrier.toIsStandardSelfConcordantOn⟩
    let yDom : ℕ → interior (K : Set E) := fun n ↦ ⟨(y n).1, hy_dom n⟩
    have hblow :
        Tendsto (fun n ↦ F (y n).1) atTop atTop := by
      simpa [yDom] using hself.tendsto_atTop_of_tendsto_frontier yDom hp₁ hpfront
    have hupper : ∀ᶠ n in atTop, (y n).2 < p.2 + 1 := by
      have hnhds : Set.Iio (p.2 + 1) ∈ nhds p.2 := by
        apply IsOpen.mem_nhds isOpen_Iio
        simpa using add_lt_add_left (show (0 : ℝ) < 1 by norm_num) p.2
      exact hp₂.eventually hnhds
    have hlower : ∀ᶠ n in atTop, p.2 + 2 ≤ F (y n).1 :=
      Filter.tendsto_atTop.1 hblow (p.2 + 2)
    obtain ⟨n, hnlow, hnup⟩ := (hlower.and hupper).exists
    have hcontr : p.2 + 2 ≤ p.2 + 1 := le_trans hnlow (le_trans (hy_ineq n) hnup.le)
    have : False := by
      have h10 : (1 : ℝ) ≤ 0 := by linarith [hcontr]
      norm_num at h10
    exact this

-- Proof sketch: use the closed logarithmically-homogeneous cone data carried by `hFlog`
-- together with salience to rule out the flat directions that obstruct strict Hessian
-- positivity, and read the result on `interior K` through the owner
-- `HasPositiveDefiniteHessianOn (interior K) F`.
/-- A logarithmically homogeneous self-concordant barrier on the interior of a salient cone has
positive-definite Hessian on that interior domain. -/
theorem hasPositiveDefiniteHessianOn_of_logHomogeneousBarrier_of_salient
    (hFlog : IsLogarithmicallyHomogeneousOnWith K (ν : ℝ) F)
    (hbarrier : IsSelfConcordantBarrierOnWith (interior (K : Set E)) ν F)
    (hK : K.Salient) :
    HasPositiveDefiniteHessianOn (interior (K : Set E)) F := by
  -- Supply the closed-epigraph and no-affine-line bridge hypotheses required by Theorem 5.1.6.
  let hself : IsSelfConcordantOn (interior (K : Set E)) F := ⟨1, hbarrier.toIsStandardSelfConcordantOn⟩
  exact hself.hasPositiveDefiniteHessianOn_of_no_affine_line
    (constrainedEpigraph_isClosed_of_logHomogeneousBarrier hFlog hbarrier)
    (fun {x h} hh ↦
      interior_cone_has_no_affine_line_of_salient hFlog hK (x := x) (h := h) hh)

end BarrierCone

section BarrierCone

variable [FiniteDimensional ℝ E]
variable {K : ConvexCone ℝ E} {ν : NNReal} {F : E → ℝ}

local instance barrierConeFiniteDimensionalComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

-- Proof sketch: apply the owner bridge
-- `HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem` to the positive-definite Hessian
-- owner supplied by `hasPositiveDefiniteHessianOn_of_logHomogeneousBarrier_of_salient`.
/-- A logarithmically homogeneous self-concordant barrier on the interior of a salient cone has
nondegenerate Hessian at every interior point. -/
theorem hessian_det_ne_zero_of_logHomogeneousBarrier_of_salient
    (hFlog : IsLogarithmicallyHomogeneousOnWith K (ν : ℝ) F)
    (hbarrier : IsSelfConcordantBarrierOnWith (interior (K : Set E)) ν F)
    (hK : K.Salient)
    {x : E} (hx : x ∈ interior (K : Set E)) :
    (hessian F x).det ≠ 0 := by
  letI : HasPositiveDefiniteHessianOn (interior (K : Set E)) F :=
    hasPositiveDefiniteHessianOn_of_logHomogeneousBarrier_of_salient hFlog hbarrier hK
  exact HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx

end BarrierCone

section LogarithmicHomogeneity

variable [CompleteSpace E]
variable {K : ConvexCone ℝ E} {ν : ℝ} {F : E → ℝ}

/-- Helper for Lemma 5.4.3.2: the affine line `s ↦ x + s • d` has derivative `d`. -/
private theorem line_hasDerivAt (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate scalar multiplication and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Lemma 5.4.3.2: differentiating `F` along an affine line recovers the gradient
pairing with the line direction. -/
private theorem value_line_hasDerivAt
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x d : E} {t : ℝ} (hxt : x + t • d ∈ interior (K : Set E)) :
    HasDerivAt (fun s : ℝ ↦ F (x + s • d)) (inner ℝ (∇ F (x + t • d)) d) t := by
  -- Differentiate the ambient function `F` at the line point and compose with the affine line.
  have hC1 : ContDiffAt ℝ 1 F (x + t • d) := by
    have hnhds : interior (K : Set E) ∈ nhds (x + t • d) := by
      simpa [mem_interior_iff_mem_nhds] using hxt
    exact (hFlog.contDiffOn.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt hnhds
  simpa using
    ((hC1.differentiableAt one_ne_zero).hasGradientAt.hasFDerivAt.comp t
      (line_hasDerivAt x d t).hasFDerivAt).hasDerivAt

/-- Helper for Lemma 5.4.3.2: scalarizing the gradient along an affine line differentiates to the
corresponding Hessian pairing. -/
private theorem scalarized_gradient_line_hasDerivAt
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x d u : E} {t : ℝ} (hxt : x + t • d ∈ interior (K : Set E)) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ F (x + s • d)) u)
      (inner ℝ (hessian F (x + t • d) d) u) t := by
  -- Route correction: differentiate a scalarized gradient line restriction instead of using a
  -- global vector-valued within-derivative on `interior K`.
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ F) (x + t • d) := by
    have hnhds : interior (K : Set E) ∈ nhds (x + t • d) := by
      simpa [mem_interior_iff_mem_nhds] using hxt
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ F) (x + t • d) :=
      (hFlog.contDiffOn.contDiffAt hnhds).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ F) (x + t • d) := by
    -- Rewrite the gradient through the Riesz map to differentiate it.
    simpa [gradient, D] using D.differentiableAt.comp (x + t • d) hfderiv
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ F (x + s • d))
        ((hessian F (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Compose the derivative of the gradient with the derivative of the affine line.
    simpa using (hgrad.hasFDerivAt.comp t (line_hasDerivAt x d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ F (x + s • d)))
        (φ.comp ((hessian F (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose with the scalar functional `v ↦ ⟪v, u⟫`.
    simpa [φ] using ((φ.hasFDerivAt).comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

-- Proof sketch: differentiate the logarithmic scaling identity
-- `F (τ • x) = F x - ν log τ` with respect to `x`; the chain rule contributes the factor `τ` on
-- the left, and rearranging gives the `τ⁻¹` scaling of the gradient.
/-- Lemma 5.4.3.2 (1): logarithmic homogeneity rescales the gradient by `τ⁻¹`. -/
theorem gradient_pos_smul_eq_inv_smul
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ interior (K : Set E)) {τ : ℝ} (hτ : 0 < τ) :
    ∇ F (τ • x) = (1 / τ) • ∇ F x := by
  -- Differentiate the logarithmic scaling law along every affine line through `x`.
  refine ext_inner_right ℝ ?_
  intro u
  have hτx : τ • x ∈ interior (K : Set E) := pos_smul_mem_interior_cone hFlog hx hτ
  have hlineDom :
      ∀ᶠ s in nhds (0 : ℝ), x + s • u ∈ interior (K : Set E) := by
    have hnhds : interior (K : Set E) ∈ nhds x := by
      simpa [mem_interior_iff_mem_nhds] using hx
    exact (line_hasDerivAt x u 0).continuousAt (by simpa using hnhds)
  have heq :
      (fun s : ℝ ↦ F (τ • x + s • (τ • u))) =ᶠ[nhds (0 : ℝ)]
        fun s : ℝ ↦ F (x + s • u) - ν * Real.log τ := by
    filter_upwards [hlineDom] with s hs
    simpa [smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
      hFlog.logarithmic_scaling hs hτ
  have hleft :
      HasDerivAt (fun s : ℝ ↦ F (τ • x + s • (τ • u)))
        (inner ℝ (∇ F (τ • x)) (τ • u)) 0 :=
    by
      simpa using value_line_hasDerivAt hFlog (x := τ • x) (d := τ • u) (t := 0)
        (by simpa using hτx)
  have hright :
      HasDerivAt (fun s : ℝ ↦ F (x + s • u) - ν * Real.log τ)
        (inner ℝ (∇ F x) u) 0 := by
    simpa using (value_line_hasDerivAt hFlog (x := x) (d := u) (t := 0) (by simpa using hx)).sub_const
      (ν * Real.log τ)
  have hpair :
      inner ℝ (∇ F (τ • x)) (τ • u) = inner ℝ (∇ F x) u :=
    (hleft.congr_of_eventuallyEq heq.symm).unique hright
  have hscaled :
      inner ℝ (∇ F (τ • x)) u = (1 / τ) * inner ℝ (∇ F x) u := by
    have hpair' : τ * inner ℝ (∇ F (τ • x)) u = inner ℝ (∇ F x) u := by
      simpa [inner_smul_right] using hpair
    calc
      inner ℝ (∇ F (τ • x)) u = (1 / τ) * (τ * inner ℝ (∇ F (τ • x)) u) := by
        field_simp [hτ.ne']
      _ = (1 / τ) * inner ℝ (∇ F x) u := by rw [hpair']
  simpa [inner_smul_left] using hscaled

-- Proof sketch: differentiate the gradient scaling identity once more with respect to `x`; the
-- chain rule introduces a second factor of `τ`, yielding the `τ⁻²` scaling of the Hessian map.
/-- Lemma 5.4.3.2 (2): logarithmic homogeneity rescales the Hessian by `τ⁻²`. -/
theorem hessian_pos_smul_eq_inv_sq_smul
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ interior (K : Set E)) {τ : ℝ} (hτ : 0 < τ) :
    hessian F (τ • x) = (1 / τ ^ (2 : ℕ)) • hessian F x := by
  -- Differentiate the gradient scaling law along every affine line through `x`.
  ext v
  refine ext_inner_right ℝ ?_
  intro u
  have hτx : τ • x ∈ interior (K : Set E) := pos_smul_mem_interior_cone hFlog hx hτ
  have hlineDom :
      ∀ᶠ s in nhds (0 : ℝ), x + s • v ∈ interior (K : Set E) := by
    have hnhds : interior (K : Set E) ∈ nhds x := by
      simpa [mem_interior_iff_mem_nhds] using hx
    exact (line_hasDerivAt x v 0).continuousAt (by simpa using hnhds)
  have heq :
      (fun s : ℝ ↦ inner ℝ (∇ F (τ • x + s • (τ • v))) u) =ᶠ[nhds (0 : ℝ)]
        fun s : ℝ ↦ (1 / τ) * inner ℝ (∇ F (x + s • v)) u := by
    filter_upwards [hlineDom] with s hs
    simpa [smul_add, smul_smul, inner_smul_left, mul_comm, mul_left_comm, mul_assoc] using
      congrArg (fun z ↦ inner ℝ z u) (gradient_pos_smul_eq_inv_smul hFlog hs hτ)
  have hleft :
      HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ F (τ • x + s • (τ • v))) u)
        (inner ℝ (hessian F (τ • x) (τ • v)) u) 0 :=
    by
      simpa using scalarized_gradient_line_hasDerivAt hFlog
        (x := τ • x) (d := τ • v) (u := u) (t := 0) (by simpa using hτx)
  have hrightBase :
      HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ F (x + s • v)) u)
        (inner ℝ (hessian F x v) u) 0 :=
    by
      simpa using scalarized_gradient_line_hasDerivAt hFlog
        (x := x) (d := v) (u := u) (t := 0) (by simpa using hx)
  have hright :
      HasDerivAt (fun s : ℝ ↦ (1 / τ) * inner ℝ (∇ F (x + s • v)) u)
        ((1 / τ) * inner ℝ (hessian F x v) u) 0 := by
    simpa using hrightBase.const_mul (1 / τ)
  have hpair :
      inner ℝ (hessian F (τ • x) (τ • v)) u = (1 / τ) * inner ℝ (hessian F x v) u :=
    (hleft.congr_of_eventuallyEq heq.symm).unique hright
  have hpair' :
      τ * inner ℝ (hessian F (τ • x) v) u = (1 / τ) * inner ℝ (hessian F x v) u := by
    simpa [ContinuousLinearMap.map_smul, inner_smul_left] using hpair
  have hscaled :
      inner ℝ (hessian F (τ • x) v) u = (1 / τ ^ (2 : ℕ)) * inner ℝ (hessian F x v) u := by
    field_simp [pow_two, hτ.ne'] at hpair' ⊢
    exact hpair'
  simpa [ContinuousLinearMap.smul_apply, inner_smul_left] using hscaled

-- Proof sketch: differentiate the logarithmic scaling identity with respect to the scalar `τ`
-- along the ray `τ ↦ τ • x`, and then evaluate at `τ = 1`.
/-- Lemma 5.4.3.2 (3): the gradient pairing with the base point equals `-ν`. -/
theorem inner_gradient_self_eq_neg_parameter
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ interior (K : Set E)) :
    inner ℝ (∇ F x) x = -ν := by
  -- Differentiate the ray scaling identity at `s = 1`.
  have hleft :
      HasDerivAt (fun s : ℝ ↦ F ((0 : E) + s • x)) (inner ℝ (∇ F x) x) 1 :=
    by
      simpa using value_line_hasDerivAt hFlog (x := 0) (d := x) (t := 1) (by simpa using hx)
  have hright :
      HasDerivAt (fun s : ℝ ↦ F x - ν * Real.log s) (-ν) 1 := by
    have hlog : HasDerivAt (fun s : ℝ ↦ -ν * Real.log s) (-ν) 1 := by
      simpa using (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).const_mul (-ν)
    have hconst : HasDerivAt (fun _ : ℝ ↦ F x) 0 1 := by
      simpa using (hasDerivAt_const (x := (1 : ℝ)) (c := F x))
    convert hconst.add hlog using 1
    · ext s
      simp [sub_eq_add_neg]
    · ring
  have hpos : Set.Ioi (0 : ℝ) ∈ nhds (1 : ℝ) := by
    exact IsOpen.mem_nhds isOpen_Ioi (by norm_num)
  have heq :
      (fun s : ℝ ↦ F ((0 : E) + s • x)) =ᶠ[nhds (1 : ℝ)]
        fun s : ℝ ↦ F x - ν * Real.log s := by
    filter_upwards [hpos] with s hs
    simpa [zero_add] using hFlog.logarithmic_scaling hx hs
  exact (hleft.congr_of_eventuallyEq heq.symm).unique hright

-- Proof sketch: differentiate the scalar identity `⟪∇ F(x), x⟫ = -ν` in an arbitrary direction
-- `h`; symmetry of the Hessian then identifies the resulting linear functional with
-- `h ↦ ⟪h, ∇²F(x) x + ∇F(x)⟫`.
/-- Lemma 5.4.3.2 (4): applying the Hessian at `x` to `x` gives `-∇ F(x)`. -/
theorem hessian_apply_self_eq_neg_gradient
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ interior (K : Set E)) :
    hessian F x x = -∇ F x := by
  -- Differentiate the gradient scaling law along the ray at `s = 1`.
  refine ext_inner_right ℝ ?_
  intro u
  have hleft :
      HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ F ((0 : E) + s • x)) u)
        (inner ℝ (hessian F x x) u) 1 :=
    by
      simpa using scalarized_gradient_line_hasDerivAt hFlog
        (x := 0) (d := x) (u := u) (t := 1) (by simpa using hx)
  have hright :
      HasDerivAt (fun s : ℝ ↦ inner ℝ ((1 / s) • ∇ F x) u)
        (-inner ℝ (∇ F x) u) 1 := by
    have hinv : HasDerivAt (fun s : ℝ ↦ s⁻¹) (-1) 1 := by
      simpa using (hasDerivAt_inv (by norm_num : (1 : ℝ) ≠ 0))
    simpa [one_div, inner_smul_left, mul_comm] using hinv.const_mul (inner ℝ (∇ F x) u)
  have hpos : Set.Ioi (0 : ℝ) ∈ nhds (1 : ℝ) := by
    exact IsOpen.mem_nhds isOpen_Ioi (by norm_num)
  have heq :
      (fun s : ℝ ↦ inner ℝ (∇ F ((0 : E) + s • x)) u) =ᶠ[nhds (1 : ℝ)]
        fun s : ℝ ↦ inner ℝ ((1 / s) • ∇ F x) u := by
    filter_upwards [hpos] with s hs
    simpa [zero_add] using congrArg (fun z ↦ inner ℝ z u)
      (gradient_pos_smul_eq_inv_smul hFlog hx hs)
  simpa [inner_neg_left] using (hleft.congr_of_eventuallyEq heq.symm).unique hright

-- Proof sketch: pair the identity `∇²F(x) x = -∇F(x)` with `x`, then substitute
-- `⟪∇ F(x), x⟫ = -ν`.
/-- Lemma 5.4.3.2 (5): the Hessian quadratic form of `x` at `x` equals `ν`. -/
theorem inner_hessian_apply_self_self_eq_parameter
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ interior (K : Set E)) :
    inner ℝ (hessian F x x) x = ν := by
  -- Pair the Hessian identity with `x` and substitute the Euler identity.
  rw [hessian_apply_self_eq_neg_gradient hFlog hx]
  have hEuler : inner ℝ (∇ F x) x = -ν :=
    inner_gradient_self_eq_neg_parameter hFlog hx
  simpa [inner_neg_left] using congrArg Neg.neg hEuler

end LogarithmicHomogeneity

section InverseHessian

variable [FiniteDimensional ℝ E]
variable {K : ConvexCone ℝ E} {ν : NNReal} {F : E → ℝ}

local instance inverseHessianFiniteDimensionalComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

-- Proof sketch: the logarithmically homogeneous salient-cone barrier hypothesis gives the owner
-- `HasPositiveDefiniteHessianOn (interior K) F`, so the Hessian at `x` has its canonical inverse
-- `(hessian F x).inverse`. Solve `∇²F(x) x = -∇F(x)` for `x` using that inverse, then substitute
-- the result into `⟪∇ F(x), x⟫ = -ν`.
/-- Lemma 5.4.3.2 (6): the inverse-Hessian pairing of the gradient with itself equals `ν`. -/
theorem inner_gradient_inverseHessian_gradient_eq_parameter
    (hFlog : IsLogarithmicallyHomogeneousOnWith K (ν : ℝ) F)
    (hbarrier : IsSelfConcordantBarrierOnWith (interior (K : Set E)) ν F)
    (hK : K.Salient)
    {x : E} (hx : x ∈ interior (K : Set E)) :
    inner ℝ (∇ F x) ((hessian F x).inverse (∇ F x)) = (ν : ℝ) := by
  have hDet : (hessian F x).det ≠ 0 :=
    hessian_det_ne_zero_of_logHomogeneousBarrier_of_salient hFlog hbarrier hK hx
  have hInv : (hessian F x).IsInvertible :=
    hessian_isInvertible_of_det_ne_zero hDet
  have hInverseGradient :
      (hessian F x).inverse (∇ F x) = -x := by
    -- Solve the Hessian identity `∇²F(x) x = -∇F(x)` using the inverse Hessian.
    have happly : (hessian F x).inverse (-∇ F x) = x := by
      simpa [hessian_apply_self_eq_neg_gradient hFlog hx] using hInv.inverse_apply_self x
    calc
      (hessian F x).inverse (∇ F x) = -((hessian F x).inverse (-∇ F x)) := by simp
      _ = -x := by rw [happly]
  have hEuler : inner ℝ (∇ F x) x = -((ν : ℝ)) :=
    inner_gradient_self_eq_neg_parameter hFlog hx
  calc
    inner ℝ (∇ F x) ((hessian F x).inverse (∇ F x)) = inner ℝ (∇ F x) (-x) := by
      rw [hInverseGradient]
    _ = (ν : ℝ) := by
      simpa [inner_neg_right] using congrArg Neg.neg hEuler

end InverseHessian

end
