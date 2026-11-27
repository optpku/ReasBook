/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace VariationalRegularization
namespace CylinderFlux

/-- Product-coordinate divergence, with the last coordinate singled out. -/
@[expose] def divProd {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin n) × ℝ)
    (q : EuclideanSpace ℝ (Fin n) × ℝ) : ℝ :=
  (∑ j : Fin n, (fderiv ℝ F q (EuclideanSpace.single j 1, 0)).1 j) +
    (fderiv ℝ F q (0, 1)).2

private lemma integral_fderiv_eq_zero {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, fderiv ℝ g x v) = 0 := by
  have hd : Integrable (fun x ↦ fderiv ℝ g x v) :=
    ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : EuclideanSpace ℝ (Fin n) ↦ (1 : ℝ)) (g := g) (v := v)
    (by simp)
    (by simpa using hd)
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hc)
    (fun _ _ ↦ differentiableAt_const _) (fun _ _ ↦ hg.differentiable one_ne_zero _)
  simpa using h

private lemma compact_slice_left {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} (hc : HasCompactSupport g) (t : ℝ) :
    HasCompactSupport (fun z ↦ g (z, t)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hc.isCompact.image continuous_fst)
  intro z hz
  exact ⟨(z, t), subset_tsupport _ hz, rfl⟩

private lemma compact_slice_right {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} (hc : HasCompactSupport g)
    (z : EuclideanSpace ℝ (Fin n)) : HasCompactSupport (fun t ↦ g (z, t)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hc.isCompact.image continuous_snd)
  intro t ht
  exact ⟨(z, t), subset_tsupport _ ht, rfl⟩

private lemma horizontal_integral_eq_zero {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ q in (univ : Set (EuclideanSpace ℝ (Fin n))) ×ˢ Iic (0 : ℝ),
      fderiv ℝ g q (v, 0)) = 0 := by
  have hd : Integrable (fun q ↦ fderiv ℝ g q (v, 0)) :=
    ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (v, 0))
  have hi : Integrable (fun q ↦ fderiv ℝ g q (v, 0))
      (volume.prod (volume.restrict (Iic (0 : ℝ)))) := by
    rw [Measure.volume_eq_prod] at hd
    exact hd.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [integral_prod_symm _ hi]
  have hslice (t : ℝ) : (∫ z, fderiv ℝ g (z, t) (v, 0)) = 0 := by
    have hgt : ContDiff ℝ 1 (fun z ↦ g (z, t)) :=
      hg.comp (contDiff_id.prodMk contDiff_const)
    have hder (z : EuclideanSpace ℝ (Fin n)) :
        fderiv ℝ (fun z ↦ g (z, t)) z v = fderiv ℝ g (z, t) (v, 0) := by
      have hin : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin n) ↦ (w, t))
          ((ContinuousLinearMap.id ℝ _).prod 0) z :=
        (hasFDerivAt_id z).prodMk (hasFDerivAt_const t z)
      have h := (hg.differentiable one_ne_zero (z, t)).hasFDerivAt.comp z hin
      simpa [Function.comp_def] using congrArg (fun L ↦ L v) h.fderiv
    simp_rw [← hder]
    exact integral_fderiv_eq_zero hgt (compact_slice_left hc t) v
  simp_rw [hslice]
  simp

private lemma vertical_integral_eq_top {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) :
    (∫ q in (univ : Set (EuclideanSpace ℝ (Fin n))) ×ˢ Iic (0 : ℝ),
      fderiv ℝ g q (0, 1)) = ∫ z, g (z, 0) := by
  have hd : Integrable (fun q ↦ fderiv ℝ g q (0, 1)) :=
    ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (0, 1))
  rw [Measure.volume_eq_prod, setIntegral_prod _ (by
    rw [← Measure.volume_eq_prod]
    exact hd.integrableOn), setIntegral_univ]
  apply integral_congr_ae
  filter_upwards [] with z
  have hgt : ContDiff ℝ 1 (fun t ↦ g (z, t)) :=
    hg.comp (contDiff_const.prodMk contDiff_id)
  have hder (t : ℝ) : deriv (fun t ↦ g (z, t)) t = fderiv ℝ g (z, t) (0, 1) := by
    have hin : HasDerivAt (fun s : ℝ ↦ (z, s)) (0, 1) t :=
      (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
    exact ((hg.differentiable one_ne_zero (z, t)).hasFDerivAt.comp_hasDerivAt t hin).deriv
  simp_rw [← hder]
  exact HasCompactSupport.integral_Iic_deriv_eq hgt (compact_slice_right hc z) 0

private lemma horizontal_projection_derivative {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin n) × ℝ}
    (hF : ContDiff ℝ 1 F) (q : EuclideanSpace ℝ (Fin n) × ℝ)
    (v : EuclideanSpace ℝ (Fin n) × ℝ) (j : Fin n) :
    fderiv ℝ (fun q ↦ (F q).1 j) q v = (fderiv ℝ F q v).1 j := by
  have h := (EuclideanSpace.proj j).hasFDerivAt.comp q
    (hF.differentiable one_ne_zero q).hasFDerivAt.fst
  simpa [Function.comp_def] using congrArg (fun L ↦ L v) h.fderiv

private lemma vertical_projection_derivative {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin n) × ℝ}
    (hF : ContDiff ℝ 1 F) (q : EuclideanSpace ℝ (Fin n) × ℝ)
    (v : EuclideanSpace ℝ (Fin n) × ℝ) :
    fderiv ℝ (fun q ↦ (F q).2) q v = (fderiv ℝ F q v).2 := by
  simpa using congrArg (fun L ↦ L v)
    (hF.differentiable one_ne_zero q).hasFDerivAt.snd.fderiv

private lemma horizontal_derivative_integrable {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin n) × ℝ}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) (j : Fin n) :
    Integrable (fun q ↦ (fderiv ℝ F q (EuclideanSpace.single j 1, 0)).1 j) := by
  have hcont : Continuous (fun q ↦ (fderiv ℝ F q (EuclideanSpace.single j 1, 0)).1 j) := (EuclideanSpace.proj j).continuous.comp
    (((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const).fst)
  have hcompact := (hc.fderiv_apply ℝ (EuclideanSpace.single j 1, 0)).comp_left
    (g := fun y ↦ y.1 j) (by simp)
  exact hcont.integrable_of_hasCompactSupport hcompact

private lemma vertical_derivative_integrable {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin n) × ℝ}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) :
    Integrable (fun q ↦ (fderiv ℝ F q (0, 1)).2) := by
  have hcont : Continuous (fun q ↦ (fderiv ℝ F q (0, 1)).2) := ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const).snd
  have hcompact := (hc.fderiv_apply ℝ (0, 1)).comp_left (g := Prod.snd) rfl
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- The compact-support divergence formula for a lower product half-space. -/
theorem integral_divProd_halfSpace {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin n) × ℝ}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) :
    (∫ q in (univ : Set (EuclideanSpace ℝ (Fin n))) ×ˢ Iic (0 : ℝ),
      divProd F q) = ∫ z, (F (z, 0)).2 := by
  have hj (j : Fin n) :
      (∫ q in (univ : Set (EuclideanSpace ℝ (Fin n))) ×ˢ Iic (0 : ℝ),
        (fderiv ℝ F q (EuclideanSpace.single j 1, 0)).1 j) = 0 := by
    have hg : ContDiff ℝ 1 (fun q ↦ (F q).1 j) :=
      by simpa [Function.comp_def] using (EuclideanSpace.proj j).contDiff.comp hF.fst
    have hgc : HasCompactSupport (fun q ↦ (F q).1 j) :=
      by simpa only [Function.comp_def] using hc.comp_left (g := fun y ↦ y.1 j) (by simp)
    simpa only [horizontal_projection_derivative hF] using
      horizontal_integral_eq_zero hg hgc (EuclideanSpace.single j 1)
  have hv :
      (∫ q in (univ : Set (EuclideanSpace ℝ (Fin n))) ×ˢ Iic (0 : ℝ),
        (fderiv ℝ F q (0, 1)).2) = ∫ z, (F (z, 0)).2 := by
    simpa only [vertical_projection_derivative hF] using
      vertical_integral_eq_top hF.snd (hc.comp_left (g := Prod.snd) rfl)
  simp only [divProd]
  rw [integral_add (by exact integrable_finsetSum _ fun j _ ↦
      (horizontal_derivative_integrable hF hc j).integrableOn)
    (vertical_derivative_integrable hF hc).integrableOn]
  rw [integral_finsetSum _ fun j _ ↦ (horizontal_derivative_integrable hF hc j).integrableOn]
  simp_rw [hj]
  simpa using hv

/-- Compact support in a product cylinder removes all lateral and bottom fluxes.
Only inclusion in the closed cylinder is needed, because derivatives vanish outside
`tsupport F`. -/
theorem integral_divProd_cylinder {n : ℕ} {R : ℝ}
    {F : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin n) × ℝ}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R ×ˢ Icc (-R) R) :
    (∫ q in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R ×ˢ Icc (-R) 0,
      divProd F q) =
      ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, (F (z, 0)).2 := by
  have htrim :
      (∫ q in (univ : Set (EuclideanSpace ℝ (Fin n))) ×ˢ Iic (0 : ℝ), divProd F q) =
        ∫ q in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R ×ˢ Icc (-R) 0,
          divProd F q := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (MeasurableSet.prod MeasurableSet.univ measurableSet_Iic)
    · intro q hq
      exact ⟨mem_univ _, hq.2.2⟩
    · intro q hq
      have hn : q ∉ tsupport F := by
        intro h
        exact hq.2 ⟨(hs h).1, (hs h).2.1, hq.1.2⟩
      simp [divProd, fderiv_of_notMem_tsupport ℝ hn]
  have htop :
      (∫ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, (F (z, 0)).2) =
        ∫ z, (F (z, 0)).2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hn : (z, (0 : ℝ)) ∉ tsupport F := fun h ↦ hz (hs h).1
    simp [image_eq_zero_of_notMem_tsupport hn]
  rw [← htrim, integral_divProd_halfSpace hF hc, htop]

/-- The version with support strictly inside the cylinder. -/
theorem integral_divProd_cylinder_of_tsupport_subset_interior {n : ℕ} {R : ℝ}
    {F : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin n) × ℝ}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ interior
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R ×ˢ Icc (-R) R)) :
    (∫ q in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R ×ˢ Icc (-R) 0,
      divProd F q) =
      ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, (F (z, 0)).2 :=
  integral_divProd_cylinder hF hc (hs.trans interior_subset)

end CylinderFlux
end VariationalRegularization
