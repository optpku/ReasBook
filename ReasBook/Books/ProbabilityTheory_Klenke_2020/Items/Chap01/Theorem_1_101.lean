/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped ENNReal

universe u v

abbrev EuclideanPoint (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A finite cover by sets that are each open or closed. -/
structure FiniteOpenClosedCover (α : Type u) [TopologicalSpace α] where
  Index : Type v
  instFintypeIndex : Fintype Index
  pieces : Index → Set α
  pieces_topology : ∀ i, IsOpen (pieces i) ∨ IsClosed (pieces i)
  iUnion_eq_univ : (⋃ i, pieces i) = univ

attribute [instance] FiniteOpenClosedCover.instFintypeIndex

/-- `f` is continuous on each piece of the given finite open/closed cover. -/
def ContinuousOnCover {α : Type u} {β : Type v} [TopologicalSpace α] [TopologicalSpace β]
    (f : α → β) (cover : FiniteOpenClosedCover α) : Prop :=
  ∀ i, ContinuousOn f (cover.pieces i)

/-- Helper for Theorem 1.101: a density that is continuous, or continuous on each member of a
finite open/closed cover, is Borel measurable. -/
lemma regularDensityMeasurable {n : ℕ} (f : EuclideanPoint n → NNReal)
    (hf_regular :
      Continuous f ∨
        ∃ cover : FiniteOpenClosedCover (EuclideanPoint n), ContinuousOnCover f cover) :
    Measurable f := by
  rcases hf_regular with hcont | ⟨cover, hcover⟩
  · exact hcont.measurable
  · classical
    let g : ∀ i, cover.pieces i → NNReal := fun i ↦ (cover.pieces i).restrict f
    have hpieces_meas : ∀ i, MeasurableSet (cover.pieces i) := fun i ↦
      (cover.pieces_topology i).elim IsOpen.measurableSet IsClosed.measurableSet
    have hg_meas : ∀ i, Measurable (g i) := fun i ↦ ((hcover i).restrict).measurable
    have hg_compat :
        ∀ (i j) (x : EuclideanPoint n) (hxi : x ∈ cover.pieces i) (hxj : x ∈ cover.pieces j),
          g i ⟨x, hxi⟩ = g j ⟨x, hxj⟩ := by
      intro i j x hxi hxj
      rfl
    have hcover_meas :
        Measurable (Set.liftCover cover.pieces g hg_compat cover.iUnion_eq_univ) :=
      measurable_liftCover cover.pieces hpieces_meas g hg_meas hg_compat cover.iUnion_eq_univ
    have hcover_eq :
        Set.liftCover cover.pieces g hg_compat cover.iUnion_eq_univ = f := by
      funext x
      rcases Set.iUnion_eq_univ_iff.mp cover.iUnion_eq_univ x with ⟨i, hi⟩
      exact Set.liftCover_of_mem hi
    rw [← hcover_eq]
    exact hcover_meas

-- Semantic recall: compare `MeasureTheory.restrict_map_withDensity_abs_det_fderiv_eq_addHaar`.
-- Mathlib's Jacobian API provides related change-of-variables formulas; this item keeps the
-- textbook inverse-density pushforward statement from the source text.
/-- Theorem 1.101 (Transformation formula in `ℝ^n`). If `μ` has a continuous or piecewise
continuous density `f : ℝⁿ → [0, ∞)`, `μ (Aᶜ) = 0`, and `φ : A → B` is a `C¹` bijection with
inverse `ψ` whose Jacobian determinant does not vanish on `A`, then the pushforward measure has
density `f (ψ y) / |det Dφ (ψ y)|` on `B`, with density `0` outside `B`. -/
theorem transformation_formula_in_euclidean_space {n : ℕ}
    (f : EuclideanPoint n → NNReal)
    (hf_regular :
      Continuous f ∨
        ∃ cover : FiniteOpenClosedCover (EuclideanPoint n), ContinuousOnCover f cover)
    {A B : Set (EuclideanPoint n)}
    (hA_topo : IsOpen A ∨ IsClosed A)
    (hA_null : (volume.withDensity fun x ↦ (f x : ENNReal)) Aᶜ = 0)
    (hB_topo : IsOpen B ∨ IsClosed B)
    (φ ψ : EuclideanPoint n → EuclideanPoint n)
    (hφ_bij : BijOn φ A B)
    (hψ_inv : InvOn ψ φ A B)
    (hφ_contdiff : ContDiffOn ℝ 1 φ A)
    (hφ_det_ne_zero : ∀ x ∈ A, (fderivWithin ℝ φ A x).det ≠ 0) :
    Measure.map φ (volume.withDensity fun x ↦ (f x : ENNReal)) =
      volume.withDensity
        (B.indicator fun y ↦
          ENNReal.ofReal
            ((f (ψ y) : ℝ) / |(fderivWithin ℝ φ A (ψ y)).det|)) := by
  classical
  let ν : Measure (EuclideanPoint n) := volume.withDensity fun x ↦ (f x : ENNReal)
  let ρ : EuclideanPoint n → ENNReal := fun y ↦
    ENNReal.ofReal ((f (ψ y) : ℝ) / |(fderivWithin ℝ φ A (ψ y)).det|)
  let u : EuclideanPoint n → EuclideanPoint n := A.piecewise φ 0
  have hA_meas : MeasurableSet A := hA_topo.elim IsOpen.measurableSet IsClosed.measurableSet
  have hB_meas : MeasurableSet B := hB_topo.elim IsOpen.measurableSet IsClosed.measurableSet
  have hf_meas : Measurable f := regularDensityMeasurable f hf_regular
  have hφ_hasFDeriv : ∀ x ∈ A, HasFDerivWithinAt φ (fderivWithin ℝ φ A x) A x := by
    intro x hx
    exact ((hφ_contdiff.contDiffWithinAt hx).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
  -- Replace `φ` by a measurable extension away from `A`; the source measure is concentrated on `A`.
  have hu_meas : Measurable u := by
    refine ContinuousOn.measurable_piecewise hφ_contdiff.continuousOn continuous_zero.continuousOn
      hA_meas
  have hA_ae : ∀ᵐ x ∂ν, x ∈ A := by
    rw [ae_iff]
    simpa [ν] using hA_null
  have hφu : φ =ᵐ[ν] u := hA_ae.mono fun x hx ↦ by simp [u, hx]
  have hmap_u : Measure.map φ ν = Measure.map u ν := Measure.map_congr hφu
  apply Measure.ext fun s hs ↦ ?_
  let g : EuclideanPoint n → ENNReal := s.indicator (B.indicator ρ)
  -- The right-hand side measure on `s` is the Jacobian target integral with test function `g`.
  have hright :
      volume.withDensity (B.indicator ρ) s = ∫⁻ y in B, g y ∂volume := by
    rw [withDensity_apply _ hs, ← lintegral_indicator hs, ← lintegral_indicator hB_meas]
    refine lintegral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y
    by_cases hyB : y ∈ B <;> by_cases hys : y ∈ s <;> simp [g, ρ, hyB, hys]
  -- Apply mathlib's change-of-variables theorem to the indicator test function.
  have hchange :
      ∫⁻ y in B, g y ∂volume =
        ∫⁻ x in A, ENNReal.ofReal |(fderivWithin ℝ φ A x).det| * g (φ x) ∂volume := by
    simpa [g, hφ_bij.image_eq] using
      (MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
        (μ := volume) (s := A) (f := φ) (f' := fun x ↦ fderivWithin ℝ φ A x) hA_meas
        hφ_hasFDeriv hφ_bij.injOn g)
  -- On `A`, the transformed integrand collapses to the original density on the preimage of `s`.
  have hleft :
      Measure.map φ ν s =
        ∫⁻ x in A, ENNReal.ofReal |(fderivWithin ℝ φ A x).det| * g (φ x) ∂volume := by
    calc
      Measure.map φ ν s = Measure.map u ν s := by rw [hmap_u]
      _ = Measure.map u (ν.restrict A) s := by
        rw [Measure.restrict_eq_self_of_ae_mem hA_ae]
      _ = (ν.restrict A) (u ⁻¹' s) := by
        rw [Measure.map_apply hu_meas hs]
      _ = ((volume.restrict A).withDensity fun x ↦ (f x : ENNReal)) (u ⁻¹' s) := by
        simpa [ν] using
          congrArg (fun μ : Measure (EuclideanPoint n) => μ (u ⁻¹' s))
            (restrict_withDensity (μ := volume) (s := A) hA_meas (fun x ↦ (f x : ENNReal)))
      _ = ∫⁻ x in u ⁻¹' s, (f x : ENNReal) ∂(volume.restrict A) := by
        rw [withDensity_apply _ (hu_meas hs)]
      _ = ∫⁻ x, Set.indicator (u ⁻¹' s) (fun x ↦ (f x : ENNReal)) x ∂(volume.restrict A) := by
        rw [lintegral_indicator (μ := volume.restrict A) (hu_meas hs)]
      _ = ∫⁻ x,
            ENNReal.ofReal |(fderivWithin ℝ φ A x).det| * g (φ x) ∂(volume.restrict A) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem hA_meas] with x hxA
        have hBx : φ x ∈ B := hφ_bij.mapsTo hxA
        have hψx : ψ (φ x) = x := hψ_inv.1 hxA
        have hdet : |(fderivWithin ℝ φ A x).det| ≠ 0 := abs_ne_zero.mpr (hφ_det_ne_zero x hxA)
        have hdiv_nonneg :
            0 ≤ (f (ψ (φ x)) : ℝ) / |(fderivWithin ℝ φ A (ψ (φ x))).det| := by
          exact div_nonneg (NNReal.coe_nonneg _) (abs_nonneg _)
        by_cases hxs : φ x ∈ s
        · have hxus : x ∈ u ⁻¹' s := by simpa [u, hxA] using hxs
          have hcalc :
              ENNReal.ofReal |(fderivWithin ℝ φ A x).det| *
                  ENNReal.ofReal ((f x : ℝ) / |(fderivWithin ℝ φ A x).det|) =
                (f x : ENNReal) := by
            rw [← ENNReal.ofReal_mul (abs_nonneg _)]
            rw [mul_div_cancel₀ _ hdet]
            simp
          rw [Set.indicator_of_mem hxus]
          rw [show g (φ x) = ENNReal.ofReal ((f x : ℝ) / |(fderivWithin ℝ φ A x).det|) by
            simp [g, ρ, hBx, hxs, hψx]]
          exact hcalc.symm
        · have hxus : x ∉ u ⁻¹' s := by simpa [u, hxA] using hxs
          rw [Set.indicator_of_notMem hxus]
          simp [g, ρ, hxs]
      _ = ∫⁻ x in A, ENNReal.ofReal |(fderivWithin ℝ φ A x).det| * g (φ x) ∂volume := by
        rfl
  calc
    Measure.map φ ν s = ∫⁻ x in A, ENNReal.ofReal |(fderivWithin ℝ φ A x).det| * g (φ x) ∂volume :=
      hleft
    _ = ∫⁻ y in B, g y ∂volume := hchange.symm
    _ = volume.withDensity (B.indicator ρ) s := hright.symm
