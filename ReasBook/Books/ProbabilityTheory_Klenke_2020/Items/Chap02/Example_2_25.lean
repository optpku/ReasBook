/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Corollary_2_22

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

universe u v

variable {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]

/-- Helper for Example 2.25: a volume-preserving measurable equivalence transports a
`withDensity` law by precomposing the density with the inverse equivalence. -/
private lemma mapWithDensityOfVolumePreserving {α β : Type*}
    [MeasureSpace α] [MeasureSpace β]
    (e : α ≃ᵐ β) (hpres : MeasurePreserving e volume volume)
    (g : α → ENNReal) (hg : Measurable g) :
    Measure.map e (volume.withDensity g) =
      volume.withDensity (fun y : β ↦ g (e.symm y)) := by
  -- Compare the two measures on measurable sets and move the set integral through `e`.
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ hs,
    withDensity_apply _ (e.measurable hs)]
  simpa using hpres.setLIntegral_comp_preimage hs (hg.comp e.symm.measurable)

/-- Helper for Example 2.25: pushing a `withDensity` law on a singleton function space through
`MeasurableEquiv.funUnique` recovers the corresponding density law on `ℝ`. -/
private lemma mapWithDensityFunUnique {α : Type*} [Unique α] (g : (α → ℝ) → ENNReal)
    (hg : Measurable g) :
    Measure.map (MeasurableEquiv.funUnique α ℝ) (volume.withDensity g) =
      volume.withDensity (fun t : ℝ ↦ g (fun _ ↦ t)) := by
  -- Specialize the general transport lemma to the singleton function-space equivalence.
  simpa using
    mapWithDensityOfVolumePreserving
      (e := MeasurableEquiv.funUnique α ℝ)
      (hpres := volume_preserving_funUnique α ℝ)
      g hg

/-- Helper for Example 2.25: the singleton coordinate map obtained from
`MeasurableEquiv.funUnique` and `Finset.restrict` is exactly `X i`. -/
private lemma funUnique_comp_singletonRestrict_eq {Ω : Type*} {ι : Type*} {X : ι → Ω → ℝ} (i : ι) :
    (MeasurableEquiv.funUnique ({i} : Finset ι) ℝ) ∘
        (fun ω ↦ ({i} : Finset ι).restrict (X · ω)) = X i := by
  classical
  -- Unfold the singleton restriction and evaluate its unique coordinate.
  funext ω
  simp [Function.comp]

/-- Helper for Example 2.25: on a singleton index set, the product Gaussian density is the
corresponding one-dimensional Gaussian density. -/
private lemma singletonGaussianProductDensity_eq_gaussianPDFReal {m σ : ι → ℝ}
    (hσ : ∀ i, 0 < σ i ^ 2) (i : ι) (x : ({i} : Finset ι) → ℝ) :
    ∏ j : ({i} : Finset ι), gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ (x j) =
      gaussianPDFReal (m i) ⟨σ i ^ 2, le_of_lt (hσ i)⟩
        ((MeasurableEquiv.funUnique ({i} : Finset ι) ℝ) x) := by
  classical
  simp

/-- Helper for Example 2.25: the finite-dimensional Gaussian product density, packaged as an
`NNReal`-valued function for Corollary 2.22. -/
private def gaussianProductDensity {m σ : ι → ℝ} (hσ : ∀ i, 0 < σ i ^ 2)
    (J : Finset ι) (x : J → ℝ) : NNReal :=
  ⟨∏ j : J, gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ (x j),
    Finset.prod_nonneg fun _ _ ↦ gaussianPDFReal_nonneg _ _ _⟩

/-- Helper for Example 2.25: the finite-dimensional Gaussian product density is continuous as an
`NNReal`-valued function. -/
private lemma jointGaussianDensityContinuous {m σ : ι → ℝ} (hσ : ∀ i, 0 < σ i ^ 2)
    (J : Finset ι) :
    Continuous (gaussianProductDensity (m := m) (σ := σ) hσ J) := by
  -- Wrap the real-valued product density once after proving continuity of the real product.
  refine Continuous.subtype_mk
    (by
      refine continuous_finset_prod _ fun j _ ↦ ?_
      rw [gaussianPDFReal_def]
      fun_prop)
    (fun x ↦ Finset.prod_nonneg fun j _ ↦ gaussianPDFReal_nonneg _ _ _)

/-- Helper for Example 2.25: the given joint density hypothesis is exactly the `withDensity`
statement for `gaussianProductDensity`. -/
private lemma jointLaw_eq_withDensity_gaussianProductDensity {P : Measure Ω} {X : ι → Ω → ℝ}
    {m σ : ι → ℝ} (hσ : ∀ i, 0 < σ i ^ 2)
    (h_density :
      ∀ J : Finset ι,
        P.map (fun ω ↦ J.restrict (X · ω)) =
          volume.withDensity
            (fun x : J → ℝ ↦
              ENNReal.ofReal
                (∏ j : J, gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ (x j)))) :
    ∀ J : Finset ι,
      P.map (fun ω ↦ J.restrict (X · ω)) =
        volume.withDensity
          (fun x ↦ (gaussianProductDensity (m := m) (σ := σ) hσ J x : ENNReal)) := by
  intro J
  -- Repackage the real-valued density as the corresponding `NNReal`-valued function.
  calc
    P.map (fun ω ↦ J.restrict (X · ω))
        = volume.withDensity
            (fun x : J → ℝ ↦
              ENNReal.ofReal
                (∏ j : J, gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ (x j))) :=
          h_density J
    _ = volume.withDensity
          (fun x ↦ (gaussianProductDensity (m := m) (σ := σ) hσ J x : ENNReal)) := by
          refine withDensity_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
          let y : NNReal := gaussianProductDensity (m := m) (σ := σ) hσ J x
          have hy : 0 ≤ ∏ j : J, gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ (x j) := by
            exact Finset.prod_nonneg fun j _ ↦ gaussianPDFReal_nonneg _ _ _
          simpa [gaussianProductDensity, y, hy] using ENNReal.ofReal_eq_coe_nnreal hy

/-- Helper for Example 2.25: the Gaussian product density factors into its singleton coordinate
densities. -/
private lemma gaussianProductDensity_factorizes {m σ : ι → ℝ} (hσ : ∀ i, 0 < σ i ^ 2) :
    ∀ (J : Finset ι) (x : J → ℝ),
      gaussianProductDensity (m := m) (σ := σ) hσ J x =
        ∏ j : J, gaussianProductDensity (m := m) (σ := σ) hσ ({j.1} : Finset ι) (fun _ ↦ x j) := by
  intro J x
  -- The singleton factors are exactly the coordinate Gaussian pdfs.
  apply Subtype.ext
  have hleft :
      ((gaussianProductDensity (m := m) (σ := σ) hσ J x : NNReal) : ℝ) =
        ∏ j : J, gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ (x j) := rfl
  have hright :
      (((∏ j : J, gaussianProductDensity (m := m) (σ := σ) hσ ({j.1} : Finset ι) (fun _ ↦ x j)) :
          NNReal) : ℝ) =
        ∏ j : J,
          ((gaussianProductDensity (m := m) (σ := σ) hσ ({j.1} : Finset ι) (fun _ ↦ x j) :
            NNReal) : ℝ) := by
      simp
  calc
    ((gaussianProductDensity (m := m) (σ := σ) hσ J x : NNReal) : ℝ)
        = ∏ j : J, gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ (x j) := hleft
    _ = ∏ j : J,
          ((gaussianProductDensity (m := m) (σ := σ) hσ ({j.1} : Finset ι) (fun _ ↦ x j) :
            NNReal) : ℝ) := by
          refine Finset.prod_congr rfl ?_
          intro j hj
          have hsingleton :
              ((gaussianProductDensity (m := m) (σ := σ) hσ ({j.1} : Finset ι) (fun _ ↦ x j) :
                  NNReal) : ℝ) =
                ∏ k : ({j.1} : Finset ι),
                  gaussianPDFReal (m k) ⟨σ k ^ 2, le_of_lt (hσ k)⟩ ((fun _ ↦ x j) k) := rfl
          rw [hsingleton]
          simp
    _ = (((∏ j : J, gaussianProductDensity (m := m) (σ := σ) hσ ({j.1} : Finset ι) (fun _ ↦ x j)) :
          NNReal) : ℝ) := hright.symm

/-- Helper for Example 2.25: the singleton case of the joint density hypothesis yields the
one-dimensional Gaussian law for `X i`. -/
private lemma singletonJointLaw_eq_gaussianReal {P : Measure Ω} {X : ι → Ω → ℝ}
    {m σ : ι → ℝ} (hX : ∀ i, Measurable (X i)) (hσ : ∀ i, 0 < σ i ^ 2)
    (h_density :
      ∀ J : Finset ι,
        P.map (fun ω ↦ J.restrict (X · ω)) =
          volume.withDensity
            (fun x : J → ℝ ↦
              ENNReal.ofReal
                (∏ j : J, gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ (x j))))
    (i : ι) :
    P.map (X i) = gaussianReal (m i) ⟨σ i ^ 2, le_of_lt (hσ i)⟩ := by
  classical
  have hrestrict_meas :
      Measurable (fun ω ↦ ({i} : Finset ι).restrict (X · ω)) := by
    fun_prop
  have hsingleton_meas :
      Measurable (fun x : ({i} : Finset ι) → ℝ ↦
        ENNReal.ofReal
          (∏ j : ({i} : Finset ι),
            gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ (x j))) := by
    -- The singleton density is measurable as a finite product of measurable Gaussian pdfs.
    refine Measurable.ennreal_ofReal ?_
    exact Finset.measurable_prod Finset.univ fun j _ ↦
      (measurable_gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩).comp
        (continuous_apply j).measurable
  have hpush :=
    congrArg (Measure.map (MeasurableEquiv.funUnique ({i} : Finset ι) ℝ))
      (h_density ({i} : Finset ι))
  have hpush' :
      P.map
          ((MeasurableEquiv.funUnique ({i} : Finset ι) ℝ) ∘
            (fun ω ↦ ({i} : Finset ι).restrict (X · ω))) =
        Measure.map (MeasurableEquiv.funUnique ({i} : Finset ι) ℝ)
          (volume.withDensity
            (fun x : ({i} : Finset ι) → ℝ ↦
              ENNReal.ofReal
                (∏ j : ({i} : Finset ι),
                  gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ (x j)))) := by
    -- Push the singleton joint law through `funUnique`.
    calc
      P.map
          ((MeasurableEquiv.funUnique ({i} : Finset ι) ℝ) ∘
            (fun ω ↦ ({i} : Finset ι).restrict (X · ω)))
          =
          Measure.map (MeasurableEquiv.funUnique ({i} : Finset ι) ℝ)
            (P.map (fun ω ↦ ({i} : Finset ι).restrict (X · ω))) := by
              symm
              exact Measure.map_map
                (MeasurableEquiv.funUnique ({i} : Finset ι) ℝ).measurable hrestrict_meas
      _ = Measure.map (MeasurableEquiv.funUnique ({i} : Finset ι) ℝ)
            (volume.withDensity
              (fun x : ({i} : Finset ι) → ℝ ↦
                ENNReal.ofReal
                  (∏ j : ({i} : Finset ι),
                    gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ (x j)))) := hpush
  have hpush'' :
      P.map (X i) =
        Measure.map (MeasurableEquiv.funUnique ({i} : Finset ι) ℝ)
          (volume.withDensity
            (fun x : ({i} : Finset ι) → ℝ ↦
              ENNReal.ofReal
                (∏ j : ({i} : Finset ι),
                  gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ (x j)))) := by
    -- The left side is exactly the coordinate law of `X i`.
    simpa [funUnique_comp_singletonRestrict_eq (X := X) i] using hpush'
  have hσ_ne : (⟨σ i ^ 2, le_of_lt (hσ i)⟩ : NNReal) ≠ 0 := by
    intro hzero
    exact (ne_of_gt (hσ i)) (congrArg (fun t : NNReal ↦ (t : ℝ)) hzero)
  -- Rewrite the transported singleton density to the one-dimensional Gaussian measure.
  calc
    P.map (X i)
        = Measure.map (MeasurableEquiv.funUnique ({i} : Finset ι) ℝ)
            (volume.withDensity
              (fun x : ({i} : Finset ι) → ℝ ↦
                ENNReal.ofReal
                  (∏ j : ({i} : Finset ι),
                    gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ (x j)))) := hpush''
    _ = volume.withDensity
          (fun t : ℝ ↦
            ENNReal.ofReal
              (∏ j : ({i} : Finset ι),
                gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ ((fun _ ↦ t) j))) := by
          simpa using
            mapWithDensityFunUnique
              (g := fun x : ({i} : Finset ι) → ℝ ↦
                ENNReal.ofReal
                  (∏ j : ({i} : Finset ι),
                    gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ (x j)))
              hsingleton_meas
    _ = volume.withDensity (gaussianPDF (m i) ⟨σ i ^ 2, le_of_lt (hσ i)⟩) := by
          refine withDensity_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
          rw [gaussianPDF_def]
          exact congrArg ENNReal.ofReal
            (singletonGaussianProductDensity_eq_gaussianPDFReal
              (m := m) (σ := σ) hσ i (fun _ ↦ t))
    _ = gaussianReal (m i) ⟨σ i ^ 2, le_of_lt (hσ i)⟩ := by
          exact (gaussianReal_of_var_ne_zero _ hσ_ne).symm

-- Proof sketch: the textbook density factors coordinatewise by the Gaussian pdfs
-- `gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩`. The singleton case identifies the
-- one-dimensional marginals with the Gaussian laws `gaussianReal (m i) ⟨σ i ^ 2, le_of_lt (hσ i)⟩`,
-- and Theorem 2.21 then upgrades the resulting lower-orthant factorization to independence.
/-- Example 2.25: Assume that each coordinate `X i` is measurable, that the variances satisfy
`σ i ^ 2 > 0`, and that every finite-dimensional joint law has the textbook Gaussian density
`x ↦ ∏ j, (2 * π * σ j ^ 2)^(-1 / 2) * exp (-(x j - m j)^2 / (2 * σ j ^ 2))`, expressed here via
`gaussianPDFReal`. Then the family is independent and each marginal has the Gaussian law
`N(m i, σ i ^ 2)`. -/
theorem iIndepFun_and_marginal_hasLaw_of_jointDensity_eq_prod_gaussianPDFReal
    {P : Measure Ω} {X : ι → Ω → ℝ} {m σ : ι → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hσ : ∀ i, 0 < σ i ^ 2)
    (h_density :
      ∀ J : Finset ι,
        P.map (fun ω ↦ J.restrict (X · ω)) =
          volume.withDensity
            (fun x : J → ℝ ↦
              ENNReal.ofReal
                (∏ j : J, gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ (x j)))) :
    iIndepFun X P ∧
      ∀ i, HasLaw (X i) (gaussianReal (m i) ⟨σ i ^ 2, le_of_lt (hσ i)⟩) P := by
  classical
  have h_indep : iIndepFun X P :=
    -- Corollary 2.22 turns the continuous density factorization into independence.
    (iIndepFun_iff_jointDensityFactorizes P X
      (gaussianProductDensity (m := m) (σ := σ) hσ)
      hX
      (jointGaussianDensityContinuous (m := m) (σ := σ) hσ)
      (jointLaw_eq_withDensity_gaussianProductDensity (X := X) (m := m) (σ := σ) hσ h_density)).2
      (gaussianProductDensity_factorizes (m := m) (σ := σ) hσ)
  -- Route correction: use Corollary 2.22 directly for independence, and keep only the singleton
  -- transport argument for the marginal laws.
  refine ⟨h_indep, ?_⟩
  intro i
  -- Package the singleton map equality as the `HasLaw` statement.
  exact ⟨(hX i).aemeasurable, singletonJointLaw_eq_gaussianReal hX hσ h_density i⟩
