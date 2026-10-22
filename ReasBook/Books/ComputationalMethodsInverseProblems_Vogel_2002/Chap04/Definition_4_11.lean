/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Probability.Density
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_9.JointCDF
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_10.DiscreteRandomVector

public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace ProbabilityTheory

universe u v

/-- Helper for Definition 4.11: `piRealVolume` is the product Lebesgue measure on `ι → ℝ`. -/
abbrev piRealVolume {ι : Type v} [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ ↦ (volume : Measure ℝ)

/-- Helper for Definition 4.11: a measure-preserving measurable equivalence transports
`withDensity` by composing the target density with the equivalence. -/
lemma map_withDensity_comp_of_measurePreservingEquiv
    {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    {f : β → ENNReal} (hf : Measurable f) :
    Measure.map e (μ.withDensity (fun x ↦ f (e x))) = ν.withDensity f := by
  -- Evaluate both measures on measurable sets and transport the set integral along `e`.
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs,
    he.setLIntegral_comp_preimage hs hf]

/-- Helper for Definition 4.11: on `Fin n`, the product of one-dimensional `withDensity`
measures is a single `withDensity` on product Lebesgue measure with density `∏ i, f i (z i)`. -/
lemma finPiWithDensity_eq_withDensity_prod
    {n : ℕ} {f : Fin n → ℝ → ENNReal} (hf : ∀ i, Measurable (f i))
    (hσ : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (f i))) :
    Measure.pi (fun i ↦ volume.withDensity (f i)) =
      ((Measure.pi fun _ : Fin n ↦ (volume : Measure ℝ))).withDensity
        (fun z ↦ ∏ i, f i (z i)) := by
  induction n with
  | zero =>
      -- The empty product density is identically `1`.
      simpa using congrArg Measure.pi (funext fun i : Fin 0 ↦ Fin.elim0 i)
  | succ n ih =>
      let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
      have h_left :
          Measure.map e (Measure.pi (fun i : Fin (n + 1) ↦ volume.withDensity (f i))) =
            (volume.withDensity (f 0)).prod
              (Measure.pi fun i : Fin n ↦ volume.withDensity (f i.succ)) := by
        -- Split the product measure into the head coordinate and the tail product.
        simpa [e] using
          (measurePreserving_piFinSuccAbove
            (fun i : Fin (n + 1) ↦ volume.withDensity (f i)) 0).map_eq
      have hσ_tail : ∀ i : Fin n, SigmaFinite ((volume : Measure ℝ).withDensity (f i.succ)) :=
        fun i ↦ hσ i.succ
      have h_tail :
          Measure.pi (fun i : Fin n ↦ volume.withDensity (f i.succ)) =
            ((Measure.pi fun _ : Fin n ↦ (volume : Measure ℝ))).withDensity
              (fun z ↦ ∏ i : Fin n, f i.succ (z i)) :=
        ih (fun i ↦ hf i.succ) hσ_tail
      have h_pair :
          (volume.withDensity (f 0)).prod
              (Measure.pi fun i : Fin n ↦ volume.withDensity (f i.succ)) =
            ((volume : Measure ℝ).prod
              (Measure.pi fun _ : Fin n ↦ (volume : Measure ℝ))).withDensity
              (fun z ↦ f 0 z.1 * ∏ i : Fin n, f i.succ (z.2 i)) := by
        -- Combine the head density with the tail density using `prod_withDensity`.
        rw [h_tail]
        simpa using
          (MeasureTheory.prod_withDensity
            (μ := (volume : Measure ℝ))
            (ν := Measure.pi fun _ : Fin n ↦ (volume : Measure ℝ))
            (f := f 0)
            (g := fun z : Fin n → ℝ ↦ ∏ i : Fin n, f i.succ (z i))
            (hf 0)
            (Finset.measurable_prod Finset.univ
              (fun (i : Fin n) _ ↦ (hf i.succ).comp (measurable_pi_apply i))))
      have h_transport :
          Measure.map e
            ((Measure.pi fun _ : Fin (n + 1) ↦ (volume : Measure ℝ)).withDensity
              (fun z ↦ ∏ i : Fin (n + 1), f i (z i))) =
            ((volume : Measure ℝ).prod
              (Measure.pi fun _ : Fin n ↦ (volume : Measure ℝ))).withDensity
              (fun z ↦ f 0 z.1 * ∏ i : Fin n, f i.succ (z.2 i)) := by
        -- Transport the product density through the same head-tail measurable equivalence.
        have h_pair_meas :
            Measurable (fun z : ℝ × (Fin n → ℝ) ↦ f 0 z.1 * ∏ i : Fin n, f i.succ (z.2 i)) := by
          exact ((hf 0).comp measurable_fst).mul
            ((Finset.measurable_prod Finset.univ
              (fun (i : Fin n) _ ↦ (hf i.succ).comp (measurable_pi_apply i))).comp measurable_snd)
        have h :=
          map_withDensity_comp_of_measurePreservingEquiv
            (e := e)
            (μ := Measure.pi fun _ : Fin (n + 1) ↦ (volume : Measure ℝ))
            (ν := (volume : Measure ℝ).prod (Measure.pi fun _ : Fin n ↦ (volume : Measure ℝ)))
            (he := by
              simpa [e] using
                (measurePreserving_piFinSuccAbove
                  (fun _ : Fin (n + 1) ↦ (volume : Measure ℝ)) 0))
            (f := fun z : ℝ × (Fin n → ℝ) ↦ f 0 z.1 * ∏ i : Fin n, f i.succ (z.2 i))
            h_pair_meas
        simpa [e, MeasurableEquiv.piFinSuccAbove, Fin.prod_univ_succ, Fin.tail] using h
      -- Compare the two measures after transporting both of them to the same binary product space.
      exact
        (MeasurableEquiv.map_measurableEquiv_injective e)
          (h_left.trans (h_pair.trans h_transport.symm))

/-- Helper for Definition 4.11: the finite product of one-dimensional `withDensity` measures on
an arbitrary finite index type is a single `withDensity` on product Lebesgue measure. -/
lemma piWithDensity_eq_withDensity_prod
    {ι : Type v} [Fintype ι] {f : ι → ℝ → ENNReal} (hf : ∀ i, Measurable (f i))
    (hσ : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (f i))) :
    Measure.pi (fun i ↦ volume.withDensity (f i)) =
      ((Measure.pi fun _ : ι ↦ (volume : Measure ℝ))).withDensity
        (fun z ↦ ∏ i, f i (z i)) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have h_left :
      Measure.map (MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) e)
        (Measure.pi fun i : Fin (Fintype.card ι) ↦ volume.withDensity (f (e i))) =
        Measure.pi (fun i : ι ↦ volume.withDensity (f i)) := by
    -- Relabel the finite index set from `Fin` back to the original coordinates.
    simpa [e] using
      (measurePreserving_piCongrLeft
        (α := fun _ : ι ↦ ℝ)
        (μ := fun i : ι ↦ volume.withDensity (f i))
        e).map_eq
  have h_transport :
      Measure.map (MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) e)
        ((Measure.pi fun _ : Fin (Fintype.card ι) ↦ (volume : Measure ℝ)).withDensity
          (fun z ↦ ∏ i : Fin (Fintype.card ι), f (e i) (z i))) =
        (Measure.pi fun _ : ι ↦ (volume : Measure ℝ)).withDensity
          (fun z ↦ ∏ i : ι, f i (z i)) := by
    -- The density itself only changes by reindexing the finite product.
    have h_prod_meas :
        Measurable (fun z : ι → ℝ ↦ ∏ i : ι, f i (z i)) := by
      exact Finset.measurable_prod Finset.univ
        (fun i _ ↦ (hf i).comp (measurable_pi_apply i))
    have h_density_reindex :
        (fun z : Fin (Fintype.card ι) → ℝ ↦
          ∏ i : ι, f i ((MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) e) z i)) =
        (fun z : Fin (Fintype.card ι) → ℝ ↦
          ∏ i : Fin (Fintype.card ι), f (e i) (z i)) := by
      funext z
      have h_eval :
          ∀ i : ι, (MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) e) z i = z (e.symm i) := by
        intro i
        simpa using
          (MeasurableEquiv.piCongrLeft_apply_apply
            (e := e)
            (β := fun _ : ι ↦ ℝ)
            z
            (e.symm i))
      calc
        ∏ i : ι, f i ((MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) e) z i) =
            ∏ i : ι, f i (z (e.symm i)) := by
              simp [h_eval]
        _ = ∏ i : Fin (Fintype.card ι), f (e i) (z i) := by
              simpa using ((e.prod_comp fun i : ι ↦ f i (z (e.symm i))).symm)
    have h :=
      map_withDensity_comp_of_measurePreservingEquiv
        (e := MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) e)
        (μ := Measure.pi fun _ : Fin (Fintype.card ι) ↦ (volume : Measure ℝ))
        (ν := Measure.pi fun _ : ι ↦ (volume : Measure ℝ))
        (he := by
          simpa [e] using
            (measurePreserving_piCongrLeft
              (α := fun _ : ι ↦ ℝ)
              (μ := fun _ : ι ↦ (volume : Measure ℝ))
              e))
        (f := fun z : ι → ℝ ↦ ∏ i : ι, f i (z i))
        h_prod_meas
    calc
      Measure.map (MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) e)
          ((Measure.pi fun _ : Fin (Fintype.card ι) ↦ (volume : Measure ℝ)).withDensity
            (fun z ↦ ∏ i : Fin (Fintype.card ι), f (e i) (z i))) =
      Measure.map (MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) e)
          ((Measure.pi fun _ : Fin (Fintype.card ι) ↦ (volume : Measure ℝ)).withDensity
            (fun z ↦ ∏ i : ι, f i ((MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) e) z i))) := by
          congr 1
          exact withDensity_congr_ae (ae_of_all _ fun z ↦ (congrFun h_density_reindex z).symm)
      _ = (Measure.pi fun _ : ι ↦ (volume : Measure ℝ)).withDensity
            (fun z ↦ ∏ i : ι, f i (z i)) := h
  -- Reindex the canonical `Fin` statement back to the original finite index type.
  have h_fin :
      Measure.map (MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) e)
        (Measure.pi fun i : Fin (Fintype.card ι) ↦ volume.withDensity (f (e i))) =
      Measure.map (MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) e)
        (((Measure.pi fun _ : Fin (Fintype.card ι) ↦ (volume : Measure ℝ))).withDensity
          (fun z ↦ ∏ i : Fin (Fintype.card ι), f (e i) (z i))) := by
    exact congrArg
      (Measure.map (MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) e))
      (finPiWithDensity_eq_withDensity_prod
        (f := fun i : Fin (Fintype.card ι) ↦ f (e i))
        (fun i ↦ hf (e i))
        (fun i ↦ hσ (e i)))
  exact h_left.symm.trans (h_fin.trans h_transport)

/-- Helper for Definition 4.11: each coordinate of the canonical `jointPmf` carries the expected
coordinate marginal law. -/
lemma jointPmfEval_hasLaw
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {X : ι → Ω → ℝ}
    (h_disc : IsDiscreteRandomVector μ X) (i : ι) :
    HasLaw (X i) (PMF.map (Function.eval i) (jointPmf h_disc)).toMeasure μ := by
  -- First identify the `i`th coordinate law under the joint PMF itself.
  have h_eval :
      HasLaw (Function.eval i) (PMF.map (Function.eval i) (jointPmf h_disc)).toMeasure
        (jointPmf h_disc).toMeasure := by
    refine ⟨measurable_pi_apply i |>.aemeasurable, ?_⟩
    -- This is the defining `PMF.map` pushforward identity.
    simpa using
      (PMF.toMeasure_map
        (p := jointPmf h_disc)
        (f := Function.eval i)
        (hf := measurable_pi_apply i))
  -- Then compose that law with the joint law of the discrete random vector.
  change
    HasLaw (fun ω ↦ Function.eval i (fun j ↦ X j ω))
      (PMF.map (Function.eval i) (jointPmf h_disc)).toMeasure μ
  exact h_eval.comp (jointPmf_spec h_disc)

/-- A companion result for Definition 4.11: for a finite real random vector with joint density,
the pushed-forward joint law of a lower orthant is the set integral of the joint `pdf` over that
lower orthant. -/
theorem jointLaw_lowerOrthant_eq_setLIntegral_pdf
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {X : ι → Ω → ℝ}
    [HasPDF (fun ω i ↦ X i ω) μ (Measure.pi fun _ ↦ volume)]
    (x : ι → ℝ) :
    Measure.map (fun ω i ↦ X i ω) μ (Set.univ.pi fun i ↦ Set.Iic (x i)) =
      ∫⁻ u in Set.univ.pi fun i ↦ Set.Iic (x i),
        pdf (fun ω i ↦ X i ω) μ (Measure.pi fun _ ↦ volume) u
          ∂Measure.pi (fun _ ↦ volume) := by
  -- This is the standard `map = set integral of pdf` identity on the lower orthant.
  have hs : MeasurableSet (Set.univ.pi fun i ↦ Set.Iic (x i)) :=
    MeasurableSet.univ_pi fun i ↦ measurableSet_Iic
  simpa using
    (MeasureTheory.map_eq_setLIntegral_pdf
      (fun ω i ↦ X i ω)
      μ
      (piRealVolume (ι := ι))
      hs)

/-- A companion result for Definition 4.11: independent components of a finite real discrete
random vector give the product law of the coordinate marginal PMFs. -/
theorem iIndepFun.jointPmf_toMeasure_eq_pi
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_disc : IsDiscreteRandomVector μ X) :
    (jointPmf h_disc).toMeasure =
      Measure.pi fun i ↦ (PMF.map (Function.eval i) (jointPmf h_disc)).toMeasure := by
  -- The joint law is both the canonical PMF law and, by independence, the product of its
  -- coordinate marginal laws.
  have h_pi :
      HasLaw (fun ω i ↦ X i ω)
        (Measure.pi fun i ↦ (PMF.map (Function.eval i) (jointPmf h_disc)).toMeasure) μ :=
    h_indep.hasLaw_pi (fun i ↦ jointPmfEval_hasLaw h_disc i)
  calc
    (jointPmf h_disc).toMeasure = Measure.map (fun ω i ↦ X i ω) μ := by
      simpa using (jointPmf_spec h_disc).map_eq.symm
    _ = Measure.pi fun i ↦ (PMF.map (Function.eval i) (jointPmf h_disc)).toMeasure := h_pi.map_eq

/-- A companion result for Definition 4.11: evaluating the product-law factorization on a
singleton gives the source pointwise formula for the joint probability mass. -/
theorem iIndepFun.jointPmf_apply_eq_prod_coordMarginals
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_disc : IsDiscreteRandomVector μ X) (x : ι → ℝ) :
    jointPmf h_disc x = ∏ i, PMF.map (Function.eval i) (jointPmf h_disc) (x i) := by
  -- Evaluate the law-level factorization on the singleton `{x}`.
  have h :=
    congrArg (fun ν : Measure (ι → ℝ) ↦ ν {x}) (h_indep.jointPmf_toMeasure_eq_pi h_disc)
  have h_pi :
      (jointPmf h_disc).toMeasure {x} =
        ∏ i, (PMF.map (Function.eval i) (jointPmf h_disc)).toMeasure {x i} := by
    simpa using
      h.trans
        (Measure.pi_singleton
          (μ := fun i ↦ (PMF.map (Function.eval i) (jointPmf h_disc)).toMeasure)
          x)
  calc
    jointPmf h_disc x = (jointPmf h_disc).toMeasure {x} := by
      simpa using ((jointPmf h_disc).toMeasure_apply_singleton x (measurableSet_singleton x)).symm
    _ = ∏ i, (PMF.map (Function.eval i) (jointPmf h_disc)).toMeasure {x i} := h_pi
    _ = ∏ i, PMF.map (Function.eval i) (jointPmf h_disc) (x i) := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      simpa using
        (PMF.toMeasure_apply_singleton
          (p := PMF.map (Function.eval i) (jointPmf h_disc))
          (a := x i)
          (h := measurableSet_singleton (x i)))

/-- Definition 4.11. For a finite real random vector with independent components and joint
density, the joint `pdf` agrees almost everywhere with the product of the coordinate `pdf`s. -/
theorem iIndepFun.jointPdf_ae_eq_prod_pdf
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {X : ι → Ω → ℝ}
    [HasPDF (fun ω i ↦ X i ω) μ (Measure.pi fun _ ↦ volume)]
    (h_indep : iIndepFun X μ) :
    pdf (fun ω i ↦ X i ω) μ (Measure.pi fun _ ↦ volume) =ᵐ[Measure.pi fun _ ↦ volume]
      fun z ↦ ∏ i, pdf (X i) μ volume (z i) := by
  haveI := h_indep.isProbabilityMeasure
  have h_joint_pdf : HasPDF (fun ω i ↦ X i ω) μ (Measure.pi fun _ ↦ volume) := inferInstance
  have h_joint_meas :
      AEMeasurable (fun ω i ↦ X i ω) μ :=
    h_joint_pdf.aemeasurable
  have h_joint_ac :
      Measure.map (fun ω i ↦ X i ω) μ ≪ piRealVolume (ι := ι) := by
    simpa using h_joint_pdf.absolutelyContinuous
  -- Each coordinate inherits a one-dimensional density from the joint density.
  have h_coord_pdf : ∀ i, HasPDF (X i) μ volume := by
    intro i
    have h_coord_meas : AEMeasurable (X i) μ := by
      change AEMeasurable (fun ω ↦ Function.eval i (fun j ↦ X j ω)) μ
      exact (measurable_pi_apply i).aemeasurable.comp_aemeasurable h_joint_meas
    have h_coord_ac : Measure.map (X i) μ ≪ volume := by
      have h_map_comp :
          Measure.map (X i) μ =
            Measure.map (Function.eval i) (Measure.map (fun ω j ↦ X j ω) μ) := by
        change
          Measure.map (fun ω ↦ Function.eval i (fun j ↦ X j ω)) μ =
            Measure.map (Function.eval i) (Measure.map (fun ω j ↦ X j ω) μ)
        exact
          (AEMeasurable.map_map_of_aemeasurable
            (measurable_pi_apply i).aemeasurable
            h_joint_meas).symm
      rw [h_map_comp]
      exact
        (h_joint_ac.map
          (Measure.quasiMeasurePreserving_eval
            (fun _ ↦ (volume : Measure ℝ)) i).measurable).trans
          (Measure.quasiMeasurePreserving_eval
            (fun _ ↦ (volume : Measure ℝ)) i).absolutelyContinuous
    exact (Real.hasPDF_iff_of_aemeasurable h_coord_meas).2 h_coord_ac
  have h_map :
      Measure.map (fun ω i ↦ X i ω) μ =
        Measure.pi (fun i ↦ volume.withDensity (pdf (X i) μ volume)) := by
    -- Independence rewrites the joint law as the product of the coordinate laws.
    rw [h_indep.map_fun_eq_pi_map (fun i ↦ (h_coord_pdf i).aemeasurable)]
    congr 1
    funext i
    simpa using (MeasureTheory.map_eq_withDensity_pdf (X i) μ volume)
  have h_coord_sigma :
      ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (pdf (X i) μ volume)) := by
    intro i
    rw [← MeasureTheory.map_eq_withDensity_pdf (X i) μ volume]
    infer_instance
  have h_prod :
      Measure.pi (fun i ↦ volume.withDensity (pdf (X i) μ volume)) =
        (piRealVolume (ι := ι)).withDensity
          (fun z ↦ ∏ i, pdf (X i) μ volume (z i)) := by
    -- Normalize the product of one-dimensional densities into one density on product Lebesgue
    -- measure.
    simpa [piRealVolume] using
      piWithDensity_eq_withDensity_prod
        (f := fun i ↦ pdf (X i) μ volume)
        (fun i ↦ measurable_pdf (X i) μ volume)
        (fun i ↦ h_coord_sigma i)
  have h_prod_meas :
      AEMeasurable (fun z : ι → ℝ ↦ ∏ i, pdf (X i) μ volume (z i))
        (piRealVolume (ι := ι)) :=
    (Finset.measurable_prod Finset.univ
      (fun i _ ↦ (measurable_pdf (X i) μ volume).comp (measurable_pi_apply i))).aemeasurable
  -- Uniqueness of the Radon-Nikodym derivative identifies the joint density.
  exact
    (MeasureTheory.pdf.eq_of_map_eq_withDensity'
      (X := fun ω i ↦ X i ω)
      (μ := piRealVolume (ι := ι))
      (f := fun z ↦ ∏ i, pdf (X i) μ volume (z i))
      h_prod_meas).mp
      (h_map.trans h_prod)

end ProbabilityTheory

/- Definition 4.11 (1). The lower-orthant density formula is formalized at the joint-law level by
`ProbabilityTheory.jointLaw_lowerOrthant_eq_setLIntegral_pdf`; Definition 4.9 supplies the
companion `jointCdf` interpretation of the same lower-orthant probability. -/
#check ProbabilityTheory.jointLaw_lowerOrthant_eq_setLIntegral_pdf

/- Definition 4.11 (2). The source pointwise factorization of the joint probability mass function
is formalized by `ProbabilityTheory.iIndepFun.jointPmf_apply_eq_prod_coordMarginals`; the
companion law-level statement is `ProbabilityTheory.iIndepFun.jointPmf_toMeasure_eq_pi`. -/
#check ProbabilityTheory.iIndepFun.jointPmf_apply_eq_prod_coordMarginals
#check ProbabilityTheory.iIndepFun.jointPmf_toMeasure_eq_pi

/- Definition 4.11 (3). The factorization of the joint `pdf` into the product of the coordinate
`pdf`s is formalized by `ProbabilityTheory.iIndepFun.jointPdf_ae_eq_prod_pdf`. -/
#check ProbabilityTheory.iIndepFun.jointPdf_ae_eq_prod_pdf
