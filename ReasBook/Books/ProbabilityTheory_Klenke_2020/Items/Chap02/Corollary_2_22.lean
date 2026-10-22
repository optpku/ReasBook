/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u v

variable {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]

local instance : DecidableEq ι := Classical.decEq ι

/-- Helper for Corollary 2.22: a volume-preserving measurable equivalence transports a
`withDensity` law by precomposing the density with the inverse equivalence. -/
private lemma mapWithDensityOfVolumePreserving {α β : Type*}
    [MeasureSpace α] [MeasureSpace β]
    (e : α ≃ᵐ β) (hpres : MeasurePreserving e volume volume)
    (g : α → ENNReal) (hg : Measurable g) :
    Measure.map e (volume.withDensity g) =
      volume.withDensity (fun y : β ↦ g (e.symm y)) := by
  refine Measure.ext fun s hs ↦ ?_
  -- Evaluate both measures on a measurable set and move the set integral through `e`.
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ hs,
    withDensity_apply _ (e.measurable hs)]
  simpa using hpres.setLIntegral_comp_preimage hs (hg.comp e.symm.measurable)

/-- Helper for Corollary 2.22: the singleton coordinate map obtained from
`MeasurableEquiv.funUnique` and `Finset.restrict` is exactly `X i`. -/
private lemma funUnique_comp_singletonRestrict_eq {X : ι → Ω → ℝ} (i : ι) :
    (MeasurableEquiv.funUnique ({i} : Finset ι) ℝ) ∘
        (fun ω ↦ ({i} : Finset ι).restrict (X · ω)) = X i := by
  classical
  -- Unfold the singleton restriction and evaluate the unique coordinate.
  funext ω
  simp [Function.comp]

/-- Helper for Corollary 2.22: on `Fin n`, a product of one-dimensional `withDensity` measures is
the `withDensity` measure of the coordinatewise product density. -/
private lemma piMarginalDensitiesFin_eq_withDensity_prodDensity {n : ℕ}
    (g : Fin n → ℝ → ENNReal) (hg : ∀ i, Measurable (g i))
    [∀ i, IsFiniteMeasure (volume.withDensity (g i))] :
    Measure.pi (fun i ↦ volume.withDensity (g i)) =
      volume.withDensity (fun x : Fin n → ℝ ↦ ∏ i, g i (x i)) := by
  induction n with
  | zero =>
      -- In dimension `0`, both sides are the unit mass on the unique point.
      calc
        Measure.pi (fun i : Fin 0 ↦ volume.withDensity (g i))
            = Measure.dirac (fun i ↦ i.elim0) := by
                simpa using
                  (Measure.pi_of_empty
                    (μ := fun i : Fin 0 ↦ volume.withDensity (g i))
                    (x := fun i ↦ i.elim0))
        _ = (volume : Measure (Fin 0 → ℝ)) := by
              simpa using
                (Measure.volume_pi_eq_dirac
                  (α := fun _ : Fin 0 ↦ ℝ) (x := fun i ↦ i.elim0)).symm
        _ = volume.withDensity (fun x : Fin 0 → ℝ ↦ ∏ i : Fin 0, g i (x i)) := by
              simp
  | succ n ih =>
      let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0
      have htail_meas :
          Measurable (fun x : Fin n → ℝ ↦ ∏ i : Fin n, g i.succ (x i)) := by
        exact Finset.measurable_prod Finset.univ fun i _ ↦
          (hg i.succ).comp (continuous_apply i).measurable
      have hprod_meas :
          Measurable (fun x : Fin (n + 1) → ℝ ↦ ∏ i : Fin (n + 1), g i (x i)) := by
        exact Finset.measurable_prod Finset.univ fun i _ ↦
          (hg i).comp (continuous_apply i).measurable
      -- Route correction: replace the old lintegral/Fubini normalization by a head-tail
      -- decomposition of the finite product measure, then transport the target density once.
      apply (MeasurableEmbedding.map_injective e.measurableEmbedding)
      calc
        Measure.map e (Measure.pi (fun i : Fin (n + 1) => volume.withDensity (g i)))
            = (volume.withDensity (g 0)).prod
                (Measure.pi (fun i : Fin n => volume.withDensity (g i.succ))) := by
              simpa [e] using
                (measurePreserving_piFinSuccAbove
                  (fun i : Fin (n + 1) => volume.withDensity (g i)) 0).map_eq
        _ = (volume.withDensity (g 0)).prod
              (volume.withDensity (fun x : Fin n → ℝ ↦ ∏ i : Fin n, g i.succ (x i))) := by
              rw [ih (g := fun i : Fin n => g i.succ) (hg := fun i ↦ hg i.succ)]
        _ = ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))).withDensity
              (fun z : ℝ × (Fin n → ℝ) => g 0 z.1 * ∏ i : Fin n, g i.succ (z.2 i)) := by
              rw [prod_withDensity (hg 0) htail_meas]
        _ = Measure.map e
              (volume.withDensity (fun x : Fin (n + 1) → ℝ ↦ ∏ i : Fin (n + 1), g i (x i))) := by
              symm
              simpa [e, hprod_meas, htail_meas, MeasurableEquiv.piFinSuccAbove_symm_apply,
                Fin.insertNthEquiv, Fin.prod_univ_succ, Fin.insertNth_zero, Fin.zero_succAbove,
                cast_eq, Fin.cons_zero, Fin.cons_succ] using
                mapWithDensityOfVolumePreserving
                  (e := e)
                  (hpres := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
                  (g := fun x : Fin (n + 1) → ℝ ↦ ∏ i : Fin (n + 1), g i (x i))
                  hprod_meas

/-- Helper for Corollary 2.22: a finite product of one-dimensional `withDensity` measures is the
`withDensity` measure of the coordinatewise product density. -/
private lemma piMarginalDensities_eq_withDensity_prodDensity {α : Type*} [Fintype α]
    (g : α → ℝ → ENNReal) (hg : ∀ i, Measurable (g i))
    [∀ i, IsFiniteMeasure (volume.withDensity (g i))] :
    Measure.pi (fun i ↦ volume.withDensity (g i)) =
      volume.withDensity (fun x : α → ℝ ↦ ∏ i, g i (x i)) := by
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  have hprod_meas :
      Measurable (fun x : Fin (Fintype.card α) → ℝ ↦ ∏ i, g (e i) (x i)) := by
    exact Finset.measurable_prod Finset.univ fun i _ ↦
      (hg (e i)).comp (continuous_apply i).measurable
  -- Reindex once to `Fin (card α)` and reuse the canonical finite-dimensional normalization.
  calc
    Measure.pi (fun i ↦ volume.withDensity (g i))
        = Measure.map (MeasurableEquiv.piCongrLeft (fun _ : α ↦ ℝ) e)
            (Measure.pi (fun i : Fin (Fintype.card α) ↦ volume.withDensity (g (e i)))) := by
          symm
          simpa [e] using
            (measurePreserving_piCongrLeft
              (fun i : α ↦ volume.withDensity (g i)) e).map_eq
    _ = Measure.map (MeasurableEquiv.piCongrLeft (fun _ : α ↦ ℝ) e)
          (volume.withDensity
            (fun x : Fin (Fintype.card α) → ℝ ↦ ∏ i, g (e i) (x i))) := by
          rw [piMarginalDensitiesFin_eq_withDensity_prodDensity
            (g := fun i : Fin (Fintype.card α) ↦ g (e i))
            (hg := fun i ↦ hg (e i))]
    _ = volume.withDensity (fun x : α → ℝ ↦ ∏ i, g i (x i)) := by
          simpa [e, hprod_meas, MeasurableEquiv.coe_piCongrLeft, Function.comp_def,
            ← e.prod_comp, Equiv.piCongrLeft_apply_apply] using
            mapWithDensityOfVolumePreserving
              (e := MeasurableEquiv.piCongrLeft (fun _ : α ↦ ℝ) e)
              (hpres := volume_measurePreserving_piCongrLeft (fun _ : α ↦ ℝ) e)
              (g := fun x : Fin (Fintype.card α) → ℝ ↦ ∏ i, g (e i) (x i))
              hprod_meas

/-- Helper for Corollary 2.22: pushing a `withDensity` measure on a singleton function space
through `MeasurableEquiv.funUnique` yields the corresponding one-dimensional density law. -/
private lemma mapWithDensityFunUnique {α : Type*} [Unique α]
    (g : (α → ℝ) → ENNReal)
    (hg : Measurable g) :
    Measure.map (MeasurableEquiv.funUnique α ℝ) (volume.withDensity g) =
      volume.withDensity (fun t : ℝ ↦ g (fun _ ↦ t)) := by
  -- Specialize the general transport lemma to the singleton function-space equivalence.
  simpa using
    mapWithDensityOfVolumePreserving
      (e := MeasurableEquiv.funUnique α ℝ)
      (hpres := volume_preserving_funUnique α ℝ)
      g hg

/-- Helper for Corollary 2.22: the singleton case of `h_density` is exactly the marginal density
statement for the law of `X i` on `ℝ`. -/
private lemma singletonLaw_eq_withDensity (μ : Measure Ω) (X : ι → Ω → ℝ)
    (f : ∀ J : Finset ι, (J → ℝ) → NNReal) (hX : ∀ i, Measurable (X i))
    (hcont : ∀ J : Finset ι, Continuous (f J))
    (h_density :
      ∀ J : Finset ι,
        μ.map (fun ω ↦ J.restrict (X · ω)) =
          volume.withDensity (fun x ↦ (f J x : ENNReal))) :
    ∀ i : ι,
      μ.map (X i) =
        volume.withDensity (fun t : ℝ ↦ (f ({i} : Finset ι) (fun _ ↦ t) : ENNReal)) := by
  intro i
  have hrestrict_meas :
      Measurable (fun ω ↦ ({i} : Finset ι).restrict (X · ω)) := by
    fun_prop
  have hpush :=
    congrArg (Measure.map (MeasurableEquiv.funUnique ({i} : Finset ι) ℝ))
      (h_density ({i} : Finset ι))
  have hpush' :
      μ.map
          ((MeasurableEquiv.funUnique ({i} : Finset ι) ℝ) ∘
            (fun ω ↦ ({i} : Finset ι).restrict (X · ω))) =
        Measure.map (MeasurableEquiv.funUnique ({i} : Finset ι) ℝ)
          (volume.withDensity (fun x ↦ (f ({i} : Finset ι) x : ENNReal))) := by
    calc
      μ.map
          ((MeasurableEquiv.funUnique ({i} : Finset ι) ℝ) ∘
            (fun ω ↦ ({i} : Finset ι).restrict (X · ω)))
          =
          Measure.map (MeasurableEquiv.funUnique ({i} : Finset ι) ℝ)
            (μ.map (fun ω ↦ ({i} : Finset ι).restrict (X · ω))) := by
              symm
              exact Measure.map_map
                (MeasurableEquiv.funUnique ({i} : Finset ι) ℝ).measurable hrestrict_meas
      _ = Measure.map (MeasurableEquiv.funUnique ({i} : Finset ι) ℝ)
            (volume.withDensity (fun x ↦ (f ({i} : Finset ι) x : ENNReal))) := hpush
  -- Push the singleton joint law through `funUnique` so that the left side becomes `μ.map (X i)`.
  have hpush'' :
      μ.map (X i) =
        Measure.map (MeasurableEquiv.funUnique ({i} : Finset ι) ℝ)
          (volume.withDensity (fun x ↦ (f ({i} : Finset ι) x : ENNReal))) := by
    simpa [funUnique_comp_singletonRestrict_eq (X := X) i] using hpush'
  -- The right side is exactly the one-dimensional `withDensity` law after the same transport.
  simpa using
    hpush''.trans <|
      mapWithDensityFunUnique
        (g := fun x : ({i} : Finset ι) → ℝ ↦ (f ({i} : Finset ι) x : ENNReal))
        ((ENNReal.continuous_coe.comp (hcont ({i} : Finset ι))).measurable)

/-- Helper for Corollary 2.22: on a finite subfamily, independence rewrites the joint law as the
product of the marginal laws. -/
private lemma jointLaw_eq_piMarginalLaws_of_indep (μ : Measure Ω) (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (h_indep : iIndepFun X μ) :
    ∀ J : Finset ι,
      μ.map (fun ω ↦ J.restrict (X · ω)) = Measure.pi (fun j : J ↦ μ.map (X j.1)) := by
  intro J
  letI : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  have h_restrict : iIndepFun (fun j : J ↦ X j.1) μ :=
    h_indep.precomp (g := (Subtype.val : J → ι)) Subtype.val_injective
  -- We invoke the canonical finite-product characterization of independence on the subtype `J`.
  simpa using
    (iIndepFun_iff_map_fun_eq_pi_map (fun j : J ↦ (hX j.1).aemeasurable)).mp h_restrict

/-- Helper for Corollary 2.22: continuous densities are uniquely determined by their
`withDensity` measures. -/
private lemma continuousDensity_eq_of_withDensity_eq {α : Type*} [Fintype α]
    {g h : (α → ℝ) → NNReal} (hg : Continuous g) (hh : Continuous h)
    (h_eq :
      volume.withDensity (fun x ↦ (g x : ENNReal)) =
        volume.withDensity (fun x ↦ (h x : ENNReal))) :
    g = h := by
  have h_ae :
      (fun x : α → ℝ ↦ ((g x : NNReal) : ENNReal)) =ᵐ[volume]
        fun x : α → ℝ ↦ ((h x : NNReal) : ENNReal) :=
    (withDensity_eq_iff_of_sigmaFinite
      ((ENNReal.continuous_coe.comp hg).measurable.aemeasurable)
      ((ENNReal.continuous_coe.comp hh).measurable.aemeasurable)).mp h_eq
  have h_eq_coe :
      (fun x : α → ℝ ↦ ((g x : NNReal) : ENNReal)) =
        fun x : α → ℝ ↦ ((h x : NNReal) : ENNReal) :=
    (Continuous.ae_eq_iff_eq (μ := volume)
      (ENNReal.continuous_coe.comp hg) (ENNReal.continuous_coe.comp hh)).mp h_ae
  exact funext fun x ↦ ENNReal.coe_injective (congrFun h_eq_coe x)

-- Proof sketch: if `X` is independent, Theorem 2.21 gives the factorization of the finite joint
-- distribution functions; uniqueness of continuous densities identifies the integrands, yielding
-- the density product formula. Conversely, integrating the product density over rectangles gives
-- the factorization of the finite joint distribution functions, and Theorem 2.21 then yields
-- independence.
/-- Corollary 2.22: If every finite joint law of a real-valued family admits a continuous density
with respect to Lebesgue measure, then the family is independent if and only if every finite joint
density factors as the product of the corresponding one-dimensional densities. -/
theorem iIndepFun_iff_jointDensityFactorizes (μ : Measure Ω) (X : ι → Ω → ℝ)
    (f : ∀ J : Finset ι, (J → ℝ) → NNReal) (hX : ∀ i, Measurable (X i))
    (hcont : ∀ J : Finset ι, Continuous (f J))
    (h_density :
      ∀ J : Finset ι,
        μ.map (fun ω ↦ J.restrict (X · ω)) =
          volume.withDensity (fun x ↦ (f J x : ENNReal))) :
    iIndepFun X μ ↔
      ∀ (J : Finset ι) (x : J → ℝ),
        f J x = ∏ j : J, f ({j.1} : Finset ι) (fun _ ↦ x j) := by
  constructor
  · intro h_indep J x
    letI : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
    have h_singleton := singletonLaw_eq_withDensity μ X f hX hcont h_density
    have hcoord_meas (j : J) :
        Measurable (fun t : ℝ ↦ (f ({j.1} : Finset ι) (fun _ ↦ t) : ENNReal)) := by
      exact
        (ENNReal.continuous_coe.comp <|
          (hcont ({j.1} : Finset ι)).comp (continuous_pi fun _ ↦ continuous_id)).measurable
    have hprod_cont :
        Continuous (fun y : J → ℝ ↦ ∏ j : J, f ({j.1} : Finset ι) (fun _ ↦ y j)) := by
      refine continuous_finset_prod _ fun j _ ↦ ?_
      exact (hcont ({j.1} : Finset ι)).comp (continuous_pi fun _ ↦ continuous_apply j)
    haveI : ∀ j : J,
        IsFiniteMeasure
          (volume.withDensity (fun t : ℝ ↦ (f ({j.1} : Finset ι) (fun _ ↦ t) : ENNReal))) :=
      fun j ↦ by
        rw [← h_singleton j.1]
        exact Measure.isFiniteMeasure_map μ (X j.1)
    have h_density_eq :
        volume.withDensity (fun y : J → ℝ ↦ (f J y : ENNReal)) =
          volume.withDensity
            (fun y : J → ℝ ↦
              ((∏ j : J, f ({j.1} : Finset ι) (fun _ ↦ y j) : NNReal) : ENNReal)) := by
      calc
        volume.withDensity (fun y : J → ℝ ↦ (f J y : ENNReal))
            = μ.map (fun ω ↦ J.restrict (X · ω)) := by
              symm
              exact h_density J
        _ = Measure.pi (fun j : J ↦ μ.map (X j.1)) := by
              exact jointLaw_eq_piMarginalLaws_of_indep μ X hX h_indep J
        _ = Measure.pi
              (fun j : J ↦
                volume.withDensity (fun t : ℝ ↦ (f ({j.1} : Finset ι) (fun _ ↦ t) : ENNReal))) := by
              congr 1
              funext j
              exact h_singleton j.1
        _ = volume.withDensity
              (fun y : J → ℝ ↦
                ((∏ j : J, f ({j.1} : Finset ι) (fun _ ↦ y j) : NNReal) : ENNReal)) := by
              simpa using
                (piMarginalDensities_eq_withDensity_prodDensity
                  (g := fun j : J ↦ fun t : ℝ ↦
                    (f ({j.1} : Finset ι) (fun _ ↦ t) : ENNReal))
                  hcoord_meas)
    -- Uniqueness of continuous densities turns the measure equality into the pointwise formula.
    exact congrFun
      (continuousDensity_eq_of_withDensity_eq
        (hg := hcont J) (hh := hprod_cont) h_density_eq) x
  · intro h_factor
    have h_empty_density :
        volume.withDensity (fun x : (∅ : Finset ι) → ℝ ↦ (f (∅ : Finset ι) x : ENNReal)) =
          (volume : Measure ((∅ : Finset ι) → ℝ)) := by
      have h_empty_fun :
          (fun x : (∅ : Finset ι) → ℝ ↦ (f (∅ : Finset ι) x : ENNReal)) = 1 := by
        funext x
        simpa using congrArg (fun r : NNReal ↦ (r : ENNReal)) (h_factor (∅ : Finset ι) x)
      rw [withDensity_congr_ae (Filter.Eventually.of_forall fun x ↦ congrFun h_empty_fun x),
        withDensity_one]
    have h_prob_univ : μ Set.univ = 1 := by
      have hrestrict_empty_meas :
          Measurable (fun ω ↦ (∅ : Finset ι).restrict (X · ω)) := by
        fun_prop
      have h_univ :=
        congrArg (fun ν : Measure ((∅ : Finset ι) → ℝ) ↦ ν Set.univ)
          ((h_density (∅ : Finset ι)).trans h_empty_density)
      have h_map_univ :
          (μ.map (fun ω ↦ (∅ : Finset ι).restrict (X · ω))) Set.univ =
            (volume : Measure ((∅ : Finset ι) → ℝ)) Set.univ := by
        simpa using h_univ
      have h_volume_univ : (volume : Measure ((∅ : Finset ι) → ℝ)) Set.univ = 1 := by
        rw [Measure.volume_pi_eq_dirac (α := fun _ : (∅ : Finset ι) ↦ ℝ)]
        simp
      have h_map_univ' : (μ.map (fun ω ↦ (∅ : Finset ι).restrict (X · ω))) Set.univ = 1 := by
        exact h_map_univ.trans h_volume_univ
      have h_map_apply :
          (μ.map (fun ω ↦ (∅ : Finset ι).restrict (X · ω))) Set.univ = μ Set.univ := by
        rw [Measure.map_apply hrestrict_empty_meas MeasurableSet.univ]
        simp
      rw [h_map_apply] at h_map_univ'
      exact h_map_univ'
    letI : IsProbabilityMeasure μ := ⟨h_prob_univ⟩
    have h_singleton := singletonLaw_eq_withDensity μ X f hX hcont h_density
    refine (iIndepFun_iff_joint_cdf_eq_prod_marginals μ X hX).2 ?_
    intro J x
    have hcoord_meas (j : J) :
        Measurable (fun t : ℝ ↦ (f ({j.1} : Finset ι) (fun _ ↦ t) : ENNReal)) := by
      exact
        (ENNReal.continuous_coe.comp <|
          (hcont ({j.1} : Finset ι)).comp (continuous_pi fun _ ↦ continuous_id)).measurable
    haveI : ∀ j : J,
        IsFiniteMeasure
          (volume.withDensity (fun t : ℝ ↦ (f ({j.1} : Finset ι) (fun _ ↦ t) : ENNReal))) :=
      fun j ↦ by
        rw [← h_singleton j.1]
        exact Measure.isFiniteMeasure_map μ (X j.1)
    have h_prod_density :
        (fun y : J → ℝ ↦ (f J y : ENNReal)) =
          fun y : J → ℝ ↦
            ((∏ j : J, f ({j.1} : Finset ι) (fun _ ↦ y j) : NNReal) : ENNReal) := by
      funext y
      simpa using congrArg (fun r : NNReal ↦ (r : ENNReal)) (h_factor J y)
    have h_joint_eq_prod :
        μ.map (fun ω ↦ J.restrict (X · ω)) =
          Measure.pi (fun j : J ↦ μ.map (X j.1)) := by
      calc
        μ.map (fun ω ↦ J.restrict (X · ω))
            = volume.withDensity (fun y : J → ℝ ↦ (f J y : ENNReal)) := h_density J
        _ = volume.withDensity
              (fun y : J → ℝ ↦
                ((∏ j : J, f ({j.1} : Finset ι) (fun _ ↦ y j) : NNReal) : ENNReal)) := by
              rw [withDensity_congr_ae <|
                Filter.Eventually.of_forall fun y ↦ congrFun h_prod_density y]
        _ = Measure.pi
              (fun j : J ↦
                volume.withDensity (fun t : ℝ ↦ (f ({j.1} : Finset ι) (fun _ ↦ t) : ENNReal))) := by
              symm
              simpa using
                (piMarginalDensities_eq_withDensity_prodDensity
                  (g := fun j : J ↦ fun t : ℝ ↦
                    (f ({j.1} : Finset ι) (fun _ ↦ t) : ENNReal))
                  hcoord_meas)
        _ = Measure.pi (fun j : J ↦ μ.map (X j.1)) := by
              congr 1
              funext j
              exact (h_singleton j.1).symm
    have h_iic :
        Set.Iic x = Set.univ.pi (fun j : J ↦ Set.Iic (x j)) := by
      ext y
      simp
    -- Rewrite the lower-orthant mass using the joint-law comparison and the rectangle formula.
    calc
      μ (⋂ j : J, X j ⁻¹' Set.Iic (x j))
          = μ.map (fun ω ↦ J.restrict (X · ω)) (Set.Iic x) := by
              symm
              exact jointDistribution_apply_Iic μ X hX J x
      _ = Measure.pi (fun j : J ↦ μ.map (X j.1)) (Set.Iic x) := by
              rw [h_joint_eq_prod]
      _ = Measure.pi (fun j : J ↦ μ.map (X j.1)) (Set.univ.pi fun j : J ↦ Set.Iic (x j)) := by
              rw [h_iic]
      _ = ∏ j : J, μ.map (X j.1) (Set.Iic (x j)) := by
              rw [Measure.pi_pi]
      _ = ∏ j : J, μ (X j.1 ⁻¹' Set.Iic (x j)) := by
              refine Finset.prod_congr rfl ?_
              intro j _
              rw [Measure.map_apply (hX j.1) measurableSet_Iic]

end
