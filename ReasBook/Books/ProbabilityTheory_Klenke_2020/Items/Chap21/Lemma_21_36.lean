/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_31
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_38
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Lemma_1_42
import Mathlib.MeasureTheory.Constructions.Projective

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped Topology

noncomputable section

namespace ProbabilityTheory

local notation "Ω" => C(NNReal, ℝ)

local instance : MeasurableSpace Ω := borel Ω

local instance : BorelSpace Ω := ⟨rfl⟩

private theorem measurable_finsetRestrict (I : Finset NNReal) :
    Measurable (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) := by
  exact measurable_pi_lambda _ fun i ↦ (continuous_eval_const (i : NNReal)).measurable

private theorem map_restrict_eq_of_continuousPathFiniteDimensionalDistribution_eq
    {P Q : ProbabilityMeasure Ω}
    (h :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        continuousPathFiniteDimensionalDistribution P times =
          continuousPathFiniteDimensionalDistribution Q times)
    {I : Finset NNReal} (hI : I.Nonempty) :
    (P : Measure Ω).map (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) =
      (Q : Measure Ω).map (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) := by
  classical
  let e : Fin ((I.card - 1) + 1) ≃ I :=
    (Fintype.equivFinOfCardEq
      (show Fintype.card I = ((I.card - 1) + 1) by
        simpa using (Nat.succ_pred_eq_of_pos (Finset.card_pos.2 hI)).symm)).symm
  let times : Fin ((I.card - 1) + 1) → NNReal := fun i ↦ (e i : NNReal)
  let f : Ω → Fin ((I.card - 1) + 1) → ℝ := fun ω i ↦ ω (times i)
  let eπ : (Fin ((I.card - 1) + 1) → ℝ) ≃ᵐ (I → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e
  have hf : Measurable f := by
    exact measurable_pi_lambda _ fun i ↦ (continuous_eval_const (times i)).measurable
  have hfin : (P : Measure Ω).map f = (Q : Measure Ω).map f := by
    simpa [continuousPathFiniteDimensionalDistribution, f, times]
      using congrArg
        ((↑) :
          ProbabilityMeasure (Fin ((I.card - 1) + 1) → ℝ) →
            Measure (Fin ((I.card - 1) + 1) → ℝ))
        (h times)
  have hcomp :
      eπ ∘ f =
        fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ) := by
    funext ω
    ext i
    change f ω (e.symm i) = ω i
    simp [f, times]
  calc
    (P : Measure Ω).map (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ))
      = ((P : Measure Ω).map f).map eπ := by
          rw [Measure.map_map eπ.measurable hf]
          simp [hcomp]
    _ = ((Q : Measure Ω).map f).map eπ := by
          exact congrArg
            (fun m : Measure (Fin ((I.card - 1) + 1) → ℝ) ↦
              m.map eπ)
            hfin
    _ = (Q : Measure Ω).map (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) := by
          rw [Measure.map_map eπ.measurable hf]
          simp [hcomp]

-- Proof sketch: view the Borel `σ`-algebra on `C([0, ∞), ℝ)` as the pullback of the product
-- `σ`-algebra on `ℝ^[0,∞)` along the canonical inclusion, then use measurable cylinders as the
-- generating `π`-system. Equality of every finite-dimensional marginal identifies the pushforwards
-- to each finite restriction space, hence the two path laws agree on all pulled-back cylinders and
-- therefore on the whole Borel `σ`-algebra.
/-- Lemma 21.36: a probability law on `C([0, ∞), ℝ)` is uniquely determined by its
finite-dimensional distributions. -/
theorem probabilityMeasure_eq_of_continuousPathFiniteDimensionalDistribution_eq
    {P Q : ProbabilityMeasure Ω}
    (h :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        continuousPathFiniteDimensionalDistribution P times =
          continuousPathFiniteDimensionalDistribution Q times) :
    P = Q := by
  classical
  let E : Set (Set Ω) :=
    Set.preimage ((↑) : Ω → NNReal → ℝ) '' measurableCylinders (fun _ : NNReal ↦ ℝ)
  have hA : borel Ω = MeasurableSpace.generateFrom E := by
    rw [← continuousPathSpace_comap_pi_eq_borel,
      ← (generateFrom_measurableCylinders :
        MeasurableSpace.generateFrom (measurableCylinders (fun _ : NNReal ↦ ℝ)) =
          MeasurableSpace.pi),
      MeasurableSpace.comap_generateFrom]
  have hE : IsPiSystem E := by
    have hmc : IsPiSystem (measurableCylinders (fun _ : NNReal ↦ ℝ)) := by
      simpa using
        (isPiSystem_measurableCylinders :
          IsPiSystem (measurableCylinders (fun _ : NNReal ↦ ℝ)))
    intro s hs t ht hst
    rcases hs with ⟨s', hs', rfl⟩
    rcases ht with ⟨t', ht', rfl⟩
    have hmc' := hmc s' hs' t' ht'
    refine ⟨s' ∩ t', hmc' ?_, rfl⟩
    rcases hst with ⟨ω, hsω, htω⟩
    exact ⟨(ω : NNReal → ℝ), hsω, htω⟩
  have hPQ : (P : Measure Ω) = (Q : Measure Ω) := by
    refine measure_ext_of_generateFrom_of_isProbabilityMeasure hA hE ?_
    intro t ht
    rcases ht with ⟨u, hu, rfl⟩
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders u).1 hu
    by_cases hI : I.Nonempty
    · have hmap :=
        map_restrict_eq_of_continuousPathFiniteDimensionalDistribution_eq h hI
      have hmap_apply_P :
          (P : Measure Ω).map (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) S =
            (P : Measure Ω) ((fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) ⁻¹' S) :=
        Measure.map_apply (measurable_finsetRestrict I) hS
      have hmap_apply_Q :
          (Q : Measure Ω).map (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) S =
            (Q : Measure Ω) ((fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) ⁻¹' S) :=
        Measure.map_apply (measurable_finsetRestrict I) hS
      rw [show ((↑) : Ω → NNReal → ℝ) ⁻¹' cylinder I S =
          (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) ⁻¹' S by
            rfl,
        ← hmap_apply_P,
        hmap,
        hmap_apply_Q]
    · have hI0 : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      subst hI0
      have : Subsingleton ((i : (∅ : Finset NNReal)) → ℝ) := inferInstance
      rcases Set.eq_empty_or_nonempty S with hSempty | hSnonempty
      · simp [hSempty]
      · have hSuniv : S = Set.univ := Subsingleton.eq_univ_of_nonempty hSnonempty
        simp [hSuniv]
  exact ProbabilityMeasure.toMeasure_injective hPQ

end ProbabilityTheory
