/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Lemma_2_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Remark_14_31
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_39
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Example_18_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Lemma_18_3
import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- Helper for Theorem 18.8: in a translation-invariant lattice walk, the singleton transition
from `x` to `y` is the origin-row mass at the increment `y - x`. -/
lemma translationInvariantOriginRow_step_eq {d : ℕ}
    (p : LatticePoint d → LatticePoint d → ENNReal)
    (htranslation : IsTranslationInvariantStepMatrix p)
    [IsMarkovKernel (discreteMatrixKernel p)] (x y : LatticePoint d) :
    dirac_convolution_kernel ((discreteMatrixKernel p 0).toPMF.toMeasure) x
        ({y} : Set (LatticePoint d)) =
      p x y := by
  -- Proof comment: rewrite the translated singleton back to the increment `y - x`, then read the
  -- origin-row mass through `toPMF`.
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
  have hpreimage :
      (fun z : LatticePoint d ↦ x + z) ⁻¹' ({y} : Set (LatticePoint d)) = {y - x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hz)
    · intro hz
      exact by simpa [add_comm] using (eq_sub_iff_add_eq.mp hz)
  rw [hpreimage, Measure.toPMF_toMeasure]
  rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton (y - x))]
  rw [tsum_eq_single (y - x)]
  · simp [htranslation x y]
  · intro z hz
    simp [Measure.smul_apply, Measure.dirac_apply', hz]

/-- Helper for Theorem 18.8: a translation-invariant lattice kernel is the convolution kernel
driven by its row at the origin. -/
lemma translationInvariantDiscreteKernel_eq_diracConvolutionKernel {d : ℕ}
    (p : LatticePoint d → LatticePoint d → ENNReal)
    (htranslation : IsTranslationInvariantStepMatrix p)
    [IsMarkovKernel (discreteMatrixKernel p)] :
    dirac_convolution_kernel ((discreteMatrixKernel p 0).toPMF.toMeasure) =
      discreteMatrixKernel p := by
  -- Proof comment: on the discrete lattice, kernel equality is determined by singleton masses,
  -- and the previous bridge lemma identifies each singleton row entry.
  ext x s hs
  exact congrArg (fun μ : Measure (LatticePoint d) ↦ μ s) <|
    Measure.ext_of_singleton fun y ↦ by
      rw [translationInvariantOriginRow_step_eq (p := p) htranslation x y]
      rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
      rw [tsum_eq_single y]
      · simp
      · intro z hz
        simp [Measure.smul_apply, Measure.dirac_apply', hz]

/-- Helper for Theorem 18.8: the convolution kernel driven by a PMF is a Markov kernel. -/
private lemma diracConvolutionKernel_isMarkovOfPMF {d : ℕ} (ν : PMF (LatticePoint d)) :
    IsMarkovKernel (dirac_convolution_kernel ν.toMeasure) := by
  -- Proof comment: each row is a Dirac translate of the probability measure `ν.toMeasure`.
  refine ⟨?_⟩
  intro x
  rw [dirac_convolution_kernel_apply]
  infer_instance

/-- Helper for Theorem 18.8: every iterate of the owner convolution kernel is again a Markov
kernel. -/
private lemma diracConvolutionKernel_pow_isMarkovOfPMF {d : ℕ}
    (ν : PMF (LatticePoint d)) (N : ℕ) :
    IsMarkovKernel (dirac_convolution_kernel ν.toMeasure ^ N) := by
  let κ : Kernel (LatticePoint d) (LatticePoint d) := dirac_convolution_kernel ν.toMeasure
  letI : IsMarkovKernel κ := by
    simpa [κ] using diracConvolutionKernel_isMarkovOfPMF ν
  induction N with
  | zero =>
      simpa [κ] using
        (inferInstance : IsMarkovKernel (Kernel.id : Kernel (LatticePoint d) (LatticePoint d)))
  | succ N ih =>
      letI : IsMarkovKernel (κ ^ N) := ih
      simpa [κ, pow_succ] using (inferInstance : IsMarkovKernel ((κ ^ N) ∘ₖ κ))

/-- Helper for Theorem 18.8: the singleton-mass matrix attached to
`dirac_convolution_kernel ν.toMeasure` recovers the kernel itself. -/
private lemma ownerStepMatrix_kernel_eq {d : ℕ} (ν : PMF (LatticePoint d)) :
    discreteMatrixKernel
        (fun x y ↦ dirac_convolution_kernel ν.toMeasure x ({y} : Set (LatticePoint d))) =
      dirac_convolution_kernel ν.toMeasure := by
  -- Proof comment: on the discrete lattice, kernel equality is determined by singleton masses.
  ext x s hs
  have hrow :
      discreteMatrixKernel
          (fun a b ↦ dirac_convolution_kernel ν.toMeasure a ({b} : Set (LatticePoint d))) x =
        dirac_convolution_kernel ν.toMeasure x := by
    refine Measure.ext_of_singleton ?_
    intro y
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
    rw [tsum_eq_single y]
    · simp
    · intro z hz
      simp [Measure.smul_apply, Measure.dirac_apply', hz]
  exact congrArg (fun μ ↦ μ s) hrow

/-- Helper for Theorem 18.8: the singleton-mass matrix of the owner kernel is stochastic. -/
private lemma ownerStepMatrix_isStochastic {d : ℕ} (ν : PMF (LatticePoint d)) :
    IsStochasticMatrix
      (fun x y ↦ dirac_convolution_kernel ν.toMeasure x ({y} : Set (LatticePoint d))) := by
  intro x
  -- Proof comment: the row sum is the total mass of the corresponding kernel row, which is `1`.
  calc
    ∑' y : LatticePoint d, dirac_convolution_kernel ν.toMeasure x ({y} : Set (LatticePoint d)) =
        discreteMatrixKernel
          (fun a b ↦ dirac_convolution_kernel ν.toMeasure a ({b} : Set (LatticePoint d))) x
            Set.univ := by
          exact
            (discreteMatrixKernel_univ
              (K := fun a b ↦ dirac_convolution_kernel ν.toMeasure a ({b} : Set (LatticePoint d)))
              x).symm
    _ = dirac_convolution_kernel ν.toMeasure x Set.univ := by
          rw [ownerStepMatrix_kernel_eq]
    _ = 1 := by
          rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
          rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
          simp

/-- Helper for Theorem 18.8: every stochastic matrix on a countable discrete space admits the
canonical path-space realization coming from `Kernel.trajMeasure`. -/
private theorem existsCanonicalDiscreteMatrixRealization
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (q : S → S → ENNReal) (hq : IsStochasticMatrix q) :
    ∃ P : S → ProbabilityMeasure (ℕ → S),
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel q ^ n) P Function.eval := by
  let κ : Kernel S S := discreteMatrixKernel q
  letI : IsMarkovKernel κ := discreteMatrixKernel_isMarkovKernel q hq
  let η : (n : ℕ) → Kernel (Π i : Finset.Iic n, S) S :=
    fun n ↦
      Kernel.comap κ
        (fun z : Π i : Finset.Iic n, S ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
        (by fun_prop)
  have hη : ∀ n : ℕ, IsMarkovKernel (η n) := by
    intro n
    dsimp [η]
    infer_instance
  let μ : S → Measure (ℕ → S) :=
    fun x ↦
      letI : ∀ n : ℕ, IsMarkovKernel (η n) := hη
      Kernel.trajMeasure (X := fun _ : ℕ ↦ S) (Measure.dirac x) η
  have hμ : ∀ x : S, IsProbabilityMeasure (μ x) := by
    intro x
    dsimp [μ]
    infer_instance
  let P : S → ProbabilityMeasure (ℕ → S) := fun x ↦ ⟨μ x, hμ x⟩
  refine ⟨P, ?_⟩
  refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
    (κ₁ := κ)
    (P := P)
    (X := Function.eval)
    (hmeas := fun n ↦ measurable_pi_apply n)
    ?_ ?_
  · intro x
    have hprefix :
        (μ x).map (Preorder.frestrictLe 0) = Measure.dirac (fun _ : Finset.Iic 0 ↦ x) := by
      letI : ∀ n : ℕ, IsMarkovKernel (η n) := hη
      simpa [μ, η, Kernel.partialTraj_self] using
        (Kernel.trajMeasure_map_frestrictLe
          (X := fun _ : ℕ ↦ S) (μ₀ := Measure.dirac x) (κ := η) 0)
    calc
      (P x : Measure (ℕ → S)).map (Function.eval 0) =
          ((μ x).map (Preorder.frestrictLe 0)).map
            (fun z : Finset.Iic 0 → S ↦ z ⟨0, Finset.mem_Iic.2 le_rfl⟩) := by
              rw [Measure.map_map (by fun_prop) (by fun_prop)]
              rfl
      _ = Measure.dirac x := by
            rw [hprefix]
            simp
  · intro x A hA s
    letI : Nonempty S := ⟨x⟩
    let H : (ℕ → S) → Finset.Iic s → S := Preorder.frestrictLe s
    have hH_meas : Measurable H := Preorder.measurable_frestrictLe s
    have hnext_meas : Measurable (Function.eval (s + 1) : (ℕ → S) → S) :=
      measurable_pi_apply (s + 1)
    have hcond :
        condDistrib (Function.eval (s + 1)) H (μ x) =ᵐ[(μ x).map H] η s := by
      letI : ∀ n : ℕ, IsMarkovKernel (η n) := hη
      simpa [μ, H, η] using
        (Kernel.condDistrib_trajMeasure
          (X := fun _ : ℕ ↦ S) (μ₀ := Measure.dirac x) (κ := η) (a := s))
    have hcondexp :
        (μ x)⟦(Function.eval (s + 1)) ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ x]
          fun ξ ↦ (condDistrib (Function.eval (s + 1)) H (μ x) (H ξ)).real A := by
      simpa using
        (condDistrib_ae_eq_condExp (μ := μ x) (X := H) (Y := Function.eval (s + 1))
          hH_meas hnext_meas hA).symm
    have hcond_comp :
        (fun ξ ↦ (condDistrib (Function.eval (s + 1)) H (μ x) (H ξ)).real A) =ᵐ[μ x]
          fun ξ ↦ (η s (H ξ)).real A := by
      filter_upwards [ae_eq_comp hH_meas.aemeasurable hcond] with ξ hξ
      simpa [Function.comp] using congrArg (fun ν : Measure S ↦ ν.real A) hξ
    have hgen :
        generatedFiltrationSpace (Function.eval : ℕ → (ℕ → S) → S) s =
          MeasurableSpace.comap (Preorder.frestrictLe s) inferInstance := by
      refine le_antisymm ?_ ?_
      · rw [generatedFiltrationSpace]
        refine iSup₂_le fun t ht ↦ ?_
        let i : Finset.Iic s := ⟨t, Finset.mem_Iic.2 ht⟩
        have hCoord :
            Measurable[
              MeasurableSpace.comap (Preorder.frestrictLe s) inferInstance]
              (Function.eval t : (ℕ → S) → S) := by
          simpa [Function.eval, Preorder.frestrictLe_apply, i] using
            (measurable_pi_apply i).comp (comap_measurable (Preorder.frestrictLe s))
        exact hCoord.comap_le
      · have hPrefix :
          Measurable[
            generatedFiltrationSpace (Function.eval : ℕ → (ℕ → S) → S) s]
            (Preorder.frestrictLe s : (ℕ → S) → Finset.Iic s → S) := by
          rw [@measurable_pi_iff]
          intro i
          refine Measurable.of_comap_le ?_
          exact le_iSup_of_le i.1 <| le_iSup_of_le (Finset.mem_Iic.1 i.2) le_rfl
        exact hPrefix.comap_le
    rw [hgen]
    exact hcondexp.trans <|
      hcond_comp.trans <|
        Filter.Eventually.of_forall fun ξ ↦ by
          simpa [η, H, Preorder.frestrictLe_apply] using
            congrArg (fun ν : Measure S ↦ ν.real A) rfl

/-- Helper for Theorem 18.8: the one-step kernel attached to the independent coalescent matrix. -/
private abbrev coalescentKernel {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    [DiscreteMeasurableSpace (E × E)]
    (p : E → E → ENNReal) : Kernel (E × E) (E × E) :=
  discreteMatrixKernel (independentCoalescentMatrix p)

/-- Helper for Theorem 18.8: the base one-step kernel attached to a transition matrix. -/
private abbrev baseKernel {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (p : E → E → ENNReal) : Kernel E E :=
  discreteMatrixKernel p

/-- Helper for Theorem 18.8: the powers of the coalescent one-step kernel form its semigroup. -/
private abbrev coalescentSemigroup {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    [DiscreteMeasurableSpace (E × E)]
    (p : E → E → ENNReal) : ℕ → Kernel (E × E) (E × E) :=
  fun n ↦ coalescentKernel p ^ n

/-- Helper for Theorem 18.8: postcomposing a process with a measurable map can only shrink its
generated history filtration. -/
private lemma generatedFiltrationSpace_comp_le {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] (X : ℕ → Ω → α) (f : α → β)
    (hf : Measurable f) (s : ℕ) :
    generatedFiltrationSpace (fun n ω ↦ f (X n ω)) s ≤ generatedFiltrationSpace X s := by
  -- Proof comment: every transformed coordinate is measurable with respect to the original
  -- coordinate sigma-algebra at the same time.
  rw [generatedFiltrationSpace]
  refine iSup_le fun n ↦ ?_
  refine iSup_le fun hn ↦ ?_
  have hXn :
      Measurable[generatedFiltrationSpace X s] (X n) := by
    exact Measurable.of_comap_le <| le_iSup_of_le n <| le_iSup_of_le hn le_rfl
  exact (hf.comp hXn).comap_le

/-- Helper for Theorem 18.8: the time-`s` coordinate sigma-algebra is contained in the generated
history filtration up to time `s`. -/
private lemma present_le_generatedHistory {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (s : ℕ) :
    MeasurableSpace.comap (X s) ‹MeasurableSpace α› ≤ generatedFiltrationSpace X s := by
  -- Proof comment: the defining supremum already contains the time-`s` coordinate sigma-algebra.
  exact le_iSup_of_le s <| le_iSup_of_le le_rfl le_rfl

/-- Helper for Theorem 18.8: if every coordinate is ambient-measurable, then the generated
history filtration is ambient-measurable as well. -/
private lemma generatedHistory_le_ambient {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (hX : ∀ n : ℕ, Measurable (X n)) (s : ℕ) :
    generatedFiltrationSpace X s ≤ ‹MeasurableSpace Ω› := by
  -- Proof comment: each coordinate sigma-algebra in the supremum already lies in the ambient
  -- measurable structure.
  refine iSup_le fun n ↦ ?_
  refine iSup_le fun hn ↦ ?_
  exact (hX n).comap_le

/-- Helper for Theorem 18.8: composing a process with a measurable equivalence does not change
its generated history filtration. -/
private lemma generatedFiltrationSpace_comp_measurableEquiv_eq
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (X : ℕ → Ω → α) (e : α ≃ᵐ β) (s : ℕ) :
    generatedFiltrationSpace (fun n ω ↦ e (X n ω)) s = generatedFiltrationSpace X s := by
  -- Proof comment: one inclusion is `generatedFiltrationSpace_comp_le`, and the reverse inclusion
  -- comes from applying the same lemma to the inverse measurable equivalence.
  refine le_antisymm ?_ ?_
  · exact generatedFiltrationSpace_comp_le X e e.measurable s
  · simpa using
      (generatedFiltrationSpace_comp_le
        (X := fun n ω ↦ e (X n ω)) (f := e.symm) e.symm.measurable s)

/-- Helper for Theorem 18.8: any transition matrix admitting a successful coupling is
stochastic. -/
private lemma successfulCoupling_stepMatrix_isStochastic
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]
    {q : E → E → ENNReal} (hq : HasSuccessfulCoupling q) :
    IsStochasticMatrix q := by
  rcases hq.exists_successfulCoupling with ⟨Ω, _, P, Z, hsuccess⟩
  intro x
  let hreal := hsuccess.toIsMarkovCoupling.fst_realization x
  have hstepMass :=
    congrArg (fun μ : Measure E ↦ μ Set.univ) (hreal.transition_eq x 1)
  -- Proof comment: the time-one marginal of the first coordinate is a probability measure, so its
  -- total mass reads off the row sum of `q`.
  calc
    ∑' y : E, q x y = ((discreteMatrixKernel q ^ 1) x) Set.univ := by
      simp [pow_one, discreteMatrixKernel_univ]
    _ = (((P (x, x) : ProbabilityMeasure Ω) : Measure Ω).map (fun ω ↦ (Z 1 ω).1)) Set.univ := by
      simpa [pow_one] using hstepMass.symm
    _ = 1 := by
      rw [Measure.map_apply (hreal.measurable_process 1) MeasurableSet.univ]
      simp

/-- Helper for Theorem 18.8: reindexing a discrete matrix kernel by a measurable equivalence is
the same as mapping each row measure through the inverse equivalence. -/
private lemma discreteMatrixKernel_transport_eq_map
    {E F : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]
    [MeasurableSpace F] [DiscreteMeasurableSpace F] [Countable F]
    (e : E ≃ᵐ F) (q : F → F → ENNReal) (x : F) :
    (((discreteMatrixKernel q) x).map e.symm) =
      discreteMatrixKernel (fun a b : E ↦ q (e a) (e b)) (e.symm x) := by
  -- Proof comment: on countable discrete spaces, it is enough to compare singleton masses, and
  -- the inverse-image of a singleton under `e.symm` is the corresponding singleton under `e`.
  refine Measure.ext_of_singleton ?_
  intro y
  rw [Measure.map_apply e.symm.measurable (measurableSet_singleton y)]
  have hpreimage : e.symm ⁻¹' ({y} : Set E) = {e y} := by
    ext z
    constructor
    · intro hz
      simpa using congrArg e hz
    · intro hz
      simpa using congrArg e.symm hz
  rw [hpreimage, discreteMatrixKernel_apply_singleton, discreteMatrixKernel_apply_singleton]
  simp

/-- Helper for Theorem 18.8: the real mass of a transported discrete row is computed by pulling
the target set back along the inverse measurable equivalence. -/
private lemma discreteMatrixKernel_transport_real
    {E F : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]
    [MeasurableSpace F] [DiscreteMeasurableSpace F] [Countable F]
    (e : E ≃ᵐ F) (q : F → F → ENNReal) (x : F) {A : Set E} (hA : MeasurableSet A) :
    ((discreteMatrixKernel q) x).real (e.symm ⁻¹' A) =
      (discreteMatrixKernel (fun a b : E ↦ q (e a) (e b)) (e.symm x)).real A := by
  -- Proof comment: apply the row-measure transport identity to the measurable set `A` and pass to
  -- real masses.
  exact
    congrArg ENNReal.toReal <| by
      simpa [Measure.map_apply e.symm.measurable hA] using
        congrArg (fun μ : Measure E ↦ μ A)
          (discreteMatrixKernel_transport_eq_map (e := e) (q := q) x)

/-- Helper for Theorem 18.8: a successful coupling transports across a measurable equivalence by
conjugating both coordinates and the step matrix. -/
private theorem hasSuccessfulCoupling_of_measurableEquiv
    {E F : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]
    [MeasurableSpace F] [DiscreteMeasurableSpace F] [Countable F]
    (e : E ≃ᵐ F) {q : F → F → ENNReal}
    (hq : HasSuccessfulCoupling q) :
    HasSuccessfulCoupling (fun x y : E ↦ q (e x) (e y)) := by
  rcases hq.exists_successfulCoupling with ⟨Ω, mΩ, P, Z, hsuccess⟩
  let P' : E × E → ProbabilityMeasure Ω := fun a ↦ P (e a.1, e a.2)
  let Z' : ℕ → Ω → E × E := fun n ω ↦ (e.symm (Z n ω).1, e.symm (Z n ω).2)
  have hq_stochastic : IsStochasticMatrix q :=
    successfulCoupling_stepMatrix_isStochastic hq
  have htransport_stochastic :
      IsStochasticMatrix (fun x y : E ↦ q (e x) (e y)) := by
    intro x
    -- Proof comment: the measurable equivalence simply reindexes the row sum of the original
    -- stochastic matrix.
    calc
      ∑' y : E, q (e x) (e y) = ∑' z : F, q (e x) z := by
        simpa using (e.tsum_eq (f := fun z : F ↦ q (e x) z))
      _ = 1 := hq_stochastic (e x)
  refine
    (ProbabilityTheory.HasSuccessfulCoupling.mk.{0, 0}
      (p := fun x y : E ↦ q (e x) (e y))) ?_
  refine ⟨Ω, mΩ, P', Z', ?_⟩
  refine
    { toIsMarkovCoupling := ?_
      tail_disagreement_tendsto_zero := ?_ }
  · refine
      { fst_realization := ?_
        snd_realization := ?_ }
    · intro y
      let r : E → E → ENNReal := fun x z ↦ q (e x) (e z)
      let hreal := hsuccess.toIsMarkovCoupling.fst_realization (e y)
      letI : IsMarkovKernel (discreteMatrixKernel r) :=
        discreteMatrixKernel_isMarkovKernel r htransport_stochastic
      refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
        (κ₁ := discreteMatrixKernel r)
        (P := fun x ↦ P' (x, y))
        (X := fun n ω ↦ e.symm ((Z n ω).1))
        (hmeas := fun n ↦ e.symm.measurable.comp (hreal.measurable_process n))
        (hstart := ?_)
        (hstep := ?_)
      · intro x
        -- Proof comment: transport the original deterministic start law through `e.symm`.
        calc
          (P' (x, y) : Measure Ω).map (fun ω ↦ e.symm ((Z 0 ω).1))
              = ((P (e x, e y) : Measure Ω).map (fun ω ↦ (Z 0 ω).1)).map e.symm := by
                  simpa [P', Function.comp] using
                    (Measure.map_map
                      (μ := (P (e x, e y) : Measure Ω))
                      (f := fun ω ↦ (Z 0 ω).1) (g := e.symm)
                      (hf := hreal.measurable_process 0)
                      (hg := e.symm.measurable)).symm
          _ = (Measure.dirac (e x)).map e.symm := by
                rw [hreal.initial_eq (e x)]
          _ = Measure.dirac x := by
                simp
      · intro x A hA s
        have hstep_old :
            (P (e x, e y))⟦(fun ω ↦ (Z (s + 1) ω).1) ⁻¹' (e.symm ⁻¹' A) |
              generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s⟧
              =ᵐ[(P (e x, e y) : Measure Ω)]
                fun ω ↦ ((discreteMatrixKernel q) ((Z s ω).1)).real (e.symm ⁻¹' A) :=
          hreal.markov_property (e x) (A := e.symm ⁻¹' A) (e.symm.measurable hA) s 1
        have hkernel :
            ∀ ω : Ω,
              ((discreteMatrixKernel q) ((Z s ω).1)).real (e.symm ⁻¹' A) =
                (discreteMatrixKernel r (e.symm ((Z s ω).1))).real A := by
          intro ω
          simpa [r] using
            discreteMatrixKernel_transport_real
              (e := e) (q := q) ((Z s ω).1) hA
        -- Proof comment: rewrite the conditioning sigma-algebra through the measurable
        -- equivalence and transport the one-step kernel on the right-hand side.
        have hstep_old' :
            (P' (x, y))⟦(fun ω ↦ e.symm ((Z (s + 1) ω).1)) ⁻¹' A |
              generatedFiltrationSpace (fun n ω ↦ e.symm ((Z n ω).1)) s⟧
              =ᵐ[(P' (x, y) : Measure Ω)]
                fun ω ↦ ((discreteMatrixKernel q) ((Z s ω).1)).real (e.symm ⁻¹' A) := by
          rw [generatedFiltrationSpace_comp_measurableEquiv_eq
            (X := fun n ω ↦ (Z n ω).1) (e := e.symm) s]
          simpa [P', Function.comp] using hstep_old
        exact hstep_old'.trans <| Filter.Eventually.of_forall hkernel
    · intro x
      let r : E → E → ENNReal := fun y z ↦ q (e y) (e z)
      let hreal := hsuccess.toIsMarkovCoupling.snd_realization (e x)
      letI : IsMarkovKernel (discreteMatrixKernel r) :=
        discreteMatrixKernel_isMarkovKernel r htransport_stochastic
      refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
        (κ₁ := discreteMatrixKernel r)
        (P := fun y ↦ P' (x, y))
        (X := fun n ω ↦ e.symm ((Z n ω).2))
        (hmeas := fun n ↦ e.symm.measurable.comp (hreal.measurable_process n))
        (hstart := ?_)
        (hstep := ?_)
      · intro y
        -- Proof comment: the second-coordinate start law transports by the same map argument.
        calc
          (P' (x, y) : Measure Ω).map (fun ω ↦ e.symm ((Z 0 ω).2))
              = ((P (e x, e y) : Measure Ω).map (fun ω ↦ (Z 0 ω).2)).map e.symm := by
                  simpa [P', Function.comp] using
                    (Measure.map_map
                      (μ := (P (e x, e y) : Measure Ω))
                      (f := fun ω ↦ (Z 0 ω).2) (g := e.symm)
                      (hf := hreal.measurable_process 0)
                      (hg := e.symm.measurable)).symm
          _ = (Measure.dirac (e y)).map e.symm := by
                rw [hreal.initial_eq (e y)]
          _ = Measure.dirac y := by
                simp
      · intro y A hA s
        have hstep_old :
            (P (e x, e y))⟦(fun ω ↦ (Z (s + 1) ω).2) ⁻¹' (e.symm ⁻¹' A) |
              generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s⟧
              =ᵐ[(P (e x, e y) : Measure Ω)]
                fun ω ↦ ((discreteMatrixKernel q) ((Z s ω).2)).real (e.symm ⁻¹' A) :=
          hreal.markov_property (e y) (A := e.symm ⁻¹' A) (e.symm.measurable hA) s 1
        have hkernel :
            ∀ ω : Ω,
              ((discreteMatrixKernel q) ((Z s ω).2)).real (e.symm ⁻¹' A) =
                (discreteMatrixKernel r (e.symm ((Z s ω).2))).real A := by
          intro ω
          simpa [r] using
            discreteMatrixKernel_transport_real
              (e := e) (q := q) ((Z s ω).2) hA
        -- Proof comment: as in the first coordinate, transport the history filtration and then
        -- rewrite the one-step kernel via the measurable equivalence.
        have hstep_old' :
            (P' (x, y))⟦(fun ω ↦ e.symm ((Z (s + 1) ω).2)) ⁻¹' A |
              generatedFiltrationSpace (fun n ω ↦ e.symm ((Z n ω).2)) s⟧
              =ᵐ[(P' (x, y) : Measure Ω)]
                fun ω ↦ ((discreteMatrixKernel q) ((Z s ω).2)).real (e.symm ⁻¹' A) := by
          rw [generatedFiltrationSpace_comp_measurableEquiv_eq
            (X := fun n ω ↦ (Z n ω).2) (e := e.symm) s]
          simpa [P', Function.comp] using hstep_old
        exact hstep_old'.trans <| Filter.Eventually.of_forall hkernel
  · intro x y
    -- Proof comment: because `e.symm` is injective, the transported process disagrees exactly
    -- when the original process disagrees.
    simpa [P', Z'] using hsuccess.tail_disagreement_tendsto_zero (e x) (e y)

/-- Helper for Theorem 18.8: on a history event fixing `X n = y`, the next-step singleton mass is
the one-step mass from `y` times the probability of that history event. -/
private lemma measureInter_eq_mul_stepMass_of_stateEvent
    {E Ω : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [MeasurableSpace Ω]
    {q : E → E → ENNReal}
    {P : E → ProbabilityMeasure Ω}
    {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X]
    (x y w : E) (n : ℕ) (A : Set Ω)
    (hA_meas : MeasurableSet A)
    (hA_measFiltration : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_state : ∀ ⦃ω : Ω⦄, ω ∈ A → X n ω = y) :
    (P x : Measure Ω) (A ∩ {ω | X (n + 1) ω = w}) =
      (discreteMatrixKernel q y ({w} : Set E)) * (P x : Measure Ω) A := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X := inferInstance
  letI : IsMarkovKernel (discreteMatrixKernel q) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  have hstep :
      ∀ x' : E, ∀ ⦃B : Set E⦄, MeasurableSet B → ∀ s : ℕ,
        (P x')⟦X (s + 1) ⁻¹' B | generatedFiltrationSpace X s⟧ =ᵐ[(P x' : Measure Ω)]
          fun ω ↦ ((discreteMatrixKernel q) (X s ω)).real B := by
    intro x' B hB s
    -- Proof comment: specialize the Markov property to one additional step and simplify `^ 1`.
    simpa [Nat.add_comm] using hReal.markov_property x' (A := B) hB s 1
  have hnext_meas : MeasurableSet (X (n + 1) ⁻¹' ({w} : Set E)) := by
    exact (hReal.measurable_process (n + 1)) (measurableSet_singleton w)
  have hslice_real :
      μ.real (A ∩ {ω | X (n + 1) ω = w}) =
        (discreteMatrixKernel q y ({w} : Set E)).toReal * μ.real A := by
    calc
      μ.real (A ∩ {ω | X (n + 1) ω = w}) =
          ∫ ω in A,
            Set.indicator (X (n + 1) ⁻¹' ({w} : Set E)) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
              rw [← MeasureTheory.integral_indicator hA_meas]
              -- Proof comment: rewrite the sliced singleton event as the indicator of the
              -- next-step singleton restricted to the history event `A`.
              simpa [Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
                Set.inter_comm, smul_eq_mul] using
                (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                  (hA_meas.inter hnext_meas)).symm
      _ =
          ∫ ω in A, ((discreteMatrixKernel q ^ 1) (X n ω)).real ({w} : Set E) ∂μ := by
            symm
            -- Proof comment: the restricted one-step event is exactly the owner Markov bridge on
            -- the history event.
            simpa [Nat.add_comm] using
              kernelPow_setIntegral_eq_on_history
                (κ₁ := discreteMatrixKernel q) (P := P) (X := X)
                hReal.measurable_process hstep x (A := ({w} : Set E))
                (measurableSet_singleton w) n 1 (B := A) hA_measFiltration
      _ = ∫ ω in A, (discreteMatrixKernel q y).real ({w} : Set E) ∂μ := by
            -- Proof comment: on `A`, the time-`n` state is fixed at `y`, so the integrand is
            -- constant.
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem hA_meas] with ω hω
            rw [hA_state hω]
            simp [pow_one]
      _ = (discreteMatrixKernel q y ({w} : Set E)).toReal * μ.real A := by
            rw [show ((discreteMatrixKernel q) y).real ({w} : Set E) =
                (((discreteMatrixKernel q) y) ({w} : Set E)).toReal by rfl]
            rw [MeasureTheory.setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
  have hslice_enn :
      μ (A ∩ {ω | X (n + 1) ω = w}) =
        (discreteMatrixKernel q y ({w} : Set E)) * μ A := by
    refine
      (ENNReal.toReal_eq_toReal_iff'
        (measure_lt_top μ _).ne
        (ENNReal.mul_ne_top
          (by exact (measure_lt_top (discreteMatrixKernel q y) ({w} : Set E)).ne)
          (by exact (measure_lt_top μ A).ne))).mp ?_
    simpa [μ, Measure.real_def, ENNReal.toReal_mul, mul_comm] using hslice_real
  simpa [μ] using hslice_enn

/-- Helper for Theorem 18.8: on a history event fixing `X n = y`, the future singleton mass after
`t` additional steps factors through the `t`-step kernel row from `y`. -/
private lemma measureInter_eq_mul_kernelPowMass_of_stateEvent
    {E Ω : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [MeasurableSpace Ω]
    {q : E → E → ENNReal}
    {P : E → ProbabilityMeasure Ω}
    {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X]
    (x y w : E) (n t : ℕ) (A : Set Ω)
    (hA_meas : MeasurableSet A)
    (hA_measFiltration : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_state : ∀ ⦃ω : Ω⦄, ω ∈ A → X n ω = y) :
    (P x : Measure Ω) (A ∩ {ω | X (n + t) ω = w}) =
      ((discreteMatrixKernel q ^ t) y ({w} : Set E)) * (P x : Measure Ω) A := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X := inferInstance
  letI : IsMarkovKernel (discreteMatrixKernel q) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  have hstep :
      ∀ x' : E, ∀ ⦃B : Set E⦄, MeasurableSet B → ∀ s : ℕ,
        (P x')⟦X (s + 1) ⁻¹' B | generatedFiltrationSpace X s⟧ =ᵐ[(P x' : Measure Ω)]
          fun ω ↦ ((discreteMatrixKernel q) (X s ω)).real B := by
    intro x' B hB s
    -- Proof comment: specialize the owner Markov property to one step and simplify `^ 1`.
    simpa [Nat.add_comm] using hReal.markov_property x' (A := B) hB s 1
  have hfuture_meas : MeasurableSet (X (n + t) ⁻¹' ({w} : Set E)) := by
    exact (hReal.measurable_process (n + t)) (measurableSet_singleton w)
  have hslice_real :
      μ.real (A ∩ {ω | X (n + t) ω = w}) =
        (((discreteMatrixKernel q ^ t) y) ({w} : Set E)).toReal * μ.real A := by
    calc
      μ.real (A ∩ {ω | X (n + t) ω = w}) =
          ∫ ω in A,
            Set.indicator (X (n + t) ⁻¹' ({w} : Set E)) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
              rw [← MeasureTheory.integral_indicator hA_meas]
              -- Proof comment: rewrite the sliced future event as the restricted indicator on
              -- the history event `A`.
              simpa [Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
                Set.inter_comm, smul_eq_mul] using
                (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                  (hA_meas.inter hfuture_meas)).symm
      _ =
          ∫ ω in A, ((discreteMatrixKernel q ^ t) (X n ω)).real ({w} : Set E) ∂μ := by
            symm
            -- Proof comment: the owner Markov bridge upgrades from one step to `t` steps on the
            -- same history event.
            simpa [Nat.add_comm] using
              kernelPow_setIntegral_eq_on_history
                (κ₁ := discreteMatrixKernel q) (P := P) (X := X)
                hReal.measurable_process hstep x (A := ({w} : Set E))
                (measurableSet_singleton w) n t (B := A) hA_measFiltration
      _ = ∫ ω in A, ((discreteMatrixKernel q ^ t) y).real ({w} : Set E) ∂μ := by
            -- Proof comment: on `A`, the time-`n` state is fixed, so the `t`-step row is
            -- constant.
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem hA_meas] with ω hω
            rw [hA_state hω]
      _ = (((discreteMatrixKernel q ^ t) y) ({w} : Set E)).toReal * μ.real A := by
            rw [show ((discreteMatrixKernel q ^ t) y).real ({w} : Set E) =
                (((discreteMatrixKernel q ^ t) y) ({w} : Set E)).toReal by rfl]
            rw [MeasureTheory.setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
  have hslice_enn :
      μ (A ∩ {ω | X (n + t) ω = w}) =
        ((discreteMatrixKernel q ^ t) y ({w} : Set E)) * μ A := by
    refine
      (ENNReal.toReal_eq_toReal_iff'
        (measure_lt_top μ _).ne
        (ENNReal.mul_ne_top
          (by exact (measure_lt_top ((discreteMatrixKernel q ^ t) y) ({w} : Set E)).ne)
          (by exact (measure_lt_top μ A).ne))).mp ?_
    simpa [μ, Measure.real_def, ENNReal.toReal_mul, mul_comm] using hslice_real
  simpa [μ] using hslice_enn

/-- Helper for Theorem 18.8: along any countable-state Markov realization, the realized one-step
transition at time `n` lands almost surely in the support of the row from the current state. -/
private lemma transitionMass_ne_zero_ae_of_markovRealization
    {E Ω : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]
    [MeasurableSpace Ω] {q : E → E → ENNReal}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X]
    (x : E) (n : ℕ) :
    ∀ᵐ ω ∂(P x : Measure Ω), q (X n ω) (X (n + 1) ω) ≠ 0 := by
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X := inferInstance
  let μ : Measure Ω := (P x : Measure Ω)
  let bad : Set Ω := {ω | q (X n ω) (X (n + 1) ω) = 0}
  let badSlice : E × E → Set Ω := fun z ↦
    if q z.1 z.2 = 0 then {ω | X n ω = z.1 ∧ X (n + 1) ω = z.2} else ∅
  have hbad_subset : bad ⊆ ⋃ z, badSlice z := by
    intro ω hω
    refine Set.mem_iUnion.2 ?_
    refine ⟨(X n ω, X (n + 1) ω), ?_⟩
    simpa [bad, badSlice] using hω
  have hslice_zero : ∀ z, μ (badSlice z) = 0 := by
    intro z
    rcases z with ⟨a, b⟩
    by_cases hz : q a b = 0
    · let A : Set Ω := {ω | X n ω = a}
      have hA_meas : MeasurableSet A := by
        -- Proof comment: the current-state atom is measurable because `X n` is measurable.
        exact hReal.measurable_process n (measurableSet_singleton a)
      have hXn_filtration :
          Measurable[generatedFiltrationSpace X n] (X n) := by
        exact Measurable.of_comap_le (present_le_generatedHistory X n)
      have hA_filtration : MeasurableSet[generatedFiltrationSpace X n] A := by
        -- Proof comment: the current-state atom is already visible in the time-`n` history
        -- filtration.
        exact hXn_filtration (measurableSet_singleton a)
      have hslice :=
        measureInter_eq_mul_stepMass_of_stateEvent
          (q := q) (P := P) (X := X)
          (x := x) (y := a) (w := b) (n := n) (A := A)
          hA_meas hA_filtration
          (by
            intro ω hω
            simpa [A] using hω)
      have hkernel_zero : discreteMatrixKernel q a ({b} : Set E) = 0 := by
        -- Proof comment: on the discrete kernel, the singleton row mass is exactly `q a b`.
        rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton b)]
        rw [tsum_eq_single b]
        · simpa [hz]
        · intro c hcb
          simp [Measure.smul_apply, Measure.dirac_apply', hcb]
      have hslice_zero' :
          μ ({ω | X n ω = a} ∩ {ω | X (n + 1) ω = b}) = 0 := by
        rw [hslice, hkernel_zero]
        simp
      -- Proof comment: the bad slice is exactly the history event `A` intersected with the next
      -- singleton `{X (n + 1) = b}`.
      simpa [badSlice, hz, A, Set.setOf_and] using hslice_zero'
    · simpa [badSlice, hz]
  have hbad_zero : μ bad = 0 := by
    have hle :
        μ bad ≤ 0 := by
      calc
        μ bad ≤ μ (⋃ z, badSlice z) := measure_mono hbad_subset
        _ ≤ ∑' z, μ (badSlice z) := measure_iUnion_le (fun z ↦ badSlice z)
        _ = 0 := by
            rw [ENNReal.tsum_eq_zero]
            intro z
            exact hslice_zero z
    exact le_antisymm hle (zero_le _)
  rw [ae_iff]
  simpa [bad]

/-- Helper for Theorem 18.8: summing an independent-coalescent row over the second coordinate
recovers the first-coordinate transition probability. -/
private lemma tsum_independentCoalescentMatrix_fst
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ENNReal} (hp : IsStochasticMatrix p) (x y z : E) :
    ∑' w : E, independentCoalescentMatrix p (x, y) (z, w) = p x z := by
  classical
  by_cases hxy : x = y
  · subst hxy
    rw [tsum_eq_single z]
    · rw [independentCoalescentMatrix_apply_diag]
    · intro w hw
      rw [independentCoalescentMatrix_apply_diag_of_ne (p := p)]
      exact fun hzw ↦ hw hzw.symm
  · calc
      ∑' w : E, independentCoalescentMatrix p (x, y) (z, w)
          = ∑' w : E, p x z * p y w := by
              refine tsum_congr fun w ↦ ?_
              rw [independentCoalescentMatrix_apply_of_ne (p := p) hxy]
      _ = p x z * ∑' w : E, p y w := by
            rw [ENNReal.tsum_mul_left]
      _ = p x z := by
            simp [hp y]

/-- Helper for Theorem 18.8: summing an independent-coalescent row over the first coordinate
recovers the second-coordinate transition probability. -/
private lemma tsum_independentCoalescentMatrix_snd
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ENNReal} (hp : IsStochasticMatrix p) (x y w : E) :
    ∑' z : E, independentCoalescentMatrix p (x, y) (z, w) = p y w := by
  classical
  by_cases hxy : x = y
  · subst hxy
    rw [tsum_eq_single w]
    · rw [independentCoalescentMatrix_apply_diag]
    · intro z hz
      rw [independentCoalescentMatrix_apply_diag_of_ne (p := p)]
      exact fun hzw ↦ hz hzw
  · calc
      ∑' z : E, independentCoalescentMatrix p (x, y) (z, w)
          = ∑' z : E, p x z * p y w := by
              refine tsum_congr fun z ↦ ?_
              rw [independentCoalescentMatrix_apply_of_ne (p := p) hxy]
      _ = (∑' z : E, p x z) * p y w := by
            rw [ENNReal.tsum_mul_right]
      _ = p y w := by
            simp [hp x]

/-- Helper for Theorem 18.8: any realization of the coalescent kernel forces the base matrix to
be stochastic. -/
private lemma baseMatrix_isStochastic_of_coalescentRealization
    {E Ω : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    [MeasurableSpace Ω] {p : E → E → ENNReal}
    (P : E × E → ProbabilityMeasure Ω) (Z : ℕ → Ω → E × E)
    [DiscreteMeasurableSpace (E × E)]
    [IsMarkovProcessRealization (coalescentSemigroup p) P Z] :
    IsStochasticMatrix p := by
  classical
  let hreal : IsMarkovProcessRealization (coalescentSemigroup p) P Z := inferInstance
  let _ : IsMarkovKernel (coalescentKernel p) := by
    simpa [coalescentSemigroup, coalescentKernel] using hreal.semigroup.isMarkovKernel 1
  intro x
  have hslice : ∀ z : E, ∑' w : E, independentCoalescentMatrix p (x, x) (z, w) = p x z := by
    intro z
    rw [tsum_eq_single z]
    · rw [independentCoalescentMatrix_apply_diag]
    · intro w hw
      rw [independentCoalescentMatrix_apply_diag_of_ne (p := p)]
      exact fun hzw ↦ hw hzw.symm
  have huniv : coalescentKernel p (x, x) Set.univ = 1 := by
    let hprob : IsProbabilityMeasure ((coalescentKernel p) (x, x)) :=
      (inferInstance : IsMarkovKernel (coalescentKernel p)).isProbabilityMeasure (x, x)
    exact hprob.measure_univ
  -- Proof comment: the diagonal coalescent row has total mass `1`, and its row sum collapses to
  -- the original row sum of `p`.
  calc
    ∑' z : E, p x z = ∑' z : E, ∑' w : E, independentCoalescentMatrix p (x, x) (z, w) := by
      refine tsum_congr fun z ↦ (hslice z).symm
    _ = ∑' s : E × E, independentCoalescentMatrix p (x, x) s := by
      simpa using
        (ENNReal.tsum_prod' (f := fun s : E × E ↦ independentCoalescentMatrix p (x, x) s)).symm
    _ = coalescentKernel p (x, x) Set.univ := by
      simp [coalescentKernel, discreteMatrixKernel_univ]
    _ = 1 := huniv

/-- Helper for Theorem 18.8: the first marginal of the coalescent one-step kernel is the base
kernel. -/
private lemma independentCoalescentKernel_fst
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    [DiscreteMeasurableSpace (E × E)]
    {p : E → E → ENNReal} (hp : IsStochasticMatrix p) :
    Kernel.fst (coalescentKernel p) =
      Kernel.comap (baseKernel p) Prod.fst measurable_fst := by
  classical
  refine Kernel.ext fun a => ?_
  rcases a with ⟨x, y⟩
  refine Measure.ext fun s hs ↦ ?_
  unfold coalescentKernel baseKernel
  rw [Kernel.fst_apply' _ _ hs, Kernel.comap_apply', discreteMatrixKernel_apply,
    discreteMatrixKernel_apply, Measure.sum_apply _ hs]
  calc
    (Measure.sum fun j ↦ independentCoalescentMatrix p (x, y) j • Measure.dirac j)
        (Prod.fst ⁻¹' s)
        = ∑' b : E × E,
            (independentCoalescentMatrix p (x, y) b • Measure.dirac b) (Prod.fst ⁻¹' s) := by
              rw [Measure.sum_apply _ (measurable_fst hs)]
    _ = ∑' b : E × E, independentCoalescentMatrix p (x, y) b * s.indicator 1 b.1 := by
          refine tsum_congr fun b ↦ ?_
          simp [Set.indicator, Measure.smul_apply, mul_comm]
    _ = ∑' z : E, ∑' w : E,
          independentCoalescentMatrix p (x, y) (z, w) * s.indicator 1 z := by
            simpa using
              (ENNReal.tsum_prod'
                (f := fun b : E × E ↦ independentCoalescentMatrix p (x, y) b * s.indicator 1 b.1))
    _ = ∑' z : E,
          (∑' w : E, independentCoalescentMatrix p (x, y) (z, w)) * s.indicator 1 z := by
          refine tsum_congr fun z ↦ ?_
          rw [ENNReal.tsum_mul_right]
    _ = ∑' z : E, p x z * s.indicator 1 z := by
          refine tsum_congr fun z ↦ ?_
          rw [tsum_independentCoalescentMatrix_fst hp x y z]
    _ = ∑' z : E, (p x z • Measure.dirac z) s := by
          refine tsum_congr fun z ↦ ?_
          simp [Measure.smul_apply]

/-- Helper for Theorem 18.8: the second marginal of the coalescent one-step kernel is the base
kernel. -/
private lemma independentCoalescentKernel_snd
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    [DiscreteMeasurableSpace (E × E)]
    {p : E → E → ENNReal} (hp : IsStochasticMatrix p) :
    Kernel.snd (coalescentKernel p) =
      Kernel.comap (baseKernel p) Prod.snd measurable_snd := by
  classical
  refine Kernel.ext fun a => ?_
  rcases a with ⟨x, y⟩
  refine Measure.ext fun s hs ↦ ?_
  unfold coalescentKernel baseKernel
  rw [Kernel.snd_apply' _ _ hs, Kernel.comap_apply', discreteMatrixKernel_apply,
    discreteMatrixKernel_apply, Measure.sum_apply _ hs]
  calc
    (Measure.sum fun j ↦ independentCoalescentMatrix p (x, y) j • Measure.dirac j)
        (Prod.snd ⁻¹' s)
        = ∑' b : E × E,
            (independentCoalescentMatrix p (x, y) b • Measure.dirac b) (Prod.snd ⁻¹' s) := by
              rw [Measure.sum_apply _ (measurable_snd hs)]
    _ = ∑' b : E × E, independentCoalescentMatrix p (x, y) b * s.indicator 1 b.2 := by
          refine tsum_congr fun b ↦ ?_
          simp [Set.indicator, Measure.smul_apply, mul_comm]
    _ = ∑' z : E, ∑' w : E,
          independentCoalescentMatrix p (x, y) (z, w) * s.indicator 1 w := by
            simpa using
              (ENNReal.tsum_prod'
                (f := fun b : E × E ↦ independentCoalescentMatrix p (x, y) b * s.indicator 1 b.2))
    _ = ∑' w : E, ∑' z : E,
          independentCoalescentMatrix p (x, y) (z, w) * s.indicator 1 w := by
            rw [ENNReal.tsum_comm]
    _ = ∑' w : E,
          (∑' z : E, independentCoalescentMatrix p (x, y) (z, w)) * s.indicator 1 w := by
          refine tsum_congr fun w ↦ ?_
          rw [ENNReal.tsum_mul_right]
    _ = ∑' w : E, p y w * s.indicator 1 w := by
          refine tsum_congr fun w ↦ ?_
          rw [tsum_independentCoalescentMatrix_snd hp x y w]
    _ = ∑' w : E, (p y w • Measure.dirac w) s := by
          refine tsum_congr fun w ↦ ?_
          simp [Measure.smul_apply]

/-- Helper for Theorem 18.8: the first coordinate of a coalescent realization satisfies the
one-step Markov property for the base kernel. -/
private lemma fst_oneStep_conditional
    {E Ω : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [MeasurableSpace Ω]
    {p : E → E → ENNReal}
    {P : E × E → ProbabilityMeasure Ω} {Z : ℕ → Ω → E × E}
    [DiscreteMeasurableSpace (E × E)]
    [IsMarkovProcessRealization (coalescentSemigroup p) P Z]
    (hp : IsStochasticMatrix p) (y x : E) (s : ℕ) {A : Set E} (hA : MeasurableSet A) :
    (P (x, y))⟦(fun ω ↦ (Z (s + 1) ω).1) ⁻¹' A |
      generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s⟧ =ᵐ[(P (x, y) : Measure Ω)]
        fun ω ↦ (baseKernel p ((Z s ω).1)).real A := by
  let μ : Measure Ω := (P (x, y) : Measure Ω)
  let hpair : IsMarkovProcessRealization (coalescentSemigroup p) P Z := inferInstance
  let g : Ω → ℝ := fun ω ↦ (baseKernel p ((Z s ω).1)).real A
  have hsmall_le :
      generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s ≤ generatedFiltrationSpace Z s := by
    exact generatedFiltrationSpace_comp_le Z Prod.fst measurable_fst s
  have hlarge_le : generatedFiltrationSpace Z s ≤ ‹MeasurableSpace Ω› := by
    exact generatedHistory_le_ambient Z hpair.measurable_process s
  have hstate :
      Measurable[generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s] fun ω ↦ (Z s ω).1 := by
    exact Measurable.of_comap_le <| present_le_generatedHistory (fun n ω ↦ (Z n ω).1) s
  have hg :
      AEStronglyMeasurable[generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s] g μ := by
    have hg_measurable :
        Measurable[generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s] g := by
      exact ((Kernel.measurable_coe (baseKernel p) hA).ennreal_toReal).comp hstate
    exact Measurable.aestronglyMeasurable hg_measurable
  have hpair_step :
      μ⟦(fun ω ↦ (Z (s + 1) ω).1) ⁻¹' A | generatedFiltrationSpace Z s⟧ =ᵐ[μ] g := by
    have hpair_raw :
        μ⟦(fun ω ↦ (Z (s + 1) ω).1) ⁻¹' A | generatedFiltrationSpace Z s⟧ =ᵐ[μ]
          fun ω ↦ ((discreteMatrixKernel (independentCoalescentMatrix p)) (Z s ω)).real
            (Prod.fst ⁻¹' A) := by
      simpa [Function.comp, pow_one, coalescentSemigroup, coalescentKernel, add_comm] using
        hpair.markov_property (x, y) (A := Prod.fst ⁻¹' A) (measurable_fst hA) s 1
    have hkernel :
        ∀ ω : Ω,
          ((discreteMatrixKernel (independentCoalescentMatrix p)) (Z s ω)).real (Prod.fst ⁻¹' A) =
            (baseKernel p ((Z s ω).1)).real A := by
      intro ω
      calc
        ((discreteMatrixKernel (independentCoalescentMatrix p)) (Z s ω)).real (Prod.fst ⁻¹' A)
            = ((Kernel.fst (coalescentKernel p)) (Z s ω)).real A := by
                simpa [coalescentKernel] using
                  (Kernel.fst_real_apply (coalescentKernel p) (Z s ω) (s := A) hA).symm
        _ = (baseKernel p ((Z s ω).1)).real A := by
              simpa [baseKernel, Kernel.comap_apply] using
                congrArg (fun κ : Kernel (E × E) E => (κ (Z s ω)).real A)
                  (independentCoalescentKernel_fst hp)
    exact hpair_raw.trans <| Filter.Eventually.of_forall hkernel
  have hg_int : Integrable g μ := by
    exact (integrable_congr hpair_step).1 integrable_condExp
  -- Proof comment: first rewrite the pair one-step conditional law through `Kernel.fst`, then
  -- shrink the conditioning sigma-algebra to the first-coordinate history.
  calc
    μ⟦(fun ω ↦ (Z (s + 1) ω).1) ⁻¹' A | generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s⟧
        =ᵐ[μ]
          MeasureTheory.condExp
            (μ := μ)
            (m := generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s)
            (MeasureTheory.condExp
              (μ := μ)
              (m := generatedFiltrationSpace Z s)
              (((fun ω ↦ (Z (s + 1) ω).1) ⁻¹' A).indicator fun _ ↦ (1 : ℝ))) := by
              symm
              exact condExp_condExp_of_le hsmall_le hlarge_le
    _ =ᵐ[μ]
          (MeasureTheory.condExp
            (μ := μ)
            (m := generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s)
            g) := by
          exact condExp_congr_ae hpair_step
    _ =ᵐ[μ] g := by
          exact condExp_of_aestronglyMeasurable' (hsmall_le.trans hlarge_le) hg hg_int

/-- Helper for Theorem 18.8: the second coordinate of a coalescent realization satisfies the
one-step Markov property for the base kernel. -/
private lemma snd_oneStep_conditional
    {E Ω : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [MeasurableSpace Ω]
    {p : E → E → ENNReal}
    {P : E × E → ProbabilityMeasure Ω} {Z : ℕ → Ω → E × E}
    [DiscreteMeasurableSpace (E × E)]
    [IsMarkovProcessRealization (coalescentSemigroup p) P Z]
    (hp : IsStochasticMatrix p) (x y : E) (s : ℕ) {A : Set E} (hA : MeasurableSet A) :
    (P (x, y))⟦(fun ω ↦ (Z (s + 1) ω).2) ⁻¹' A |
      generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s⟧ =ᵐ[(P (x, y) : Measure Ω)]
        fun ω ↦ (baseKernel p ((Z s ω).2)).real A := by
  let μ : Measure Ω := (P (x, y) : Measure Ω)
  let hpair : IsMarkovProcessRealization (coalescentSemigroup p) P Z := inferInstance
  let g : Ω → ℝ := fun ω ↦ (baseKernel p ((Z s ω).2)).real A
  have hsmall_le :
      generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s ≤ generatedFiltrationSpace Z s := by
    exact generatedFiltrationSpace_comp_le Z Prod.snd measurable_snd s
  have hlarge_le : generatedFiltrationSpace Z s ≤ ‹MeasurableSpace Ω› := by
    exact generatedHistory_le_ambient Z hpair.measurable_process s
  have hstate :
      Measurable[generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s] fun ω ↦ (Z s ω).2 := by
    exact Measurable.of_comap_le <| present_le_generatedHistory (fun n ω ↦ (Z n ω).2) s
  have hg :
      AEStronglyMeasurable[generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s] g μ := by
    have hg_measurable :
        Measurable[generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s] g := by
      exact ((Kernel.measurable_coe (baseKernel p) hA).ennreal_toReal).comp hstate
    exact Measurable.aestronglyMeasurable hg_measurable
  have hpair_step :
      μ⟦(fun ω ↦ (Z (s + 1) ω).2) ⁻¹' A | generatedFiltrationSpace Z s⟧ =ᵐ[μ] g := by
    have hpair_raw :
        μ⟦(fun ω ↦ (Z (s + 1) ω).2) ⁻¹' A | generatedFiltrationSpace Z s⟧ =ᵐ[μ]
          fun ω ↦ ((discreteMatrixKernel (independentCoalescentMatrix p)) (Z s ω)).real
            (Prod.snd ⁻¹' A) := by
      simpa [Function.comp, pow_one, coalescentSemigroup, coalescentKernel, add_comm] using
        hpair.markov_property (x, y) (A := Prod.snd ⁻¹' A) (measurable_snd hA) s 1
    have hkernel :
        ∀ ω : Ω,
          ((discreteMatrixKernel (independentCoalescentMatrix p)) (Z s ω)).real (Prod.snd ⁻¹' A) =
            (baseKernel p ((Z s ω).2)).real A := by
      intro ω
      calc
        ((discreteMatrixKernel (independentCoalescentMatrix p)) (Z s ω)).real (Prod.snd ⁻¹' A)
            = ((Kernel.snd (coalescentKernel p)) (Z s ω)).real A := by
                simpa [coalescentKernel, measureReal_def] using
                  congrArg ENNReal.toReal
                    (Kernel.snd_apply' (coalescentKernel p) (Z s ω) hA).symm
        _ = (baseKernel p ((Z s ω).2)).real A := by
              simpa [baseKernel, Kernel.comap_apply'] using
                congrArg (fun κ : Kernel (E × E) E => (κ (Z s ω)).real A)
                  (independentCoalescentKernel_snd hp)
    exact hpair_raw.trans <| Filter.Eventually.of_forall hkernel
  have hg_int : Integrable g μ := by
    exact (integrable_congr hpair_step).1 integrable_condExp
  -- Proof comment: rewrite the pair one-step conditional law through `Kernel.snd`, then shrink
  -- the conditioning sigma-algebra to the second-coordinate history.
  calc
    μ⟦(fun ω ↦ (Z (s + 1) ω).2) ⁻¹' A | generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s⟧
        =ᵐ[μ]
          MeasureTheory.condExp
            (μ := μ)
            (m := generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s)
            (MeasureTheory.condExp
              (μ := μ)
              (m := generatedFiltrationSpace Z s)
              (((fun ω ↦ (Z (s + 1) ω).2) ⁻¹' A).indicator fun _ ↦ (1 : ℝ))) := by
              symm
              exact condExp_condExp_of_le hsmall_le hlarge_le
    _ =ᵐ[μ]
          (MeasureTheory.condExp
            (μ := μ)
            (m := generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s)
            g) := by
          exact condExp_congr_ae hpair_step
    _ =ᵐ[μ] g := by
          exact condExp_of_aestronglyMeasurable' (hsmall_le.trans hlarge_le) hg hg_int

/-- Helper for Theorem 18.8: every realization of the independent coalescent semigroup already
provides the coordinate-chain part of a Markov coupling. -/
private lemma independentCoalescentChain_isMarkovCoupling_of_realization
    {E Ω : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [MeasurableSpace Ω]
    {p : E → E → ENNReal}
    {P : E × E → ProbabilityMeasure Ω} {Z : ℕ → Ω → E × E}
    [DiscreteMeasurableSpace (E × E)]
    (hrealization :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) P Z) :
    IsMarkovCoupling p P Z := by
  let hpair : IsMarkovProcessRealization (coalescentSemigroup p) P Z := by
    simpa [coalescentSemigroup, coalescentKernel] using hrealization
  letI : IsMarkovProcessRealization (coalescentSemigroup p) P Z := hpair
  let hp : IsStochasticMatrix p := baseMatrix_isStochastic_of_coalescentRealization P Z
  letI : IsMarkovKernel (baseKernel p) := discreteMatrixKernel_isMarkovKernel p hp
  refine
    { fst_realization := ?_
      snd_realization := ?_ }
  · intro y
    refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
      (κ₁ := baseKernel p)
      (P := fun x ↦ P (x, y))
      (X := fun n ω ↦ (Z n ω).1)
      (hmeas := fun n ↦ measurable_fst.comp (hpair.measurable_process n))
      (hstart := ?_)
      (hstep := ?_)
    · intro x
      let μ : Measure Ω := (P (x, y) : Measure Ω)
      have hmap :
          (μ.map (Z 0)).map Prod.fst = μ.map (fun ω ↦ (Z 0 ω).1) := by
        simpa [Function.comp] using
          (Measure.map_map (μ := μ) (f := Z 0) (g := Prod.fst)
            (hf := hpair.measurable_process 0) (hg := measurable_fst))
      -- Proof comment: the pair process starts at `(x,y)`, so the first coordinate starts at `x`.
      calc
        μ.map (fun ω ↦ (Z 0 ω).1) = (μ.map (Z 0)).map Prod.fst := hmap.symm
        _ = (Measure.dirac (x, y)).map Prod.fst := by
          rw [hpair.initial_eq (x, y)]
        _ = Measure.dirac x := by
          simp
    · intro x A hA s
      simpa using fst_oneStep_conditional hp y x s hA
  · intro x
    refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
      (κ₁ := baseKernel p)
      (P := fun y ↦ P (x, y))
      (X := fun n ω ↦ (Z n ω).2)
      (hmeas := fun n ↦ measurable_snd.comp (hpair.measurable_process n))
      (hstart := ?_)
      (hstep := ?_)
    · intro y
      let μ : Measure Ω := (P (x, y) : Measure Ω)
      have hmap :
          (μ.map (Z 0)).map Prod.snd = μ.map (fun ω ↦ (Z 0 ω).2) := by
        simpa [Function.comp] using
          (Measure.map_map (μ := μ) (f := Z 0) (g := Prod.snd)
            (hf := hpair.measurable_process 0) (hg := measurable_snd))
      -- Proof comment: the second coordinate starts at `y` by the same pushforward argument.
      calc
        μ.map (fun ω ↦ (Z 0 ω).2) = (μ.map (Z 0)).map Prod.snd := hmap.symm
        _ = (Measure.dirac (x, y)).map Prod.snd := by
          rw [hpair.initial_eq (x, y)]
        _ = Measure.dirac y := by
          simp
    · intro y A hA s
      simpa using snd_oneStep_conditional hp x y s hA

/-- Helper for Theorem 18.8: the finite cube of lattice increments with coordinates in
`{-1, 0, 1}`. -/
def uniformCubePoints (d : ℕ) : Finset (LatticePoint d) :=
  Fintype.piFinset fun _ : Fin d ↦ ({-1, 0, 1} : Finset ℤ)

/-- Helper for Theorem 18.8: an integer belongs to `{-1, 0, 1}` exactly when its absolute value
is at most `1`. -/
private lemma mem_threePointFinset_iff (z : ℤ) :
    z ∈ ({-1, 0, 1} : Finset ℤ) ↔ |z| ≤ 1 := by
  constructor
  · intro hz
    simp at hz
    rcases hz with rfl | rfl | rfl <;> norm_num
  · intro hz
    have hz' : -1 ≤ z ∧ z ≤ 1 := by
      simpa using abs_le.mp hz
    have hcases : z = -1 ∨ z = 0 ∨ z = 1 := by
      omega
    simpa using hcases

/-- Helper for Theorem 18.8: membership in the finite cube is equivalent to the coordinatewise
bound `|z i| ≤ 1`. -/
lemma mem_uniformCubePoints_iff {d : ℕ} {z : LatticePoint d} :
    z ∈ uniformCubePoints d ↔ ∀ i : Fin d, |z i| ≤ 1 := by
  constructor
  · intro hz i
    exact (mem_threePointFinset_iff (z i)).mp ((Fintype.mem_piFinset.mp hz) i)
  · intro hz
    exact Fintype.mem_piFinset.mpr fun i => (mem_threePointFinset_iff (z i)).mpr (hz i)

/-- Helper for Theorem 18.8: a `Fin.cons` lattice point belongs to the `(d+1)`-dimensional cube
exactly when its head coordinate lies in `{-1, 0, 1}` and its tail belongs to the
`d`-dimensional cube. -/
private lemma cons_mem_uniformCubePoints_iff {d : ℕ} {a : ℤ} {z : LatticePoint d} :
    Fin.cons a z ∈ uniformCubePoints (d + 1) ↔ |a| ≤ 1 ∧ z ∈ uniformCubePoints d := by
  -- Proof comment: `uniformCubePoints (d + 1)` is a product finset, so `Fin.cons` membership
  -- splits into the one-dimensional head condition and the `d`-dimensional tail condition.
  rw [mem_uniformCubePoints_iff, Fin.forall_fin_succ]
  constructor
  · intro h
    exact ⟨h.1, (mem_uniformCubePoints_iff (z := z)).2 h.2⟩
  · intro h
    exact ⟨h.1, (mem_uniformCubePoints_iff (z := z)).1 h.2⟩

/-- Helper for Theorem 18.8: the `d`-dimensional cube of allowed increments has cardinality
`3^d`. -/
private lemma uniformCubePoints_card (d : ℕ) :
    (uniformCubePoints d).card = 3 ^ d := by
  -- Proof comment: each coordinate has exactly three admissible values, and the cube is the full
  -- finite product over `Fin d`.
  simpa [uniformCubePoints] using
    (Fintype.card_piFinset_const ({-1, 0, 1} : Finset ℤ) d)

/-- Helper for Theorem 18.8: the origin belongs to the finite cube of allowed increments. -/
lemma zero_mem_uniformCubePoints (d : ℕ) :
    (0 : LatticePoint d) ∈ uniformCubePoints d := by
  -- Proof comment: every coordinate of the origin has absolute value `0`, hence lies in
  -- `{-1, 0, 1}`.
  rw [mem_uniformCubePoints_iff]
  intro i
  norm_num

/-- Helper for Theorem 18.8: if the lattice state space is not subsingleton, then the cube of
allowed increments contains a nonzero point. -/
private lemma exists_nonzero_uniformCubePoint_of_notSubsingleton {d : ℕ}
    (hns : ¬ Subsingleton (LatticePoint d)) :
    ∃ z : LatticePoint d, z ∈ uniformCubePoints d ∧ z ≠ 0 := by
  have hd_pos : 0 < d := by
    by_contra hd_pos
    have hd_zero : d = 0 := Nat.eq_zero_of_not_pos hd_pos
    apply hns
    subst hd_zero
    infer_instance
  let i : Fin d := ⟨0, hd_pos⟩
  let z : LatticePoint d := Function.update 0 i 1
  refine ⟨z, ?_, ?_⟩
  · -- Proof comment: the chosen point has one coordinate equal to `1` and all others equal to
    -- `0`, so it lies in the cube.
    rw [mem_uniformCubePoints_iff]
    intro j
    by_cases hji : j = i
    · subst hji
      simp [z]
    · simp [z, hji]
  · -- Proof comment: evaluating at the distinguished coordinate shows that the chosen cube point
    -- cannot be the origin.
    intro hz
    have hz_eval : z i = (0 : LatticePoint d) i := by simpa [hz]
    simpa [z] using hz_eval

/-- Helper for Theorem 18.8: the uniform law on the finite cube of increments. -/
def uniformCubeStepPMF (d : ℕ) : PMF (LatticePoint d) :=
  PMF.uniformOfFinset (uniformCubePoints d) ⟨0, zero_mem_uniformCubePoints d⟩

/-- Helper for Theorem 18.8: the cube law gives constant mass on cube points and zero outside. -/
lemma uniformCubeStepPMF_apply {d : ℕ} (z : LatticePoint d) :
    uniformCubeStepPMF d z =
      if z ∈ uniformCubePoints d then
        ((uniformCubePoints d).card : ENNReal)⁻¹
      else
        0 := by
  -- Proof comment: unfold the uniform PMF on the finite cube and use mathlib's explicit formula.
  simp [uniformCubeStepPMF]

/-- Helper for Theorem 18.8: the `(d+1)`-dimensional cube law on a `Fin.cons` point is supported
exactly on the split head-tail cube condition. -/
private lemma uniformCubeStepPMF_cons_apply {d : ℕ} (a : ℤ) (z : LatticePoint d) :
    uniformCubeStepPMF (d + 1) (Fin.cons a z) =
      if |a| ≤ 1 ∧ z ∈ uniformCubePoints d then
        ((uniformCubePoints (d + 1)).card : ENNReal)⁻¹
      else
        0 := by
  -- Proof comment: combine the explicit cube PMF formula with the `Fin.cons` support splitting
  -- lemma so later product arguments can reason on head and tail separately.
  rw [uniformCubeStepPMF_apply]
  simpa [cons_mem_uniformCubePoints_iff]

/-- Helper for Theorem 18.8: on cube increments, the uniform cube law has the expected constant
mass. -/
lemma uniformCubeStepPMF_apply_of_mem {d : ℕ} {z : LatticePoint d}
    (hz : z ∈ uniformCubePoints d) :
    uniformCubeStepPMF d z = ((uniformCubePoints d).card : ENNReal)⁻¹ := by
  -- Proof comment: specialize the explicit cube PMF formula to a support point.
  simp [uniformCubeStepPMF_apply, hz]

/-- Helper for Theorem 18.8: outside the cube, the uniform cube law vanishes. -/
lemma uniformCubeStepPMF_apply_of_notMem {d : ℕ} {z : LatticePoint d}
    (hz : z ∉ uniformCubePoints d) :
    uniformCubeStepPMF d z = 0 := by
  -- Proof comment: specialize the explicit cube PMF formula off the finite support.
  simp [uniformCubeStepPMF_apply, hz]

/-- Helper for Theorem 18.8: the owner kernel driven by `uniformCubeStepPMF d` depends only on
the increment `y - x`, and it is uniform exactly on the cube increments. -/
private lemma uniformCubeOwnerKernel_apply {d : ℕ} (x y : LatticePoint d) :
    dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure x ({y} : Set (LatticePoint d)) =
      if y - x ∈ uniformCubePoints d then
        ((uniformCubePoints d).card : ENNReal)⁻¹
      else
        0 := by
  -- Proof comment: translate the singleton target back to the increment `y - x` and then read
  -- off the mass from the explicit uniform cube PMF formula.
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
  have hpreimage :
      (fun z : LatticePoint d ↦ x + z) ⁻¹' ({y} : Set (LatticePoint d)) = {y - x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hz)
    · intro hz
      exact by simpa [add_comm] using (eq_sub_iff_add_eq.mp hz)
  rw [hpreimage, PMF.toMeasure_apply (p := uniformCubeStepPMF d)
    (measurableSet_singleton (y - x))]
  simp [uniformCubeStepPMF_apply]

/-- Helper for Theorem 18.8: a positive `n`-step singleton mass followed by a positive one-step
singleton mass yields a positive `(n + 1)`-step singleton mass. -/
private theorem kernelSingletonPos_succ
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (κ : Kernel E E) {x y z : E} {n : ℕ}
    (hxy : 0 < ((κ ^ n) x) ({y} : Set E))
    (hyz : 0 < κ y ({z} : Set E)) :
    0 < ((κ ^ (n + 1)) x) ({z} : Set E) := by
  have hmeas : Measurable fun w : E ↦ κ w ({z} : Set E) :=
    Kernel.measurable_coe κ (MeasurableSet.singleton z)
  have hySupport : y ∈ Function.support fun w : E ↦ κ w ({z} : Set E) := by
    change κ y ({z} : Set E) ≠ 0
    exact ne_of_gt hyz
  have hsupportPos :
      0 < ((κ ^ n) x) (Function.support fun w : E ↦ κ w ({z} : Set E)) :=
    measure_pos_of_superset (Set.singleton_subset_iff.mpr hySupport) hxy.ne'
  -- Proof comment: the positive intermediate state `y` lies in the integrand support of the
  -- one-step singleton mass, so the successor-step lintegral is strictly positive.
  rw [Kernel.pow_succ_apply_eq_lintegral κ n x (measurableSet_singleton z)]
  rw [MeasureTheory.lintegral_pos_iff_support hmeas]
  exact hsupportPos

/-- Helper for Theorem 18.8: the constant one-coordinate lattice point with value `z`. -/
private def oneDimPoint (z : ℤ) : LatticePoint 1 :=
  fun _ ↦ z

/-- Helper for Theorem 18.8: evaluating a one-dimensional lattice point at its unique coordinate
recovers the chosen integer. -/
private lemma oneDimPoint_apply_zero (z : ℤ) :
    oneDimPoint z 0 = z := rfl

/-- Helper for Theorem 18.8: every one-dimensional lattice point is determined by its unique
coordinate. -/
private lemma oneDimPoint_eq (x : LatticePoint 1) :
    oneDimPoint (x 0) = x := by
  -- Proof comment: `Fin 1` has only the zero coordinate, so extensionality reduces to that
  -- single value.
  ext i
  fin_cases i
  rfl

/-- Helper for Theorem 18.8: split a `(d + 1)`-dimensional lattice point into its head
coordinate and tail. -/
private def latticePointSuccMeasurableEquiv (d : ℕ) :
    LatticePoint (d + 1) ≃ᵐ (LatticePoint 1 × LatticePoint d) where
  toEquiv :=
    { toFun := fun x ↦ (oneDimPoint (x 0), fun i ↦ x i.succ)
      invFun := fun yz ↦ Fin.cons (yz.1 0) yz.2
      left_inv := by
        intro x
        -- Proof comment: rebuilding a finite function from its head and tail gives the original
        -- lattice point coordinatewise.
        ext i
        cases i using Fin.cases with
        | zero =>
            rfl
        | succ i =>
            rfl
      right_inv := by
        intro yz
        rcases yz with ⟨u, z⟩
        -- Proof comment: the head is determined by the unique coordinate of `u`, and the tail is
        -- left untouched.
        refine Prod.ext ?_ ?_
        · simpa [oneDimPoint] using oneDimPoint_eq u
        · funext i
          simp }
  measurable_toFun := Measurable.of_discrete
  measurable_invFun := Measurable.of_discrete

/-- Helper for Theorem 18.8: the successor split sends `Fin.cons a z` to the pair consisting of
its one-dimensional head and its tail. -/
private lemma latticePointSuccMeasurableEquiv_apply_cons {d : ℕ} (a : ℤ) (z : LatticePoint d) :
    latticePointSuccMeasurableEquiv d (Fin.cons a z) = (oneDimPoint a, z) := by
  -- Proof comment: both coordinates of the split are definitionally the head `a` and tail `z`.
  rfl

/-- Helper for Theorem 18.8: rebuilding from the successor split inserts the head coordinate back
with `Fin.cons`. -/
private lemma latticePointSuccMeasurableEquiv_symm_apply {d : ℕ}
    (u : LatticePoint 1) (z : LatticePoint d) :
    (latticePointSuccMeasurableEquiv d).symm (u, z) = Fin.cons (u 0) z := by
  -- Proof comment: the inverse map of the split equivalence is exactly `Fin.cons`.
  rfl

/-- Helper for Theorem 18.8: in dimension `1`, the uniform cube step law is the lazy
nearest-neighbor law on the unique coordinate. -/
private lemma uniformCubeStepPMF_one_apply (z : ℤ) :
    uniformCubeStepPMF 1 (oneDimPoint z) =
      if |z| ≤ 1 then (3 : ENNReal)⁻¹ else 0 := by
  have hz_mem :
      oneDimPoint z ∈ uniformCubePoints 1 ↔ |z| ≤ 1 := by
    simpa [oneDimPoint] using
      (mem_uniformCubePoints_iff (z := oneDimPoint z))
  rw [uniformCubeStepPMF_apply]
  by_cases h : |z| ≤ 1
  · simp [hz_mem.mpr h, h, uniformCubePoints_card]
  · simp [hz_mem.not.mpr h, h, uniformCubePoints_card]

/-- Helper for Theorem 18.8: the one-dimensional cube owner kernel depends only on the increment
between the start and target states. -/
private lemma uniformCubeKernelOne_apply (x y : ℤ) :
    dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure (oneDimPoint x)
        ({oneDimPoint y} : Set (LatticePoint 1)) =
      if |y - x| ≤ 1 then (3 : ENNReal)⁻¹ else 0 := by
  -- Proof comment: translate the singleton target back to the increment `y - x` and then use the
  -- explicit one-dimensional cube PMF formula.
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (oneDimPoint y))]
  have hpreimage :
      (fun z : LatticePoint 1 ↦ oneDimPoint x + z) ⁻¹' ({oneDimPoint y} : Set (LatticePoint 1)) =
        {oneDimPoint (y - x)} := by
    ext z
    constructor
    · intro hz
      have hz0 : oneDimPoint x 0 + z 0 = oneDimPoint y 0 := by
        simpa [Set.mem_preimage, Set.mem_singleton_iff, oneDimPoint_apply_zero] using
          congrArg (fun w : LatticePoint 1 ↦ w 0) hz
      have hz0' : x + z 0 = y := by
        simpa [oneDimPoint_apply_zero] using hz0
      have hzEq : z 0 = y - x := by
        have : x + z 0 = y := hz0'
        omega
      have : z = oneDimPoint (y - x) := by
        calc
          z = oneDimPoint (z 0) := (oneDimPoint_eq z).symm
          _ = oneDimPoint (y - x) := by simp [hzEq]
      simpa [Set.mem_singleton_iff] using this
    · intro hz
      have hzEq : z = oneDimPoint (y - x) := by
        simpa [Set.mem_singleton_iff] using hz
      have hzShift : z = -oneDimPoint x + oneDimPoint y := by
        ext i
        fin_cases i
        have : y - x = -x + y := by omega
        simpa [hzEq, oneDimPoint_apply_zero, this, sub_eq_add_neg, add_assoc, add_left_comm,
          add_comm]
      simpa [Set.mem_preimage, Set.mem_singleton_iff] using hzShift
  rw [hpreimage, PMF.toMeasure_apply (p := uniformCubeStepPMF 1)
    (measurableSet_singleton (oneDimPoint (y - x)))]
  simpa using uniformCubeStepPMF_one_apply (y - x)

/-- Helper for Theorem 18.8: the `(d+1)`-dimensional uniform-cube owner kernel factors into the
product of the head-coordinate cube owner kernel and the tail `d`-dimensional cube owner kernel. -/
private lemma uniformCubeOwnerKernel_cons_eq_product {d : ℕ}
    (a b : ℤ) (z w : LatticePoint d) :
    dirac_convolution_kernel (uniformCubeStepPMF (d + 1)).toMeasure (Fin.cons a z)
        ({Fin.cons b w} : Set (LatticePoint (d + 1))) =
      dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure (oneDimPoint a)
          ({oneDimPoint b} : Set (LatticePoint 1)) *
        dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure z ({w} : Set (LatticePoint d)) := by
  -- Proof comment: rewrite every singleton mass through the increment formula, split the
  -- `(d + 1)`-dimensional cube membership into head and tail conditions, and factor the uniform
  -- cube constant using `#uniformCubePoints (d + 1) = 3 * #uniformCubePoints d`.
  rw [uniformCubeOwnerKernel_apply, uniformCubeKernelOne_apply, uniformCubeOwnerKernel_apply]
  have hconsMem :
      Fin.cons b w - Fin.cons a z ∈ uniformCubePoints (d + 1) ↔
        |b - a| ≤ 1 ∧ w - z ∈ uniformCubePoints d := by
    rw [mem_uniformCubePoints_iff, Fin.forall_fin_succ, mem_uniformCubePoints_iff]
    constructor
    · intro h
      refine ⟨?_, h.2⟩
      simpa using h.1
    · intro h
      refine ⟨?_, h.2⟩
      simpa using h.1
  by_cases hab : |b - a| ≤ 1 <;> by_cases hzw : w - z ∈ uniformCubePoints d
  · have hcard :
        ((uniformCubePoints (d + 1)).card : ENNReal)⁻¹ =
          (3 : ENNReal)⁻¹ * ((uniformCubePoints d).card : ENNReal)⁻¹ := by
      rw [uniformCubePoints_card, uniformCubePoints_card, Nat.pow_succ, Nat.cast_mul, mul_comm]
      rw [ENNReal.mul_inv]
      · simp
      · simp
      · simp
    -- Proof comment: on the support of both factors, the mass is the product of the two uniform
    -- constants.
    have hmem : Fin.cons b w - Fin.cons a z ∈ uniformCubePoints (d + 1) :=
      hconsMem.mpr ⟨hab, hzw⟩
    simp [hmem, hab, hzw, hcard]
  · -- Proof comment: if the tail increment leaves the cube, the full `(d + 1)`-dimensional mass
    -- and the tail factor both vanish.
    have hnotMem : Fin.cons b w - Fin.cons a z ∉ uniformCubePoints (d + 1) := by
      intro hmem
      exact hzw (hconsMem.mp hmem).2
    simp [hnotMem, hab, hzw]
  · -- Proof comment: if the head increment leaves `{-1,0,1}`, the full mass and the head factor
    -- both vanish.
    have hnotMem : Fin.cons b w - Fin.cons a z ∉ uniformCubePoints (d + 1) := by
      intro hmem
      exact hab ((hconsMem.mp hmem).1)
    simp [hnotMem, hab, hzw]
  · -- Proof comment: off both support conditions, every factorized term is already zero.
    have hnotMem : Fin.cons b w - Fin.cons a z ∉ uniformCubePoints (d + 1) := by
      intro hmem
      exact hab ((hconsMem.mp hmem).1)
    simp [hnotMem, hab, hzw]

/-- Helper for Theorem 18.8: transporting a successor-dimensional cube-owner row through the
head-tail split yields the product of the one-dimensional and tail cube-owner rows. -/
private lemma uniformCubeOwnerKernel_succ_row_map_eq_parallel {d : ℕ}
    (x : LatticePoint (d + 1)) :
    Measure.map (latticePointSuccMeasurableEquiv d)
      (discreteMatrixKernel
        (fun u v : LatticePoint (d + 1) ↦
          dirac_convolution_kernel (uniformCubeStepPMF (d + 1)).toMeasure u
            ({v} : Set (LatticePoint (d + 1)))) x) =
      ((discreteMatrixKernel
          (fun u v : LatticePoint 1 ↦
            dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u
              ({v} : Set (LatticePoint 1)))) ∥ₖ
        (discreteMatrixKernel
          (fun u v : LatticePoint d ↦
            dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure u
              ({v} : Set (LatticePoint d)))))
        (latticePointSuccMeasurableEquiv d x) := by
  let a : ℤ := x 0
  let z : LatticePoint d := fun i ↦ x i.succ
  have hx : Fin.cons a z = x := by
    -- Proof comment: a finite lattice point is recovered by reattaching its head coordinate to
    -- its successor tail.
    ext i
    cases i using Fin.cases with
    | zero =>
        rfl
    | succ i =>
        rfl
  have hsplitx : latticePointSuccMeasurableEquiv d x = (oneDimPoint a, z) := by
    -- Proof comment: after rewriting `x` as `Fin.cons a z`, the split equivalence is explicit.
    simpa [hx, a, z] using latticePointSuccMeasurableEquiv_apply_cons (d := d) a z
  refine Measure.ext_of_singleton ?_
  intro y
  rcases y with ⟨u, w⟩
  have hpreimage :
      (latticePointSuccMeasurableEquiv d) ⁻¹' ({(u, w)} : Set (LatticePoint 1 × LatticePoint d)) =
        {Fin.cons (u 0) w} := by
    -- Proof comment: the only point mapping to the singleton target is the lattice point rebuilt
    -- from the head `u 0` and tail `w`.
    ext v
    constructor
    · intro hv
      have hv' := congrArg (fun yz ↦ (latticePointSuccMeasurableEquiv d).symm yz) hv
      simpa [latticePointSuccMeasurableEquiv_symm_apply] using hv'
    · intro hv
      rcases Set.mem_singleton_iff.mp hv with rfl
      simp [latticePointSuccMeasurableEquiv_apply_cons, oneDimPoint_eq u]
  have hsingleton :
      ({((u, w) : LatticePoint 1 × LatticePoint d)} : Set (LatticePoint 1 × LatticePoint d)) =
        ({u} : Set (LatticePoint 1)) ×ˢ ({w} : Set (LatticePoint d)) := by
    ext t
    simp
  let κ1 : Kernel (LatticePoint 1) (LatticePoint 1) :=
    discreteMatrixKernel
      (fun u v : LatticePoint 1 ↦
        dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1)))
  let κ2 : Kernel (LatticePoint d) (LatticePoint d) :=
    discreteMatrixKernel
      (fun u v : LatticePoint d ↦
        dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure u ({v} : Set (LatticePoint d)))
  letI : IsMarkovKernel κ1 := by
    simpa [κ1] using
      (discreteMatrixKernel_isMarkovKernel
        (fun u v : LatticePoint 1 ↦
          dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u
            ({v} : Set (LatticePoint 1)))
        (ownerStepMatrix_isStochastic (ν := uniformCubeStepPMF 1)))
  letI : IsMarkovKernel κ2 := by
    simpa [κ2] using
      (discreteMatrixKernel_isMarkovKernel
        (fun u v : LatticePoint d ↦
          dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure u
            ({v} : Set (LatticePoint d)))
        (ownerStepMatrix_isStochastic (ν := uniformCubeStepPMF d)))
  rw [Measure.map_apply (latticePointSuccMeasurableEquiv d).measurable
    (measurableSet_singleton (u, w))]
  rw [hpreimage, hsplitx, hsingleton, Kernel.parallelComp_apply_prod,
    discreteMatrixKernel_apply_singleton, discreteMatrixKernel_apply_singleton,
    discreteMatrixKernel_apply_singleton]
  -- Proof comment: the transported singleton row is exactly the factorization from
  -- `uniformCubeOwnerKernel_cons_eq_product`.
  simpa [a, z, hx, oneDimPoint_eq u] using
    uniformCubeOwnerKernel_cons_eq_product (d := d) a (u 0) z w

/-- Helper for Theorem 18.8: in one dimension, the cube owner kernel gives positive mass to the
lazy self-loop. -/
private lemma uniformCubeKernelOne_selfLoop_pos (x : ℤ) :
    0 <
      dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure (oneDimPoint x)
        ({oneDimPoint x} : Set (LatticePoint 1)) := by
  -- Proof comment: the zero increment belongs to the one-dimensional cube support with mass
  -- `1 / 3`.
  rw [uniformCubeKernelOne_apply]
  norm_num

/-- Helper for Theorem 18.8: in one dimension, the cube owner kernel gives positive mass to a
right jump by one lattice unit. -/
private lemma uniformCubeKernelOne_rightJump_pos (x : ℤ) :
    0 <
      dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure (oneDimPoint x)
        ({oneDimPoint (x + 1)} : Set (LatticePoint 1)) := by
  -- Proof comment: the increment `+1` lies in the one-dimensional cube support with mass `1 / 3`.
  rw [uniformCubeKernelOne_apply]
  norm_num

/-- Helper for Theorem 18.8: in one dimension, the cube owner kernel gives positive mass to a
left jump by one lattice unit. -/
private lemma uniformCubeKernelOne_leftJump_pos (x : ℤ) :
    0 <
      dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure (oneDimPoint x)
        ({oneDimPoint (x - 1)} : Set (LatticePoint 1)) := by
  -- Proof comment: the increment `-1` lies in the one-dimensional cube support with mass `1 / 3`.
  rw [uniformCubeKernelOne_apply]
  norm_num

/-- Helper for Theorem 18.8: following `n` successive right jumps in the one-dimensional cube walk
has strictly positive `n`-step mass. -/
private theorem uniformCubeKernelOne_rightPath_pos (x : ℤ) :
    ∀ n : ℕ,
      0 <
        ((dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure ^ n) (oneDimPoint x))
          ({oneDimPoint (x + n)} : Set (LatticePoint 1)) := by
  intro n
  induction n generalizing x with
  | zero =>
      -- Proof comment: the zero-step kernel is the identity, so it charges the starting point.
      simpa using
        (show 0 <
            (Kernel.id (oneDimPoint x)) ({oneDimPoint x} : Set (LatticePoint 1)) by
          simp [Kernel.id_apply])
  | succ n ih =>
      -- Proof comment: extend the positive `n`-step right path by one more positive right jump.
      have hstep :
          0 <
            dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure (oneDimPoint (x + n))
              ({oneDimPoint (x + (n + 1))} : Set (LatticePoint 1)) := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
          uniformCubeKernelOne_rightJump_pos (x + n)
      exact
        kernelSingletonPos_succ
          (κ := dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure)
          (hxy := ih x) (hyz := hstep)

/-- Helper for Theorem 18.8: following `n` successive left jumps in the one-dimensional cube walk
has strictly positive `n`-step mass. -/
private theorem uniformCubeKernelOne_leftPath_pos (x : ℤ) :
    ∀ n : ℕ,
      0 <
        ((dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure ^ n) (oneDimPoint x))
          ({oneDimPoint (x - n)} : Set (LatticePoint 1)) := by
  intro n
  induction n generalizing x with
  | zero =>
      -- Proof comment: the zero-step kernel is the identity, so it charges the starting point.
      simpa using
        (show 0 <
            (Kernel.id (oneDimPoint x)) ({oneDimPoint x} : Set (LatticePoint 1)) by
          simp [Kernel.id_apply])
  | succ n ih =>
      -- Proof comment: extend the positive `n`-step left path by one more positive left jump.
      have hstep :
          0 <
            dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure (oneDimPoint (x - n))
              ({oneDimPoint (x - (n + 1))} : Set (LatticePoint 1)) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          uniformCubeKernelOne_leftJump_pos (x - n)
      exact
        kernelSingletonPos_succ
          (κ := dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure)
          (hxy := ih x) (hyz := hstep)

/-- Helper for Theorem 18.8: the one-dimensional cube step law induces the expected
`{-1, 0, 1}`-valued coordinate law on `ℤ`. -/
private def uniformCubeOneCoordinateMeasure : Measure ℤ :=
  Measure.map (fun x : LatticePoint 1 ↦ x 0) (uniformCubeStepPMF 1).toMeasure

/-- Helper for Theorem 18.8: the one-dimensional coordinate law obtained from the cube walk is a
probability measure. -/
private lemma uniformCubeOneCoordinateMeasure_isProbability :
    IsProbabilityMeasure uniformCubeOneCoordinateMeasure := by
  -- Proof comment: the coordinate map pushes forward the probability law `uniformCubeStepPMF 1`.
  change IsProbabilityMeasure
    (Measure.map (fun x : LatticePoint 1 ↦ x 0) (uniformCubeStepPMF 1).toMeasure)
  exact Measure.isProbabilityMeasure_map (measurable_pi_apply 0).aemeasurable

/-- Helper for Theorem 18.8: the coordinate law of the one-dimensional cube walk has the explicit
lazy nearest-neighbor singleton masses. -/
private lemma uniformCubeOneCoordinateMeasure_apply (z : ℤ) :
    uniformCubeOneCoordinateMeasure ({z} : Set ℤ) =
      if |z| ≤ 1 then (3 : ENNReal)⁻¹ else 0 := by
  -- Proof comment: the coordinate map has the singleton fiber `oneDimPoint z`, so the explicit
  -- one-dimensional cube PMF formula transfers directly to `ℤ`.
  rw [uniformCubeOneCoordinateMeasure, Measure.map_apply (by fun_prop) (measurableSet_singleton z)]
  have hpreimage :
      (fun x : LatticePoint 1 ↦ x 0) ⁻¹' ({z} : Set ℤ) = {oneDimPoint z} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      ext i
      fin_cases i
      simpa [oneDimPoint_apply_zero] using hx
    · intro hx
      simpa [hx, oneDimPoint_apply_zero]
  rw [hpreimage, PMF.toMeasure_apply (p := uniformCubeStepPMF 1)
    (measurableSet_singleton (oneDimPoint z))]
  simpa using uniformCubeStepPMF_one_apply z

/-- Helper for Theorem 18.8: the difference of two independent one-dimensional cube increments is
the pushforward of the product coordinate law by subtraction. -/
private def uniformCubeOneDifferenceMeasure : Measure ℤ :=
  Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2)
    (uniformCubeOneCoordinateMeasure.prod uniformCubeOneCoordinateMeasure)

/-- Helper for Theorem 18.8: the one-dimensional cube-difference kernel is the convolution kernel
driven by the difference increment law. -/
private abbrev uniformCubeOneDifferenceKernel : Kernel ℤ ℤ :=
  dirac_convolution_kernel uniformCubeOneDifferenceMeasure

/-- Helper for Theorem 18.8: the one-dimensional cube-difference law has positive mass at `-1`. -/
private lemma uniformCubeOneDifferenceMeasure_negOne_pos :
    0 < uniformCubeOneDifferenceMeasure ({(-1 : ℤ)} : Set ℤ) := by
  let μ : Measure ℤ := uniformCubeOneCoordinateMeasure
  let diff : ℤ × ℤ → ℤ := fun s ↦ s.1 - s.2
  have hpair_pos :
      0 < (μ.prod μ) ({(0, 1)} : Set (ℤ × ℤ)) := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod (μ := μ) (ν := μ)
      ({0} : Set ℤ) ({1} : Set ℤ)]
    rw [uniformCubeOneCoordinateMeasure_apply, uniformCubeOneCoordinateMeasure_apply]
    norm_num
  have hsubset :
      ({(0, 1)} : Set (ℤ × ℤ)) ⊆ diff ⁻¹' ({(-1 : ℤ)} : Set ℤ) := by
    intro s hs
    simp only [Set.mem_singleton_iff] at hs
    simp [diff, hs]
  have hmap_pos :
      0 < Measure.map diff (μ.prod μ) ({(-1 : ℤ)} : Set ℤ) := by
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (-1 : ℤ))]
    exact lt_of_lt_of_le hpair_pos (measure_mono hsubset)
  simpa [uniformCubeOneDifferenceMeasure, μ, diff] using hmap_pos

/-- Helper for Theorem 18.8: the one-dimensional cube-difference law has positive mass at `1`. -/
private lemma uniformCubeOneDifferenceMeasure_posOne_pos :
    0 < uniformCubeOneDifferenceMeasure ({(1 : ℤ)} : Set ℤ) := by
  let μ : Measure ℤ := uniformCubeOneCoordinateMeasure
  let diff : ℤ × ℤ → ℤ := fun s ↦ s.1 - s.2
  have hpair_pos :
      0 < (μ.prod μ) ({(1, 0)} : Set (ℤ × ℤ)) := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod (μ := μ) (ν := μ)
      ({1} : Set ℤ) ({0} : Set ℤ)]
    rw [uniformCubeOneCoordinateMeasure_apply, uniformCubeOneCoordinateMeasure_apply]
    norm_num
  have hsubset :
      ({(1, 0)} : Set (ℤ × ℤ)) ⊆ diff ⁻¹' ({(1 : ℤ)} : Set ℤ) := by
    intro s hs
    simp only [Set.mem_singleton_iff] at hs
    simp [diff, hs]
  have hmap_pos :
      0 < Measure.map diff (μ.prod μ) ({(1 : ℤ)} : Set ℤ) := by
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (1 : ℤ))]
    exact lt_of_lt_of_le hpair_pos (measure_mono hsubset)
  simpa [uniformCubeOneDifferenceMeasure, μ, diff] using hmap_pos

/-- Helper for Theorem 18.8: the one-dimensional cube-difference law is again a probability
measure. -/
private lemma uniformCubeOneDifferenceMeasure_isProbability :
    IsProbabilityMeasure uniformCubeOneDifferenceMeasure := by
  -- Proof comment: the difference law is the pushforward of the product of two probability laws.
  letI : IsProbabilityMeasure uniformCubeOneCoordinateMeasure :=
    uniformCubeOneCoordinateMeasure_isProbability
  change IsProbabilityMeasure
    (Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2)
      (uniformCubeOneCoordinateMeasure.prod uniformCubeOneCoordinateMeasure))
  exact
    Measure.isProbabilityMeasure_map
      (μ := uniformCubeOneCoordinateMeasure.prod uniformCubeOneCoordinateMeasure) (by fun_prop)

/-- Helper for Theorem 18.8: the one-dimensional cube-difference law has finite first moment and
zero drift. -/
private lemma uniformCubeOneDifferenceMeasure_integrable_mean_zero :
    Integrable (fun z : ℤ ↦ (z : ℝ)) uniformCubeOneDifferenceMeasure ∧
      ∫ z, (z : ℝ) ∂uniformCubeOneDifferenceMeasure = 0 := by
  let μ : Measure ℤ := uniformCubeOneCoordinateMeasure
  letI : IsProbabilityMeasure μ := uniformCubeOneCoordinateMeasure_isProbability
  letI : IsFiniteMeasure μ := by infer_instance
  let ν : Measure (ℤ × ℤ) := μ.prod μ
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  letI : IsFiniteMeasure ν := by infer_instance
  let A : Set ℤ := {z | |z| ≤ 1}
  let B : Set (ℤ × ℤ) := {s | |s.1| ≤ 1 ∧ |s.2| ≤ 1}
  let f : ℤ × ℤ → ℝ := fun s ↦ ((s.1 - s.2 : ℤ) : ℝ)
  have hAcompl_zero : μ Aᶜ = 0 := by
    -- Proof comment: the one-dimensional coordinate law is supported on `{-1, 0, 1}`.
    change
      Measure.map (fun x : LatticePoint 1 ↦ x 0) (uniformCubeStepPMF 1).toMeasure Aᶜ = 0
    unfold uniformCubeOneCoordinateMeasure
    rw [Measure.map_apply (by fun_prop)
      (show MeasurableSet Aᶜ from MeasurableSet.of_discrete)]
    rw [PMF.toMeasure_apply_eq_tsum]
    refine ENNReal.tsum_eq_zero.2 ?_
    intro z
    by_cases hz : |z 0| ≤ 1
    · simp [A, hz]
    · have hz0 : uniformCubeStepPMF 1 z = 0 := by
        rw [← oneDimPoint_eq z]
        simpa [hz] using uniformCubeStepPMF_one_apply (z 0)
      simp [A, hz, hz0]
  have hBcompl_subset :
      Bᶜ ⊆ (Aᶜ ×ˢ (Set.univ : Set ℤ)) ∪ ((Set.univ : Set ℤ) ×ˢ Aᶜ) := by
    intro s hs
    by_cases hs₁ : |s.1| ≤ 1
    · right
      simp [A, B, hs₁] at hs ⊢
      exact hs
    · left
      simp [A, B, hs₁]
  have hBcompl_zero : ν Bᶜ = 0 := by
    have hfst_zero : ν (Aᶜ ×ˢ (Set.univ : Set ℤ)) = 0 := by
      rw [Measure.prod_prod, hAcompl_zero]
      simp [μ, ν]
    have hsnd_zero : ν ((Set.univ : Set ℤ) ×ˢ Aᶜ) = 0 := by
      rw [Measure.prod_prod, hAcompl_zero]
      simp [μ, ν]
    refine le_antisymm ?_ bot_le
    calc
      ν Bᶜ ≤ ν ((Aᶜ ×ˢ (Set.univ : Set ℤ)) ∪ ((Set.univ : Set ℤ) ×ˢ Aᶜ)) := by
            exact measure_mono hBcompl_subset
      _ ≤ ν (Aᶜ ×ˢ (Set.univ : Set ℤ)) + ν ((Set.univ : Set ℤ) ×ˢ Aᶜ) := by
            exact measure_union_le _ _
      _ = 0 := by rw [hfst_zero, hsnd_zero, zero_add]
  have hB_ae : ∀ᵐ s ∂ν, s ∈ B := by
    filter_upwards [compl_mem_ae_iff.2 hBcompl_zero] with s hs
    simpa using hs
  let g : ℤ × ℤ → ℝ := fun s ↦ if s ∈ B then f s else 0
  have hg_integrable : Integrable g ν := by
    -- Proof comment: on the nine-point support, the difference observable is bounded by `2`.
    refine (integrable_const (2 : ℝ)).mono'
      (Measurable.of_discrete.aestronglyMeasurable) <|
      Filter.Eventually.of_forall fun s => by
        by_cases hs : s ∈ B
        · have hs₁ : |s.1| ≤ 1 := hs.1
          have hs₂ : |s.2| ≤ 1 := hs.2
          have hs₁' : |(s.1 : ℝ)| ≤ 1 := by
            exact_mod_cast hs₁
          have hs₂' : |(s.2 : ℝ)| ≤ 1 := by
            exact_mod_cast hs₂
          have hbound : |((s.1 : ℝ) - s.2)| ≤ 2 := by
            calc
              |((s.1 : ℝ) - s.2)| = |(s.1 : ℝ) + (-(s.2 : ℝ))| := by ring_nf
              _ ≤ |(s.1 : ℝ)| + |-(s.2 : ℝ)| := abs_add_le _ _
              _ = |(s.1 : ℝ)| + |(s.2 : ℝ)| := by simp
              _ ≤ 2 := by linarith
          simpa [g, f, hs, Real.norm_eq_abs] using hbound
        · simp [g, hs]
  have hfg_ae : f =ᵐ[ν] g := by
    filter_upwards [hB_ae] with s hs
    simp [g, hs]
  have hf_integrable : Integrable f ν :=
    hg_integrable.congr hfg_ae.symm
  have hmap :
      uniformCubeOneDifferenceMeasure =
        Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2) ν := by
    rfl
  have h_map_integrable :
      Integrable (fun z : ℤ ↦ (z : ℝ))
        (Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2) ν) := by
    have hcomp_eq :
        ((fun z : ℤ ↦ (z : ℝ)) ∘ fun s : ℤ × ℤ ↦ s.1 - s.2) = f := by
      funext s
      simp [f, Function.comp]
    have hcomp_integrable :
        Integrable (((fun z : ℤ ↦ (z : ℝ)) ∘ fun s : ℤ × ℤ ↦ s.1 - s.2)) ν := by
      rw [hcomp_eq]
      exact hf_integrable
    exact
      (integrable_map_measure
        (Measurable.of_discrete.aestronglyMeasurable :
          AEStronglyMeasurable (fun z : ℤ ↦ (z : ℝ))
            (Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2) ν))
        (by fun_prop : AEMeasurable (fun s : ℤ × ℤ ↦ s.1 - s.2) ν)).2 hcomp_integrable
  refine ⟨by simpa [hmap] using h_map_integrable, ?_⟩
  have hswap_map : Measure.map Prod.swap ν = ν := by
    simpa [ν] using (Measure.prod_swap (μ := μ) (ν := μ))
  have hswap_neg : ∀ s : ℤ × ℤ, f s.swap = -f s := by
    intro s
    dsimp [f]
    have h : s.2 - s.1 = -(s.1 - s.2 : ℤ) := by
      omega
    exact_mod_cast h
  have hsymm :
      ∫ s, f s ∂ν = ∫ s, f s.swap ∂ν := by
    calc
      ∫ s, f s ∂ν = ∫ s, f s ∂Measure.map Prod.swap ν := by rw [hswap_map]
      _ = ∫ s, f (Prod.swap s) ∂ν := by
            rw [MeasureTheory.integral_map
              (by fun_prop : AEMeasurable Prod.swap ν)
              (Measurable.of_discrete.aestronglyMeasurable :
                AEStronglyMeasurable f (Measure.map Prod.swap ν))]
  have hzero_pair : ∫ s, f s ∂ν = 0 := by
    have hEq : ∫ s, f s ∂ν = -∫ s, f s ∂ν := by
      calc
        ∫ s, f s ∂ν = ∫ s, f s.swap ∂ν := hsymm
        _ = ∫ s, -f s ∂ν := by
              refine integral_congr_ae ?_
              exact Filter.Eventually.of_forall fun s ↦ hswap_neg s
        _ = -∫ s, f s ∂ν := by rw [integral_neg]
    linarith
  -- Proof comment: the mapped difference law inherits integrability from the bounded product
  -- support, and the mean vanishes because swapping the two coordinates negates the difference
  -- while preserving the symmetric product law.
  rw [hmap]
  calc
    ∫ z, (z : ℝ) ∂Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2) ν =
        ∫ s, ((s.1 - s.2 : ℤ) : ℝ) ∂ν := by
          rw [MeasureTheory.integral_map
            (by fun_prop : AEMeasurable (fun s : ℤ × ℤ ↦ s.1 - s.2) ν)
            (Measurable.of_discrete.aestronglyMeasurable :
              AEStronglyMeasurable (fun z : ℤ ↦ (z : ℝ))
                (Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2) ν))]
    _ = 0 := by simpa [f] using hzero_pair

/-- Helper for Theorem 18.8: every row of the one-dimensional cube-difference kernel has
positive mass to move one lattice step left. -/
private lemma uniformCubeOneDifferenceKernel_stepLeft_pos (t : ℤ) :
    0 < uniformCubeOneDifferenceKernel t ({t - 1} : Set ℤ) := by
  -- Proof comment: translation reduces the singleton target to the increment `-1`, which has
  -- positive mass under the difference law.
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (t - 1))]
  have hpreimage :
      (fun z : ℤ ↦ t + z) ⁻¹' ({t - 1} : Set ℤ) = {(-1 : ℤ)} := by
    ext z
    simp
    omega
  rw [hpreimage]
  exact uniformCubeOneDifferenceMeasure_negOne_pos

/-- Helper for Theorem 18.8: every row of the one-dimensional cube-difference kernel has
positive mass to move one lattice step right. -/
private lemma uniformCubeOneDifferenceKernel_stepRight_pos (t : ℤ) :
    0 < uniformCubeOneDifferenceKernel t ({t + 1} : Set ℤ) := by
  -- Proof comment: translation reduces the singleton target to the increment `1`, which has
  -- positive mass under the difference law.
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (t + 1))]
  have hpreimage :
      (fun z : ℤ ↦ t + z) ⁻¹' ({t + 1} : Set ℤ) = ({(1 : ℤ)} : Set ℤ) := by
    ext z
    simp
  rw [hpreimage]
  exact uniformCubeOneDifferenceMeasure_posOne_pos

/-- Helper for Theorem 18.8: every positive displacement reaches `0` by repeated left moves with
positive probability under the one-dimensional cube-difference kernel. -/
private theorem uniformCubeOneDifferenceKernel_leftPath_pos (x : ℤ) :
    ∀ n : ℕ, 0 < (uniformCubeOneDifferenceKernel ^ n) x ({x - n} : Set ℤ) := by
  intro n
  induction n with
  | zero =>
      simpa using
        (show 0 < (Kernel.id x) ({x} : Set ℤ) by simp [Kernel.id_apply])
  | succ n ih =>
      -- Proof comment: append one more positive left jump to the already positive path.
      have hstep :
          0 < uniformCubeOneDifferenceKernel (x - n) ({x - (n + 1)} : Set ℤ) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          uniformCubeOneDifferenceKernel_stepLeft_pos (x - n)
      exact kernelSingletonPos_succ (κ := uniformCubeOneDifferenceKernel) (hxy := ih)
        (hyz := hstep)

/-- Helper for Theorem 18.8: every positive displacement reaches `0` by repeated left moves with
positive probability under the one-dimensional cube-difference kernel. -/
private theorem uniformCubeOneDifferenceKernel_reachesZeroFromNat :
    ∀ n : ℕ, 0 < (uniformCubeOneDifferenceKernel ^ (n + 1)) (n + 1 : ℤ) ({0} : Set ℤ) := by
  intro n
  simpa using uniformCubeOneDifferenceKernel_leftPath_pos (x := (n + 1 : ℤ)) (n + 1)

/-- Helper for Theorem 18.8: every negative displacement reaches `0` by repeated right moves
with positive probability under the one-dimensional cube-difference kernel. -/
private theorem uniformCubeOneDifferenceKernel_rightPath_pos (x : ℤ) :
    ∀ n : ℕ, 0 < (uniformCubeOneDifferenceKernel ^ n) x ({x + n} : Set ℤ) := by
  intro n
  induction n with
  | zero =>
      simpa using
        (show 0 < (Kernel.id x) ({x} : Set ℤ) by simp [Kernel.id_apply])
  | succ n ih =>
      -- Proof comment: append one more positive right jump to the already positive path.
      have hstep :
          0 < uniformCubeOneDifferenceKernel (x + n) ({x + (n + 1)} : Set ℤ) := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
          uniformCubeOneDifferenceKernel_stepRight_pos (x + n)
      exact kernelSingletonPos_succ (κ := uniformCubeOneDifferenceKernel) (hxy := ih)
        (hyz := hstep)

/-- Helper for Theorem 18.8: every negative displacement reaches `0` by repeated right moves
with positive probability under the one-dimensional cube-difference kernel. -/
private theorem uniformCubeOneDifferenceKernel_reachesZeroFromNegNat :
    ∀ n : ℕ, 0 < (uniformCubeOneDifferenceKernel ^ (n + 1))
      (-((n + 1 : ℕ) : ℤ)) ({0} : Set ℤ) := by
  intro n
  simpa using uniformCubeOneDifferenceKernel_rightPath_pos (x := -((n + 1 : ℕ) : ℤ)) (n + 1)

/-- Helper for Theorem 18.8: every realization of the one-dimensional cube-difference walk hits
`0` almost surely from every start. -/
private theorem uniformCubeOneDifferenceHitsZero_eq_one
    {Ωq : Type*} [MeasurableSpace Ωq]
    {Pq : ℤ → ProbabilityMeasure Ωq}
    {Xq : ℕ → Ωq → ℤ}
    [IsMarkovProcessRealization (fun n ↦ uniformCubeOneDifferenceKernel ^ n) Pq Xq] :
    ∀ z : ℤ, (F[Pq, Xq]) z 0 = 1 := by
  let ν : ProbabilityMeasure ℤ := ⟨uniformCubeOneDifferenceMeasure, uniformCubeOneDifferenceMeasure_isProbability⟩
  have hconv :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) Pq Xq := by
    simpa [ν, uniformCubeOneDifferenceKernel] using
      (inferInstance :
        IsMarkovProcessRealization (fun n ↦ uniformCubeOneDifferenceKernel ^ n) Pq Xq)
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) Pq Xq := hconv
  have hν_moment := uniformCubeOneDifferenceMeasure_integrable_mean_zero
  have hrec : IsRecurrentMarkovChain Pq Xq := by
    simpa [ν, uniformCubeOneDifferenceKernel] using
      integerRandomWalk_recurrent_of_integrable_mean_zero
        (ν := ν) (P := Pq) (X := Xq) hν_moment.1 hν_moment.2
  intro z
  by_cases hz0 : z = 0
  · subst hz0
    simpa [IsRecurrentState] using hrec 0
  · let hproc : IsStochasticProcess Xq := fun n ↦
      (inferInstance :
        IsMarkovProcessRealization (fun n ↦ uniformCubeOneDifferenceKernel ^ n) Pq Xq).measurable_process n
    have hhit_pos : 0 < (F[Pq, Xq]) z 0 := by
      rcases lt_trichotomy z 0 with hzneg | rfl | hzpos
      · have hz_nonneg : 0 ≤ -z := by omega
        let n : ℕ := Int.toNat (-z)
        have hn_eq : (n : ℤ) = -z := by
          simpa [n] using Int.toNat_of_nonneg hz_nonneg
        cases hn : n with
        | zero =>
            exfalso
            have hz_eq : z = 0 := by
              have hnegz : (-z : ℤ) = 0 := by
                simpa [n, hn] using hn_eq
              omega
            exact hz0 hz_eq
        | succ m =>
            have hz_eq : z = -((m + 1 : ℕ) : ℤ) := by
              have hnegz : ((m + 1 : ℕ) : ℤ) = -z := by
                simpa [n, hn] using hn_eq
              omega
            have hstep :
                0 < (uniformCubeOneDifferenceKernel ^ (m + 1)) z ({0} : Set ℤ) := by
              have hbase :
                  0 < (uniformCubeOneDifferenceKernel ^ (m + 1))
                    (-((m + 1 : ℕ) : ℤ)) ({0} : Set ℤ) :=
                uniformCubeOneDifferenceKernel_reachesZeroFromNegNat m
              simpa [hz_eq] using hbase
            have hgreen : 0 < (G[Pq, Xq; 1]) z 0 :=
              greenFunctionFrom_one_pos_of_posStepMass
                (κ := fun n : ℕ ↦ uniformCubeOneDifferenceKernel ^ n)
                Pq Xq (Nat.succ_pos m) hstep
            exact
              (greenFunctionFrom_one_pos_iff_everHitsProbability_pos Pq Xq hproc z 0).1 hgreen
      · simp at hz0
      · have hz_nonneg : 0 ≤ z := le_of_lt hzpos
        let n : ℕ := Int.toNat z
        have hn_eq : (n : ℤ) = z := by
          simpa [n] using Int.toNat_of_nonneg hz_nonneg
        cases hn : n with
        | zero =>
            exfalso
            have hz_eq : z = 0 := by
              simpa [n, hn] using hn_eq.symm
            exact hz0 hz_eq
        | succ m =>
            have hz_eq : z = (m + 1 : ℤ) := by
              simpa [n, hn] using hn_eq.symm
            have hstep :
                0 < (uniformCubeOneDifferenceKernel ^ (m + 1)) z ({0} : Set ℤ) := by
              have hbase :
                  0 < (uniformCubeOneDifferenceKernel ^ (m + 1))
                    (m + 1 : ℤ) ({0} : Set ℤ) :=
                uniformCubeOneDifferenceKernel_reachesZeroFromNat m
              simpa [hz_eq] using hbase
            have hgreen : 0 < (G[Pq, Xq; 1]) z 0 :=
              greenFunctionFrom_one_pos_of_posStepMass
                (κ := fun n : ℕ ↦ uniformCubeOneDifferenceKernel ^ n)
                Pq Xq (Nat.succ_pos m) hstep
            exact
              (greenFunctionFrom_one_pos_iff_everHitsProbability_pos Pq Xq hproc z 0).1 hgreen
    -- Proof comment: recurrence of the starting state upgrades any positive hit probability to an
    -- almost-sure hit probability.
    exact
      everHitsProbability_eq_one_of_isRecurrentState_of_everHitsProbability_pos
        (P := Pq) (X := Xq)
        (κ := fun n : ℕ ↦ uniformCubeOneDifferenceKernel ^ n)
        (hrec z) hhit_pos

/-- Helper for Theorem 18.8: two one-dimensional lattice coordinates disagree exactly when their
difference is nonzero. -/
private theorem integerPairDisagreementEvent_eq_differenceEvent
    {Ω : Type*} [MeasurableSpace Ω] (Z : ℕ → Ω → ℤ × ℤ) (n : ℕ) :
    {ω | (Z n ω).1 ≠ (Z n ω).2} = {ω | (Z n ω).1 - (Z n ω).2 ≠ 0} := by
  -- Proof comment: on `ℤ`, equality of the two coordinates is equivalent to vanishing of their
  -- difference.
  ext ω
  change (Z n ω).1 ≠ (Z n ω).2 ↔ (Z n ω).1 - (Z n ω).2 ≠ 0
  constructor
  · intro h hsub
    exact h (sub_eq_zero.mp hsub)
  · intro h hxy
    exact h (sub_eq_zero.mpr hxy)

/-- Helper for Theorem 18.8: the singleton-mass presentation of the one-dimensional
cube-difference kernel. -/
private abbrev uniformCubeOneDifferenceStepMatrix : ℤ → ℤ → ENNReal :=
  fun x y ↦ uniformCubeOneDifferenceKernel x ({y} : Set ℤ)

/-- Helper for Theorem 18.8: absorbing an integer step matrix at `0` freezes the state `0` and
leaves all other rows unchanged. -/
private def absorbAtZeroIntegerStepMatrix (q : ℤ → ℤ → ENNReal) : ℤ → ℤ → ENNReal :=
  fun z w ↦ if z = 0 then if w = 0 then 1 else 0 else q z w

/-- Helper for Theorem 18.8: the absorbed-at-zero integer matrix has the Dirac row at `0`. -/
private lemma absorbAtZeroIntegerStepMatrix_apply_zero
    (q : ℤ → ℤ → ENNReal) (w : ℤ) :
    absorbAtZeroIntegerStepMatrix q 0 w = if w = 0 then 1 else 0 := by
  -- Proof comment: the absorbing row is built into the definition.
  simp [absorbAtZeroIntegerStepMatrix]

/-- Helper for Theorem 18.8: away from `0`, the absorbed-at-zero integer matrix agrees with the
original step matrix. -/
private lemma absorbAtZeroIntegerStepMatrix_apply_of_ne
    (q : ℤ → ℤ → ENNReal) {z w : ℤ} (hz : z ≠ 0) :
    absorbAtZeroIntegerStepMatrix q z w = q z w := by
  -- Proof comment: every nonzero row is copied verbatim from the original matrix.
  simp [absorbAtZeroIntegerStepMatrix, hz]

/-- Helper for Theorem 18.8: the absorbed-at-zero integer matrix stays stochastic when the
original step matrix is stochastic. -/
private lemma absorbAtZeroIntegerStepMatrix_isStochastic
    (q : ℤ → ℤ → ENNReal) (hq : IsStochasticMatrix q) :
    IsStochasticMatrix (absorbAtZeroIntegerStepMatrix q) := by
  intro z
  by_cases hz : z = 0
  · subst hz
    -- Proof comment: the absorbing row has exactly one nonzero entry.
    rw [tsum_eq_single (0 : ℤ)]
    · simp [absorbAtZeroIntegerStepMatrix]
    · intro w hw
      simp [absorbAtZeroIntegerStepMatrix, hw]
  · -- Proof comment: every nonzero row is unchanged, so stochasticity transfers directly.
    simp [absorbAtZeroIntegerStepMatrix, hz, hq z]

/-- Helper for Theorem 18.8: the endpoint-refined bounded zero-avoidance event for a free
integer walk. -/
private def avoidZeroUntilWithEndpoint {Ωq : Type*} [MeasurableSpace Ωq]
    (Xq : ℕ → Ωq → ℤ) (n : ℕ) (w : ℤ) : Set Ωq :=
  -- Proof comment: this records both the prescribed endpoint `Xq n = w` and avoidance of `0`
  -- up to time `n`.
  {ω | Xq n ω = w ∧ ∀ m ≤ n, Xq m ω ≠ 0}

/-- Helper for Theorem 18.8: bounded zero-avoidance with a fixed endpoint is measurable with
respect to the time-`n` history filtration. -/
private lemma avoidZeroUntilWithEndpoint_measurableSet
    {Ωq : Type*} [MeasurableSpace Ωq] {Xq : ℕ → Ωq → ℤ}
    (_hXq : ∀ n : ℕ, Measurable (Xq n)) (n : ℕ) (w : ℤ) :
    MeasurableSet[generatedFiltrationSpace Xq n] (avoidZeroUntilWithEndpoint Xq n w) := by
  have hState :
      MeasurableSet[generatedFiltrationSpace Xq n] {ω | Xq n ω = w} := by
    have hXqn : Measurable[generatedFiltrationSpace Xq n] (Xq n) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) n
    rw [show ({ω | Xq n ω = w} : Set Ωq) = Xq n ⁻¹' ({w} : Set ℤ) by
      ext ω
      simp]
    exact hXqn (measurableSet_singleton w)
  have hAvoid :
      MeasurableSet[generatedFiltrationSpace Xq n] {ω | ∀ m ≤ n, Xq m ω ≠ 0} := by
    have hrepr :
        {ω | ∀ m ≤ n, Xq m ω ≠ 0} =
          ⋂ m : ℕ, if m ≤ n then {ω | Xq m ω ≠ 0} else Set.univ := by
      ext ω
      simp
    rw [hrepr]
    refine MeasurableSet.iInter fun m ↦ ?_
    by_cases hm : m ≤ n
    · have hXqm : Measurable[generatedFiltrationSpace Xq n] (Xq m) := by
        exact Measurable.of_comap_le <|
          le_iSup_of_le m <| le_iSup_of_le hm le_rfl
      have hZero :
          MeasurableSet[generatedFiltrationSpace Xq n] {ω : Ωq | Xq m ω = (0 : ℤ)} := by
        rw [show ({ω : Ωq | Xq m ω = (0 : ℤ)} : Set Ωq) =
            Xq m ⁻¹' ({0} : Set ℤ) by
          ext ω
          simp]
        exact hXqm (measurableSet_singleton (0 : ℤ))
      have hNonzero :
          MeasurableSet[generatedFiltrationSpace Xq n] {ω : Ωq | Xq m ω ≠ (0 : ℤ)} := by
        rw [show ({ω : Ωq | Xq m ω ≠ (0 : ℤ)} : Set Ωq) =
            ({ω : Ωq | Xq m ω = (0 : ℤ)} : Set Ωq)ᶜ by
          ext ω
          simp]
        exact hZero.compl
      simpa [hm] using hNonzero
    · simp [hm]
  have hrepr :
      avoidZeroUntilWithEndpoint Xq n w =
        {ω | Xq n ω = w} ∩ {ω | ∀ m ≤ n, Xq m ω ≠ 0} := by
    ext ω
    simp [avoidZeroUntilWithEndpoint]
  -- Proof comment: both the endpoint condition and the bounded avoidance condition are already
  -- determined by the time-`n` history.
  rw [hrepr]
  exact hState.inter hAvoid

/-- Helper for Theorem 18.8: bounded zero-avoidance with endpoint `0` is impossible. -/
private lemma avoidZeroUntilWithEndpoint_eq_empty_of_zero
    {Ωq : Type*} [MeasurableSpace Ωq] {Xq : ℕ → Ωq → ℤ}
    (n : ℕ) :
    avoidZeroUntilWithEndpoint Xq n 0 = (∅ : Set Ωq) := by
  ext ω
  constructor
  · intro hω
    exact False.elim <| (hω.2 n le_rfl) hω.1
  · simp [avoidZeroUntilWithEndpoint]

/-- Helper for Theorem 18.8: bounded zero-avoidance with nonzero endpoint equals the
corresponding absorbed singleton mass. -/
private theorem freeAvoidZeroEndpointProb_eq_absorbedEndpointMass
    {Ωq : Type*} [MeasurableSpace Ωq]
    {q : ℤ → ℤ → ENNReal}
    {Pq : ℤ → ProbabilityMeasure Ωq}
    {Xq : ℕ → Ωq → ℤ}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq]
    [IsMarkovKernel (discreteMatrixKernel (absorbAtZeroIntegerStepMatrix q))] :
    ∀ n : ℕ, ∀ z : ℤ, ∀ {w : ℤ}, w ≠ 0 →
      (Pq z : Measure Ωq) (avoidZeroUntilWithEndpoint Xq n w) =
        ((discreteMatrixKernel (absorbAtZeroIntegerStepMatrix q) ^ n) z)
          ({w} : Set ℤ) := by
  let κAbs : Kernel ℤ ℤ := discreteMatrixKernel (absorbAtZeroIntegerStepMatrix q)
  let hqreal :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq := inferInstance
  intro n
  induction n with
  | zero =>
      intro z w hw
      have hset : avoidZeroUntilWithEndpoint Xq 0 w = {ω | Xq 0 ω = w} := by
        -- Proof comment: at time `0`, the endpoint condition already forces zero avoidance.
        ext ω
        constructor
        · intro hω
          exact hω.1
        · intro hω
          refine ⟨hω, ?_⟩
          intro m hm
          have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
          subst hm0
          intro hzero
          exact hw (hω.symm.trans hzero)
      rw [hset]
      rw [show ({ω | Xq 0 ω = w} : Set Ωq) = Xq 0 ⁻¹' ({w} : Set ℤ) by
        ext ω
        simp]
      rw [← Measure.map_apply (hqreal.measurable_process 0) (measurableSet_singleton w)]
      rw [hqreal.transition_eq z 0]
      simp
  | succ n ih =>
      intro z w hw
      let μ : Measure Ωq := (Pq z : Measure Ωq)
      have hUnion :
          avoidZeroUntilWithEndpoint Xq (n + 1) w =
            ⋃ c : ℤ,
              avoidZeroUntilWithEndpoint Xq n c ∩ {ω | Xq (n + 1) ω = w} := by
            ext ω
            constructor
            · intro hω
              refine Set.mem_iUnion.2 ⟨Xq n ω, ?_⟩
              refine ⟨?_, hω.1⟩
              refine ⟨rfl, ?_⟩
              intro m hm
              exact hω.2 m (Nat.le_trans hm (Nat.le_succ _))
            · intro hω
              rcases Set.mem_iUnion.1 hω with ⟨c, hcω⟩
              refine ⟨hcω.2, ?_⟩
              intro m hm
              rcases Nat.eq_or_lt_of_le hm with rfl | hm_lt
              · intro hzero
                exact hw (hcω.2.symm.trans hzero)
              · exact hcω.1.2 m (Nat.le_of_lt_succ hm_lt)
      have hPairwise :
          Pairwise fun c d : ℤ ↦
            Disjoint
              (avoidZeroUntilWithEndpoint Xq n c ∩ {ω | Xq (n + 1) ω = w})
              (avoidZeroUntilWithEndpoint Xq n d ∩ {ω | Xq (n + 1) ω = w}) := by
            intro c d hcd
            refine Set.disjoint_left.2 ?_
            intro ω hc hd
            apply hcd
            exact hc.1.1.symm.trans hd.1.1
      have hMeas :
          ∀ c : ℤ,
            MeasurableSet
              (avoidZeroUntilWithEndpoint Xq n c ∩ {ω | Xq (n + 1) ω = w}) := by
            intro c
            have hAvoid_hist :
                MeasurableSet[generatedFiltrationSpace Xq n]
                  (avoidZeroUntilWithEndpoint Xq n c) :=
              avoidZeroUntilWithEndpoint_measurableSet hqreal.measurable_process n c
            have hAvoid :
                MeasurableSet (avoidZeroUntilWithEndpoint Xq n c) := by
              exact (generatedHistory_le_ambient Xq hqreal.measurable_process n) _
                hAvoid_hist
            have hState :
                MeasurableSet ({ω | Xq (n + 1) ω = w} : Set Ωq) := by
              rw [show ({ω | Xq (n + 1) ω = w} : Set Ωq) =
                  Xq (n + 1) ⁻¹' ({w} : Set ℤ) by
                ext ω
                simp]
              exact (hqreal.measurable_process (n + 1)) (measurableSet_singleton w)
            exact hAvoid.inter hState
      -- Proof comment: decompose by the time-`n` endpoint, factor each history slice through the
      -- free one-step row, and replace that row by the absorbed row away from `0`.
      calc
        μ (avoidZeroUntilWithEndpoint Xq (n + 1) w) =
            ∑' c : ℤ,
              μ (avoidZeroUntilWithEndpoint Xq n c ∩ {ω | Xq (n + 1) ω = w}) := by
                rw [hUnion]
                exact MeasureTheory.measure_iUnion hPairwise hMeas
        _ =
            ∑' c : ℤ,
              (discreteMatrixKernel (absorbAtZeroIntegerStepMatrix q) c
                  ({w} : Set ℤ)) *
                ((κAbs ^ n) z) ({c} : Set ℤ) := by
                  refine tsum_congr fun c ↦ ?_
                  by_cases hc : c ≠ 0
                  · have hAvoid_meas :
                        MeasurableSet[generatedFiltrationSpace Xq n]
                          (avoidZeroUntilWithEndpoint Xq n c) :=
                      avoidZeroUntilWithEndpoint_measurableSet hqreal.measurable_process n c
                    have hAvoid_meas_ambient :
                        MeasurableSet (avoidZeroUntilWithEndpoint Xq n c) := by
                      exact
                        (generatedHistory_le_ambient Xq hqreal.measurable_process n) _
                          hAvoid_meas
                    have hAvoid_state :
                        ∀ ⦃ω : Ωq⦄, ω ∈ avoidZeroUntilWithEndpoint Xq n c → Xq n ω = c := by
                      intro ω hω
                      exact hω.1
                    rw [measureInter_eq_mul_stepMass_of_stateEvent
                      (q := q) (P := Pq) (X := Xq) z c w n
                      (avoidZeroUntilWithEndpoint Xq n c)
                      hAvoid_meas_ambient hAvoid_meas hAvoid_state]
                    rw [ih z hc, discreteMatrixKernel_apply_singleton,
                      discreteMatrixKernel_apply_singleton]
                    simpa [κAbs, absorbAtZeroIntegerStepMatrix, hc]
                  · have hczero : c = 0 := by simpa using hc
                    subst c
                    have hrow_zero :
                        discreteMatrixKernel (absorbAtZeroIntegerStepMatrix q) 0
                          ({w} : Set ℤ) = 0 := by
                      rw [discreteMatrixKernel_apply_singleton,
                        absorbAtZeroIntegerStepMatrix_apply_zero]
                      simp [hw]
                    rw [avoidZeroUntilWithEndpoint_eq_empty_of_zero (Xq := Xq) n]
                    rw [hrow_zero]
                    simp
        _ = ((κAbs ^ (n + 1)) z) ({w} : Set ℤ) := by
              rw [Kernel.pow_succ_apply_eq_lintegral κAbs n z (measurableSet_singleton w)]
              rw [MeasureTheory.lintegral_countable']

/-- Helper for Theorem 18.8: the nonzero mass of the absorbed difference walk is exactly the
bounded zero-avoidance probability of the free difference walk. -/
private theorem absorbedDifferenceNonzeroMass_eq_freeAvoidZeroProb
    {Ωq : Type*} [MeasurableSpace Ωq]
    {q : ℤ → ℤ → ENNReal}
    {Pq : ℤ → ProbabilityMeasure Ωq}
    {Xq : ℕ → Ωq → ℤ}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq]
    [IsMarkovKernel (discreteMatrixKernel (absorbAtZeroIntegerStepMatrix q))]
    (z : ℤ) (n : ℕ) :
    ((discreteMatrixKernel (absorbAtZeroIntegerStepMatrix q) ^ n) z)
        {w : ℤ | w ≠ 0} =
      (Pq z : Measure Ωq) {ω | ∀ m ≤ n, Xq m ω ≠ 0} := by
  let κAbs : Kernel ℤ ℤ := discreteMatrixKernel (absorbAtZeroIntegerStepMatrix q)
  let offDiag : Set ℤ := {w : ℤ | w ≠ 0}
  let μ : Measure Ωq := (Pq z : Measure Ωq)
  let hqreal :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq := inferInstance
  have hMass :
      ((κAbs ^ n) z) offDiag =
        ∑' w : {u : ℤ // u ∈ offDiag},
          ((κAbs ^ n) z) ({(w : ℤ)} : Set ℤ) := by
    calc
      ((κAbs ^ n) z) offDiag =
          ∑' w : ℤ,
            offDiag.indicator
              (fun w ↦ ((κAbs ^ n) z) ({w} : Set ℤ)) w := by
                simpa using
                  (Measure.tsum_indicator_apply_singleton ((κAbs ^ n) z) offDiag
                    (show MeasurableSet offDiag from MeasurableSet.of_discrete)).symm
      _ =
          ∑' w : {u : ℤ // u ∈ offDiag},
            ((κAbs ^ n) z) ({(w : ℤ)} : Set ℤ) := by
              rw [← tsum_subtype offDiag
                (fun w : ℤ ↦ ((κAbs ^ n) z) ({w} : Set ℤ))]
  have hUnion :
      {ω | ∀ m ≤ n, Xq m ω ≠ 0} =
        ⋃ w : {u : ℤ // u ∈ offDiag}, avoidZeroUntilWithEndpoint Xq n w := by
      ext ω
      constructor
      · intro hω
        refine Set.mem_iUnion.2 ⟨⟨Xq n ω, hω n le_rfl⟩, ?_⟩
        exact ⟨rfl, hω⟩
      · intro hω
        rcases Set.mem_iUnion.1 hω with ⟨w, hw⟩
        exact hw.2
  have hAvoid :
      μ {ω | ∀ m ≤ n, Xq m ω ≠ 0} =
        ∑' w : {u : ℤ // u ∈ offDiag},
          μ (avoidZeroUntilWithEndpoint Xq n w) := by
    have hPairwise :
        Pairwise fun w₁ w₂ : {u : ℤ // u ∈ offDiag} ↦
          Disjoint
            (avoidZeroUntilWithEndpoint Xq n (w₁ : ℤ))
            (avoidZeroUntilWithEndpoint Xq n (w₂ : ℤ)) := by
          intro w₁ w₂ hw
          refine Set.disjoint_left.2 ?_
          intro ω h₁ h₂
          apply hw
          exact Subtype.ext <| h₁.1.symm.trans h₂.1
    have hMeas :
        ∀ w : {u : ℤ // u ∈ offDiag},
          MeasurableSet (avoidZeroUntilWithEndpoint Xq n (w : ℤ)) := by
          intro w
          have hAvoid_hist :
              MeasurableSet[generatedFiltrationSpace Xq n]
                (avoidZeroUntilWithEndpoint Xq n (w : ℤ)) :=
            avoidZeroUntilWithEndpoint_measurableSet hqreal.measurable_process n (w : ℤ)
          exact
            (generatedHistory_le_ambient Xq hqreal.measurable_process n) _ hAvoid_hist
    rw [hUnion]
    exact MeasureTheory.measure_iUnion hPairwise hMeas
  -- Proof comment: decompose the absorbed nonzero mass into singleton endpoints and match each
  -- singleton mass with the corresponding bounded free zero-avoidance endpoint event.
  calc
    ((κAbs ^ n) z) offDiag =
        ∑' w : {u : ℤ // u ∈ offDiag},
          ((κAbs ^ n) z) ({(w : ℤ)} : Set ℤ) := hMass
    _ =
        ∑' w : {u : ℤ // u ∈ offDiag},
          μ (avoidZeroUntilWithEndpoint Xq n w) := by
            refine tsum_congr fun w ↦ ?_
            symm
            simpa [μ, offDiag] using
              freeAvoidZeroEndpointProb_eq_absorbedEndpointMass
                (Pq := Pq) (Xq := Xq) n z (w := (w : ℤ)) w.2
    _ = μ {ω | ∀ m ≤ n, Xq m ω ≠ 0} := hAvoid.symm

/-- Helper for Theorem 18.8: if the free walk hits `0` almost surely from every start, then the
bounded zero-avoidance probabilities converge to `0`. -/
private theorem freeAvoidZeroProb_tendsto_zero_of_hitsZero_eq_one
    {Ωq : Type*} [MeasurableSpace Ωq]
    {q : ℤ → ℤ → ENNReal}
    {Pq : ℤ → ProbabilityMeasure Ωq}
    {Xq : ℕ → Ωq → ℤ}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq]
    (hHit : ∀ z : ℤ, (F[Pq, Xq]) z 0 = 1) (z : ℤ) :
    Tendsto
      (fun n ↦ (Pq z : Measure Ωq) {ω | ∀ m ≤ n, Xq m ω ≠ 0})
      atTop (nhds 0) := by
  let μ : Measure Ωq := (Pq z : Measure Ωq)
  let avoidUpTo : ℕ → Set Ωq := fun n ↦ {ω | ∀ m ≤ n, Xq m ω ≠ 0}
  let noHit : Set Ωq := {ω | ∀ m : ℕ, Xq m ω ≠ 0}
  let noPositiveHit : Set Ωq := {ω | ∀ m : ℕ, 0 < m → Xq m ω ≠ 0}
  let hitZero : Set Ωq := {ω | ∃ m : ℕ, 0 < m ∧ Xq m ω = 0}
  let hReal :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq := inferInstance
  have hAvoid_meas : ∀ n : ℕ, MeasurableSet (avoidUpTo n) := by
    intro n
    have hrepr :
        avoidUpTo n = ⋂ m : ℕ, if m ≤ n then {ω | Xq m ω ≠ 0} else Set.univ := by
      ext ω
      simp [avoidUpTo]
    rw [hrepr]
    refine MeasurableSet.iInter fun m ↦ ?_
    by_cases hm : m ≤ n
    · have hZero : MeasurableSet ({ω : Ωq | Xq m ω = (0 : ℤ)} : Set Ωq) := by
        rw [show ({ω : Ωq | Xq m ω = (0 : ℤ)} : Set Ωq) =
            Xq m ⁻¹' ({0} : Set ℤ) by
          ext ω
          simp]
        exact (hReal.measurable_process m) (measurableSet_singleton (0 : ℤ))
      have hNonzero : MeasurableSet ({ω : Ωq | Xq m ω ≠ (0 : ℤ)} : Set Ωq) := by
        rw [show ({ω : Ωq | Xq m ω ≠ (0 : ℤ)} : Set Ωq) =
            ({ω : Ωq | Xq m ω = (0 : ℤ)} : Set Ωq)ᶜ by
          ext ω
          simp]
        exact hZero.compl
      simpa [hm] using hNonzero
    · simp [hm]
  have hNoPositiveHit_meas : MeasurableSet noPositiveHit := by
    have hrepr :
        noPositiveHit = ⋂ m : ℕ, if 0 < m then {ω | Xq m ω ≠ 0} else Set.univ := by
      ext ω
      simp [noPositiveHit]
    rw [hrepr]
    refine MeasurableSet.iInter fun m ↦ ?_
    by_cases hm : 0 < m
    · have hZero : MeasurableSet ({ω : Ωq | Xq m ω = (0 : ℤ)} : Set Ωq) := by
        rw [show ({ω : Ωq | Xq m ω = (0 : ℤ)} : Set Ωq) =
            Xq m ⁻¹' ({0} : Set ℤ) by
          ext ω
          simp]
        exact (hReal.measurable_process m) (measurableSet_singleton (0 : ℤ))
      have hNonzero : MeasurableSet ({ω : Ωq | Xq m ω ≠ (0 : ℤ)} : Set Ωq) := by
        rw [show ({ω : Ωq | Xq m ω ≠ (0 : ℤ)} : Set Ωq) =
            ({ω : Ωq | Xq m ω = (0 : ℤ)} : Set Ωq)ᶜ by
          ext ω
          simp]
        exact hZero.compl
      simpa [hm] using hNonzero
    · simp [hm]
  have hAntitone : Antitone avoidUpTo := by
    intro n m hnm ω hω k hk
    exact hω k (le_trans hk hnm)
  have hInter : (⋂ n : ℕ, avoidUpTo n) = noHit := by
    ext ω
    constructor
    · intro hω m
      exact (Set.mem_iInter.1 hω) m m le_rfl
    · intro hω
      refine Set.mem_iInter.2 ?_
      intro n
      exact fun m _ ↦ hω m
  have hHit_compl : hitZero = noPositiveHitᶜ := by
    ext ω
    simp [hitZero, noPositiveHit]
  have hNoHit_subset : noHit ⊆ noPositiveHit := by
    intro ω hω m hm
    exact hω m
  have hAvoid_tendsto :
      Tendsto (fun n ↦ μ (avoidUpTo n)) atTop (nhds (μ (⋂ n : ℕ, avoidUpTo n))) := by
    exact
      tendsto_measure_iInter_atTop
        (μ := μ)
        (s := avoidUpTo)
        (fun n ↦ (hAvoid_meas n).nullMeasurableSet)
        hAntitone
        ⟨0, by finiteness⟩
  have hHit_real : μ.real hitZero = 1 := by
    simpa [μ, hitZero, everHitsProbability_def] using hHit z
  have hNoPositiveHit_real : μ.real noPositiveHit = 0 := by
    have hsum :
        μ.real noPositiveHit + μ.real hitZero = μ.real Set.univ := by
      rw [hHit_compl]
      simpa using measureReal_add_measureReal_compl (μ := μ) hNoPositiveHit_meas
    have huniv : μ.real Set.univ = 1 := by
      simp [μ]
    linarith
  have hNoPositiveHit_zero : μ noPositiveHit = 0 := by
    exact (measureReal_eq_zero_iff (μ := μ) (s := noPositiveHit)).1 hNoPositiveHit_real
  have hInter_zero : μ (⋂ n : ℕ, avoidUpTo n) = 0 := by
    rw [hInter]
    exact le_antisymm
      (le_trans (measure_mono hNoHit_subset) hNoPositiveHit_zero.le)
      bot_le
  -- Proof comment: continuity from above reduces the bounded avoidance events to the infinite
  -- no-hit event, and the almost-sure hit hypothesis makes that limit event null.
  simpa [μ, hInter_zero] using hAvoid_tendsto

/-- Helper for Theorem 18.8: once the coalescent chain starts on the diagonal, the next step has
zero mass on the off-diagonal. -/
private lemma coalescentDiagonal_offDiagonalMass_eq_zero
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]
    {p : E → E → ENNReal} (hp : IsStochasticMatrix p) (x : E) :
    discreteMatrixKernel (independentCoalescentMatrix p) (x, x)
      {s : E × E | s.1 ≠ s.2} = 0 := by
  let κ : Kernel (E × E) (E × E) := discreteMatrixKernel (independentCoalescentMatrix p)
  let offDiag : Set (E × E) := {s | s.1 ≠ s.2}
  have hstochastic :
      IsStochasticMatrix (independentCoalescentMatrix p) := by
    exact independentCoalescentMatrix_isStochasticMatrix (p := p) hp
  letI : IsMarkovKernel κ := discreteMatrixKernel_isMarkovKernel
    (independentCoalescentMatrix p) hstochastic
  calc
    κ (x, x) offDiag
        = ∑' s : E × E, offDiag.indicator (fun s ↦ κ (x, x) ({s} : Set (E × E))) s := by
            simpa using
              (Measure.tsum_indicator_apply_singleton (κ (x, x)) offDiag
                (show MeasurableSet offDiag from MeasurableSet.of_discrete)).symm
    _ = 0 := by
          refine ENNReal.tsum_eq_zero.mpr ?_
          intro s
          by_cases hs : s.1 ≠ s.2
          · rcases s with ⟨z, w⟩
            have hsOff : (z, w) ∈ offDiag := by
              simpa [offDiag] using hs
            rw [Set.indicator_of_mem hsOff]
            rw [discreteMatrixKernel_apply_singleton]
            simpa using independentCoalescentMatrix_apply_diag_of_ne (p := p) (x := x) hs
          · have hsNotOff : s ∉ offDiag := by
              simpa [offDiag] using hs
            rw [Set.indicator_of_notMem hsNotOff]

/-- Helper for Theorem 18.8: once the coalescent chain reaches the diagonal, every later
off-diagonal mass vanishes. -/
private theorem coalescentDiagonal_offDiagonalMass_pow_eq_zero
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]
    {p : E → E → ENNReal}
    (hp : IsStochasticMatrix p) (x : E) :
    ∀ n : ℕ, 0 < n →
      ((discreteMatrixKernel (independentCoalescentMatrix p) ^ n) (x, x))
        {s : E × E | s.1 ≠ s.2} = 0 := by
  let κ : Kernel (E × E) (E × E) := discreteMatrixKernel (independentCoalescentMatrix p)
  let offDiag : Set (E × E) := {s | s.1 ≠ s.2}
  have hstochastic :
      IsStochasticMatrix (independentCoalescentMatrix p) := by
    exact independentCoalescentMatrix_isStochasticMatrix (p := p) hp
  letI : IsMarkovKernel κ := discreteMatrixKernel_isMarkovKernel
    (independentCoalescentMatrix p) hstochastic
  have hoffDiag_meas : MeasurableSet offDiag := MeasurableSet.of_discrete
  have hstep_le :
      ∀ z : E × E,
        κ z offDiag ≤ Set.indicator offDiag (fun _ ↦ (1 : ENNReal)) z := by
    intro z
    by_cases hz : z.1 ≠ z.2
    · have hzOff : z ∈ offDiag := by
        simpa [offDiag] using hz
      rw [Set.indicator_of_mem hzOff]
      calc
        κ z offDiag ≤ κ z Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := by
            simpa [κ, discreteMatrixKernel_univ] using hstochastic z
    · have hzNotOff : z ∉ offDiag := by
        simpa [offDiag] using hz
      rw [Set.indicator_of_notMem hzNotOff]
      rcases z with ⟨a, b⟩
      have hab : a = b := by
        simpa using hz
      subst b
      simpa [κ, offDiag] using coalescentDiagonal_offDiagonalMass_eq_zero (p := p) hp a
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  induction m with
  | zero =>
      -- Proof comment: at one step, the diagonal row already has zero off-diagonal mass.
      simpa [κ, offDiag] using coalescentDiagonal_offDiagonalMass_eq_zero (p := p) hp x
  | succ m ih =>
      -- Proof comment: the next Chapman-Kolmogorov step integrates the same one-step
      -- off-diagonal bound against a measure already supported on the diagonal.
      rw [Kernel.pow_succ_apply_eq_lintegral κ (m + 1) (x, x) hoffDiag_meas]
      refine le_antisymm ?_ bot_le
      calc
        ∫⁻ z, κ z offDiag ∂((κ ^ (m + 1)) (x, x)) ≤
            ∫⁻ z, Set.indicator offDiag (fun _ ↦ (1 : ENNReal)) z
              ∂((κ ^ (m + 1)) (x, x)) := by
                refine lintegral_mono ?_
                intro z
                exact hstep_le z
        _ = ((κ ^ (m + 1)) (x, x)) offDiag := by
            simp [offDiag, hoffDiag_meas]
        _ = 0 := ih (Nat.succ_pos _)

/-- Helper for Theorem 18.8: after time `n`, any later disagreement was already present at time
`n`, because the coalescent cannot leave the diagonal once it has entered it. -/
private lemma coalescentTailDisagreement_le_currentDisagreement
    {E Ω : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]
    [MeasurableSpace Ω]
    {p : E → E → ENNReal}
    {P : E × E → ProbabilityMeasure Ω} {Z : ℕ → Ω → E × E}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) P Z]
    (hp : IsStochasticMatrix p) (x y : E) :
    ∀ n : ℕ,
      (P (x, y) : Measure Ω) (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}) ≤
        (P (x, y) : Measure Ω) {ω | (Z n ω).1 ≠ (Z n ω).2} := by
  let μ : Measure Ω := P (x, y)
  let disagree : ℕ → Set Ω := fun n ↦ {ω | (Z n ω).1 ≠ (Z n ω).2}
  let hrealization :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) P Z :=
    inferInstance
  intro n
  have hfuture_null :
      μ ({ω | (Z n ω).1 = (Z n ω).2} ∩ ⋃ k : ℕ, disagree (n + (k + 1))) = 0 := by
    have hslice_zero :
        ∀ k : ℕ, μ ({ω | (Z n ω).1 = (Z n ω).2} ∩ disagree (n + (k + 1))) = 0 := by
      intro k
      have hcover :
          {ω | (Z n ω).1 = (Z n ω).2} ∩ disagree (n + (k + 1)) ⊆
            ⋃ z : E, ⋃ s : {t : E × E // t.1 ≠ t.2},
              ({ω | Z n ω = (z, z)} ∩ {ω | Z (n + (k + 1)) ω = s}) := by
        intro ω hω
        rcases hω with ⟨hdiag, hdis⟩
        refine Set.mem_iUnion.2 ?_
        refine ⟨(Z n ω).1, ?_⟩
        have hpair : Z n ω = ((Z n ω).1, (Z n ω).1) := by
          exact Prod.ext rfl hdiag.symm
        refine Set.mem_iUnion.2 ?_
        refine ⟨⟨Z (n + (k + 1)) ω, hdis⟩, ?_⟩
        constructor
        · exact hpair
        · rfl
      refine measure_mono_null hcover ?_
      refine measure_iUnion_null fun z ↦ ?_
      refine measure_iUnion_null fun s ↦ ?_
      have hslice_zero :
          μ ({ω | Z n ω = (z, z)} ∩ {ω | Z (n + (k + 1)) ω = s}) = 0 := by
        have hState_meas :
            MeasurableSet ({ω | Z n ω = (z, z)} : Set Ω) := by
          rw [show ({ω | Z n ω = (z, z)} : Set Ω) =
              Z n ⁻¹' ({(z, z)} : Set (E × E)) by
            ext ω
            simp]
          exact (hrealization.measurable_process n) (measurableSet_singleton (z, z))
        have hState_hist :
            MeasurableSet[generatedFiltrationSpace Z n] ({ω | Z n ω = (z, z)} : Set Ω) := by
          exact Measurable.of_comap_le
            (present_le_generatedHistory (X := Z) n) (measurableSet_singleton (z, z))
        have hState_fixed :
            ∀ ⦃ω : Ω⦄, ω ∈ ({ω | Z n ω = (z, z)} : Set Ω) → Z n ω = (z, z) := by
          intro ω hω
          exact hω
        have hMass :
            μ ({ω | Z n ω = (z, z)} ∩ {ω | Z (n + (k + 1)) ω = s}) =
              ((discreteMatrixKernel (independentCoalescentMatrix p) ^ (k + 1)) (z, z))
                ({(s : E × E)} : Set (E × E)) *
                μ ({ω | Z n ω = (z, z)} : Set Ω) := by
          simpa [μ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            measureInter_eq_mul_kernelPowMass_of_stateEvent
              (q := independentCoalescentMatrix p) (P := P) (X := Z)
              (x := (x, y)) (y := (z, z)) (w := (s : E × E))
              n (k + 1) ({ω | Z n ω = (z, z)} : Set Ω)
              hState_meas hState_hist hState_fixed
        have hpow_zero :
            ((discreteMatrixKernel (independentCoalescentMatrix p) ^ (k + 1)) (z, z))
              ({(s : E × E)} : Set (E × E)) = 0 := by
          have hoffdiag :
              ((discreteMatrixKernel (independentCoalescentMatrix p) ^ (k + 1)) (z, z))
                {t : E × E | t.1 ≠ t.2} = 0 := by
            exact coalescentDiagonal_offDiagonalMass_pow_eq_zero (p := p) hp z (k + 1)
              (Nat.succ_pos k)
          refine le_antisymm ?_ bot_le
          calc
            ((discreteMatrixKernel (independentCoalescentMatrix p) ^ (k + 1)) (z, z))
                ({(s : E × E)} : Set (E × E)) ≤
              ((discreteMatrixKernel (independentCoalescentMatrix p) ^ (k + 1)) (z, z))
                {t : E × E | t.1 ≠ t.2} := by
                  refine measure_mono ?_
                  intro t ht
                  simp only [Set.mem_singleton_iff] at ht
                  simpa [ht] using s.2
            _ = 0 := hoffdiag
        rw [hMass, hpow_zero]
        simp
      exact hslice_zero
    have hUnion :
        ({ω | (Z n ω).1 = (Z n ω).2} ∩ ⋃ k : ℕ, disagree (n + (k + 1))) =
          ⋃ k : ℕ, ({ω | (Z n ω).1 = (Z n ω).2} ∩ disagree (n + (k + 1))) := by
      ext ω
      simp [Set.mem_iUnion, and_left_comm, and_assoc]
    rw [hUnion]
    exact measure_iUnion_null hslice_zero
  have hUnion :
      (⋃ m ≥ n, disagree m) = disagree n ∪ ⋃ k : ℕ, disagree (n + (k + 1)) := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨m, hm⟩
      rcases Set.mem_iUnion.1 hm with ⟨hmn, hdis⟩
      rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
      · exact Or.inl hdis
      · have hkExists : ∃ k : ℕ, n + (k + 1) = m := ⟨m - n - 1, by omega⟩
        rcases hkExists with ⟨k, hk⟩
        exact Or.inr <| Set.mem_iUnion.2 ⟨k, hk ▸ hdis⟩
    · intro hω
      rcases hω with hω | hω
      · exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨le_rfl, hω⟩⟩
      · rcases Set.mem_iUnion.1 hω with ⟨k, hk⟩
        exact Set.mem_iUnion.2 ⟨n + (k + 1), Set.mem_iUnion.2 ⟨by omega, hk⟩⟩
  have hsubset :
      ⋃ k : ℕ, disagree (n + (k + 1)) ⊆
        disagree n ∪ ({ω | (Z n ω).1 = (Z n ω).2} ∩ ⋃ k : ℕ, disagree (n + (k + 1))) := by
    intro ω hω
    by_cases hdis : (Z n ω).1 ≠ (Z n ω).2
    · exact Or.inl hdis
    · have hEq : (Z n ω).1 = (Z n ω).2 := by
        by_contra hneq
        exact hdis hneq
      exact Or.inr ⟨hEq, hω⟩
  -- Proof comment: split the tail into the present disagreement slice and the strictly later
  -- disagreements; the latter can only occur on a null event where the chain is already on the
  -- diagonal at time `n` and then leaves it again.
  calc
    μ (⋃ m ≥ n, disagree m)
        = μ (disagree n ∪ ⋃ k : ℕ, disagree (n + (k + 1))) := by
            rw [hUnion]
    _ ≤ μ (disagree n) +
          μ ({ω | (Z n ω).1 = (Z n ω).2} ∩ ⋃ k : ℕ, disagree (n + (k + 1))) := by
          refine le_trans (measure_mono ?_) (measure_union_le _ _)
          intro ω hω
          rcases hω with hω | hω
          · exact Or.inl hω
          · exact hsubset hω
    _ = μ (disagree n) := by rw [hfuture_null, add_zero]

/-- Helper for Theorem 18.8: the coordinate projection of a one-dimensional cube row is the
translation of the common increment law by the starting point. -/
private lemma uniformCubeOneCoordinateRow_eq_shiftedIncrement (x : ℤ) :
    Measure.map (fun u : LatticePoint 1 ↦ u 0)
      (dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure (oneDimPoint x)) =
        Measure.map (fun z : ℤ ↦ x + z) uniformCubeOneCoordinateMeasure := by
  refine Measure.ext_of_singleton ?_
  intro w
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton w)]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton w)]
  have hleft :
      (fun u : LatticePoint 1 ↦ u 0) ⁻¹' ({w} : Set ℤ) = {oneDimPoint w} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hu
      ext i
      fin_cases i
      simpa [oneDimPoint_apply_zero] using hu
    · intro hu
      simpa [hu, oneDimPoint_apply_zero]
  have hright :
      (fun z : ℤ ↦ x + z) ⁻¹' ({w} : Set ℤ) = {w - x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      omega
    · intro hz
      omega
  rw [hleft, hright]
  -- Proof comment: both singleton masses are the same explicit lazy nearest-neighbor value.
  simpa using
    Eq.trans
      (uniformCubeKernelOne_apply x w)
      (uniformCubeOneCoordinateMeasure_apply (w - x)).symm

/-- Helper for Theorem 18.8: off the diagonal, a one-dimensional cube coalescent row is the
product of the two one-step rows. -/
private lemma uniformCubeOneCoalescentRow_eq_prod_of_ne
    {x y : ℤ} (hxy : x ≠ y) :
    discreteMatrixKernel
        (independentCoalescentMatrix
          (fun u v ↦
            dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1))))
        (oneDimPoint x, oneDimPoint y) =
      (dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure (oneDimPoint x)).prod
        (dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure (oneDimPoint y)) := by
  refine Measure.ext_of_singleton ?_
  intro b
  rcases b with ⟨z, w⟩
  have hsingleton :
      ({((z, w) : LatticePoint 1 × LatticePoint 1)} : Set (LatticePoint 1 × LatticePoint 1)) =
        ({z} : Set (LatticePoint 1)) ×ˢ ({w} : Set (LatticePoint 1)) := by
    ext s
    simp
  have hxy' : oneDimPoint x ≠ oneDimPoint y := by
    intro h
    apply hxy
    simpa using congrArg (fun u : LatticePoint 1 ↦ u 0) h
  -- Proof comment: compare the two rows on singleton rectangles and unfold the off-diagonal
  -- branch of `independentCoalescentMatrix`.
  rw [discreteMatrixKernel_apply_singleton, hsingleton]
  rw [Measure.prod_prod]
  rw [independentCoalescentMatrix_apply_of_ne
    (p := fun u v ↦
      dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1))) hxy']

/-- Helper for Theorem 18.8: subtracting the coordinates of the product row yields the free
one-dimensional cube-difference kernel at the current displacement. -/
private lemma productPairDifferenceRow_eq_uniformCubeOneDifferenceKernel
    (x y : ℤ) :
    Measure.map (fun s : LatticePoint 1 × LatticePoint 1 ↦ s.1 0 - s.2 0)
      ((dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure (oneDimPoint x)).prod
        (dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure (oneDimPoint y))) =
      uniformCubeOneDifferenceKernel (x - y) := by
  let μ : Measure ℤ := uniformCubeOneCoordinateMeasure
  let coord : LatticePoint 1 → ℤ := fun u ↦ u 0
  let diffLP : LatticePoint 1 × LatticePoint 1 → ℤ := fun s ↦ s.1 0 - s.2 0
  let diffInt : ℤ × ℤ → ℤ := fun s ↦ s.1 - s.2
  let rowx : Measure (LatticePoint 1) :=
    dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure (oneDimPoint x)
  let rowy : Measure (LatticePoint 1) :=
    dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure (oneDimPoint y)
  have hx :
      Measure.map coord rowx = Measure.map (fun z : ℤ ↦ x + z) μ := by
    simpa [coord, rowx, μ] using uniformCubeOneCoordinateRow_eq_shiftedIncrement x
  have hy :
      Measure.map coord rowy = Measure.map (fun z : ℤ ↦ y + z) μ := by
    simpa [coord, rowy, μ] using uniformCubeOneCoordinateRow_eq_shiftedIncrement y
  have hmap_prod :
      Measure.map (Prod.map coord coord) (rowx.prod rowy) =
        (Measure.map coord rowx).prod (Measure.map coord rowy) := by
    simpa [coord, rowx, rowy] using
      (Measure.map_prod_map rowx rowy (by fun_prop) (by fun_prop))
  have hcomp₁ :
      diffInt ∘ Prod.map (fun z : ℤ ↦ x + z) (fun z : ℤ ↦ y + z) =
        fun s : ℤ × ℤ ↦ (x - y) + (s.1 - s.2) := by
    funext s
    simp [diffInt, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hcomp₂ :
      (fun s : ℤ × ℤ ↦ (x - y) + (s.1 - s.2)) =
        (fun z : ℤ ↦ (x - y) + z) ∘ diffInt := by
    rfl
  -- Proof comment: first pass to integer coordinates on each factor, then translate the common
  -- difference law by the displacement `x - y`.
  change Measure.map diffLP (rowx.prod rowy) =
    Measure.map (fun z : ℤ ↦ (x - y) + z) uniformCubeOneDifferenceMeasure
  calc
    Measure.map diffLP (rowx.prod rowy)
        = Measure.map diffInt (Measure.map (Prod.map coord coord) (rowx.prod rowy)) := by
            rw [← Measure.map_map (μ := rowx.prod rowy)
              (f := Prod.map coord coord) (g := diffInt) (by fun_prop) (by fun_prop)]
            rfl
    _ = Measure.map diffInt ((Measure.map coord rowx).prod (Measure.map coord rowy)) := by
          rw [hmap_prod]
    _ =
        Measure.map diffInt ((Measure.map (fun z : ℤ ↦ x + z) μ).prod
          (Measure.map (fun z : ℤ ↦ y + z) μ)) := by
            rw [hx, hy]
    _ =
        Measure.map (fun s : ℤ × ℤ ↦ (x - y) + (s.1 - s.2)) (μ.prod μ) := by
          rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          simp [hcomp₁]
    _ =
        Measure.map (fun z : ℤ ↦ (x - y) + z)
          (Measure.map diffInt (μ.prod μ)) := by
            rw [hcomp₂]
            rw [← Measure.map_map (μ := μ.prod μ) (f := diffInt)
              (g := fun z : ℤ ↦ (x - y) + z) (by fun_prop) (by fun_prop)]
    _ = Measure.map (fun z : ℤ ↦ (x - y) + z) uniformCubeOneDifferenceMeasure := by
          rfl

/-- Helper for Theorem 18.8: subtracting the coordinates of one coalescent step gives the
absorbed one-dimensional cube-difference kernel. -/
private lemma uniformCubeOneDifferenceRow_eq_absorbedDifferenceKernel
    (x y : ℤ) :
    Measure.map (fun s : LatticePoint 1 × LatticePoint 1 ↦ s.1 0 - s.2 0)
      (discreteMatrixKernel
        (independentCoalescentMatrix
          (fun u v ↦
            dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1))))
        (oneDimPoint x, oneDimPoint y)) =
      discreteMatrixKernel
        (absorbAtZeroIntegerStepMatrix uniformCubeOneDifferenceStepMatrix) (x - y) := by
  by_cases hxy : x = y
  · subst hxy
    refine Measure.ext_of_singleton ?_
    intro w
    by_cases hw : w = 0
    · subst hw
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
      have hpreimage :
          (fun s : LatticePoint 1 × LatticePoint 1 ↦ s.1 0 - s.2 0) ⁻¹' ({0} : Set ℤ) =
            {s : LatticePoint 1 × LatticePoint 1 | s.1 = s.2} := by
        ext s
        simp [sub_eq_zero]
      rw [hpreimage]
      have hOff :
          discreteMatrixKernel
              (independentCoalescentMatrix
                (fun u v ↦
                  dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1))))
              (oneDimPoint x, oneDimPoint x)
              {s : LatticePoint 1 × LatticePoint 1 | s.1 ≠ s.2} = 0 := by
        let q : LatticePoint 1 → LatticePoint 1 → ENNReal :=
          fun u v ↦ dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1))
        have hq : IsStochasticMatrix q := by
          simpa [q] using ownerStepMatrix_isStochastic (ν := uniformCubeStepPMF 1)
        simpa [q] using coalescentDiagonal_offDiagonalMass_eq_zero (p := q) hq (oneDimPoint x)
      have hDiag :
          discreteMatrixKernel
              (independentCoalescentMatrix
                (fun u v ↦
                  dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1))))
              (oneDimPoint x, oneDimPoint x)
              {s : LatticePoint 1 × LatticePoint 1 | s.1 = s.2} = 1 := by
        let q : LatticePoint 1 → LatticePoint 1 → ENNReal :=
          fun u v ↦ dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1))
        have hq : IsStochasticMatrix q := by
          simpa [q] using ownerStepMatrix_isStochastic (ν := uniformCubeStepPMF 1)
        have hstochastic :
            IsStochasticMatrix (independentCoalescentMatrix q) := by
          exact independentCoalescentMatrix_isStochasticMatrix (p := q) hq
        have hcompl_zero :
            discreteMatrixKernel (independentCoalescentMatrix q) (oneDimPoint x, oneDimPoint x)
                ({s : LatticePoint 1 × LatticePoint 1 | s.1 = s.2}ᶜ) = 0 := by
          simpa [Set.compl_setOf, not_not] using hOff
        calc
          discreteMatrixKernel (independentCoalescentMatrix q) (oneDimPoint x, oneDimPoint x)
              {s : LatticePoint 1 × LatticePoint 1 | s.1 = s.2}
              =
            discreteMatrixKernel (independentCoalescentMatrix q) (oneDimPoint x, oneDimPoint x)
              Set.univ := by
                exact measure_of_measure_compl_eq_zero
                  (μ := discreteMatrixKernel (independentCoalescentMatrix q)
                    (oneDimPoint x, oneDimPoint x)) hcompl_zero
          _ = 1 := by
                simpa [discreteMatrixKernel_univ] using hstochastic (oneDimPoint x, oneDimPoint x)
      calc
        discreteMatrixKernel
            (independentCoalescentMatrix
              (fun u v ↦
                dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1))))
            (oneDimPoint x, oneDimPoint x)
            {s : LatticePoint 1 × LatticePoint 1 | s.1 = s.2} = 1 := hDiag
        _ = discreteMatrixKernel
              (absorbAtZeroIntegerStepMatrix uniformCubeOneDifferenceStepMatrix) 0
                ({0} : Set ℤ) := by
              rw [discreteMatrixKernel_apply_singleton, absorbAtZeroIntegerStepMatrix_apply_zero]
              simp
        _ = discreteMatrixKernel
              (absorbAtZeroIntegerStepMatrix uniformCubeOneDifferenceStepMatrix) (x - x)
                ({0} : Set ℤ) := by
              simp
    · have hsubset :
          (fun s : LatticePoint 1 × LatticePoint 1 ↦ s.1 0 - s.2 0) ⁻¹' ({w} : Set ℤ) ⊆
            {s : LatticePoint 1 × LatticePoint 1 | s.1 ≠ s.2} := by
        intro s hs
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hs
        intro hEq
        apply hw
        have : s.1 0 = s.2 0 := congrArg (fun u : LatticePoint 1 ↦ u 0) hEq
        omega
      have hOff :
          discreteMatrixKernel
              (independentCoalescentMatrix
                (fun u v ↦
                  dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1))))
              (oneDimPoint x, oneDimPoint x)
              {s : LatticePoint 1 × LatticePoint 1 | s.1 ≠ s.2} = 0 := by
        let q : LatticePoint 1 → LatticePoint 1 → ENNReal :=
          fun u v ↦ dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1))
        have hq : IsStochasticMatrix q := by
          simpa [q] using ownerStepMatrix_isStochastic (ν := uniformCubeStepPMF 1)
        simpa [q] using coalescentDiagonal_offDiagonalMass_eq_zero (p := q) hq (oneDimPoint x)
      have hright :
          discreteMatrixKernel
              (absorbAtZeroIntegerStepMatrix uniformCubeOneDifferenceStepMatrix) (x - x)
              ({w} : Set ℤ) = 0 := by
        simpa [sub_self, hw] using
          (show
            discreteMatrixKernel
                (absorbAtZeroIntegerStepMatrix uniformCubeOneDifferenceStepMatrix) 0
                ({w} : Set ℤ) = 0 by
              rw [discreteMatrixKernel_apply_singleton, absorbAtZeroIntegerStepMatrix_apply_zero]
              simp [hw])
      have hleft :
          Measure.map (fun s : LatticePoint 1 × LatticePoint 1 ↦ s.1 0 - s.2 0)
              (discreteMatrixKernel
                (independentCoalescentMatrix
                  (fun u v ↦
                    dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1))))
                (oneDimPoint x, oneDimPoint x))
              ({w} : Set ℤ) = 0 := by
        refine le_antisymm ?_ bot_le
        calc
          Measure.map (fun s : LatticePoint 1 × LatticePoint 1 ↦ s.1 0 - s.2 0)
              (discreteMatrixKernel
                (independentCoalescentMatrix
                  (fun u v ↦
                    dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1))))
                (oneDimPoint x, oneDimPoint x))
              ({w} : Set ℤ)
              =
            discreteMatrixKernel
              (independentCoalescentMatrix
                (fun u v ↦
                  dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1))))
              (oneDimPoint x, oneDimPoint x)
              ((fun s : LatticePoint 1 × LatticePoint 1 ↦ s.1 0 - s.2 0) ⁻¹' ({w} : Set ℤ)) := by
                rw [Measure.map_apply (by fun_prop) (measurableSet_singleton w)]
          _ ≤ discreteMatrixKernel
                (independentCoalescentMatrix
                  (fun u v ↦
                    dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1))))
                (oneDimPoint x, oneDimPoint x)
                {s : LatticePoint 1 × LatticePoint 1 | s.1 ≠ s.2} := by
                  exact measure_mono hsubset
          _ = 0 := hOff
      rw [hleft, hright]
  · -- Proof comment: off the diagonal, the coalescent row factorizes, and subtracting the two
    -- coordinates recovers the free difference kernel, which matches the absorbed kernel away
    -- from zero.
    rw [uniformCubeOneCoalescentRow_eq_prod_of_ne hxy,
      productPairDifferenceRow_eq_uniformCubeOneDifferenceKernel]
    have hdiff : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hrow :
        discreteMatrixKernel
            (absorbAtZeroIntegerStepMatrix uniformCubeOneDifferenceStepMatrix) (x - y) =
          uniformCubeOneDifferenceKernel (x - y) := by
      refine Measure.ext_of_singleton ?_
      intro w
      rw [discreteMatrixKernel_apply_singleton]
      rw [absorbAtZeroIntegerStepMatrix_apply_of_ne
        (q := uniformCubeOneDifferenceStepMatrix) hdiff]
    exact hrow.symm

/-- Helper for Theorem 18.8: pushing the one-dimensional cube coalescent `n`-step law through
the coordinate-difference map gives the absorbed difference `n`-step law at displacement
`x - y`. -/
private lemma uniformCubeOneCoalescentDifferencePow_eq_absorbedDifferencePow
    (n : ℕ) (x y : ℤ) :
    Measure.map (fun s : LatticePoint 1 × LatticePoint 1 ↦ s.1 0 - s.2 0)
      ((discreteMatrixKernel
        (independentCoalescentMatrix
          (fun u v ↦
            dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1)))) ^ n)
        (oneDimPoint x, oneDimPoint y)) =
      (discreteMatrixKernel
        (absorbAtZeroIntegerStepMatrix uniformCubeOneDifferenceStepMatrix) ^ n) (x - y) := by
  let κPair : Kernel (LatticePoint 1 × LatticePoint 1) (LatticePoint 1 × LatticePoint 1) :=
    discreteMatrixKernel
      (independentCoalescentMatrix
        (fun u v ↦
          dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1)))
  let κAbs : Kernel ℤ ℤ :=
    discreteMatrixKernel (absorbAtZeroIntegerStepMatrix uniformCubeOneDifferenceStepMatrix)
  let diff : LatticePoint 1 × LatticePoint 1 → ℤ := fun s ↦ s.1 0 - s.2 0
  have hdiff_meas : Measurable diff := Measurable.of_discrete
  induction n with
  | zero =>
      refine Measure.ext_of_singleton ?_
      intro w
      rw [Measure.map_apply hdiff_meas (measurableSet_singleton w)]
      simp only [pow_zero]
      change Measure.dirac (oneDimPoint x, oneDimPoint y) (diff ⁻¹' ({w} : Set ℤ)) =
        Measure.dirac (x - y) ({w} : Set ℤ)
      by_cases h : x - y = w
      · simp [Measure.dirac_apply', diff, h, oneDimPoint_apply_zero]
      · simp [Measure.dirac_apply', diff, h, oneDimPoint_apply_zero]
  | succ n ih =>
      refine Measure.ext_of_singleton ?_
      intro w
      have hpreimage_meas :
          MeasurableSet (diff ⁻¹' ({w} : Set ℤ)) :=
        hdiff_meas (measurableSet_singleton w)
      calc
        Measure.map diff ((κPair ^ (n + 1)) (oneDimPoint x, oneDimPoint y)) ({w} : Set ℤ) =
            ((κPair ^ (n + 1)) (oneDimPoint x, oneDimPoint y)) (diff ⁻¹' ({w} : Set ℤ)) := by
              rw [Measure.map_apply hdiff_meas (measurableSet_singleton w)]
        _ =
            ∫⁻ s : LatticePoint 1 × LatticePoint 1,
              (κPair s) (diff ⁻¹' ({w} : Set ℤ))
                ∂((κPair ^ n) (oneDimPoint x, oneDimPoint y)) := by
              rw [Kernel.pow_succ_apply_eq_lintegral κPair n (oneDimPoint x, oneDimPoint y)
                hpreimage_meas]
        _ =
            ∫⁻ s : LatticePoint 1 × LatticePoint 1,
              Measure.map diff (κPair s) ({w} : Set ℤ)
                ∂((κPair ^ n) (oneDimPoint x, oneDimPoint y)) := by
              refine lintegral_congr_ae <| Filter.Eventually.of_forall ?_
              intro s
              symm
              exact Measure.map_apply hdiff_meas (measurableSet_singleton w)
        _ =
            ∫⁻ s : LatticePoint 1 × LatticePoint 1,
              κAbs (diff s) ({w} : Set ℤ)
                ∂((κPair ^ n) (oneDimPoint x, oneDimPoint y)) := by
              refine lintegral_congr_ae <| Filter.Eventually.of_forall ?_
              intro s
              rcases s with ⟨u, v⟩
              have hrow :
                  Measure.map diff (κPair (u, v)) = κAbs (u 0 - v 0) := by
                simpa [κPair, κAbs, diff] using
                  uniformCubeOneDifferenceRow_eq_absorbedDifferenceKernel (u 0) (v 0)
              exact congrArg (fun μ : Measure ℤ ↦ μ ({w} : Set ℤ)) hrow
        _ =
            ∫⁻ z : ℤ, κAbs z ({w} : Set ℤ)
              ∂Measure.map diff ((κPair ^ n) (oneDimPoint x, oneDimPoint y)) := by
              symm
              exact
                MeasureTheory.lintegral_map'
                  (μ := ((κPair ^ n) (oneDimPoint x, oneDimPoint y)))
                  (f := fun z : ℤ ↦ κAbs z ({w} : Set ℤ))
                  (g := diff)
                  (Kernel.measurable_coe κAbs (measurableSet_singleton w)).aemeasurable
                  hdiff_meas.aemeasurable
        _ =
            ∫⁻ z : ℤ, κAbs z ({w} : Set ℤ) ∂((κAbs ^ n) (x - y)) := by
              rw [ih]
        _ = (κAbs ^ (n + 1)) (x - y) ({w} : Set ℤ) := by
              rw [Kernel.pow_succ_apply_eq_lintegral κAbs n (x - y)
                (measurableSet_singleton w)]

/-- Helper for Theorem 18.8: the current disagreement probability of a one-dimensional cube
coalescent realization equals the nonzero mass of the absorbed difference kernel at the current
displacement. -/
private lemma uniformCubeOneCurrentDisagreement_eq_absorbedDifferenceNonzeroMass
    {Ω : Type*} [MeasurableSpace Ω]
    {P : LatticePoint 1 × LatticePoint 1 → ProbabilityMeasure Ω}
    {Z : ℕ → Ω → LatticePoint 1 × LatticePoint 1}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (independentCoalescentMatrix
            (fun u v ↦
              dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1)))) ^ n)
      P Z]
    (n : ℕ) (x y : ℤ) :
    (P (oneDimPoint x, oneDimPoint y) : Measure Ω) {ω | (Z n ω).1 ≠ (Z n ω).2} =
      ((discreteMatrixKernel
          (absorbAtZeroIntegerStepMatrix uniformCubeOneDifferenceStepMatrix) ^ n) (x - y))
        {w : ℤ | w ≠ 0} := by
  let diff : LatticePoint 1 × LatticePoint 1 → ℤ := fun s ↦ s.1 0 - s.2 0
  have hdiff_meas : Measurable diff := Measurable.of_discrete
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel
            (independentCoalescentMatrix
              (fun u v ↦
                dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1)))) ^ n)
        P Z := inferInstance
  have hdiff_process_meas : Measurable (fun ω ↦ (Z n ω).1 0 - (Z n ω).2 0) :=
    hdiff_meas.comp (hReal.measurable_process n)
  -- Proof comment: rewrite disagreement as nonvanishing of the coordinate difference and then
  -- push the time-`n` coalescent law through the transport theorem above.
  have hEvent :
      {ω | (Z n ω).1 ≠ (Z n ω).2} = {ω | (Z n ω).1 0 - (Z n ω).2 0 ≠ 0} := by
    ext ω
    constructor
    · intro hω hzero
      apply hω
      ext i
      fin_cases i
      exact sub_eq_zero.mp hzero
    · intro hω hEq
      apply hω
      have : (Z n ω).1 0 = (Z n ω).2 0 := congrArg (fun u : LatticePoint 1 ↦ u 0) hEq
      exact sub_eq_zero.mpr this
  rw [hEvent]
  have hpreimage :
      {ω | (Z n ω).1 0 - (Z n ω).2 0 ≠ 0} =
        (fun ω ↦ (Z n ω).1 0 - (Z n ω).2 0) ⁻¹' ({w : ℤ | w ≠ 0}) := by
    ext ω
    simp
  rw [hpreimage, ← Measure.map_apply hdiff_process_meas
    (show MeasurableSet {w : ℤ | w ≠ 0} from MeasurableSet.of_discrete)]
  have hmap :
      Measure.map (fun ω ↦ (Z n ω).1 0 - (Z n ω).2 0)
          (P (oneDimPoint x, oneDimPoint y) : Measure Ω) =
        Measure.map diff
          ((discreteMatrixKernel
            (independentCoalescentMatrix
              (fun u v ↦
                dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1)))) ^ n)
            (oneDimPoint x, oneDimPoint y)) := by
    calc
      Measure.map (fun ω ↦ (Z n ω).1 0 - (Z n ω).2 0)
          (P (oneDimPoint x, oneDimPoint y) : Measure Ω) =
        Measure.map diff (Measure.map (Z n) (P (oneDimPoint x, oneDimPoint y) : Measure Ω)) := by
          symm
          simpa [diff, Function.comp] using
            (Measure.map_map (μ := (P (oneDimPoint x, oneDimPoint y) : Measure Ω))
              (f := Z n) (g := diff)
              (hf := hReal.measurable_process n) (hg := hdiff_meas))
      _ =
          Measure.map diff
            ((discreteMatrixKernel
              (independentCoalescentMatrix
                (fun u v ↦
                  dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1)))) ^ n)
              (oneDimPoint x, oneDimPoint y)) := by
                rw [hReal.transition_eq (oneDimPoint x, oneDimPoint y) n]
  rw [hmap]
  simpa using
    congrArg (fun μ : Measure ℤ ↦ μ ({w : ℤ | w ≠ 0}))
      (uniformCubeOneCoalescentDifferencePow_eq_absorbedDifferencePow n x y)

/-- Helper for Theorem 18.8: the discrete kernel built from
`uniformCubeOneDifferenceStepMatrix` is the owner convolution kernel of
`uniformCubeOneDifferenceMeasure`. -/
private lemma uniformCubeOneDifferenceStepMatrix_kernel_eq_diracConvolutionKernel :
    discreteMatrixKernel uniformCubeOneDifferenceStepMatrix =
      dirac_convolution_kernel uniformCubeOneDifferenceMeasure := by
  -- Proof comment: on the discrete state space `ℤ`, equality of kernels is determined by
  -- singleton masses, and `uniformCubeOneDifferenceStepMatrix` was defined from exactly those
  -- masses.
  ext x s hs
  have hrow :
      discreteMatrixKernel uniformCubeOneDifferenceStepMatrix x =
        dirac_convolution_kernel uniformCubeOneDifferenceMeasure x := by
    refine Measure.ext_of_singleton ?_
    intro y
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
    rw [tsum_eq_single y]
    · simp [uniformCubeOneDifferenceStepMatrix]
    · intro z hz
      simp [Measure.smul_apply, Measure.dirac_apply', hz]
  exact congrArg (fun μ ↦ μ s) hrow

/-- Helper for Theorem 18.8: the free one-dimensional cube-difference kernel is stochastic. -/
private lemma uniformCubeOneDifferenceStepMatrix_isStochastic :
    IsStochasticMatrix uniformCubeOneDifferenceStepMatrix := by
  intro x
  -- Proof comment: each row sum is the total mass of the corresponding convolution-kernel row.
  calc
    ∑' y : ℤ, uniformCubeOneDifferenceStepMatrix x y =
        discreteMatrixKernel uniformCubeOneDifferenceStepMatrix x Set.univ := by
          rw [← discreteMatrixKernel_univ uniformCubeOneDifferenceStepMatrix x]
    _ = dirac_convolution_kernel uniformCubeOneDifferenceMeasure x Set.univ := by
      rw [uniformCubeOneDifferenceStepMatrix_kernel_eq_diracConvolutionKernel]
    _ = 1 := by
      simp

/-- Helper for Theorem 18.8: the free one-dimensional cube-difference kernel is translation
invariant. -/
private lemma uniformCubeOneDifferenceStepMatrix_isTranslationInvariant :
    IsTranslationInvariantStepMatrix uniformCubeOneDifferenceStepMatrix := by
  intro x y
  -- Proof comment: the convolution-kernel row depends only on the increment `y - x`.
  change dirac_convolution_kernel uniformCubeOneDifferenceMeasure x ({y} : Set ℤ) =
    dirac_convolution_kernel uniformCubeOneDifferenceMeasure 0 ({y - x} : Set ℤ)
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
  have hpreimage : (fun z : ℤ ↦ x + z) ⁻¹' ({y} : Set ℤ) = {y - x} := by
    ext z
    simp
    omega
  rw [hpreimage]
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (y - x))]
  simp

/-- Helper for Theorem 18.8: every realization of the one-dimensional independent-coalescent
chain for the cube owner kernel has vanishing tail disagreement. -/
private lemma uniformCubeOneIndependentCoalescent_tailDisagreement_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω]
    {P : LatticePoint 1 × LatticePoint 1 → ProbabilityMeasure Ω}
    {Z : ℕ → Ω → LatticePoint 1 × LatticePoint 1}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (independentCoalescentMatrix
            (fun u v ↦
              dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1)))) ^ n)
      P Z] :
    ∀ x y : ℤ,
      Tendsto
        (fun n ↦
          (P (oneDimPoint x, oneDimPoint y) : Measure Ω)
            (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}))
        atTop (nhds 0) := by
  -- Route correction: keep the transport boundary at the one-dimensional difference map and reuse
  -- the already-closed current-disagreement identity instead of reopening owner-level transports.
  let hrealization :
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel
            (independentCoalescentMatrix
              (fun u v ↦
                dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1)))) ^ n)
        P Z := inferInstance
  let κPair : Kernel (LatticePoint 1 × LatticePoint 1) (LatticePoint 1 × LatticePoint 1) :=
    discreteMatrixKernel
      (independentCoalescentMatrix
        (fun u v ↦
          dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1))))
  let κq : Kernel ℤ ℤ := discreteMatrixKernel uniformCubeOneDifferenceStepMatrix
  let κAbs : Kernel ℤ ℤ :=
    discreteMatrixKernel (absorbAtZeroIntegerStepMatrix uniformCubeOneDifferenceStepMatrix)
  let hκq_stochastic : IsStochasticMatrix uniformCubeOneDifferenceStepMatrix :=
    uniformCubeOneDifferenceStepMatrix_isStochastic
  letI : IsMarkovKernel κq :=
    discreteMatrixKernel_isMarkovKernel uniformCubeOneDifferenceStepMatrix hκq_stochastic
  have hκAbs_stochastic :
      IsStochasticMatrix (absorbAtZeroIntegerStepMatrix uniformCubeOneDifferenceStepMatrix) := by
    exact
      absorbAtZeroIntegerStepMatrix_isStochastic
        uniformCubeOneDifferenceStepMatrix uniformCubeOneDifferenceStepMatrix_isStochastic
  letI : IsMarkovKernel κAbs :=
    discreteMatrixKernel_isMarkovKernel
      (absorbAtZeroIntegerStepMatrix uniformCubeOneDifferenceStepMatrix) hκAbs_stochastic
  let _ : IsProbabilityMeasure (κq 0) := inferInstance
  obtain ⟨Ωi, hΩi, Qq, Zlift, hZ_meas, hZ_law, hZ_indep, hQ_prob⟩ :=
    ProbabilityTheory.exists_iid (ULift.{0} ℕ) (κq 0)
  let Qprob : ProbabilityMeasure Ωi := ⟨Qq, hQ_prob⟩
  let Zq : ℕ → Ωi → ℤ := fun n ω ↦ Zlift ⟨n⟩ ω
  have hZq_meas : ∀ n : ℕ, Measurable (Zq n) := by
    intro n
    simpa [Zq] using hZ_meas ⟨n⟩
  have hZq_law : ∀ n : ℕ, HasLaw (Zq n) (κq 0) (Qprob : Measure Ωi) := by
    intro n
    simpa [Zq, Qprob] using hZ_law ⟨n⟩
  have hZq_indep : iIndepFun Zq (Qprob : Measure Ωi) := by
    simpa [Zq, Qprob] using
      hZ_indep.precomp (g := fun n : ℕ ↦ (⟨n⟩ : ULift.{0} ℕ)) (by
        intro i j hij
        simpa using congrArg ULift.down hij)
  have hqreal :
      IsMarkovProcessRealization (fun n : ℕ ↦ κq ^ n)
        (productStartRandomWalkMeasure Qprob) (productStartRandomWalk Zq) := by
    exact
      productStartRandomWalk_isMarkovProcessRealization
        uniformCubeOneDifferenceStepMatrix hκq_stochastic
        uniformCubeOneDifferenceStepMatrix_isTranslationInvariant
        Qprob Zq hZq_meas hZq_indep <| by
          intro n
          simpa [κq] using hZq_law n
  letI :
      IsMarkovProcessRealization (fun n : ℕ ↦ κq ^ n)
        (productStartRandomWalkMeasure Qprob) (productStartRandomWalk Zq) := hqreal
  intro x y
  let offZero : Set ℤ := {w : ℤ | w ≠ 0}
  have hHit :
      ∀ z : ℤ,
        (F[productStartRandomWalkMeasure Qprob, productStartRandomWalk Zq]) z 0 = 1 :=
    uniformCubeOneDifferenceHitsZero_eq_one
      (Pq := productStartRandomWalkMeasure Qprob)
      (Xq := productStartRandomWalk Zq)
  have hcurrent_tendsto :
      Tendsto
        (fun n ↦ (P (oneDimPoint x, oneDimPoint y) : Measure Ω) {ω | (Z n ω).1 ≠ (Z n ω).2})
        atTop (nhds 0) := by
    have habsorbed_tendsto :
        Tendsto
          (fun n ↦ (κAbs ^ n) (x - y) offZero)
          atTop (nhds 0) := by
      have hfree_tendsto :
          Tendsto
            (fun n ↦
              (productStartRandomWalkMeasure Qprob (x - y) : Measure (ℤ × Ωi))
                {ω | ∀ m ≤ n, productStartRandomWalk Zq m ω ≠ 0})
            atTop (nhds 0) := by
        simpa using
          freeAvoidZeroProb_tendsto_zero_of_hitsZero_eq_one
            (Pq := productStartRandomWalkMeasure Qprob)
            (Xq := productStartRandomWalk Zq) hHit (x - y)
      have habsorbed_fun :
          (fun n ↦ (κAbs ^ n) (x - y) offZero) =
            (fun n ↦
              (productStartRandomWalkMeasure Qprob (x - y) : Measure (ℤ × Ωi))
                {ω | ∀ m ≤ n, productStartRandomWalk Zq m ω ≠ 0}) := by
        funext n
        symm
        simpa [κAbs, offZero] using
          absorbedDifferenceNonzeroMass_eq_freeAvoidZeroProb
            (q := uniformCubeOneDifferenceStepMatrix)
            (Pq := productStartRandomWalkMeasure Qprob)
            (Xq := productStartRandomWalk Zq) (x - y) n
      simpa [habsorbed_fun] using hfree_tendsto
    have hcurrent_fun :
        (fun n ↦ (P (oneDimPoint x, oneDimPoint y) : Measure Ω) {ω | (Z n ω).1 ≠ (Z n ω).2}) =
          (fun n ↦ (κAbs ^ n) (x - y) offZero) := by
      funext n
      simpa [κAbs, offZero] using
        uniformCubeOneCurrentDisagreement_eq_absorbedDifferenceNonzeroMass
          (P := P) (Z := Z) n x y
    -- Proof comment: current disagreement is exactly the absorbed difference nonzero mass, which
    -- is the bounded zero-avoidance probability for the recurrent free difference walk.
    simpa [hcurrent_fun] using habsorbed_tendsto
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hcurrent_tendsto (fun n ↦ zero_le _)
      (coalescentTailDisagreement_le_currentDisagreement
        (P := P) (Z := Z)
        (p := fun u v ↦
          dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure u ({v} : Set (LatticePoint 1)))
        (ownerStepMatrix_isStochastic (ν := uniformCubeStepPMF 1))
        (oneDimPoint x) (oneDimPoint y))

/-- Helper for Theorem 18.8: the one-dimensional cube owner kernel already admits a successful
coupling via its canonical independent-coalescent realization. -/
private theorem uniformCubeOwnerOne_hasSuccessfulCoupling :
    HasSuccessfulCoupling.{0, 0}
      (fun x y ↦
        dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure x
          ({y} : Set (LatticePoint 1))) := by
  let q : LatticePoint 1 → LatticePoint 1 → ENNReal :=
    fun x y ↦
      dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure x ({y} : Set (LatticePoint 1))
  have hq : IsStochasticMatrix q := by
    simpa [q] using ownerStepMatrix_isStochastic (ν := uniformCubeStepPMF 1)
  have hcoalescent :
      IsStochasticMatrix (independentCoalescentMatrix q) := by
    exact independentCoalescentMatrix_isStochasticMatrix (p := q) hq
  obtain ⟨P, hreal⟩ :=
    existsCanonicalDiscreteMatrixRealization
      (q := independentCoalescentMatrix q) (hq := hcoalescent)
  let Z : ℕ → (ℕ → (LatticePoint 1 × LatticePoint 1)) → LatticePoint 1 × LatticePoint 1 :=
    Function.eval
  refine ProbabilityTheory.HasSuccessfulCoupling.mk.{0, 0} ?_
  refine ⟨ℕ → (LatticePoint 1 × LatticePoint 1), inferInstance, P, Z, ?_⟩
  refine
    { toIsMarkovCoupling := ?_
      tail_disagreement_tendsto_zero := ?_ }
  · exact independentCoalescentChain_isMarkovCoupling_of_realization (p := q) hreal
  · exact uniformCubeOneIndependentCoalescent_tailDisagreement_tendsto_zero
      (P := P) (Z := Z)

/-- Helper for Theorem 18.8: for each fixed target increment, aperiodicity upgrades irreducibility
to eventual positivity of the origin row along all sufficiently large times. -/
lemma existsEventualPositiveOriginMass
    {d : ℕ} (ν : PMF (LatticePoint d))
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d)) (dirac_convolution_kernel ν.toMeasure)]
    (haperiodic : IsAperiodic (dirac_convolution_kernel ν.toMeasure))
    (z : LatticePoint d) :
    ∃ n0 : ℕ, ∀ n ≥ n0,
      0 <
        (dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint d)
          ({z} : Set (LatticePoint d)) := by
  let κ : Kernel (LatticePoint d) (LatticePoint d) := dirac_convolution_kernel ν.toMeasure
  letI : IsMarkovKernel κ := by
    simpa [κ] using diracConvolutionKernel_isMarkovOfPMF ν
  have hperiod0 : statePeriod κ (0 : LatticePoint d) = 1 := haperiodic 0
  rcases exists_eventual_period_residue (κ := κ) (0 : LatticePoint d) z with
    ⟨L, hLlt, ⟨n0, hn0⟩⟩
  have hLlt' : L < 1 := by
    simpa [hperiod0] using hLlt
  have hLzero : L = 0 := Nat.lt_one_iff.mp hLlt'
  refine ⟨n0, ?_⟩
  intro n hn
  have hmem :
      n * statePeriod κ (0 : LatticePoint d) + L ∈ positiveTransitionStepSet κ (0 : LatticePoint d) z :=
    hn0 n hn
  rw [hperiod0, hLzero, Nat.mul_one, Nat.add_zero, mem_positiveTransitionStepSet_iff] at hmem
  simpa [κ] using hmem

/-- Helper for Theorem 18.8: aperiodicity and irreducibility give one block length whose
`N`-step origin row assigns positive mass to every cube increment. -/
lemma existsPositiveCubeBlockTime
    {d : ℕ} (ν : PMF (LatticePoint d))
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d)) (dirac_convolution_kernel ν.toMeasure)]
    (haperiodic : IsAperiodic (dirac_convolution_kernel ν.toMeasure)) :
    ∃ N : ℕ, ∀ z ∈ uniformCubePoints d,
      0 <
        (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d)
          ({z} : Set (LatticePoint d)) := by
  classical
  let κ : Kernel (LatticePoint d) (LatticePoint d) := dirac_convolution_kernel ν.toMeasure
  let n0 : LatticePoint d → ℕ :=
    fun z ↦ if hz : z ∈ uniformCubePoints d then
      Classical.choose (existsEventualPositiveOriginMass (ν := ν) haperiodic z)
      else 0
  let N : ℕ := (uniformCubePoints d).sup n0
  refine ⟨N, ?_⟩
  intro z hz
  have hzle : n0 z ≤ N := Finset.le_sup hz
  have hchosen := Classical.choose_spec (existsEventualPositiveOriginMass (ν := ν) haperiodic z)
  have hchosen_le :
      Classical.choose (existsEventualPositiveOriginMass (ν := ν) haperiodic z) ≤ N := by
    simpa [n0, hz] using hzle
  simpa [N, n0, hz, κ] using hchosen N hchosen_le

/-- Helper for Theorem 18.8: the common block time from `existsPositiveCubeBlockTime` has a
uniform positive lower bound on all cube singleton masses. -/
lemma existsPositiveCubeBlockLowerBound
    {d : ℕ} (ν : PMF (LatticePoint d))
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d)) (dirac_convolution_kernel ν.toMeasure)]
    (haperiodic : IsAperiodic (dirac_convolution_kernel ν.toMeasure)) :
    ∃ N : ℕ, ∃ lam : ENNReal, 0 < lam ∧
      ∀ z ∈ uniformCubePoints d,
        lam ≤
          (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d)
            ({z} : Set (LatticePoint d)) := by
  classical
  let κ : Kernel (LatticePoint d) (LatticePoint d) := dirac_convolution_kernel ν.toMeasure
  obtain ⟨N, hN⟩ := existsPositiveCubeBlockTime (ν := ν) haperiodic
  let lam : ENNReal :=
    (uniformCubePoints d).inf' ⟨0, zero_mem_uniformCubePoints d⟩
      (fun z ↦ (κ ^ N) (0 : LatticePoint d) ({z} : Set (LatticePoint d)))
  refine ⟨N, lam, ?_, ?_⟩
  · -- Proof comment: the infimum over finitely many strictly positive cube masses is still
    -- strictly positive.
    have hlam :
        0 <
          (uniformCubePoints d).inf' ⟨0, zero_mem_uniformCubePoints d⟩
            (fun z ↦ (κ ^ N) (0 : LatticePoint d) ({z} : Set (LatticePoint d))) := by
      exact
        (Finset.lt_inf'_iff
          (s := uniformCubePoints d)
          (H := ⟨0, zero_mem_uniformCubePoints d⟩)
          (f := fun z ↦ (κ ^ N) (0 : LatticePoint d) ({z} : Set (LatticePoint d)))
          (a := 0)).2 fun z hz => by
            simpa [κ] using hN z hz
    simpa [lam] using hlam
  · intro z hz
    exact Finset.inf'_le _ hz

/-- Helper for Theorem 18.8: the cube cardinality is nonzero, so the coefficient
`(uniformCubePoints d).card * lam` is strictly positive whenever `lam` is. -/
lemma uniformCubeBlockCoefficient_pos {d : ℕ} {lam : ENNReal} (hlam_pos : 0 < lam) :
    0 < ((uniformCubePoints d).card : ENNReal) * lam := by
  -- Proof comment: the cube contains the origin, so its cardinality contributes a nonzero factor.
  have hcard_pos :
      0 < ((uniformCubePoints d).card : ENNReal) := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, zero_mem_uniformCubePoints d⟩
  exact ENNReal.mul_pos hcard_pos.ne' hlam_pos.ne'

/-- Helper for Theorem 18.8: the block-row cube coefficient is at most `1`, because the row is a
probability measure and dominates each cube singleton by at least `lam`. -/
lemma uniformCubeBlockCoefficient_le_one
    {d : ℕ} (ν : PMF (LatticePoint d)) {N : ℕ} {lam : ENNReal}
    (hcube : ∀ z ∈ uniformCubePoints d,
      lam ≤
        (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d)
          ({z} : Set (LatticePoint d))) :
    ((uniformCubePoints d).card : ENNReal) * lam ≤ 1 := by
  let κ : Kernel (LatticePoint d) (LatticePoint d) := dirac_convolution_kernel ν.toMeasure
  letI : IsMarkovKernel κ := by
    simpa [κ] using diracConvolutionKernel_isMarkovOfPMF ν
  let μ : Measure (LatticePoint d) := (κ ^ N) (0 : LatticePoint d)
  have hcard_mul :
      ((uniformCubePoints d).card : ENNReal) * lam =
        (uniformCubePoints d).sum (fun _ : LatticePoint d ↦ lam) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  calc
    ((uniformCubePoints d).card : ENNReal) * lam =
        (uniformCubePoints d).sum (fun _ : LatticePoint d ↦ lam) := hcard_mul
    _ ≤ (uniformCubePoints d).sum (fun z ↦ μ ({z} : Set (LatticePoint d))) := by
      refine Finset.sum_le_sum ?_
      intro z hz
      simpa [κ, μ] using hcube z hz
    _ = μ (uniformCubePoints d : Set (LatticePoint d)) := by
      simpa using (Measure.sum_measure_singleton (μ := μ) (s := uniformCubePoints d))
    _ ≤ μ Set.univ := by
      exact measure_mono (by intro z hz; simp)
    _ = 1 := by
      have hκpow : IsMarkovKernel (κ ^ N) := by
        simpa [κ] using diracConvolutionKernel_pow_isMarkovOfPMF (ν := ν) N
      have hμ_univ : ((κ ^ N) (0 : LatticePoint d)) Set.univ = 1 := by
        letI : IsProbabilityMeasure ((κ ^ N) (0 : LatticePoint d)) :=
          hκpow.isProbabilityMeasure (0 : LatticePoint d)
        exact measure_univ
      simpa [μ] using hμ_univ

/-- Helper for Theorem 18.8: the singleton lower bounds from `hcube` assemble to a measure
minorant by the uniform cube law with coefficient `#cube * lam`. -/
lemma uniformCubeBlockMinorant
    {d : ℕ} (ν : PMF (LatticePoint d)) {N : ℕ} {lam : ENNReal}
    (hcube : ∀ z ∈ uniformCubePoints d,
      lam ≤
        (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d)
          ({z} : Set (LatticePoint d))) :
    (((uniformCubePoints d).card : ENNReal) * lam) • (uniformCubeStepPMF d).toMeasure ≤
      (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d) := by
  let κ : Kernel (LatticePoint d) (LatticePoint d) := dirac_convolution_kernel ν.toMeasure
  let α : ENNReal := ((uniformCubePoints d).card : ENNReal) * lam
  let μ : Measure (LatticePoint d) := (κ ^ N) (0 : LatticePoint d)
  have hcard_ne_zero : ((uniformCubePoints d).card : ENNReal) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast Finset.card_pos.mpr ⟨0, zero_mem_uniformCubePoints d⟩)
  have hcard_ne_top : ((uniformCubePoints d).card : ENNReal) ≠ ∞ := by
    simp
  have hsingleton :
      ∀ z : LatticePoint d,
        α * uniformCubeStepPMF d z ≤ μ ({z} : Set (LatticePoint d)) := by
    intro z
    by_cases hz : z ∈ uniformCubePoints d
    · -- Proof comment: on cube points, the chosen coefficient cancels the uniform mass and
      -- recovers exactly the singleton lower bound `lam`.
      rw [uniformCubeStepPMF_apply_of_mem hz]
      have hα :
          α * ((uniformCubePoints d).card : ENNReal)⁻¹ = lam := by
        dsimp [α]
        calc
          ((uniformCubePoints d).card : ENNReal) * lam *
              ((uniformCubePoints d).card : ENNReal)⁻¹
              = lam * (((uniformCubePoints d).card : ENNReal) *
                ((uniformCubePoints d).card : ENNReal)⁻¹) := by
                  ac_rfl
          _ = lam * 1 := by rw [ENNReal.mul_inv_cancel hcard_ne_zero hcard_ne_top]
          _ = lam := by simp
      calc
        α * ((uniformCubePoints d).card : ENNReal)⁻¹ = lam := hα
        _ ≤ μ ({z} : Set (LatticePoint d)) := by
            simpa [κ, μ] using hcube z hz
    · -- Proof comment: outside the cube support, the minorant contributes no singleton mass.
      rw [uniformCubeStepPMF_apply_of_notMem hz]
      simp
  change ∀ s : Set (LatticePoint d),
    ((((uniformCubePoints d).card : ENNReal) * lam) • (uniformCubeStepPMF d).toMeasure) s ≤
      μ s
  intro s
  let g : LatticePoint d → ENNReal := fun z ↦ s.indicator (fun z ↦ μ ({z} : Set (LatticePoint d))) z
  rw [Measure.smul_apply, smul_eq_mul, PMF.toMeasure_apply_eq_tsum,
    ← ENNReal.tsum_mul_left]
  have htsum :
      ∑' z : LatticePoint d,
        ((uniformCubePoints d).card : ENNReal) * lam * s.indicator (uniformCubeStepPMF d) z ≤
          ∑' z : LatticePoint d, g z := by
    refine ENNReal.tsum_le_tsum ?_
    intro z
    by_cases hz : z ∈ s
    · -- Proof comment: on the target set, reduce to the singleton comparison already proved.
      simpa [hz, g, α, mul_assoc, mul_left_comm, mul_comm] using hsingleton z
    · -- Proof comment: off the target set, both indicator contributions vanish.
      simp [hz, g]
  have hg :
      (∑' z : LatticePoint d, g z) = μ s := by
    -- Proof comment: summing the singleton masses over `s` recovers the full measure `μ s`.
    simpa [g] using
      (Measure.tsum_indicator_apply_singleton (μ := μ) s MeasurableSet.of_discrete)
  exact htsum.trans_eq hg

/-- Helper for Theorem 18.8: a measure minorant between PMFs can be normalized into an exact
convex-combination decomposition of the larger PMF. -/
lemma pmfEq_convexCombo_ofMeasureMinorant
    {d : ℕ} (μ ν : PMF (LatticePoint d)) {α : ENNReal}
    (hα_le_one : α ≤ 1) (hminorant : α • μ.toMeasure ≤ ν.toMeasure) :
    ∃ ρ : PMF (LatticePoint d),
      ν.toMeasure = α • μ.toMeasure + (1 - α) • ρ.toMeasure := by
  by_cases hα_one : α = 1
  · have hμ_le_ν : μ.toMeasure ≤ ν.toMeasure := by
      -- Proof comment: when `α = 1`, the minorant is already the whole probability measure
      -- `μ.toMeasure`.
      simpa [hα_one] using hminorant
    have hμ_eq_ν : μ.toMeasure = ν.toMeasure :=
      Measure.eq_of_le_of_isProbabilityMeasure hμ_le_ν
    refine ⟨μ, ?_⟩
    -- Proof comment: in the degenerate branch, the residual coefficient vanishes and we can
    -- reuse `μ` as the formal remainder PMF.
    calc
      ν.toMeasure = μ.toMeasure := hμ_eq_ν.symm
      _ = α • μ.toMeasure + (1 - α) • μ.toMeasure := by
        simp [hα_one]
  · let ξ : Measure (LatticePoint d) := ν.toMeasure - α • μ.toMeasure
    letI : IsFiniteMeasure (α • μ.toMeasure) := by
      exact μ.toMeasure.smul_finite (ne_of_lt (lt_of_le_of_lt hα_le_one (by simp)))
    have hξ_add : ξ + α • μ.toMeasure = ν.toMeasure := by
      -- Proof comment: the remainder is the canonical measure subtraction of the minorant from
      -- `ν.toMeasure`.
      dsimp [ξ]
      simpa [add_comm] using
        (Measure.sub_add_cancel_of_le
          (μ := ν.toMeasure) (ν := α • μ.toMeasure) hminorant)
    have hα_lt_one : α < 1 := lt_of_le_of_ne hα_le_one hα_one
    have hξ_univ_eq : ξ Set.univ = 1 - α := by
      have huniv :
          ξ Set.univ + α = 1 := by
        -- Proof comment: evaluating the subtraction identity on `Set.univ` turns the remainder
        -- mass into the missing probability `1 - α`.
        have huniv' := congrArg (fun η : Measure (LatticePoint d) ↦ η Set.univ) hξ_add
        simpa [Measure.smul_apply, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
          mul_assoc] using huniv'
      exact ENNReal.eq_sub_of_add_eq' (by simp) (by simpa [add_comm] using huniv)
    have hξ_univ_pos : 0 < ξ Set.univ := by
      simpa [hξ_univ_eq] using (tsub_pos_iff_lt.mpr hα_lt_one)
    have hξ_ne_zero : ξ ≠ 0 := by
      -- Proof comment: a positive total mass rules out the zero remainder measure.
      exact (Measure.measure_univ_pos).mp hξ_univ_pos
    letI : NeZero ξ := ⟨hξ_ne_zero⟩
    let ρ : PMF (LatticePoint d) := (((ξ Set.univ)⁻¹ • ξ)).toPMF
    have hρ_toMeasure : ρ.toMeasure = (ξ Set.univ)⁻¹ • ξ := by
      -- Proof comment: after normalizing the residual measure, `toPMF` remembers the exact
      -- probability measure we started from.
      simpa [ρ] using
        (Measure.toPMF_toMeasure (μ := (ξ Set.univ)⁻¹ • ξ))
    have hξ_recover : (1 - α) • ρ.toMeasure = ξ := by
      -- Proof comment: rescaling the normalized residual PMF by its total mass recovers the
      -- original remainder measure.
      have hone : (1 - α) * (1 - α)⁻¹ = 1 := by
        exact ENNReal.mul_inv_cancel (by simpa [hξ_univ_eq] using hξ_univ_pos.ne') (by simp)
      rw [hρ_toMeasure, smul_smul, hξ_univ_eq, hone]
      simp
    refine ⟨ρ, ?_⟩
    -- Proof comment: substitute the recovered residual into the additive measure decomposition.
    calc
      ν.toMeasure = ξ + α • μ.toMeasure := hξ_add.symm
      _ = α • μ.toMeasure + ξ := by rw [add_comm]
      _ = α • μ.toMeasure + (1 - α) • ρ.toMeasure := by rw [hξ_recover]

/-- Helper for Theorem 18.8: on a subsingleton lattice, the diagonal process from a canonical
path-space realization is already a successful coupling for the owner kernel. -/
theorem subsingletonOwner_hasSuccessfulCoupling
    {d : ℕ} (ν : PMF (LatticePoint d)) [Subsingleton (LatticePoint d)] :
    HasSuccessfulCoupling.{0, 0}
      (fun x y ↦ dirac_convolution_kernel ν.toMeasure x ({y} : Set (LatticePoint d))) := by
  let Ω : Type := ℕ → LatticePoint d
  let q : LatticePoint d → LatticePoint d → ENNReal :=
    fun x y ↦ dirac_convolution_kernel ν.toMeasure x ({y} : Set (LatticePoint d))
  obtain ⟨Pbase, hbase⟩ :=
    existsCanonicalDiscreteMatrixRealization (q := q) (hq := ownerStepMatrix_isStochastic ν)
  let P : LatticePoint d × LatticePoint d → ProbabilityMeasure Ω :=
    fun a ↦ Pbase a.1
  let Z : ℕ → Ω → LatticePoint d × LatticePoint d :=
    fun n ω ↦ (ω n, ω n)
  refine ProbabilityTheory.HasSuccessfulCoupling.mk.{0, 0} ?_
  refine ⟨Ω, inferInstance, P, Z, ?_⟩
  refine
    { toIsMarkovCoupling := ?_
      tail_disagreement_tendsto_zero := ?_ }
  · refine
      { fst_realization := ?_
        snd_realization := ?_ }
    · intro y
      -- Proof comment: the first coordinate is exactly the canonical realization of the owner
      -- kernel started from the first component.
      simpa [P, Z, q] using hbase
    · intro x
      -- Proof comment: on a subsingleton space, the second coordinate starts from the same state
      -- as the first, so the same realization also controls the second marginal.
      have hP : (fun y : LatticePoint d ↦ P (x, y)) = Pbase := by
        funext y
        simpa [P] using (congrArg Pbase (Subsingleton.elim y x)).symm
      simpa [Z, q, hP] using hbase
  · intro x y
    -- Proof comment: the diagonal process never disagrees, so every tail disagreement event is
    -- empty and its probability is identically zero.
    simpa [P, Z] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ENNReal)) atTop (nhds 0))

/-- Helper for Theorem 18.8: the Bernoulli selector indicator on `Bool` has expectation
`p.toReal` after pushing the Bernoulli law forward to `ℝ`. -/
private theorem bernoulliIndicator_map_integral
    {p : NNReal} (hp_le_one : p ≤ 1) :
    ∫ x, x ∂Measure.map (fun b : Bool ↦ bif b then (1 : ℝ) else 0)
      ((PMF.bernoulli p hp_le_one).toMeasure) = p.toReal := by
  -- Proof comment: rewrite the pushed-forward integral back to the original Bernoulli law and
  -- then apply the explicit two-point expectation formula.
  calc
    ∫ x, x ∂Measure.map (fun b : Bool ↦ bif b then (1 : ℝ) else 0)
        ((PMF.bernoulli p hp_le_one).toMeasure)
      = ∫ b, (bif b then (1 : ℝ) else 0) ∂((PMF.bernoulli p hp_le_one).toMeasure) := by
          rw [integral_map]
          · exact (Measurable.of_discrete : Measurable fun b : Bool ↦ bif b then (1 : ℝ) else 0).aemeasurable
          · exact aestronglyMeasurable_id
    _ = p.toReal := by
          simpa using (PMF.bernoulli_expectation (p := p) hp_le_one)

/-- Helper for Theorem 18.8: for i.i.d. Bernoulli selectors with positive parameter, the lower
tail event that the first `n` selectors contain fewer than `K` successes has probability tending
to `0`. -/
private theorem bernoulliSelectorCount_lowerTail_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℕ → Ω → Bool} (hB_meas : ∀ n, Measurable (B n)) (hB_iid : IsIID B μ)
    {p : NNReal} (hp_pos : 0 < p) (hp_le_one : p ≤ 1)
    (hB_law : HasLaw (B 0) (PMF.bernoulli p hp_le_one).toMeasure μ) (K : ℕ) :
    Tendsto
      (fun n ↦
        μ ({ω | Finset.sum (Finset.range n) (fun i ↦ bif B i ω then (1 : ℝ) else 0) < (K : ℝ)}))
      atTop (nhds 0) := by
  let F : Bool → ℝ := fun b ↦ bif b then 1 else 0
  let Y : ℕ → Ω → ℝ := fun n ω ↦ F (B n ω)
  let lowerTail : ℕ → Set Ω :=
    fun n ↦ {ω | Finset.sum (Finset.range n) (fun i ↦ Y i ω) < (K : ℝ)}
  let futureLowerTail : ℕ → Set Ω := fun n ↦ ⋃ m ≥ n, lowerTail m
  have hF_meas : Measurable F := Measurable.of_discrete
  have hY_meas : ∀ n, Measurable (Y n) := by
    intro n
    exact hF_meas.comp (hB_meas n)
  have hY_iIndep : iIndepFun Y μ := by
    -- Proof comment: postcomposing the Boolean selectors with the `0/1` indicator preserves
    -- independence.
    simpa [Y, F] using hB_iid.iIndepFun.comp (fun _ ↦ F) (fun _ ↦ hF_meas)
  have hY_pairwise : Pairwise fun i j ↦ Y i ⟂ᵢ[μ] Y j := by
    -- Proof comment: pairwise independence is the two-coordinate shadow of the i.i.d. family.
    intro i j hij
    exact hY_iIndep.indepFun hij
  have hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ := by
    -- Proof comment: all real-valued indicator coordinates have the same law.
    intro n
    simpa [Y, F] using (hB_iid.identDistrib n 0).comp hF_meas
  have hF_law :
      HasLaw F (Measure.map F ((PMF.bernoulli p hp_le_one).toMeasure))
        ((PMF.bernoulli p hp_le_one).toMeasure) := by
    exact
      (show
          MeasurePreserving F ((PMF.bernoulli p hp_le_one).toMeasure)
            (Measure.map F ((PMF.bernoulli p hp_le_one).toMeasure)) from
          ⟨hF_meas, rfl⟩).hasLaw
  have hY0_ident :
      IdentDistrib (Y 0) F μ ((PMF.bernoulli p hp_le_one).toMeasure) := by
    -- Proof comment: the first transformed selector is distributed like the Bernoulli indicator
    -- under the reference Bernoulli law.
    simpa [Y] using (HasLaw.fun_comp hF_law hB_law).identDistrib hF_law
  have hY0_integrable : Integrable (Y 0) μ := by
    have hF_integrable : Integrable F ((PMF.bernoulli p hp_le_one).toMeasure) := by
      exact Integrable.of_finite
    exact hY0_ident.integrable_iff.2 hF_integrable
  have hY0_expectation : ∫ ω, Y 0 ω ∂μ = p.toReal := by
    -- Proof comment: evaluate the mean through the Bernoulli law of the first selector.
    calc
      ∫ ω, Y 0 ω ∂μ = ∫ b, F b ∂((PMF.bernoulli p hp_le_one).toMeasure) := by
          simpa [Y, F] using hB_law.integral_comp hF_meas.aestronglyMeasurable
      _ = ∫ x, x ∂Measure.map F ((PMF.bernoulli p hp_le_one).toMeasure) := by
          rw [integral_map]
          · exact hF_meas.aemeasurable
          · exact aestronglyMeasurable_id
      _ = p.toReal := by
          simpa [F] using bernoulliIndicator_map_integral (p := p) hp_le_one
  have hp_real_pos : 0 < p.toReal := by
    exact_mod_cast hp_pos
  have hhalf_pos : 0 < p.toReal / 2 := by
    linarith
  have hhalf_lt : p.toReal / 2 < p.toReal := by
    linarith
  have hStrongLaw :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ ↦ Finset.sum (Finset.range n) (fun i ↦ Y i ω) / (n : ℝ))
          atTop (nhds (p.toReal)) := by
    -- Proof comment: the strong law upgrades the Bernoulli selectors to an almost-sure linear
    -- success rate.
    filter_upwards [ProbabilityTheory.strong_law_ae_real Y hY0_integrable hY_pairwise hY_ident]
      with ω hω
    exact hY0_expectation ▸ (by simpa [Y] using hω)
  have hEventuallyNoLowerTail :
      ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ lowerTail n := by
    filter_upwards [hStrongLaw] with ω hω
    have hAvgLower :
        ∀ᶠ n : ℕ in atTop, p.toReal / 2 <
          Finset.sum (Finset.range n) (fun i ↦ Y i ω) / (n : ℝ) := by
      simpa using hω.eventually (Ioi_mem_nhds hhalf_lt)
    have hLinearLarge :
        ∀ᶠ n : ℕ in atTop, (K : ℝ) ≤ (p.toReal / 2) * (n : ℝ) := by
      obtain ⟨N, hN⟩ := exists_nat_gt ((K : ℝ) / (p.toReal / 2))
      refine Filter.eventually_atTop.mpr ?_
      refine ⟨N, fun n hn ↦ ?_⟩
      have hKn : (K : ℝ) / (p.toReal / 2) < (n : ℝ) := by
        exact lt_of_lt_of_le hN (by exact_mod_cast hn)
      exact le_of_lt <| by
        have hmul : (K : ℝ) < (n : ℝ) * (p.toReal / 2) := by
          exact (div_lt_iff₀ hhalf_pos).mp hKn
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    have hNatPos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
      refine Filter.eventually_atTop.mpr ?_
      refine ⟨1, fun n hn ↦ ?_⟩
      positivity
    -- Proof comment: for almost every sample point, the strong law gives a positive linear lower
    -- bound on the success count, so the fixed finite lower-tail event eventually disappears.
    filter_upwards [hAvgLower, hLinearLarge, hNatPos] with n hnAvg hnK hnPos
    have hCountLarge : (K : ℝ) ≤ Finset.sum (Finset.range n) (fun i ↦ Y i ω) := by
      have hScaled :
          (p.toReal / 2) * (n : ℝ) < Finset.sum (Finset.range n) (fun i ↦ Y i ω) := by
        have htmp : (p.toReal / 2) <
            Finset.sum (Finset.range n) (fun i ↦ Y i ω) / (n : ℝ) := hnAvg
        have hmul : (p.toReal / 2) * (n : ℝ) <
            Finset.sum (Finset.range n) (fun i ↦ Y i ω) := by
          exact (lt_div_iff₀ hnPos).mp htmp
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      exact hnK.trans hScaled.le
    simpa [lowerTail, not_lt] using hCountLarge
  have hLowerTail_meas : ∀ n, MeasurableSet (lowerTail n) := by
    intro n
    -- Proof comment: each lower-tail event is measurable because it depends on a finite real sum
    -- of measurable selector indicators.
    exact measurableSet_lt (by fun_prop) measurable_const
  have hFutureLowerTail_meas : ∀ n, MeasurableSet (futureLowerTail n) := by
    intro n
    refine MeasurableSet.iUnion fun m ↦ ?_
    refine MeasurableSet.iUnion fun _ ↦ ?_
    exact hLowerTail_meas m
  have hFutureLowerTail_anti : Antitone futureLowerTail := by
    intro n m hnm ω hω
    rcases Set.mem_iUnion.1 hω with ⟨k, hk⟩
    rcases Set.mem_iUnion.1 hk with ⟨hkm, hωk⟩
    exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨le_trans hnm hkm, hωk⟩⟩
  have hFutureLowerTail_zero : μ (⋂ n : ℕ, futureLowerTail n) = 0 := by
    have hCompl_ae : ∀ᵐ ω ∂μ, ω ∈ (⋂ n : ℕ, futureLowerTail n)ᶜ := by
      filter_upwards [hEventuallyNoLowerTail] with ω hω
      rcases Filter.eventually_atTop.1 hω with ⟨N, hN⟩
      simp only [Set.mem_compl_iff, Set.mem_iInter, not_forall]
      refine ⟨N, ?_⟩
      intro hωN
      rcases Set.mem_iUnion.1 hωN with ⟨m, hm⟩
      rcases Set.mem_iUnion.1 hm with ⟨hmN, hTailm⟩
      exact hN m hmN hTailm
    exact (compl_mem_ae_iff.1 hCompl_ae)
  have hFutureLowerTail_tendsto :
      Tendsto (fun n ↦ μ (futureLowerTail n)) atTop (nhds 0) := by
    -- Proof comment: the future lower-tail events decrease to a null limsup because almost every
    -- sample path eventually accumulates enough selector successes.
    simpa [hFutureLowerTail_zero] using
      (tendsto_measure_iInter_atTop
        (μ := μ) (s := futureLowerTail)
        (fun n ↦ (hFutureLowerTail_meas n).nullMeasurableSet)
        hFutureLowerTail_anti ⟨0, by
          simpa using (Set.toFinite {n : ℕ | n ≤ 0})⟩)
  have hLowerTail_le : ∀ n, μ (lowerTail n) ≤ μ (futureLowerTail n) := by
    intro n
    refine measure_mono ?_
    intro ω hω
    exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨le_rfl, hω⟩⟩
  -- Proof comment: the fixed-time lower-tail event is contained in the future lower-tail event,
  -- so its probability is squeezed to `0`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hFutureLowerTail_tendsto (fun n ↦ zero_le _) ?_
  intro n
  simpa [lowerTail, futureLowerTail] using hLowerTail_le n

/-- Helper for Theorem 18.8: a pair disagreement forces a disagreement in at least one
coordinate. -/
private lemma pairDisagreement_subset_union
    {Ω E₁ E₂ : Type*} (X₁ Y₁ : Ω → E₁) (X₂ Y₂ : Ω → E₂) :
    {ω | (X₁ ω, X₂ ω) ≠ (Y₁ ω, Y₂ ω)} ⊆
      {ω | X₁ ω ≠ Y₁ ω} ∪ {ω | X₂ ω ≠ Y₂ ω} := by
  intro ω hω
  by_cases h₁ : X₁ ω = Y₁ ω
  · -- Proof comment: if the first coordinates already agree, the pair disagreement must come
    -- from the second coordinate.
    right
    intro h₂
    exact hω (Prod.ext h₁ h₂)
  · -- Proof comment: otherwise we are already in the first-coordinate disagreement branch.
    exact Or.inl h₁

/-- Helper for Theorem 18.8: the tail disagreement of a product-valued coupling is bounded by the
sum of the two coordinate tail disagreements. -/
private lemma pairTailDisagreement_measure_le
    {Ω E₁ E₂ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X₁ Y₁ : ℕ → Ω → E₁) (X₂ Y₂ : ℕ → Ω → E₂) (n : ℕ) :
    μ (⋃ m ≥ n, {ω | (X₁ m ω, X₂ m ω) ≠ (Y₁ m ω, Y₂ m ω)})
      ≤ μ (⋃ m ≥ n, {ω | X₁ m ω ≠ Y₁ m ω}) +
          μ (⋃ m ≥ n, {ω | X₂ m ω ≠ Y₂ m ω}) := by
  have hsubset :
      (⋃ m ≥ n, {ω | (X₁ m ω, X₂ m ω) ≠ (Y₁ m ω, Y₂ m ω)}) ⊆
        (⋃ m ≥ n, {ω | X₁ m ω ≠ Y₁ m ω}) ∪
          ⋃ m ≥ n, {ω | X₂ m ω ≠ Y₂ m ω} := by
    intro ω hω
    rcases Set.mem_iUnion.1 hω with ⟨m, hm⟩
    rcases Set.mem_iUnion.1 hm with ⟨hmn, hpair⟩
    have hcoord :=
      pairDisagreement_subset_union
        (X₁ := fun ω ↦ X₁ m ω) (Y₁ := fun ω ↦ Y₁ m ω)
        (X₂ := fun ω ↦ X₂ m ω) (Y₂ := fun ω ↦ Y₂ m ω) hpair
    rcases hcoord with hcoord | hcoord
    · exact Or.inl <| Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨hmn, hcoord⟩⟩
    · exact Or.inr <| Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨hmn, hcoord⟩⟩
  -- Proof comment: once the product tail event is contained in the union of the two coordinate
  -- tail events, `measure_union_le` gives the desired estimate.
  exact le_trans (measure_mono hsubset) (measure_union_le _ _)

/-- Helper for Theorem 18.8: if both coordinate tail disagreements tend to zero, then the
product-state tail disagreement also tends to zero. -/
private lemma pairTailDisagreement_tendsto_zero
    {Ω E₁ E₂ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X₁ Y₁ : ℕ → Ω → E₁) (X₂ Y₂ : ℕ → Ω → E₂)
    (h₁ :
      Tendsto (fun n ↦ μ (⋃ m ≥ n, {ω | X₁ m ω ≠ Y₁ m ω})) atTop (nhds 0))
    (h₂ :
      Tendsto (fun n ↦ μ (⋃ m ≥ n, {ω | X₂ m ω ≠ Y₂ m ω})) atTop (nhds 0)) :
    Tendsto (fun n ↦ μ (⋃ m ≥ n, {ω | (X₁ m ω, X₂ m ω) ≠ (Y₁ m ω, Y₂ m ω)}))
      atTop (nhds 0) := by
  have hsum :
      Tendsto
        (fun n ↦
          μ (⋃ m ≥ n, {ω | X₁ m ω ≠ Y₁ m ω}) +
            μ (⋃ m ≥ n, {ω | X₂ m ω ≠ Y₂ m ω}))
        atTop (nhds (0 + 0)) := by
    exact h₁.add h₂
  -- Proof comment: squeeze the product tail between `0` and the coordinate-sum bound.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n ↦ zero_le _) ?_
  · simpa using hsum
  · intro n
    exact pairTailDisagreement_measure_le (μ := μ) (X₁ := X₁) (Y₁ := Y₁)
      (X₂ := X₂) (Y₂ := Y₂) n

/-- Helper for Theorem 18.8: the pointwise product of two stochastic matrices on countable
discrete spaces is again stochastic. -/
private lemma productStepMatrix_isStochastic
    {E₁ E₂ : Type*} [MeasurableSpace E₁] [DiscreteMeasurableSpace E₁] [Countable E₁]
    [MeasurableSpace E₂] [DiscreteMeasurableSpace E₂] [Countable E₂]
    {q₁ : E₁ → E₁ → ENNReal} {q₂ : E₂ → E₂ → ENNReal}
    (hq₁ : IsStochasticMatrix q₁) (hq₂ : IsStochasticMatrix q₂) :
    IsStochasticMatrix (fun x y : E₁ × E₂ ↦ q₁ x.1 y.1 * q₂ x.2 y.2) := by
  intro x
  -- Proof comment: the row sum factorizes as a product of the two coordinate row sums.
  calc
    ∑' y : E₁ × E₂, q₁ x.1 y.1 * q₂ x.2 y.2
        = ∑' y₁ : E₁, ∑' y₂ : E₂, q₁ x.1 y₁ * q₂ x.2 y₂ := by
            simpa using
              (ENNReal.tsum_prod' (f := fun y : E₁ × E₂ ↦ q₁ x.1 y.1 * q₂ x.2 y.2)).symm
    _ = ∑' y₁ : E₁, q₁ x.1 y₁ * ∑' y₂ : E₂, q₂ x.2 y₂ := by
          refine tsum_congr fun y₁ ↦ ?_
          rw [ENNReal.tsum_mul_left]
    _ = ∑' y₁ : E₁, q₁ x.1 y₁ * 1 := by
          simp [hq₂ x.2]
    _ = 1 := by
          simp [hq₁ x.1]

/-- Helper for Theorem 18.8: the discrete kernel attached to the pointwise product step matrix is
the parallel composition of the two discrete kernels. -/
private lemma discreteProductKernel_eq_parallelComp
    {E₁ E₂ : Type*} [MeasurableSpace E₁] [DiscreteMeasurableSpace E₁] [Countable E₁]
    [MeasurableSpace E₂] [DiscreteMeasurableSpace E₂] [Countable E₂]
    {q₁ : E₁ → E₁ → ENNReal} {q₂ : E₂ → E₂ → ENNReal} :
    discreteMatrixKernel (fun x y : E₁ × E₂ ↦ q₁ x.1 y.1 * q₂ x.2 y.2) =
      (discreteMatrixKernel q₁) ∥ₖ (discreteMatrixKernel q₂) := by
  -- Proof comment: on countable discrete spaces, kernel equality is determined by singleton
  -- masses, and the singleton rectangle formula for `∥ₖ` matches the product step matrix entry.
  ext x s hs
  have hrow :
      discreteMatrixKernel (fun a b : E₁ × E₂ ↦ q₁ a.1 b.1 * q₂ a.2 b.2) x =
        ((discreteMatrixKernel q₁) ∥ₖ (discreteMatrixKernel q₂)) x := by
    refine Measure.ext_of_singleton ?_
    intro y
    have hsingleton :
        ({y} : Set (E₁ × E₂)) = ({y.1} : Set E₁) ×ˢ ({y.2} : Set E₂) := by
      ext z
      simp
    -- Proof comment: after rewriting the singleton as a singleton rectangle, both sides reduce
    -- to the same product of the two coordinate singleton masses.
    rw [discreteMatrixKernel_apply_singleton, hsingleton, Kernel.parallelComp_apply_prod]
    rw [discreteMatrixKernel_apply_singleton, discreteMatrixKernel_apply_singleton]
  exact congrArg (fun μ ↦ μ s) hrow

/-- Helper for Theorem 18.8: independent products of discrete realizations realize the parallel
product kernel. -/
private theorem productKernelRealization_of_realizations
    {E₁ E₂ : Type*} [MeasurableSpace E₁] [DiscreteMeasurableSpace E₁] [Countable E₁]
    [MeasurableSpace E₂] [DiscreteMeasurableSpace E₂] [Countable E₂]
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : E₁ → ProbabilityMeasure Ω₁} {P₂ : E₂ → ProbabilityMeasure Ω₂}
    {X₁ : ℕ → Ω₁ → E₁} {X₂ : ℕ → Ω₂ → E₂}
    {q₁ : E₁ → E₁ → ENNReal} {q₂ : E₂ → E₂ → ENNReal}
    (h₁ : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel q₁ ^ n) P₁ X₁)
    (h₂ : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel q₂ ^ n) P₂ X₂) :
    IsMarkovProcessRealization
      (fun n : ℕ ↦ ((discreteMatrixKernel q₁) ∥ₖ (discreteMatrixKernel q₂)) ^ n)
      (fun x : E₁ × E₂ ↦ (P₁ x.1).prod (P₂ x.2))
      (fun n ω ↦ (X₁ n ω.1, X₂ n ω.2)) := by
  let κ₁ : Kernel E₁ E₁ := discreteMatrixKernel q₁
  let κ₂ : Kernel E₂ E₂ := discreteMatrixKernel q₂
  let κ : Kernel (E₁ × E₂) (E₁ × E₂) := κ₁ ∥ₖ κ₂
  let P : E₁ × E₂ → ProbabilityMeasure (Ω₁ × Ω₂) := fun x ↦ (P₁ x.1).prod (P₂ x.2)
  let X : ℕ → (Ω₁ × Ω₂) → E₁ × E₂ := fun n ω ↦ (X₁ n ω.1, X₂ n ω.2)
  let _ : IsMarkovKernel κ₁ := by
    simpa [κ₁] using h₁.semigroup.isMarkovKernel 1
  let _ : IsMarkovKernel κ₂ := by
    simpa [κ₂] using h₂.semigroup.isMarkovKernel 1
  let _ : IsMarkovKernel κ := by
    simpa [κ] using (inferInstance : IsMarkovKernel (κ₁ ∥ₖ κ₂))
  -- Proof comment: package the product process by the one-step kernel theorem, using the
  -- product-history split law obtained from the coordinate realizations.
  refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
    (κ₁ := κ)
    (P := P)
    (X := X)
    (hmeas := fun n ↦
      ((h₁.measurable_process n).comp measurable_fst).prodMk
        ((h₂.measurable_process n).comp measurable_snd))
    (hstart := ?_)
    (hstep := ?_)
  · intro x
    -- Proof comment: the product process starts from the product of the two deterministic Dirac
    -- measures, which is the Dirac mass at the product start state.
    calc
      (P x : Measure (Ω₁ × Ω₂)).map (X 0)
          = ((P₁ x.1 : Measure Ω₁).map (X₁ 0)).prod ((P₂ x.2 : Measure Ω₂).map (X₂ 0)) := by
              simpa [P, X] using
                (Measure.map_prod_map
                  (μa := (P₁ x.1 : Measure Ω₁))
                  (μc := (P₂ x.2 : Measure Ω₂))
                  (f := X₁ 0) (g := X₂ 0)
                  (h₁.measurable_process 0) (h₂.measurable_process 0)).symm
      _ = (Measure.dirac x.1).prod (Measure.dirac x.2) := by
            rw [h₁.initial_eq x.1, h₂.initial_eq x.2]
      _ = Measure.dirac x := by
            simpa using (Measure.dirac_prod_dirac (x := x.1) (y := x.2))
  · intro x A hA s
    let μ₁ : Measure Ω₁ := (P₁ x.1 : Measure Ω₁)
    let μ₂ : Measure Ω₂ := (P₂ x.2 : Measure Ω₂)
    let μ : Measure (Ω₁ × Ω₂) := (P x : Measure (Ω₁ × Ω₂))
    let H₁ : Ω₁ → Fin (s + 1) → E₁ := fun ω i ↦ X₁ i ω
    let H₂ : Ω₂ → Fin (s + 1) → E₂ := fun ω i ↦ X₂ i ω
    let H : (Ω₁ × Ω₂) → Fin (s + 1) → E₁ × E₂ := fun ω i ↦ (H₁ ω.1 i, H₂ ω.2 i)
    let split₁ : Ω₁ → (Fin (s + 1) → E₁) × E₁ := fun ω ↦ (H₁ ω, X₁ (s + 1) ω)
    let split₂ : Ω₂ → (Fin (s + 1) → E₂) × E₂ := fun ω ↦ (H₂ ω, X₂ (s + 1) ω)
    let next : (Ω₁ × Ω₂) → E₁ × E₂ := fun ω ↦ (X₁ (s + 1) ω.1, X₂ (s + 1) ω.2)
    let step₁ : Kernel (Fin (s + 1) → E₁) E₁ :=
      Kernel.comap κ₁ (fun z ↦ z (Fin.last s)) (by fun_prop)
    let step₂ : Kernel (Fin (s + 1) → E₂) E₂ :=
      Kernel.comap κ₂ (fun z ↦ z (Fin.last s)) (by fun_prop)
    let step : Kernel (Fin (s + 1) → E₁ × E₂) (E₁ × E₂) :=
      Kernel.comap κ (fun z ↦ z (Fin.last s)) (by fun_prop)
    have hμ : μ = μ₁.prod μ₂ := by
      rfl
    have hH_meas : Measurable H := by
      refine measurable_pi_lambda _ fun i ↦ ?_
      exact ((h₁.measurable_process i).comp measurable_fst).prodMk
        ((h₂.measurable_process i).comp measurable_snd)
    have hH₁_meas : Measurable H₁ := by
      exact measurable_historyTuple (X := X₁) (times := fun i : Fin (s + 1) ↦ i)
        h₁.measurable_process
    have hH₂_meas : Measurable H₂ := by
      exact measurable_historyTuple (X := X₂) (times := fun i : Fin (s + 1) ↦ i)
        h₂.measurable_process
    have hsplit₁_meas : Measurable split₁ := by
      exact hH₁_meas.prodMk (h₁.measurable_process (s + 1))
    have hsplit₂_meas : Measurable split₂ := by
      exact hH₂_meas.prodMk (h₂.measurable_process (s + 1))
    have hnext_meas : Measurable next := by
      exact ((h₁.measurable_process (s + 1)).comp measurable_fst).prodMk
        ((h₂.measurable_process (s + 1)).comp measurable_snd)
    have hfiltration :
        generatedFiltrationSpace X s = MeasurableSpace.comap H inferInstance := by
      let times : Fin (s + 1) → ℕ := fun i ↦ i
      have htimes : StrictMono times := fun _ _ hij ↦ hij
      have hleft :
          MeasurableSpace.comap H inferInstance ≤ generatedFiltrationSpace X s := by
        simpa [H, X, times] using
          (historyTuple_comap_le_generatedFiltrationSpace (X := X) (times := times) htimes)
      have hright :
          generatedFiltrationSpace X s ≤ MeasurableSpace.comap H inferInstance := by
        rw [generatedFiltrationSpace]
        refine iSup₂_le fun t ht ↦ ?_
        let i : Fin (s + 1) := ⟨t, Nat.lt_succ_of_le ht⟩
        have hCoord :
            Measurable[MeasurableSpace.comap H inferInstance] (fun ω ↦ H ω i) := by
          exact (measurable_pi_apply i).comp (comap_measurable H)
        simpa [H, X, i, H₁, H₂] using hCoord.comap_le
      exact le_antisymm hright hleft
    have hsplit₁ :
        μ₁.map split₁ = (μ₁.map H₁) ⊗ₘ step₁ := by
      let times : Fin (s + 2) → ℕ := fun i ↦ i
      have htimes : StrictMono times := fun _ _ hij ↦ hij
      -- Proof comment: the first coordinate split law is exactly the `m = s` instance of the
      -- standard tuple-successor factorization for Markov realizations.
      simpa [μ₁, H₁, split₁, step₁, κ₁, times] using
        (orderedTupleLawSucc_eq_compProd_kernelPow
          (κ₁ := κ₁) (P := P₁) (X := X₁) x.1 times htimes)
    have hsplit₂ :
        μ₂.map split₂ = (μ₂.map H₂) ⊗ₘ step₂ := by
      let times : Fin (s + 2) → ℕ := fun i ↦ i
      have htimes : StrictMono times := fun _ _ hij ↦ hij
      -- Proof comment: the second coordinate split law is the same factorization on the second
      -- witness space.
      simpa [μ₂, H₂, split₂, step₂, κ₂, times] using
        (orderedTupleLawSucc_eq_compProd_kernelPow
          (κ₁ := κ₂) (P := P₂) (X := X₂) x.2 times htimes)
    have hpair :
        μ.map (fun ω ↦ (H ω, next ω)) = (μ.map H) ⊗ₘ step := by
      let zipHistory : (Fin (s + 1) → E₁) × (Fin (s + 1) → E₂) → Fin (s + 1) → E₁ × E₂ :=
        fun h i ↦ (h.1 i, h.2 i)
      let zipSplit :
          ((Fin (s + 1) → E₁) × E₁) × ((Fin (s + 1) → E₂) × E₂) →
            (Fin (s + 1) → E₁ × E₂) × (E₁ × E₂) :=
        fun z ↦ (fun i ↦ (z.1.1 i, z.2.1 i), (z.1.2, z.2.2))
      have hzipHistory_meas : Measurable zipHistory := by
        fun_prop
      have hzipSplit_meas : Measurable zipSplit := by
        fun_prop
      have hmap_history :
          μ.map H = ((μ₁.map H₁).prod (μ₂.map H₂)).map zipHistory := by
        rw [hμ]
        calc
          (μ₁.prod μ₂).map H
              = ((μ₁.prod μ₂).map (Prod.map H₁ H₂)).map zipHistory := by
                  rw [← Measure.map_map (μ := μ₁.prod μ₂) (f := Prod.map H₁ H₂)
                    (g := zipHistory) (by fun_prop) hzipHistory_meas]
                  rfl
          _ = ((μ₁.map H₁).prod (μ₂.map H₂)).map zipHistory := by
                rw [Measure.map_prod_map _ _ hH₁_meas hH₂_meas]
      have hmap_split :
          μ.map (fun ω ↦ (H ω, next ω)) =
            ((μ₁.map split₁).prod (μ₂.map split₂)).map zipSplit := by
        rw [hμ]
        calc
          (μ₁.prod μ₂).map (fun ω ↦ (H ω, next ω))
              = ((μ₁.prod μ₂).map (Prod.map split₁ split₂)).map zipSplit := by
                  rw [← Measure.map_map (μ := μ₁.prod μ₂) (f := Prod.map split₁ split₂)
                    (g := zipSplit) (by fun_prop) hzipSplit_meas]
                  rfl
          _ = ((μ₁.map split₁).prod (μ₂.map split₂)).map zipSplit := by
                rw [Measure.map_prod_map _ _ hsplit₁_meas hsplit₂_meas]
      rw [hmap_split, hsplit₁, hsplit₂, hmap_history]
      -- Proof comment: after moving the pairing to the finite product side, every singleton
      -- preimage is a singleton rectangle, so `Measure.compProd_apply_prod` closes both sides.
      refine Measure.ext_of_singleton fun z ↦ ?_
      let h₁ : Fin (s + 1) → E₁ := fun i ↦ (z.1 i).1
      let h₂ : Fin (s + 1) → E₂ := fun i ↦ (z.1 i).2
      let y₁ : E₁ := z.2.1
      let y₂ : E₂ := z.2.2
      let z₁ : (Fin (s + 1) → E₁) × E₁ := (h₁, y₁)
      let z₂ : (Fin (s + 1) → E₂) × E₂ := (h₂, y₂)
      have hzipHistory_preimage :
          zipHistory ⁻¹' ({z.1} : Set (Fin (s + 1) → E₁ × E₂)) =
            ({h₁} : Set (Fin (s + 1) → E₁)) ×ˢ ({h₂} : Set (Fin (s + 1) → E₂)) := by
        ext h
        rcases h with ⟨h₁', h₂'⟩
        simp [zipHistory, h₁, h₂]
      have hzipSplit_preimage :
          zipSplit ⁻¹' ({z} : Set ((Fin (s + 1) → E₁ × E₂) × (E₁ × E₂))) =
            ({z₁} : Set ((Fin (s + 1) → E₁) × E₁)) ×ˢ
              ({z₂} : Set ((Fin (s + 1) → E₂) × E₂)) := by
        ext w
        rcases w with ⟨w₁, w₂⟩
        simp [zipSplit, z₁, z₂, h₁, h₂, y₁, y₂]
      have hsingleton_split₁ :
          ({z₁} : Set ((Fin (s + 1) → E₁) × E₁)) =
            ({h₁} : Set (Fin (s + 1) → E₁)) ×ˢ ({y₁} : Set E₁) := by
        ext w
        simp [z₁, h₁, y₁]
      have hsingleton_split₂ :
          ({z₂} : Set ((Fin (s + 1) → E₂) × E₂)) =
            ({h₂} : Set (Fin (s + 1) → E₂)) ×ˢ ({y₂} : Set E₂) := by
        ext w
        simp [z₂, h₂, y₂]
      have hsingleton_next :
          ({z.2} : Set (E₁ × E₂)) = ({y₁} : Set E₁) ×ˢ ({y₂} : Set E₂) := by
        ext w
        simp [y₁, y₂]
      have hstep_singleton :
          step z.1 ({z.2} : Set (E₁ × E₂)) = step₁ h₁ ({y₁} : Set E₁) * step₂ h₂ ({y₂} : Set E₂) := by
        rw [step, Kernel.comap_apply, hsingleton_next, Kernel.parallelComp_apply_prod]
        simp [h₁, h₂]
      have hhistory_singleton :
          (((μ₁.map H₁).prod (μ₂.map H₂)).map zipHistory)
            ({z.1} : Set (Fin (s + 1) → E₁ × E₂)) =
              μ₁.map H₁ ({h₁} : Set (Fin (s + 1) → E₁)) *
                μ₂.map H₂ ({h₂} : Set (Fin (s + 1) → E₂)) := by
        rw [Measure.map_apply hzipHistory_meas (measurableSet_singleton z.1), hzipHistory_preimage]
        rw [Measure.prod_apply ((measurableSet_singleton h₁).prod (measurableSet_singleton h₂))]
      calc
        (((μ₁.map H₁) ⊗ₘ step₁).prod ((μ₂.map H₂) ⊗ₘ step₂)).map zipSplit
            ({z} : Set ((Fin (s + 1) → E₁ × E₂) × (E₁ × E₂)))
            =
              (((μ₁.map H₁) ⊗ₘ step₁).prod ((μ₂.map H₂) ⊗ₘ step₂))
                (({z₁} : Set ((Fin (s + 1) → E₁) × E₁)) ×ˢ
                  ({z₂} : Set ((Fin (s + 1) → E₂) × E₂))) := by
                  rw [Measure.map_apply hzipSplit_meas (measurableSet_singleton z), hzipSplit_preimage]
        _ =
            (((μ₁.map H₁) ⊗ₘ step₁) ({z₁} : Set ((Fin (s + 1) → E₁) × E₁))) *
              (((μ₂.map H₂) ⊗ₘ step₂) ({z₂} : Set ((Fin (s + 1) → E₂) × E₂)) := by
                rw [Measure.prod_apply ((measurableSet_singleton z₁).prod (measurableSet_singleton z₂))]
        _ =
            ((μ₁.map H₁) ({h₁} : Set (Fin (s + 1) → E₁)) * step₁ h₁ ({y₁} : Set E₁)) *
              ((μ₂.map H₂) ({h₂} : Set (Fin (s + 1) → E₂)) * step₂ h₂ ({y₂} : Set E₂)) := by
                rw [hsingleton_split₁, hsingleton_split₂]
                rw [Measure.compProd_apply_prod (measurableSet_singleton h₁)
                  (measurableSet_singleton y₁)]
                rw [Measure.compProd_apply_prod (measurableSet_singleton h₂)
                  (measurableSet_singleton y₂)]
        _ =
            ((((μ₁.map H₁).prod (μ₂.map H₂)).map zipHistory)
              ({z.1} : Set (Fin (s + 1) → E₁ × E₂))) * step z.1 ({z.2} : Set (E₁ × E₂)) := by
                rw [hhistory_singleton, hstep_singleton]
                simp only [mul_assoc, mul_left_comm, mul_comm]
        _ =
            ((((μ₁.map H₁).prod (μ₂.map H₂)).map zipHistory) ⊗ₘ step)
              ({z} : Set ((Fin (s + 1) → E₁ × E₂) × (E₁ × E₂))) := by
                have hsingleton_pair :
                    ({z} : Set ((Fin (s + 1) → E₁ × E₂) × (E₁ × E₂)) =
                      ({z.1} : Set (Fin (s + 1) → E₁ × E₂)) ×ˢ ({z.2} : Set (E₁ × E₂)) := by
                  ext w
                  simp
                rw [hsingleton_pair]
                symm
                exact Measure.compProd_apply_prod
                  (measurableSet_singleton z.1) (measurableSet_singleton z.2)
    have hcond :
        condDistrib next H μ =ᵐ[μ.map H] step := by
      exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hH_meas hnext_meas hpair
    have hcondexp :
        μ⟦next ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ]
          fun ω ↦ (condDistrib next H μ (H ω)).real A := by
      simpa using
        (condDistrib_ae_eq_condExp (μ := μ) (X := H) (Y := next)
          hH_meas hnext_meas hA).symm
    have hkernel :
        (fun ω ↦ (step (H ω)).real A) =ᵐ[μ]
          fun ω ↦ (κ (X s ω)).real A := by
      exact Filter.Eventually.of_forall fun ω ↦ by
        simp [step, H, X]
    rw [hfiltration]
    exact hcondexp.trans <|
      (ae_eq_comp hH_meas.aemeasurable hcond).trans hkernel

/-- Helper for Theorem 18.8: successful couplings on two countable discrete state spaces can be
combined independently to a successful coupling for the pointwise product step matrix. -/
private theorem productStepMatrix_hasSuccessfulCoupling
    {E₁ E₂ : Type*} [MeasurableSpace E₁] [DiscreteMeasurableSpace E₁] [Countable E₁]
    [MeasurableSpace E₂] [DiscreteMeasurableSpace E₂] [Countable E₂]
    {q₁ : E₁ → E₁ → ENNReal} {q₂ : E₂ → E₂ → ENNReal}
    (hq₁ : HasSuccessfulCoupling q₁) (hq₂ : HasSuccessfulCoupling q₂) :
    HasSuccessfulCoupling (fun x y : E₁ × E₂ ↦ q₁ x.1 y.1 * q₂ x.2 y.2) := by
  -- Route correction: Step 1 no longer needs a fully generic product-kernel development; it only
  -- needs this witness-level successful-coupling constructor for the product step matrix.
  -- Proof comment: the intended witness space is the product of the two coupling spaces, with the
  -- product process formed coordinatewise and the tail estimate closed by
  -- `pairTailDisagreement_tendsto_zero`.
  rcases hq₁.exists_successfulCoupling with ⟨Ω₁, mΩ₁, P₁, Z₁, hsuccess₁⟩
  rcases hq₂.exists_successfulCoupling with ⟨Ω₂, mΩ₂, P₂, Z₂, hsuccess₂⟩
  let P : (E₁ × E₂) × (E₁ × E₂) → ProbabilityMeasure (Ω₁ × Ω₂) := fun a ↦
    (P₁ (a.1.1, a.2.1)).prod (P₂ (a.1.2, a.2.2))
  let Z : ℕ → (Ω₁ × Ω₂) → (E₁ × E₂) × (E₁ × E₂) := fun n ω ↦
    (((Z₁ n ω.1).1, (Z₂ n ω.2).1), ((Z₁ n ω.1).2, (Z₂ n ω.2).2))
  refine (ProbabilityTheory.HasSuccessfulCoupling.mk.{0, 0}
    (p := fun x y : E₁ × E₂ ↦ q₁ x.1 y.1 * q₂ x.2 y.2)) ?_
  refine ⟨Ω₁ × Ω₂, inferInstance, P, Z, ?_⟩
  refine
    { toIsMarkovCoupling := ?_
      tail_disagreement_tendsto_zero := ?_ }
  · refine
      { fst_realization := ?_
        snd_realization := ?_ }
    · intro y
      let hfst₁ := hsuccess₁.toIsMarkovCoupling.fst_realization y.1
      let hfst₂ := hsuccess₂.toIsMarkovCoupling.fst_realization y.2
      -- Proof comment: the first product coordinate is the independent product of the two
      -- first-coordinate realizations on the product witness space.
      simpa [P, Z, discreteProductKernel_eq_parallelComp] using
        productKernelRealization_of_realizations hfst₁ hfst₂
    · intro x
      let hsnd₁ := hsuccess₁.toIsMarkovCoupling.snd_realization x.1
      let hsnd₂ := hsuccess₂.toIsMarkovCoupling.snd_realization x.2
      -- Proof comment: the second product coordinate is the same independent-product
      -- construction applied to the two second-coordinate realizations.
      simpa [P, Z, discreteProductKernel_eq_parallelComp] using
        productKernelRealization_of_realizations hsnd₁ hsnd₂
  · intro x y
    let μ₁ : Measure Ω₁ := (P₁ (x.1, y.1) : Measure Ω₁)
    let μ₂ : Measure Ω₂ := (P₂ (x.2, y.2) : Measure Ω₂)
    let tail₁ : ℕ → Set Ω₁ := fun n ↦ ⋃ m ≥ n, {ω | (Z₁ m ω).1 ≠ (Z₁ m ω).2}
    let tail₂ : ℕ → Set Ω₂ := fun n ↦ ⋃ m ≥ n, {ω | (Z₂ m ω).1 ≠ (Z₂ m ω).2}
    let hreal₁ := hsuccess₁.toIsMarkovCoupling.fst_realization y.1
    let hsnd₁ := hsuccess₁.toIsMarkovCoupling.snd_realization x.1
    let hreal₂ := hsuccess₂.toIsMarkovCoupling.fst_realization y.2
    let hsnd₂ := hsuccess₂.toIsMarkovCoupling.snd_realization x.2
    have htail₁_meas : ∀ n : ℕ, MeasurableSet (tail₁ n) := by
      intro n
      refine MeasurableSet.iUnion ?_
      intro m
      refine MeasurableSet.iUnion ?_
      intro hnm
      simpa [tail₁] using
        ((hreal₁.measurable_process m).prodMk (hsnd₁.measurable_process m))
          (MeasurableSet.of_discrete : MeasurableSet {z : E₁ × E₁ | z.1 ≠ z.2})
    have htail₂_meas : ∀ n : ℕ, MeasurableSet (tail₂ n) := by
      intro n
      refine MeasurableSet.iUnion ?_
      intro m
      refine MeasurableSet.iUnion ?_
      intro hnm
      simpa [tail₂] using
        ((hreal₂.measurable_process m).prodMk (hsnd₂.measurable_process m))
          (MeasurableSet.of_discrete : MeasurableSet {z : E₂ × E₂ | z.1 ≠ z.2})
    have htail₁ :
        Tendsto
          (fun n ↦
            (P (x, y) : Measure (Ω₁ × Ω₂))
              (⋃ m ≥ n, {ω | (Z₁ m ω.1).1 ≠ (Z₁ m ω.1).2}))
          atTop (nhds 0) := by
      -- Proof comment: the first-coordinate tail event depends only on the first witness-space
      -- coordinate, so its product-space mass is the original tail mass for `hq₁`.
      have hmap :
          Measure.map Prod.fst (μ₁.prod μ₂) = μ₁ := by
        simpa using (Measure.map_fst_prod (μ := μ₁) (ν := μ₂))
      have hbase := hsuccess₁.tail_disagreement_tendsto_zero x.1 y.1
      refine hbase.congr' ?_
      refine Filter.Eventually.of_forall fun n ↦ ?_
      rw [← hmap]
      symm
      simpa [tail₁] using Measure.map_apply measurable_fst (htail₁_meas n)
    have htail₂ :
        Tendsto
          (fun n ↦
            (P (x, y) : Measure (Ω₁ × Ω₂))
              (⋃ m ≥ n, {ω | (Z₂ m ω.2).1 ≠ (Z₂ m ω.2).2}))
          atTop (nhds 0) := by
      -- Proof comment: the same marginal argument reduces the second-coordinate tail to the
      -- original successful coupling on `Ω₂`.
      have hmap :
          Measure.map Prod.snd (μ₁.prod μ₂) = μ₂ := by
        simpa using (Measure.map_snd_prod (μ := μ₁) (ν := μ₂))
      have hbase := hsuccess₂.tail_disagreement_tendsto_zero x.2 y.2
      refine hbase.congr' ?_
      refine Filter.Eventually.of_forall fun n ↦ ?_
      rw [← hmap]
      symm
      simpa [tail₂] using Measure.map_apply measurable_snd (htail₂_meas n)
    -- Proof comment: once both coordinate tail probabilities tend to zero, the pair tail tends
    -- to zero by the deterministic union bound for pair disagreement.
    simpa [P, Z] using
      (pairTailDisagreement_tendsto_zero
        (μ := (P (x, y) : Measure (Ω₁ × Ω₂)))
        (X₁ := fun n ω ↦ (Z₁ n ω.1).1) (Y₁ := fun n ω ↦ (Z₁ n ω.1).2)
        (X₂ := fun n ω ↦ (Z₂ n ω.2).1) (Y₂ := fun n ω ↦ (Z₂ n ω.2).2)
        htail₁ htail₂)

/-- Helper for Theorem 18.8: if the `d`-dimensional cube owner kernel has a successful coupling,
then so does the `(d + 1)`-dimensional cube owner kernel. -/
private theorem uniformCubeOwnerSucc_hasSuccessfulCoupling {d : ℕ}
    (hprev :
      HasSuccessfulCoupling.{0, 0}
        (fun x y ↦
          dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure x
            ({y} : Set (LatticePoint d)))) :
    HasSuccessfulCoupling.{0, 0}
      (fun x y ↦
        dirac_convolution_kernel (uniformCubeStepPMF (d + 1)).toMeasure x
          ({y} : Set (LatticePoint (d + 1)))) := by
  let e : LatticePoint (d + 1) ≃ᵐ (LatticePoint 1 × LatticePoint d) :=
    latticePointSuccMeasurableEquiv d
  let q₁ : LatticePoint 1 → LatticePoint 1 → ENNReal := fun x y ↦
    dirac_convolution_kernel (uniformCubeStepPMF 1).toMeasure x ({y} : Set (LatticePoint 1))
  let qd : LatticePoint d → LatticePoint d → ENNReal := fun x y ↦
    dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure x ({y} : Set (LatticePoint d))
  let qprod : (LatticePoint 1 × LatticePoint d) → (LatticePoint 1 × LatticePoint d) → ENNReal :=
    fun x y ↦ q₁ x.1 y.1 * qd x.2 y.2
  have hprod : HasSuccessfulCoupling qprod := by
    -- Proof comment: the successor step reduces to the product of the one-dimensional cube
    -- coupling and the already constructed `d`-dimensional cube coupling.
    exact productStepMatrix_hasSuccessfulCoupling
      (hq₁ := uniformCubeOwnerOne_hasSuccessfulCoupling) (hq₂ := hprev)
  have htransport :
      HasSuccessfulCoupling
        (fun x y : LatticePoint (d + 1) ↦ qprod (e x) (e y)) := by
    -- Proof comment: the head-tail measurable equivalence transports the product-state coupling
    -- back to the original `(d + 1)`-dimensional lattice state space.
    simpa [e, qprod] using
      hasSuccessfulCoupling_of_measurableEquiv (e := e) (q := qprod) hprod
  have hsucc_eq :
      (fun x y : LatticePoint (d + 1) ↦ qprod (e x) (e y)) =
        (fun x y : LatticePoint (d + 1) ↦
          dirac_convolution_kernel (uniformCubeStepPMF (d + 1)).toMeasure x
            ({y} : Set (LatticePoint (d + 1)))) := by
    funext x y
    have hrow :=
      congrArg
        (fun μ : Measure (LatticePoint 1 × LatticePoint d) ↦
          μ ({e y} : Set (LatticePoint 1 × LatticePoint d)))
        (uniformCubeOwnerKernel_succ_row_map_eq_parallel (d := d) x)
    have hpreimage :
        e ⁻¹' ({e y} : Set (LatticePoint 1 × LatticePoint d)) =
          ({y} : Set (LatticePoint (d + 1))) := by
      ext z
      simp [e]
    have hsingleton :
        ({e y} : Set (LatticePoint 1 × LatticePoint d)) =
          ({(e y).1} : Set (LatticePoint 1)) ×ˢ ({(e y).2} : Set (LatticePoint d)) := by
      ext z
      simp
    have hmap :
        Measure.map e
            ((discreteMatrixKernel
                (fun u v ↦
                  dirac_convolution_kernel (uniformCubeStepPMF (d + 1)).toMeasure u
                    ({v} : Set (LatticePoint (d + 1)))) x))
            ({e y} : Set (LatticePoint 1 × LatticePoint d)) =
          (((discreteMatrixKernel q₁) ∥ₖ (discreteMatrixKernel qd)) (e x))
            ({e y} : Set (LatticePoint 1 × LatticePoint d)) := hrow
    rw [Measure.map_apply e.measurable (measurableSet_singleton (e y)), hpreimage,
      hsingleton, Kernel.parallelComp_apply_prod, discreteMatrixKernel_apply_singleton,
      discreteMatrixKernel_apply_singleton, discreteMatrixKernel_apply_singleton] at hmap
    simpa [qprod, q₁, qd] using hmap.symm
  -- Proof comment: after identifying the transported product matrix with the successor cube owner
  -- matrix, the transported successful coupling is exactly the desired one.
  simpa [hsucc_eq] using htransport

/-- Helper for Theorem 18.8: every uniform-cube owner kernel admits a successful coupling. -/
private theorem uniformCubeOwner_hasSuccessfulCoupling (d : ℕ) :
    HasSuccessfulCoupling.{0, 0}
      (fun x y ↦
        dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure x
          ({y} : Set (LatticePoint d))) := by
  induction d with
  | zero =>
      -- Proof comment: the zero-dimensional lattice is subsingleton, so the diagonal coupling is
      -- already successful.
      simpa using subsingletonOwner_hasSuccessfulCoupling (ν := uniformCubeStepPMF 0)
  | succ d ih =>
      -- Proof comment: the successor-dimensional cube coupling comes from the head-tail product
      -- construction transported through `latticePointSuccMeasurableEquiv`.
      exact uniformCubeOwnerSucc_hasSuccessfulCoupling ih

/-- Helper for Theorem 18.8: composing `dirac_convolution_kernel ν` with a measure `μ`
recovers the additive convolution `μ ∗ ν`. -/
private lemma diracConvolutionKernel_comp_measure_eq_conv {d : ℕ}
    (μ ν : Measure (LatticePoint d)) [SFinite μ] [SFinite ν] :
    dirac_convolution_kernel ν ∘ₘ μ = μ ∗ ν := by
  -- Proof comment: evaluate the kernel-level constant-composition identity at the origin row.
  have hconst :=
    congrArg
      (fun κ : Kernel (LatticePoint d) (LatticePoint d) ↦ κ (0 : LatticePoint d))
      (dirac_convolution_kernel_comp_const_eq_const_conv (μ := μ) (ν := ν))
  simpa [Kernel.comp_apply] using hconst

/-- Helper for Theorem 18.8: after `n` steps, the row of a lattice convolution kernel is the
translate of the `n`-step law started from the origin. -/
private lemma diracConvolutionKernel_pow_apply_eq_diracConv_origin
    {d : ℕ} (μ : Measure (LatticePoint d)) :
    ∀ n : ℕ, ∀ x : LatticePoint d,
      ((dirac_convolution_kernel μ ^ n) x) =
        (Measure.dirac x) ∗ ((dirac_convolution_kernel μ ^ n) (0 : LatticePoint d)) :=
  fun n ↦ by
    induction n with
    | zero =>
        intro x
        -- Proof comment: the zero-step law is the starting Dirac mass.
        change Measure.dirac x = Measure.dirac x ∗ Measure.dirac (0 : LatticePoint d)
        simp
    | succ n ih =>
        intro x
        let κ : Kernel (LatticePoint d) (LatticePoint d) := dirac_convolution_kernel μ
        have hpow : κ ^ (n + 1) = κ ∘ₖ (κ ^ n) := by
          simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κ 1 n)
        -- Proof comment: evolve the translated `n`-step law by one more convolution step and
        -- reassociate the convolution product.
        calc
          (κ ^ (n + 1)) x = κ ∘ₘ ((κ ^ n) x) := by
            rw [hpow, Kernel.comp_apply]
          _ = ((κ ^ n) x) ∗ μ := by
            simpa [κ] using
              (diracConvolutionKernel_comp_measure_eq_conv
                (μ := (κ ^ n) x) (ν := μ))
          _ = (Measure.dirac x ∗ ((κ ^ n) (0 : LatticePoint d))) ∗ μ := by
            rw [ih x]
          _ = Measure.dirac x ∗ (((κ ^ n) (0 : LatticePoint d)) ∗ μ) := by
            rw [Measure.conv_assoc]
          _ = Measure.dirac x ∗ ((κ ^ (n + 1)) (0 : LatticePoint d)) := by
            congr 1
            calc
              ((κ ^ n) (0 : LatticePoint d)) ∗ μ = κ ∘ₘ ((κ ^ n) (0 : LatticePoint d)) := by
                symm
                simpa [κ] using
                  (diracConvolutionKernel_comp_measure_eq_conv
                    (μ := (κ ^ n) (0 : LatticePoint d)) (ν := μ))
              _ = (κ ∘ₖ (κ ^ n)) (0 : LatticePoint d) := by
                rw [Kernel.comp_apply]
              _ = (κ ^ (n + 1)) (0 : LatticePoint d) := by
                rw [← hpow]

/-- Helper for Theorem 18.8: the `n`-step singleton mass of a lattice convolution kernel depends
only on the displacement `y - x`. -/
private lemma diracConvolutionKernel_pow_apply_singleton_eq_originMass
    {d : ℕ} (μ : Measure (LatticePoint d)) (n : ℕ)
    (x y : LatticePoint d) :
    ((dirac_convolution_kernel μ ^ n) x) ({y} : Set (LatticePoint d)) =
      ((dirac_convolution_kernel μ ^ n) (0 : LatticePoint d)) ({y - x} : Set (LatticePoint d)) := by
  -- Proof comment: rewrite the `x`-row as a translated origin law and compute the singleton
  -- preimage under addition by `x`.
  rw [diracConvolutionKernel_pow_apply_eq_diracConv_origin (μ := μ) n x]
  rw [Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
  have hpreimage :
      (fun z : LatticePoint d ↦ x + z) ⁻¹' ({y} : Set (LatticePoint d)) = {y - x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hz)
    · intro hz
      exact by simpa [add_comm] using (eq_sub_iff_add_eq.mp hz)
  rw [hpreimage]

/-- Helper for Theorem 18.8: the selector-success count up to time `n + 1` is the previous count
plus the indicator of the next selector bit. -/
private lemma selectorSuccessCount_succ {Ω : Type*}
    (B : ℕ → Ω → Bool) (ω : Ω) (n : ℕ) :
    Finset.sum (Finset.range (n + 1)) (fun i ↦ bif B i ω then 1 else 0) =
      Finset.sum (Finset.range n) (fun i ↦ bif B i ω then 1 else 0) +
        bif B n ω then 1 else 0 := by
  -- Proof comment: split the finite sum at the last index `n`.
  simp [Finset.sum_range_succ]

/-- Helper for Theorem 18.8: the selector-success count is monotone in time. -/
private lemma selectorSuccessCount_monotone {Ω : Type*}
    (B : ℕ → Ω → Bool) :
    ∀ ω, Monotone fun n ↦
      Finset.sum (Finset.range n) (fun i ↦ bif B i ω then 1 else 0) := by
  intro ω n m hnm
  induction hnm with
  | refl =>
      exact le_rfl
  | @step m hnm ih =>
      -- Proof comment: one extra selector step can only add either `0` or `1`.
      calc
        Finset.sum (Finset.range n) (fun i ↦ bif B i ω then 1 else 0)
          ≤ Finset.sum (Finset.range m) (fun i ↦ bif B i ω then 1 else 0) := ih
        _ ≤ Finset.sum (Finset.range m) (fun i ↦ bif B i ω then 1 else 0) +
              bif B m ω then 1 else 0 := Nat.le_add_right _ _
        _ = Finset.sum (Finset.range (m + 1)) (fun i ↦ bif B i ω then 1 else 0) := by
            symm
            exact selectorSuccessCount_succ B ω m

/-- Helper for Theorem 18.8: the selector-success count up to time `n` never exceeds `n`. -/
private lemma selectorSuccessCount_le_time {Ω : Type*}
    (B : ℕ → Ω → Bool) (ω : Ω) :
    ∀ n : ℕ,
      Finset.sum (Finset.range n) (fun i ↦ bif B i ω then 1 else 0) ≤ n
  | 0 => by
      -- Proof comment: the empty selector prefix contributes zero successes.
      simp
  | n + 1 => by
      -- Proof comment: at time `n + 1`, the new selector contributes either `0` or `1`, so the
      -- count stays below the time index.
      rw [selectorSuccessCount_succ]
      by_cases hB : B n ω
      · simpa [hB] using Nat.succ_le_succ (selectorSuccessCount_le_time B ω n)
      · simpa [hB] using
          Nat.le_trans (selectorSuccessCount_le_time B ω n) (Nat.le_succ n)

/-- Helper for Theorem 18.8: matching selector bits on the whole prefix `{0, …, n - 1}` gives the
same selector-success count at time `n`. -/
private lemma selectorSuccessCount_eq_of_prefixEq
    {Ω : Type*} (B : ℕ → Ω → Bool) {ω ω' : Ω} {n : ℕ}
    (hprefix : ∀ i < n, B i ω = B i ω') :
    Finset.sum (Finset.range n) (fun i ↦ bif B i ω then 1 else 0) =
      Finset.sum (Finset.range n) (fun i ↦ bif B i ω' then 1 else 0) := by
  -- Proof comment: the summands agree pointwise on `range n`, so the finite selector counts are
  -- equal.
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact by simpa using congrArg (fun b : Bool ↦ bif b then 1 else 0) (hprefix i (Finset.mem_range.1 hi))

/-- Helper for Theorem 18.8: equality of selector-prefix tuples is equivalent to pointwise
agreement on the corresponding initial time interval. -/
private lemma selectorPrefixTuple_eq_iff_pointwise
    {Ω : Type*} (B : ℕ → Ω → Bool) {ω ω' : Ω} {s : ℕ} :
    (fun i : Fin s ↦ B i ω) = (fun i : Fin s ↦ B i ω') ↔
      ∀ i < s, B i ω = B i ω' := by
  constructor
  · intro h i hi
    -- Proof comment: evaluate the tuple equality at the coordinate `i`.
    simpa using congrArg (fun f : Fin s → Bool ↦ f ⟨i, hi⟩) h
  · intro h
    -- Proof comment: pointwise agreement on every prefix coordinate reconstructs the tuple.
    funext i
    exact h i i.2

/-- Helper for Theorem 18.8: the number of `true` bits in a finite selector prefix, written in the
same `Nat`-sum normal form as `selectorSuccessCount`. -/
private def selectorPrefixSuccessCount {s : ℕ} (u : Fin s → Bool) : ℕ :=
  Finset.sum (Finset.range s) fun i ↦
    bif h : i < s then u ⟨i, h⟩ else 0

/-- Helper for Theorem 18.8: the first `s` selector bits of a prefix of length `s + 1`. -/
private def selectorPrefixInit {s : ℕ} (u : Fin (s + 1) → Bool) : Fin s → Bool :=
  fun i ↦ u ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self s)⟩

/-- Helper for Theorem 18.8: the fresh selector bit at the end of a prefix of length `s + 1`. -/
private def selectorPrefixLast {s : ℕ} (u : Fin (s + 1) → Bool) : Bool :=
  u ⟨s, Nat.lt_succ_self s⟩

/-- Helper for Theorem 18.8: restrict a visible history on `Iic (s + 1)` to the shorter prefix
`Iic s`. -/
private def historyInit {α : Type*} {s : ℕ} (h : Finset.Iic (s + 1) → α) :
    Finset.Iic s → α :=
  fun i ↦ h ⟨i.1, Nat.le_trans i.2 (Nat.le_succ s)⟩

/-- Helper for Theorem 18.8: the visible endpoint at time `s` inside a history on `Iic (s + 1)`. -/
private def historyPrev {α : Type*} {s : ℕ} (h : Finset.Iic (s + 1) → α) : α :=
  h ⟨s, Finset.mem_Iic.2 (Nat.le_succ s)⟩

/-- Helper for Theorem 18.8: the visible endpoint at time `s + 1`. -/
private def historyLast {α : Type*} {s : ℕ} (h : Finset.Iic (s + 1) → α) : α :=
  h ⟨s + 1, Finset.mem_Iic.2 le_rfl⟩

/-- Helper for Theorem 18.8: restrict a selector word on `Fin s` to the shorter prefix indexed by
`i : Finset.Iic s`. -/
private def selectorPrefixRestrict {s : ℕ} (u : Fin s → Bool) (i : Finset.Iic s) :
    Fin i.1 → Bool :=
  fun j ↦ u ⟨j.1, Nat.lt_of_lt_of_le j.2 i.2⟩

/-- Helper for Theorem 18.8: restrict a visible history on `Finset.Iic s` to the shorter history
ending at the time index `i`. -/
private def historyRestrict {α : Type*} {s : ℕ} (h : Finset.Iic s → α) (i : Finset.Iic s) :
    Finset.Iic i.1 → α :=
  fun j ↦ h ⟨j.1, Nat.le_trans j.2 i.2⟩

/-- Helper for Theorem 18.8: the deterministic cube current reconstructed from a fixed start,
selector prefix, and visible history. -/
private def selectorHistoryCubeCurrent {d : ℕ} (x : LatticePoint d) :
    ∀ {s : ℕ}, (Fin s → Bool) → (Finset.Iic s → LatticePoint d) → LatticePoint d
  | 0, _, _ => x
  | s + 1, u, h =>
      let cubePrev :=
        selectorHistoryCubeCurrent x (selectorPrefixInit u) (historyInit h)
      if selectorPrefixLast u then
        cubePrev + (historyLast h - historyPrev h)
      else
        cubePrev

/-- Helper for Theorem 18.8: the deterministic residual current reconstructed from a fixed
selector prefix and visible history. -/
private def selectorHistoryResidualCurrent {d : ℕ} :
    ∀ {s : ℕ}, (Fin s → Bool) → (Finset.Iic s → LatticePoint d) → LatticePoint d
  | 0, _, _ => 0
  | s + 1, u, h =>
      let residualPrev :=
        selectorHistoryResidualCurrent (selectorPrefixInit u) (historyInit h)
      if selectorPrefixLast u then
        residualPrev
      else
        residualPrev + (historyLast h - historyPrev h)

/-- Helper for Theorem 18.8: extending a selector prefix by one fresh bit adds exactly that last
bit to the success count. -/
private lemma selectorPrefixSuccessCount_succ
    {s : ℕ} (u : Fin (s + 1) → Bool) :
    selectorPrefixSuccessCount u =
      selectorPrefixSuccessCount (selectorPrefixInit u) +
        bif selectorPrefixLast u then 1 else 0 := by
  -- Proof comment: split the count over `range (s + 1)` into the old prefix and the fresh final
  -- selector bit.
  unfold selectorPrefixSuccessCount selectorPrefixInit selectorPrefixLast
  rw [Finset.sum_range_succ]
  simp

/-- Helper for Theorem 18.8: the reconstructed cube and residual currents always add up to the
visible endpoint at the same time. -/
private lemma selectorHistoryCurrent_sum
    {d : ℕ} (x : LatticePoint d) :
    ∀ {s : ℕ} (u : Fin s → Bool) (h : Finset.Iic s → LatticePoint d),
      h ⟨0, Finset.mem_Iic.2 (Nat.zero_le s)⟩ = x →
        selectorHistoryCubeCurrent x u h + selectorHistoryResidualCurrent u h =
          h ⟨s, Finset.mem_Iic.2 le_rfl⟩
  | 0, u, h, hx => by
      -- Proof comment: at time `0`, the reconstruction starts from `(x, 0)`.
      simpa [selectorHistoryCubeCurrent, selectorHistoryResidualCurrent] using hx
  | s + 1, u, h, hx => by
      let uInit : Fin s → Bool := selectorPrefixInit u
      let hInit : Finset.Iic s → LatticePoint d := historyInit h
      have hsumInit :
          selectorHistoryCubeCurrent x uInit hInit +
              selectorHistoryResidualCurrent uInit hInit =
            historyPrev h := by
        -- Proof comment: apply the induction hypothesis to the shorter visible/selector prefix.
        simpa [uInit, hInit, historyPrev] using
          selectorHistoryCurrent_sum x uInit hInit hx
      by_cases hbranch : selectorPrefixLast u
      · -- Proof comment: on the `true` branch, the cube current absorbs the new visible increment.
        calc
          selectorHistoryCubeCurrent x u h + selectorHistoryResidualCurrent u h =
              (selectorHistoryCubeCurrent x uInit hInit + (historyLast h - historyPrev h)) +
                selectorHistoryResidualCurrent uInit hInit := by
                  simp [selectorHistoryCubeCurrent, selectorHistoryResidualCurrent, uInit, hInit,
                    hbranch]
          _ =
              historyLast h := by
                rw [← add_assoc, hsumInit]
                abel
      · -- Proof comment: on the `false` branch, the residual current absorbs the new increment.
        calc
          selectorHistoryCubeCurrent x u h + selectorHistoryResidualCurrent u h =
              selectorHistoryCubeCurrent x uInit hInit +
                (selectorHistoryResidualCurrent uInit hInit +
                  (historyLast h - historyPrev h)) := by
                    simp [selectorHistoryCubeCurrent, selectorHistoryResidualCurrent, uInit, hInit,
                      hbranch]
          _ =
              historyLast h := by
                rw [add_assoc, hsumInit]
                abel

/-- Helper for Theorem 18.8: the reconstructed hidden cube prefix records the cube current at
every visible time on a fixed selector/history slice. -/
private def selectorHistoryCubePrefix {d : ℕ} (x : LatticePoint d) {s : ℕ}
    (u : Fin s → Bool) (h : Finset.Iic s → LatticePoint d) :
    Finset.Iic s → LatticePoint d :=
  fun i ↦
    selectorHistoryCubeCurrent x (selectorPrefixRestrict u i) (historyRestrict h i)

/-- Helper for Theorem 18.8: the reconstructed hidden residual prefix records the residual
current at every visible time on the same selector/history slice. -/
private def selectorHistoryResidualPrefix {d : ℕ} {s : ℕ}
    (u : Fin s → Bool) (h : Finset.Iic s → LatticePoint d) :
    Finset.Iic s → LatticePoint d :=
  fun i ↦
    selectorHistoryResidualCurrent (selectorPrefixRestrict u i) (historyRestrict h i)

/-- Helper for Theorem 18.8: fixing the selector prefix tuple up to time `s` determines the
selector-success count at time `s`. -/
private lemma selectorSuccessCount_eq_selectorPrefixSuccessCount
    {Ω : Type*} (B : ℕ → Ω → Bool) {ω : Ω} {s : ℕ} {u : Fin s → Bool}
    (hprefix : (fun i : Fin s ↦ B i ω) = u) :
    Finset.sum (Finset.range s) (fun i ↦ bif B i ω then 1 else 0) =
      selectorPrefixSuccessCount u := by
  -- Proof comment: after unfolding the normal form for `selectorPrefixSuccessCount`, each
  -- summand is identified by evaluating the tuple equality at the corresponding prefix index.
  unfold selectorPrefixSuccessCount
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi_lt : i < s := Finset.mem_range.1 hi
  have hbit : B i ω = u ⟨i, hi_lt⟩ := by
    simpa using congrArg (fun f : Fin s → Bool ↦ f ⟨i, hi_lt⟩) hprefix
  simp [hi_lt, hbit]

/-- Helper for Theorem 18.8: fixing the selector prefix tuple up to time `s` and the fresh branch
bit at time `s` determines the selector-success count at time `s + 1`. -/
private lemma selectorSuccessCount_succ_eq_selectorPrefixBranchCount
    {Ω : Type*} (B : ℕ → Ω → Bool) {ω : Ω} {s : ℕ} {u : Fin s → Bool} {b : Bool}
    (hprefix : (fun i : Fin s ↦ B i ω) = u)
    (hbranch : B s ω = b) :
    Finset.sum (Finset.range (s + 1)) (fun i ↦ bif B i ω then 1 else 0) =
      selectorPrefixSuccessCount u + bif b then 1 else 0 := by
  -- Proof comment: split off the last selector bit with `selectorSuccessCount_succ`, then use the
  -- fixed prefix tuple to normalize the old count.
  rw [selectorSuccessCount_succ, hbranch, selectorSuccessCount_eq_selectorPrefixSuccessCount B hprefix]
  simp

/-- Helper for Theorem 18.8: a finite selector word has at most as many `true` bits as its
length. -/
private lemma selectorPrefixSuccessCount_le_time
    {s : ℕ} (u : Fin s → Bool) :
    selectorPrefixSuccessCount u ≤ s := by
  let B : ℕ → Unit → Bool := fun n _ ↦
    if h : n < s then
      u ⟨n, h⟩
    else
      false
  have hprefix : (fun i : Fin s ↦ B i ()) = u := by
    -- Proof comment: on the first `s` times, the auxiliary selector process is exactly `u`.
    funext i
    simp [B]
  calc
    selectorPrefixSuccessCount u =
        Finset.sum (Finset.range s) (fun i ↦ bif B i () then 1 else 0) := by
          symm
          exact selectorSuccessCount_eq_selectorPrefixSuccessCount B hprefix
    _ ≤ s := selectorSuccessCount_le_time B () s

/-- Helper for Theorem 18.8: restricting a selector word to a shorter visible prefix cannot
increase its success count. -/
private lemma selectorPrefixSuccessCount_restrict_le
    {s : ℕ} (u : Fin s → Bool) (i : Finset.Iic s) :
    selectorPrefixSuccessCount (selectorPrefixRestrict u i) ≤ selectorPrefixSuccessCount u := by
  let B : ℕ → Unit → Bool := fun n _ ↦
    if h : n < s then
      u ⟨n, h⟩
    else
      false
  have hprefix_i : (fun j : Fin i.1 ↦ B j ()) = selectorPrefixRestrict u i := by
    -- Proof comment: on the shorter prefix of length `i.1`, the same auxiliary selector process
    -- reads off the restricted selector word.
    funext j
    simp [B, selectorPrefixRestrict, Nat.lt_of_lt_of_le j.2 i.2]
  have hprefix : (fun j : Fin s ↦ B j ()) = u := by
    -- Proof comment: at the full length `s`, the auxiliary selector process is exactly `u`.
    funext j
    simp [B]
  calc
    selectorPrefixSuccessCount (selectorPrefixRestrict u i) =
        Finset.sum (Finset.range i.1) (fun j ↦ bif B j () then 1 else 0) := by
          symm
          exact selectorSuccessCount_eq_selectorPrefixSuccessCount B hprefix_i
    _ ≤ Finset.sum (Finset.range s) (fun j ↦ bif B j () then 1 else 0) :=
          (selectorSuccessCount_monotone B ()) i.2
    _ = selectorPrefixSuccessCount u := selectorSuccessCount_eq_selectorPrefixSuccessCount B hprefix

/-- Helper for Theorem 18.8: complementing a selector word turns successes into failures. -/
private lemma selectorPrefixSuccessCount_not :
    ∀ {s : ℕ} (u : Fin s → Bool),
      selectorPrefixSuccessCount (fun i ↦ !u i) = s - selectorPrefixSuccessCount u
  | 0, u => by
      -- Proof comment: the empty selector word has neither successes nor failures.
      simp [selectorPrefixSuccessCount]
  | s + 1, u => by
      let uInit : Fin s → Bool := selectorPrefixInit u
      let c : ℕ := selectorPrefixSuccessCount uInit
      have hc_le : c ≤ s := selectorPrefixSuccessCount_le_time uInit
      have hih :
          selectorPrefixSuccessCount (fun i : Fin s ↦ !uInit i) = s - c := by
        -- Proof comment: the inductive hypothesis already computes the failure count on the old
        -- prefix.
        simpa [uInit, c] using selectorPrefixSuccessCount_not uInit
      -- Proof comment: after splitting off the last selector bit, only the arithmetic of whether
      -- the last bit is `true` or `false` remains.
      rw [selectorPrefixSuccessCount_succ, selectorPrefixSuccessCount_succ]
      simp [selectorPrefixInit, selectorPrefixLast, uInit, hih]
      by_cases hlast : selectorPrefixLast u
      · simp [hlast, c]
        omega
      · simp [hlast, c]
        omega

/-- Helper for Theorem 18.8: the residual clock attached to a shorter visible prefix is bounded
by the residual clock at the final time. -/
private lemma selectorPrefixResidualCount_restrict_le
    {s : ℕ} (u : Fin s → Bool) (i : Finset.Iic s) :
    i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i) ≤
      s - selectorPrefixSuccessCount u := by
  have hcomp :
      selectorPrefixSuccessCount
          (selectorPrefixRestrict (fun j : Fin s ↦ !u j) i) ≤
        selectorPrefixSuccessCount (fun j : Fin s ↦ !u j) :=
    selectorPrefixSuccessCount_restrict_le (u := fun j : Fin s ↦ !u j) i
  -- Proof comment: the residual clock is the success count of the complemented selector word.
  simpa [selectorPrefixRestrict, selectorPrefixSuccessCount_not] using hcomp

/-- Helper for Theorem 18.8: on a fixed start-restricted selector/history slice, the hidden cube
and residual currents at time `s` are the deterministic currents reconstructed from that visible
history. -/
private lemma thinnedCurrents_eq_selectorHistoryCurrents
    {d : ℕ} {Ωcube Ωr Ωb : Type*}
    (B : ℕ → Ωb → Bool) (C : ℕ → Ωcube → LatticePoint d) (R : ℕ → Ωr → LatticePoint d)
    (x : LatticePoint d) {ω : Ωcube × (Ωr × Ωb)} :
    ∀ {s : ℕ} (u : Fin s → Bool) (h : Finset.Iic s → LatticePoint d),
      C 0 ω.1 = x →
      R 0 ω.2.1 = 0 →
      (fun i : Fin s ↦ B i ω.2.2) = u →
      (fun i : Finset.Iic s ↦
        let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0)
        C t ω.1 + R (i.1 - t) ω.2.1) = h →
      C (selectorPrefixSuccessCount u) ω.1 = selectorHistoryCubeCurrent x u h ∧
        R (s - selectorPrefixSuccessCount u) ω.2.1 = selectorHistoryResidualCurrent u h
  | 0, u, h, hC0, hR0, hprefix, hhistory => by
      -- Proof comment: at time `0`, the selector count is zero, so the hidden currents are
      -- exactly the fixed initial states `(x, 0)`.
      constructor
      · simpa [selectorPrefixSuccessCount, selectorHistoryCubeCurrent] using hC0
      · simpa [selectorPrefixSuccessCount, selectorHistoryResidualCurrent] using hR0
  | s + 1, u, h, hC0, hR0, hprefix, hhistory => by
      let uInit : Fin s → Bool := selectorPrefixInit u
      let hInit : Finset.Iic s → LatticePoint d := historyInit h
      have hprefixInit : (fun i : Fin s ↦ B i ω.2.2) = uInit := by
        funext i
        simpa [uInit, selectorPrefixInit] using
          congrArg (fun f : Fin (s + 1) → Bool ↦ f ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self s)⟩)
            hprefix
      have hhistoryInit :
          (fun i : Finset.Iic s ↦
            let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0)
            C t ω.1 + R (i.1 - t) ω.2.1) = hInit := by
        funext i
        simpa [hInit, historyInit] using
          congrArg
            (fun f : Finset.Iic (s + 1) → LatticePoint d ↦
              f ⟨i.1, Nat.le_trans i.2 (Nat.le_succ s)⟩)
            hhistory
      rcases
        thinnedCurrents_eq_selectorHistoryCurrents
          (B := B) (C := C) (R := R) x uInit hInit hC0 hR0 hprefixInit hhistoryInit
        with ⟨hCubeInit, hResidInit⟩
      have hcountInit :
          Finset.sum (Finset.range s) (fun i ↦ bif B i ω.2.2 then 1 else 0) =
            selectorPrefixSuccessCount uInit :=
        selectorSuccessCount_eq_selectorPrefixSuccessCount B hprefixInit
      have hcount :
          Finset.sum (Finset.range (s + 1)) (fun i ↦ bif B i ω.2.2 then 1 else 0) =
            selectorPrefixSuccessCount u := by
        simpa using selectorSuccessCount_eq_selectorPrefixSuccessCount B hprefix
      have hbranch : B s ω.2.2 = selectorPrefixLast u := by
        simpa [selectorPrefixLast] using
          congrArg (fun f : Fin (s + 1) → Bool ↦ f ⟨s, Nat.lt_succ_self s⟩) hprefix
      have hcountInit_le : selectorPrefixSuccessCount uInit ≤ s := by
        rw [← hcountInit]
        exact selectorSuccessCount_le_time B ω.2.2 s
      have hprev :
          historyPrev h =
            C (selectorPrefixSuccessCount uInit) ω.1 +
              R (s - selectorPrefixSuccessCount uInit) ω.2.1 := by
        simpa [historyPrev, hcountInit] using
          congrArg
            (fun f : Finset.Iic (s + 1) → LatticePoint d ↦
              f ⟨s, Finset.mem_Iic.2 (Nat.le_succ s)⟩)
            hhistory
      have hlast :
          historyLast h =
            C (selectorPrefixSuccessCount u) ω.1 +
              R (s + 1 - selectorPrefixSuccessCount u) ω.2.1 := by
        simpa [historyLast, hcount] using
          congrArg
            (fun f : Finset.Iic (s + 1) → LatticePoint d ↦
              f ⟨s + 1, Finset.mem_Iic.2 le_rfl⟩)
            hhistory
      by_cases hlastBranch : selectorPrefixLast u
      · -- Proof comment: on the `true` branch, the cube current absorbs the new visible
        -- increment while the residual current stays fixed.
        have hcountSucc :
            selectorPrefixSuccessCount u = selectorPrefixSuccessCount uInit + 1 := by
          rw [selectorPrefixSuccessCount_succ]
          simp [hlastBranch]
        constructor
        · calc
            C (selectorPrefixSuccessCount u) ω.1
                = C (selectorPrefixSuccessCount uInit + 1) ω.1 := by
                    rw [hcountSucc]
            _ = C (selectorPrefixSuccessCount uInit) ω.1 +
                  (historyLast h - historyPrev h) := by
                    rw [hlast, hcountSucc]
                    rw [Nat.succ_sub (Nat.succ_le_succ hcountInit_le), hprev]
                    abel
            _ = selectorHistoryCubeCurrent x uInit hInit +
                  (historyLast h - historyPrev h) := by
                    rw [hCubeInit]
            _ = selectorHistoryCubeCurrent x u h := by
                    simp [selectorHistoryCubeCurrent, uInit, hInit, hlastBranch]
        · calc
            R (s + 1 - selectorPrefixSuccessCount u) ω.2.1
                = R (s - selectorPrefixSuccessCount uInit) ω.2.1 := by
                    rw [hcountSucc]
                    simp [Nat.succ_sub (Nat.succ_le_succ hcountInit_le)]
            _ = selectorHistoryResidualCurrent uInit hInit := by
                  rw [hResidInit]
            _ = selectorHistoryResidualCurrent u h := by
                  simp [selectorHistoryResidualCurrent, uInit, hInit, hlastBranch]
      · -- Proof comment: on the `false` branch, the residual current absorbs the new visible
        -- increment while the cube current stays fixed.
        have hcountSucc :
            selectorPrefixSuccessCount u = selectorPrefixSuccessCount uInit := by
          rw [selectorPrefixSuccessCount_succ]
          simp [hlastBranch]
        constructor
        · calc
            C (selectorPrefixSuccessCount u) ω.1
                = C (selectorPrefixSuccessCount uInit) ω.1 := by
                    rw [hcountSucc]
            _ = selectorHistoryCubeCurrent x uInit hInit := by
                  rw [hCubeInit]
            _ = selectorHistoryCubeCurrent x u h := by
                  simp [selectorHistoryCubeCurrent, uInit, hInit, hlastBranch]
        · calc
            R (s + 1 - selectorPrefixSuccessCount u) ω.2.1
                = R (s - selectorPrefixSuccessCount uInit + 1) ω.2.1 := by
                    rw [hcountSucc]
                    simp
            _ = R (s - selectorPrefixSuccessCount uInit) ω.2.1 +
                  (historyLast h - historyPrev h) := by
                    rw [hlast, hcountSucc, hprev]
                    abel
            _ = selectorHistoryResidualCurrent uInit hInit +
                  (historyLast h - historyPrev h) := by
                    rw [hResidInit]
            _ = selectorHistoryResidualCurrent u h := by
                    simp [selectorHistoryResidualCurrent, uInit, hInit, hlastBranch]

/-- Helper for Theorem 18.8: on a started-history slice, the whole hidden cube/residual prefixes
are uniquely reconstructed from the visible history and the selector prefix. -/
private theorem thinnedHiddenPrefixes_eq_selectorHistoryPrefixes
    {d : ℕ} {Ωcube Ωr Ωb : Type*}
    (B : ℕ → Ωb → Bool) (C : ℕ → Ωcube → LatticePoint d) (R : ℕ → Ωr → LatticePoint d)
    (x : LatticePoint d) {ω : Ωcube × (Ωr × Ωb)} {s : ℕ}
    {u : Fin s → Bool} {h : Finset.Iic s → LatticePoint d}
    (hC0 : C 0 ω.1 = x)
    (hR0 : R 0 ω.2.1 = 0)
    (hprefix : (fun i : Fin s ↦ B i ω.2.2) = u)
    (hhistory :
      (fun i : Finset.Iic s ↦
        let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0)
        C t ω.1 + R (i.1 - t) ω.2.1) = h) :
    (fun i : Finset.Iic s ↦
      C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1) =
        selectorHistoryCubePrefix x u h ∧
      (fun i : Finset.Iic s ↦
        R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1) =
          selectorHistoryResidualPrefix u h := by
  constructor
  · -- Proof comment: apply the one-time current reconstruction at each visible index after
    -- restricting the selector word and visible history to that shorter prefix.
    funext i
    let ui : Fin i.1 → Bool := selectorPrefixRestrict u i
    let hi : Finset.Iic i.1 → LatticePoint d := historyRestrict h i
    have hprefix_i : (fun j : Fin i.1 ↦ B j ω.2.2) = ui := by
      funext j
      simpa [ui, selectorPrefixRestrict] using
        congrArg
          (fun f : Fin s → Bool ↦ f ⟨j.1, Nat.lt_of_lt_of_le j.2 i.2⟩)
          hprefix
    have hhistory_i :
        (fun j : Finset.Iic i.1 ↦
          let t := Finset.sum (Finset.range j.1) (fun k ↦ bif B k ω.2.2 then 1 else 0)
          C t ω.1 + R (j.1 - t) ω.2.1) = hi := by
      funext j
      simpa [hi, historyRestrict] using
        congrArg
          (fun f : Finset.Iic s → LatticePoint d ↦
            f ⟨j.1, Nat.le_trans j.2 i.2⟩)
          hhistory
    exact
      (thinnedCurrents_eq_selectorHistoryCurrents
        (B := B) (C := C) (R := R) x ui hi hC0 hR0 hprefix_i hhistory_i).1
  · -- Proof comment: the residual prefix is recovered by the same restricted-prefix argument,
    -- taking the second component of the current reconstruction theorem.
    funext i
    let ui : Fin i.1 → Bool := selectorPrefixRestrict u i
    let hi : Finset.Iic i.1 → LatticePoint d := historyRestrict h i
    have hprefix_i : (fun j : Fin i.1 ↦ B j ω.2.2) = ui := by
      funext j
      simpa [ui, selectorPrefixRestrict] using
        congrArg
          (fun f : Fin s → Bool ↦ f ⟨j.1, Nat.lt_of_lt_of_le j.2 i.2⟩)
          hprefix
    have hhistory_i :
        (fun j : Finset.Iic i.1 ↦
          let t := Finset.sum (Finset.range j.1) (fun k ↦ bif B k ω.2.2 then 1 else 0)
          C t ω.1 + R (j.1 - t) ω.2.1) = hi := by
      funext j
      simpa [hi, historyRestrict] using
        congrArg
          (fun f : Finset.Iic s → LatticePoint d ↦
            f ⟨j.1, Nat.le_trans j.2 i.2⟩)
          hhistory
    exact
      (thinnedCurrents_eq_selectorHistoryCurrents
        (B := B) (C := C) (R := R) x ui hi hC0 hR0 hprefix_i hhistory_i).2

/-- Helper for Theorem 18.8: once the selector prefix and the required cube/residual prefixes
agree, the thinned process has the same state at that time. -/
private lemma thinnedProcess_eq_of_prefixDataEq
    {d : ℕ} {Ωcube Ωr Ωb : Type*}
    (B : ℕ → Ωb → Bool) (C : ℕ → Ωcube → LatticePoint d) (R : ℕ → Ωr → LatticePoint d)
    {ω ω' : Ωcube × (Ωr × Ωb)} {n : ℕ}
    (hselector : ∀ i < n, B i ω.2.2 = B i ω'.2.2)
    (hcube :
      ∀ k ≤ Finset.sum (Finset.range n) (fun i ↦ bif B i ω.2.2 then 1 else 0),
        C k ω.1 = C k ω'.1)
    (hresid : ∀ k ≤ n, R k ω.2.1 = R k ω'.2.1) :
    (let s := Finset.sum (Finset.range n) (fun i ↦ bif B i ω.2.2 then 1 else 0)
      C s ω.1 + R (n - s) ω.2.1) =
      (let s := Finset.sum (Finset.range n) (fun i ↦ bif B i ω'.2.2 then 1 else 0)
        C s ω'.1 + R (n - s) ω'.2.1) := by
  let s :=
    Finset.sum (Finset.range n) (fun i ↦ bif B i ω.2.2 then 1 else 0)
  let s' :=
    Finset.sum (Finset.range n) (fun i ↦ bif B i ω'.2.2 then 1 else 0)
  have hs : s = s' := selectorSuccessCount_eq_of_prefixEq B hselector
  -- Proof comment: the selector clocks agree, then the visible state agrees because both the
  -- cube and residual coordinates are already synchronized on the required finite prefixes.
  calc
    (let s := Finset.sum (Finset.range n) (fun i ↦ bif B i ω.2.2 then 1 else 0)
      C s ω.1 + R (n - s) ω.2.1)
        = C s ω.1 + R (n - s) ω.2.1 := by
            simp [s]
    _ = C s ω'.1 + R (n - s) ω'.2.1 := by
          rw [hcube s le_rfl, hresid (n - s) (Nat.sub_le _ _)]
    _ = C s' ω'.1 + R (n - s') ω'.2.1 := by
          rw [hs]
    _ = (let s := Finset.sum (Finset.range n) (fun i ↦ bif B i ω'.2.2 then 1 else 0)
        C s ω'.1 + R (n - s) ω'.2.1) := by
          simp [s']

/-- Helper for Theorem 18.8: matching selector prefixes together with the corresponding finite
cube/residual prefixes determines the whole visible history of the thinned process. -/
private lemma thinnedHistory_eq_of_prefixDataEq
    {d : ℕ} {Ωcube Ωr Ωb : Type*}
    (B : ℕ → Ωb → Bool) (C : ℕ → Ωcube → LatticePoint d) (R : ℕ → Ωr → LatticePoint d)
    {ω ω' : Ωcube × (Ωr × Ωb)} {s : ℕ}
    (hselector : ∀ i < s, B i ω.2.2 = B i ω'.2.2)
    (hcube :
      ∀ k ≤ Finset.sum (Finset.range s) (fun i ↦ bif B i ω.2.2 then 1 else 0),
        C k ω.1 = C k ω'.1)
    (hresid : ∀ k ≤ s, R k ω.2.1 = R k ω'.2.1) :
    (fun i : Finset.Iic s ↦
      let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0)
      C t ω.1 + R (i.1 - t) ω.2.1) =
      (fun i : Finset.Iic s ↦
        let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω'.2.2 then 1 else 0)
        C t ω'.1 + R (i.1 - t) ω'.2.1) := by
  -- Proof comment: apply the one-time equality at each history index and use monotonicity of the
  -- selector clock to inherit the larger cube-prefix agreement.
  funext i
  refine thinnedProcess_eq_of_prefixDataEq B C R ?_ ?_ ?_
  · intro j hj
    exact hselector j (lt_of_lt_of_le hj i.2)
  · intro k hk
    exact hcube k <| Nat.le_trans hk ((selectorSuccessCount_monotone B ω.2.2) i.2)
  · intro k hk
    exact hresid k (Nat.le_trans hk i.2)

/-- Helper for Theorem 18.8: matching selector bits through time `s` together with the required
cube/residual prefixes determines both the visible history up to `s` and the next state. -/
private lemma thinnedHistoryNext_eq_of_prefixDataEq
    {d : ℕ} {Ωcube Ωr Ωb : Type*}
    (B : ℕ → Ωb → Bool) (C : ℕ → Ωcube → LatticePoint d) (R : ℕ → Ωr → LatticePoint d)
    {ω ω' : Ωcube × (Ωr × Ωb)} {s : ℕ}
    (hselector : ∀ i ≤ s, B i ω.2.2 = B i ω'.2.2)
    (hcube :
      ∀ k ≤ Finset.sum (Finset.range (s + 1)) (fun i ↦ bif B i ω.2.2 then 1 else 0),
        C k ω.1 = C k ω'.1)
    (hresid : ∀ k ≤ s + 1, R k ω.2.1 = R k ω'.2.1) :
    ((fun i : Finset.Iic s ↦
        let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0)
        C t ω.1 + R (i.1 - t) ω.2.1),
      (let t := Finset.sum (Finset.range (s + 1)) (fun j ↦ bif B j ω.2.2 then 1 else 0)
        C t ω.1 + R (s + 1 - t) ω.2.1)) =
      ((fun i : Finset.Iic s ↦
          let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω'.2.2 then 1 else 0)
          C t ω'.1 + R (i.1 - t) ω'.2.1),
        (let t := Finset.sum (Finset.range (s + 1)) (fun j ↦ bif B j ω'.2.2 then 1 else 0)
          C t ω'.1 + R (s + 1 - t) ω'.2.1)) := by
  -- Proof comment: the visible history is the time-by-time restriction of the larger prefix
  -- agreement, while the next state is the same equality at time `s + 1`.
  refine Prod.ext ?_ ?_
  · refine thinnedHistory_eq_of_prefixDataEq B C R ?_ ?_ ?_
    · intro i hi
      exact hselector i (Nat.le_of_lt_succ hi)
    · intro k hk
      exact hcube k <| Nat.le_trans hk ((selectorSuccessCount_monotone B ω.2.2) (Nat.le_succ s))
    · intro k hk
      exact hresid k (Nat.le_trans hk (Nat.le_succ s))
  · refine thinnedProcess_eq_of_prefixDataEq B C R ?_ ?_ ?_
    · intro i hi
      exact hselector i (Nat.lt_succ_iff.mp hi)
    · exact hcube
    · exact hresid

/-- Helper for Theorem 18.8: a selector-prefix tuple equality packages the pointwise selector
agreement needed to identify the thinned visible history. -/
private lemma thinnedHistory_eq_of_selectorPrefixTupleEq
    {d : ℕ} {Ωcube Ωr Ωb : Type*}
    (B : ℕ → Ωb → Bool) (C : ℕ → Ωcube → LatticePoint d) (R : ℕ → Ωr → LatticePoint d)
    {ω ω' : Ωcube × (Ωr × Ωb)} {s : ℕ}
    (hprefix : (fun i : Fin s ↦ B i ω.2.2) = (fun i : Fin s ↦ B i ω'.2.2))
    (hcube :
      ∀ k ≤ Finset.sum (Finset.range s) (fun i ↦ bif B i ω.2.2 then 1 else 0),
        C k ω.1 = C k ω'.1)
    (hresid : ∀ k ≤ s, R k ω.2.1 = R k ω'.2.1) :
    (fun i : Finset.Iic s ↦
      let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0)
      C t ω.1 + R (i.1 - t) ω.2.1) =
      (fun i : Finset.Iic s ↦
        let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω'.2.2 then 1 else 0)
        C t ω'.1 + R (i.1 - t) ω'.2.1) := by
  -- Proof comment: the tuple equality is exactly the prefixwise selector agreement required by
  -- `thinnedHistory_eq_of_prefixDataEq`.
  refine thinnedHistory_eq_of_prefixDataEq B C R ?_ hcube hresid
  exact (selectorPrefixTuple_eq_iff_pointwise B).mp hprefix

/-- Helper for Theorem 18.8: a selector-prefix tuple equality together with the fresh branch bit
packages the selector hypotheses needed to identify the visible history/next-state pair. -/
private lemma thinnedHistoryNext_eq_of_selectorPrefixBranchEq
    {d : ℕ} {Ωcube Ωr Ωb : Type*}
    (B : ℕ → Ωb → Bool) (C : ℕ → Ωcube → LatticePoint d) (R : ℕ → Ωr → LatticePoint d)
    {ω ω' : Ωcube × (Ωr × Ωb)} {s : ℕ}
    (hprefix : (fun i : Fin s ↦ B i ω.2.2) = (fun i : Fin s ↦ B i ω'.2.2))
    (hbranch : B s ω.2.2 = B s ω'.2.2)
    (hcube :
      ∀ k ≤ Finset.sum (Finset.range (s + 1)) (fun i ↦ bif B i ω.2.2 then 1 else 0),
        C k ω.1 = C k ω'.1)
    (hresid : ∀ k ≤ s + 1, R k ω.2.1 = R k ω'.2.1) :
    ((fun i : Finset.Iic s ↦
        let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0)
        C t ω.1 + R (i.1 - t) ω.2.1),
      (let t := Finset.sum (Finset.range (s + 1)) (fun j ↦ bif B j ω.2.2 then 1 else 0)
        C t ω.1 + R (s + 1 - t) ω.2.1)) =
      ((fun i : Finset.Iic s ↦
          let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω'.2.2 then 1 else 0)
          C t ω'.1 + R (i.1 - t) ω'.2.1),
        (let t := Finset.sum (Finset.range (s + 1)) (fun j ↦ bif B j ω'.2.2 then 1 else 0)
          C t ω'.1 + R (s + 1 - t) ω'.2.1)) := by
  have hprefix_pointwise : ∀ i < s, B i ω.2.2 = B i ω'.2.2 :=
    (selectorPrefixTuple_eq_iff_pointwise B).mp hprefix
  -- Proof comment: split the selector agreement into the old prefix coordinates and the fresh
  -- branch bit at time `s`, then invoke the existing prefix-data transport lemma.
  refine thinnedHistoryNext_eq_of_prefixDataEq B C R ?_ hcube hresid
  intro i hi
  rcases lt_or_eq_of_le hi with hlt | rfl
  · exact hprefix_pointwise i hlt
  · exact hbranch

/-- Helper for Theorem 18.8: if the next selector bit is `true`, the thinned process uses one
more cube step and leaves the residual clock unchanged. -/
private lemma thinnedProcess_succ_of_selector_true
    {d : ℕ} {Ωcube Ωr Ωb : Type*}
    (B : ℕ → Ωb → Bool) (C : ℕ → Ωcube → LatticePoint d) (R : ℕ → Ωr → LatticePoint d)
    (ω : Ωcube × (Ωr × Ωb)) (n : ℕ) (hB : B n ω.2.2 = true) :
    let s := Finset.sum (Finset.range n) (fun i ↦ bif B i ω.2.2 then 1 else 0)
    let s' := Finset.sum (Finset.range (n + 1)) (fun i ↦ bif B i ω.2.2 then 1 else 0)
    C s' ω.1 + R ((n + 1) - s') ω.2.1 = C (s + 1) ω.1 + R (n - s) ω.2.1 := by
  -- Proof comment: rewrite the new selector count using `selectorSuccessCount_succ`, then cancel
  -- the extra success in both the cube clock and the residual time index.
  dsimp
  rw [selectorSuccessCount_succ, hB]
  simp [Nat.succ_eq_add_one, Nat.add_assoc]

/-- Helper for Theorem 18.8: if the next selector bit is `false`, the thinned process keeps the
cube clock fixed and advances the residual path by one step. -/
private lemma thinnedProcess_succ_of_selector_false
    {d : ℕ} {Ωcube Ωr Ωb : Type*}
    (B : ℕ → Ωb → Bool) (C : ℕ → Ωcube → LatticePoint d) (R : ℕ → Ωr → LatticePoint d)
    (ω : Ωcube × (Ωr × Ωb)) (n : ℕ) (hB : B n ω.2.2 = false) :
    let s := Finset.sum (Finset.range n) (fun i ↦ bif B i ω.2.2 then 1 else 0)
    let s' := Finset.sum (Finset.range (n + 1)) (fun i ↦ bif B i ω.2.2 then 1 else 0)
    C s' ω.1 + R ((n + 1) - s') ω.2.1 = C s ω.1 + R (n - s + 1) ω.2.1 := by
  -- Proof comment: with a failed selector bit, the selector count stays fixed; the only change
  -- is that the residual clock moves from `n - s` to `(n - s) + 1`.
  dsimp
  rw [selectorSuccessCount_succ, hB]
  have hs_le :
      Finset.sum (Finset.range n) (fun i ↦ bif B i ω.2.2 then 1 else 0) ≤ n :=
    selectorSuccessCount_le_time B ω.2.2 n
  rw [Nat.succ_sub hs_le]
  rfl

/-- Helper for Theorem 18.8: on a fixed selector/history branch started from `(x, 0)`, the next
visible state is the active hidden next step plus the inactive deterministic current reconstructed
from the visible history. -/
private lemma thinnedNext_eq_of_selectorHistoryBranch
    {d : ℕ} {Ωcube Ωr Ωb : Type*}
    (B : ℕ → Ωb → Bool) (C : ℕ → Ωcube → LatticePoint d) (R : ℕ → Ωr → LatticePoint d)
    (x : LatticePoint d) {ω : Ωcube × (Ωr × Ωb)} {s : ℕ}
    {u : Fin s → Bool} {h : Finset.Iic s → LatticePoint d} {b : Bool}
    (hC0 : C 0 ω.1 = x)
    (hR0 : R 0 ω.2.1 = 0)
    (hprefix : (fun i : Fin s ↦ B i ω.2.2) = u)
    (hhistory :
      (fun i : Finset.Iic s ↦
        let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0)
        C t ω.1 + R (i.1 - t) ω.2.1) = h)
    (hbranch : B s ω.2.2 = b) :
    (let t := Finset.sum (Finset.range (s + 1)) (fun j ↦ bif B j ω.2.2 then 1 else 0)
      C t ω.1 + R (s + 1 - t) ω.2.1) =
      if b then
        C (selectorPrefixSuccessCount u + 1) ω.1 + selectorHistoryResidualCurrent u h
      else
        selectorHistoryCubeCurrent x u h + R (s - selectorPrefixSuccessCount u + 1) ω.2.1 := by
  rcases
    thinnedCurrents_eq_selectorHistoryCurrents
      (B := B) (C := C) (R := R) x u h hC0 hR0 hprefix hhistory
    with ⟨hCube, hResid⟩
  by_cases hb : b
  · -- Proof comment: on the `true` branch, the fresh hidden step is a cube step and the
    -- inactive residual current is already the reconstructed one.
    subst hb
    have hcount :
        Finset.sum (Finset.range s) (fun i ↦ bif B i ω.2.2 then 1 else 0) =
          selectorPrefixSuccessCount u :=
      selectorSuccessCount_eq_selectorPrefixSuccessCount B hprefix
    calc
      (let t := Finset.sum (Finset.range (s + 1)) (fun j ↦ bif B j ω.2.2 then 1 else 0)
        C t ω.1 + R (s + 1 - t) ω.2.1)
          = C (selectorPrefixSuccessCount u + 1) ω.1 +
              R (s - selectorPrefixSuccessCount u) ω.2.1 := by
                simpa [hcount] using thinnedProcess_succ_of_selector_true B C R ω s hbranch
      _ = C (selectorPrefixSuccessCount u + 1) ω.1 + selectorHistoryResidualCurrent u h := by
            rw [hResid]
      _ = if true then
            C (selectorPrefixSuccessCount u + 1) ω.1 + selectorHistoryResidualCurrent u h
          else
            selectorHistoryCubeCurrent x u h + R (s - selectorPrefixSuccessCount u + 1) ω.2.1 := by
              simp
  · -- Proof comment: on the `false` branch, the fresh hidden step is a residual step and the
    -- inactive cube current is already the reconstructed one.
    have hcount :
        Finset.sum (Finset.range s) (fun i ↦ bif B i ω.2.2 then 1 else 0) =
          selectorPrefixSuccessCount u :=
      selectorSuccessCount_eq_selectorPrefixSuccessCount B hprefix
    calc
      (let t := Finset.sum (Finset.range (s + 1)) (fun j ↦ bif B j ω.2.2 then 1 else 0)
        C t ω.1 + R (s + 1 - t) ω.2.1)
          = C (selectorPrefixSuccessCount u) ω.1 +
              R (s - selectorPrefixSuccessCount u + 1) ω.2.1 := by
                simpa [hcount] using thinnedProcess_succ_of_selector_false B C R ω s hbranch
      _ = selectorHistoryCubeCurrent x u h + R (s - selectorPrefixSuccessCount u + 1) ω.2.1 := by
            rw [hCube]
      _ = if b then
            C (selectorPrefixSuccessCount u + 1) ω.1 + selectorHistoryResidualCurrent u h
          else
            selectorHistoryCubeCurrent x u h + R (s - selectorPrefixSuccessCount u + 1) ω.2.1 := by
              simp [hb]

/-- Helper for Theorem 18.8: on a fixed started-history selector branch, the visible next-state
atom is equivalent to the corresponding active hidden one-step atom. -/
private lemma thinnedNext_eq_iff_activeBranchTarget
    {d : ℕ} {Ωcube Ωr Ωb : Type*}
    (B : ℕ → Ωb → Bool) (C : ℕ → Ωcube → LatticePoint d) (R : ℕ → Ωr → LatticePoint d)
    (x y : LatticePoint d) {ω : Ωcube × (Ωr × Ωb)} {s : ℕ}
    {u : Fin s → Bool} {h : Finset.Iic s → LatticePoint d} {b : Bool}
    (hC0 : C 0 ω.1 = x)
    (hR0 : R 0 ω.2.1 = 0)
    (hprefix : (fun i : Fin s ↦ B i ω.2.2) = u)
    (hhistory :
      (fun i : Finset.Iic s ↦
        let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0)
        C t ω.1 + R (i.1 - t) ω.2.1) = h)
    (hbranch : B s ω.2.2 = b) :
    ((let t := Finset.sum (Finset.range (s + 1)) (fun j ↦ bif B j ω.2.2 then 1 else 0)
      C t ω.1 + R (s + 1 - t) ω.2.1) = y) ↔
      if b then
        C (selectorPrefixSuccessCount u + 1) ω.1 =
          y - selectorHistoryResidualCurrent u h
      else
        R (s - selectorPrefixSuccessCount u + 1) ω.2.1 =
          y - selectorHistoryCubeCurrent x u h := by
  have hnext :=
    thinnedNext_eq_of_selectorHistoryBranch
      (B := B) (C := C) (R := R) x hC0 hR0 hprefix hhistory hbranch
  by_cases hb : b
  · subst hb
    constructor
    · intro hy
      calc
        C (selectorPrefixSuccessCount u + 1) ω.1 =
            y - selectorHistoryResidualCurrent u h := by
              rw [← hy, hnext]
              abel
    · intro hy
      calc
        (let t := Finset.sum (Finset.range (s + 1)) (fun j ↦ bif B j ω.2.2 then 1 else 0)
          C t ω.1 + R (s + 1 - t) ω.2.1) =
            C (selectorPrefixSuccessCount u + 1) ω.1 +
              selectorHistoryResidualCurrent u h := by
                simpa [hb] using hnext
        _ = y := by
              rw [hy]
              abel
  · constructor
    · intro hy
      calc
        R (s - selectorPrefixSuccessCount u + 1) ω.2.1 =
            y - selectorHistoryCubeCurrent x u h := by
              rw [← hy, hnext]
              simp [hb]
              abel
    · intro hy
      calc
        (let t := Finset.sum (Finset.range (s + 1)) (fun j ↦ bif B j ω.2.2 then 1 else 0)
          C t ω.1 + R (s + 1 - t) ω.2.1) =
            selectorHistoryCubeCurrent x u h +
              R (s - selectorPrefixSuccessCount u + 1) ω.2.1 := by
                simpa [hb] using hnext
        _ = y := by
              rw [hy]
              abel

/-- Helper for Theorem 18.8: on the full start slice and in the started-history branch
`h 0 = x`, fixing the visible history, selector prefix, branch bit, and next state is equivalent
to fixing the deterministic hidden cube/residual prefixes together with the active hidden
one-step target. -/
private lemma startedHistoryAtom_on_start_iff_splitData
    {d : ℕ} {Ωcube Ωr Ωb : Type*}
    (B : ℕ → Ωb → Bool) (C : ℕ → Ωcube → LatticePoint d) (R : ℕ → Ωr → LatticePoint d)
    (x : LatticePoint d) {s : ℕ}
    {u : Fin s → Bool} {h : Finset.Iic s → LatticePoint d}
    {ω : Ωcube × (Ωr × Ωb)}
    (hx : h ⟨0, Finset.mem_Iic.2 (Nat.zero_le s)⟩ = x) :
    ((fun i : Finset.Iic s ↦
        let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0)
        C t ω.1 + R (i.1 - t) ω.2.1) = h ∧
      (fun i : Fin s ↦ B i ω.2.2) = u ∧
      C 0 ω.1 = x ∧
      R 0 ω.2.1 = 0) ↔
    ((fun i : Fin s ↦ B i ω.2.2) = u ∧
      (fun i : Finset.Iic s ↦
        C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1) =
          selectorHistoryCubePrefix x u h ∧
      (fun i : Finset.Iic s ↦
        R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1) =
          selectorHistoryResidualPrefix u h ∧
      C 0 ω.1 = x ∧
      R 0 ω.2.1 = 0) := by
  constructor
  · intro hω
    rcases hω with ⟨hhistory, hprefix, hC0, hR0⟩
    rcases
      thinnedHiddenPrefixes_eq_selectorHistoryPrefixes
        (B := B) (C := C) (R := R) x hC0 hR0 hprefix hhistory
      with ⟨hcube, hresid⟩
    -- Proof comment: on the started-history slice, the hidden cube and residual prefixes are
    -- exactly the deterministic reconstructions from the visible history and selector word.
    exact ⟨hprefix, hcube, hresid, hC0, hR0⟩
  · intro hω
    rcases hω with ⟨hprefix, hcube, hresid, hC0, hR0⟩
    have hhistory :
        (fun i : Finset.Iic s ↦
          let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0)
          C t ω.1 + R (i.1 - t) ω.2.1) = h := by
      funext i
      have hprefix_i : (fun j : Fin i.1 ↦ B j ω.2.2) = selectorPrefixRestrict u i := by
        funext j
        simpa [selectorPrefixRestrict] using
          congrArg
            (fun f : Fin s → Bool ↦ f ⟨j.1, Nat.lt_of_lt_of_le j.2 i.2⟩)
            hprefix
      have hcount_i :
          Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0) =
            selectorPrefixSuccessCount (selectorPrefixRestrict u i) :=
        selectorSuccessCount_eq_selectorPrefixSuccessCount B hprefix_i
      have hcube_i :
          C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1 =
            selectorHistoryCubePrefix x u h i := by
        simpa using congrArg (fun f : Finset.Iic s → LatticePoint d ↦ f i) hcube
      have hresid_i :
          R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1 =
            selectorHistoryResidualPrefix u h i := by
        simpa using congrArg (fun f : Finset.Iic s → LatticePoint d ↦ f i) hresid
      have hx_i :
          historyRestrict h i ⟨0, Finset.mem_Iic.2 (Nat.zero_le i.1)⟩ = x := by
        simpa [historyRestrict] using hx
      have hsum_i :
          selectorHistoryCubePrefix x u h i + selectorHistoryResidualPrefix u h i = h i := by
        -- Proof comment: at each visible index, the reconstructed cube and residual currents add
        -- back up to the prescribed visible history value.
        simpa [selectorHistoryCubePrefix, selectorHistoryResidualPrefix] using
          selectorHistoryCurrent_sum x (selectorPrefixRestrict u i) (historyRestrict h i) hx_i
      -- Proof comment: the prefix equalities determine both hidden currents at time `i`, and
      -- their sum recovers the visible history coordinate `h i`.
      calc
        (let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0)
          C t ω.1 + R (i.1 - t) ω.2.1) =
            C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1 +
              R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1 := by
                simp [hcount_i]
        _ = selectorHistoryCubePrefix x u h i + selectorHistoryResidualPrefix u h i := by
              rw [hcube_i, hresid_i]
        _ = h i := hsum_i
    -- Proof comment: the hidden prefix reconstruction suffices to recover the whole visible
    -- history on the start slice.
    exact ⟨hhistory, hprefix, hC0, hR0⟩

/-- Helper for Theorem 18.8: on the full start slice and in the started-history branch
`h 0 = x`, fixing the visible history, selector prefix, branch bit, and next state is equivalent
to fixing the deterministic hidden cube/residual prefixes together with the active hidden
one-step target. -/
private lemma startedHistoryBranchAtom_on_start_iff_splitData
    {d : ℕ} {Ωcube Ωr Ωb : Type*}
    (B : ℕ → Ωb → Bool) (C : ℕ → Ωcube → LatticePoint d) (R : ℕ → Ωr → LatticePoint d)
    (x y : LatticePoint d) {s : ℕ}
    {u : Fin s → Bool} {h : Finset.Iic s → LatticePoint d} {b : Bool}
    {ω : Ωcube × (Ωr × Ωb)}
    (hx : h ⟨0, Finset.mem_Iic.2 (Nat.zero_le s)⟩ = x) :
    ((fun i : Finset.Iic s ↦
        let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0)
        C t ω.1 + R (i.1 - t) ω.2.1) = h ∧
      (fun i : Fin s ↦ B i ω.2.2) = u ∧
      B s ω.2.2 = b ∧
      (let t := Finset.sum (Finset.range (s + 1)) (fun j ↦ bif B j ω.2.2 then 1 else 0)
        C t ω.1 + R (s + 1 - t) ω.2.1) = y ∧
      C 0 ω.1 = x ∧
      R 0 ω.2.1 = 0) ↔
    ((fun i : Fin s ↦ B i ω.2.2) = u ∧
      B s ω.2.2 = b ∧
      (fun i : Finset.Iic s ↦
        C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1) =
          selectorHistoryCubePrefix x u h ∧
      (fun i : Finset.Iic s ↦
        R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1) =
          selectorHistoryResidualPrefix u h ∧
      (if b then
        C (selectorPrefixSuccessCount u + 1) ω.1 =
          y - selectorHistoryResidualCurrent u h
      else
        R (s - selectorPrefixSuccessCount u + 1) ω.2.1 =
          y - selectorHistoryCubeCurrent x u h) ∧
      C 0 ω.1 = x ∧
      R 0 ω.2.1 = 0) := by
  constructor
  · intro hω
    rcases hω with ⟨hhistory, hprefix, hbranch, hnext, hC0, hR0⟩
    rcases
      thinnedHiddenPrefixes_eq_selectorHistoryPrefixes
        (B := B) (C := C) (R := R) x hC0 hR0 hprefix hhistory
      with ⟨hcube, hresid⟩
    have hactive :
        if b then
          C (selectorPrefixSuccessCount u + 1) ω.1 =
            y - selectorHistoryResidualCurrent u h
        else
          R (s - selectorPrefixSuccessCount u + 1) ω.2.1 =
            y - selectorHistoryCubeCurrent x u h :=
      (thinnedNext_eq_iff_activeBranchTarget
        (B := B) (C := C) (R := R) x y hC0 hR0 hprefix hhistory hbranch).mp hnext
    -- Proof comment: once the visible branch data are fixed on the start slice, the hidden
    -- prefixes and the active one-step target are exactly the deterministic reconstructions.
    exact ⟨hprefix, hbranch, hcube, hresid, hactive, hC0, hR0⟩
  · intro hω
    rcases hω with ⟨hprefix, hbranch, hcube, hresid, hactive, hC0, hR0⟩
    have hhistory :
        (fun i : Finset.Iic s ↦
          let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0)
          C t ω.1 + R (i.1 - t) ω.2.1) = h := by
      funext i
      have hprefix_i : (fun j : Fin i.1 ↦ B j ω.2.2) = selectorPrefixRestrict u i := by
        funext j
        simpa [selectorPrefixRestrict] using
          congrArg
            (fun f : Fin s → Bool ↦ f ⟨j.1, Nat.lt_of_lt_of_le j.2 i.2⟩)
            hprefix
      have hcount_i :
          Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0) =
            selectorPrefixSuccessCount (selectorPrefixRestrict u i) :=
        selectorSuccessCount_eq_selectorPrefixSuccessCount B hprefix_i
      have hcube_i :
          C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1 =
            selectorHistoryCubePrefix x u h i := by
        simpa using congrArg (fun f : Finset.Iic s → LatticePoint d ↦ f i) hcube
      have hresid_i :
          R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1 =
            selectorHistoryResidualPrefix u h i := by
        simpa using congrArg (fun f : Finset.Iic s → LatticePoint d ↦ f i) hresid
      have hx_i :
          historyRestrict h i ⟨0, Finset.mem_Iic.2 (Nat.zero_le i.1)⟩ = x := by
        simpa [historyRestrict] using hx
      have hsum_i :
          selectorHistoryCubePrefix x u h i + selectorHistoryResidualPrefix u h i = h i := by
        -- Proof comment: at each visible time `i`, the reconstructed cube and residual currents
        -- still sum to the prescribed visible history value `h i`.
        simpa [selectorHistoryCubePrefix, selectorHistoryResidualPrefix] using
          selectorHistoryCurrent_sum x (selectorPrefixRestrict u i) (historyRestrict h i) hx_i
      -- Proof comment: the hidden prefix equalities pin down both hidden currents at time `i`,
      -- and their sum recovers the visible history coordinate.
      calc
        (let t := Finset.sum (Finset.range i.1) (fun j ↦ bif B j ω.2.2 then 1 else 0)
          C t ω.1 + R (i.1 - t) ω.2.1) =
            C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1 +
              R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1 := by
                simp [hcount_i]
        _ = selectorHistoryCubePrefix x u h i + selectorHistoryResidualPrefix u h i := by
              rw [hcube_i, hresid_i]
        _ = h i := hsum_i
    have hnext :
        (let t := Finset.sum (Finset.range (s + 1)) (fun j ↦ bif B j ω.2.2 then 1 else 0)
          C t ω.1 + R (s + 1 - t) ω.2.1) = y :=
      (thinnedNext_eq_iff_activeBranchTarget
        (B := B) (C := C) (R := R) x y hC0 hR0 hprefix hhistory hbranch).mpr hactive
    -- Proof comment: after reconstructing the whole visible history from the hidden prefix data,
    -- the active-target equivalence recovers the visible next-state atom.
    exact ⟨hhistory, hprefix, hbranch, hnext, hC0, hR0⟩

/-- Helper for Theorem 18.8: evaluating the owner row on the convex decomposition
`η.toMeasure = α • uniformCubeStepPMF d + (1 - α) • ρ.toMeasure` splits the singleton mass into
the corresponding convex combination. -/
private lemma ownerMixtureRow_apply_singleton
    {d : ℕ} (η ρ : PMF (LatticePoint d)) {α : ENNReal}
    (hη_decomp :
      η.toMeasure = α • (uniformCubeStepPMF d).toMeasure + (1 - α) • ρ.toMeasure)
    (x y : LatticePoint d) :
    dirac_convolution_kernel η.toMeasure x ({y} : Set (LatticePoint d)) =
      α * dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure x ({y} : Set (LatticePoint d)) +
        (1 - α) * dirac_convolution_kernel ρ.toMeasure x ({y} : Set (LatticePoint d)) := by
  have hconv :
      Measure.dirac x ∗ η.toMeasure =
        α • (Measure.dirac x ∗ (uniformCubeStepPMF d).toMeasure) +
          (1 - α) • (Measure.dirac x ∗ ρ.toMeasure) := by
    -- Proof comment: convolution with the fixed starting Dirac mass is additive and homogeneous
    -- in the increment law.
    rw [hη_decomp, Measure.conv_add, Measure.conv_smul_right, Measure.conv_smul_right]
  -- Proof comment: evaluate the decomposed convolution row on the singleton `{y}`.
  simpa [dirac_convolution_kernel_apply, Measure.smul_apply, smul_eq_mul]
    using congrArg (fun μ : Measure (LatticePoint d) ↦ μ ({y} : Set (LatticePoint d))) hconv

/-- Helper for Theorem 18.8: translating the start state of a convolution row by a fixed lattice
point is equivalent to translating the singleton target by the opposite displacement. -/
private lemma diracConvolutionKernel_apply_singleton_sub_right
    {d : ℕ} (μ : Measure (LatticePoint d))
    (x r y : LatticePoint d) :
    dirac_convolution_kernel μ x ({y - r} : Set (LatticePoint d)) =
      dirac_convolution_kernel μ (x + r) ({y} : Set (LatticePoint d)) := by
  -- Proof comment: both singleton rows are the same translated increment event under addition by
  -- the fixed displacement `r`.
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (y - r))]
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
  have hpreimage :
      (fun z : LatticePoint d ↦ x + z) ⁻¹' ({y - r} : Set (LatticePoint d)) =
        (fun z : LatticePoint d ↦ (x + r) + z) ⁻¹' ({y} : Set (LatticePoint d)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      calc
        (x + r) + z = r + (x + z) := by abel
        _ = r + (y - r) := by rw [hz]
        _ = y := by abel
    · intro hz
      calc
        x + z = (x + r + z) - r := by abel
        _ = y - r := by rw [hz]
  exact congrArg (fun s : Set (LatticePoint d) ↦ μ s) hpreimage

/-- Helper for Theorem 18.8: after reconstructing the hidden cube and residual currents from the
visible history, the two branch rows in the Bernoulli mixture collapse back to the owner row at
the visible current state. -/
private lemma ownerMixtureRow_apply_singleton_of_selectorHistory
    {d : ℕ} (η ρ : PMF (LatticePoint d)) {α : ENNReal}
    (hη_decomp :
      η.toMeasure = α • (uniformCubeStepPMF d).toMeasure + (1 - α) • ρ.toMeasure)
    (x y : LatticePoint d) {s : ℕ}
    (u : Fin s → Bool) (h : Finset.Iic s → LatticePoint d)
    (hx : h ⟨0, Finset.mem_Iic.2 (Nat.zero_le s)⟩ = x) :
    α *
        dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure
          (selectorHistoryCubeCurrent x u h)
          ({y - selectorHistoryResidualCurrent u h} : Set (LatticePoint d)) +
      (1 - α) *
        dirac_convolution_kernel ρ.toMeasure
          (selectorHistoryResidualCurrent u h)
          ({y - selectorHistoryCubeCurrent x u h} : Set (LatticePoint d)) =
      dirac_convolution_kernel η.toMeasure
        (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) ({y} : Set (LatticePoint d)) := by
  have hcurrent :
      selectorHistoryCubeCurrent x u h + selectorHistoryResidualCurrent u h =
        h ⟨s, Finset.mem_Iic.2 le_rfl⟩ :=
    selectorHistoryCurrent_sum x u h hx
  -- Proof comment: first rewrite each branch row to the common visible current, then apply the
  -- owner-level convex-combination formula at that current state.
  calc
    α *
        dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure
          (selectorHistoryCubeCurrent x u h)
          ({y - selectorHistoryResidualCurrent u h} : Set (LatticePoint d)) +
      (1 - α) *
        dirac_convolution_kernel ρ.toMeasure
          (selectorHistoryResidualCurrent u h)
          ({y - selectorHistoryCubeCurrent x u h} : Set (LatticePoint d)) =
      α *
          dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure
            (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) ({y} : Set (LatticePoint d)) +
        (1 - α) *
          dirac_convolution_kernel ρ.toMeasure
            (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) ({y} : Set (LatticePoint d)) := by
          rw [← hcurrent]
          rw [diracConvolutionKernel_apply_singleton_sub_right
            (μ := (uniformCubeStepPMF d).toMeasure)
            (x := selectorHistoryCubeCurrent x u h)
            (r := selectorHistoryResidualCurrent u h)
            (y := y)]
          rw [add_comm (selectorHistoryResidualCurrent u h) (selectorHistoryCubeCurrent x u h)]
          rw [diracConvolutionKernel_apply_singleton_sub_right
            (μ := ρ.toMeasure)
            (x := selectorHistoryResidualCurrent u h)
            (r := selectorHistoryCubeCurrent x u h)
            (y := y)]
    _ =
      dirac_convolution_kernel η.toMeasure
        (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) ({y} : Set (LatticePoint d)) := by
          symm
          exact
            ownerMixtureRow_apply_singleton
              (η := η) (ρ := ρ) (hη_decomp := hη_decomp)
              (x := h ⟨s, Finset.mem_Iic.2 le_rfl⟩) (y := y)

/-- Helper for Theorem 18.8: on countable discrete target spaces, a joint law is determined by
the singleton masses of the history/next-state pair, so singleton factorizations lift to a
`compProd` identity. -/
private lemma compProd_eq_of_pairSingletonMass
    {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
    [MeasurableSpace β] [DiscreteMeasurableSpace β] [Countable β]
    (μ : Measure Ω) (H : Ω → α) (next : Ω → β) (κ : Kernel α β)
    (hsingleton :
      ∀ h y,
        μ.map (fun ω ↦ (H ω, next ω)) ({(h, y)} : Set (α × β)) =
          μ.map H ({h} : Set α) * κ h ({y} : Set β)) :
    μ.map (fun ω ↦ (H ω, next ω)) = (μ.map H) ⊗ₘ κ := by
  refine Measure.ext_of_singleton fun z ↦ ?_
  rcases z with ⟨h, y⟩
  have hrect :
      ({(h, y)} : Set (α × β)) = ({h} : Set α) ×ˢ ({y} : Set β) := by
    ext z'
    simp
  -- Proof comment: after rewriting the singleton pair as a singleton rectangle, the assumed
  -- singleton factorization is exactly the `compProd` rectangle mass.
  rw [hsingleton, hrect]
  simpa using
    (Measure.compProd_apply_prod
      (μ := μ.map H) (κ := κ)
      (measurableSet_singleton h) (measurableSet_singleton y))

/-- Helper for Theorem 18.8: once a history/next-state pair map factors on singleton atoms,
the corresponding conditional expectation is the kernel evaluated at the visible history. -/
private theorem condExp_eq_kernel_of_pairSingletonMass
    {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
    [MeasurableSpace β] [DiscreteMeasurableSpace β] [Countable β]
    (μ : Measure Ω) (H : Ω → α) (next : Ω → β) (κ : Kernel α β)
    (hH_meas : Measurable H) (hnext_meas : Measurable next)
    (hsingleton :
      ∀ h y,
        μ.map (fun ω ↦ (H ω, next ω)) ({(h, y)} : Set (α × β)) =
          μ.map H ({h} : Set α) * κ h ({y} : Set β))
    {A : Set β} (hA : MeasurableSet A) :
    μ⟦next ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ]
      fun ω ↦ (κ (H ω)).real A := by
  have hpair :
      μ.map (fun ω ↦ (H ω, next ω)) = (μ.map H) ⊗ₘ κ := by
    -- Proof comment: on discrete countable target spaces, singleton masses determine the whole
    -- joint law of the history/next-state pair.
    exact compProd_eq_of_pairSingletonMass μ H next κ hsingleton
  have hcond :
      condDistrib next H μ =ᵐ[μ.map H] κ := by
    -- Proof comment: the `compProd` description turns the conditional law into the prescribed
    -- kernel.
    exact
      condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hH_meas hnext_meas hpair
  have hcondexp :
      μ⟦next ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ]
        fun ω ↦ (condDistrib next H μ (H ω)).real A := by
    -- Proof comment: `condDistrib` is the concrete version of the conditional expectation of the
    -- next-step event along the visible history.
    simpa using
      (condDistrib_ae_eq_condExp (μ := μ) (X := H) (Y := next)
        hH_meas hnext_meas hA).symm
  have hcond_comp :
      (fun ω ↦ (condDistrib next H μ (H ω)).real A) =ᵐ[μ]
        fun ω ↦ (κ (H ω)).real A := by
    -- Proof comment: compose the almost-everywhere equality of kernels with the history map.
    filter_upwards [ae_eq_comp hH_meas.aemeasurable hcond] with ω hω
    simpa [Function.comp] using congrArg (fun ν : Measure β ↦ ν.real A) hω
  exact hcondexp.trans hcond_comp

/-- Helper for Theorem 18.8: the filtration generated by a process up to time `s` is exactly the
pullback sigma-algebra of its finite history tuple on `Finset.Iic s`. -/
private lemma generatedFiltrationSpace_eq_comap_historyIic
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (X : ℕ → Ω → E) (s : ℕ) :
    generatedFiltrationSpace X s =
      MeasurableSpace.comap (fun ω (i : Finset.Iic s) ↦ X i.1 ω) inferInstance := by
  let H : Ω → Finset.Iic s → E := fun ω i ↦ X i.1 ω
  refine le_antisymm ?_ ?_
  · rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let i : Finset.Iic s := ⟨t, Finset.mem_Iic.2 ht⟩
    have hCoord :
        Measurable[MeasurableSpace.comap H inferInstance] (X t) := by
      simpa [H, i] using
        (measurable_pi_apply i).comp (comap_measurable H)
    exact hCoord.comap_le
  · have hHistory :
        Measurable[generatedFiltrationSpace X s] H := by
      rw [@measurable_pi_iff]
      intro i
      exact le_iSup_of_le i.1 <| le_iSup_of_le (Finset.mem_Iic.1 i.2) le_rfl
    simpa [H] using hHistory.comap_le

/-- Helper for Theorem 18.8: every discrete-state Markov realization satisfies the usual
history/next-step singleton factorization. -/
private theorem pairSingleton_eq_historyMass_mul_step_of_markovRealization
    {E Ω : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [MeasurableSpace Ω]
    {q : E → E → ENNReal}
    {P : E → ProbabilityMeasure Ω}
    {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X]
    (x : E) (s : ℕ) (h : Finset.Iic s → E) (w : E) :
    let μ : Measure Ω := (P x : Measure Ω)
    let H : Ω → Finset.Iic s → E := fun ω i ↦ X i.1 ω
    let next : Ω → E := fun ω ↦ X (s + 1) ω
    μ.map (fun ω ↦ (H ω, next ω)) ({(h, w)} : Set ((Finset.Iic s → E) × E)) =
      μ.map H ({h} : Set (Finset.Iic s → E)) *
        discreteMatrixKernel q (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) ({w} : Set E) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let H : Ω → Finset.Iic s → E := fun ω i ↦ X i.1 ω
  let next : Ω → E := fun ω ↦ X (s + 1) ω
  let histEvent : Set Ω := {ω | H ω = h}
  have hH_meas : Measurable H := by
    -- Proof comment: the finite history tuple is measurable because the target is discrete.
    exact Measurable.of_discrete
  have hhist_meas : MeasurableSet histEvent := by
    -- Proof comment: the singleton history atom is the preimage of a singleton under `H`.
    exact hH_meas (measurableSet_singleton h)
  have hhist_filtration :
      MeasurableSet[generatedFiltrationSpace X s] histEvent := by
    -- Proof comment: the whole history atom is already visible in the time-`s` history
    -- filtration after rewriting that filtration as the pullback of the history tuple.
    rw [generatedFiltrationSpace_eq_comap_historyIic (X := X) s]
    simpa [H, histEvent] using
      (comap_measurable H) (measurableSet_singleton h)
  have hhist_state :
      ∀ ⦃ω : Ω⦄, ω ∈ histEvent → X s ω = h ⟨s, Finset.mem_Iic.2 le_rfl⟩ := by
    intro ω hω
    have hHω : H ω = h := by
      simpa [histEvent] using hω
    simpa [H] using
      congrArg (fun f : Finset.Iic s → E ↦ f ⟨s, Finset.mem_Iic.2 le_rfl⟩) hHω
  have hpair_preimage :
      (fun ω ↦ (H ω, next ω)) ⁻¹' ({(h, w)} : Set ((Finset.Iic s → E) × E)) =
        histEvent ∩ {ω | next ω = w} := by
    ext ω
    simp [histEvent, H, next]
  have hstep :=
    measureInter_eq_mul_stepMass_of_stateEvent
      (q := q) (P := P) (X := X)
      (x := x) (y := h ⟨s, Finset.mem_Iic.2 le_rfl⟩) (w := w)
      (n := s) (A := histEvent) hhist_meas hhist_filtration hhist_state
  calc
    μ.map (fun ω ↦ (H ω, next ω)) ({(h, w)} : Set ((Finset.Iic s → E) × E)) =
        μ (histEvent ∩ {ω | next ω = w}) := by
          rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (h, w))]
          exact congrArg (fun t : Set Ω ↦ μ t) hpair_preimage
    _ =
        discreteMatrixKernel q (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) ({w} : Set E) *
          μ histEvent := by
          simpa [μ, next] using hstep
    _ =
        μ.map H ({h} : Set (Finset.Iic s → E)) *
          discreteMatrixKernel q (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) ({w} : Set E) := by
          rw [Measure.map_apply hH_meas (measurableSet_singleton h)]
          simp [histEvent, mul_comm]

/-- Helper for Theorem 18.8: once the selector clock has reached `K` by time `n`, every later
thinned disagreement must already come from a disagreement of the cube coupling at a selector time
at least `K`. -/
private lemma thinnedTailEvent_subset_clockOrCubeTail
    {Ω E : Type*} [AddRightCancelSemigroup E]
    (S : ℕ → Ω → ℕ) (X Y : ℕ → Ω → E) (R : ℕ → Ω → E)
    (hS_mono : ∀ ω, Monotone fun n ↦ S n ω) (n K : ℕ) :
    (⋃ m ≥ n, {ω | X (S m ω) ω + R (m - S m ω) ω ≠
        Y (S m ω) ω + R (m - S m ω) ω}) ⊆
      {ω | S n ω < K} ∪ ⋃ j ≥ K, {ω | X j ω ≠ Y j ω} := by
  intro ω hω
  by_cases hclock : S n ω < K
  · -- Proof comment: if the selector clock is still below `K` at time `n`, we are already in the
    -- lower-tail branch of the union bound.
    exact Or.inl hclock
  · -- Proof comment: otherwise every later selector time is at least `K`, so any future thinned
    -- disagreement must come from a genuine cube-coupling disagreement at that selector time.
    rcases Set.mem_iUnion.1 hω with ⟨m, hm⟩
    rcases Set.mem_iUnion.1 hm with ⟨hnm, hneq⟩
    have hselector_ge :
        K ≤ S m ω := by
      exact le_trans (Nat.not_lt.1 hclock) ((hS_mono ω) hnm)
    have hcube_neq : X (S m ω) ω ≠ Y (S m ω) ω := by
      intro hxy
      exact hneq (by simpa [hxy])
    exact Or.inr <|
      Set.mem_iUnion.2 ⟨S m ω, Set.mem_iUnion.2 ⟨hselector_ge, hcube_neq⟩⟩

/-- Helper for Theorem 18.8: taking measures of the deterministic thinning containment gives the
key Step 2 probability estimate. -/
private lemma thinnedTailEvent_measure_le_clock_plus_cubeTail
    {Ω E : Type*} [MeasurableSpace Ω] [AddRightCancelSemigroup E]
    (μ : Measure Ω) (S : ℕ → Ω → ℕ) (X Y : ℕ → Ω → E) (R : ℕ → Ω → E)
    (hS_mono : ∀ ω, Monotone fun n ↦ S n ω) (n K : ℕ) :
    μ (⋃ m ≥ n, {ω | X (S m ω) ω + R (m - S m ω) ω ≠
        Y (S m ω) ω + R (m - S m ω) ω})
      ≤ μ ({ω | S n ω < K}) + μ (⋃ j ≥ K, {ω | X j ω ≠ Y j ω}) := by
  -- Proof comment: the first term is a direct `measure_mono` consequence of the containment
  -- lemma, and the second step is the standard union bound.
  calc
    μ (⋃ m ≥ n, {ω | X (S m ω) ω + R (m - S m ω) ω ≠
        Y (S m ω) ω + R (m - S m ω) ω})
      ≤ μ ({ω | S n ω < K} ∪ ⋃ j ≥ K, {ω | X j ω ≠ Y j ω}) := by
          exact measure_mono <|
            thinnedTailEvent_subset_clockOrCubeTail
              (S := S) (X := X) (Y := Y) (R := R) hS_mono n K
    _ ≤ μ ({ω | S n ω < K}) + μ (⋃ j ≥ K, {ω | X j ω ≠ Y j ω}) := by
          exact measure_union_le _ _

/-- Helper for Theorem 18.8: once the selector clock eventually escapes every fixed lower tail
and the original cube-coupling tail probabilities tend to zero, the corresponding thinned tail
disagreement probabilities also tend to zero. -/
private lemma thinnedTailDisagreement_tendsto_zero_of_clock_and_cube
    {Ω E : Type*} [MeasurableSpace Ω] [AddRightCancelSemigroup E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : ℕ → Ω → ℕ) (X Y : ℕ → Ω → E) (R : ℕ → Ω → E)
    (hS_mono : ∀ ω, Monotone fun n ↦ S n ω)
    (hclock :
      ∀ K : ℕ, Tendsto (fun n ↦ μ ({ω | S n ω < K})) atTop (nhds 0))
    (hcube :
      Tendsto (fun K ↦ μ (⋃ j ≥ K, {ω | X j ω ≠ Y j ω})) atTop (nhds 0)) :
    Tendsto
      (fun n ↦
        μ (⋃ m ≥ n, {ω | X (S m ω) ω + R (m - S m ω) ω ≠
          Y (S m ω) ω + R (m - S m ω) ω}))
      atTop (nhds 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact (ENNReal.not_lt_zero ha).elim
  · intro ε hε
    by_cases hε_top : ε = ∞
    · -- Proof comment: every measure value is finite, so the target upper bound is automatic when
      -- the neighborhood is cut out by `∞`.
      refine Filter.Eventually.of_forall fun n ↦ ?_
      simpa [hε_top] using measure_lt_top μ
        (⋃ m ≥ n, {ω | X (S m ω) ω + R (m - S m ω) ω ≠ Y (S m ω) ω + R (m - S m ω) ω})
    · have hhalf_pos : 0 < ε / 2 := ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top
      have hcube_small :
          ∀ᶠ K : ℕ in atTop, μ (⋃ j ≥ K, {ω | X j ω ≠ Y j ω}) < ε / 2 := by
        exact hcube (Iio_mem_nhds hhalf_pos)
      rcases Filter.eventually_atTop.1 hcube_small with ⟨K, hK⟩
      have hclock_small :
          ∀ᶠ n : ℕ in atTop, μ ({ω | S n ω < K}) < ε / 2 := by
        exact hclock K (Iio_mem_nhds hhalf_pos)
      filter_upwards [hclock_small] with n hn
      have htail_le :=
        thinnedTailEvent_measure_le_clock_plus_cubeTail
          (μ := μ) (S := S) (X := X) (Y := Y) (R := R) hS_mono n K
      have hcubeK : μ (⋃ j ≥ K, {ω | X j ω ≠ Y j ω}) < ε / 2 := hK K le_rfl
      exact lt_of_le_of_lt htail_le <|
        (ENNReal.add_lt_add hn hcubeK).trans_eq (ENNReal.add_halves ε)

/-- Helper for Theorem 18.8: under a product with a probability measure on the second factor,
events depending only on the first factor keep their original mass. -/
private lemma prodMeasure_preimage_fst_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : ProbabilityMeasure β) {A : Set α} (hA : MeasurableSet A) :
    (μ.prod (ν : Measure β)) (Prod.fst ⁻¹' A) = μ A := by
  have hpreimage : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set β) := by
    ext z
    simp
  rw [hpreimage, Measure.prod_apply (hA.prod MeasurableSet.univ)]
  rw [measure_univ, mul_one]

/-- Helper for Theorem 18.8: under a product with a probability measure on the first factor,
events depending only on the second factor keep their original mass. -/
private lemma prodMeasure_preimage_snd_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) {A : Set β} (hA : MeasurableSet A) :
    ((μ : Measure α).prod (ν : Measure β)) (Prod.snd ⁻¹' A) = (ν : Measure β) A := by
  have hpreimage : Prod.snd ⁻¹' A = (Set.univ : Set α) ×ˢ A := by
    ext z
    simp
  rw [hpreimage, Measure.prod_apply (MeasurableSet.univ.prod hA)]
  rw [measure_univ, one_mul]

/-- Helper for Theorem 18.8: on the nested product witness space
`Ωcube × (Ωr × Ωb)`, events depending only on the selector factor `Ωb` have the same mass as
under the selector law itself. -/
private lemma prodMeasure_preimage_snd_snd_eq
    {Ωcube Ωr Ωb : Type*}
    [MeasurableSpace Ωcube] [MeasurableSpace Ωr] [MeasurableSpace Ωb]
    (μcube : ProbabilityMeasure Ωcube) (μr : ProbabilityMeasure Ωr) (μβ : ProbabilityMeasure Ωb)
    {A : Set Ωb} (hA : MeasurableSet A) :
    ((μcube : Measure Ωcube).prod ((μr : Measure Ωr).prod μβ))
        ((fun ω : Ωcube × (Ωr × Ωb) ↦ ω.2.2) ⁻¹' A) =
      (μβ : Measure Ωb) A := by
  have hpreimage :
      (fun ω : Ωcube × (Ωr × Ωb) ↦ ω.2.2) ⁻¹' A =
        Prod.snd ⁻¹' (Prod.snd ⁻¹' A) := by
    rfl
  rw [hpreimage]
  rw [prodMeasure_preimage_snd_eq (μ := μcube)
    (ν := μr.prod μβ) (hA := measurable_snd hA)]
  exact prodMeasure_preimage_snd_eq (μ := μr) (ν := μβ) hA

/-- Helper for Theorem 18.8: in an i.i.d. family, the law at time `0` transports to every time
index. -/
private lemma iidCoordinate_hasLaw_zero
    {ι Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ι → Ω → α} (hX_iid : IsIID X μ) {ν : Measure α} (hX0_law : HasLaw (X 0) ν μ)
    [Zero ι] (i : ι) :
    HasLaw (X i) ν μ := by
  -- Proof comment: identical distribution in the i.i.d. family transfers the reference law at
  -- index `0` to the requested coordinate.
  simpa using (hX_iid.identDistrib 0 i).hasLaw hX0_law

/-- Helper for Theorem 18.8: the selector prefix before time `s` is independent of the fresh
selector bit at time `s`. -/
private theorem selectorPrefixTuple_indep_selector
    {Ωb : Type*} [MeasurableSpace Ωb]
    (Qb : ProbabilityMeasure Ωb) (B : ℕ → Ωb → Bool)
    (hB_meas : ∀ n, Measurable (B n))
    (hB_iid : IsIID B (Qb : Measure Ωb)) (s : ℕ) :
    IndepFun (fun ω ↦ fun i : Fin s ↦ B i ω) (B s) (Qb : Measure Ωb) := by
  let prefixIdx : Finset ℕ := Finset.range s
  let prefixCoord : Ωb → prefixIdx → Bool := fun ω i ↦ B i ω
  let prefixToTuple : (prefixIdx → Bool) → Fin s → Bool := fun z i ↦
    z ⟨(i : ℕ), by
      simp [prefixIdx, i.2]⟩
  let singletonEval : (({s} : Finset ℕ) → Bool) → Bool := fun z ↦
    z ⟨s, Finset.mem_singleton_self s⟩
  have hPrefixToTuple : Measurable prefixToTuple := by
    -- Proof comment: the `range s` selector block is reindexed to `Fin s` by coordinatewise
    -- evaluation.
    refine measurable_pi_lambda _ fun i ↦ ?_
    let idx : prefixIdx := ⟨(i : ℕ), by
      simp [prefixIdx, i.2]⟩
    simpa [prefixToTuple, idx] using
      (measurable_pi_apply idx : Measurable fun z : prefixIdx → Bool ↦ z idx)
  have hSingletonEval : Measurable singletonEval := by
    -- Proof comment: the singleton future block is evaluation at the unique fresh time `s`.
    let idx : ({s} : Finset ℕ) := ⟨s, Finset.mem_singleton_self s⟩
    simpa [singletonEval, idx] using
      (measurable_pi_apply idx : Measurable fun z : ({s} : Finset ℕ) → Bool ↦ z idx)
  have hdisj : Disjoint prefixIdx ({s} : Finset ℕ) := by
    -- Proof comment: the fresh time `s` does not belong to the prefix block `range s`.
    simpa [prefixIdx] using
      (Finset.disjoint_singleton_right.mpr
        (Finset.notMem_range_self : s ∉ Finset.range s))
  have hRaw :
      IndepFun prefixCoord (fun ω ↦ fun i : ({s} : Finset ℕ) ↦ B i ω) (Qb : Measure Ωb) := by
    -- Proof comment: independence of disjoint coordinate blocks is exactly
    -- `iIndepFun.indepFun_finset`.
    simpa [prefixCoord] using hB_iid.iIndepFun.indepFun_finset prefixIdx {s} hdisj hB_meas
  have hTuple :
      IndepFun (prefixToTuple ∘ prefixCoord)
        (singletonEval ∘ fun ω ↦ fun i : ({s} : Finset ℕ) ↦ B i ω)
        (Qb : Measure Ωb) := by
    -- Proof comment: compose the raw block independence with the deterministic reindexing maps.
    exact hRaw.comp hPrefixToTuple hSingletonEval
  simpa [Function.comp, prefixToTuple, prefixCoord, singletonEval] using hTuple

/-- Helper for Theorem 18.8: the mass of a selector-prefix singleton together with the fresh
branch bit factors as the product of the prefix mass and the one-bit Bernoulli mass. -/
private theorem selectorPrefix_singleton_branchMass
    {Ωb : Type*} [MeasurableSpace Ωb]
    (Qb : ProbabilityMeasure Ωb) (B : ℕ → Ωb → Bool)
    (hB_meas : ∀ n, Measurable (B n))
    (hB_iid : IsIID B (Qb : Measure Ωb))
    (s : ℕ) (u : Fin s → Bool) (b : Bool) :
    (Qb : Measure Ωb) {ω | (fun i : Fin s ↦ B i ω) = u ∧ B s ω = b} =
      ((Qb : Measure Ωb).map (fun ω ↦ fun i : Fin s ↦ B i ω)) ({u} : Set (Fin s → Bool)) *
        ((Qb : Measure Ωb).map (B s)) ({b} : Set Bool) := by
  let prefix : Ωb → Fin s → Bool := fun ω i ↦ B i ω
  have hprefix_meas : Measurable prefix := by
    -- Proof comment: the prefix tuple is measurable because every coordinate `B i` is measurable.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact hB_meas i
  have hIndep :
      IndepFun prefix (B s) (Qb : Measure Ωb) :=
    selectorPrefixTuple_indep_selector Qb B hB_meas hB_iid s
  have hpair :
      Measure.map (fun ω ↦ (prefix ω, B s ω)) (Qb : Measure Ωb) =
        (Measure.map prefix (Qb : Measure Ωb)).prod (Measure.map (B s) (Qb : Measure Ωb)) := by
    -- Proof comment: independence is converted to the product law for the pair map.
    exact
      (indepFun_iff_map_prod_eq_prod_map_map
        (μ := (Qb : Measure Ωb))
        (f := prefix) (g := B s)
        hprefix_meas.aemeasurable (hB_meas s).aemeasurable).mp hIndep
  have hpreimage :
      {ω | prefix ω = u ∧ B s ω = b} =
        (fun ω ↦ (prefix ω, B s ω)) ⁻¹'
          (({u} : Set (Fin s → Bool)) ×ˢ ({b} : Set Bool)) := by
    -- Proof comment: the conjunction event is exactly the rectangle singleton for the pair map.
    ext ω
    simp [prefix]
  calc
    (Qb : Measure Ωb) {ω | prefix ω = u ∧ B s ω = b} =
        Measure.map (fun ω ↦ (prefix ω, B s ω)) (Qb : Measure Ωb)
          (({u} : Set (Fin s → Bool)) ×ˢ ({b} : Set Bool)) := by
            rw [Measure.map_apply (hprefix_meas.prodMk (hB_meas s))
              ((measurableSet_singleton u).prod (measurableSet_singleton b))]
            exact congrArg (fun t : Set Ωb ↦ (Qb : Measure Ωb) t) hpreimage
    _ = ((Measure.map prefix (Qb : Measure Ωb)).prod (Measure.map (B s) (Qb : Measure Ωb)))
          (({u} : Set (Fin s → Bool)) ×ˢ ({b} : Set Bool)) := by
            rw [hpair]
    _ = ((Qb : Measure Ωb).map prefix) ({u} : Set (Fin s → Bool)) *
          ((Qb : Measure Ωb).map (B s)) ({b} : Set Bool) := by
            rw [Measure.prod_apply ((measurableSet_singleton u).prod (measurableSet_singleton b))]

/-- Helper for Theorem 18.8: the selector-prefix/branch singleton event has the same mass on the
nested product witness space as on the selector factor, so the selector-only factorization lifts
directly to the full witness measure. -/
private theorem prodMeasure_selectorPrefixBranchMass
    {Ωcube Ωr Ωb : Type*}
    [MeasurableSpace Ωcube] [MeasurableSpace Ωr] [MeasurableSpace Ωb]
    (μcube : ProbabilityMeasure Ωcube) (μr : ProbabilityMeasure Ωr) (Qb : ProbabilityMeasure Ωb)
    (B : ℕ → Ωb → Bool) (hB_meas : ∀ n, Measurable (B n))
    (hB_iid : IsIID B (Qb : Measure Ωb))
    (s : ℕ) (u : Fin s → Bool) (b : Bool) :
    ((μcube : Measure Ωcube).prod ((μr : Measure Ωr).prod Qb))
        {ω : Ωcube × (Ωr × Ωb) | (fun i : Fin s ↦ B i ω.2.2) = u ∧ B s ω.2.2 = b} =
      ((Qb : Measure Ωb).map (fun ωb ↦ fun i : Fin s ↦ B i ωb)) ({u} : Set (Fin s → Bool)) *
        ((Qb : Measure Ωb).map (B s)) ({b} : Set Bool) := by
  have hpreimage :
      {ω : Ωcube × (Ωr × Ωb) | (fun i : Fin s ↦ B i ω.2.2) = u ∧ B s ω.2.2 = b} =
        (fun ω : Ωcube × (Ωr × Ωb) ↦ ω.2.2) ⁻¹'
          {ωb : Ωb | (fun i : Fin s ↦ B i ωb) = u ∧ B s ωb = b} := by
    -- Proof comment: the event only depends on the selector coordinate of the nested product.
    ext ω
    simp
  rw [hpreimage]
  rw [prodMeasure_preimage_snd_snd_eq (μcube := μcube) (μr := μr) (μβ := Qb)]
  · exact selectorPrefix_singleton_branchMass Qb B hB_meas hB_iid s u b
  · exact (measurable_pi_lambda _ fun i ↦ hB_meas i) (measurableSet_singleton u) |>.inter
      ((hB_meas s) (measurableSet_singleton b))

/-- Helper for Theorem 18.8: on a fixed selector word, the Step 2 started-history split-data
fiber is a genuine product event on the cube, residual, and selector coordinates. -/
private theorem startedHistorySplitFiber_mass
    {d : ℕ} {Ωcube Ωr Ωb : Type*}
    [MeasurableSpace Ωcube] [MeasurableSpace Ωr] [MeasurableSpace Ωb]
    (μcube : ProbabilityMeasure Ωcube) (μr : ProbabilityMeasure Ωr) (Qb : ProbabilityMeasure Ωb)
    (B : ℕ → Ωb → Bool) (C : ℕ → Ωcube → LatticePoint d) (R : ℕ → Ωr → LatticePoint d)
    (x : LatticePoint d) {s : ℕ} (u : Fin s → Bool) (h : Finset.Iic s → LatticePoint d) :
    let cubeEvent : Set Ωcube := {ωc |
      (fun i : Finset.Iic s ↦
        C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωc) =
          selectorHistoryCubePrefix x u h ∧
        C 0 ωc = x}
    let residualEvent : Set Ωr := {ωr |
      (fun i : Finset.Iic s ↦
        R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωr) =
          selectorHistoryResidualPrefix u h ∧
        R 0 ωr = 0}
    let selectorEvent : Set Ωb := {ωb | (fun i : Fin s ↦ B i ωb) = u}
    ((μcube : Measure Ωcube).prod ((μr : Measure Ωr).prod Qb))
        {ω : Ωcube × (Ωr × Ωb) |
          (fun i : Fin s ↦ B i ω.2.2) = u ∧
          (fun i : Finset.Iic s ↦
            C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1) =
              selectorHistoryCubePrefix x u h ∧
          (fun i : Finset.Iic s ↦
            R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1) =
              selectorHistoryResidualPrefix u h ∧
          C 0 ω.1 = x ∧
          R 0 ω.2.1 = 0} =
      ((μcube : Measure Ωcube) cubeEvent) *
        (((μr : Measure Ωr) residualEvent) * (Qb : Measure Ωb) selectorEvent) := by
  let cubeEvent : Set Ωcube := {ωc |
    (fun i : Finset.Iic s ↦
      C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωc) =
        selectorHistoryCubePrefix x u h ∧
      C 0 ωc = x}
  let residualEvent : Set Ωr := {ωr |
    (fun i : Finset.Iic s ↦
      R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωr) =
        selectorHistoryResidualPrefix u h ∧
      R 0 ωr = 0}
  let selectorEvent : Set Ωb := {ωb | (fun i : Fin s ↦ B i ωb) = u}
  have hcubeEvent_meas : MeasurableSet cubeEvent := by
    have hmap : Measurable
        (fun ωc : Ωcube ↦
          ((fun i : Finset.Iic s ↦
            C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωc), C 0 ωc)) := by
      exact Measurable.of_discrete
    -- Proof comment: the cube-side split data land in a discrete finite history space, so their
    -- singleton fiber is measurable.
    simpa [cubeEvent] using
      hmap (measurableSet_singleton (selectorHistoryCubePrefix x u h, x))
  have hresidualEvent_meas : MeasurableSet residualEvent := by
    have hmap : Measurable
        (fun ωr : Ωr ↦
          ((fun i : Finset.Iic s ↦
            R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωr),
            R 0 ωr)) := by
      exact Measurable.of_discrete
    -- Proof comment: the residual-side split data are measured in the same discrete function
    -- space, so the corresponding singleton fiber is measurable.
    simpa [residualEvent] using
      hmap (measurableSet_singleton (selectorHistoryResidualPrefix u h, (0 : LatticePoint d)))
  have hselectorEvent_meas : MeasurableSet selectorEvent := by
    have hmap : Measurable (fun ωb : Ωb ↦ fun i : Fin s ↦ B i ωb) := by
      exact Measurable.of_discrete
    -- Proof comment: the selector word is a finite Boolean tuple, so its singleton fiber is
    -- measurable on the selector coordinate.
    simpa [selectorEvent] using hmap (measurableSet_singleton u)
  have hset :
      {ω : Ωcube × (Ωr × Ωb) |
          (fun i : Fin s ↦ B i ω.2.2) = u ∧
          (fun i : Finset.Iic s ↦
            C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1) =
              selectorHistoryCubePrefix x u h ∧
          (fun i : Finset.Iic s ↦
            R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1) =
              selectorHistoryResidualPrefix u h ∧
          C 0 ω.1 = x ∧
          R 0 ω.2.1 = 0} =
        cubeEvent ×ˢ (residualEvent ×ˢ selectorEvent) := by
    ext ω
    rcases ω with ⟨ωc, ωrb⟩
    rcases ωrb with ⟨ωr, ωb⟩
    simp [cubeEvent, residualEvent, selectorEvent, and_assoc, and_left_comm, and_comm]
  -- Proof comment: once the split data are written as a literal product rectangle, the nested
  -- product measure evaluates it by two successive `Measure.prod_apply` calls.
  rw [hset, Measure.prod_apply (hcubeEvent_meas.prod (hresidualEvent_meas.prod hselectorEvent_meas))]
  rw [Measure.prod_apply (hresidualEvent_meas.prod hselectorEvent_meas)]

/-- Helper for Theorem 18.8: on the `true` selector branch, the Step 2 history/next split-data
fiber factors into the active cube history/next fiber, the passive residual fiber, and the
selector prefix/branch fiber. -/
private theorem startedHistoryTrueBranchSplitFiber_mass
    {d : ℕ} {Ωcube Ωr Ωb : Type*}
    [MeasurableSpace Ωcube] [MeasurableSpace Ωr] [MeasurableSpace Ωb]
    (μcube : ProbabilityMeasure Ωcube) (μr : ProbabilityMeasure Ωr) (Qb : ProbabilityMeasure Ωb)
    (B : ℕ → Ωb → Bool) (C : ℕ → Ωcube → LatticePoint d) (R : ℕ → Ωr → LatticePoint d)
    (x y : LatticePoint d) {s : ℕ} (u : Fin s → Bool) (h : Finset.Iic s → LatticePoint d) :
    let cubeEvent : Set Ωcube := {ωc |
      (fun i : Finset.Iic s ↦
        C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωc) =
          selectorHistoryCubePrefix x u h ∧
        C (selectorPrefixSuccessCount u + 1) ωc =
          y - selectorHistoryResidualCurrent u h ∧
        C 0 ωc = x}
    let residualEvent : Set Ωr := {ωr |
      (fun i : Finset.Iic s ↦
        R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωr) =
          selectorHistoryResidualPrefix u h ∧
        R 0 ωr = 0}
    let selectorEvent : Set Ωb := {ωb | (fun i : Fin s ↦ B i ωb) = u ∧ B s ωb = true}
    ((μcube : Measure Ωcube).prod ((μr : Measure Ωr).prod Qb))
        {ω : Ωcube × (Ωr × Ωb) |
          (fun i : Fin s ↦ B i ω.2.2) = u ∧
          B s ω.2.2 = true ∧
          (fun i : Finset.Iic s ↦
            C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1) =
              selectorHistoryCubePrefix x u h ∧
          (fun i : Finset.Iic s ↦
            R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1) =
              selectorHistoryResidualPrefix u h ∧
          C (selectorPrefixSuccessCount u + 1) ω.1 =
            y - selectorHistoryResidualCurrent u h ∧
          C 0 ω.1 = x ∧
          R 0 ω.2.1 = 0} =
      ((μcube : Measure Ωcube) cubeEvent) *
        (((μr : Measure Ωr) residualEvent) * (Qb : Measure Ωb) selectorEvent) := by
  let cubeEvent : Set Ωcube := {ωc |
    (fun i : Finset.Iic s ↦
      C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωc) =
        selectorHistoryCubePrefix x u h ∧
      C (selectorPrefixSuccessCount u + 1) ωc =
        y - selectorHistoryResidualCurrent u h ∧
      C 0 ωc = x}
  let residualEvent : Set Ωr := {ωr |
    (fun i : Finset.Iic s ↦
      R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωr) =
        selectorHistoryResidualPrefix u h ∧
      R 0 ωr = 0}
  let selectorEvent : Set Ωb := {ωb | (fun i : Fin s ↦ B i ωb) = u ∧ B s ωb = true}
  have hcubeEvent_meas : MeasurableSet cubeEvent := by
    have hmap : Measurable
        (fun ωc : Ωcube ↦
          ((fun i : Finset.Iic s ↦
            C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωc),
            C (selectorPrefixSuccessCount u + 1) ωc, C 0 ωc)) := by
      exact Measurable.of_discrete
    -- Proof comment: on the active `true` branch, the cube side contributes both the visible
    -- reconstructed prefix and the fresh active cube target.
    simpa [cubeEvent] using
      hmap (measurableSet_singleton
        (selectorHistoryCubePrefix x u h,
          y - selectorHistoryResidualCurrent u h, x))
  have hresidualEvent_meas : MeasurableSet residualEvent := by
    have hmap : Measurable
        (fun ωr : Ωr ↦
          ((fun i : Finset.Iic s ↦
            R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωr),
            R 0 ωr)) := by
      exact Measurable.of_discrete
    -- Proof comment: the residual side remains passive on the `true` branch, so only its
    -- visible prefix and start value are fixed.
    simpa [residualEvent] using
      hmap (measurableSet_singleton (selectorHistoryResidualPrefix u h, (0 : LatticePoint d)))
  have hselectorEvent_meas : MeasurableSet selectorEvent := by
    have hmap : Measurable (fun ωb : Ωb ↦ (fun i : Fin s ↦ B i ωb, B s ωb)) := by
      exact Measurable.of_discrete
    -- Proof comment: the selector side fixes both the old selector prefix and the fresh `true`
    -- branch bit.
    simpa [selectorEvent] using hmap (measurableSet_singleton (u, true))
  have hset :
      {ω : Ωcube × (Ωr × Ωb) |
          (fun i : Fin s ↦ B i ω.2.2) = u ∧
          B s ω.2.2 = true ∧
          (fun i : Finset.Iic s ↦
            C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1) =
              selectorHistoryCubePrefix x u h ∧
          (fun i : Finset.Iic s ↦
            R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1) =
              selectorHistoryResidualPrefix u h ∧
          C (selectorPrefixSuccessCount u + 1) ω.1 =
            y - selectorHistoryResidualCurrent u h ∧
          C 0 ω.1 = x ∧
          R 0 ω.2.1 = 0} =
        cubeEvent ×ˢ (residualEvent ×ˢ selectorEvent) := by
    ext ω
    rcases ω with ⟨ωc, ωrb⟩
    rcases ωrb with ⟨ωr, ωb⟩
    simp [cubeEvent, residualEvent, selectorEvent, and_assoc, and_left_comm, and_comm]
  -- Proof comment: the active `true` branch is again a literal product rectangle after the split
  -- data are unpacked by coordinate.
  rw [hset, Measure.prod_apply (hcubeEvent_meas.prod (hresidualEvent_meas.prod hselectorEvent_meas))]
  rw [Measure.prod_apply (hresidualEvent_meas.prod hselectorEvent_meas)]

/-- Helper for Theorem 18.8: on the `false` selector branch, the Step 2 history/next split-data
fiber factors into the passive cube fiber, the active residual history/next fiber, and the
selector prefix/branch fiber. -/
private theorem startedHistoryFalseBranchSplitFiber_mass
    {d : ℕ} {Ωcube Ωr Ωb : Type*}
    [MeasurableSpace Ωcube] [MeasurableSpace Ωr] [MeasurableSpace Ωb]
    (μcube : ProbabilityMeasure Ωcube) (μr : ProbabilityMeasure Ωr) (Qb : ProbabilityMeasure Ωb)
    (B : ℕ → Ωb → Bool) (C : ℕ → Ωcube → LatticePoint d) (R : ℕ → Ωr → LatticePoint d)
    (x y : LatticePoint d) {s : ℕ} (u : Fin s → Bool) (h : Finset.Iic s → LatticePoint d) :
    let cubeEvent : Set Ωcube := {ωc |
      (fun i : Finset.Iic s ↦
        C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωc) =
          selectorHistoryCubePrefix x u h ∧
        C 0 ωc = x}
    let residualEvent : Set Ωr := {ωr |
      (fun i : Finset.Iic s ↦
        R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωr) =
          selectorHistoryResidualPrefix u h ∧
        R (s - selectorPrefixSuccessCount u + 1) ωr =
          y - selectorHistoryCubeCurrent x u h ∧
        R 0 ωr = 0}
    let selectorEvent : Set Ωb := {ωb | (fun i : Fin s ↦ B i ωb) = u ∧ B s ωb = false}
    ((μcube : Measure Ωcube).prod ((μr : Measure Ωr).prod Qb))
        {ω : Ωcube × (Ωr × Ωb) |
          (fun i : Fin s ↦ B i ω.2.2) = u ∧
          B s ω.2.2 = false ∧
          (fun i : Finset.Iic s ↦
            C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1) =
              selectorHistoryCubePrefix x u h ∧
          (fun i : Finset.Iic s ↦
            R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1) =
              selectorHistoryResidualPrefix u h ∧
          R (s - selectorPrefixSuccessCount u + 1) ω.2.1 =
            y - selectorHistoryCubeCurrent x u h ∧
          C 0 ω.1 = x ∧
          R 0 ω.2.1 = 0} =
      ((μcube : Measure Ωcube) cubeEvent) *
        (((μr : Measure Ωr) residualEvent) * (Qb : Measure Ωb) selectorEvent) := by
  let cubeEvent : Set Ωcube := {ωc |
    (fun i : Finset.Iic s ↦
      C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωc) =
        selectorHistoryCubePrefix x u h ∧
      C 0 ωc = x}
  let residualEvent : Set Ωr := {ωr |
    (fun i : Finset.Iic s ↦
      R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωr) =
        selectorHistoryResidualPrefix u h ∧
      R (s - selectorPrefixSuccessCount u + 1) ωr =
        y - selectorHistoryCubeCurrent x u h ∧
      R 0 ωr = 0}
  let selectorEvent : Set Ωb := {ωb | (fun i : Fin s ↦ B i ωb) = u ∧ B s ωb = false}
  have hcubeEvent_meas : MeasurableSet cubeEvent := by
    have hmap : Measurable
        (fun ωc : Ωcube ↦
          ((fun i : Finset.Iic s ↦
            C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωc), C 0 ωc)) := by
      exact Measurable.of_discrete
    -- Proof comment: on the passive `false` branch, the cube side only contributes its visible
    -- reconstructed prefix and start value.
    simpa [cubeEvent] using
      hmap (measurableSet_singleton (selectorHistoryCubePrefix x u h, x))
  have hresidualEvent_meas : MeasurableSet residualEvent := by
    have hmap : Measurable
        (fun ωr : Ωr ↦
          ((fun i : Finset.Iic s ↦
            R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωr),
            R (s - selectorPrefixSuccessCount u + 1) ωr, R 0 ωr)) := by
      exact Measurable.of_discrete
    -- Proof comment: on the active `false` branch, the residual side supplies the visible
    -- reconstructed prefix together with the fresh active residual target.
    simpa [residualEvent] using
      hmap (measurableSet_singleton
        (selectorHistoryResidualPrefix u h,
          y - selectorHistoryCubeCurrent x u h, (0 : LatticePoint d)))
  have hselectorEvent_meas : MeasurableSet selectorEvent := by
    have hmap : Measurable (fun ωb : Ωb ↦ (fun i : Fin s ↦ B i ωb, B s ωb)) := by
      exact Measurable.of_discrete
    -- Proof comment: the selector side fixes the old selector prefix together with the fresh
    -- `false` branch bit.
    simpa [selectorEvent] using hmap (measurableSet_singleton (u, false))
  have hset :
      {ω : Ωcube × (Ωr × Ωb) |
          (fun i : Fin s ↦ B i ω.2.2) = u ∧
          B s ω.2.2 = false ∧
          (fun i : Finset.Iic s ↦
            C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1) =
              selectorHistoryCubePrefix x u h ∧
          (fun i : Finset.Iic s ↦
            R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1) =
              selectorHistoryResidualPrefix u h ∧
          R (s - selectorPrefixSuccessCount u + 1) ω.2.1 =
            y - selectorHistoryCubeCurrent x u h ∧
          C 0 ω.1 = x ∧
          R 0 ω.2.1 = 0} =
        cubeEvent ×ˢ (residualEvent ×ˢ selectorEvent) := by
    ext ω
    rcases ω with ⟨ωc, ωrb⟩
    rcases ωrb with ⟨ωr, ωb⟩
    simp [cubeEvent, residualEvent, selectorEvent, and_assoc, and_left_comm, and_comm]
  -- Proof comment: the active `false` branch reduces to the analogous product rectangle with the
  -- roles of the cube and residual coordinates swapped.
  rw [hset, Measure.prod_apply (hcubeEvent_meas.prod (hresidualEvent_meas.prod hselectorEvent_meas))]
  rw [Measure.prod_apply (hresidualEvent_meas.prod hselectorEvent_meas)]

/-- Helper for Theorem 18.8: on the nested product witness space, the mass of a selector branch
is computed from the selector law alone. -/
private lemma prodMeasure_selectorBranch_eq
    {Ωcube Ωr Ωb : Type*}
    [MeasurableSpace Ωcube] [MeasurableSpace Ωr] [MeasurableSpace Ωb]
    (μcube : ProbabilityMeasure Ωcube) (μr : ProbabilityMeasure Ωr) (μβ : ProbabilityMeasure Ωb)
    {β : Type*} [MeasurableSpace β] {f : Ωb → β} (hf : Measurable f)
    {ν : Measure β} (hlaw : HasLaw f ν (μβ : Measure Ωb)) (b : β) :
    ((μcube : Measure Ωcube).prod ((μr : Measure Ωr).prod μβ))
        {ω : Ωcube × (Ωr × Ωb) | f ω.2.2 = b} =
      ν ({b} : Set β) := by
  have hpreimage :
      {ω : Ωcube × (Ωr × Ωb) | f ω.2.2 = b} =
        (fun ω : Ωcube × (Ωr × Ωb) ↦ ω.2.2) ⁻¹' (f ⁻¹' ({b} : Set β)) := by
    ext ω
    simp
  rw [hpreimage]
  rw [prodMeasure_preimage_snd_snd_eq (μcube := μcube) (μr := μr) (μβ := μβ)
    (hA := hf (measurableSet_singleton b))]
  calc
    (μβ : Measure Ωb) (f ⁻¹' ({b} : Set β)) = (Measure.map f (μβ : Measure Ωb)) ({b} : Set β) := by
      rw [Measure.map_apply hf (measurableSet_singleton b)]
    _ = ν ({b} : Set β) := by
      simpa using congrArg (fun ξ : Measure β ↦ ξ ({b} : Set β)) hlaw.map_eq

/-- Helper for Theorem 18.8: a measurable event can be partitioned into singleton fibers of a
finite observable. -/
private lemma measure_eq_sum_inter_preimage_singleton
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Fintype α] [DecidableEq α] [MeasurableSingletonClass α]
    (μ : Measure Ω) (S : Set Ω) (f : Ω → α)
    (hS : MeasurableSet S) (hf : Measurable f) :
    μ S = ∑ a, μ (S ∩ f ⁻¹' ({a} : Set α)) := by
  classical
  let fiber : α → Set Ω := fun a ↦ S ∩ f ⁻¹' ({a} : Set α)
  have hUnion :
      (⋃ a ∈ (Finset.univ : Finset α), fiber a) = S := by
    ext ω
    simp [fiber]
  have hDisj : PairwiseDisjoint (↑(Finset.univ : Finset α)) fiber := by
    intro a ha b hb hab
    refine Set.disjoint_left.2 ?_
    intro ω hωa hωb
    have hfa : f ω = a := by
      simpa [fiber] using hωa.2
    have hfb : f ω = b := by
      simpa [fiber] using hωb.2
    exact hab (hfa.symm.trans hfb)
  have hfiber_meas :
      ∀ a ∈ (Finset.univ : Finset α), MeasurableSet (fiber a) := by
    intro a ha
    exact hS.inter (hf (measurableSet_singleton a))
  -- Proof comment: the measurable event `S` is the finite disjoint union of the singleton fibers
  -- of `f`, so its mass is the sum of the fiber masses.
  calc
    μ S = μ (⋃ a ∈ (Finset.univ : Finset α), fiber a) := by
      rw [hUnion.symm]
    _ = ∑ a ∈ (Finset.univ : Finset α), μ (fiber a) := by
      exact measure_biUnion_finset hDisj hfiber_meas
    _ = ∑ a, μ (S ∩ f ⁻¹' ({a} : Set α)) := by
      simp [fiber]

/-- Helper for Theorem 18.8: one marginal of the Bernoulli-thinned product witness realizes the
owner kernel with increment law `η`. -/
private theorem bernoulliThinnedOwnerRealization
    {d : ℕ} {η ρ : PMF (LatticePoint d)} {α : ENNReal}
    {Ωcube Ωr Ωb : Type*}
    [MeasurableSpace Ωcube] [MeasurableSpace Ωr] [MeasurableSpace Ωb]
    {Pcube : LatticePoint d → ProbabilityMeasure Ωcube}
    {C : ℕ → Ωcube → LatticePoint d}
    {Pr : LatticePoint d → ProbabilityMeasure Ωr}
    {R : ℕ → Ωr → LatticePoint d}
    {Qb : ProbabilityMeasure Ωb} {B : ℕ → Ωb → Bool}
    {p : NNReal}
    (hη_decomp :
      η.toMeasure = α • (uniformCubeStepPMF d).toMeasure + (1 - α) • ρ.toMeasure)
    (hcube :
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel
            (fun x y ↦
              dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure x
                ({y} : Set (LatticePoint d))) ^ n)
        Pcube C)
    (hresid :
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel
            (fun x y ↦ dirac_convolution_kernel ρ.toMeasure x ({y} : Set (LatticePoint d))) ^ n)
        Pr R)
    (hB_meas : ∀ n, Measurable (B n))
    (hB_iid : IsIID B (Qb : Measure Ωb))
    (hp_le_one : p ≤ 1)
    (hp_eq_alpha : (p : ENNReal) = α)
    (hB_law : HasLaw (B 0) (PMF.bernoulli p hp_le_one).toMeasure (Qb : Measure Ωb)) :
    IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (fun x y ↦ dirac_convolution_kernel η.toMeasure x ({y} : Set (LatticePoint d))) ^ n)
      (fun x : LatticePoint d ↦ (Pcube x).prod ((Pr 0).prod Qb))
      (fun n : ℕ => fun ω : Ωcube × (Ωr × Ωb) ↦
        let s :=
          Finset.sum (Finset.range n) (fun i ↦ bif B i ω.2.2 then 1 else 0)
        C s ω.1 + R (n - s) ω.2.1) := by
  let κη : Kernel (LatticePoint d) (LatticePoint d) :=
    discreteMatrixKernel
      (fun x y ↦ dirac_convolution_kernel η.toMeasure x ({y} : Set (LatticePoint d)))
  let P : LatticePoint d → ProbabilityMeasure (Ωcube × (Ωr × Ωb)) := fun x ↦
    (Pcube x).prod ((Pr 0).prod Qb)
  let X : ℕ → (Ωcube × (Ωr × Ωb)) → LatticePoint d := fun n ω ↦
    let s :=
      Finset.sum (Finset.range n) (fun i ↦ bif B i ω.2.2 then 1 else 0)
    C s ω.1 + R (n - s) ω.2.1
  letI : IsMarkovKernel κη := discreteMatrixKernel_isMarkovKernel
    (fun x y ↦ dirac_convolution_kernel η.toMeasure x ({y} : Set (LatticePoint d)))
    (ownerStepMatrix_isStochastic η)
  refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
    (κ₁ := κη) (P := P) (X := X) (hmeas := ?_) (hstart := ?_) (hstep := ?_)
  · -- Proof comment: the thinned marginal lands in a countable discrete lattice, so each time
    -- slice is ambient-measurable.
    intro n
    exact Measurable.of_discrete
  · intro x
    let μcube : Measure Ωcube := (Pcube x : Measure Ωcube)
    let μr : Measure Ωr := (Pr 0 : Measure Ωr)
    let μb : Measure Ωb := (Qb : Measure Ωb)
    have hpair_map :
        ((μcube.prod (μr.prod μb)).map
          (fun ω : Ωcube × (Ωr × Ωb) ↦ (C 0 ω.1, R 0 ω.2.1))) =
          (μcube.map (C 0)).prod
            ((μr.prod μb).map (fun ωrb : Ωr × Ωb ↦ R 0 ωrb.1)) := by
      -- Proof comment: separate the start state into the cube and residual coordinates before
      -- collapsing the residual-selector product.
      simpa using
        (Measure.map_prod_map
          (μa := μcube) (μc := μr.prod μb)
          (f := C 0) (g := fun ωrb : Ωr × Ωb ↦ R 0 ωrb.1)
          (hcube.measurable_process 0)
          ((hresid.measurable_process 0).comp measurable_fst)).symm
    have hresid_prod_map :
        ((μr.prod μb).map (fun ωrb : Ωr × Ωb ↦ R 0 ωrb.1)) = μr.map (R 0) := by
      -- Proof comment: the selector coordinate is ignored at time `0`, so only the residual
      -- start law remains.
      calc
        ((μr.prod μb).map (fun ωrb : Ωr × Ωb ↦ R 0 ωrb.1)) =
            (Measure.map Prod.fst (μr.prod μb)).map (R 0) := by
              rw [Measure.map_map (μ := μr.prod μb) (f := Prod.fst) (g := R 0)
                (hf := measurable_fst) (hg := hresid.measurable_process 0)]
              rfl
        _ = μr.map (R 0) := by
              rw [Measure.map_fst_prod]
    -- Proof comment: at time `0`, the selector count is zero, so the thinned path starts from
    -- the cube start state plus the residual start state `0`.
    calc
      (P x : Measure (Ωcube × (Ωr × Ωb))).map (X 0) =
          (((μcube.prod (μr.prod μb)).map
            (fun ω : Ωcube × (Ωr × Ωb) ↦ (C 0 ω.1, R 0 ω.2.1))).map
              (fun z : LatticePoint d × LatticePoint d ↦ z.1 + z.2)) := by
            rw [← Measure.map_map
              (μ := (P x : Measure (Ωcube × (Ωr × Ωb))))
              (f := fun ω : Ωcube × (Ωr × Ωb) ↦ (C 0 ω.1, R 0 ω.2.1))
              (g := fun z : LatticePoint d × LatticePoint d ↦ z.1 + z.2)
              (hf := by fun_prop) (hg := by fun_prop)]
            simp [P, X]
      _ =
          (((μcube.map (C 0)).prod
            ((μr.prod μb).map (fun ωrb : Ωr × Ωb ↦ R 0 ωrb.1))).map
              (fun z : LatticePoint d × LatticePoint d ↦ z.1 + z.2)) := by
            rw [hpair_map]
      _ =
          (((μcube.map (C 0)).prod (μr.map (R 0))).map
            (fun z : LatticePoint d × LatticePoint d ↦ z.1 + z.2)) := by
            rw [hresid_prod_map]
      _ = (((Measure.dirac x).prod (Measure.dirac (0 : LatticePoint d))).map
            (fun z : LatticePoint d × LatticePoint d ↦ z.1 + z.2)) := by
            rw [hcube.initial_eq x, hresid.initial_eq 0]
      _ = Measure.dirac x := by
            rw [Measure.dirac_prod_dirac]
            simp
  · intro x A hA s
    let selectorCount : ℕ → Ωcube × (Ωr × Ωb) → ℕ := fun n ω ↦
      Finset.sum (Finset.range n) (fun i ↦ bif B i ω.2.2 then 1 else 0)
    let μ : Measure (Ωcube × (Ωr × Ωb)) := (P x : Measure (Ωcube × (Ωr × Ωb)))
    let H : (Ωcube × (Ωr × Ωb)) → Finset.Iic s → LatticePoint d := fun ω i ↦ X i.1 ω
    let next : (Ωcube × (Ωr × Ωb)) → LatticePoint d := fun ω ↦ X (s + 1) ω
    let step : Kernel (Finset.Iic s → LatticePoint d) (LatticePoint d) :=
      Kernel.comap κη (fun h ↦ h ⟨s, Finset.mem_Iic.2 le_rfl⟩) (by fun_prop)
    have hB_law_s :
        HasLaw (B s) (PMF.bernoulli p hp_le_one).toMeasure (Qb : Measure Ωb) := by
      -- Proof comment: the i.i.d. selector family has the same Bernoulli law at every time.
      exact iidCoordinate_hasLaw_zero (hX_iid := hB_iid) (hX0_law := hB_law) s
    have hselector_true_mass :
        (P x : Measure (Ωcube × (Ωr × Ωb))) {ω | B s ω.2.2 = true} = p := by
      -- Proof comment: under the nested product witness measure, the `true` branch mass is just
      -- the Bernoulli parameter of the selector coordinate.
      simpa [P] using
        prodMeasure_selectorBranch_eq
          (μcube := Pcube x) (μr := Pr 0) (μβ := Qb)
          (f := B s) (hf := hB_meas s) (hlaw := hB_law_s) true
    have hselector_false_mass :
        (P x : Measure (Ωcube × (Ωr × Ωb))) {ω | B s ω.2.2 = false} = 1 - p := by
      -- Proof comment: the complementary selector branch carries the remaining Bernoulli mass.
      simpa [P] using
        prodMeasure_selectorBranch_eq
          (μcube := Pcube x) (μr := Pr 0) (μβ := Qb)
          (f := B s) (hf := hB_meas s) (hlaw := hB_law_s) false
    have hselectorPrefixBranchMass :
        ∀ (u : Fin s → Bool) (b : Bool),
          (P x : Measure (Ωcube × (Ωr × Ωb)))
              {ω | (fun i : Fin s ↦ B i ω.2.2) = u ∧ B s ω.2.2 = b} =
            ((Qb : Measure Ωb).map (fun ωb ↦ fun i : Fin s ↦ B i ωb)) ({u} : Set (Fin s → Bool)) *
              ((Qb : Measure Ωb).map (B s)) ({b} : Set Bool) := by
      intro u b
      -- Proof comment: after pushing the selector-only factorization through the nested product,
      -- the fixed prefix and the fresh selector bit are already separated on the full witness
      -- space used by the Bernoulli-thinning argument.
      simpa [P] using
        prodMeasure_selectorPrefixBranchMass
          (μcube := Pcube x) (μr := Pr 0) (Qb := Qb)
          B hB_meas hB_iid s u b
    have htrue_step :
        ∀ ω : Ωcube × (Ωr × Ωb), B s ω.2.2 = true →
          X (s + 1) ω =
            C (selectorCount s ω + 1) ω.1 + R (s - selectorCount s ω) ω.2.1 := by
      intro ω hω
      -- Proof comment: on the `true` branch, the new hidden step is the cube increment branch of
      -- the Bernoulli-thinned recursion.
      simpa [X, selectorCount] using
        thinnedProcess_succ_of_selector_true B C R ω s hω
    have hfalse_step :
        ∀ ω : Ωcube × (Ωr × Ωb), B s ω.2.2 = false →
          X (s + 1) ω =
            C (selectorCount s ω) ω.1 + R (s - selectorCount s ω + 1) ω.2.1 := by
      intro ω hω
      -- Proof comment: on the `false` branch, the new hidden step is the residual increment
      -- branch of the same recursion.
      simpa [X, selectorCount] using
        thinnedProcess_succ_of_selector_false B C R ω s hω
    have hH_meas : Measurable H := by
      -- Proof comment: the visible history lives in a finite discrete product of lattice points.
      exact Measurable.of_discrete
    have hnext_meas : Measurable next := by
      -- Proof comment: each visible state map is measurable on the discrete lattice.
      exact Measurable.of_discrete
    have hfiltration :
        generatedFiltrationSpace X s = MeasurableSpace.comap H inferInstance := by
      refine le_antisymm ?_ ?_
      · rw [generatedFiltrationSpace]
        refine iSup₂_le fun t ht ↦ ?_
        let i : Finset.Iic s := ⟨t, Finset.mem_Iic.2 ht⟩
        have hCoord :
            Measurable[MeasurableSpace.comap H inferInstance] (X t) := by
          simpa [H, X, i] using
            (measurable_pi_apply i).comp (comap_measurable H)
        exact hCoord.comap_le
      · have hPrefix :
          Measurable[generatedFiltrationSpace X s] H := by
          rw [@measurable_pi_iff]
          intro i
          exact le_iSup_of_le i.1 <| le_iSup_of_le (Finset.mem_Iic.1 i.2) le_rfl
        exact hPrefix.comap_le
    have hstart_map :
        μ.map (X 0) = Measure.dirac x := by
      let μcube : Measure Ωcube := (Pcube x : Measure Ωcube)
      let μr : Measure Ωr := (Pr 0 : Measure Ωr)
      let μb : Measure Ωb := (Qb : Measure Ωb)
      have hpair_map :
          ((μcube.prod (μr.prod μb)).map
            (fun ω : Ωcube × (Ωr × Ωb) ↦ (C 0 ω.1, R 0 ω.2.1))) =
            (μcube.map (C 0)).prod
              ((μr.prod μb).map (fun ωrb : Ωr × Ωb ↦ R 0 ωrb.1)) := by
        -- Proof comment: separate the time-`0` cube and residual coordinates before collapsing
        -- the unused selector component.
        simpa using
          (Measure.map_prod_map
            (μa := μcube) (μc := μr.prod μb)
            (f := C 0) (g := fun ωrb : Ωr × Ωb ↦ R 0 ωrb.1)
            (hcube.measurable_process 0)
            ((hresid.measurable_process 0).comp measurable_fst)).symm
      have hresid_prod_map :
          ((μr.prod μb).map (fun ωrb : Ωr × Ωb ↦ R 0 ωrb.1)) = μr.map (R 0) := by
        -- Proof comment: at time `0`, the residual state ignores the selector coordinate.
        calc
          ((μr.prod μb).map (fun ωrb : Ωr × Ωb ↦ R 0 ωrb.1)) =
              (Measure.map Prod.fst (μr.prod μb)).map (R 0) := by
                rw [Measure.map_map (μ := μr.prod μb) (f := Prod.fst) (g := R 0)
                  (hf := measurable_fst) (hg := hresid.measurable_process 0)]
                rfl
          _ = μr.map (R 0) := by
                rw [Measure.map_fst_prod]
      -- Proof comment: the thinned process starts from the cube start state `x` plus the
      -- residual start state `0`, so its time-`0` law is the Dirac mass at `x`.
      calc
        μ.map (X 0) =
            (((μcube.prod (μr.prod μb)).map
              (fun ω : Ωcube × (Ωr × Ωb) ↦ (C 0 ω.1, R 0 ω.2.1))).map
                (fun z : LatticePoint d × LatticePoint d ↦ z.1 + z.2)) := by
              rw [← Measure.map_map
                (μ := μ)
                (f := fun ω : Ωcube × (Ωr × Ωb) ↦ (C 0 ω.1, R 0 ω.2.1))
                (g := fun z : LatticePoint d × LatticePoint d ↦ z.1 + z.2)
                (hf := by fun_prop) (hg := by fun_prop)]
              simp [μ, P, X]
        _ =
            (((μcube.map (C 0)).prod
              ((μr.prod μb).map (fun ωrb : Ωr × Ωb ↦ R 0 ωrb.1))).map
                (fun z : LatticePoint d × LatticePoint d ↦ z.1 + z.2)) := by
              rw [hpair_map]
        _ =
            (((μcube.map (C 0)).prod (μr.map (R 0))).map
              (fun z : LatticePoint d × LatticePoint d ↦ z.1 + z.2)) := by
              rw [hresid_prod_map]
        _ = (((Measure.dirac x).prod (Measure.dirac (0 : LatticePoint d))).map
              (fun z : LatticePoint d × LatticePoint d ↦ z.1 + z.2)) := by
              rw [hcube.initial_eq x, hresid.initial_eq 0]
        _ = Measure.dirac x := by
              rw [Measure.dirac_prod_dirac]
              simp
    have hstart_bad_zero :
        μ {ω | X 0 ω ≠ x} = 0 := by
      have hpreimage :
          {ω | X 0 ω ≠ x} = (X 0) ⁻¹' (({x} : Set (LatticePoint d))ᶜ) := by
        ext ω
        simp
      rw [hpreimage]
      rw [← Measure.map_apply (μ := μ) (f := X 0) (by fun_prop)
        ((measurableSet_singleton x).compl)]
      rw [hstart_map]
      simp
    have hsingleton :
        ∀ h y,
          μ.map (fun ω ↦ (H ω, next ω)) ({(h, y)} : Set ((Finset.Iic s → LatticePoint d) ×
            LatticePoint d)) =
            μ.map H ({h} : Set (Finset.Iic s → LatticePoint d)) *
              step h ({y} : Set (LatticePoint d)) := by
      intro h y
      by_cases hstart : h ⟨0, Finset.mem_Iic.2 le_rfl⟩ = x
      · -- TODO: in the genuine history branch `h 0 = x`, partition the pair singleton by the
        -- selector prefix `u : Fin s → Bool` and the fresh branch bit `b : Bool`.
        -- Route correction: the direct visible-slice factorization kept reproducing the same
        -- normalization blocker. The next proof must first rewrite the started-history atom to an
        -- explicit singleton atom in the independent cube/residual/selector coordinates, then
        -- compute those masses using the tuple-successor laws before collapsing the branch weights
        -- with `ownerMixtureRow_apply_singleton`.
        let startEvt : Set (Ωcube × (Ωr × Ωb)) := {ω | C 0 ω.1 = x ∧ R 0 ω.2.1 = 0}
        have hstartEvt_eq_preimage :
            startEvt =
              (fun ω : Ωcube × (Ωr × Ωb) ↦ (C 0 ω.1, R 0 ω.2.1)) ⁻¹'
                ((({x} : Set (LatticePoint d)) ×ˢ ({0} : Set (LatticePoint d)))) := by
          ext ω
          simp [startEvt]
        have hstartEvt_meas : MeasurableSet startEvt := by
          rw [hstartEvt_eq_preimage]
          fun_prop
        have hstartEvt_full : μ startEvt = 1 := by
          let μcube : Measure Ωcube := (Pcube x : Measure Ωcube)
          let μr : Measure Ωr := (Pr 0 : Measure Ωr)
          let μb : Measure Ωb := (Qb : Measure Ωb)
          have hpair_map :
              ((μcube.prod (μr.prod μb)).map
                (fun ω : Ωcube × (Ωr × Ωb) ↦ (C 0 ω.1, R 0 ω.2.1))) =
                (μcube.map (C 0)).prod
                  ((μr.prod μb).map (fun ωrb : Ωr × Ωb ↦ R 0 ωrb.1)) := by
            -- Proof comment: separate the time-`0` cube and residual coordinates before dropping
            -- the unused selector factor.
            simpa using
              (Measure.map_prod_map
                (μa := μcube) (μc := μr.prod μb)
                (f := C 0) (g := fun ωrb : Ωr × Ωb ↦ R 0 ωrb.1)
                (hcube.measurable_process 0)
                ((hresid.measurable_process 0).comp measurable_fst)).symm
          have hresid_prod_map :
              ((μr.prod μb).map (fun ωrb : Ωr × Ωb ↦ R 0 ωrb.1)) = μr.map (R 0) := by
            -- Proof comment: the residual start state ignores the selector coordinate.
            calc
              ((μr.prod μb).map (fun ωrb : Ωr × Ωb ↦ R 0 ωrb.1)) =
                  (Measure.map Prod.fst (μr.prod μb)).map (R 0) := by
                    rw [Measure.map_map (μ := μr.prod μb) (f := Prod.fst) (g := R 0)
                      (hf := measurable_fst) (hg := hresid.measurable_process 0)]
                    rfl
              _ = μr.map (R 0) := by
                    rw [Measure.map_fst_prod]
          -- Proof comment: the cube coordinate starts from `x` and the residual coordinate starts
          -- from `0`, so the full start slice has mass `1`.
          calc
            μ startEvt =
                (μ.map (fun ω : Ωcube × (Ωr × Ωb) ↦ (C 0 ω.1, R 0 ω.2.1)))
                  ((({x} : Set (LatticePoint d)) ×ˢ ({0} : Set (LatticePoint d)))) := by
                    rw [hstartEvt_eq_preimage]
                    exact
                      Measure.map_apply (μ := μ)
                        (f := fun ω : Ωcube × (Ωr × Ωb) ↦ (C 0 ω.1, R 0 ω.2.1))
                        (by fun_prop)
                        ((measurableSet_singleton x).prod
                          (measurableSet_singleton (0 : LatticePoint d)))
            _ =
                (((μcube.map (C 0)).prod
                  ((μr.prod μb).map (fun ωrb : Ωr × Ωb ↦ R 0 ωrb.1))))
                    ((({x} : Set (LatticePoint d)) ×ˢ ({0} : Set (LatticePoint d)))) := by
                      rw [show μ = μcube.prod (μr.prod μb) by rfl]
                      rw [hpair_map]
            _ =
                (((μcube.map (C 0)).prod (μr.map (R 0))))
                  ((({x} : Set (LatticePoint d)) ×ˢ ({0} : Set (LatticePoint d)))) := by
                    rw [hresid_prod_map]
            _ =
                (((Measure.dirac x).prod (Measure.dirac (0 : LatticePoint d))))
                  ((({x} : Set (LatticePoint d)) ×ˢ ({0} : Set (LatticePoint d)))) := by
                    rw [hcube.initial_eq x, hresid.initial_eq 0]
            _ = 1 := by
                  rw [Measure.dirac_prod_dirac]
                  simp
        have hstartEvt_compl : μ startEvtᶜ = 0 := by
          -- Proof comment: the complement of the almost-sure start slice is null.
          simpa [measure_univ, hstartEvt_full] using
            (measure_compl hstartEvt_meas (measure_ne_top μ startEvt))
        have hpair_on_start :
            μ.map (fun ω ↦ (H ω, next ω))
                ({(h, y)} : Set ((Finset.Iic s → LatticePoint d) × LatticePoint d)) =
              μ ({ω | H ω = h ∧ next ω = y} ∩ startEvt) := by
          let pairEvt : Set (Ωcube × (Ωr × Ωb)) := {ω | H ω = h ∧ next ω = y}
          have hpairEvt_preimage :
              pairEvt =
                (fun ω ↦ (H ω, next ω)) ⁻¹'
                  ({(h, y)} : Set ((Finset.Iic s → LatticePoint d) × LatticePoint d)) := by
            ext ω
            simp [pairEvt]
          have hdecomp :
              pairEvt = (pairEvt ∩ startEvt) ∪ (pairEvt ∩ startEvtᶜ) := by
            ext ω
            by_cases hs : ω ∈ startEvt <;> simp [pairEvt, hs]
          have hdisj : Disjoint (pairEvt ∩ startEvt) (pairEvt ∩ startEvtᶜ) := by
            refine Set.disjoint_left.2 ?_
            intro ω hω₁ hω₂
            exact hω₂.2 hω₁.2
          have hnull : μ (pairEvt ∩ startEvtᶜ) = 0 := by
            refine measure_mono_null ?_ hstartEvt_compl
            intro ω hω
            exact hω.2
          -- Proof comment: intersecting the pair atom with the full-measure start slice does not
          -- change its mass, and this is the slice where the hidden-prefix API applies.
          rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (h, y))]
          rw [hpairEvt_preimage, hdecomp, measure_union hdisj, hnull, add_zero]
        have hhistory_on_start :
            μ.map H ({h} : Set (Finset.Iic s → LatticePoint d)) =
              μ ({ω | H ω = h} ∩ startEvt) := by
          let histEvt : Set (Ωcube × (Ωr × Ωb)) := {ω | H ω = h}
          have hhistEvt_preimage :
              histEvt = H ⁻¹' ({h} : Set (Finset.Iic s → LatticePoint d)) := by
            ext ω
            simp [histEvt]
          have hdecomp :
              histEvt = (histEvt ∩ startEvt) ∪ (histEvt ∩ startEvtᶜ) := by
            ext ω
            by_cases hs : ω ∈ startEvt <;> simp [histEvt, hs]
          have hdisj : Disjoint (histEvt ∩ startEvt) (histEvt ∩ startEvtᶜ) := by
            refine Set.disjoint_left.2 ?_
            intro ω hω₁ hω₂
            exact hω₂.2 hω₁.2
          have hnull : μ (histEvt ∩ startEvtᶜ) = 0 := by
            refine measure_mono_null ?_ hstartEvt_compl
            intro ω hω
            exact hω.2
          -- Proof comment: the history atom can likewise be restricted to the start slice before
          -- evaluating its mass.
          rw [Measure.map_apply hH_meas (measurableSet_singleton h)]
          rw [hhistEvt_preimage, hdecomp, measure_union hdisj, hnull, add_zero]
        have hstartedHistoryPairSingleton :
            μ.map (fun ω ↦ (H ω, next ω)) ({(h, y)} : Set ((Finset.Iic s → LatticePoint d) ×
              LatticePoint d)) =
              μ.map H ({h} : Set (Finset.Iic s → LatticePoint d)) *
                step h ({y} : Set (LatticePoint d)) := by
          let selectorPrefix : Ωcube × (Ωr × Ωb) → Fin s → Bool := fun ω i ↦ B i ω.2.2
          let selectorBranch : Ωcube × (Ωr × Ωb) → (Fin s → Bool) × Bool := fun ω ↦
            (selectorPrefix ω, B s ω.2.2)
          let histStartEvt : Set (Ωcube × (Ωr × Ωb)) := {ω | H ω = h} ∩ startEvt
          let pairStartEvt : Set (Ωcube × (Ωr × Ωb)) := {ω | H ω = h ∧ next ω = y} ∩ startEvt
          have hselectorPrefix_meas : Measurable selectorPrefix := by
            -- Proof comment: the selector prefix is a finite Boolean tuple, hence measurable on
            -- the discrete codomain.
            exact Measurable.of_discrete
          have hselectorBranch_meas : Measurable selectorBranch := by
            -- Proof comment: adjoining the fresh selector bit still lands in a finite discrete
            -- type, so the branch observable is measurable as well.
            exact Measurable.of_discrete
          have hhistStartEvt_meas : MeasurableSet histStartEvt := by
            -- Proof comment: the started-history event is the visible history atom restricted to
            -- the full-measure start slice.
            change MeasurableSet ({ω | H ω = h} ∩ startEvt)
            exact (hH_meas (measurableSet_singleton h)).inter hstartEvt_meas
          have hpairStartEvt_meas : MeasurableSet pairStartEvt := by
            -- Proof comment: the started history/next-state atom is the corresponding pair atom
            -- restricted to the same start slice.
            change MeasurableSet ({ω | H ω = h ∧ next ω = y} ∩ startEvt)
            exact ((by fun_prop : Measurable fun ω ↦ (H ω, next ω))
              (measurableSet_singleton (h, y))).inter hstartEvt_meas
          have hhistory_selector_partition :
              μ.map H ({h} : Set (Finset.Iic s → LatticePoint d)) =
                ∑ u : Fin s → Bool,
                  μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) := by
            rw [hhistory_on_start]
            exact
              measure_eq_sum_inter_preimage_singleton
                (μ := μ) (S := histStartEvt) (f := selectorPrefix)
                hhistStartEvt_meas hselectorPrefix_meas
          have hpair_selector_partition :
              μ.map (fun ω ↦ (H ω, next ω))
                  ({(h, y)} : Set ((Finset.Iic s → LatticePoint d) × LatticePoint d)) =
                ∑ ub : (Fin s → Bool) × Bool,
                  μ (pairStartEvt ∩ selectorBranch ⁻¹' ({ub} : Set ((Fin s → Bool) × Bool))) := by
            rw [hpair_on_start]
            exact
              measure_eq_sum_inter_preimage_singleton
                (μ := μ) (S := pairStartEvt) (f := selectorBranch)
                hpairStartEvt_meas hselectorBranch_meas
          have hbit_true :
              ((Qb : Measure Ωb).map (B s)) ({true} : Set Bool) = p := by
            -- Proof comment: the fresh selector bit at time `s` has the Bernoulli law fixed by
            -- `hB_law_s`.
            simpa [PMF.bernoulli_apply] using
              congrArg (fun ν : Measure Bool ↦ ν ({true} : Set Bool)) hB_law_s.map_eq
          have hbit_false :
              ((Qb : Measure Ωb).map (B s)) ({false} : Set Bool) = 1 - p := by
            -- Proof comment: the complementary selector branch carries the remaining Bernoulli
            -- mass.
            simpa [PMF.bernoulli_apply] using
              congrArg (fun ν : Measure Bool ↦ ν ({false} : Set Bool)) hB_law_s.map_eq
          have hpair_true :
              ∀ u : Fin s → Bool,
                μ (pairStartEvt ∩
                    selectorBranch ⁻¹' ({(u, true)} : Set ((Fin s → Bool) × Bool))) =
                  μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) * α *
                    dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure
                      (selectorHistoryCubeCurrent x u h)
                      ({y - selectorHistoryResidualCurrent u h} : Set (LatticePoint d)) := by
            intro u
            let k : ℕ := selectorPrefixSuccessCount u
            let cubeHistEvent : Set Ωcube := {ωc |
              (fun i : Finset.Iic s ↦
                C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωc) =
                  selectorHistoryCubePrefix x u h ∧
                C 0 ωc = x}
            let residualHistEvent : Set Ωr := {ωr |
              (fun i : Finset.Iic s ↦
                R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωr) =
                  selectorHistoryResidualPrefix u h ∧
                R 0 ωr = 0}
            let selectorPrefixEvent : Set Ωb := {ωb | (fun i : Fin s ↦ B i ωb) = u}
            let cubeTrueEvent : Set Ωcube := {ωc |
              (fun i : Finset.Iic s ↦
                C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωc) =
                  selectorHistoryCubePrefix x u h ∧
                C (selectorPrefixSuccessCount u + 1) ωc =
                  y - selectorHistoryResidualCurrent u h ∧
                C 0 ωc = x}
            let selectorTrueEvent : Set Ωb := {ωb |
              (fun i : Fin s ↦ B i ωb) = u ∧
                B s ωb = true}
            let qcube : LatticePoint d → LatticePoint d → ENNReal := fun a b ↦
              dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure a
                ({b} : Set (LatticePoint d))
            letI :
                IsMarkovProcessRealization
                  (fun n : ℕ ↦ discreteMatrixKernel qcube ^ n) Pcube C := by
              simpa [qcube] using hcube
            have hhistory_rect :
                histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool)) =
                  {ω : Ωcube × (Ωr × Ωb) |
                    (fun i : Fin s ↦ B i ω.2.2) = u ∧
                    (fun i : Finset.Iic s ↦
                      C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1) =
                        selectorHistoryCubePrefix x u h ∧
                    (fun i : Finset.Iic s ↦
                      R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1) =
                        selectorHistoryResidualPrefix u h ∧
                    C 0 ω.1 = x ∧
                    R 0 ω.2.1 = 0} := by
              ext ω
              simpa [histStartEvt, startEvt, selectorPrefix, H, X, selectorCount,
                and_assoc, and_left_comm, and_comm] using
                (startedHistoryAtom_on_start_iff_splitData
                  (B := B) (C := C) (R := R) (x := x) (u := u) (h := h)
                  (ω := ω) hstart)
            have hpair_rect :
                pairStartEvt ∩ selectorBranch ⁻¹' ({(u, true)} : Set ((Fin s → Bool) × Bool)) =
                  {ω : Ωcube × (Ωr × Ωb) |
                    (fun i : Fin s ↦ B i ω.2.2) = u ∧
                    B s ω.2.2 = true ∧
                    (fun i : Finset.Iic s ↦
                      C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1) =
                        selectorHistoryCubePrefix x u h ∧
                    (fun i : Finset.Iic s ↦
                      R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1) =
                        selectorHistoryResidualPrefix u h ∧
                    C (selectorPrefixSuccessCount u + 1) ω.1 =
                      y - selectorHistoryResidualCurrent u h ∧
                    C 0 ω.1 = x ∧
                    R 0 ω.2.1 = 0} := by
              ext ω
              simpa [pairStartEvt, startEvt, selectorBranch, selectorPrefix, H, next, X,
                selectorCount, and_assoc, and_left_comm, and_comm] using
                (startedHistoryBranchAtom_on_start_iff_splitData
                  (B := B) (C := C) (R := R) (x := x) (y := y) (u := u) (h := h)
                  (b := true) (ω := ω) hstart)
            have hhistory_mass :
                μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) =
                  (Pcube x : Measure Ωcube) cubeHistEvent *
                    (((Pr 0 : Measure Ωr) residualHistEvent) *
                      (Qb : Measure Ωb) selectorPrefixEvent) := by
              rw [hhistory_rect]
              simpa [μ, P, cubeHistEvent, residualHistEvent, selectorPrefixEvent] using
                (startedHistorySplitFiber_mass
                  (μcube := Pcube x) (μr := Pr 0) (Qb := Qb)
                  (B := B) (C := C) (R := R) (x := x) (u := u) (h := h))
            have hpair_mass :
                μ (pairStartEvt ∩
                    selectorBranch ⁻¹' ({(u, true)} : Set ((Fin s → Bool) × Bool))) =
                  (Pcube x : Measure Ωcube) cubeTrueEvent *
                    (((Pr 0 : Measure Ωr) residualHistEvent) *
                      (Qb : Measure Ωb) selectorTrueEvent) := by
              rw [hpair_rect]
              simpa [μ, P, cubeTrueEvent, residualHistEvent, selectorTrueEvent] using
                (startedHistoryTrueBranchSplitFiber_mass
                  (μcube := Pcube x) (μr := Pr 0) (Qb := Qb)
                  (B := B) (C := C) (R := R) (x := x) (y := y) (u := u) (h := h))
            have hselector_true_prefix :
                (Qb : Measure Ωb) selectorTrueEvent =
                  (Qb : Measure Ωb) selectorPrefixEvent *
                    ((Qb : Measure Ωb).map (B s)) ({true} : Set Bool) := by
              simpa [selectorTrueEvent, selectorPrefixEvent] using
                (selectorPrefix_singleton_branchMass
                  (Qb := Qb) (B := B) hB_meas hB_iid s u true)
            have hk_le : k ≤ s := selectorPrefixSuccessCount_le_time u
            have hcubeHist_filtration :
                MeasurableSet[generatedFiltrationSpace C k] cubeHistEvent := by
              have hprefix_meas :
                  Measurable[generatedFiltrationSpace C k]
                    (fun ωc : Ωcube ↦
                      fun i : Finset.Iic s ↦
                        C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωc) := by
                rw [@measurable_pi_iff]
                intro i
                exact Measurable.of_comap_le <|
                  le_trans
                    (present_le_generatedHistory C
                      (selectorPrefixSuccessCount (selectorPrefixRestrict u i)))
                    (generatedFiltrationSpace_monoNat
                      (X := C)
                      (m := selectorPrefixSuccessCount (selectorPrefixRestrict u i))
                      (n := k)
                      (selectorPrefixSuccessCount_restrict_le u i))
              have hstart_meas :
                  Measurable[generatedFiltrationSpace C k] (C 0) := by
                exact Measurable.of_comap_le <|
                  le_trans
                    (present_le_generatedHistory C 0)
                    (generatedFiltrationSpace_monoNat
                      (X := C) (m := 0) (n := k) (Nat.zero_le k))
              -- Proof comment: every coordinate in the repeated visible cube fiber is observed by
              -- time `k`, because only `k` cube steps have occurred before time `s`.
              simpa [cubeHistEvent] using
                (hprefix_meas.prodMk hstart_meas)
                  (measurableSet_singleton (selectorHistoryCubePrefix x u h, x))
            have hcubeHist_meas : MeasurableSet cubeHistEvent := by
              exact (generatedHistory_le_ambient C hcube.measurable_process k) _ hcubeHist_filtration
            have hcubeHist_state :
                ∀ ⦃ωc : Ωcube⦄, ωc ∈ cubeHistEvent →
                  C k ωc = selectorHistoryCubeCurrent x u h := by
              intro ωc hωc
              have hprefix :=
                congrArg
                  (fun f : Finset.Iic s → LatticePoint d ↦
                    f ⟨s, Finset.mem_Iic.2 le_rfl⟩)
                  hωc.1
              simpa [k, cubeHistEvent, selectorHistoryCubePrefix, selectorPrefixRestrict] using hprefix
            have hcubeTrue_rect :
                cubeTrueEvent =
                  cubeHistEvent ∩
                    {ωc | C (k + 1) ωc = y - selectorHistoryResidualCurrent u h} := by
              ext ωc
              simp [cubeTrueEvent, cubeHistEvent, k, and_assoc, and_left_comm, and_comm]
            have hcubeTrue_mass :
                (Pcube x : Measure Ωcube) cubeTrueEvent =
                  qcube (selectorHistoryCubeCurrent x u h)
                      ({y - selectorHistoryResidualCurrent u h} : Set (LatticePoint d)) *
                    (Pcube x : Measure Ωcube) cubeHistEvent := by
              rw [hcubeTrue_rect]
              simpa [qcube, k, discreteMatrixKernel_apply_singleton] using
                (measureInter_eq_mul_stepMass_of_stateEvent
                  (q := qcube) (P := Pcube) (X := C)
                  (x := x) (y := selectorHistoryCubeCurrent x u h)
                  (w := y - selectorHistoryResidualCurrent u h)
                  (n := k) (A := cubeHistEvent)
                  hcubeHist_meas hcubeHist_filtration hcubeHist_state)
            -- Proof comment: on the `true` branch, the selector fiber keeps the residual prefix
            -- fixed and only adds one more cube step at the active current.
            calc
              μ (pairStartEvt ∩
                  selectorBranch ⁻¹' ({(u, true)} : Set ((Fin s → Bool) × Bool))) =
                    (Pcube x : Measure Ωcube) cubeTrueEvent *
                      (((Pr 0 : Measure Ωr) residualHistEvent) *
                        (Qb : Measure Ωb) selectorTrueEvent) := hpair_mass
              _ =
                  μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) *
                    ((Qb : Measure Ωb).map (B s)) ({true} : Set Bool) *
                    qcube (selectorHistoryCubeCurrent x u h)
                      ({y - selectorHistoryResidualCurrent u h} : Set (LatticePoint d)) := by
                    rw [hcubeTrue_mass, hselector_true_prefix, hhistory_mass]
                    simp [mul_assoc, mul_left_comm, mul_comm]
              _ =
                  μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) * p *
                    qcube (selectorHistoryCubeCurrent x u h)
                      ({y - selectorHistoryResidualCurrent u h} : Set (LatticePoint d)) := by
                    rw [hbit_true]
              _ =
                  μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) * α *
                    dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure
                      (selectorHistoryCubeCurrent x u h)
                      ({y - selectorHistoryResidualCurrent u h} : Set (LatticePoint d)) := by
                    rw [hp_eq_alpha]
                    rfl
          have hpair_false :
              ∀ u : Fin s → Bool,
                μ (pairStartEvt ∩
                    selectorBranch ⁻¹' ({(u, false)} : Set ((Fin s → Bool) × Bool))) =
                  μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) *
                    (1 - α) *
                    dirac_convolution_kernel ρ.toMeasure
                      (selectorHistoryResidualCurrent u h)
                      ({y - selectorHistoryCubeCurrent x u h} : Set (LatticePoint d)) := by
            intro u
            let k : ℕ := selectorPrefixSuccessCount u
            let rlen : ℕ := s - k
            let cubeHistEvent : Set Ωcube := {ωc |
              (fun i : Finset.Iic s ↦
                C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωc) =
                  selectorHistoryCubePrefix x u h ∧
                C 0 ωc = x}
            let residualHistEvent : Set Ωr := {ωr |
              (fun i : Finset.Iic s ↦
                R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωr) =
                  selectorHistoryResidualPrefix u h ∧
                R 0 ωr = 0}
            let selectorPrefixEvent : Set Ωb := {ωb | (fun i : Fin s ↦ B i ωb) = u}
            let residualFalseEvent : Set Ωr := {ωr |
              (fun i : Finset.Iic s ↦
                R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωr) =
                  selectorHistoryResidualPrefix u h ∧
                R (s - selectorPrefixSuccessCount u + 1) ωr =
                  y - selectorHistoryCubeCurrent x u h ∧
                R 0 ωr = 0}
            let selectorFalseEvent : Set Ωb := {ωb |
              (fun i : Fin s ↦ B i ωb) = u ∧
                B s ωb = false}
            let qresid : LatticePoint d → LatticePoint d → ENNReal := fun a b ↦
              dirac_convolution_kernel ρ.toMeasure a ({b} : Set (LatticePoint d))
            letI :
                IsMarkovProcessRealization
                  (fun n : ℕ ↦ discreteMatrixKernel qresid ^ n) Pr R := by
              simpa [qresid] using hresid
            have hhistory_rect :
                histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool)) =
                  {ω : Ωcube × (Ωr × Ωb) |
                    (fun i : Fin s ↦ B i ω.2.2) = u ∧
                    (fun i : Finset.Iic s ↦
                      C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1) =
                        selectorHistoryCubePrefix x u h ∧
                    (fun i : Finset.Iic s ↦
                      R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1) =
                        selectorHistoryResidualPrefix u h ∧
                    C 0 ω.1 = x ∧
                    R 0 ω.2.1 = 0} := by
              ext ω
              simpa [histStartEvt, startEvt, selectorPrefix, H, X, selectorCount,
                and_assoc, and_left_comm, and_comm] using
                (startedHistoryAtom_on_start_iff_splitData
                  (B := B) (C := C) (R := R) (x := x) (u := u) (h := h)
                  (ω := ω) hstart)
            have hpair_rect :
                pairStartEvt ∩ selectorBranch ⁻¹' ({(u, false)} : Set ((Fin s → Bool) × Bool)) =
                  {ω : Ωcube × (Ωr × Ωb) |
                    (fun i : Fin s ↦ B i ω.2.2) = u ∧
                    B s ω.2.2 = false ∧
                    (fun i : Finset.Iic s ↦
                      C (selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.1) =
                        selectorHistoryCubePrefix x u h ∧
                    (fun i : Finset.Iic s ↦
                      R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ω.2.1) =
                        selectorHistoryResidualPrefix u h ∧
                    R (s - selectorPrefixSuccessCount u + 1) ω.2.1 =
                      y - selectorHistoryCubeCurrent x u h ∧
                    C 0 ω.1 = x ∧
                    R 0 ω.2.1 = 0} := by
              ext ω
              simpa [pairStartEvt, startEvt, selectorBranch, selectorPrefix, H, next, X,
                selectorCount, and_assoc, and_left_comm, and_comm] using
                (startedHistoryBranchAtom_on_start_iff_splitData
                  (B := B) (C := C) (R := R) (x := x) (y := y) (u := u) (h := h)
                  (b := false) (ω := ω) hstart)
            have hhistory_mass :
                μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) =
                  (Pcube x : Measure Ωcube) cubeHistEvent *
                    (((Pr 0 : Measure Ωr) residualHistEvent) *
                      (Qb : Measure Ωb) selectorPrefixEvent) := by
              rw [hhistory_rect]
              simpa [μ, P, cubeHistEvent, residualHistEvent, selectorPrefixEvent] using
                (startedHistorySplitFiber_mass
                  (μcube := Pcube x) (μr := Pr 0) (Qb := Qb)
                  (B := B) (C := C) (R := R) (x := x) (u := u) (h := h))
            have hpair_mass :
                μ (pairStartEvt ∩
                    selectorBranch ⁻¹' ({(u, false)} : Set ((Fin s → Bool) × Bool))) =
                  (Pcube x : Measure Ωcube) cubeHistEvent *
                    (((Pr 0 : Measure Ωr) residualFalseEvent) *
                      (Qb : Measure Ωb) selectorFalseEvent) := by
              rw [hpair_rect]
              simpa [μ, P, cubeHistEvent, residualFalseEvent, selectorFalseEvent] using
                (startedHistoryFalseBranchSplitFiber_mass
                  (μcube := Pcube x) (μr := Pr 0) (Qb := Qb)
                  (B := B) (C := C) (R := R) (x := x) (y := y) (u := u) (h := h))
            have hselector_false_prefix :
                (Qb : Measure Ωb) selectorFalseEvent =
                  (Qb : Measure Ωb) selectorPrefixEvent *
                    ((Qb : Measure Ωb).map (B s)) ({false} : Set Bool) := by
              simpa [selectorFalseEvent, selectorPrefixEvent] using
                (selectorPrefix_singleton_branchMass
                  (Qb := Qb) (B := B) hB_meas hB_iid s u false)
            have hresidualHist_filtration :
                MeasurableSet[generatedFiltrationSpace R rlen] residualHistEvent := by
              have hprefix_meas :
                  Measurable[generatedFiltrationSpace R rlen]
                    (fun ωr : Ωr ↦
                      fun i : Finset.Iic s ↦
                        R (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)) ωr) := by
                rw [@measurable_pi_iff]
                intro i
                exact Measurable.of_comap_le <|
                  le_trans
                    (present_le_generatedHistory R
                      (i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i)))
                    (generatedFiltrationSpace_monoNat
                      (X := R)
                      (m := i.1 - selectorPrefixSuccessCount (selectorPrefixRestrict u i))
                      (n := rlen)
                      (selectorPrefixResidualCount_restrict_le u i))
              have hstart_meas :
                  Measurable[generatedFiltrationSpace R rlen] (R 0) := by
                exact Measurable.of_comap_le <|
                  le_trans
                    (present_le_generatedHistory R 0)
                    (generatedFiltrationSpace_monoNat
                      (X := R) (m := 0) (n := rlen) (Nat.zero_le rlen))
              -- Proof comment: on the residual side, every repeated visible time is read before
              -- the residual clock reaches `rlen = s - selectorPrefixSuccessCount u`.
              simpa [residualHistEvent] using
                (hprefix_meas.prodMk hstart_meas)
                  (measurableSet_singleton (selectorHistoryResidualPrefix u h, (0 : LatticePoint d)))
            have hresidualHist_meas : MeasurableSet residualHistEvent := by
              exact
                (generatedHistory_le_ambient R hresid.measurable_process rlen) _ hresidualHist_filtration
            have hresidualHist_state :
                ∀ ⦃ωr : Ωr⦄, ωr ∈ residualHistEvent →
                  R rlen ωr = selectorHistoryResidualCurrent u h := by
              intro ωr hωr
              have hprefix :=
                congrArg
                  (fun f : Finset.Iic s → LatticePoint d ↦
                    f ⟨s, Finset.mem_Iic.2 le_rfl⟩)
                  hωr.1
              simpa [rlen, k, residualHistEvent, selectorHistoryResidualPrefix,
                selectorPrefixRestrict] using hprefix
            have hresidualFalse_rect :
                residualFalseEvent =
                  residualHistEvent ∩
                    {ωr | R (rlen + 1) ωr = y - selectorHistoryCubeCurrent x u h} := by
              ext ωr
              simp [residualFalseEvent, residualHistEvent, rlen, k, and_assoc,
                and_left_comm, and_comm]
            have hresidualFalse_mass :
                (Pr 0 : Measure Ωr) residualFalseEvent =
                  qresid (selectorHistoryResidualCurrent u h)
                      ({y - selectorHistoryCubeCurrent x u h} : Set (LatticePoint d)) *
                    (Pr 0 : Measure Ωr) residualHistEvent := by
              rw [hresidualFalse_rect]
              simpa [qresid, rlen, k, discreteMatrixKernel_apply_singleton] using
                (measureInter_eq_mul_stepMass_of_stateEvent
                  (q := qresid) (P := Pr) (X := R)
                  (x := (0 : LatticePoint d)) (y := selectorHistoryResidualCurrent u h)
                  (w := y - selectorHistoryCubeCurrent x u h)
                  (n := rlen) (A := residualHistEvent)
                  hresidualHist_meas hresidualHist_filtration hresidualHist_state)
            -- Proof comment: the `false` selector branch is symmetric, with the fresh active step
            -- now taken on the residual process.
            calc
              μ (pairStartEvt ∩
                  selectorBranch ⁻¹' ({(u, false)} : Set ((Fin s → Bool) × Bool))) =
                    (Pcube x : Measure Ωcube) cubeHistEvent *
                      (((Pr 0 : Measure Ωr) residualFalseEvent) *
                        (Qb : Measure Ωb) selectorFalseEvent) := hpair_mass
              _ =
                  μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) *
                    ((Qb : Measure Ωb).map (B s)) ({false} : Set Bool) *
                    qresid (selectorHistoryResidualCurrent u h)
                      ({y - selectorHistoryCubeCurrent x u h} : Set (LatticePoint d)) := by
                    rw [hresidualFalse_mass, hselector_false_prefix, hhistory_mass]
                    simp [mul_assoc, mul_left_comm, mul_comm]
              _ =
                  μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) *
                    (1 - p) *
                    qresid (selectorHistoryResidualCurrent u h)
                      ({y - selectorHistoryCubeCurrent x u h} : Set (LatticePoint d)) := by
                    rw [hbit_false]
              _ =
                  μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) *
                    (1 - α) *
                    dirac_convolution_kernel ρ.toMeasure
                      (selectorHistoryResidualCurrent u h)
                      ({y - selectorHistoryCubeCurrent x u h} : Set (LatticePoint d)) := by
                    rw [hp_eq_alpha]
                    rfl
          -- Proof comment: after splitting by selector words, the `true` and `false` branch
          -- contributions share the same started-history mass and collapse to the owner mixture
          -- row at the visible current state.
          calc
            μ.map (fun ω ↦ (H ω, next ω))
                ({(h, y)} : Set ((Finset.Iic s → LatticePoint d) × LatticePoint d)) =
                ∑ ub : (Fin s → Bool) × Bool,
                  μ (pairStartEvt ∩ selectorBranch ⁻¹' ({ub} : Set ((Fin s → Bool) × Bool))) := by
                    exact hpair_selector_partition
            _ =
                ∑ u : Fin s → Bool,
                  (μ (pairStartEvt ∩
                    selectorBranch ⁻¹' ({(u, true)} : Set ((Fin s → Bool) × Bool))) +
                    μ (pairStartEvt ∩
                      selectorBranch ⁻¹' ({(u, false)} : Set ((Fin s → Bool) × Bool)))) := by
                    simpa [add_comm, add_left_comm, add_assoc] using
                      (show
                        (∑ ub : (Fin s → Bool) × Bool,
                          μ (pairStartEvt ∩
                            selectorBranch ⁻¹' ({ub} : Set ((Fin s → Bool) × Bool)))) =
                          ∑ u : Fin s → Bool,
                            (μ (pairStartEvt ∩
                              selectorBranch ⁻¹' ({(u, false)} : Set ((Fin s → Bool) × Bool))) +
                              μ (pairStartEvt ∩
                                selectorBranch ⁻¹' ({(u, true)} : Set ((Fin s → Bool) × Bool)))) by
                        rw [Fintype.sum_prod_type, Fintype.sum_bool])
            _ =
                ∑ u : Fin s → Bool,
                  μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) *
                    step h ({y} : Set (LatticePoint d)) := by
                    refine Finset.sum_congr rfl ?_
                    intro u hu
                    rw [hpair_true u, hpair_false u]
                    have hmix :=
                      ownerMixtureRow_apply_singleton_of_selectorHistory
                        (η := η) (ρ := ρ) (hη_decomp := hη_decomp)
                        (x := x) (y := y) (u := u) (h := h) hstart
                    have hstep_row :
                        step h ({y} : Set (LatticePoint d)) =
                          dirac_convolution_kernel η.toMeasure
                            (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) ({y} : Set (LatticePoint d)) := by
                      simp [step]
                    calc
                      μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) * α *
                          dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure
                            (selectorHistoryCubeCurrent x u h)
                            ({y - selectorHistoryResidualCurrent u h} : Set (LatticePoint d)) +
                        μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) *
                          (1 - α) *
                          dirac_convolution_kernel ρ.toMeasure
                            (selectorHistoryResidualCurrent u h)
                            ({y - selectorHistoryCubeCurrent x u h} : Set (LatticePoint d)) =
                          μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) *
                            (α *
                              dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure
                                (selectorHistoryCubeCurrent x u h)
                                ({y - selectorHistoryResidualCurrent u h} : Set (LatticePoint d)) +
                              (1 - α) *
                                dirac_convolution_kernel ρ.toMeasure
                                  (selectorHistoryResidualCurrent u h)
                                  ({y - selectorHistoryCubeCurrent x u h} : Set (LatticePoint d))) := by
                            simp [mul_assoc, left_distrib, right_distrib]
                      _ =
                          μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) *
                            dirac_convolution_kernel η.toMeasure
                              (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) ({y} : Set (LatticePoint d)) := by
                            exact
                              congrArg
                                (fun t ↦
                                  μ (histStartEvt ∩
                                      selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) * t)
                                hmix
                      _ =
                          μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))) *
                            step h ({y} : Set (LatticePoint d)) := by
                            rw [hstep_row]
            _ =
                (∑ u : Fin s → Bool,
                  μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool)))) *
                  step h ({y} : Set (LatticePoint d)) := by
                    symm
                    simpa using
                      (Finset.sum_mul
                        (Finset.univ : Finset (Fin s → Bool))
                        (fun u : Fin s → Bool ↦
                          μ (histStartEvt ∩ selectorPrefix ⁻¹' ({u} : Set (Fin s → Bool))))
                        (step h ({y} : Set (LatticePoint d))))
            _ =
                μ.map H ({h} : Set (Finset.Iic s → LatticePoint d)) *
                  step h ({y} : Set (LatticePoint d)) := by
                    rw [hhistory_selector_partition]
        exact hstartedHistoryPairSingleton
      · -- Proof comment: if the visible history starts at the wrong point, both the history atom
        -- and the pair atom are null because the thinned process starts at `x` almost surely.
        have hhistory_zero :
            μ.map H ({h} : Set (Finset.Iic s → LatticePoint d)) = 0 := by
          rw [Measure.map_apply hH_meas (measurableSet_singleton h)]
          refine measure_mono_null ?_ hstart_bad_zero
          intro ω hω
          have hHω : H ω = h := by
            simpa using hω
          have hX0 : X 0 ω = h ⟨0, Finset.mem_Iic.2 le_rfl⟩ := by
            simpa [H] using
              congrArg (fun f : Finset.Iic s → LatticePoint d ↦
                f ⟨0, Finset.mem_Iic.2 le_rfl⟩) hHω
          simpa [Set.mem_setOf_eq, hX0] using hstart
        have hpair_zero :
            μ.map (fun ω ↦ (H ω, next ω))
                ({(h, y)} : Set ((Finset.Iic s → LatticePoint d) × LatticePoint d)) = 0 := by
          rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (h, y))]
          refine measure_mono_null ?_ hstart_bad_zero
          intro ω hω
          have hpairω : (H ω, next ω) = (h, y) := by
            simpa using hω
          have hHω : H ω = h := (Prod.mk.inj hpairω).1
          have hX0 : X 0 ω = h ⟨0, Finset.mem_Iic.2 le_rfl⟩ := by
            simpa [H] using
              congrArg (fun f : Finset.Iic s → LatticePoint d ↦
                f ⟨0, Finset.mem_Iic.2 le_rfl⟩) hHω
          simpa [Set.mem_setOf_eq, hX0] using hstart
        rw [hpair_zero, hhistory_zero]
        simp
    have hpair :
        μ.map (fun ω ↦ (H ω, next ω)) = (μ.map H) ⊗ₘ step := by
      -- Proof comment: on countable discrete target spaces, the joint law is determined by the
      -- singleton masses proved in `hsingleton`.
      exact compProd_eq_of_pairSingletonMass μ H next step hsingleton
    have hcond :
        condDistrib next H μ =ᵐ[μ.map H] step := by
      exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hH_meas hnext_meas hpair
    have hcondexp :
        μ⟦next ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ]
          fun ω ↦ (condDistrib next H μ (H ω)).real A := by
      simpa using
        (condDistrib_ae_eq_condExp (μ := μ) (X := H) (Y := next)
          hH_meas hnext_meas hA).symm
    have hkernel :
        (fun ω ↦ (step (H ω)).real A) =ᵐ[μ]
          fun ω ↦ (κη (X s ω)).real A := by
      -- Proof comment: the one-step kernel is evaluated at the current visible endpoint of the
      -- history tuple.
      exact Filter.Eventually.of_forall fun ω ↦ by
        simp [step, H, X]
    rw [hfiltration]
    exact hcondexp.trans <| (ae_eq_comp hH_meas.aemeasurable hcond).trans hkernel

/-- Helper for Theorem 18.8: a convex decomposition of the owner increment law into a uniform
cube part and a residual part yields a successful owner-level coupling. -/
private theorem ownerMixture_hasSuccessfulCoupling_of_uniformCubeDecomp
    {d : ℕ} (η ρ : PMF (LatticePoint d)) {α : ENNReal}
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hη_decomp :
      η.toMeasure = α • (uniformCubeStepPMF d).toMeasure + (1 - α) • ρ.toMeasure) :
    HasSuccessfulCoupling.{0, 0}
      (fun x y ↦ dirac_convolution_kernel η.toMeasure x ({y} : Set (LatticePoint d))) := by
  -- Route correction: the remaining Step 2 work is no longer the tail-event algebra. The file
  -- now has the deterministic containment and its measure bound, so the only missing pieces are
  -- the base uniform-cube successful coupling and the marginal verification for the thinned walk.
  -- Proof comment: this is the Step 2 Bernoulli-thinning construction from the textbook proof.
  by_cases hsub : Subsingleton (LatticePoint d)
  · -- Proof comment: on a subsingleton lattice, every owner kernel is coupled by the diagonal
    -- realization, so the mixture decomposition is irrelevant.
    letI : Subsingleton (LatticePoint d) := hsub
    simpa using subsingletonOwner_hasSuccessfulCoupling (ν := η)
  have hcube :
      HasSuccessfulCoupling.{0, 0}
        (fun x y ↦
          dirac_convolution_kernel (uniformCubeStepPMF d).toMeasure x
            ({y} : Set (LatticePoint d))) :=
    uniformCubeOwner_hasSuccessfulCoupling d
  rcases hcube.exists_successfulCoupling with
    ⟨Ωcube, mΩcube, Pcube, Zcube, hcubeSuccess⟩
  let qρ : LatticePoint d → LatticePoint d → ENNReal :=
    fun x y ↦ dirac_convolution_kernel ρ.toMeasure x ({y} : Set (LatticePoint d))
  obtain ⟨Pr, hresid⟩ :=
    existsCanonicalDiscreteMatrixRealization (q := qρ) (hq := ownerStepMatrix_isStochastic ρ)
  have hα_ne_top : α ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt hα_le_one (by simp))
  let p : NNReal := ⟨α.toReal, ENNReal.toReal_nonneg⟩
  have hp_pos : 0 < p := by
    change 0 < α.toReal
    exact ENNReal.toReal_pos (ne_of_gt hα_pos) hα_ne_top
  have hp_le_one : p ≤ 1 := by
    change α.toReal ≤ 1
    exact (ENNReal.toReal_le_toReal hα_ne_top (by simp)).2 hα_le_one
  obtain ⟨Ωb, mΩb, Qraw, Braw, hBraw_meas, hBraw_law, hBraw_indep, hQraw_prob⟩ :=
    ProbabilityTheory.exists_iid (ULift.{0} ℕ) ((PMF.bernoulli p hp_le_one).toMeasure)
  let Qb : ProbabilityMeasure Ωb := ⟨Qraw, hQraw_prob⟩
  let B : ℕ → Ωb → Bool := fun n ω ↦ Braw ⟨n⟩ ω
  have hB_meas : ∀ n, Measurable (B n) := by
    intro n
    simpa [B] using hBraw_meas ⟨n⟩
  have hB_law_zero :
      HasLaw (B 0) (PMF.bernoulli p hp_le_one).toMeasure (Qb : Measure Ωb) := by
    simpa [B, Qb] using hBraw_law ⟨0⟩
  have hB_law : ∀ n, HasLaw (B n) (PMF.bernoulli p hp_le_one).toMeasure (Qb : Measure Ωb) := by
    intro n
    simpa [B, Qb] using hBraw_law ⟨n⟩
  have hB_iid : IsIID B (Qb : Measure Ωb) := by
    refine ⟨?_, ?_⟩
    · simpa [B, Qb] using
        hBraw_indep.precomp (g := fun n : ℕ ↦ (⟨n⟩ : ULift.{0} ℕ)) (by
          intro i j hij
          simpa using congrArg ULift.down hij)
    · intro i j
      exact (hB_law i).identDistrib (hB_law j)
  let Ωr : Type := ℕ → LatticePoint d
  let Ω : Type := Ωcube × (Ωr × Ωb)
  let P : LatticePoint d × LatticePoint d → ProbabilityMeasure Ω :=
    fun a ↦ (Pcube a).prod ((Pr 0).prod Qb)
  let S : ℕ → Ω → ℕ := fun n ω ↦
    Finset.sum (Finset.range n) (fun i ↦ bif B i ω.2.2 then 1 else 0)
  let Xcube : ℕ → Ω → LatticePoint d := fun n ω ↦ (Zcube n ω.1).1
  let Ycube : ℕ → Ω → LatticePoint d := fun n ω ↦ (Zcube n ω.1).2
  let Rpath : ℕ → Ω → LatticePoint d := fun n ω ↦ ω.2.1 n
  let Z : ℕ → Ω → LatticePoint d × LatticePoint d := fun n ω ↦
    (Xcube (S n ω) ω + Rpath (n - S n ω) ω, Ycube (S n ω) ω + Rpath (n - S n ω) ω)
  refine ProbabilityTheory.HasSuccessfulCoupling.mk.{0, 0} ?_
  refine ⟨Ω, inferInstance, P, Z, ?_⟩
  refine
    { toIsMarkovCoupling := ?_
      tail_disagreement_tendsto_zero := ?_ }
  · refine
      { fst_realization := ?_
        snd_realization := ?_ }
    · intro y
      let hcubeFst := hcubeSuccess.toIsMarkovCoupling.fst_realization y
      -- Proof comment: the first thinned coordinate uses the first cube marginal together with
      -- the shared residual and Bernoulli clock.
      simpa [P, Z, S, Xcube, Rpath] using
        bernoulliThinnedOwnerRealization
          (η := η) (ρ := ρ) (α := α) (Ωr := Ωr) (p := p)
          (Pcube := fun x ↦ Pcube (x, y))
          (C := fun n ω ↦ (Zcube n ω).1)
          (hη_decomp := hη_decomp)
          (hcube := hcubeFst)
          (Pr := Pr) (R := Function.eval) (hresid := hresid)
          (hB_meas := hB_meas) (hB_iid := hB_iid)
          (hp_le_one := hp_le_one)
          (hp_eq_alpha := by
            -- Proof comment: the thinning Bernoulli parameter was chosen as the real value of the
            -- mixture coefficient `α`, so their `ENNReal` masses agree.
            change ENNReal.ofReal α.toReal = α
            simpa using ENNReal.ofReal_toReal hα_ne_top)
          (hB_law := hB_law_zero)
    · intro x
      let hcubeSnd := hcubeSuccess.toIsMarkovCoupling.snd_realization x
      -- Proof comment: the second thinned coordinate is the same construction on the second cube
      -- marginal.
      simpa [P, Z, S, Ycube, Rpath] using
        bernoulliThinnedOwnerRealization
          (η := η) (ρ := ρ) (α := α) (Ωr := Ωr) (p := p)
          (Pcube := fun y ↦ Pcube (x, y))
          (C := fun n ω ↦ (Zcube n ω).2)
          (hη_decomp := hη_decomp)
          (hcube := hcubeSnd)
          (Pr := Pr) (R := Function.eval) (hresid := hresid)
          (hB_meas := hB_meas) (hB_iid := hB_iid)
          (hp_le_one := hp_le_one)
          (hp_eq_alpha := by
            -- Proof comment: the same Bernoulli/mixing-coefficient identification is reused for
            -- the second marginal.
            change ENNReal.ofReal α.toReal = α
            simpa using ENNReal.ofReal_toReal hα_ne_top)
          (hB_law := hB_law_zero)
  · intro x y
    let hcubeFst :=
      hcubeSuccess.toIsMarkovCoupling.fst_realization y
    let hcubeSnd :=
      hcubeSuccess.toIsMarkovCoupling.snd_realization x
    have hselectorLower_meas :
        ∀ n K : ℕ,
          MeasurableSet
            {ωb : Ωb |
              Finset.sum (Finset.range n) (fun i ↦ bif B i ωb then 1 else 0) < K} := by
      intro n K
      exact measurableSet_lt (by fun_prop) measurable_const
    have hclockBase :
        ∀ K : ℕ,
          Tendsto
            (fun n ↦
              (Qb : Measure Ωb)
                {ωb : Ωb |
                  Finset.sum (Finset.range n) (fun i ↦ bif B i ωb then 1 else 0) < K})
            atTop (nhds 0) := by
      intro K
      simpa using
        bernoulliSelectorCount_lowerTail_tendsto_zero
          (μ := (Qb : Measure Ωb)) (B := B)
          hB_meas hB_iid hp_pos hp_le_one hB_law_zero K
    have hclock :
        ∀ K : ℕ,
          Tendsto
            (fun n ↦ (P (x, y) : Measure Ω) {ω | S n ω < K})
            atTop (nhds 0) := by
      intro K
      have hEq :
          (fun n ↦ (P (x, y) : Measure Ω) {ω | S n ω < K}) =
            fun n ↦
              (Qb : Measure Ωb)
                {ωb : Ωb |
                  Finset.sum (Finset.range n) (fun i ↦ bif B i ωb then 1 else 0) < K} := by
        funext n
        dsimp [P, S]
        have hpreimage :
            {ω : Ω | Finset.sum (Finset.range n) (fun i ↦ bif B i ω.2.2 then 1 else 0) < K} =
              (fun ω : Ω ↦ ω.2.2) ⁻¹'
                {ωb : Ωb |
                  Finset.sum (Finset.range n) (fun i ↦ bif B i ωb then 1 else 0) < K} := by
          ext ω
          simp
        rw [hpreimage]
        exact
          prodMeasure_preimage_snd_snd_eq
            (μcube := Pcube (x, y)) (μr := Pr 0) (μβ := Qb)
            (hA := hselectorLower_meas n K)
      rw [hEq]
      exact hclockBase K
    have hcubeTail_meas :
        ∀ K : ℕ,
          MeasurableSet
            (⋃ j ≥ K, {ωc : Ωcube | (Zcube j ωc).1 ≠ (Zcube j ωc).2}) := by
      intro K
      refine MeasurableSet.iUnion fun j ↦ ?_
      refine MeasurableSet.iUnion fun _ ↦ ?_
      exact (measurableSet_eq_fun (hcubeFst.measurable_process j) (hcubeSnd.measurable_process j)).compl
    have hcubeTail :
        Tendsto
          (fun K ↦ (P (x, y) : Measure Ω) (⋃ j ≥ K, {ω | Xcube j ω ≠ Ycube j ω}))
          atTop (nhds 0) := by
      have hEq :
          (fun K ↦ (P (x, y) : Measure Ω) (⋃ j ≥ K, {ω | Xcube j ω ≠ Ycube j ω})) =
            fun K ↦
              (Pcube (x, y) : Measure Ωcube) (⋃ j ≥ K, {ωc : Ωcube | (Zcube j ωc).1 ≠ (Zcube j ωc).2}) := by
        funext K
        dsimp [P]
        have hpreimage :
            (⋃ j ≥ K, {ω : Ω | Xcube j ω ≠ Ycube j ω}) =
              Prod.fst ⁻¹' (⋃ j ≥ K, {ωc : Ωcube | (Zcube j ωc).1 ≠ (Zcube j ωc).2}) := by
          ext ω
          simp [Xcube, Ycube]
        rw [hpreimage]
        exact
          prodMeasure_preimage_fst_eq
            (μ := (Pcube (x, y) : Measure Ωcube))
            (ν := (Pr 0).prod Qb)
            (hA := hcubeTail_meas K)
      rw [hEq]
      simpa using hcubeSuccess.tail_disagreement_tendsto_zero x y
    have hS_mono : ∀ ω, Monotone fun n ↦ S n ω := by
      intro ω
      simpa [S] using selectorSuccessCount_monotone (fun n ωb ↦ B n ωb) ω.2.2
    -- Proof comment: the remaining tail estimate is exactly the shared-residual thinning bound
    -- already proved above, with the clock term carried by the Bernoulli lower-tail theorem.
    simpa [Z, Xcube, Ycube, Rpath] using
      thinnedTailDisagreement_tendsto_zero_of_clock_and_cube
        (μ := (P (x, y) : Measure Ω))
        (S := S) (X := Xcube) (Y := Ycube) (R := Rpath)
        hS_mono hclock hcubeTail

/-- Helper for Theorem 18.8: condition the canonical owner path law on the block endpoint to get
an endpoint-indexed kernel of prefixes on `Finset.Iic N`. -/
private noncomputable def ownerEndpointConditionedPrefixKernelIic
    {d : ℕ} (P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)) (N : ℕ)
    (x : LatticePoint d) :
    Kernel (LatticePoint d) (Finset.Iic N → LatticePoint d) :=
  condDistrib (Preorder.frestrictLe N) (fun ξ : ℕ → LatticePoint d ↦ ξ N) (P x)

/-- Helper for Theorem 18.8: the canonical owner path law factors into the endpoint law at time
`N` and the endpoint-conditioned prefix kernel. -/
private theorem ownerEndpointConditionedPrefixKernelIic_reconstruction
    {d : ℕ} (ν : PMF (LatticePoint d))
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (hP :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P Function.eval)
    (N : ℕ) (x : LatticePoint d) :
    (P x : Measure (ℕ → LatticePoint d)).map
      (fun ξ ↦ (ξ N, Preorder.frestrictLe N ξ)) =
      (((dirac_convolution_kernel ν.toMeasure ^ N) x) ⊗ₘ
        ownerEndpointConditionedPrefixKernelIic P N x) := by
  let μ : Measure (ℕ → LatticePoint d) := (P x : Measure (ℕ → LatticePoint d))
  -- Proof comment: this is exactly `compProd_map_condDistrib` for the endpoint/prefix pair, and
  -- the endpoint marginal is the canonical owner row at time `N`.
  calc
    μ.map (fun ξ ↦ (ξ N, Preorder.frestrictLe N ξ)) =
        (μ.map (fun ξ : ℕ → LatticePoint d ↦ ξ N)) ⊗ₘ
          condDistrib (Preorder.frestrictLe N) (fun ξ : ℕ → LatticePoint d ↦ ξ N) μ := by
            simpa [μ, ownerEndpointConditionedPrefixKernelIic] using
              (compProd_map_condDistrib
                (μ := μ)
                (X := fun ξ : ℕ → LatticePoint d ↦ ξ N)
                (Y := Preorder.frestrictLe N)
                (hY := (Preorder.measurable_frestrictLe N).aemeasurable)).symm
    _ = (((dirac_convolution_kernel ν.toMeasure ^ N) x) ⊗ₘ
          ownerEndpointConditionedPrefixKernelIic P N x) := by
          rw [hP.transition_eq x N]

/-- Helper for Theorem 18.8: conditioning the canonical owner path law on the endpoint at time
`N` forces the sampled prefix to end at that endpoint. -/
private theorem ownerEndpointConditionedPrefixKernelIic_endpoint
    {d : ℕ}
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (N : ℕ) (x y : LatticePoint d)
    (hy :
      ((P x : Measure (ℕ → LatticePoint d)).map (fun ξ : ℕ → LatticePoint d ↦ ξ N))
        ({y} : Set (LatticePoint d)) ≠ 0) :
    ownerEndpointConditionedPrefixKernelIic P N x y
        {ξ : Finset.Iic N → LatticePoint d | ξ ⟨N, Finset.mem_Iic.2 le_rfl⟩ = y} = 1 := by
  let μ : Measure (ℕ → LatticePoint d) := (P x : Measure (ℕ → LatticePoint d))
  let endpoint : (ℕ → LatticePoint d) → LatticePoint d := fun ξ ↦ ξ N
  let prefix : (ℕ → LatticePoint d) → Finset.Iic N → LatticePoint d := Preorder.frestrictLe N
  let endFiber : Set (Finset.Iic N → LatticePoint d) :=
    {ξ | ξ ⟨N, Finset.mem_Iic.2 le_rfl⟩ = y}
  have hendFiber_meas : MeasurableSet endFiber := by
    -- Proof comment: the endpoint fiber is a singleton condition on one discrete coordinate of
    -- the finite prefix tuple.
    exact measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  have hpair_preimage :
      (fun ξ : ℕ → LatticePoint d ↦ (endpoint ξ, prefix ξ)) ⁻¹' (({y} : Set (LatticePoint d)) ×ˢ endFiber) =
        endpoint ⁻¹' ({y} : Set (LatticePoint d)) := by
    -- Proof comment: a prefix obtained by restricting a full path to `Finset.Iic N` already has
    -- the same value at coordinate `N` as the endpoint map itself.
    ext ξ
    simp [endpoint, prefix, endFiber, Preorder.frestrictLe_apply]
  have hrect :
      μ.map (fun ξ : ℕ → LatticePoint d ↦ (endpoint ξ, prefix ξ))
          (({y} : Set (LatticePoint d)) ×ˢ endFiber) =
        μ.map endpoint ({y} : Set (LatticePoint d)) := by
    rw [Measure.map_apply (by fun_prop) ((measurableSet_singleton y).prod hendFiber_meas)]
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
    exact congrArg (fun s : Set (ℕ → LatticePoint d) ↦ μ s) hpair_preimage
  -- Proof comment: `condDistrib_apply_of_ne_zero` converts the conditional row to the normalized
  -- joint mass, and the previous rectangle identity shows that the normalized mass is total.
  rw [ownerEndpointConditionedPrefixKernelIic]
  rw [condDistrib_apply_of_ne_zero
    (μ := μ) (X := endpoint) (Y := prefix) (hY := Preorder.measurable_frestrictLe N) y hy]
  rw [hrect]
  exact ENNReal.inv_mul_cancel hy (measure_ne_top _ _)

/-- Helper for Theorem 18.8: for fixed block endpoints, use the diagonal bridge when the two
start-end pairs agree and otherwise take the product of the two conditioned prefix rows. -/
private noncomputable def pairedEndpointBridgeKernelIic
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (N : ℕ) (x₁ x₂ : LatticePoint d) :
    Kernel (LatticePoint d × LatticePoint d)
      ((Finset.Iic N → LatticePoint d) × (Finset.Iic N → LatticePoint d)) :=
  ⟨
    fun y ↦
      if h : (x₁, y.1) = (x₂, y.2) then
        Measure.map (fun ξ : Finset.Iic N → LatticePoint d ↦ (ξ, ξ))
          (ownerEndpointConditionedPrefixKernelIic P N x₁ y.1)
      else
        (ownerEndpointConditionedPrefixKernelIic P N x₁ y.1).prod
          (ownerEndpointConditionedPrefixKernelIic P N x₂ y.2),
    Measure.measurable_of_measurable_coe _ fun _ _ ↦ Measurable.of_discrete
  ⟩

/-- Helper for Theorem 18.8: the first marginal of the paired endpoint bridge is the first
conditioned prefix row. -/
private theorem pairedEndpointBridgeKernelIic_fst_row
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (N : ℕ) (x₁ x₂ y₁ y₂ : LatticePoint d) :
    Measure.map Prod.fst (pairedEndpointBridgeKernelIic P N x₁ x₂ (y₁, y₂)) =
      ownerEndpointConditionedPrefixKernelIic P N x₁ y₁ := by
  by_cases h : (x₁, y₁) = (x₂, y₂)
  · rcases Prod.mk.inj h with ⟨hx, hy⟩
    subst hx
    subst hy
    -- Proof comment: on the diagonal branch, projecting the mapped diagonal measure to the first
    -- coordinate recovers the original conditioned prefix row.
    rw [pairedEndpointBridgeKernelIic, dif_pos rfl]
    rw [Measure.map_map (f := fun ξ : Finset.Iic N → LatticePoint d ↦ (ξ, ξ))
      (g := Prod.fst) (hf := by fun_prop) (hg := measurable_fst)]
    simp
  · -- Proof comment: off the diagonal branch, the bridge row is the product of the two
    -- conditioned prefix rows, and `Measure.map_fst_prod` reads off the first factor.
    rw [pairedEndpointBridgeKernelIic, dif_neg h]
    simpa using
      (Measure.map_fst_prod
        (μ := ownerEndpointConditionedPrefixKernelIic P N x₁ y₁)
        (ν := ownerEndpointConditionedPrefixKernelIic P N x₂ y₂))

/-- Helper for Theorem 18.8: the second marginal of the paired endpoint bridge is the second
conditioned prefix row. -/
private theorem pairedEndpointBridgeKernelIic_snd_row
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (N : ℕ) (x₁ x₂ y₁ y₂ : LatticePoint d) :
    Measure.map Prod.snd (pairedEndpointBridgeKernelIic P N x₁ x₂ (y₁, y₂)) =
      ownerEndpointConditionedPrefixKernelIic P N x₂ y₂ := by
  by_cases h : (x₁, y₁) = (x₂, y₂)
  · rcases Prod.mk.inj h with ⟨hx, hy⟩
    subst hx
    subst hy
    -- Proof comment: on the diagonal branch, the second projection of the diagonal map is again
    -- the identity on the underlying conditioned prefix row.
    rw [pairedEndpointBridgeKernelIic, dif_pos rfl]
    rw [Measure.map_map (f := fun ξ : Finset.Iic N → LatticePoint d ↦ (ξ, ξ))
      (g := Prod.snd) (hf := by fun_prop) (hg := measurable_snd)]
    simp
  · -- Proof comment: off the diagonal branch, the second marginal of the product bridge is the
    -- second conditioned prefix row.
    rw [pairedEndpointBridgeKernelIic, dif_neg h]
    simpa using
      (Measure.map_snd_prod
        (μ := ownerEndpointConditionedPrefixKernelIic P N x₁ y₁)
        (ν := ownerEndpointConditionedPrefixKernelIic P N x₂ y₂))

/-- Helper for Theorem 18.8: when the two block endpoint pairs agree, the paired bridge samples
equal prefixes almost surely. -/
private theorem pairedEndpointBridgeKernelIic_diag_row
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (N : ℕ) (x₁ x₂ y₁ y₂ : LatticePoint d)
    (hxy : (x₁, y₁) = (x₂, y₂)) :
    pairedEndpointBridgeKernelIic P N x₁ x₂ (y₁, y₂)
      {z : (Finset.Iic N → LatticePoint d) × (Finset.Iic N → LatticePoint d) | z.1 = z.2} = 1 := by
  rcases Prod.mk.inj hxy with ⟨hx, hy⟩
  subst hx
  subst hy
  let diagSet :
      Set ((Finset.Iic N → LatticePoint d) × (Finset.Iic N → LatticePoint d)) :=
    {z | z.1 = z.2}
  have hdiag_meas : MeasurableSet diagSet := by
    -- Proof comment: on the discrete prefix space, equality of the two coordinates defines a
    -- measurable diagonal event.
    exact measurableSet_eq_fun measurable_fst measurable_snd
  have hpreimage :
      (fun ξ : Finset.Iic N → LatticePoint d ↦ (ξ, ξ)) ⁻¹' diagSet = Set.univ := by
    -- Proof comment: every point on the diagonal map lands in the diagonal event by definition.
    ext ξ
    simp [diagSet]
  -- Proof comment: the diagonal branch is literally the pushforward of a single bridge row along
  -- the diagonal embedding, so the diagonal event pulls back to the whole space.
  rw [pairedEndpointBridgeKernelIic, dif_pos rfl]
  rw [Measure.map_apply (by fun_prop) hdiag_meas, hpreimage]
  simp

/-- Helper for Theorem 18.8: if the owner `N`-step transition from `x` to `y` has positive mass,
then the endpoint-conditioned prefix row is supported on prefixes ending at `y`. -/
private theorem ownerEndpointConditionedPrefixKernelIic_endpoint_of_transition_ne_zero
    {d : ℕ} {ν : PMF (LatticePoint d)}
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (hP :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P Function.eval)
    (N : ℕ) (x y : LatticePoint d)
    (hy : ((dirac_convolution_kernel ν.toMeasure ^ N) x) ({y} : Set (LatticePoint d)) ≠ 0) :
    ownerEndpointConditionedPrefixKernelIic P N x y
        {ξ : Finset.Iic N → LatticePoint d | ξ ⟨N, Finset.mem_Iic.2 le_rfl⟩ = y} = 1 := by
  -- Proof comment: rewrite the required nonzero endpoint mass through the realization identity,
  -- then apply the conditioned-prefix endpoint theorem already proved above.
  apply ownerEndpointConditionedPrefixKernelIic_endpoint
  simpa [hP.transition_eq x N] using hy

/-- Helper for Theorem 18.8: if the owner `N`-step transition from `x` to `y` has positive mass,
then the endpoint-conditioned prefix row is also supported on prefixes starting at `x`. -/
private theorem ownerEndpointConditionedPrefixKernelIic_start_of_transition_ne_zero
    {d : ℕ} {ν : PMF (LatticePoint d)}
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (hP :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P Function.eval)
    (N : ℕ) (x y : LatticePoint d)
    (hy : ((dirac_convolution_kernel ν.toMeasure ^ N) x) ({y} : Set (LatticePoint d)) ≠ 0) :
    ownerEndpointConditionedPrefixKernelIic P N x y
        {ξ : Finset.Iic N → LatticePoint d |
          ξ ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = x} = 1 := by
  let μ : Measure (ℕ → LatticePoint d) := (P x : Measure (ℕ → LatticePoint d))
  let endpoint : (ℕ → LatticePoint d) → LatticePoint d := fun ξ ↦ ξ N
  let prefix : (ℕ → LatticePoint d) → Finset.Iic N → LatticePoint d := Preorder.frestrictLe N
  let startFiber : Set (Finset.Iic N → LatticePoint d) :=
    {ξ | ξ ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = x}
  let startEvent : Set (ℕ → LatticePoint d) := {ξ | ξ 0 = x}
  have hstartFiber_meas : MeasurableSet startFiber := by
    -- Proof comment: the start fiber is a singleton condition on the first coordinate of the
    -- finite prefix tuple.
    exact measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  have hpreimage :
      (fun ξ : ℕ → LatticePoint d ↦ (endpoint ξ, prefix ξ)) ⁻¹'
          (({y} : Set (LatticePoint d)) ×ˢ startFiber) =
        endpoint ⁻¹' ({y} : Set (LatticePoint d)) ∩ startEvent := by
    -- Proof comment: a full path contributes to the rectangle exactly when its endpoint is `y`
    -- and its time-`0` coordinate matches the prescribed start `x`.
    ext ξ
    simp [endpoint, prefix, startFiber, startEvent, Preorder.frestrictLe_apply]
  have hstart_zero : μ (startEventᶜ) = 0 := by
    have hpreimage_bad :
        startEventᶜ = (fun ξ : ℕ → LatticePoint d ↦ ξ 0) ⁻¹'
          (({x} : Set (LatticePoint d))ᶜ) := by
      ext ξ
      simp [startEvent]
    -- Proof comment: every owner path sampled from `P x` starts at `x`, so the complementary
    -- start event is null.
    rw [hpreimage_bad]
    rw [← Measure.map_apply (μ := μ) (f := fun ξ : ℕ → LatticePoint d ↦ ξ 0) (by fun_prop)
      ((measurableSet_singleton x).compl)]
    rw [hP.initial_eq x]
    simp
  have hstart_slice :
      μ (endpoint ⁻¹' ({y} : Set (LatticePoint d)) ∩ startEvent) =
        μ (endpoint ⁻¹' ({y} : Set (LatticePoint d))) := by
    let endEvent : Set (ℕ → LatticePoint d) := endpoint ⁻¹' ({y} : Set (LatticePoint d))
    have hdecomp :
        endEvent = (endEvent ∩ startEvent) ∪ (endEvent ∩ startEventᶜ) := by
      ext ξ
      simp [endEvent]
    have hdisj : Disjoint (endEvent ∩ startEvent) (endEvent ∩ startEventᶜ) := by
      refine Set.disjoint_left.2 ?_
      intro ξ hξ₁ hξ₂
      exact hξ₂.2 hξ₁.2
    have hnull : μ (endEvent ∩ startEventᶜ) = 0 := by
      refine measure_mono_null ?_ hstart_zero
      intro ξ hξ
      exact hξ.2
    -- Proof comment: intersecting with the almost-sure start event does not change the endpoint
    -- slice because the discarded part sits inside the null bad-start set.
    rw [hdecomp, measure_union hdisj]
    simp [hnull, endEvent]
  have hy_row :
      (μ.map endpoint) ({y} : Set (LatticePoint d)) ≠ 0 := by
    -- Proof comment: the endpoint marginal of the canonical owner realization is the genuine
    -- `N`-step owner row from `x`.
    simpa [μ, endpoint, hP.transition_eq x N] using hy
  -- Proof comment: after expanding `condDistrib` on the endpoint/prefix rectangle, the start
  -- fiber contributes full mass because the underlying owner path starts at `x` almost surely.
  rw [ownerEndpointConditionedPrefixKernelIic]
  rw [condDistrib_apply_of_ne_zero
    (μ := μ) (X := endpoint) (Y := prefix) (hY := Preorder.measurable_frestrictLe N) y hy_row]
  rw [Measure.map_apply (by fun_prop) ((measurableSet_singleton y).prod hstartFiber_meas)]
  rw [hpreimage, hstart_slice]
  exact ENNReal.inv_mul_cancel hy_row (measure_ne_top _ _)

/-- Helper for Theorem 18.8: under the paired endpoint bridge, the first sampled prefix ends at
the prescribed first endpoint whenever that endpoint has positive owner `N`-step mass. -/
private theorem pairedEndpointBridgeKernelIic_fst_endpoint_of_transition_ne_zero
    {d : ℕ} {ν : PMF (LatticePoint d)}
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (hP :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P Function.eval)
    (N : ℕ) (x₁ x₂ y₁ y₂ : LatticePoint d)
    (hy₁ : ((dirac_convolution_kernel ν.toMeasure ^ N) x₁) ({y₁} : Set (LatticePoint d)) ≠ 0) :
    pairedEndpointBridgeKernelIic P N x₁ x₂ (y₁, y₂)
        {z : (Finset.Iic N → LatticePoint d) × (Finset.Iic N → LatticePoint d) |
          z.1 ⟨N, Finset.mem_Iic.2 le_rfl⟩ = y₁} = 1 := by
  let endFiber :
      Set (Finset.Iic N → LatticePoint d) :=
    {ξ | ξ ⟨N, Finset.mem_Iic.2 le_rfl⟩ = y₁}
  have hendFiber_meas : MeasurableSet endFiber := by
    -- Proof comment: the endpoint event is a singleton condition on one discrete prefix
    -- coordinate.
    exact measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  have hpreimage :
      {z : (Finset.Iic N → LatticePoint d) × (Finset.Iic N → LatticePoint d) |
          z.1 ⟨N, Finset.mem_Iic.2 le_rfl⟩ = y₁} =
        Prod.fst ⁻¹' endFiber := by
    -- Proof comment: projecting to the first prefix coordinate turns the bridge endpoint event
    -- into the corresponding first-factor endpoint fiber.
    ext z
    simp [endFiber]
  rw [hpreimage]
  rw [← Measure.map_apply measurable_fst hendFiber_meas]
  rw [pairedEndpointBridgeKernelIic_fst_row]
  exact
    ownerEndpointConditionedPrefixKernelIic_endpoint_of_transition_ne_zero
      (hP := hP) N x₁ y₁ hy₁

/-- Helper for Theorem 18.8: inside a bridge conditioned on the endpoint `ξ N = y`, a
history/next-step atom picks up both the owner one-step mass and the remaining bridge mass to
`y`. -/
private theorem ownerEndpointConditionedPrefixKernelIic_average_historyNextMass
    {d : ℕ} {ν : PMF (LatticePoint d)}
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (hP :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P Function.eval)
    (N r : ℕ) (hr : r < N) (x w : LatticePoint d)
    (h : Finset.Iic r → LatticePoint d) :
    (∑' y : LatticePoint d,
      ((dirac_convolution_kernel ν.toMeasure ^ N) x) ({y} : Set (LatticePoint d)) *
        ownerEndpointConditionedPrefixKernelIic P N x y
          {ξ : Finset.Iic N → LatticePoint d |
            Preorder.frestrictLe r ξ = h ∧
              ξ ⟨r + 1, Finset.mem_Iic.2 (Nat.le_of_lt hr)⟩ = w}) =
      (∑' y : LatticePoint d,
        ((dirac_convolution_kernel ν.toMeasure ^ N) x) ({y} : Set (LatticePoint d)) *
          ownerEndpointConditionedPrefixKernelIic P N x y
            {ξ : Finset.Iic N → LatticePoint d | Preorder.frestrictLe r ξ = h}) *
        dirac_convolution_kernel ν.toMeasure
          (h ⟨r, Finset.mem_Iic.2 le_rfl⟩) ({w} : Set (LatticePoint d)) := by
  let μ : Measure (ℕ → LatticePoint d) := (P x : Measure (ℕ → LatticePoint d))
  let endpoint : (ℕ → LatticePoint d) → LatticePoint d := fun ξ ↦ ξ N
  let prefixN : (ℕ → LatticePoint d) → Finset.Iic N → LatticePoint d := Preorder.frestrictLe N
  let prefixR : (ℕ → LatticePoint d) → Finset.Iic r → LatticePoint d := Preorder.frestrictLe r
  let curr : LatticePoint d := h ⟨r, Finset.mem_Iic.2 le_rfl⟩
  let histEvent : Set (ℕ → LatticePoint d) := {ξ | prefixR ξ = h}
  let histNextEvent : Set (ℕ → LatticePoint d) :=
    histEvent ∩ {ξ | Function.eval (r + 1) ξ = w}
  let prefixEvent : Set (Finset.Iic N → LatticePoint d) := {ξ | Preorder.frestrictLe r ξ = h}
  let prefixNextEvent : Set (Finset.Iic N → LatticePoint d) :=
    {ξ |
      Preorder.frestrictLe r ξ = h ∧
        ξ ⟨r + 1, Finset.mem_Iic.2 (Nat.le_of_lt hr)⟩ = w}
  let q : LatticePoint d → LatticePoint d → ENNReal := fun a b ↦
    dirac_convolution_kernel ν.toMeasure a ({b} : Set (LatticePoint d))
  have hPstep :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel q ^ n) P Function.eval := by
    -- Proof comment: the singleton-mass spelling of the owner kernel gives the same owner
    -- realization, so the discrete matrix step-event lemma applies directly.
    simpa [q, ownerStepMatrix_kernel_eq] using hP
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel q ^ n) P Function.eval := hPstep
  have hhist_filtration :
      MeasurableSet[generatedFiltrationSpace Function.eval r] histEvent := by
    let times : Fin (r + 2) → ℕ := fun i ↦ i
    have htimes : StrictMono times := fun _ _ hij ↦ hij
    -- Proof comment: fixing the owner prefix through time `r` is a generated-filtration event.
    simpa [histEvent, prefixR, times] using
      (prefixTuple_preimage_measurable_generatedFiltration
        (X := Function.eval) (times := times) htimes
        (B := {h}) (measurableSet_singleton h))
  have hhist_meas : MeasurableSet histEvent := by
    exact (generatedHistory_le_ambient Function.eval hP.measurable_process r) _ hhist_filtration
  have hhist_state :
      ∀ ⦃ξ : ℕ → LatticePoint d⦄, ξ ∈ histEvent → Function.eval r ξ = curr := by
    intro ξ hξ
    have hprefix : prefixR ξ = h := by
      simpa [histEvent] using hξ
    simpa [curr, prefixR, Preorder.frestrictLe_apply] using
      congrArg (fun f : Finset.Iic r → LatticePoint d ↦ f ⟨r, Finset.mem_Iic.2 le_rfl⟩) hprefix
  have hhistNext_mass :
      μ histNextEvent =
        dirac_convolution_kernel ν.toMeasure curr ({w} : Set (LatticePoint d)) * μ histEvent := by
    -- Proof comment: before conditioning on the far endpoint, the prefix event already fixes the
    -- current owner state `curr`, so one more step gives the next-state atom.
    simpa [μ, histNextEvent, q, curr, discreteMatrixKernel_apply_singleton] using
      (measureInter_eq_mul_stepMass_of_stateEvent
        (q := q) (P := P) (X := Function.eval)
        (x := x) (y := curr) (w := w) (n := r) (A := histEvent)
        hhist_meas hhist_filtration hhist_state)
  have hprefixEvent_meas : MeasurableSet prefixEvent := MeasurableSet.of_discrete
  have hprefixNextEvent_meas : MeasurableSet prefixNextEvent := MeasurableSet.of_discrete
  have hprefix_rect :
      (fun ξ : ℕ → LatticePoint d ↦ (endpoint ξ, prefixN ξ)) ⁻¹'
          (Set.univ ×ˢ prefixEvent) = histEvent := by
    ext ξ
    simp [endpoint, prefixN, prefixEvent, histEvent, prefixR, Preorder.frestrictLe_apply]
  have hprefixNext_rect :
      (fun ξ : ℕ → LatticePoint d ↦ (endpoint ξ, prefixN ξ)) ⁻¹'
          (Set.univ ×ˢ prefixNextEvent) = histNextEvent := by
    ext ξ
    simp [endpoint, prefixN, prefixNextEvent, histNextEvent, histEvent, prefixR,
      Preorder.frestrictLe_apply, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
  have hprefix_mass :
      (∑' y : LatticePoint d,
        ((dirac_convolution_kernel ν.toMeasure ^ N) x) ({y} : Set (LatticePoint d)) *
          ownerEndpointConditionedPrefixKernelIic P N x y prefixEvent) =
        μ histEvent := by
    calc
      (∑' y : LatticePoint d,
        ((dirac_convolution_kernel ν.toMeasure ^ N) x) ({y} : Set (LatticePoint d)) *
          ownerEndpointConditionedPrefixKernelIic P N x y prefixEvent) =
          ((((dirac_convolution_kernel ν.toMeasure ^ N) x) ⊗ₘ
            ownerEndpointConditionedPrefixKernelIic P N x) (Set.univ ×ˢ prefixEvent)) := by
              rw [Measure.compProd_apply (MeasurableSet.univ.prod hprefixEvent_meas)]
              simpa [MeasureTheory.lintegral_countable', mul_comm]
      _ =
          μ.map (fun ξ : ℕ → LatticePoint d ↦ (endpoint ξ, prefixN ξ))
            (Set.univ ×ˢ prefixEvent) := by
              rw [ownerEndpointConditionedPrefixKernelIic_reconstruction (ν := ν) hP N x]
      _ = μ histEvent := by
            rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ.prod hprefixEvent_meas)]
            exact congrArg (fun s : Set (ℕ → LatticePoint d) ↦ μ s) hprefix_rect
  have hprefixNext_mass :
      (∑' y : LatticePoint d,
        ((dirac_convolution_kernel ν.toMeasure ^ N) x) ({y} : Set (LatticePoint d)) *
          ownerEndpointConditionedPrefixKernelIic P N x y prefixNextEvent) =
        μ histNextEvent := by
    calc
      (∑' y : LatticePoint d,
        ((dirac_convolution_kernel ν.toMeasure ^ N) x) ({y} : Set (LatticePoint d)) *
          ownerEndpointConditionedPrefixKernelIic P N x y prefixNextEvent) =
          ((((dirac_convolution_kernel ν.toMeasure ^ N) x) ⊗ₘ
            ownerEndpointConditionedPrefixKernelIic P N x) (Set.univ ×ˢ prefixNextEvent)) := by
              rw [Measure.compProd_apply (MeasurableSet.univ.prod hprefixNextEvent_meas)]
              simpa [MeasureTheory.lintegral_countable', mul_comm]
      _ =
          μ.map (fun ξ : ℕ → LatticePoint d ↦ (endpoint ξ, prefixN ξ))
            (Set.univ ×ˢ prefixNextEvent) := by
              rw [ownerEndpointConditionedPrefixKernelIic_reconstruction (ν := ν) hP N x]
      _ = μ histNextEvent := by
            rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ.prod hprefixNextEvent_meas)]
            exact congrArg (fun s : Set (ℕ → LatticePoint d) ↦ μ s) hprefixNext_rect
  -- Proof comment: reconstruct both averaged conditioned-prefix masses from the endpoint/prefix
  -- `compProd`, then discharge the remaining equality by the ordinary owner one-step law.
  rw [hprefixNext_mass, hhistNext_mass, hprefix_mass]

private theorem ownerEndpointConditionedPrefixKernelIic_historyNextMass_mul_remaining
    {d : ℕ} {ν : PMF (LatticePoint d)}
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (hP :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P Function.eval)
    (N r : ℕ) (hr : r < N) (x y w : LatticePoint d)
    (h : Finset.Iic r → LatticePoint d)
    (hy : ((dirac_convolution_kernel ν.toMeasure ^ N) x) ({y} : Set (LatticePoint d)) ≠ 0) :
    ownerEndpointConditionedPrefixKernelIic P N x y
        {ξ : Finset.Iic N → LatticePoint d |
          Preorder.frestrictLe r ξ = h ∧
            ξ ⟨r + 1, Finset.mem_Iic.2 (Nat.le_of_lt hr)⟩ = w} *
      ((dirac_convolution_kernel ν.toMeasure ^ (N - r))
        (h ⟨r, Finset.mem_Iic.2 le_rfl⟩) ({y} : Set (LatticePoint d))) =
      ownerEndpointConditionedPrefixKernelIic P N x y
          {ξ : Finset.Iic N → LatticePoint d | Preorder.frestrictLe r ξ = h} *
        dirac_convolution_kernel ν.toMeasure
          (h ⟨r, Finset.mem_Iic.2 le_rfl⟩) ({w} : Set (LatticePoint d)) *
        ((dirac_convolution_kernel ν.toMeasure ^ (N - (r + 1))) w)
          ({y} : Set (LatticePoint d)) := by
private theorem ownerEndpointConditionedPrefixKernelIic_historyNextMass_mul_remaining
    {d : ℕ} {ν : PMF (LatticePoint d)}
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (hP :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P Function.eval)
    (N r : ℕ) (hr : r < N) (x y w : LatticePoint d)
    (h : Finset.Iic r → LatticePoint d)
    (hy : ((dirac_convolution_kernel ν.toMeasure ^ N) x) ({y} : Set (LatticePoint d)) ≠ 0) :
    ownerEndpointConditionedPrefixKernelIic P N x y
        {ξ : Finset.Iic N → LatticePoint d |
          Preorder.frestrictLe r ξ = h ∧
            ξ ⟨r + 1, Finset.mem_Iic.2 (Nat.le_of_lt hr)⟩ = w} *
      ((dirac_convolution_kernel ν.toMeasure ^ (N - r))
        (h ⟨r, Finset.mem_Iic.2 le_rfl⟩) ({y} : Set (LatticePoint d))) =
      ownerEndpointConditionedPrefixKernelIic P N x y
          {ξ : Finset.Iic N → LatticePoint d | Preorder.frestrictLe r ξ = h} *
        dirac_convolution_kernel ν.toMeasure
          (h ⟨r, Finset.mem_Iic.2 le_rfl⟩) ({w} : Set (LatticePoint d)) *
        ((dirac_convolution_kernel ν.toMeasure ^ (N - (r + 1))) w)
          ({y} : Set (LatticePoint d)) := by
  let μ : Measure (ℕ → LatticePoint d) := (P x : Measure (ℕ → LatticePoint d))
  let endpoint : (ℕ → LatticePoint d) → LatticePoint d := fun ξ ↦ ξ N
  let prefixN : (ℕ → LatticePoint d) → Finset.Iic N → LatticePoint d := Preorder.frestrictLe N
  let prefixR : (ℕ → LatticePoint d) → Finset.Iic r → LatticePoint d := Preorder.frestrictLe r
  let curr : LatticePoint d := h ⟨r, Finset.mem_Iic.2 le_rfl⟩
  let histEvent : Set (ℕ → LatticePoint d) := {ξ | prefixR ξ = h}
  let histNextEvent : Set (ℕ → LatticePoint d) :=
    histEvent ∩ {ξ | Function.eval (r + 1) ξ = w}
  let prefixEvent : Set (Finset.Iic N → LatticePoint d) := {ξ | Preorder.frestrictLe r ξ = h}
  let prefixNextEvent : Set (Finset.Iic N → LatticePoint d) :=
    {ξ |
      Preorder.frestrictLe r ξ = h ∧
        ξ ⟨r + 1, Finset.mem_Iic.2 (Nat.le_of_lt hr)⟩ = w}
  let q : LatticePoint d → LatticePoint d → ENNReal := fun a b ↦
    dirac_convolution_kernel ν.toMeasure a ({b} : Set (LatticePoint d))
  have hPstep :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel q ^ n) P Function.eval := by
    -- Proof comment: the singleton-mass matrix of the owner kernel is definitionally the same
    -- one-step kernel, so the existing owner realization can be reused unchanged.
    simpa [q, ownerStepMatrix_kernel_eq] using hP
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel q ^ n) P Function.eval := hPstep
  have hy_row :
      (μ.map endpoint) ({y} : Set (LatticePoint d)) ≠ 0 := by
    -- Proof comment: the endpoint marginal of the canonical realization is the genuine `N`-step
    -- owner row.
    simpa [μ, endpoint, hP.transition_eq x N] using hy
  have hhist_filtration :
      MeasurableSet[generatedFiltrationSpace Function.eval r] histEvent := by
    let times : Fin (r + 2) → ℕ := fun i ↦ i
    have htimes : StrictMono times := fun _ _ hij ↦ hij
    -- Proof comment: fixing the prefix tuple through time `r` is a generated-filtration event at
    -- time `r`.
    simpa [histEvent, prefixR, times] using
      (prefixTuple_preimage_measurable_generatedFiltration
        (X := Function.eval) (times := times) htimes
        (B := {h}) (measurableSet_singleton h))
  have hhist_meas : MeasurableSet histEvent := by
    exact (generatedHistory_le_ambient Function.eval hP.measurable_process r) _ hhist_filtration
  have hhist_state :
      ∀ ⦃ξ : ℕ → LatticePoint d⦄, ξ ∈ histEvent → Function.eval r ξ = curr := by
    intro ξ hξ
    have hprefix : prefixR ξ = h := by
      simpa [histEvent] using hξ
    simpa [curr, prefixR, Preorder.frestrictLe_apply] using
      congrArg (fun f : Finset.Iic r → LatticePoint d ↦ f ⟨r, Finset.mem_Iic.2 le_rfl⟩) hprefix
  have hhist_filtration_succ :
      MeasurableSet[generatedFiltrationSpace Function.eval (r + 1)] histEvent := by
    exact
      (generatedFiltrationSpace_monoNat
        (X := Function.eval) (m := r) (n := r + 1) (Nat.le_succ r)) _ hhist_filtration
  have hnext_state_filtration :
      MeasurableSet[generatedFiltrationSpace Function.eval (r + 1)]
        {ξ : ℕ → LatticePoint d | Function.eval (r + 1) ξ = w} := by
    have hmeas :
        Measurable[generatedFiltrationSpace Function.eval (r + 1)] (Function.eval (r + 1)) := by
      exact Measurable.of_comap_le (present_le_generatedHistory Function.eval (r + 1))
    exact hmeas (measurableSet_singleton w)
  have hhistNext_filtration :
      MeasurableSet[generatedFiltrationSpace Function.eval (r + 1)] histNextEvent := by
    -- Proof comment: the refined history/next event is the time-`r` prefix atom together with
    -- the time-`r + 1` singleton.
    simpa [histNextEvent] using hhist_filtration_succ.inter hnext_state_filtration
  have hhistNext_meas : MeasurableSet histNextEvent := by
    exact
      (generatedHistory_le_ambient Function.eval hP.measurable_process (r + 1)) _
        hhistNext_filtration
  have hhistNext_state :
      ∀ ⦃ξ : ℕ → LatticePoint d⦄, ξ ∈ histNextEvent → Function.eval (r + 1) ξ = w := by
    intro ξ hξ
    simpa [histNextEvent] using hξ.2
  have hhistNext_step :
      μ histNextEvent =
        dirac_convolution_kernel ν.toMeasure curr ({w} : Set (LatticePoint d)) * μ histEvent := by
    -- Proof comment: before conditioning on the far endpoint, the history atom already fixes the
    -- current state `curr`, so one more step uses the owner one-step law from `curr`.
    simpa [μ, histNextEvent, q, curr, discreteMatrixKernel_apply_singleton] using
      (measureInter_eq_mul_stepMass_of_stateEvent
        (q := q) (P := P) (X := Function.eval)
        (x := x) (y := curr) (w := w) (n := r) (A := histEvent)
        hhist_meas hhist_filtration hhist_state)
  have hhist_endpoint :
      μ (histEvent ∩ {ξ : ℕ → LatticePoint d | endpoint ξ = y}) =
        ((dirac_convolution_kernel ν.toMeasure ^ (N - r)) curr) ({y} : Set (LatticePoint d)) *
          μ histEvent := by
    -- Proof comment: the remaining owner mass from `curr` to the fixed endpoint `y` governs the
    -- endpoint slice of the time-`r` history atom.
    simpa [μ, endpoint, q, curr, histEvent, Nat.add_sub_of_le hr.le, ownerStepMatrix_kernel_eq]
      using
      (measureInter_eq_mul_kernelPowMass_of_stateEvent
        (q := q) (P := P) (X := Function.eval)
        (x := x) (y := curr) (w := y) (n := r) (t := N - r) (A := histEvent)
        hhist_meas hhist_filtration hhist_state)
  have hhistNext_endpoint :
      μ (histNextEvent ∩ {ξ : ℕ → LatticePoint d | endpoint ξ = y}) =
        ((dirac_convolution_kernel ν.toMeasure ^ (N - (r + 1))) w) ({y} : Set (LatticePoint d)) *
          μ histNextEvent := by
    -- Proof comment: after fixing the one-step extension to `w`, the remaining bridge mass is the
    -- owner `(N - (r + 1))`-step row from `w` to `y`.
    simpa [μ, endpoint, q, histNextEvent, Nat.add_sub_of_le (Nat.succ_le_of_lt hr),
      ownerStepMatrix_kernel_eq] using
      (measureInter_eq_mul_kernelPowMass_of_stateEvent
        (q := q) (P := P) (X := Function.eval)
        (x := x) (y := w) (w := y) (n := r + 1) (t := N - (r + 1)) (A := histNextEvent)
        hhistNext_meas hhistNext_filtration hhistNext_state)
  have hprefixEvent_meas : MeasurableSet prefixEvent := MeasurableSet.of_discrete
  have hprefixNextEvent_meas : MeasurableSet prefixNextEvent := MeasurableSet.of_discrete
  have hprefix_rect :
      (fun ξ : ℕ → LatticePoint d ↦ (endpoint ξ, prefixN ξ)) ⁻¹'
          (({y} : Set (LatticePoint d)) ×ˢ prefixEvent) =
        histEvent ∩ {ξ : ℕ → LatticePoint d | endpoint ξ = y} := by
    ext ξ
    simp [endpoint, prefixN, prefixEvent, prefixR, Preorder.frestrictLe_apply, Set.inter_comm,
      Set.inter_left_comm, Set.inter_assoc]
  have hprefixNext_rect :
      (fun ξ : ℕ → LatticePoint d ↦ (endpoint ξ, prefixN ξ)) ⁻¹'
          (({y} : Set (LatticePoint d)) ×ˢ prefixNextEvent) =
        histNextEvent ∩ {ξ : ℕ → LatticePoint d | endpoint ξ = y} := by
    ext ξ
    simp [endpoint, prefixN, prefixNextEvent, prefixR, histNextEvent,
      Preorder.frestrictLe_apply, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
  have hcond_prefix :
      ownerEndpointConditionedPrefixKernelIic P N x y prefixEvent =
        μ (histEvent ∩ {ξ : ℕ → LatticePoint d | endpoint ξ = y}) *
          ((μ.map endpoint) ({y} : Set (LatticePoint d)))⁻¹ := by
    rw [ownerEndpointConditionedPrefixKernelIic]
    rw [condDistrib_apply_of_ne_zero
      (μ := μ) (X := endpoint) (Y := prefixN) (hY := Preorder.measurable_frestrictLe N) y hy_row]
    rw [Measure.map_apply (by fun_prop) ((measurableSet_singleton y).prod hprefixEvent_meas)]
    exact congrArg (fun s : Set (ℕ → LatticePoint d) ↦ μ s) hprefix_rect
  have hcond_prefixNext :
      ownerEndpointConditionedPrefixKernelIic P N x y prefixNextEvent =
        μ (histNextEvent ∩ {ξ : ℕ → LatticePoint d | endpoint ξ = y}) *
          ((μ.map endpoint) ({y} : Set (LatticePoint d)))⁻¹ := by
    rw [ownerEndpointConditionedPrefixKernelIic]
    rw [condDistrib_apply_of_ne_zero
      (μ := μ) (X := endpoint) (Y := prefixN) (hY := Preorder.measurable_frestrictLe N) y hy_row]
    rw [Measure.map_apply (by fun_prop) ((measurableSet_singleton y).prod hprefixNextEvent_meas)]
    exact congrArg (fun s : Set (ℕ → LatticePoint d) ↦ μ s) hprefixNext_rect
  -- Proof comment: after expanding both conditioned masses through `condDistrib`, the common
  -- endpoint normalizing factor cancels and the remaining equality is exactly the unconditional
  -- bridge factorization through `histEvent`, `histNextEvent`, and the owner rows.
  calc
    ownerEndpointConditionedPrefixKernelIic P N x y prefixNextEvent *
        ((dirac_convolution_kernel ν.toMeasure ^ (N - r)) curr) ({y} : Set (LatticePoint d)) =
      (μ (histNextEvent ∩ {ξ : ℕ → LatticePoint d | endpoint ξ = y}) *
          ((μ.map endpoint) ({y} : Set (LatticePoint d)))⁻¹) *
        ((dirac_convolution_kernel ν.toMeasure ^ (N - r)) curr) ({y} : Set (LatticePoint d)) := by
          rw [hcond_prefixNext]
    _ =
      (((dirac_convolution_kernel ν.toMeasure ^ (N - (r + 1))) w)
          ({y} : Set (LatticePoint d)) * μ histNextEvent) *
        ((μ.map endpoint) ({y} : Set (LatticePoint d)))⁻¹ *
        ((dirac_convolution_kernel ν.toMeasure ^ (N - r)) curr) ({y} : Set (LatticePoint d)) := by
          rw [hhistNext_endpoint]
          ring_nf
    _ =
      (((dirac_convolution_kernel ν.toMeasure ^ (N - (r + 1))) w)
          ({y} : Set (LatticePoint d)) *
        (dirac_convolution_kernel ν.toMeasure curr ({w} : Set (LatticePoint d)) * μ histEvent)) *
        ((μ.map endpoint) ({y} : Set (LatticePoint d)))⁻¹ *
        ((dirac_convolution_kernel ν.toMeasure ^ (N - r)) curr) ({y} : Set (LatticePoint d)) := by
          rw [hhistNext_step]
    _ =
      (((dirac_convolution_kernel ν.toMeasure ^ (N - (r + 1))) w)
          ({y} : Set (LatticePoint d)) *
        (ownerEndpointConditionedPrefixKernelIic P N x y prefixEvent *
          ((μ.map endpoint) ({y} : Set (LatticePoint d)))) *
        dirac_convolution_kernel ν.toMeasure curr ({w} : Set (LatticePoint d))) *
        ((μ.map endpoint) ({y} : Set (LatticePoint d)))⁻¹ := by
          rw [hcond_prefix]
          rw [hhist_endpoint]
          ring_nf
    _ =
      ownerEndpointConditionedPrefixKernelIic P N x y prefixEvent *
        dirac_convolution_kernel ν.toMeasure curr ({w} : Set (LatticePoint d)) *
        ((dirac_convolution_kernel ν.toMeasure ^ (N - (r + 1))) w)
          ({y} : Set (LatticePoint d)) := by
          have hcancel :
              (μ.map endpoint) ({y} : Set (LatticePoint d)) *
                  ((μ.map endpoint) ({y} : Set (LatticePoint d)))⁻¹ = 1 := by
            exact ENNReal.mul_inv_cancel hy_row (measure_ne_top _ _)
          rw [hcancel]
          ring_nf

/-- Helper for Theorem 18.8: under the paired endpoint bridge, the second sampled prefix ends at
the prescribed second endpoint whenever that endpoint has positive owner `N`-step mass. -/
private theorem pairedEndpointBridgeKernelIic_snd_endpoint_of_transition_ne_zero
    {d : ℕ} {ν : PMF (LatticePoint d)}
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (hP :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P Function.eval)
    (N : ℕ) (x₁ x₂ y₁ y₂ : LatticePoint d)
    (hy₂ : ((dirac_convolution_kernel ν.toMeasure ^ N) x₂) ({y₂} : Set (LatticePoint d)) ≠ 0) :
    pairedEndpointBridgeKernelIic P N x₁ x₂ (y₁, y₂)
        {z : (Finset.Iic N → LatticePoint d) × (Finset.Iic N → LatticePoint d) |
          z.2 ⟨N, Finset.mem_Iic.2 le_rfl⟩ = y₂} = 1 := by
  let endFiber :
      Set (Finset.Iic N → LatticePoint d) :=
    {ξ | ξ ⟨N, Finset.mem_Iic.2 le_rfl⟩ = y₂}
  have hendFiber_meas : MeasurableSet endFiber := by
    -- Proof comment: the second endpoint event is again a one-coordinate equality on a discrete
    -- prefix space.
    exact measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  have hpreimage :
      {z : (Finset.Iic N → LatticePoint d) × (Finset.Iic N → LatticePoint d) |
          z.2 ⟨N, Finset.mem_Iic.2 le_rfl⟩ = y₂} =
        Prod.snd ⁻¹' endFiber := by
    -- Proof comment: projecting to the second prefix coordinate identifies the corresponding
    -- bridge endpoint fiber.
    ext z
    simp [endFiber]
  rw [hpreimage]
  rw [← Measure.map_apply measurable_snd hendFiber_meas]
  rw [pairedEndpointBridgeKernelIic_snd_row]
  exact
    ownerEndpointConditionedPrefixKernelIic_endpoint_of_transition_ne_zero
      (hP := hP) N x₂ y₂ hy₂

/-- Helper for Theorem 18.8: each paired endpoint bridge row is a probability measure. -/
private lemma pairedEndpointBridgeKernelIic_isProbabilityMeasure
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (N : ℕ) (x₁ x₂ : LatticePoint d) (y : LatticePoint d × LatticePoint d) :
    IsProbabilityMeasure (pairedEndpointBridgeKernelIic P N x₁ x₂ y) := by
  by_cases h : (x₁, y.1) = (x₂, y.2)
  · -- Proof comment: on the diagonal branch, the row is the image of a conditioned prefix
    -- probability measure under the diagonal embedding.
    rw [pairedEndpointBridgeKernelIic, dif_pos h]
    infer_instance
  · -- Proof comment: off the diagonal branch, the row is the product of the two conditioned
    -- prefix probability measures.
    rw [pairedEndpointBridgeKernelIic, dif_neg h]
    infer_instance

/-- Helper for Theorem 18.8: a fixed endpoint skeleton determines an independent product law on
the sequence of paired block bridges. -/
private noncomputable def pairedEndpointBridgeTrajectoryMeasure
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (N : ℕ) (ζ : ℕ → LatticePoint d × LatticePoint d) :
    Measure
      (ℕ →
        ((Finset.Iic N → LatticePoint d) × (Finset.Iic N → LatticePoint d))) :=
  let μblock :
      ℕ → Measure
        ((Finset.Iic N → LatticePoint d) × (Finset.Iic N → LatticePoint d)) :=
    fun q ↦ pairedEndpointBridgeKernelIic P N (ζ q).1 (ζ q).2 (ζ (q + 1))
  letI : ∀ q, IsProbabilityMeasure (μblock q) := fun q ↦
    pairedEndpointBridgeKernelIic_isProbabilityMeasure
      (P := P) (N := N) (x₁ := (ζ q).1) (x₂ := (ζ q).2) (y := ζ (q + 1))
  Measure.infinitePi μblock

/-- Helper for Theorem 18.8: combine an endpoint-coupling witness with the block-bridge kernel
into the product measure used for the Step 3 unit-time lift. -/
private noncomputable def pairedEndpointBridgeLiftMeasure
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    {Ωend : Type*} [MeasurableSpace Ωend]
    (Pend : LatticePoint d × LatticePoint d → ProbabilityMeasure Ωend)
    (N : ℕ) (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (x y : LatticePoint d) :
    Measure
      (Ωend ×
        (ℕ →
          ((Finset.Iic N → LatticePoint d) × (Finset.Iic N → LatticePoint d)))) :=
  (Pend (x, y) : Measure Ωend) ⊗ₘ
    (fun ωend ↦ pairedEndpointBridgeTrajectoryMeasure P N (fun q ↦ Zend q ωend))

/-- Helper for Theorem 18.8: splice the endpoint skeleton with the sampled bridge blocks to get
the unit-time pair process used in the genuine block case. -/
private noncomputable def pairedEndpointBridgeLiftProcess
    {d : ℕ} {Ωend : Type*} [MeasurableSpace Ωend]
    (N : ℕ) (hN : 0 < N)
    (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d) :
    ℕ →
      (Ωend ×
        (ℕ →
          ((Finset.Iic N → LatticePoint d) × (Finset.Iic N → LatticePoint d)))) →
        LatticePoint d × LatticePoint d
  | n, θ =>
      let q := n / N
      let r := n % N
      if hr : r = 0 then
        Zend q θ.1
      else
        let hr_le : r ≤ N := Nat.le_of_lt (Nat.mod_lt _ hN)
        (((θ.2 q).1) ⟨r, hr_le⟩, ((θ.2 q).2) ⟨r, hr_le⟩)

/-- Helper for Theorem 18.8: at block boundaries, the spliced unit-time process agrees with the
endpoint skeleton. -/
private lemma pairedEndpointBridgeLiftProcess_boundary
    {d : ℕ} {Ωend : Type*} [MeasurableSpace Ωend]
    (N : ℕ) (hN : 0 < N)
    (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (q : ℕ)
    (θ :
      Ωend ×
        (ℕ →
          ((Finset.Iic N → LatticePoint d) × (Finset.Iic N → LatticePoint d)))) :
    pairedEndpointBridgeLiftProcess N hN Zend (q * N) θ = Zend q θ.1 := by
  -- Proof comment: the remainder at a block boundary is `0`, so the spliced process reads the
  -- block endpoint directly from `Zend`.
  simp [pairedEndpointBridgeLiftProcess, Nat.mul_div_right, Nat.mul_mod_right]

/-- Helper for Theorem 18.8: away from block boundaries, the spliced unit-time process reads the
corresponding interior point of the sampled bridge block. -/
private lemma pairedEndpointBridgeLiftProcess_interior
    {d : ℕ} {Ωend : Type*} [MeasurableSpace Ωend]
    (N : ℕ) (hN : 0 < N)
    (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (q r : ℕ) (hr_pos : 0 < r) (hr_lt : r < N)
    (θ :
      Ωend ×
        (ℕ →
          ((Finset.Iic N → LatticePoint d) × (Finset.Iic N → LatticePoint d)))) :
    pairedEndpointBridgeLiftProcess N hN Zend (q * N + r) θ =
      (((θ.2 q).1) ⟨r, Nat.le_of_lt hr_lt⟩, ((θ.2 q).2) ⟨r, Nat.le_of_lt hr_lt⟩) := by
  have hdiv : (q * N + r) / N = q := by
    omega
  have hmod : (q * N + r) % N = r := by
    omega
  -- Proof comment: for `0 < r < N`, Euclidean division identifies the enclosing block `q` and
  -- the interior bridge coordinate `r`.
  simp [pairedEndpointBridgeLiftProcess, hdiv, hmod, hr_pos.ne']

/-- Helper for Theorem 18.8: under the block-bridge trajectory law, the `q`-th sampled block has
exactly the prescribed paired endpoint bridge row as its marginal. -/
private theorem pairedEndpointBridgeTrajectoryMeasure_blockMarginal
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (N : ℕ) (ζ : ℕ → LatticePoint d × LatticePoint d) (q : ℕ) :
    Measure.map (Function.eval q) (pairedEndpointBridgeTrajectoryMeasure P N ζ) =
      pairedEndpointBridgeKernelIic P N (ζ q).1 (ζ q).2 (ζ (q + 1)) := by
  let μblock :
      ℕ → Measure
        ((Finset.Iic N → LatticePoint d) × (Finset.Iic N → LatticePoint d)) :=
    fun n ↦ pairedEndpointBridgeKernelIic P N (ζ n).1 (ζ n).2 (ζ (n + 1))
  letI : ∀ n, IsProbabilityMeasure (μblock n) := fun n ↦
    pairedEndpointBridgeKernelIic_isProbabilityMeasure
      (P := P) (N := N) (x₁ := (ζ n).1) (x₂ := (ζ n).2) (y := ζ (n + 1))
  -- Proof comment: the trajectory measure is an infinite product of the block rows, so each
  -- coordinate marginal is the corresponding block row itself.
  simpa [pairedEndpointBridgeTrajectoryMeasure, μblock] using
    (Measure.infinitePi_map_eval (μ := μblock) q)

/-- Helper for Theorem 18.8: the first coordinate of the `q`-th sampled bridge block has the
first conditioned prefix row as its marginal. -/
private theorem pairedEndpointBridgeTrajectoryMeasure_fstBlockMarginal
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (N : ℕ) (ζ : ℕ → LatticePoint d × LatticePoint d) (q : ℕ) :
    Measure.map (fun ξ ↦ (ξ q).1) (pairedEndpointBridgeTrajectoryMeasure P N ζ) =
      ownerEndpointConditionedPrefixKernelIic P N (ζ q).1 ((ζ (q + 1)).1) := by
  -- Proof comment: first project to the `q`-th block and then to the first bridge coordinate.
  rw [← Measure.map_map (μ := pairedEndpointBridgeTrajectoryMeasure P N ζ)
    (f := Function.eval q) (g := Prod.fst) (hf := measurable_pi_apply q) (hg := measurable_fst)]
  rw [pairedEndpointBridgeTrajectoryMeasure_blockMarginal, pairedEndpointBridgeKernelIic_fst_row]

/-- Helper for Theorem 18.8: the second coordinate of the `q`-th sampled bridge block has the
second conditioned prefix row as its marginal. -/
private theorem pairedEndpointBridgeTrajectoryMeasure_sndBlockMarginal
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (N : ℕ) (ζ : ℕ → LatticePoint d × LatticePoint d) (q : ℕ) :
    Measure.map (fun ξ ↦ (ξ q).2) (pairedEndpointBridgeTrajectoryMeasure P N ζ) =
      ownerEndpointConditionedPrefixKernelIic P N (ζ q).2 ((ζ (q + 1)).2) := by
  -- Proof comment: the second block marginal is obtained by the same two-step projection.
  rw [← Measure.map_map (μ := pairedEndpointBridgeTrajectoryMeasure P N ζ)
    (f := Function.eval q) (g := Prod.snd) (hf := measurable_pi_apply q) (hg := measurable_snd)]
  rw [pairedEndpointBridgeTrajectoryMeasure_blockMarginal, pairedEndpointBridgeKernelIic_snd_row]

/-- Helper for Theorem 18.8: under the lifted Step 3 measure, the first sampled bridge block over
the `q`-th endpoint interval has the first conditioned-prefix row as its marginal. -/
private theorem pairedEndpointBridgeLiftMeasure_fstBlockMarginal
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    {Ωend : Type*} [MeasurableSpace Ωend]
    (Pend : LatticePoint d × LatticePoint d → ProbabilityMeasure Ωend)
    (N : ℕ) (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (x y : LatticePoint d) (q : ℕ) :
    Measure.map
        (fun θ :
          Ωend ×
            (ℕ →
              ((Finset.Iic N → LatticePoint d) ×
                (Finset.Iic N → LatticePoint d))) ↦
          (θ.1, (θ.2 q).1))
        (pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y) =
      ((Pend (x, y) : Measure Ωend) ⊗ₘ
        fun ωend ↦
          ownerEndpointConditionedPrefixKernelIic P N
            (Zend q ωend).1 ((Zend (q + 1) ωend).1)) := by
  have hkernel :
      (fun ωend ↦ pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend)).map
          (fun ξ ↦ (ξ q).1) =
        (fun ωend ↦
          ownerEndpointConditionedPrefixKernelIic P N
            (Zend q ωend).1 ((Zend (q + 1) ωend).1)) := by
    ext ωend s hs
    -- Proof comment: after fixing the endpoint skeleton, the `q`-th first bridge block marginal
    -- is exactly the conditioned owner prefix row already identified above.
    rw [Kernel.map_apply (by fun_prop) hs]
    simpa using
      congrArg (fun μ : Measure (Finset.Iic N → LatticePoint d) ↦ μ s)
        (pairedEndpointBridgeTrajectoryMeasure_fstBlockMarginal
          (P := P) N (ζ := fun n ↦ Zend n ωend) q)
  calc
    Measure.map
        (fun θ :
          Ωend ×
            (ℕ →
              ((Finset.Iic N → LatticePoint d) ×
                (Finset.Iic N → LatticePoint d))) ↦
          (θ.1, (θ.2 q).1))
        (pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y) =
      ((Pend (x, y) : Measure Ωend) ⊗ₘ
        ((fun ωend ↦ pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend)).map
          (fun ξ ↦ (ξ q).1))) := by
          -- Proof comment: the lifted measure is a composition-product over the endpoint
          -- skeleton, so mapping out the first sampled bridge block is `Measure.compProd_map`.
          rw [pairedEndpointBridgeLiftMeasure]
          simpa using
            (Measure.compProd_map
              (μ := (Pend (x, y) : Measure Ωend))
              (κ := fun ωend ↦ pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend))
              (f := fun ξ ↦ (ξ q).1)
              (hf := by fun_prop)).symm
    _ = ((Pend (x, y) : Measure Ωend) ⊗ₘ
          fun ωend ↦
            ownerEndpointConditionedPrefixKernelIic P N
              (Zend q ωend).1 ((Zend (q + 1) ωend).1)) := by
          rw [hkernel]

/-- Helper for Theorem 18.8: under the lifted Step 3 measure, the second sampled bridge block
over the `q`-th endpoint interval has the second conditioned-prefix row as its marginal. -/
private theorem pairedEndpointBridgeLiftMeasure_sndBlockMarginal
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    {Ωend : Type*} [MeasurableSpace Ωend]
    (Pend : LatticePoint d × LatticePoint d → ProbabilityMeasure Ωend)
    (N : ℕ) (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (x y : LatticePoint d) (q : ℕ) :
    Measure.map
        (fun θ :
          Ωend ×
            (ℕ →
              ((Finset.Iic N → LatticePoint d) ×
                (Finset.Iic N → LatticePoint d))) ↦
          (θ.1, (θ.2 q).2))
        (pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y) =
      ((Pend (x, y) : Measure Ωend) ⊗ₘ
        fun ωend ↦
          ownerEndpointConditionedPrefixKernelIic P N
            (Zend q ωend).2 ((Zend (q + 1) ωend).2)) := by
  have hkernel :
      (fun ωend ↦ pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend)).map
          (fun ξ ↦ (ξ q).2) =
        (fun ωend ↦
          ownerEndpointConditionedPrefixKernelIic P N
            (Zend q ωend).2 ((Zend (q + 1) ωend).2)) := by
    ext ωend s hs
    -- Proof comment: the second bridge coordinate has the symmetric conditioned-prefix marginal.
    rw [Kernel.map_apply (by fun_prop) hs]
    simpa using
      congrArg (fun μ : Measure (Finset.Iic N → LatticePoint d) ↦ μ s)
        (pairedEndpointBridgeTrajectoryMeasure_sndBlockMarginal
          (P := P) N (ζ := fun n ↦ Zend n ωend) q)
  calc
    Measure.map
        (fun θ :
          Ωend ×
            (ℕ →
              ((Finset.Iic N → LatticePoint d) ×
                (Finset.Iic N → LatticePoint d))) ↦
          (θ.1, (θ.2 q).2))
        (pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y) =
      ((Pend (x, y) : Measure Ωend) ⊗ₘ
        ((fun ωend ↦ pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend)).map
          (fun ξ ↦ (ξ q).2))) := by
          -- Proof comment: the same `compProd_map` normalization works for the second block
          -- coordinate.
          rw [pairedEndpointBridgeLiftMeasure]
          simpa using
            (Measure.compProd_map
              (μ := (Pend (x, y) : Measure Ωend))
              (κ := fun ωend ↦ pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend))
              (f := fun ξ ↦ (ξ q).2)
              (hf := by fun_prop)).symm
    _ = ((Pend (x, y) : Measure Ωend) ⊗ₘ
          fun ωend ↦
            ownerEndpointConditionedPrefixKernelIic P N
              (Zend q ωend).2 ((Zend (q + 1) ωend).2)) := by
          rw [hkernel]

/-- Helper for Theorem 18.8: at a block boundary, the first lifted coordinate is just the first
endpoint-skeleton coordinate at that boundary time. -/
private theorem pairedEndpointBridgeLiftMeasure_fstBoundaryMarginal
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    {Ωend : Type*} [MeasurableSpace Ωend]
    (Pend : LatticePoint d × LatticePoint d → ProbabilityMeasure Ωend)
    (N : ℕ) (hN : 0 < N)
    (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (x y : LatticePoint d) (q : ℕ) :
    Measure.map
        (fun θ :
          Ωend ×
            (ℕ →
              ((Finset.Iic N → LatticePoint d) ×
                (Finset.Iic N → LatticePoint d))) ↦
          (θ.1, (pairedEndpointBridgeLiftProcess N hN Zend (q * N) θ).1))
        (pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y) =
      Measure.map
        (fun ωend : Ωend ↦ (ωend, (Zend q ωend).1))
        (Pend (x, y) : Measure Ωend) := by
  -- Proof comment: at a block boundary the lifted process reads the endpoint skeleton, so the
  -- map factors through `Prod.fst` and the first marginal of the composition-product measure.
  have hpoint :
      (fun θ :
        Ωend ×
          (ℕ →
            ((Finset.Iic N → LatticePoint d) ×
              (Finset.Iic N → LatticePoint d))) ↦
        (θ.1, (pairedEndpointBridgeLiftProcess N hN Zend (q * N) θ).1)) =
        (fun θ :
          Ωend ×
            (ℕ →
              ((Finset.Iic N → LatticePoint d) ×
                (Finset.Iic N → LatticePoint d))) ↦
          (θ.1, (Zend q θ.1).1)) := by
    funext θ
    simp [pairedEndpointBridgeLiftProcess_boundary, hN]
  rw [hpoint]
  rw [← Measure.map_map
    (μ := pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y)
    (f := Prod.fst)
    (g := fun ωend : Ωend ↦ (ωend, (Zend q ωend).1))
    (hf := measurable_fst) (hg := by fun_prop)]
  rw [pairedEndpointBridgeLiftMeasure]
  simpa [Measure.fst] using
    congrArg
      (fun μ : Measure Ωend ↦
        Measure.map (fun ωend : Ωend ↦ (ωend, (Zend q ωend).1)) μ)
      (Measure.fst_compProd
        (μ := (Pend (x, y) : Measure Ωend))
        (κ := fun ωend ↦ pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend)))

/-- Helper for Theorem 18.8: at a block boundary, the second lifted coordinate is just the second
endpoint-skeleton coordinate at that boundary time. -/
private theorem pairedEndpointBridgeLiftMeasure_sndBoundaryMarginal
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    {Ωend : Type*} [MeasurableSpace Ωend]
    (Pend : LatticePoint d × LatticePoint d → ProbabilityMeasure Ωend)
    (N : ℕ) (hN : 0 < N)
    (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (x y : LatticePoint d) (q : ℕ) :
    Measure.map
        (fun θ :
          Ωend ×
            (ℕ →
              ((Finset.Iic N → LatticePoint d) ×
                (Finset.Iic N → LatticePoint d))) ↦
          (θ.1, (pairedEndpointBridgeLiftProcess N hN Zend (q * N) θ).2))
        (pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y) =
      Measure.map
        (fun ωend : Ωend ↦ (ωend, (Zend q ωend).2))
        (Pend (x, y) : Measure Ωend) := by
  -- Proof comment: the second coordinate has the same boundary normalization because the whole
  -- lifted pair process equals the endpoint skeleton at times divisible by `N`.
  have hpoint :
      (fun θ :
        Ωend ×
          (ℕ →
            ((Finset.Iic N → LatticePoint d) ×
              (Finset.Iic N → LatticePoint d))) ↦
        (θ.1, (pairedEndpointBridgeLiftProcess N hN Zend (q * N) θ).2)) =
        (fun θ :
          Ωend ×
            (ℕ →
              ((Finset.Iic N → LatticePoint d) ×
                (Finset.Iic N → LatticePoint d))) ↦
          (θ.1, (Zend q θ.1).2)) := by
    funext θ
    simp [pairedEndpointBridgeLiftProcess_boundary, hN]
  rw [hpoint]
  rw [← Measure.map_map
    (μ := pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y)
    (f := Prod.fst)
    (g := fun ωend : Ωend ↦ (ωend, (Zend q ωend).2))
    (hf := measurable_fst) (hg := by fun_prop)]
  rw [pairedEndpointBridgeLiftMeasure]
  simpa [Measure.fst] using
    congrArg
      (fun μ : Measure Ωend ↦
        Measure.map (fun ωend : Ωend ↦ (ωend, (Zend q ωend).2)) μ)
      (Measure.fst_compProd
        (μ := (Pend (x, y) : Measure Ωend))
        (κ := fun ωend ↦ pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend)))

/-- Helper for Theorem 18.8: at an interior time `q * N + r`, the first lifted coordinate is the
`r`-th point of the first conditioned bridge prefix in block `q`. -/
private theorem pairedEndpointBridgeLiftMeasure_fstInteriorMarginal
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    {Ωend : Type*} [MeasurableSpace Ωend]
    (Pend : LatticePoint d × LatticePoint d → ProbabilityMeasure Ωend)
    (N : ℕ) (hN : 0 < N)
    (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (x y : LatticePoint d) (q r : ℕ) (hr_pos : 0 < r) (hr_lt : r < N) :
    Measure.map
        (fun θ :
          Ωend ×
            (ℕ →
              ((Finset.Iic N → LatticePoint d) ×
                (Finset.Iic N → LatticePoint d))) ↦
          (θ.1, (pairedEndpointBridgeLiftProcess N hN Zend (q * N + r) θ).1))
        (pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y) =
      Measure.map
        (fun z : Ωend × (Finset.Iic N → LatticePoint d) ↦
          (z.1, z.2 ⟨r, Nat.le_of_lt hr_lt⟩))
        (((Pend (x, y) : Measure Ωend) ⊗ₘ
          fun ωend ↦
            ownerEndpointConditionedPrefixKernelIic P N
              (Zend q ωend).1 ((Zend (q + 1) ωend).1))) := by
  -- Proof comment: away from the boundary, the lifted process reads the `r`-th coordinate of the
  -- sampled first bridge block, so the claim is a direct map-map consequence of the first block
  -- marginal theorem.
  have hpoint :
      (fun θ :
        Ωend ×
          (ℕ →
            ((Finset.Iic N → LatticePoint d) ×
              (Finset.Iic N → LatticePoint d))) ↦
        (θ.1, (pairedEndpointBridgeLiftProcess N hN Zend (q * N + r) θ).1)) =
        (fun θ :
          Ωend ×
            (ℕ →
              ((Finset.Iic N → LatticePoint d) ×
                (Finset.Iic N → LatticePoint d))) ↦
          (θ.1, ((θ.2 q).1) ⟨r, Nat.le_of_lt hr_lt⟩)) := by
    funext θ
    simp [pairedEndpointBridgeLiftProcess_interior, hN, hr_pos, hr_lt]
  rw [hpoint]
  rw [← Measure.map_map
    (μ := pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y)
    (f := fun θ :
      Ωend ×
        (ℕ →
          ((Finset.Iic N → LatticePoint d) ×
            (Finset.Iic N → LatticePoint d))) ↦ (θ.1, (θ.2 q).1))
    (g := fun z : Ωend × (Finset.Iic N → LatticePoint d) ↦
      (z.1, z.2 ⟨r, Nat.le_of_lt hr_lt⟩))
    (hf := by fun_prop) (hg := by fun_prop)]
  rw [pairedEndpointBridgeLiftMeasure_fstBlockMarginal]

/-- Helper for Theorem 18.8: at an interior time `q * N + r`, the second lifted coordinate is the
`r`-th point of the second conditioned bridge prefix in block `q`. -/
private theorem pairedEndpointBridgeLiftMeasure_sndInteriorMarginal
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    {Ωend : Type*} [MeasurableSpace Ωend]
    (Pend : LatticePoint d × LatticePoint d → ProbabilityMeasure Ωend)
    (N : ℕ) (hN : 0 < N)
    (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (x y : LatticePoint d) (q r : ℕ) (hr_pos : 0 < r) (hr_lt : r < N) :
    Measure.map
        (fun θ :
          Ωend ×
            (ℕ →
              ((Finset.Iic N → LatticePoint d) ×
                (Finset.Iic N → LatticePoint d))) ↦
          (θ.1, (pairedEndpointBridgeLiftProcess N hN Zend (q * N + r) θ).2))
        (pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y) =
      Measure.map
        (fun z : Ωend × (Finset.Iic N → LatticePoint d) ↦
          (z.1, z.2 ⟨r, Nat.le_of_lt hr_lt⟩))
        (((Pend (x, y) : Measure Ωend) ⊗ₘ
          fun ωend ↦
            ownerEndpointConditionedPrefixKernelIic P N
              (Zend q ωend).2 ((Zend (q + 1) ωend).2))) := by
  -- Proof comment: the second interior coordinate is normalized in the same way via the second
  -- conditioned-prefix block marginal.
  have hpoint :
      (fun θ :
        Ωend ×
          (ℕ →
            ((Finset.Iic N → LatticePoint d) ×
              (Finset.Iic N → LatticePoint d))) ↦
        (θ.1, (pairedEndpointBridgeLiftProcess N hN Zend (q * N + r) θ).2)) =
        (fun θ :
          Ωend ×
            (ℕ →
              ((Finset.Iic N → LatticePoint d) ×
                (Finset.Iic N → LatticePoint d))) ↦
          (θ.1, ((θ.2 q).2) ⟨r, Nat.le_of_lt hr_lt⟩)) := by
    funext θ
    simp [pairedEndpointBridgeLiftProcess_interior, hN, hr_pos, hr_lt]
  rw [hpoint]
  rw [← Measure.map_map
    (μ := pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y)
    (f := fun θ :
      Ωend ×
        (ℕ →
          ((Finset.Iic N → LatticePoint d) ×
            (Finset.Iic N → LatticePoint d))) ↦ (θ.1, (θ.2 q).2))
    (g := fun z : Ωend × (Finset.Iic N → LatticePoint d) ↦
      (z.1, z.2 ⟨r, Nat.le_of_lt hr_lt⟩))
    (hf := by fun_prop) (hg := by fun_prop)]
  rw [pairedEndpointBridgeLiftMeasure_sndBlockMarginal]

/-- Helper for Theorem 18.8: under the lifted Step 3 measure, the first lifted coordinate starts
at the prescribed first endpoint state. -/
private theorem pairedEndpointBridgeLiftMeasure_fstInitial
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    {Ωend : Type*} [MeasurableSpace Ωend]
    {p : LatticePoint d → LatticePoint d → ENNReal}
    (Pend : LatticePoint d × LatticePoint d → ProbabilityMeasure Ωend)
    {N : ℕ} (hN : 0 < N)
    (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (hEnd : IsMarkovCoupling p Pend Zend)
    (x y : LatticePoint d) :
    Measure.map
        (fun θ :
          Ωend ×
            (ℕ →
              ((Finset.Iic N → LatticePoint d) ×
                (Finset.Iic N → LatticePoint d))) ↦
          (pairedEndpointBridgeLiftProcess N hN Zend 0 θ).1)
        (pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y) =
      Measure.dirac x := by
  let μlift :=
    pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y
  -- Proof comment: first rewrite the time-`0` lifted coordinate through the boundary marginal,
  -- then use the endpoint-skeleton start law from the first coordinate of `hEnd`.
  calc
    Measure.map
        (fun θ :
          Ωend ×
            (ℕ →
              ((Finset.Iic N → LatticePoint d) ×
                (Finset.Iic N → LatticePoint d))) ↦
          (pairedEndpointBridgeLiftProcess N hN Zend 0 θ).1) μlift =
      Measure.map Prod.snd
        (Measure.map
          (fun θ :
            Ωend ×
              (ℕ →
                ((Finset.Iic N → LatticePoint d) ×
                  (Finset.Iic N → LatticePoint d))) ↦
            (θ.1, (pairedEndpointBridgeLiftProcess N hN Zend 0 θ).1)) μlift) := by
          rw [← Measure.map_map
            (μ := μlift)
            (f := fun θ :
              Ωend ×
                (ℕ →
                  ((Finset.Iic N → LatticePoint d) ×
                    (Finset.Iic N → LatticePoint d))) ↦
              (θ.1, (pairedEndpointBridgeLiftProcess N hN Zend 0 θ).1))
            (g := Prod.snd) (hf := by fun_prop) (hg := measurable_snd)]
          rfl
    _ =
      Measure.map Prod.snd
        (Measure.map
          (fun ωend : Ωend ↦ (ωend, (Zend 0 ωend).1))
          (Pend (x, y) : Measure Ωend)) := by
            rw [pairedEndpointBridgeLiftMeasure_fstBoundaryMarginal
              (P := P) (Pend := Pend) N hN Zend x y 0]
    _ = Measure.map (fun ωend : Ωend ↦ (Zend 0 ωend).1) (Pend (x, y) : Measure Ωend) := by
          rw [Measure.map_map
            (μ := (Pend (x, y) : Measure Ωend))
            (f := fun ωend : Ωend ↦ (ωend, (Zend 0 ωend).1))
            (g := Prod.snd) (hf := by fun_prop) (hg := measurable_snd)]
          rfl
    _ = Measure.dirac x := by
          simpa using (hEnd.fst_realization y).initial_eq x

/-- Helper for Theorem 18.8: under the lifted Step 3 measure, the second lifted coordinate starts
at the prescribed second endpoint state. -/
private theorem pairedEndpointBridgeLiftMeasure_sndInitial
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    {Ωend : Type*} [MeasurableSpace Ωend]
    {p : LatticePoint d → LatticePoint d → ENNReal}
    (Pend : LatticePoint d × LatticePoint d → ProbabilityMeasure Ωend)
    {N : ℕ} (hN : 0 < N)
    (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (hEnd : IsMarkovCoupling p Pend Zend)
    (x y : LatticePoint d) :
    Measure.map
        (fun θ :
          Ωend ×
            (ℕ →
              ((Finset.Iic N → LatticePoint d) ×
                (Finset.Iic N → LatticePoint d))) ↦
          (pairedEndpointBridgeLiftProcess N hN Zend 0 θ).2)
        (pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y) =
      Measure.dirac y := by
  let μlift :=
    pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y
  -- Proof comment: the second lifted coordinate uses the symmetric boundary marginal and the
  -- endpoint-skeleton start law for the second coordinate.
  calc
    Measure.map
        (fun θ :
          Ωend ×
            (ℕ →
              ((Finset.Iic N → LatticePoint d) ×
                (Finset.Iic N → LatticePoint d))) ↦
          (pairedEndpointBridgeLiftProcess N hN Zend 0 θ).2) μlift =
      Measure.map Prod.snd
        (Measure.map
          (fun θ :
            Ωend ×
              (ℕ →
                ((Finset.Iic N → LatticePoint d) ×
                  (Finset.Iic N → LatticePoint d))) ↦
            (θ.1, (pairedEndpointBridgeLiftProcess N hN Zend 0 θ).2)) μlift) := by
          rw [← Measure.map_map
            (μ := μlift)
            (f := fun θ :
              Ωend ×
                (ℕ →
                  ((Finset.Iic N → LatticePoint d) ×
                    (Finset.Iic N → LatticePoint d))) ↦
              (θ.1, (pairedEndpointBridgeLiftProcess N hN Zend 0 θ).2))
            (g := Prod.snd) (hf := by fun_prop) (hg := measurable_snd)]
          rfl
    _ =
      Measure.map Prod.snd
        (Measure.map
          (fun ωend : Ωend ↦ (ωend, (Zend 0 ωend).2))
          (Pend (x, y) : Measure Ωend)) := by
            rw [pairedEndpointBridgeLiftMeasure_sndBoundaryMarginal
              (P := P) (Pend := Pend) N hN Zend x y 0]
    _ = Measure.map (fun ωend : Ωend ↦ (Zend 0 ωend).2) (Pend (x, y) : Measure Ωend) := by
          rw [Measure.map_map
            (μ := (Pend (x, y) : Measure Ωend))
            (f := fun ωend : Ωend ↦ (ωend, (Zend 0 ωend).2))
            (g := Prod.snd) (hf := by fun_prop) (hg := measurable_snd)]
          rfl
    _ = Measure.dirac y := by
          simpa using (hEnd.snd_realization x).initial_eq y

/-- Helper for Theorem 18.8: if the first block endpoint row has positive owner mass, then the
first sampled bridge block ends at the prescribed first endpoint almost surely. -/
private theorem pairedEndpointBridgeTrajectoryMeasure_fstEndpoint_of_transition_ne_zero
    {d : ℕ} {ν : PMF (LatticePoint d)}
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (hP :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P Function.eval)
    (N : ℕ) (ζ : ℕ → LatticePoint d × LatticePoint d) (q : ℕ)
    (hy :
      ((dirac_convolution_kernel ν.toMeasure ^ N) (ζ q).1)
        ({(ζ (q + 1)).1} : Set (LatticePoint d)) ≠ 0) :
    pairedEndpointBridgeTrajectoryMeasure P N ζ
        {ξ |
          (ξ q).1 ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (ζ (q + 1)).1} = 1 := by
  let endFiber : Set (Finset.Iic N → LatticePoint d) :=
    {η | η ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (ζ (q + 1)).1}
  have hendFiber_meas : MeasurableSet endFiber := by
    -- Proof comment: the first endpoint event is a singleton condition on one discrete prefix
    -- coordinate.
    exact measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  have hpreimage :
      {ξ | (ξ q).1 ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (ζ (q + 1)).1} =
        (fun ξ ↦ (ξ q).1) ⁻¹' endFiber := by
    ext ξ
    simp [endFiber]
  rw [hpreimage]
  rw [← Measure.map_apply
    ((measurable_fst.comp (measurable_pi_apply q : Measurable fun ξ ↦ ξ q))) hendFiber_meas]
  rw [pairedEndpointBridgeTrajectoryMeasure_fstBlockMarginal]
  exact
    ownerEndpointConditionedPrefixKernelIic_endpoint_of_transition_ne_zero
      (hP := hP) N (ζ q).1 ((ζ (q + 1)).1) hy

/-- Helper for Theorem 18.8: if the first block endpoint row has positive owner mass, then the
first sampled bridge block starts at the prescribed first endpoint almost surely. -/
private theorem pairedEndpointBridgeTrajectoryMeasure_fstStart_of_transition_ne_zero
    {d : ℕ} {ν : PMF (LatticePoint d)}
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (hP :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P Function.eval)
    (N : ℕ) (ζ : ℕ → LatticePoint d × LatticePoint d) (q : ℕ)
    (hy :
      ((dirac_convolution_kernel ν.toMeasure ^ N) (ζ q).1)
        ({(ζ (q + 1)).1} : Set (LatticePoint d)) ≠ 0) :
    pairedEndpointBridgeTrajectoryMeasure P N ζ
        {ξ |
          (ξ q).1 ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = (ζ q).1} = 1 := by
  let startFiber : Set (Finset.Iic N → LatticePoint d) :=
    {η | η ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = (ζ q).1}
  have hstartFiber_meas : MeasurableSet startFiber := by
    -- Proof comment: the first-start event is again a one-coordinate equality on the discrete
    -- prefix space.
    exact measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  have hpreimage :
      {ξ | (ξ q).1 ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = (ζ q).1} =
        (fun ξ ↦ (ξ q).1) ⁻¹' startFiber := by
    ext ξ
    simp [startFiber]
  rw [hpreimage]
  rw [← Measure.map_apply
    ((measurable_fst.comp (measurable_pi_apply q : Measurable fun ξ ↦ ξ q))) hstartFiber_meas]
  rw [pairedEndpointBridgeTrajectoryMeasure_fstBlockMarginal]
  exact
    ownerEndpointConditionedPrefixKernelIic_start_of_transition_ne_zero
      (hP := hP) N (ζ q).1 ((ζ (q + 1)).1) hy

/-- Helper for Theorem 18.8: if the second block endpoint row has positive owner mass, then the
second sampled bridge block ends at the prescribed second endpoint almost surely. -/
private theorem pairedEndpointBridgeTrajectoryMeasure_sndEndpoint_of_transition_ne_zero
    {d : ℕ} {ν : PMF (LatticePoint d)}
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (hP :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P Function.eval)
    (N : ℕ) (ζ : ℕ → LatticePoint d × LatticePoint d) (q : ℕ)
    (hy :
      ((dirac_convolution_kernel ν.toMeasure ^ N) (ζ q).2)
        ({(ζ (q + 1)).2} : Set (LatticePoint d)) ≠ 0) :
    pairedEndpointBridgeTrajectoryMeasure P N ζ
        {ξ |
          (ξ q).2 ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (ζ (q + 1)).2} = 1 := by
  let endFiber : Set (Finset.Iic N → LatticePoint d) :=
    {η | η ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (ζ (q + 1)).2}
  have hendFiber_meas : MeasurableSet endFiber := by
    -- Proof comment: the second endpoint event is again a singleton condition on one discrete
    -- prefix coordinate.
    exact measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  have hpreimage :
      {ξ | (ξ q).2 ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (ζ (q + 1)).2} =
        (fun ξ ↦ (ξ q).2) ⁻¹' endFiber := by
    ext ξ
    simp [endFiber]
  rw [hpreimage]
  rw [← Measure.map_apply
    ((measurable_snd.comp (measurable_pi_apply q : Measurable fun ξ ↦ ξ q))) hendFiber_meas]
  rw [pairedEndpointBridgeTrajectoryMeasure_sndBlockMarginal]
  exact
    ownerEndpointConditionedPrefixKernelIic_endpoint_of_transition_ne_zero
      (hP := hP) N (ζ q).2 ((ζ (q + 1)).2) hy

/-- Helper for Theorem 18.8: if the second block endpoint row has positive owner mass, then the
second sampled bridge block starts at the prescribed second endpoint almost surely. -/
private theorem pairedEndpointBridgeTrajectoryMeasure_sndStart_of_transition_ne_zero
    {d : ℕ} {ν : PMF (LatticePoint d)}
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (hP :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P Function.eval)
    (N : ℕ) (ζ : ℕ → LatticePoint d × LatticePoint d) (q : ℕ)
    (hy :
      ((dirac_convolution_kernel ν.toMeasure ^ N) (ζ q).2)
        ({(ζ (q + 1)).2} : Set (LatticePoint d)) ≠ 0) :
    pairedEndpointBridgeTrajectoryMeasure P N ζ
        {ξ |
          (ξ q).2 ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = (ζ q).2} = 1 := by
  let startFiber : Set (Finset.Iic N → LatticePoint d) :=
    {η | η ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = (ζ q).2}
  have hstartFiber_meas : MeasurableSet startFiber := by
    -- Proof comment: the second-start event is the symmetric one-coordinate equality on the
    -- second prefix space.
    exact measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  have hpreimage :
      {ξ | (ξ q).2 ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = (ζ q).2} =
        (fun ξ ↦ (ξ q).2) ⁻¹' startFiber := by
    ext ξ
    simp [startFiber]
  rw [hpreimage]
  rw [← Measure.map_apply
    ((measurable_snd.comp (measurable_pi_apply q : Measurable fun ξ ↦ ξ q))) hstartFiber_meas]
  rw [pairedEndpointBridgeTrajectoryMeasure_sndBlockMarginal]
  exact
    ownerEndpointConditionedPrefixKernelIic_start_of_transition_ne_zero
      (hP := hP) N (ζ q).2 ((ζ (q + 1)).2) hy

/-- Helper for Theorem 18.8: if consecutive block boundary states are already diagonal, then the
sampled bridge block is diagonal almost surely. -/
private theorem pairedEndpointBridgeTrajectoryMeasure_diagBlock
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (N : ℕ) (ζ : ℕ → LatticePoint d × LatticePoint d) (q : ℕ)
    (hstart : (ζ q).1 = (ζ q).2) (hend : (ζ (q + 1)).1 = (ζ (q + 1)).2) :
    pairedEndpointBridgeTrajectoryMeasure P N ζ
        {ξ | (ξ q).1 = (ξ q).2} = 1 := by
  let diagSet :
      Set ((Finset.Iic N → LatticePoint d) × (Finset.Iic N → LatticePoint d)) :=
    {z | z.1 = z.2}
  have hdiag_meas : MeasurableSet diagSet := by
    -- Proof comment: equality of the two bridge prefixes is a measurable diagonal event on the
    -- discrete block space.
    exact measurableSet_eq_fun measurable_fst measurable_snd
  have hpreimage :
      {ξ | (ξ q).1 = (ξ q).2} = (Function.eval q) ⁻¹' diagSet := by
    ext ξ
    simp [diagSet]
  have hpair :
      ((ζ q).1, (ζ (q + 1)).1) = ((ζ q).2, (ζ (q + 1)).2) := by
    exact Prod.ext hstart hend
  rw [hpreimage]
  rw [← Measure.map_apply (measurable_pi_apply q) hdiag_meas]
  rw [pairedEndpointBridgeTrajectoryMeasure_blockMarginal]
  exact
    pairedEndpointBridgeKernelIic_diag_row
      (P := P) N (ζ q).1 (ζ q).2 ((ζ (q + 1)).1) ((ζ (q + 1)).2) hpair

/-- Helper for Theorem 18.8: if diagonal boundary states at consecutive block endpoints force the
entire block prefix to stay on the diagonal, then every unit-time disagreement after block `k`
already creates a boundary disagreement at or after block `k`. -/
private lemma unitTailDisagreement_subset_blockBoundaryTail
    {Ω E : Type*} (N k : ℕ) (hN : 0 < N)
    (Zend Z : ℕ → Ω → E × E)
    (hdiag :
      ∀ q r ω, r < N →
        (Zend q ω).1 = (Zend q ω).2 →
        (Zend (q + 1) ω).1 = (Zend (q + 1) ω).2 →
          (Z (q * N + r) ω).1 = (Z (q * N + r) ω).2) :
    (⋃ n ≥ k * N, {ω | (Z n ω).1 ≠ (Z n ω).2}) ⊆
      ⋃ q ≥ k, {ω | (Zend q ω).1 ≠ (Zend q ω).2} := by
  intro ω hω
  rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
  rcases Set.mem_iUnion.1 hn with ⟨hnk, hneq⟩
  let q := n / N
  let r := n % N
  have hqk : k ≤ q := by
    have hmod : n % N < N := Nat.mod_lt n hN
    have hdecomp : n / N * N + n % N = n := Nat.div_add_mod n N
    have hdiv : k ≤ n / N := by
      omega
    simpa [q] using hdiv
  by_contra hboundary
  have hboundary_diag : ∀ m ≥ k, (Zend m ω).1 = (Zend m ω).2 := by
    intro m hm
    by_contra hmneq
    exact hboundary <|
      Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨hm, hmneq⟩⟩
  have hr : r < N := by
    simpa [r] using Nat.mod_lt n hN
  have hq_diag : (Zend q ω).1 = (Zend q ω).2 :=
    hboundary_diag q hqk
  have hq1_diag : (Zend (q + 1) ω).1 = (Zend (q + 1) ω).2 :=
    hboundary_diag (q + 1) (Nat.le_trans hqk (Nat.le_succ q))
  have hdecomp : q * N + r = n := by
    simpa [q, r] using Nat.div_add_mod n N
  have hdiag_state :
      (Z n ω).1 = (Z n ω).2 := by
    simpa [hdecomp] using hdiag q r ω hr hq_diag hq1_diag
  exact hneq hdiag_state

/-- Helper for Theorem 18.8: taking measures of the block-diagonal containment turns the unit-time
tail disagreement into a monotone image of the boundary-tail disagreement. -/
private lemma unitTailDisagreement_measure_le_blockBoundaryTail
    {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N k : ℕ) (hN : 0 < N)
    (Zend Z : ℕ → Ω → E × E)
    (hdiag :
      ∀ q r ω, r < N →
        (Zend q ω).1 = (Zend q ω).2 →
        (Zend (q + 1) ω).1 = (Zend (q + 1) ω).2 →
          (Z (q * N + r) ω).1 = (Z (q * N + r) ω).2) :
    μ (⋃ n ≥ k * N, {ω | (Z n ω).1 ≠ (Z n ω).2}) ≤
      μ (⋃ q ≥ k, {ω | (Zend q ω).1 ≠ (Zend q ω).2}) := by
  -- Proof comment: the measure inequality is the direct monotonicity consequence of the set
  -- containment proved above.
  exact measure_mono <|
    unitTailDisagreement_subset_blockBoundaryTail
      (N := N) (k := k) hN Zend Z hdiag

/-- Helper for Theorem 18.8: once each diagonal pair of consecutive block endpoints forces the
sampled bridge block to stay on the diagonal almost surely, the unit-time disagreement tail of the
spliced bridge process is controlled by the endpoint-tail disagreement of the block skeleton. -/
private theorem pairedEndpointBridgeLift_tailDisagreement_tendsto_zero
    {d : ℕ} {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    {Ωend : Type*} [MeasurableSpace Ωend]
    {Pend : LatticePoint d × LatticePoint d → ProbabilityMeasure Ωend}
    {Zend : ℕ → Ωend → LatticePoint d × LatticePoint d}
    {p : LatticePoint d × LatticePoint d → LatticePoint d × LatticePoint d → ENNReal}
    {N : ℕ} (hN : 0 < N)
    (hEndSuccess : IsSuccessfulMarkovCoupling p Pend Zend)
    (x y : LatticePoint d) :
    Tendsto
      (fun n ↦
        pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y
          (⋃ m ≥ n,
            {θ |
              (pairedEndpointBridgeLiftProcess N hN Zend m θ).1 ≠
                (pairedEndpointBridgeLiftProcess N hN Zend m θ).2}))
      atTop (nhds 0) := by
  let Ωlift :=
    Ωend ×
      (ℕ →
        ((Finset.Iic N → LatticePoint d) × (Finset.Iic N → LatticePoint d)))
  let μend : Measure Ωend := (Pend (x, y) : Measure Ωend)
  let μlift : Measure Ωlift :=
    pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y
  let Z : ℕ → Ωlift → LatticePoint d × LatticePoint d :=
    pairedEndpointBridgeLiftProcess N hN Zend
  let boundaryTail : ℕ → Set Ωend := fun k ↦
    ⋃ q ≥ k, {ωend | (Zend q ωend).1 ≠ (Zend q ωend).2}
  let unitTail : ℕ → Set Ωlift := fun n ↦
    ⋃ m ≥ n, {θ | (Z m θ).1 ≠ (Z m θ).2}
  let badDiagBlock : ℕ → Set Ωlift := fun q ↦
    {θ |
      (Zend q θ.1).1 = (Zend q θ.1).2 ∧
        (Zend (q + 1) θ.1).1 = (Zend (q + 1) θ.1).2 ∧
          (θ.2 q).1 ≠ (θ.2 q).2}
  let hfstEnd := hEndSuccess.toIsMarkovCoupling.fst_realization y
  let hsndEnd := hEndSuccess.toIsMarkovCoupling.snd_realization x
  have hboundary_meas : ∀ k : ℕ, MeasurableSet (boundaryTail k) := by
    intro k
    refine MeasurableSet.iUnion fun q ↦ ?_
    refine MeasurableSet.iUnion fun _ ↦ ?_
    exact
      ((hfstEnd.measurable_process q).prodMk (hsndEnd.measurable_process q))
        (MeasurableSet.of_discrete :
          MeasurableSet {z : LatticePoint d × LatticePoint d | z.1 ≠ z.2})
  have hunit_meas : ∀ n : ℕ, MeasurableSet (unitTail n) := by
    intro n
    refine MeasurableSet.iUnion fun m ↦ ?_
    refine MeasurableSet.iUnion fun _ ↦ ?_
    exact MeasurableSet.of_discrete
  have hbad_meas : ∀ q : ℕ, MeasurableSet (badDiagBlock q) := by
    intro q
    exact MeasurableSet.of_discrete
  have hunit_subset : ∀ k : ℕ, unitTail (k * N) ⊆ Prod.fst ⁻¹' boundaryTail k ∪ ⋃ q ≥ k, badDiagBlock q := by
    intro k θ hθ
    by_cases hboundary : θ.1 ∈ boundaryTail k
    · exact Or.inl hboundary
    · rcases Set.mem_iUnion.1 hθ with ⟨n, hn⟩
      rcases Set.mem_iUnion.1 hn with ⟨hnk, hneq⟩
      let q : ℕ := n / N
      let r : ℕ := n % N
      have hqk : k ≤ q := by
        omega
      have hdiag_boundary : ∀ m ≥ k, (Zend m θ.1).1 = (Zend m θ.1).2 := by
        intro m hm
        by_contra hmneq
        exact hboundary <| Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨hm, hmneq⟩⟩
      have hqdiag : (Zend q θ.1).1 = (Zend q θ.1).2 :=
        hdiag_boundary q hqk
      have hq1diag : (Zend (q + 1) θ.1).1 = (Zend (q + 1) θ.1).2 :=
        hdiag_boundary (q + 1) (Nat.le_trans hqk (Nat.le_succ q))
      have hr_lt : r < N := by
        simpa [r] using Nat.mod_lt n hN
      by_cases hr0 : r = 0
      · have hdecomp : n = q * N := by
          omega
        have hboundary_eq :
            Z n θ = Zend q θ.1 := by
          simpa [Z, q, hdecomp] using
            pairedEndpointBridgeLiftProcess_boundary N hN Zend q θ
        exact (hneq <| by simpa [hboundary_eq] using hqdiag).elim
      · have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
        have hinterior :
            Z (q * N + r) θ =
              (((θ.2 q).1) ⟨r, Nat.le_of_lt hr_lt⟩, ((θ.2 q).2) ⟨r, Nat.le_of_lt hr_lt⟩) := by
          simpa [Z] using
            pairedEndpointBridgeLiftProcess_interior N hN Zend q r hr_pos hr_lt θ
        have hprefix_neq : (θ.2 q).1 ≠ (θ.2 q).2 := by
          intro hEq
          apply hneq
          have hdecomp : n = q * N + r := by
            omega
          rw [hdecomp, hinterior]
          simpa [hEq]
        exact Or.inr <|
          Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hqk, by
            exact ⟨hqdiag, hq1diag, hprefix_neq⟩⟩⟩
  have hbad_zero : ∀ q : ℕ, μlift (badDiagBlock q) = 0 := by
    intro q
    rw [pairedEndpointBridgeLiftMeasure, Measure.compProd_apply (hbad_meas q)]
    refine lintegral_eq_zero.2 ?_
    intro ωend
    have hsection :
        Prod.mk ωend ⁻¹' badDiagBlock q =
          if (Zend q ωend).1 = (Zend q ωend).2 ∧
              (Zend (q + 1) ωend).1 = (Zend (q + 1) ωend).2 then
            {ξ | (ξ q).1 ≠ (ξ q).2}
          else
            ∅ := by
      ext ξ
      by_cases hdiag :
          (Zend q ωend).1 = (Zend q ωend).2 ∧
            (Zend (q + 1) ωend).1 = (Zend (q + 1) ωend).2
      · simp [badDiagBlock, hdiag]
      · simp [badDiagBlock, hdiag]
    by_cases hdiag :
        (Zend q ωend).1 = (Zend q ωend).2 ∧
          (Zend (q + 1) ωend).1 = (Zend (q + 1) ωend).2
    · rcases hdiag with ⟨hqdiag, hq1diag⟩
      have hdiag_mass :
          pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend)
            {ξ | (ξ q).1 = (ξ q).2} = 1 := by
        exact pairedEndpointBridgeTrajectoryMeasure_diagBlock
          (P := P) N (ζ := fun n ↦ Zend n ωend) q hqdiag hq1diag
      have hneq_mass :
          pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend)
            {ξ | (ξ q).1 ≠ (ξ q).2} = 0 := by
        have hdiag_set_meas : MeasurableSet {ξ | (ξ q).1 = (ξ q).2} := by
          exact MeasurableSet.of_discrete
        have hcompl :
            {ξ | (ξ q).1 ≠ (ξ q).2} = ({ξ | (ξ q).1 = (ξ q).2} : Set _)ᶜ := by
          ext ξ
          simp
        rw [hcompl, measure_compl hdiag_set_meas, hdiag_mass]
        simp
      simp [hsection, hdiag, hneq_mass]
    · simp [hsection, hdiag]
  have hbadTail_zero : ∀ k : ℕ, μlift (⋃ q ≥ k, badDiagBlock q) = 0 := by
    intro k
    refine measure_iUnion_null fun q ↦ ?_
    refine measure_iUnion_null fun _ ↦ ?_
    exact hbad_zero q
  have hboundary_mass : ∀ k : ℕ, μlift (Prod.fst ⁻¹' boundaryTail k) = μend (boundaryTail k) := by
    intro k
    calc
      μlift (Prod.fst ⁻¹' boundaryTail k) = Measure.map Prod.fst μlift (boundaryTail k) := by
        symm
        exact Measure.map_apply measurable_fst (hboundary_meas k)
      _ = μend (boundaryTail k) := by
        have hfst :
            Measure.map Prod.fst μlift = μend := by
          simpa [μlift, pairedEndpointBridgeLiftMeasure, Measure.fst] using
            (Measure.fst_compProd
              (μ := μend)
              (κ := fun ωend ↦ pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend)))
        rw [hfst]
  have hblock_tail_le : ∀ k : ℕ, μlift (unitTail (k * N)) ≤ μend (boundaryTail k) := by
    intro k
    calc
      μlift (unitTail (k * N)) ≤ μlift (Prod.fst ⁻¹' boundaryTail k ∪ ⋃ q ≥ k, badDiagBlock q) := by
        exact measure_mono (hunit_subset k)
      _ ≤ μlift (Prod.fst ⁻¹' boundaryTail k) + μlift (⋃ q ≥ k, badDiagBlock q) := by
        exact measure_union_le _ _
      _ = μend (boundaryTail k) + 0 := by
        rw [hboundary_mass k, hbadTail_zero k]
      _ = μend (boundaryTail k) := by
        simp
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact (ENNReal.not_lt_zero ha).elim
  · intro ε hε
    have hboundary_small :
        ∀ᶠ k : ℕ in atTop, μend (boundaryTail k) < ε := by
      simpa [μend, boundaryTail] using hEndSuccess.tail_disagreement_tendsto_zero x y (Iio_mem_nhds hε)
    rcases Filter.eventually_atTop.1 hboundary_small with ⟨K, hK⟩
    filter_upwards [Filter.Eventually.ge_atTop (K * N)] with n hn
    have hmono :
        unitTail n ⊆ unitTail (K * N) := by
      intro θ hθ
      rcases Set.mem_iUnion.1 hθ with ⟨m, hm⟩
      rcases Set.mem_iUnion.1 hm with ⟨hmn, hneq⟩
      exact Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨Nat.le_trans hn hmn, hneq⟩⟩
    calc
      μlift (unitTail n) ≤ μlift (unitTail (K * N)) := by
        exact measure_mono hmono
      _ ≤ μend (boundaryTail K) := hblock_tail_le K
      _ < ε := hK K le_rfl

/-- Helper for Theorem 18.8: once the auxiliary block law `μN` is identified with the origin row
of the `N`-step owner kernel, its translated singleton rows are exactly the genuine `N`-step
singleton masses. -/
private lemma ownerBlockStepMass_eq_powSingletonMass
    {d : ℕ} {ν μN : PMF (LatticePoint d)} {N : ℕ}
    (hμN :
      μN.toMeasure = (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d))
    (x y : LatticePoint d) :
    dirac_convolution_kernel μN.toMeasure x ({y} : Set (LatticePoint d)) =
      ((dirac_convolution_kernel ν.toMeasure ^ N) x) ({y} : Set (LatticePoint d)) := by
  -- Proof comment: rewrite the auxiliary row through the identified origin law and then use the
  -- translation formula for `N`-step convolution-kernel singleton masses.
  rw [hμN]
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
  have hpreimage :
      (fun z : LatticePoint d ↦ x + z) ⁻¹' ({y} : Set (LatticePoint d)) = {y - x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hz)
    · intro hz
      exact by simpa [add_comm] using (eq_sub_iff_add_eq.mp hz)
  rw [hpreimage]
  symm
  exact diracConvolutionKernel_pow_apply_singleton_eq_originMass (μ := ν.toMeasure) N x y

/-- Helper for Theorem 18.8: a realization of the auxiliary block chain written via singleton
matrix rows is the same realization of the corresponding convolution-kernel semigroup. -/
private lemma endpointOwnerKernelRealization_of_blockRealization
    {d : ℕ} {μN : PMF (LatticePoint d)}
    {Ω : Type*} [MeasurableSpace Ω]
    {P : LatticePoint d → ProbabilityMeasure Ω}
    {Z : ℕ → Ω → LatticePoint d}
    (hZ :
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel
            (fun a b ↦
              dirac_convolution_kernel μN.toMeasure a ({b} : Set (LatticePoint d))) ^ n)
        P Z) :
    IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel μN.toMeasure ^ n) P Z := by
  -- Proof comment: the singleton-mass matrix of the auxiliary owner law is exactly the same
  -- kernel, so the realization transport is only a rewrite through `ownerStepMatrix_kernel_eq`.
  simpa [ownerStepMatrix_kernel_eq] using hZ

/-- Helper for Theorem 18.8: along any realization of the auxiliary block chain, the realized next
endpoint lies almost surely in the support of the genuine `N`-step owner row. -/
private theorem endpointStepMass_ne_zero_ae
    {d : ℕ} {ν μN : PMF (LatticePoint d)} {N : ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    {P : LatticePoint d → ProbabilityMeasure Ω}
    {Z : ℕ → Ω → LatticePoint d}
    (hμN :
      μN.toMeasure = (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d))
    (hZ :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel μN.toMeasure ^ n) P Z)
    (x : LatticePoint d) (q : ℕ) :
    ∀ᵐ ω ∂(P x : Measure Ω),
      ((dirac_convolution_kernel ν.toMeasure ^ N) (Z q ω))
        ({Z (q + 1) ω} : Set (LatticePoint d)) ≠ 0 := by
  let step : LatticePoint d → LatticePoint d → ENNReal := fun a b ↦
    dirac_convolution_kernel μN.toMeasure a ({b} : Set (LatticePoint d))
  have hZ_step :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel step ^ n) P Z := by
    -- Proof comment: the auxiliary owner matrix is the discrete singleton form of the same
    -- convolution kernel, so the existing realization can be reused verbatim.
    simpa [step, ownerStepMatrix_kernel_eq] using hZ
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel step ^ n) P Z := hZ_step
  have hbase :
      ∀ᵐ ω ∂(P x : Measure Ω), step (Z q ω) (Z (q + 1) ω) ≠ 0 :=
    transitionMass_ne_zero_ae_of_markovRealization (q := step) (P := P) (X := Z) x q
  -- Proof comment: transport the nonzero row support from the auxiliary step matrix to the
  -- genuine `N`-step owner row using the row-identification lemma above.
  filter_upwards [hbase] with ω hω
  simpa [step, ownerBlockStepMass_eq_powSingletonMass (hμN := hμN)] using hω

/-- Helper for Theorem 18.8: along the first endpoint skeleton, every block transition up to time
`q` has positive genuine `N`-step owner mass almost surely. -/
private theorem fstEndpointStepMass_ne_zero_ae_upto
    {d : ℕ} {ν μN : PMF (LatticePoint d)} {N : ℕ}
    {Ωend : Type*} [MeasurableSpace Ωend]
    (Pend : LatticePoint d × LatticePoint d → ProbabilityMeasure Ωend)
    (hμN :
      μN.toMeasure = (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d))
    (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (x y : LatticePoint d)
    (hZend :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel μN.toMeasure ^ n)
        (fun a : LatticePoint d ↦ Pend (a, y))
        (fun n ω ↦ (Zend n ω).1))
    (q : ℕ) :
    ∀ᵐ ω ∂(Pend (x, y) : Measure Ωend),
      ∀ j ∈ Finset.range (q + 1),
        ((dirac_convolution_kernel ν.toMeasure ^ N) ((Zend j ω).1))
          ({(Zend (j + 1) ω).1} : Set (LatticePoint d)) ≠ 0 := by
  induction q with
  | zero =>
      have hstep :=
        endpointStepMass_ne_zero_ae
          (ν := ν) (μN := μN) (hμN := hμN) (P := fun a ↦ Pend (a, y))
          (Z := fun n ω ↦ (Zend n ω).1) hZend x 0
      -- Proof comment: for the initial prefix, the range contains only the first block step.
      filter_upwards [hstep] with ω hω j hj
      have hj0 : j = 0 := by
        simp [Finset.mem_range] at hj
        omega
      subst hj0
      simpa using hω
  | succ q ih =>
      have hstep :=
        endpointStepMass_ne_zero_ae
          (ν := ν) (μN := μN) (hμN := hμN) (P := fun a ↦ Pend (a, y))
          (Z := fun n ω ↦ (Zend n ω).1) hZend x (q + 1)
      -- Proof comment: append the `(q + 1)`-st endpoint step to the already controlled prefix.
      filter_upwards [ih, hstep] with ω hω_prefix hω_step j hj
      by_cases hj_last : j = q + 1
      · subst hj_last
        simpa using hω_step
      · exact
          hω_prefix j <| by
            simp [Finset.mem_range] at hj ⊢
            omega

/-- Helper for Theorem 18.8: along the second endpoint skeleton, every block transition up to time
`q` has positive genuine `N`-step owner mass almost surely. -/
private theorem sndEndpointStepMass_ne_zero_ae_upto
    {d : ℕ} {ν μN : PMF (LatticePoint d)} {N : ℕ}
    {Ωend : Type*} [MeasurableSpace Ωend]
    (Pend : LatticePoint d × LatticePoint d → ProbabilityMeasure Ωend)
    (hμN :
      μN.toMeasure = (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d))
    (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (x y : LatticePoint d)
    (hZend :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel μN.toMeasure ^ n)
        (fun b : LatticePoint d ↦ Pend (x, b))
        (fun n ω ↦ (Zend n ω).2))
    (q : ℕ) :
    ∀ᵐ ω ∂(Pend (x, y) : Measure Ωend),
      ∀ j ∈ Finset.range (q + 1),
        ((dirac_convolution_kernel ν.toMeasure ^ N) ((Zend j ω).2))
          ({(Zend (j + 1) ω).2} : Set (LatticePoint d)) ≠ 0 := by
  induction q with
  | zero =>
      have hstep :=
        endpointStepMass_ne_zero_ae
          (ν := ν) (μN := μN) (hμN := hμN) (P := fun b ↦ Pend (x, b))
          (Z := fun n ω ↦ (Zend n ω).2) hZend y 0
      -- Proof comment: the second endpoint prefix starts with its first block step as well.
      filter_upwards [hstep] with ω hω j hj
      have hj0 : j = 0 := by
        simp [Finset.mem_range] at hj
        omega
      subst hj0
      simpa using hω
  | succ q ih =>
      have hstep :=
        endpointStepMass_ne_zero_ae
          (ν := ν) (μN := μN) (hμN := hμN) (P := fun b ↦ Pend (x, b))
          (Z := fun n ω ↦ (Zend n ω).2) hZend y (q + 1)
      -- Proof comment: extend the controlled second-coordinate endpoint prefix by one block.
      filter_upwards [ih, hstep] with ω hω_prefix hω_step j hj
      by_cases hj_last : j = q + 1
      · subst hj_last
        simpa using hω_step
      · exact
          hω_prefix j <| by
            simp [Finset.mem_range] at hj ⊢
            omega

/-- Helper for Theorem 18.8: up to any fixed block index, the first sampled bridge blocks in the
lifted Step 3 construction start and end at the corresponding first endpoint skeleton values
almost surely. -/
private theorem pairedEndpointBridgeLiftFst_visibleSupport_ae_upto
    {d : ℕ} {ν μN : PMF (LatticePoint d)}
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (hP :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P Function.eval)
    {Ωend : Type*} [MeasurableSpace Ωend]
    (Pend : LatticePoint d × LatticePoint d → ProbabilityMeasure Ωend)
    {N : ℕ}
    (hμN :
      μN.toMeasure = (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d))
    (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (x y : LatticePoint d)
    (hZend :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel μN.toMeasure ^ n)
        (fun a : LatticePoint d ↦ Pend (a, y))
        (fun n ω ↦ (Zend n ω).1))
    (q : ℕ) :
    ∀ᵐ θ ∂(pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y),
      ∀ j ∈ Finset.range (q + 1),
        ((θ.2 j).1) ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = (Zend j θ.1).1 ∧
          ((θ.2 j).1) ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (Zend (j + 1) θ.1).1 := by
  induction q with
  | zero =>
      have hstep :
          ∀ᵐ ωend ∂(Pend (x, y) : Measure Ωend),
            ((dirac_convolution_kernel ν.toMeasure ^ N) ((Zend 0 ωend).1))
              ({(Zend 1 ωend).1} : Set (LatticePoint d)) ≠ 0 := by
        simpa using
          endpointStepMass_ne_zero_ae
            (ν := ν) (μN := μN) (hμN := hμN)
            (P := fun a ↦ Pend (a, y)) (Z := fun n ω ↦ (Zend n ω).1)
            hZend x 0
      have hstart :
          ∀ᵐ θ ∂(pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y),
            ((θ.2 0).1) ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = (Zend 0 θ.1).1 := by
        rw [pairedEndpointBridgeLiftMeasure]
        refine Measure.ae_compProd_of_ae_ae ?_ ?_
        · exact measurableSet_eq_fun (by fun_prop) (by
            simpa using (hZend.measurable_process 0).comp measurable_fst)
        · filter_upwards [hstep] with ωend hω
          let good :
              Set
                (ℕ →
                  ((Finset.Iic N → LatticePoint d) ×
                    (Finset.Iic N → LatticePoint d))) :=
            {ξ | (ξ 0).1 ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = (Zend 0 ωend).1}
          have hgood :
              pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend) good = 1 := by
            -- Proof comment: the first block row is supported on paths starting at the current
            -- first endpoint once the corresponding block transition has positive mass.
            simpa [good] using
              pairedEndpointBridgeTrajectoryMeasure_fstStart_of_transition_ne_zero
                (hP := hP) N (ζ := fun n ↦ Zend n ωend) 0 hω
          have hgood_meas : MeasurableSet good := by
            exact measurableSet_eq_fun (by fun_prop) measurable_const
          have hbad :
              {ξ |
                ¬(ξ 0).1 ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = (Zend 0 ωend).1} =
                goodᶜ := by
            ext ξ
            simp [good]
          rw [ae_iff]
          rw [hbad, measure_compl hgood_meas, hgood]
          simp
      have hend :
          ∀ᵐ θ ∂(pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y),
            ((θ.2 0).1) ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (Zend 1 θ.1).1 := by
        rw [pairedEndpointBridgeLiftMeasure]
        refine Measure.ae_compProd_of_ae_ae ?_ ?_
        · exact measurableSet_eq_fun (by fun_prop) (by
            simpa using (hZend.measurable_process 1).comp measurable_fst)
        · filter_upwards [hstep] with ωend hω
          let good :
              Set
                (ℕ →
                  ((Finset.Iic N → LatticePoint d) ×
                    (Finset.Iic N → LatticePoint d))) :=
            {ξ | (ξ 0).1 ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (Zend 1 ωend).1}
          have hgood :
              pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend) good = 1 := by
            -- Proof comment: the same first block row is also supported on the prescribed first
            -- endpoint at time `N`.
            simpa [good] using
              pairedEndpointBridgeTrajectoryMeasure_fstEndpoint_of_transition_ne_zero
                (hP := hP) N (ζ := fun n ↦ Zend n ωend) 0 hω
          have hgood_meas : MeasurableSet good := by
            exact measurableSet_eq_fun (by fun_prop) measurable_const
          have hbad :
              {ξ | ¬(ξ 0).1 ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (Zend 1 ωend).1} = goodᶜ := by
            ext ξ
            simp [good]
          rw [ae_iff]
          rw [hbad, measure_compl hgood_meas, hgood]
          simp
      -- Proof comment: for the one-block prefix, only block `0` is visible and both boundary
      -- coordinates are now forced almost surely.
      filter_upwards [hstart, hend] with θ hstartθ hendθ j hj
      have hj0 : j = 0 := by
        simp [Finset.mem_range] at hj
        omega
      subst hj0
      exact ⟨hstartθ, hendθ⟩
  | succ q ih =>
      have hstep :
          ∀ᵐ ωend ∂(Pend (x, y) : Measure Ωend),
            ((dirac_convolution_kernel ν.toMeasure ^ N) ((Zend (q + 1) ωend).1))
              ({(Zend (q + 2) ωend).1} : Set (LatticePoint d)) ≠ 0 := by
        simpa using
          endpointStepMass_ne_zero_ae
            (ν := ν) (μN := μN) (hμN := hμN)
            (P := fun a ↦ Pend (a, y)) (Z := fun n ω ↦ (Zend n ω).1)
            hZend x (q + 1)
      have hstart :
          ∀ᵐ θ ∂(pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y),
            ((θ.2 (q + 1)).1) ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ =
              (Zend (q + 1) θ.1).1 := by
        rw [pairedEndpointBridgeLiftMeasure]
        refine Measure.ae_compProd_of_ae_ae ?_ ?_
        · exact measurableSet_eq_fun (by fun_prop) (by
            simpa using (hZend.measurable_process (q + 1)).comp measurable_fst)
        · filter_upwards [hstep] with ωend hω
          let good :
              Set
                (ℕ →
                  ((Finset.Iic N → LatticePoint d) ×
                    (Finset.Iic N → LatticePoint d))) :=
            {ξ |
              (ξ (q + 1)).1 ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = (Zend (q + 1) ωend).1}
          have hgood :
              pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend) good = 1 := by
            -- Proof comment: the `(q + 1)`-st first bridge block starts at the next first
            -- endpoint once its owner block mass is nonzero.
            simpa [good] using
              pairedEndpointBridgeTrajectoryMeasure_fstStart_of_transition_ne_zero
                (hP := hP) N (ζ := fun n ↦ Zend n ωend) (q + 1) hω
          have hgood_meas : MeasurableSet good := by
            exact measurableSet_eq_fun (by fun_prop) measurable_const
          have hbad :
              {ξ |
                ¬(ξ (q + 1)).1 ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ =
                  (Zend (q + 1) ωend).1} = goodᶜ := by
            ext ξ
            simp [good]
          rw [ae_iff]
          rw [hbad, measure_compl hgood_meas, hgood]
          simp
      have hend :
          ∀ᵐ θ ∂(pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y),
            ((θ.2 (q + 1)).1) ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (Zend (q + 2) θ.1).1 := by
        rw [pairedEndpointBridgeLiftMeasure]
        refine Measure.ae_compProd_of_ae_ae ?_ ?_
        · exact measurableSet_eq_fun (by fun_prop) (by
            simpa using (hZend.measurable_process (q + 2)).comp measurable_fst)
        · filter_upwards [hstep] with ωend hω
          let good :
              Set
                (ℕ →
                  ((Finset.Iic N → LatticePoint d) ×
                    (Finset.Iic N → LatticePoint d))) :=
            {ξ | (ξ (q + 1)).1 ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (Zend (q + 2) ωend).1}
          have hgood :
              pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend) good = 1 := by
            -- Proof comment: the same visible block also ends at the corresponding next first
            -- endpoint almost surely.
            simpa [good] using
              pairedEndpointBridgeTrajectoryMeasure_fstEndpoint_of_transition_ne_zero
                (hP := hP) N (ζ := fun n ↦ Zend n ωend) (q + 1) hω
          have hgood_meas : MeasurableSet good := by
            exact measurableSet_eq_fun (by fun_prop) measurable_const
          have hbad :
              {ξ |
                ¬(ξ (q + 1)).1 ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (Zend (q + 2) ωend).1} =
                goodᶜ := by
            ext ξ
            simp [good]
          rw [ae_iff]
          rw [hbad, measure_compl hgood_meas, hgood]
          simp
      -- Proof comment: append the newly controlled first bridge block to the already supported
      -- visible prefix from the induction hypothesis.
      filter_upwards [ih, hstart, hend] with θ hprefix hstartθ hendθ j hj
      by_cases hj_last : j = q + 1
      · subst hj_last
        exact ⟨hstartθ, hendθ⟩
      · exact
          hprefix j <| by
            simp [Finset.mem_range] at hj ⊢
            omega

/-- Helper for Theorem 18.8: up to any fixed block index, the second sampled bridge blocks in the
lifted Step 3 construction start and end at the corresponding second endpoint skeleton values
almost surely. -/
private theorem pairedEndpointBridgeLiftSnd_visibleSupport_ae_upto
    {d : ℕ} {ν μN : PMF (LatticePoint d)}
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (hP :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P Function.eval)
    {Ωend : Type*} [MeasurableSpace Ωend]
    (Pend : LatticePoint d × LatticePoint d → ProbabilityMeasure Ωend)
    {N : ℕ}
    (hμN :
      μN.toMeasure = (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d))
    (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (x y : LatticePoint d)
    (hZend :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel μN.toMeasure ^ n)
        (fun b : LatticePoint d ↦ Pend (x, b))
        (fun n ω ↦ (Zend n ω).2))
    (q : ℕ) :
    ∀ᵐ θ ∂(pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y),
      ∀ j ∈ Finset.range (q + 1),
        ((θ.2 j).2) ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = (Zend j θ.1).2 ∧
          ((θ.2 j).2) ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (Zend (j + 1) θ.1).2 := by
  induction q with
  | zero =>
      have hstep :
          ∀ᵐ ωend ∂(Pend (x, y) : Measure Ωend),
            ((dirac_convolution_kernel ν.toMeasure ^ N) ((Zend 0 ωend).2))
              ({(Zend 1 ωend).2} : Set (LatticePoint d)) ≠ 0 := by
        simpa using
          endpointStepMass_ne_zero_ae
            (ν := ν) (μN := μN) (hμN := hμN)
            (P := fun b ↦ Pend (x, b)) (Z := fun n ω ↦ (Zend n ω).2)
            hZend y 0
      have hstart :
          ∀ᵐ θ ∂(pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y),
            ((θ.2 0).2) ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = (Zend 0 θ.1).2 := by
        rw [pairedEndpointBridgeLiftMeasure]
        refine Measure.ae_compProd_of_ae_ae ?_ ?_
        · exact measurableSet_eq_fun (by fun_prop) (by
            simpa using (hZend.measurable_process 0).comp measurable_fst)
        · filter_upwards [hstep] with ωend hω
          let good :
              Set
                (ℕ →
                  ((Finset.Iic N → LatticePoint d) ×
                    (Finset.Iic N → LatticePoint d))) :=
            {ξ | (ξ 0).2 ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = (Zend 0 ωend).2}
          have hgood :
              pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend) good = 1 := by
            -- Proof comment: the first visible second-coordinate bridge block starts at the
            -- current second endpoint once the corresponding block transition has positive mass.
            simpa [good] using
              pairedEndpointBridgeTrajectoryMeasure_sndStart_of_transition_ne_zero
                (hP := hP) N (ζ := fun n ↦ Zend n ωend) 0 hω
          have hgood_meas : MeasurableSet good := by
            exact measurableSet_eq_fun (by fun_prop) measurable_const
          have hbad :
              {ξ |
                ¬(ξ 0).2 ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = (Zend 0 ωend).2} =
                goodᶜ := by
            ext ξ
            simp [good]
          rw [ae_iff]
          rw [hbad, measure_compl hgood_meas, hgood]
          simp
      have hend :
          ∀ᵐ θ ∂(pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y),
            ((θ.2 0).2) ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (Zend 1 θ.1).2 := by
        rw [pairedEndpointBridgeLiftMeasure]
        refine Measure.ae_compProd_of_ae_ae ?_ ?_
        · exact measurableSet_eq_fun (by fun_prop) (by
            simpa using (hZend.measurable_process 1).comp measurable_fst)
        · filter_upwards [hstep] with ωend hω
          let good :
              Set
                (ℕ →
                  ((Finset.Iic N → LatticePoint d) ×
                    (Finset.Iic N → LatticePoint d))) :=
            {ξ | (ξ 0).2 ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (Zend 1 ωend).2}
          have hgood :
              pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend) good = 1 := by
            -- Proof comment: the same second block row also lands at the prescribed second
            -- endpoint at time `N`.
            simpa [good] using
              pairedEndpointBridgeTrajectoryMeasure_sndEndpoint_of_transition_ne_zero
                (hP := hP) N (ζ := fun n ↦ Zend n ωend) 0 hω
          have hgood_meas : MeasurableSet good := by
            exact measurableSet_eq_fun (by fun_prop) measurable_const
          have hbad :
              {ξ | ¬(ξ 0).2 ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (Zend 1 ωend).2} = goodᶜ := by
            ext ξ
            simp [good]
          rw [ae_iff]
          rw [hbad, measure_compl hgood_meas, hgood]
          simp
      -- Proof comment: for the one-block visible second prefix, only block `0` appears and both
      -- second-coordinate boundary constraints now hold almost surely.
      filter_upwards [hstart, hend] with θ hstartθ hendθ j hj
      have hj0 : j = 0 := by
        simp [Finset.mem_range] at hj
        omega
      subst hj0
      exact ⟨hstartθ, hendθ⟩
  | succ q ih =>
      have hstep :
          ∀ᵐ ωend ∂(Pend (x, y) : Measure Ωend),
            ((dirac_convolution_kernel ν.toMeasure ^ N) ((Zend (q + 1) ωend).2))
              ({(Zend (q + 2) ωend).2} : Set (LatticePoint d)) ≠ 0 := by
        simpa using
          endpointStepMass_ne_zero_ae
            (ν := ν) (μN := μN) (hμN := hμN)
            (P := fun b ↦ Pend (x, b)) (Z := fun n ω ↦ (Zend n ω).2)
            hZend y (q + 1)
      have hstart :
          ∀ᵐ θ ∂(pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y),
            ((θ.2 (q + 1)).2) ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ =
              (Zend (q + 1) θ.1).2 := by
        rw [pairedEndpointBridgeLiftMeasure]
        refine Measure.ae_compProd_of_ae_ae ?_ ?_
        · exact measurableSet_eq_fun (by fun_prop) (by
            simpa using (hZend.measurable_process (q + 1)).comp measurable_fst)
        · filter_upwards [hstep] with ωend hω
          let good :
              Set
                (ℕ →
                  ((Finset.Iic N → LatticePoint d) ×
                    (Finset.Iic N → LatticePoint d))) :=
            {ξ |
              (ξ (q + 1)).2 ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ = (Zend (q + 1) ωend).2}
          have hgood :
              pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend) good = 1 := by
            -- Proof comment: the `(q + 1)`-st second bridge block starts at the matching second
            -- endpoint once the owner block row is positive.
            simpa [good] using
              pairedEndpointBridgeTrajectoryMeasure_sndStart_of_transition_ne_zero
                (hP := hP) N (ζ := fun n ↦ Zend n ωend) (q + 1) hω
          have hgood_meas : MeasurableSet good := by
            exact measurableSet_eq_fun (by fun_prop) measurable_const
          have hbad :
              {ξ |
                ¬(ξ (q + 1)).2 ⟨0, Finset.mem_Iic.2 (Nat.zero_le N)⟩ =
                  (Zend (q + 1) ωend).2} = goodᶜ := by
            ext ξ
            simp [good]
          rw [ae_iff]
          rw [hbad, measure_compl hgood_meas, hgood]
          simp
      have hend :
          ∀ᵐ θ ∂(pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y),
            ((θ.2 (q + 1)).2) ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (Zend (q + 2) θ.1).2 := by
        rw [pairedEndpointBridgeLiftMeasure]
        refine Measure.ae_compProd_of_ae_ae ?_ ?_
        · exact measurableSet_eq_fun (by fun_prop) (by
            simpa using (hZend.measurable_process (q + 2)).comp measurable_fst)
        · filter_upwards [hstep] with ωend hω
          let good :
              Set
                (ℕ →
                  ((Finset.Iic N → LatticePoint d) ×
                    (Finset.Iic N → LatticePoint d))) :=
            {ξ | (ξ (q + 1)).2 ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (Zend (q + 2) ωend).2}
          have hgood :
              pairedEndpointBridgeTrajectoryMeasure P N (fun n ↦ Zend n ωend) good = 1 := by
            -- Proof comment: the same visible second block also ends at the corresponding next
            -- second endpoint almost surely.
            simpa [good] using
              pairedEndpointBridgeTrajectoryMeasure_sndEndpoint_of_transition_ne_zero
                (hP := hP) N (ζ := fun n ↦ Zend n ωend) (q + 1) hω
          have hgood_meas : MeasurableSet good := by
            exact measurableSet_eq_fun (by fun_prop) measurable_const
          have hbad :
              {ξ |
                ¬(ξ (q + 1)).2 ⟨N, Finset.mem_Iic.2 le_rfl⟩ = (Zend (q + 2) ωend).2} =
                goodᶜ := by
            ext ξ
            simp [good]
          rw [ae_iff]
          rw [hbad, measure_compl hgood_meas, hgood]
          simp
      -- Proof comment: append the new second bridge block support to the already controlled
      -- visible second-coordinate prefix.
      filter_upwards [ih, hstart, hend] with θ hprefix hstartθ hendθ j hj
      by_cases hj_last : j = q + 1
      · subst hj_last
        exact ⟨hstartθ, hendθ⟩
      · exact
          hprefix j <| by
            simp [Finset.mem_range] at hj ⊢
            omega

/-- Helper for Theorem 18.8: decompose a visible time into its block index and in-block
offset. -/
private lemma pairedEndpointBridgeLift_divMod {N s : ℕ} (hN : 0 < N) :
    let q := s / N
    let r := s % N
    q * N + r = s ∧ r < N := by
  refine ⟨?_, ?_⟩
  · simpa using (Nat.div_add_mod s N).symm
  · simpa using Nat.mod_lt s hN

/-- Helper for Theorem 18.8: the in-block offset is either the boundary case `0` or a genuine
interior time. -/
private lemma pairedEndpointBridgeLift_boundary_or_interior {N s : ℕ} (hN : 0 < N) :
    let r := s % N
    r = 0 ∨ 0 < r ∧ r < N := by
  by_cases hr0 : s % N = 0
  · exact Or.inl hr0
  · refine Or.inr ⟨Nat.pos_of_ne_zero hr0, ?_⟩
    simpa using Nat.mod_lt s hN

/-- Helper for Theorem 18.8: the first lifted coordinate in the Step 3 block-splicing
construction should satisfy the same pair-singleton factorization as in Step 2. -/
private theorem pairedEndpointBridgeLiftFst_pairSingleton_eq_historyMass_mul_ownerStep
    {d : ℕ} {ν μN : PMF (LatticePoint d)}
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (hP :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P Function.eval)
    {Ωend : Type*} [MeasurableSpace Ωend]
    (Pend : LatticePoint d × LatticePoint d → ProbabilityMeasure Ωend)
    {N : ℕ} (hN : 0 < N)
    (hμN :
      μN.toMeasure = (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d))
    (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (x y : LatticePoint d)
    (hZend :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel μN.toMeasure ^ n)
        (fun a : LatticePoint d ↦ Pend (a, y))
        (fun n ω ↦ (Zend n ω).1))
    (s : ℕ)
    (h : Finset.Iic s → LatticePoint d) (w : LatticePoint d) :
    let μ := pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y
    let Z := pairedEndpointBridgeLiftProcess N hN Zend
    let H := fun θ (i : Finset.Iic s) ↦ (Z i.1 θ).1
    let next := fun θ ↦ (Z (s + 1) θ).1
    μ.map (fun θ ↦ (H θ, next θ))
        ({(h, w)} : Set ((Finset.Iic s → LatticePoint d) × LatticePoint d)) =
      μ.map H ({h} : Set (Finset.Iic s → LatticePoint d)) *
        dirac_convolution_kernel ν.toMeasure
          (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) ({w} : Set (LatticePoint d)) := by
  let μ := pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y
  let Z := pairedEndpointBridgeLiftProcess N hN Zend
  let H := fun θ (i : Finset.Iic s) ↦ (Z i.1 θ).1
  let next := fun θ ↦ (Z (s + 1) θ).1
  let q : ℕ := s / N
  let r : ℕ := s % N
  -- Route correction: the blocker is no longer the global Markov shell. It is exactly this
  -- local pair-singleton identity for the first lifted coordinate.
  have hsdecomp : q * N + r = s := by
    simpa [q, r] using (pairedEndpointBridgeLift_divMod (s := s) hN).1
  have hr_cases : r = 0 ∨ 0 < r ∧ r < N := by
    simpa [r] using pairedEndpointBridgeLift_boundary_or_interior (s := s) hN
  let _ := μ
  let _ := H
  let _ := next
  let _ := hP
  let _ := hμN
  let _ := hZend
  cases hr_cases with
  | inl hr0 =>
      -- TODO: boundary case. Rewrite `s = q * N`, so the visible history ends at the endpoint
      -- skeleton value `Zend q`. Then identify both singleton masses through
      -- `pairedEndpointBridgeLiftProcess_boundary`, the boundary marginal at block `q`, and the
      -- first-coordinate support package `pairedEndpointBridgeLiftFst_visibleSupport_ae_upto`.
      -- The remaining first bridge step is the `r = 0` instance of the owner conditioned-prefix
      -- factorization on the `q`-th block.
      have hs_boundary : q * N = s := by simpa [hr0] using hsdecomp
      let hend : Finset.Iic q → LatticePoint d := fun i ↦
        h ⟨i.1 * N, by
          have hiq : i.1 ≤ q := Finset.mem_Iic.1 i.2
          omega⟩
      let prefix0 : Finset.Iic 0 → LatticePoint d := fun _ ↦ h ⟨s, Finset.mem_Iic.2 le_rfl⟩
      have hendpoint_singleton :
          ∀ u : LatticePoint d,
            (let μend : Measure Ωend := (Pend (x, y) : Measure Ωend)
             let Hend : Ωend → Finset.Iic q → LatticePoint d := fun ω i ↦ (Zend i.1 ω).1
             let nextEnd : Ωend → LatticePoint d := fun ω ↦ (Zend (q + 1) ω).1
             μend.map (fun ω ↦ (Hend ω, nextEnd ω))
                 ({(hend, u)} : Set ((Finset.Iic q → LatticePoint d) × LatticePoint d)) =
               μend.map Hend ({hend} : Set (Finset.Iic q → LatticePoint d)) *
                 dirac_convolution_kernel μN.toMeasure
                   (hend ⟨q, Finset.mem_Iic.2 le_rfl⟩) ({u} : Set (LatticePoint d))) := by
        intro u
        -- Proof comment: the endpoint skeleton itself is already a Markov realization of the
        -- auxiliary block chain, so its history/next atom factorizes immediately.
        simpa [hend, discreteMatrixKernel_apply_singleton] using
          pairSingleton_eq_historyMass_mul_step_of_markovRealization
            (q := fun a b ↦ dirac_convolution_kernel μN.toMeasure a ({b} : Set (LatticePoint d)))
            (P := fun a ↦ Pend (a, y)) (X := fun n ω ↦ (Zend n ω).1) x q hend u
      have hactive_average :
          (∑' u : LatticePoint d,
            ((dirac_convolution_kernel ν.toMeasure ^ N) (h ⟨s, Finset.mem_Iic.2 le_rfl⟩))
                ({u} : Set (LatticePoint d)) *
              ownerEndpointConditionedPrefixKernelIic P N
                (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) u
                {ξ : Finset.Iic N → LatticePoint d |
                  Preorder.frestrictLe 0 ξ = prefix0 ∧
                    ξ ⟨1, Finset.mem_Iic.2 hN⟩ = w}) =
            (∑' u : LatticePoint d,
              ((dirac_convolution_kernel ν.toMeasure ^ N) (h ⟨s, Finset.mem_Iic.2 le_rfl⟩))
                  ({u} : Set (LatticePoint d)) *
                ownerEndpointConditionedPrefixKernelIic P N
                  (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) u
                  {ξ : Finset.Iic N → LatticePoint d | Preorder.frestrictLe 0 ξ = prefix0}) *
              dirac_convolution_kernel ν.toMeasure
                (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) ({w} : Set (LatticePoint d)) := by
        -- Proof comment: the active block contribution at a boundary time is the `r = 0`
        -- instance of the averaged conditioned-prefix identity.
        simpa [prefix0] using
          ownerEndpointConditionedPrefixKernelIic_average_historyNextMass
            (hP := hP) (N := N) (r := 0) (hr := hN)
            (x := h ⟨s, Finset.mem_Iic.2 le_rfl⟩) (w := w) prefix0
      let _ := hendpoint_singleton
      let _ := hactive_average
      let _ := hs_boundary
      sorry
  | inr hr =>
      -- TODO: interior case. Rewrite `s = q * N + r` with `0 < r < N`, normalize the active
      -- block through `pairedEndpointBridgeLiftProcess_interior`, and use
      -- `pairedEndpointBridgeLiftMeasure_fstBlockMarginal` to move the `q`-th sampled first
      -- bridge block to `ownerEndpointConditionedPrefixKernelIic`. After inserting the invisible
      -- block boundary equalities from `pairedEndpointBridgeLiftFst_visibleSupport_ae_upto`, the
      -- pointwise identity should be exactly
      -- `ownerEndpointConditionedPrefixKernelIic_historyNextMass_mul_remaining`.
      rcases hr with ⟨hr_pos, hr_lt⟩
      let prefix : Finset.Iic r → LatticePoint d := fun i ↦
        h ⟨q * N + i.1, by
          have hir : i.1 ≤ r := Finset.mem_Iic.1 i.2
          omega⟩
      have hactive_average :
          (∑' u : LatticePoint d,
            ((dirac_convolution_kernel ν.toMeasure ^ N) (h ⟨q * N, by omega⟩))
                ({u} : Set (LatticePoint d)) *
              ownerEndpointConditionedPrefixKernelIic P N
                (h ⟨q * N, by omega⟩) u
                {ξ : Finset.Iic N → LatticePoint d |
                  Preorder.frestrictLe r ξ = prefix ∧
                    ξ ⟨r + 1, Finset.mem_Iic.2 (Nat.le_of_lt hr_lt)⟩ = w}) =
            (∑' u : LatticePoint d,
              ((dirac_convolution_kernel ν.toMeasure ^ N) (h ⟨q * N, by omega⟩))
                  ({u} : Set (LatticePoint d)) *
                ownerEndpointConditionedPrefixKernelIic P N
                  (h ⟨q * N, by omega⟩) u
                  {ξ : Finset.Iic N → LatticePoint d | Preorder.frestrictLe r ξ = prefix}) *
              dirac_convolution_kernel ν.toMeasure
                (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) ({w} : Set (LatticePoint d)) := by
        -- Proof comment: after normalizing the active block to the prefix of length `r`, the
        -- remaining first-coordinate step is exactly the averaged conditioned-prefix identity.
        simpa [prefix, hsdecomp] using
          ownerEndpointConditionedPrefixKernelIic_average_historyNextMass
            (hP := hP) (N := N) (r := r) (hr := hr_lt)
            (x := h ⟨q * N, by omega⟩) (w := w) prefix
      let _ := hactive_average
      let _ := hr_pos
      let _ := hr_lt
      let _ := hsdecomp
      sorry

/-- Helper for Theorem 18.8: the second lifted coordinate in the Step 3 block-splicing
construction should satisfy the symmetric pair-singleton factorization. -/
private theorem pairedEndpointBridgeLiftSnd_pairSingleton_eq_historyMass_mul_ownerStep
    {d : ℕ} {ν μN : PMF (LatticePoint d)}
    {P : LatticePoint d → ProbabilityMeasure (ℕ → LatticePoint d)}
    (hP :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P Function.eval)
    {Ωend : Type*} [MeasurableSpace Ωend]
    (Pend : LatticePoint d × LatticePoint d → ProbabilityMeasure Ωend)
    {N : ℕ} (hN : 0 < N)
    (hμN :
      μN.toMeasure = (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d))
    (Zend : ℕ → Ωend → LatticePoint d × LatticePoint d)
    (x y : LatticePoint d)
    (hZend :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel μN.toMeasure ^ n)
        (fun b : LatticePoint d ↦ Pend (x, b))
        (fun n ω ↦ (Zend n ω).2))
    (s : ℕ)
    (h : Finset.Iic s → LatticePoint d) (w : LatticePoint d) :
    let μ := pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y
    let Z := pairedEndpointBridgeLiftProcess N hN Zend
    let H := fun θ (i : Finset.Iic s) ↦ (Z i.1 θ).2
    let next := fun θ ↦ (Z (s + 1) θ).2
    μ.map (fun θ ↦ (H θ, next θ))
        ({(h, w)} : Set ((Finset.Iic s → LatticePoint d) × LatticePoint d)) =
      μ.map H ({h} : Set (Finset.Iic s → LatticePoint d)) *
        dirac_convolution_kernel ν.toMeasure
          (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) ({w} : Set (LatticePoint d)) := by
  let μ := pairedEndpointBridgeLiftMeasure (P := P) (Pend := Pend) N Zend x y
  let Z := pairedEndpointBridgeLiftProcess N hN Zend
  let H := fun θ (i : Finset.Iic s) ↦ (Z i.1 θ).2
  let next := fun θ ↦ (Z (s + 1) θ).2
  let q : ℕ := s / N
  let r : ℕ := s % N
  -- Route correction: the second-coordinate `hstep` now depends only on this symmetric
  -- pair-singleton identity, not on a second independent reconstruction shell.
  have hsdecomp : q * N + r = s := by
    simpa [q, r] using (pairedEndpointBridgeLift_divMod (s := s) hN).1
  have hr_cases : r = 0 ∨ 0 < r ∧ r < N := by
    simpa [r] using pairedEndpointBridgeLift_boundary_or_interior (s := s) hN
  let _ := μ
  let _ := H
  let _ := next
  let _ := hP
  let _ := hμN
  let _ := hZend
  cases hr_cases with
  | inl hr0 =>
      -- TODO: symmetric boundary case. Replace the visible block boundary history by endpoint
      -- skeleton data using `pairedEndpointBridgeLiftProcess_boundary`,
      -- `pairedEndpointBridgeLiftMeasure_sndBlockMarginal`, and
      -- `pairedEndpointBridgeLiftSnd_visibleSupport_ae_upto`, then apply the `r = 0` instance of
      -- the owner conditioned-prefix factorization on the second coordinate.
      have hs_boundary : q * N = s := by simpa [hr0] using hsdecomp
      let hend : Finset.Iic q → LatticePoint d := fun i ↦
        h ⟨i.1 * N, by
          have hiq : i.1 ≤ q := Finset.mem_Iic.1 i.2
          omega⟩
      let prefix0 : Finset.Iic 0 → LatticePoint d := fun _ ↦ h ⟨s, Finset.mem_Iic.2 le_rfl⟩
      have hendpoint_singleton :
          ∀ u : LatticePoint d,
            (let μend : Measure Ωend := (Pend (x, y) : Measure Ωend)
             let Hend : Ωend → Finset.Iic q → LatticePoint d := fun ω i ↦ (Zend i.1 ω).2
             let nextEnd : Ωend → LatticePoint d := fun ω ↦ (Zend (q + 1) ω).2
             μend.map (fun ω ↦ (Hend ω, nextEnd ω))
                 ({(hend, u)} : Set ((Finset.Iic q → LatticePoint d) × LatticePoint d)) =
               μend.map Hend ({hend} : Set (Finset.Iic q → LatticePoint d)) *
                 dirac_convolution_kernel μN.toMeasure
                   (hend ⟨q, Finset.mem_Iic.2 le_rfl⟩) ({u} : Set (LatticePoint d))) := by
        intro u
        -- Proof comment: the second endpoint skeleton has the same block-time Markov law, so the
        -- same generic singleton factorization applies verbatim.
        simpa [hend, discreteMatrixKernel_apply_singleton] using
          pairSingleton_eq_historyMass_mul_step_of_markovRealization
            (q := fun a b ↦ dirac_convolution_kernel μN.toMeasure a ({b} : Set (LatticePoint d)))
            (P := fun b ↦ Pend (x, b)) (X := fun n ω ↦ (Zend n ω).2) y q hend u
      have hactive_average :
          (∑' u : LatticePoint d,
            ((dirac_convolution_kernel ν.toMeasure ^ N) (h ⟨s, Finset.mem_Iic.2 le_rfl⟩))
                ({u} : Set (LatticePoint d)) *
              ownerEndpointConditionedPrefixKernelIic P N
                (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) u
                {ξ : Finset.Iic N → LatticePoint d |
                  Preorder.frestrictLe 0 ξ = prefix0 ∧
                    ξ ⟨1, Finset.mem_Iic.2 hN⟩ = w}) =
            (∑' u : LatticePoint d,
              ((dirac_convolution_kernel ν.toMeasure ^ N) (h ⟨s, Finset.mem_Iic.2 le_rfl⟩))
                  ({u} : Set (LatticePoint d)) *
                ownerEndpointConditionedPrefixKernelIic P N
                  (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) u
                  {ξ : Finset.Iic N → LatticePoint d | Preorder.frestrictLe 0 ξ = prefix0}) *
              dirac_convolution_kernel ν.toMeasure
                (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) ({w} : Set (LatticePoint d)) := by
        -- Proof comment: the active second block is governed by the same `r = 0` averaged
        -- conditioned-prefix identity because only the owner row matters here.
        simpa [prefix0] using
          ownerEndpointConditionedPrefixKernelIic_average_historyNextMass
            (hP := hP) (N := N) (r := 0) (hr := hN)
            (x := h ⟨s, Finset.mem_Iic.2 le_rfl⟩) (w := w) prefix0
      let _ := hendpoint_singleton
      let _ := hactive_average
      let _ := hs_boundary
      sorry
  | inr hr =>
      -- TODO: symmetric interior case. Rewrite the active visible time by
      -- `pairedEndpointBridgeLiftProcess_interior`, identify the `q`-th second sampled bridge
      -- block through `pairedEndpointBridgeLiftMeasure_sndBlockMarginal`, insert the hidden block
      -- start/end equalities from `pairedEndpointBridgeLiftSnd_visibleSupport_ae_upto`, and then
      -- close pointwise with
      -- `ownerEndpointConditionedPrefixKernelIic_historyNextMass_mul_remaining`.
      rcases hr with ⟨hr_pos, hr_lt⟩
      let prefix : Finset.Iic r → LatticePoint d := fun i ↦
        h ⟨q * N + i.1, by
          have hir : i.1 ≤ r := Finset.mem_Iic.1 i.2
          omega⟩
      have hactive_average :
          (∑' u : LatticePoint d,
            ((dirac_convolution_kernel ν.toMeasure ^ N) (h ⟨q * N, by omega⟩))
                ({u} : Set (LatticePoint d)) *
              ownerEndpointConditionedPrefixKernelIic P N
                (h ⟨q * N, by omega⟩) u
                {ξ : Finset.Iic N → LatticePoint d |
                  Preorder.frestrictLe r ξ = prefix ∧
                    ξ ⟨r + 1, Finset.mem_Iic.2 (Nat.le_of_lt hr_lt)⟩ = w}) =
            (∑' u : LatticePoint d,
              ((dirac_convolution_kernel ν.toMeasure ^ N) (h ⟨q * N, by omega⟩))
                  ({u} : Set (LatticePoint d)) *
                ownerEndpointConditionedPrefixKernelIic P N
                  (h ⟨q * N, by omega⟩) u
                  {ξ : Finset.Iic N → LatticePoint d | Preorder.frestrictLe r ξ = prefix}) *
              dirac_convolution_kernel ν.toMeasure
                (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) ({w} : Set (LatticePoint d)) := by
        -- Proof comment: the active second block reduces to the same averaged conditioned-prefix
        -- identity once the visible time is normalized to the `q`-th prefix of length `r`.
        simpa [prefix, hsdecomp] using
          ownerEndpointConditionedPrefixKernelIic_average_historyNextMass
            (hP := hP) (N := N) (r := r) (hr := hr_lt)
            (x := h ⟨q * N, by omega⟩) (w := w) prefix
      let _ := hactive_average
      let _ := hr_pos
      let _ := hr_lt
      let _ := hsdecomp
      sorry

/-- Helper for Theorem 18.8: a successful coupling for the owner matrix driven by the `N`-step
origin law lifts to a successful coupling for the original one-step owner matrix. -/
private theorem ownerHasSuccessfulCoupling_of_powHasSuccessfulCoupling
    {d : ℕ} (ν μN : PMF (LatticePoint d)) {N : ℕ} (hN_pos : 0 < N)
    (hμN :
      μN.toMeasure = (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d))
    (hpow :
      HasSuccessfulCoupling.{0, 0}
        (fun x y ↦ dirac_convolution_kernel μN.toMeasure x ({y} : Set (LatticePoint d)))) :
    HasSuccessfulCoupling.{0, 0}
      (fun x y ↦ dirac_convolution_kernel ν.toMeasure x ({y} : Set (LatticePoint d))) := by
  -- Route correction: Step 3 is now isolated to the missing conditioned block-bridge interface.
  -- The remaining work is not another normalization rewrite but the construction of a total
  -- endpoint-conditioned bridge family and the block-tail comparison that reuses one bridge after
  -- the first diagonal boundary block.
  -- Proof comment: this is the Step 3 block-splicing lift from block times back to unit time.
  by_cases hsub : Subsingleton (LatticePoint d)
  · -- Proof comment: on a subsingleton lattice, the target owner walk is already coupled by the
    -- diagonal realization, so no block splicing is needed.
    letI : Subsingleton (LatticePoint d) := hsub
    simpa using subsingletonOwner_hasSuccessfulCoupling (ν := ν)
  cases N with
  | zero =>
      cases (Nat.not_lt_zero _ hN_pos)
  | succ N =>
      cases N with
      | zero =>
          -- Proof comment: for `N = 1`, the block kernel is the original owner kernel, so the
          -- given successful coupling already has the target marginals.
          have hμN_eq : μN.toMeasure = ν.toMeasure := by
            simpa [pow_one] using hμN
          simpa [hμN_eq] using hpow
      | succ N =>
          rcases hpow.exists_successfulCoupling with
            ⟨Ωend, mΩend, Pend, Zend, hEndSuccess⟩
          let Nblock : ℕ := Nat.succ (Nat.succ N)
          have hNblock_pos : 0 < Nblock := by
            simp [Nblock]
          obtain ⟨Powner, howner⟩ :=
            existsCanonicalDiscreteMatrixRealization
              (q := fun x y ↦
                dirac_convolution_kernel ν.toMeasure x ({y} : Set (LatticePoint d)))
              (hq := ownerStepMatrix_isStochastic ν)
          let mulift : LatticePoint d × LatticePoint d →
              Measure
                (Ωend ×
                  (ℕ →
                    ((Finset.Iic Nblock → LatticePoint d) ×
                      (Finset.Iic Nblock → LatticePoint d)))) := fun z ↦
            pairedEndpointBridgeLiftMeasure
              (P := Powner) (Pend := Pend) Nblock Zend z.1 z.2
          let Zlift :
              ℕ →
                (Ωend ×
                  (ℕ →
                    ((Finset.Iic Nblock → LatticePoint d) ×
                      (Finset.Iic Nblock → LatticePoint d)))) →
                  LatticePoint d × LatticePoint d :=
            pairedEndpointBridgeLiftProcess Nblock hNblock_pos Zend
          let _ := hμN
          let _ := hEndSuccess
          let _ := howner
          let _ := mulift
          let _ := Zlift
          let _ :=
            pairedEndpointBridgeLiftMeasure_fstBlockMarginal
              (P := Powner) (Pend := Pend) Nblock Zend
          let _ :=
            pairedEndpointBridgeLiftMeasure_sndBlockMarginal
              (P := Powner) (Pend := Pend) Nblock Zend
          let Plift :
              LatticePoint d × LatticePoint d →
                ProbabilityMeasure
                  (Ωend ×
                    (ℕ →
                      ((Finset.Iic Nblock → LatticePoint d) ×
                        (Finset.Iic Nblock → LatticePoint d)))) := fun z ↦
            ⟨mulift z, by
              -- Proof comment: the lifted bridge measure is a composition-product of
              -- probability measures, hence itself a probability measure.
              dsimp [mulift, pairedEndpointBridgeLiftMeasure]
              infer_instance⟩
          -- TODO: for genuine block lengths `N ≥ 2`, the tail transfer is now isolated in
          -- `unitTailDisagreement_measure_le_blockBoundaryTail`.
          -- Route correction: the endpoint skeleton already determines the bridge rows blockwise,
          -- so the right next objects are the fixed-skeleton lifted measure `mulift` and the
          -- spliced unit-time process `Zlift`. The block-prefix marginals are now normalized by
          -- `pairedEndpointBridgeLiftMeasure_fstBlockMarginal` and
          -- `pairedEndpointBridgeLiftMeasure_sndBlockMarginal`; the remaining work is to upgrade
          -- those blockwise laws to the unit-time owner marginals via
          -- `ownerEndpointConditionedPrefixKernelIic_reconstruction`, and then transfer the tail
          -- bound with `unitTailDisagreement_measure_le_blockBoundaryTail`.
          refine ProbabilityTheory.HasSuccessfulCoupling.mk.{0, 0} ?_
          refine ⟨_, inferInstance, Plift, Zlift, ?_⟩
          have hLiftCoupling :
              ProbabilityTheory.IsMarkovCoupling
                (fun a b ↦
                  dirac_convolution_kernel ν.toMeasure a ({b} : Set (LatticePoint d)))
                Plift Zlift := by
            refine
              { fst_realization := ?_
                snd_realization := ?_ }
            · intro y
              refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
                (κ₁ := discreteMatrixKernel
                  (fun a b ↦
                    dirac_convolution_kernel ν.toMeasure a ({b} : Set (LatticePoint d))))
                (P := fun x ↦ Plift (x, y))
                (X := fun n θ ↦ (Zlift n θ).1)
                (hmeas := fun n ↦ Measurable.of_discrete)
                (hstart := ?_)
                (hstep := ?_)
              · intro x
                -- Proof comment: the first lifted coordinate starts at the first endpoint of the
                -- successful block-time coupling, so the initial law is Dirac at `x`.
                simpa [Plift, mulift, Zlift] using
                  pairedEndpointBridgeLiftMeasure_fstInitial
                    (P := Powner) (Pend := Pend) hNblock_pos Zend hEndSuccess x y
              · intro x A hA s
                let μ :
                    Measure
                      (Ωend ×
                        (ℕ →
                          ((Finset.Iic Nblock → LatticePoint d) ×
                            (Finset.Iic Nblock → LatticePoint d)))) := Plift (x, y)
                let H :
                    (Ωend ×
                      (ℕ →
                        ((Finset.Iic Nblock → LatticePoint d) ×
                          (Finset.Iic Nblock → LatticePoint d)))) →
                        Finset.Iic s → LatticePoint d := fun θ i ↦ (Zlift i.1 θ).1
                let next :
                    (Ωend ×
                      (ℕ →
                        ((Finset.Iic Nblock → LatticePoint d) ×
                          (Finset.Iic Nblock → LatticePoint d)))) →
                        LatticePoint d := fun θ ↦ (Zlift (s + 1) θ).1
                let step : Kernel (Finset.Iic s → LatticePoint d) (LatticePoint d) :=
                  Kernel.comap
                    (discreteMatrixKernel
                      (fun a b ↦
                        dirac_convolution_kernel ν.toMeasure a ({b} : Set (LatticePoint d))))
                    (fun h ↦ h ⟨s, Finset.mem_Iic.2 le_rfl⟩)
                    (by fun_prop)
                have hH_meas : Measurable H := by
                  exact Measurable.of_discrete
                have hnext_meas : Measurable next := by
                  exact Measurable.of_discrete
                have hsingleton :
                    ∀ h w,
                      μ.map (fun θ ↦ (H θ, next θ))
                          ({(h, w)} : Set ((Finset.Iic s → LatticePoint d) × LatticePoint d)) =
                        μ.map H ({h} : Set (Finset.Iic s → LatticePoint d)) *
                          step h ({w} : Set (LatticePoint d)) := by
                  have hfstEndPow :
                      IsMarkovProcessRealization
                        (fun n : ℕ ↦ dirac_convolution_kernel μN.toMeasure ^ n)
                        (fun a : LatticePoint d ↦ Pend (a, y))
                        (fun n ω ↦ (Zend n ω).1) := by
                    -- Proof comment: the successful block-time coupling already realizes the
                    -- auxiliary block chain on the first coordinate; only the kernel spelling
                    -- changes from singleton rows to the convolution kernel itself.
                    exact
                      endpointOwnerKernelRealization_of_blockRealization
                        (μN := μN)
                        (Z := fun n ω ↦ (Zend n ω).1)
                        (hZ := by
                          simpa using hEndSuccess.toIsMarkovCoupling.fst_realization y)
                  intro h w
                  -- Proof comment: the Step 3 boundary/interior reconstruction has been reduced
                  -- to the dedicated first-coordinate singleton lemma above.
                  simpa [μ, H, next, step, Plift, mulift, Zlift, Kernel.comap_apply,
                    discreteMatrixKernel_apply] using
                    pairedEndpointBridgeLiftFst_pairSingleton_eq_historyMass_mul_ownerStep
                      (ν := ν) (μN := μN) (P := Powner) (hP := howner) (Pend := Pend)
                      (hN := hNblock_pos) (hμN := hμN) (Zend := Zend) x y hfstEndPow s h w
                have hcondexp :
                    μ⟦next ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ]
                      fun θ ↦ (step (H θ)).real A := by
                  exact
                    condExp_eq_kernel_of_pairSingletonMass
                      μ H next step hH_meas hnext_meas hsingleton hA
                have hkernel :
                    (fun θ ↦ (step (H θ)).real A) =ᵐ[μ]
                      fun θ ↦
                        ((discreteMatrixKernel
                          (fun a b ↦
                            dirac_convolution_kernel ν.toMeasure a
                              ({b} : Set (LatticePoint d))))
                          ((Zlift s θ).1)).real A := by
                  -- Proof comment: the comapped step kernel depends only on the last history
                  -- value, which is exactly the visible state `(Zlift s θ).1`.
                  exact Filter.Eventually.of_forall fun θ ↦ by
                    simp [step, H, Kernel.comap_apply, discreteMatrixKernel_apply]
                rw [generatedFiltrationSpace_eq_comap_historyIic
                  (X := fun n θ ↦ (Zlift n θ).1) s]
                exact hcondexp.trans hkernel
            · intro x
              refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
                (κ₁ := discreteMatrixKernel
                  (fun a b ↦
                    dirac_convolution_kernel ν.toMeasure a ({b} : Set (LatticePoint d))))
                (P := fun y ↦ Plift (x, y))
                (X := fun n θ ↦ (Zlift n θ).2)
                (hmeas := fun n ↦ Measurable.of_discrete)
                (hstart := ?_)
                (hstep := ?_)
              · intro y
                -- Proof comment: the second lifted coordinate starts at the second endpoint of
                -- the block-time coupling, so its initial law is Dirac at `y`.
                simpa [Plift, mulift, Zlift] using
                  pairedEndpointBridgeLiftMeasure_sndInitial
                    (P := Powner) (Pend := Pend) hNblock_pos Zend hEndSuccess x y
              · intro y A hA s
                let μ :
                    Measure
                      (Ωend ×
                        (ℕ →
                          ((Finset.Iic Nblock → LatticePoint d) ×
                            (Finset.Iic Nblock → LatticePoint d)))) := Plift (x, y)
                let H :
                    (Ωend ×
                      (ℕ →
                        ((Finset.Iic Nblock → LatticePoint d) ×
                          (Finset.Iic Nblock → LatticePoint d)))) →
                        Finset.Iic s → LatticePoint d := fun θ i ↦ (Zlift i.1 θ).2
                let next :
                    (Ωend ×
                      (ℕ →
                        ((Finset.Iic Nblock → LatticePoint d) ×
                          (Finset.Iic Nblock → LatticePoint d)))) →
                        LatticePoint d := fun θ ↦ (Zlift (s + 1) θ).2
                let step : Kernel (Finset.Iic s → LatticePoint d) (LatticePoint d) :=
                  Kernel.comap
                    (discreteMatrixKernel
                      (fun a b ↦
                        dirac_convolution_kernel ν.toMeasure a ({b} : Set (LatticePoint d))))
                    (fun h ↦ h ⟨s, Finset.mem_Iic.2 le_rfl⟩)
                    (by fun_prop)
                have hH_meas : Measurable H := by
                  exact Measurable.of_discrete
                have hnext_meas : Measurable next := by
                  exact Measurable.of_discrete
                have hsingleton :
                    ∀ h w,
                      μ.map (fun θ ↦ (H θ, next θ))
                          ({(h, w)} : Set ((Finset.Iic s → LatticePoint d) × LatticePoint d)) =
                        μ.map H ({h} : Set (Finset.Iic s → LatticePoint d)) *
                          step h ({w} : Set (LatticePoint d)) := by
                  have hsndEndPow :
                      IsMarkovProcessRealization
                        (fun n : ℕ ↦ dirac_convolution_kernel μN.toMeasure ^ n)
                        (fun b : LatticePoint d ↦ Pend (x, b))
                        (fun n ω ↦ (Zend n ω).2) := by
                    -- Proof comment: the second endpoint coordinate is the same auxiliary block
                    -- chain, rewritten from its singleton-mass matrix form to the owner kernel.
                    exact
                      endpointOwnerKernelRealization_of_blockRealization
                        (μN := μN)
                        (Z := fun n ω ↦ (Zend n ω).2)
                        (hZ := by
                          simpa using hEndSuccess.toIsMarkovCoupling.snd_realization x)
                  intro h w
                  -- Proof comment: the second-coordinate endgame is the symmetric singleton
                  -- factorization extracted above.
                  simpa [μ, H, next, step, Plift, mulift, Zlift, Kernel.comap_apply,
                    discreteMatrixKernel_apply] using
                    pairedEndpointBridgeLiftSnd_pairSingleton_eq_historyMass_mul_ownerStep
                      (ν := ν) (μN := μN) (P := Powner) (hP := howner) (Pend := Pend)
                      (hN := hNblock_pos) (hμN := hμN) (Zend := Zend) x y hsndEndPow s h w
                have hcondexp :
                    μ⟦next ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ]
                      fun θ ↦ (step (H θ)).real A := by
                  exact
                    condExp_eq_kernel_of_pairSingletonMass
                      μ H next step hH_meas hnext_meas hsingleton hA
                have hkernel :
                    (fun θ ↦ (step (H θ)).real A) =ᵐ[μ]
                      fun θ ↦
                        ((discreteMatrixKernel
                          (fun a b ↦
                            dirac_convolution_kernel ν.toMeasure a
                              ({b} : Set (LatticePoint d))))
                          ((Zlift s θ).2)).real A := by
                  -- Proof comment: after the `snd` singleton factorization, only the final
                  -- comap-to-current-state simplification remains.
                  exact Filter.Eventually.of_forall fun θ ↦ by
                    simp [step, H, Kernel.comap_apply, discreteMatrixKernel_apply]
                rw [generatedFiltrationSpace_eq_comap_historyIic
                  (X := fun n θ ↦ (Zlift n θ).2) s]
                exact hcondexp.trans hkernel
          refine
            { toIsMarkovCoupling := ?_
              tail_disagreement_tendsto_zero := ?_ }
          · -- Proof comment: once the shared Step 3 coupling theorem is supplied, the coordinate
            -- realizations are exactly its `fst_realization` and `snd_realization` fields.
            exact hLiftCoupling
          · intro x y
            simpa [Plift, mulift, Zlift] using
              pairedEndpointBridgeLift_tailDisagreement_tendsto_zero
                (P := Powner) (Pend := Pend) (Zend := Zend)
                (N := Nblock) hNblock_pos hEndSuccess x y

/-- Helper for Theorem 18.8: once the walk is rewritten as a convolution kernel driven by its
origin row, the remaining task is to construct the owner-level successful coupling. -/
theorem owner_exists_successfulCoupling_of_aperiodic_irreducible_latticeRandomWalk
    {d : ℕ} (ν : PMF (LatticePoint d))
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d)) (dirac_convolution_kernel ν.toMeasure)]
    (haperiodic : IsAperiodic (dirac_convolution_kernel ν.toMeasure)) :
    HasSuccessfulCoupling.{0, 0}
      (fun x y ↦ dirac_convolution_kernel ν.toMeasure x ({y} : Set (LatticePoint d))) := by
  by_cases hsub : Subsingleton (LatticePoint d)
  · -- Proof comment: in the degenerate branch, the canonical path-space realization is already
    -- diagonal, so the coupling is immediate.
    letI : Subsingleton (LatticePoint d) := hsub
    simpa using subsingletonOwner_hasSuccessfulCoupling (ν := ν)
  letI : IsMarkovKernel (dirac_convolution_kernel ν.toMeasure) :=
    diracConvolutionKernel_isMarkovOfPMF ν
  obtain ⟨N, lam, hlam_pos, hcube⟩ :=
    existsPositiveCubeBlockLowerBound (ν := ν) haperiodic
  have hN_pos : 0 < N := by
    -- Proof comment: in the nontrivial branch, the cube contains a nonzero point, so `N = 0`
    -- would force the `N`-step origin row to be Dirac at `0`, contradicting `hcube`.
    obtain ⟨z, hz_cube, hz_ne_zero⟩ :=
      exists_nonzero_uniformCubePoint_of_notSubsingleton (d := d) hsub
    by_contra hN_pos
    have hmass := hcube z hz_cube
    have hN_zero : N = 0 := Nat.eq_zero_of_not_pos hN_pos
    have hmass_zero : lam = 0 := by
      rw [hN_zero, pow_zero] at hmass
      change lam ≤ (Kernel.id (0 : LatticePoint d)) ({z} : Set (LatticePoint d)) at hmass
      simp [Kernel.id_apply, hz_ne_zero] at hmass
      exact hmass
    exact (ne_of_gt hlam_pos) hmass_zero
  let α : ENNReal := ((uniformCubePoints d).card : ENNReal) * lam
  have hα_pos : 0 < α := by
    -- Proof comment: the cube contains at least the origin, so the positive lower bound on each
    -- cube singleton mass yields a positive mixture coefficient.
    simpa [α] using uniformCubeBlockCoefficient_pos (d := d) hlam_pos
  have hα_le_one : α ≤ 1 := by
    -- Proof comment: summing the singleton lower bounds over the finite cube cannot exceed the
    -- total mass `1` of the `N`-step origin row.
    simpa [α] using uniformCubeBlockCoefficient_le_one (ν := ν) (N := N) hcube
  have hminorant :
      α • (uniformCubeStepPMF d).toMeasure ≤
        (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d) := by
    -- Proof comment: the singleton lower bounds assemble to a true measure minorant of the whole
    -- `N`-step origin row by the uniform cube law.
    simpa [α] using uniformCubeBlockMinorant (ν := ν) (N := N) hcube
  letI : IsMarkovKernel (dirac_convolution_kernel ν.toMeasure ^ N) :=
    diracConvolutionKernel_pow_isMarkovOfPMF (ν := ν) N
  let μN : PMF (LatticePoint d) :=
    ((dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d)).toPMF
  have hμN_toMeasure :
      μN.toMeasure = (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d) := by
    -- Proof comment: the `N`-step origin row is a probability measure because it is a row of a
    -- Markov kernel power, so `toPMF` is definitionally lossless here.
    simpa [μN] using
      (Measure.toPMF_toMeasure
        (μ := (dirac_convolution_kernel ν.toMeasure ^ N) (0 : LatticePoint d)))
  have hminorantPMF :
      α • (uniformCubeStepPMF d).toMeasure ≤ μN.toMeasure := by
    -- Proof comment: rewrite the block-row measure through its PMF normalization before
    -- extracting the residual law.
    simpa [hμN_toMeasure] using hminorant
  obtain ⟨ρ, hμN_decomp⟩ :=
    pmfEq_convexCombo_ofMeasureMinorant
      (μ := uniformCubeStepPMF d) (ν := μN) hα_le_one hminorantPMF
  have hblock :
      HasSuccessfulCoupling.{0, 0}
        (fun x y ↦ dirac_convolution_kernel μN.toMeasure x ({y} : Set (LatticePoint d))) := by
    -- Proof comment: the exact convex decomposition of the `N`-step origin law is the input for
    -- the owner-level Bernoulli-thinning construction.
    exact
      ownerMixture_hasSuccessfulCoupling_of_uniformCubeDecomp
        (η := μN) (ρ := ρ) hα_pos hα_le_one hμN_decomp
  -- Proof comment: once the block-time owner chain is successfully coupled, the remaining task
  -- is the block-splicing lift back to the original one-step owner walk.
  exact
    ownerHasSuccessfulCoupling_of_powHasSuccessfulCoupling
      (ν := ν) (μN := μN) hN_pos hμN_toMeasure hblock

/-- Theorem 18.8: every aperiodic irreducible translation-invariant random walk on `ℤ^d` admits a
successful coupling. -/
theorem translationInvariant_exists_successfulCoupling_of_aperiodic_irreducible_latticeRandomWalk
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    (hp : IsStochasticMatrix p) (htranslation : IsTranslationInvariantStepMatrix p)
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d)) (discreteMatrixKernel p)]
    (haperiodic : IsAperiodic (discreteMatrixKernel p)) :
    HasSuccessfulCoupling.{0, 0} p := by
  -- Route correction: the file had been overwritten by a self-import stub, so first re-establish
  -- the origin-row owner bridge and then reduce the theorem to the owner-level coupling result.
  letI : IsMarkovKernel (discreteMatrixKernel p) :=
    discreteMatrixKernel_isMarkovKernel p hp
  let ν : PMF (LatticePoint d) := (discreteMatrixKernel p 0).toPMF
  have hkernel :
      dirac_convolution_kernel ν.toMeasure = discreteMatrixKernel p := by
    -- Proof comment: translation invariance identifies the whole kernel with the origin-row
    -- convolution kernel.
    simpa [ν] using
      translationInvariantDiscreteKernel_eq_diracConvolutionKernel (p := p) htranslation
  have hmatrix :
      (fun x y ↦ dirac_convolution_kernel ν.toMeasure x ({y} : Set (LatticePoint d))) = p := by
    -- Proof comment: the matrix entries are exactly the singleton masses of the two kernels.
    funext x y
    simpa [ν] using translationInvariantOriginRow_step_eq (p := p) htranslation x y
  have hmatrixConv :
      (fun x y ↦ (Measure.dirac x ∗ ν.toMeasure) ({y} : Set (LatticePoint d))) = p := by
    -- Proof comment: the entrywise owner formula is just the unfolded kernel notation.
    simpa [dirac_convolution_kernel_apply] using hmatrix
  letI :
      Kernel.IsIrreducible
        (Measure.count : Measure (LatticePoint d)) (dirac_convolution_kernel ν.toMeasure) := by
    -- Proof comment: irreducibility transports across the kernel identity.
    simpa [hkernel] using
      (inferInstance :
        Kernel.IsIrreducible
          (Measure.count : Measure (LatticePoint d)) (discreteMatrixKernel p))
  have haperiodicOwner : IsAperiodic (dirac_convolution_kernel ν.toMeasure) := by
    -- Proof comment: the state-period statement is about the kernel itself, so the same rewrite
    -- moves aperiodicity to the owner kernel.
    simpa [hkernel] using haperiodic
  simpa [hmatrixConv] using
    owner_exists_successfulCoupling_of_aperiodic_irreducible_latticeRandomWalk
      (ν := ν) haperiodicOwner

end ProbabilityTheory
