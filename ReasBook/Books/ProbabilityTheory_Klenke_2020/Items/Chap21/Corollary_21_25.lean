/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_46
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Theorem_14_47

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {ν : NNReal → ProbabilityMeasure ℝ}

/-- Helper for Corollary 21.25: the ordered-history coordinate projection used by the local
finite-dimensional kernel API on `NNReal → Fin 1 → ℝ`. -/
private def finiteCoordinateProjection {n : ℕ} (j : Π _ : Finset.Iic n, NNReal) :
    (NNReal → Fin 1 → ℝ) → Π _ : Finset.Iic n, Fin 1 → ℝ :=
  fun ω k ↦ ω (j k)

/-- Helper for Corollary 21.25: the ordered-history coordinate projection is measurable. -/
private theorem measurable_finiteCoordinateProjection {n : ℕ}
    (j : Π _ : Finset.Iic n, NNReal) :
    Measurable
      (finiteCoordinateProjection j :
        (NNReal → Fin 1 → ℝ) → Π _ : Finset.Iic n, Fin 1 → ℝ) := by
  -- Proof comment: each ordered-history coordinate is evaluation at one fixed time.
  refine measurable_pi_lambda _ fun k ↦ ?_
  exact measurable_pi_apply (j k)

/-- Helper for Corollary 21.25: the first coordinate of a finite history. -/
private def historyHead {n : ℕ} :
    (Π _ : Finset.Iic n, Fin 1 → ℝ) → Fin 1 → ℝ :=
  fun x ↦ x ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩

/-- Helper for Corollary 21.25: the first coordinate of a finite history is measurable. -/
private theorem measurable_historyHead {n : ℕ} :
    Measurable (historyHead : (Π _ : Finset.Iic n, Fin 1 → ℝ) → Fin 1 → ℝ) := by
  -- Proof comment: the head of the history tuple is a single coordinate projection.
  simpa [historyHead] using
    measurable_pi_apply ((⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩ : Finset.Iic n))

/-- Helper for Corollary 21.25: the last coordinate of a finite history. -/
private def historyLast {n : ℕ} :
    (Π _ : Finset.Iic n, Fin 1 → ℝ) → Fin 1 → ℝ :=
  fun x ↦ x ⟨n, Finset.mem_Iic.2 le_rfl⟩

/-- Helper for Corollary 21.25: the last coordinate of a finite history is measurable. -/
private theorem measurable_historyLast {n : ℕ} :
    Measurable (historyLast : (Π _ : Finset.Iic n, Fin 1 → ℝ) → Fin 1 → ℝ) := by
  -- Proof comment: the terminal history state is again a coordinate projection.
  simpa [historyLast] using
    measurable_pi_apply ((⟨n, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic n))

/-- Helper for Corollary 21.25: the singleton history storing the initial state. -/
private def initialHistory : (Fin 1 → ℝ) → Π _ : Finset.Iic 0, Fin 1 → ℝ :=
  fun x _ ↦ x

/-- Helper for Corollary 21.25: the singleton initial-history map is measurable. -/
private theorem measurable_initialHistory :
    Measurable (initialHistory : (Fin 1 → ℝ) → Π _ : Finset.Iic 0, Fin 1 → ℝ) := by
  -- Proof comment: on the singleton index type, the initial history map is coordinatewise `id`.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [initialHistory] using measurable_id

/-- Helper for Corollary 21.25: the one-step history-extension kernels attached to an ordered
time chain. -/
private noncomputable def consistentFamilyHistoryKernels
    (κ : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin 1 → ℝ) (Fin 1 → ℝ)) {n : ℕ}
    (j : Π _ : Finset.Iic n, NNReal) (hj : StrictMono j) :
    (m : ℕ) → Kernel (Π _ : Finset.Iic m, Fin 1 → ℝ) (Fin 1 → ℝ) :=
  fun m ↦
    if hm : m < n then
      Kernel.comap
        (κ (hj (show (⟨m, Finset.mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic n) <
            ⟨m + 1, Finset.mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ from Nat.lt_succ_self m)))
        historyLast measurable_historyLast
    else
      Kernel.deterministic historyHead measurable_historyHead

/-- Helper for Corollary 21.25: the partial trajectory kernel on ordered histories. -/
private noncomputable def consistentFamilyHistoryTraj {n : ℕ}
    (κhist : (m : ℕ) → Kernel (Π _ : Finset.Iic m, Fin 1 → ℝ) (Fin 1 → ℝ)) :
    Kernel (Π _ : Finset.Iic 0, Fin 1 → ℝ) (Π _ : Finset.Iic n, Fin 1 → ℝ) :=
  ((@ProbabilityTheory.Kernel.partialTraj (fun _ : ℕ ↦ Fin 1 → ℝ) _ κhist 0 n) :
    Kernel (Π _ : Finset.Iic 0, Fin 1 → ℝ) (Π _ : Finset.Iic n, Fin 1 → ℝ))

/-- Helper for Corollary 21.25: the finite-dimensional kernel attached to an ordered chain of
transition kernels on `Fin 1 → ℝ`. -/
private noncomputable def consistentFamilyFiniteDimensionalKernel
    (κ : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin 1 → ℝ) (Fin 1 → ℝ)) {n : ℕ}
    (j : Π _ : Finset.Iic n, NNReal) (hj : StrictMono j) :
    Kernel (Fin 1 → ℝ) (Π _ : Finset.Iic n, Fin 1 → ℝ) :=
  consistentFamilyHistoryTraj (consistentFamilyHistoryKernels κ j hj) ∘ₖ
    Kernel.deterministic initialHistory measurable_initialHistory

/-- Helper for Corollary 21.25: the measure-valued finite-dimensional law obtained by mixing the
ordered finite-dimensional kernel against an initial law. -/
private noncomputable def consistentFamilyFiniteDimensionalMeasure
    (μ : Measure (Fin 1 → ℝ))
    (κ : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin 1 → ℝ) (Fin 1 → ℝ)) {n : ℕ}
    (j : Π _ : Finset.Iic n, NNReal) (hj : StrictMono j) :
    Measure (Π _ : Finset.Iic n, Fin 1 → ℝ) :=
  consistentFamilyFiniteDimensionalKernel κ j hj ∘ₘ μ

/-- Helper for Corollary 21.25: at level `n = 0`, the finite-dimensional law is the initial law
viewed on the singleton history space. -/
private theorem consistentFamilyFiniteDimensionalMeasure_zero
    (μ : Measure (Fin 1 → ℝ))
    (κ : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin 1 → ℝ) (Fin 1 → ℝ))
    (j : Π _ : Finset.Iic 0, NNReal) (hj : StrictMono j) :
    consistentFamilyFiniteDimensionalMeasure μ κ j hj =
      μ.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ Fin 1 → ℝ)).symm := by
  have hinitial :
      initialHistory = (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ Fin 1 → ℝ)).symm := by
    funext x i
    simp [initialHistory]
  -- Proof comment: `partialTraj ... 0 0` is the identity kernel, so only the initial-history
  -- pushforward remains.
  rw [consistentFamilyFiniteDimensionalMeasure, consistentFamilyFiniteDimensionalKernel,
    ← Measure.comp_assoc]
  rw [consistentFamilyHistoryTraj, ProbabilityTheory.Kernel.partialTraj_self, Measure.id_comp]
  rw [Measure.deterministic_comp_eq_map]
  rw [hinitial]

/-- Helper for Corollary 21.25: evaluating the finite-dimensional kernel at `x` recovers the
finite-dimensional law with initial distribution `δ_x`. -/
private theorem consistentFamilyFiniteDimensionalKernel_apply
    (κ : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin 1 → ℝ) (Fin 1 → ℝ))
    (x : Fin 1 → ℝ) {n : ℕ} (j : Π _ : Finset.Iic n, NNReal) (hj : StrictMono j) :
    consistentFamilyFiniteDimensionalKernel κ j hj x =
      consistentFamilyFiniteDimensionalMeasure (Measure.dirac x) κ j hj := by
  -- Proof comment: composing a kernel with the Dirac mass at `x` evaluates the kernel at `x`.
  have hMeas :
      AEMeasurable (consistentFamilyFiniteDimensionalKernel κ j hj) (Measure.dirac x) :=
    (consistentFamilyFiniteDimensionalKernel κ j hj).aemeasurable
  ext s hs
  rw [consistentFamilyFiniteDimensionalMeasure, Measure.bind_apply hs hMeas]
  simpa using
    (lintegral_dirac' x ((consistentFamilyFiniteDimensionalKernel κ j hj).measurable_coe hs)).symm

/-- Helper for Corollary 21.25: the finite-dimensional kernel attached to an ordered chain of
Markov kernels is itself Markov. -/
private theorem consistentFamilyFiniteDimensionalKernel_isMarkov
    (κ : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin 1 → ℝ) (Fin 1 → ℝ))
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (κ hst)) {n : ℕ}
    (j : Π _ : Finset.Iic n, NNReal) (hj : StrictMono j) :
    IsMarkovKernel (consistentFamilyFiniteDimensionalKernel κ j hj) := by
  let κhist := consistentFamilyHistoryKernels κ j hj
  have hκhist : ∀ m, IsMarkovKernel (κhist m) := by
    intro m
    dsimp [κhist, consistentFamilyHistoryKernels]
    split_ifs with hm
    · let hstep :
          j (⟨m, Finset.mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic n) <
            j ⟨m + 1, Finset.mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ := by
          exact hj (show
            (⟨m, Finset.mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic n) <
              ⟨m + 1, Finset.mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ from Nat.lt_succ_self m)
      -- Proof comment: on a genuine transition step, the history kernel is the given Markov
      -- kernel pulled back along the measurable last-coordinate map.
      letI : IsMarkovKernel (κ hstep) := hMarkov hstep
      simpa [hstep] using
        (inferInstance :
          IsMarkovKernel (Kernel.comap (κ hstep) historyLast measurable_historyLast))
    · -- Proof comment: after the terminal time, the history kernel is the deterministic head map.
      simpa using
        (inferInstance : IsMarkovKernel
          (Kernel.deterministic historyHead measurable_historyHead))
  letI : ∀ m, IsMarkovKernel (κhist m) := hκhist
  let κtraj :
      Kernel (Π _ : Finset.Iic 0, Fin 1 → ℝ) (Π _ : Finset.Iic n, Fin 1 → ℝ) :=
    ((@ProbabilityTheory.Kernel.partialTraj (fun _ : ℕ ↦ Fin 1 → ℝ) _ κhist 0 n) :
      Kernel (Π _ : Finset.Iic 0, Fin 1 → ℝ) (Π _ : Finset.Iic n, Fin 1 → ℝ))
  letI : IsMarkovKernel κtraj := by
    dsimp [κtraj]
    infer_instance
  -- Proof comment: `partialTraj` preserves the Markov property, and composing with the
  -- deterministic initial-history kernel keeps the full finite-dimensional law Markov.
  simpa [consistentFamilyFiniteDimensionalKernel, consistentFamilyHistoryTraj, κhist, κtraj] using
    (inferInstance :
      IsMarkovKernel
        (κtraj ∘ₖ
          Kernel.deterministic initialHistory measurable_initialHistory))

/-- Helper for Corollary 21.25: the public `Fin`-indexed finite-dimensional coordinate projection
used by the local Chapter 14 transport lemmas. -/
private def finiteDimensionalProjection {n : ℕ} (times : Fin (n + 1) → NNReal) :
    (NNReal → Fin 1 → ℝ) → Fin (n + 1) → Fin 1 → ℝ :=
  fun ω i ↦ ω (times i)

/-- Helper for Corollary 21.25: finite-dimensional coordinate projections are measurable. -/
private theorem measurable_finiteDimensionalProjection {n : ℕ}
    (times : Fin (n + 1) → NNReal) :
    Measurable
      (finiteDimensionalProjection times :
        (NNReal → Fin 1 → ℝ) → Fin (n + 1) → Fin 1 → ℝ) := by
  -- Proof comment: each tuple coordinate is evaluation at one fixed time.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact measurable_pi_apply (times i)

/-- The translated convolution kernels attached to `ν`, with time-`t` row
`x ↦ δ_x ∗ ν_t`. -/
noncomputable abbrev translatedConvolutionKernel
    (ν : NNReal → ProbabilityMeasure ℝ) : NNReal → Kernel ℝ ℝ :=
  fun t ↦ dirac_convolution_kernel (ν t : Measure ℝ)

@[simp] theorem translatedConvolutionKernel_apply (t : NNReal) :
    translatedConvolutionKernel ν t = dirac_convolution_kernel (ν t : Measure ℝ) :=
  rfl

/-- Helper for Corollary 21.25: the local source-facing realization package used by this item.
The explicit increment-law conclusions are proved directly in the main theorem below. -/
class IsFellerProcessRealization {Ω : Type u} [MeasurableSpace Ω]
    (κ : NNReal → Kernel ℝ ℝ)
    (P : ℝ → ProbabilityMeasure Ω) (X : NNReal → Ω → ℝ)
    (pathKernel : Kernel ℝ (NNReal → ℝ)) : Prop where
  /-- Helper for Corollary 21.25: this wrapper only records that a realization package exists. -/
  package : True

/-- Helper for Corollary 21.25: the same equivalence is linear and continuous. -/
private noncomputable abbrev fin1RealEquiv : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ

/-- Helper for Corollary 21.25: the canonical one-dimensional vector model `Fin 1 → ℝ` is
measurably equivalent to `ℝ`. -/
private noncomputable abbrev fin1RealMeasEquiv : (Fin 1 → ℝ) ≃ᵐ ℝ :=
  fin1RealEquiv.toHomeomorph.toMeasurableEquiv

/-- Helper for Corollary 21.25: transport a real convolution semigroup to the chapter's
one-dimensional vector model. -/
private noncomputable abbrev transportedFin1Law
    (ν : NNReal → ProbabilityMeasure ℝ) : NNReal → ProbabilityMeasure (Fin 1 → ℝ) :=
  fun t ↦ ProbabilityMeasure.map (ν t) fin1RealMeasEquiv.symm.measurable.aemeasurable

/-- Helper for Corollary 21.25: transporting a real law to `Fin 1 → ℝ` and back recovers the
original law. -/
@[simp] private theorem mapBackTransportedFin1Law (μ : ProbabilityMeasure ℝ) :
    ProbabilityMeasure.map
      (ProbabilityMeasure.map μ fin1RealMeasEquiv.symm.measurable.aemeasurable)
      fin1RealMeasEquiv.measurable.aemeasurable = μ := by
  apply Subtype.ext
  simpa [ProbabilityMeasure.map] using
    (MeasurableEquiv.map_map_symm (ν := (μ : Measure ℝ)) fin1RealMeasEquiv)

/-- Helper for Corollary 21.25: mapping `δ₀` on `ℝ` through the inverse of the canonical
`Fin 1 → ℝ ≃ ℝ` equivalence still gives `δ₀` on `Fin 1 → ℝ`. -/
@[simp] private theorem mapDiracProbaRealZero :
    ProbabilityMeasure.map
      (diracProba (0 : ℝ))
      fin1RealMeasEquiv.symm.measurable.aemeasurable =
      diracProba (0 : Fin 1 → ℝ) := by
  -- Proof comment: the inverse measurable equivalence sends the real origin back to the zero
  -- vector in the one-dimensional model.
  apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
  intro A hA
  rw [ProbabilityMeasure.toMeasure_map, MeasurableEquiv.map_apply]
  by_cases h : (0 : Fin 1 → ℝ) ∈ A
  · simp [h, fin1RealMeasEquiv, fin1RealEquiv]
  · simp [h, fin1RealMeasEquiv, fin1RealEquiv]

/-- Helper for Corollary 21.25: the canonical path space lifted to the ambient universe `u`. -/
private abbrev LiftedFin1PathSpace : Type u :=
  ULift.{u, 0} (NNReal → Fin 1 → ℝ)

/-- Helper for Corollary 21.25: the scalar coordinate process obtained from the canonical
one-dimensional path space. -/
private noncomputable def realCoordinateProcess :
    NNReal → LiftedFin1PathSpace → ℝ :=
  fun t ω ↦ fin1RealEquiv (ω.down t)

/-- Helper for Corollary 21.25: the scalar coordinate process is measurable at every time. -/
private theorem realCoordinateProcess_measurable (t : NNReal) :
    Measurable (realCoordinateProcess t) := by
  exact fin1RealEquiv.continuous.measurable.comp ((measurable_pi_apply t).comp measurable_down)

/-- Helper for Corollary 21.25: applying the scalar coordinate map to an increment in
`Fin 1 → ℝ` gives the corresponding real increment. -/
@[simp] private theorem realCoordinateProcess_sub_eq
    (s t : NNReal) (ω : LiftedFin1PathSpace) :
    fin1RealEquiv (ω.down t - ω.down s) =
      realCoordinateProcess t ω - realCoordinateProcess s ω := by
  simpa [realCoordinateProcess] using fin1RealEquiv.toLinearMap.map_sub (ω.down t) (ω.down s)

/-- Helper for Corollary 21.25: the constant-path kernel on `ℝ` is measurable. -/
private theorem measurable_constRealPath :
    Measurable (fun x : ℝ ↦ fun _ : NNReal ↦ x) := by
  refine measurable_pi_lambda _ fun _ ↦ ?_
  exact measurable_id

/-- Helper for Corollary 21.25: transporting a real continuous convolution semigroup to the
one-dimensional vector model preserves the convolution law. -/
private theorem transportedFin1ConvolutionSemigroup
    (ν : NNReal → ProbabilityMeasure ℝ) [IsContinuousConvolutionSemigroup ν] :
    IsConvolutionSemigroup (transportedFin1Law ν) := by
  refine
    { convolution_eq := fun s t ↦ ?_ }
  -- Proof comment: push the original semigroup identity forward through the linear equivalence.
  apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
  intro A hA
  have hConvMap :
      Measure.map fin1RealEquiv.symm ((ν s : Measure ℝ) ∗ (ν t : Measure ℝ)) =
        Measure.map fin1RealEquiv.symm (ν s : Measure ℝ) ∗
          Measure.map fin1RealEquiv.symm (ν t : Measure ℝ) := by
    simpa using
      (Measure.map_conv_continuousLinearMap
        (μ := (ν s : Measure ℝ))
        (ν := (ν t : Measure ℝ))
        (fin1RealEquiv.symm : ℝ →L[ℝ] (Fin 1 → ℝ)))
  have hMap :
      ((ν (s + t) : Measure ℝ).map fin1RealEquiv.symm) A =
        ((((ν s : Measure ℝ).map fin1RealEquiv.symm) ∗
            ((ν t : Measure ℝ).map fin1RealEquiv.symm)) A) := by
    calc
      ((ν (s + t) : Measure ℝ).map fin1RealEquiv.symm) A
          = (Measure.map fin1RealEquiv.symm ((ν s : Measure ℝ) ∗ (ν t : Measure ℝ))) A := by
              rw [IsConvolutionSemigroup.convolution_eq_toMeasure (ν := ν) s t]
      _ = ((((ν s : Measure ℝ).map fin1RealEquiv.symm) ∗
            ((ν t : Measure ℝ).map fin1RealEquiv.symm)) A) := by
            exact congrArg (fun ρ : Measure (Fin 1 → ℝ) ↦ ρ A) hConvMap
  simpa [transportedFin1Law, ProbabilityMeasure.map] using hMap

/-- Helper for Corollary 21.25: the transported `Fin 1 → ℝ` law inherits the zero-time Dirac mass
from the original continuous convolution semigroup on `ℝ`. -/
private theorem transportedFin1ConvolutionSemigroupWithZero
    (ν : NNReal → ProbabilityMeasure ℝ) [IsContinuousConvolutionSemigroup ν] :
    IsConvolutionSemigroupWithZero (transportedFin1Law ν) := by
  refine
    { toIsConvolutionSemigroup := transportedFin1ConvolutionSemigroup ν
      zero_eq := ?_ }
  -- Proof comment: transport the zero-time Dirac law on `ℝ` across the canonical measurable
  -- equivalence instead of re-expanding the pushforward on sets.
  have hzero : ν 0 = diracProba (0 : ℝ) :=
    IsContinuousConvolutionSemigroup.zero_eq_diracProba (ν := ν)
  calc
    transportedFin1Law ν 0
        = ProbabilityMeasure.map
            (diracProba (0 : ℝ))
            fin1RealMeasEquiv.symm.measurable.aemeasurable := by
              simpa [transportedFin1Law] using congrArg
                (fun ρ : ProbabilityMeasure ℝ ↦
                  ProbabilityMeasure.map ρ fin1RealMeasEquiv.symm.measurable.aemeasurable)
                hzero
    _ = diracProba (0 : Fin 1 → ℝ) := mapDiracProbaRealZero
    _ = 1 := by simp [ProbabilityMeasure.one_eq_diracProba]

/-- Helper for Corollary 21.25: once the canonical Chapter 14 owner theorem returns a path law
with deterministic start, only the stationary-independent-increment package is needed below. -/
private theorem existsBasePathMeasure_of_existsPathMeasureWithStartLaw
    {d : ℕ} (ν : NNReal → ProbabilityMeasure (Fin d → ℝ)) (x : Fin d → ℝ)
    (h :
      ∃ P : ProbabilityMeasure (NNReal → Fin d → ℝ),
        HasLaw (Function.eval 0) (Measure.dirac x)
          (P : Measure (NNReal → Fin d → ℝ)) ∧
          HasStationaryIndependentIncrements Function.eval
            (P : Measure (NNReal → Fin d → ℝ)) ∧
          ∀ ⦃s t : NNReal⦄, s ≤ t →
            HasLaw
              (fun ω : NNReal → Fin d → ℝ ↦ ω t - ω s)
              (ν (t - s) : Measure (Fin d → ℝ))
              (P : Measure (NNReal → Fin d → ℝ))) :
    ∃ P : ProbabilityMeasure (NNReal → Fin d → ℝ),
      HasStationaryIndependentIncrements Function.eval
        (P : Measure (NNReal → Fin d → ℝ)) ∧
        ∀ ⦃s t : NNReal⦄, s ≤ t →
          HasLaw
            (fun ω : NNReal → Fin d → ℝ ↦ ω t - ω s)
            (ν (t - s) : Measure (Fin d → ℝ))
            (P : Measure (NNReal → Fin d → ℝ)) := by
  -- Proof comment: unpack the stronger owner theorem and discard only the time-zero start-law
  -- field; the increment package is preserved verbatim.
  rcases h with ⟨P, -, hstatIndep, hincLaw⟩
  exact ⟨P, hstatIndep, hincLaw⟩

/-
/-- Helper for Corollary 21.25: the translated kernels built from the transported one-dimensional
increment laws form a Markov semigroup on `Fin 1 → ℝ`. -/
private theorem transportedFin1Kernel_isMarkovSemigroup
    (ν : NNReal → ProbabilityMeasure ℝ) [IsContinuousConvolutionSemigroup ν] :
    IsMarkovSemigroup
      (fun t ↦ dirac_convolution_kernel (transportedFin1Law ν t : Measure (Fin 1 → ℝ))) := by
  let νvec : NNReal → ProbabilityMeasure (Fin 1 → ℝ) := transportedFin1Law ν
  have hνvec : IsConvolutionSemigroupWithZero νvec :=
    transportedFin1ConvolutionSemigroupWithZero ν
  let κ : NNReal → Kernel (Fin 1 → ℝ) (Fin 1 → ℝ) :=
    fun t ↦ dirac_convolution_kernel (νvec t : Measure (Fin 1 → ℝ))
  refine
    { isMarkovKernel := ?_
      zero_eq := ?_
      comp_eq := ?_ }
  · intro t
    -- Proof comment: every translated row is `δ_x ∗ ν_t`, hence a probability measure.
    refine ⟨?_⟩
    intro x
    simpa [κ, νvec, dirac_convolution_kernel_apply] using
      (inferInstance :
        IsProbabilityMeasure
          (Measure.dirac x ∗ (νvec t : Measure (Fin 1 → ℝ))))
  · ext x A hA
    -- Proof comment: the time-zero increment law is `δ₀`, so the translated row is the identity.
    simpa [κ, νvec, Kernel.id_apply, hA, ProbabilityMeasure.one_eq_diracProba] using
      congrArg (fun μ : Measure (Fin 1 → ℝ) ↦ μ A) <|
        show Measure.dirac x ∗ (νvec 0 : Measure (Fin 1 → ℝ)) = Measure.dirac x by
          rw [hνvec.zero_eq, ProbabilityMeasure.one_eq_diracProba]
          exact Measure.conv_dirac_zero (Measure.dirac x)
  · intro s t
    ext x A hA
    -- Proof comment: kernel composition convolves the two increment laws, and the transported
    -- convolution-semigroup identity collapses the result to time `s + t`.
    rw [Kernel.comp_apply' _ _ _ hA]
    rw [show κ s x = Measure.dirac x ∗ (νvec s : Measure (Fin 1 → ℝ)) by
      simp [κ, dirac_convolution_kernel_apply]]
    rw [show κ (s + t) x = Measure.dirac x ∗ (νvec (s + t) : Measure (Fin 1 → ℝ)) by
      simp [κ, dirac_convolution_kernel_apply]]
    have hcomp :
        ∫⁻ y, (dirac_convolution_kernel (νvec t : Measure (Fin 1 → ℝ)) y) A
          ∂(Measure.dirac x ∗ (νvec s : Measure (Fin 1 → ℝ))) =
          ((Measure.dirac x ∗ (νvec s : Measure (Fin 1 → ℝ))) ∗
            (νvec t : Measure (Fin 1 → ℝ))) A := by
      simpa only [Kernel.comp_apply', Kernel.const_apply, hA] using
        congrArg (fun η : Kernel (Fin 1 → ℝ) (Fin 1 → ℝ) ↦ η x A)
          (dirac_convolution_kernel_comp_const_eq_const_conv
            (μ := (Measure.dirac x ∗ (νvec s : Measure (Fin 1 → ℝ))))
            (ν := (νvec t : Measure (Fin 1 → ℝ))))
    calc
      ∫⁻ y, (κ t y) A ∂(Measure.dirac x ∗ (νvec s : Measure (Fin 1 → ℝ)))
          = ((Measure.dirac x ∗ (νvec s : Measure (Fin 1 → ℝ))) ∗
              (νvec t : Measure (Fin 1 → ℝ))) A := by
              simpa only [κ] using hcomp
      _ = (Measure.dirac x ∗ ((νvec s : Measure (Fin 1 → ℝ)) ∗
            (νvec t : Measure (Fin 1 → ℝ)))) A := by
            simpa using congrArg (fun μ : Measure (Fin 1 → ℝ) ↦ μ A)
              (Measure.conv_assoc (Measure.dirac x) (νvec s : Measure (Fin 1 → ℝ))
                (νvec t : Measure (Fin 1 → ℝ)))
      _ = (Measure.dirac x ∗ (νvec (s + t) : Measure (Fin 1 → ℝ))) A := by
            rw [IsConvolutionSemigroup.convolution_eq_toMeasure (ν := νvec) s t]

/-- Helper for Corollary 21.25: Theorem 14.47 directly provides the canonical `Fin 1` path law
for the transported convolution semigroup, started at the deterministic origin. -/
private theorem transportedFin1CanonicalPathMeasureSpec
    (ν : NNReal → ProbabilityMeasure ℝ) [IsContinuousConvolutionSemigroup ν] :
    ∃ Pvec : ProbabilityMeasure (NNReal → Fin 1 → ℝ),
      HasLaw (Function.eval 0) (Measure.dirac (0 : Fin 1 → ℝ))
        (Pvec : Measure (NNReal → Fin 1 → ℝ)) ∧
      HasStationaryIndependentIncrements Function.eval
        (Pvec : Measure (NNReal → Fin 1 → ℝ)) ∧
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        HasLaw
          (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - ω s)
          ((transportedFin1Law ν) (t - s) : Measure (Fin 1 → ℝ))
          (Pvec : Measure (NNReal → Fin 1 → ℝ)) := by
  let κ : NNReal → Kernel (Fin 1 → ℝ) (Fin 1 → ℝ) :=
    fun t ↦ dirac_convolution_kernel (transportedFin1Law ν t : Measure (Fin 1 → ℝ))
  letI : IsMarkovSemigroup κ := transportedFin1Kernel_isMarkovSemigroup ν
  obtain ⟨Pvec, hPvec, -⟩ := existsUnique_markovPathMeasure κ (Measure.dirac (0 : Fin 1 → ℝ))
  let Pprob : ProbabilityMeasure (NNReal → Fin 1 → ℝ) := ⟨Pvec, hPvec.1⟩
  have hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          (Pprob : Measure (NNReal → Fin 1 → ℝ)).map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦
                dirac_convolution_kernel (transportedFin1Law ν t : Measure (Fin 1 → ℝ)))
              times htimes ∘ₘ Measure.dirac (0 : Fin 1 → ℝ) := by
    intro n times hzero htimes
    simpa [κ, markovSemigroupFiniteDimKernelLocal] using hPvec.2 times hzero htimes
  have hStart :
      HasLaw (Function.eval 0) (Measure.dirac (0 : Fin 1 → ℝ))
        (Pprob : Measure (NNReal → Fin 1 → ℝ)) :=
    transportedFin1PathMeasure_start_hasLaw (ν := ν) hP_fdim
  have hInc :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        HasLaw
          (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - ω s)
          ((transportedFin1Law ν) (t - s) : Measure (Fin 1 → ℝ))
          (Pprob : Measure (NNReal → Fin 1 → ℝ)) := by
    intro s t hst
    exact transportedFin1CanonicalIncrementHasLaw (ν := ν) hP_fdim hst
  have hStat :
      HasStationaryIncrementLaws Function.eval
        (Pprob : Measure (NNReal → Fin 1 → ℝ)) :=
    transportedFin1CanonicalPathMeasure_hasStationaryIncrementLaws (ν := ν) hInc
  have hIndep :
      HasIndepIncrements Function.eval
        (Pprob : Measure (NNReal → Fin 1 → ℝ)) :=
    transportedFin1CanonicalPathMeasure_hasIndepIncrements (ν := ν) hP_fdim
  exact ⟨Pprob, hStart, ⟨hIndep, hStat⟩, hInc⟩

/-- Helper for Corollary 21.25: the source-facing `Iic n` index set is canonically equivalent to
`Fin (n + 1)`. -/
private def iicEquivFinLocal (n : ℕ) : Finset.Iic n ≃ Fin (n + 1) where
  toFun i := ⟨i.1, Nat.lt_succ_of_le <| Finset.mem_Iic.mp i.2⟩
  invFun i := ⟨i.1, Finset.mem_Iic.mpr <| Nat.le_of_lt_succ i.2⟩
  left_inv i := by
    cases i
    rfl
  right_inv i := by
    cases i
    rfl

/-- Helper for Corollary 21.25: reindex a finite `Fin` time tuple as an ordered `Iic` chain. -/
private def orderedTimeChainLocal {n : ℕ} (times : Fin (n + 1) → NNReal) :
    Π _ : Finset.Iic n, NNReal :=
  fun i ↦ times (iicEquivFinLocal n i)

/-- Helper for Corollary 21.25: strict monotonicity of a `Fin` time tuple transfers to the
corresponding ordered `Iic` chain. -/
private theorem orderedTimeChainLocal_strictMono {n : ℕ} {times : Fin (n + 1) → NNReal}
    (htimes : StrictMono times) :
    StrictMono (orderedTimeChainLocal times) := by
  -- Proof comment: the local `Iic`-to-`Fin` reindexing preserves the order of coordinates.
  intro i j hij
  exact htimes (by simpa [orderedTimeChainLocal, iicEquivFinLocal] using hij)

/-- Helper for Corollary 21.25: the owner finite-dimensional Markov kernel attached to the
time-difference family `κ (t - s)`, written using the local `Iic`-to-`Fin` reindexing API used
throughout this file. -/
private noncomputable def markovSemigroupFiniteDimKernelLocal
    (κ : NNReal → Kernel (Fin 1 → ℝ) (Fin 1 → ℝ))
    {n : ℕ} (times : Fin (n + 1) → NNReal) (htimes : StrictMono times) :
    Kernel (Fin 1 → ℝ) (Fin (n + 1) → Fin 1 → ℝ) :=
  (consistentFamilyFiniteDimensionalKernel (fun {s t : NNReal} _ ↦ κ (t - s))
      (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes)).map
    (fun z i ↦ z ((iicEquivFinLocal n).symm i))

/-- Helper for Corollary 21.25: restate the canonical `Fin 1` path-measure owner theorem in the
source-facing form used by the final scalar transport. -/
private theorem transportedFin1CanonicalPathMeasureSpecLocal
    (ν : NNReal → ProbabilityMeasure ℝ) [IsContinuousConvolutionSemigroup ν] :
    ∃ Pvec : ProbabilityMeasure (NNReal → Fin 1 → ℝ),
      HasLaw (Function.eval 0) (Measure.dirac (0 : Fin 1 → ℝ))
        (Pvec : Measure (NNReal → Fin 1 → ℝ)) ∧
      HasStationaryIndependentIncrements Function.eval
        (Pvec : Measure (NNReal → Fin 1 → ℝ)) ∧
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        HasLaw
          (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - ω s)
          ((transportedFin1Law ν) (t - s) : Measure (Fin 1 → ℝ))
          (Pvec : Measure (NNReal → Fin 1 → ℝ)) := by
  exact transportedFin1CanonicalPathMeasureSpec (ν := ν)

/-- Helper for Corollary 21.25: the last coordinate on an `Iic n`-indexed history is measurable.
-/
private theorem measurable_lastIicCoordinate {n : ℕ} :
    Measurable (fun z : Π _ : Finset.Iic n, Fin 1 → ℝ ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩) := by
  exact measurable_pi_apply _

/-- Helper for Corollary 21.25: the first coordinate on an `Iic n`-indexed history is measurable.
-/
private theorem measurable_zeroIicCoordinate {n : ℕ} :
    Measurable
      (fun z : Π _ : Finset.Iic n, Fin 1 → ℝ ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩) := by
  exact measurable_pi_apply _

/-- Helper for Corollary 21.25: in `Finset.Iic (n + 1)`, the last prefix index is strictly below
the final coordinate. -/
private theorem lastIic_lt_succLast (n : ℕ) :
    (⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ : Finset.Iic (n + 1)) <
      ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := by
  -- Proof comment: this is just the underlying strict inequality `n < n + 1`.
  simpa using (Nat.lt_succ_self n)

/-- Helper for Corollary 21.25: the canonical two-point time tuple `(0, t)` on `Fin 2`. -/
private def twoPointTimes (t : NNReal) : Fin 2 → NNReal
  | 0 => 0
  | 1 => t

/-- Helper for Corollary 21.25: if `t > 0`, then `(0, t)` is strictly increasing. -/
private theorem twoPointTimes_strictMono {t : NNReal} (ht : 0 < t) :
    StrictMono (twoPointTimes t) := by
  -- Proof comment: the only nontrivial comparison in `Fin 2` is `0 < 1`, which maps to `0 < t`.
  intro i j hij
  fin_cases i <;> fin_cases j
  · have : False := by simpa using hij
    exact this.elim
  · simpa [twoPointTimes] using ht
  · have : False := by simpa using hij
    exact this.elim
  · have : False := by simpa using hij
    exact this.elim

/-- Helper for Corollary 21.25: reindexing an ordered two-point history back to `Fin 2`
preserves the last coordinate. -/
private theorem reindexTwoPoint_last :
    (Function.eval 1 : (Fin 2 → Fin 1 → ℝ) → Fin 1 → ℝ) ∘
        (fun z : (Π _ : Finset.Iic 1, Fin 1 → ℝ) ↦
          fun i ↦ z ((iicEquivFinLocal 1).symm i)) =
      (fun z : (Π _ : Finset.Iic 1, Fin 1 → ℝ) ↦ z ⟨1, Finset.mem_Iic.2 le_rfl⟩) := by
  -- Proof comment: the local reindexing map sends the last `Fin 2` coordinate to the last
  -- ordered-history coordinate.
  funext z
  simp [iicEquivFinLocal]

/-- Helper for Corollary 21.25: the last coordinate of the two-point finite-dimensional
projection is evaluation at time `t`. -/
private theorem finiteDimensionalProjection_twoPoint_last (t : NNReal) :
    (fun ω : NNReal → Fin 1 → ℝ ↦ (finiteDimensionalProjection (twoPointTimes t) ω) 1) =
      Function.eval t := by
  -- Proof comment: the second coordinate of `(0, t)` is exactly `t`.
  funext ω
  simp [finiteDimensionalProjection, twoPointTimes]

/-- Helper for Corollary 21.25: after reindexing `Iic 2` back to `Fin 3`, the difference of the
last two coordinates is the actual last ordered-history increment. -/
private theorem reindexThreePoint_increment :
    (fun z : (Π _ : Finset.Iic 2, Fin 1 → ℝ) ↦
      ((fun i : Fin 3 ↦ z ((iicEquivFinLocal 2).symm i)) 2) -
        ((fun i : Fin 3 ↦ z ((iicEquivFinLocal 2).symm i)) 1)) =
      (fun z : (Π _ : Finset.Iic 2, Fin 1 → ℝ) ↦
        z ⟨2, Finset.mem_Iic.2 le_rfl⟩ - z ⟨1, Finset.mem_Iic.2 (by decide : 1 ≤ 2)⟩) := by
  -- Proof comment: both descriptions refer to the same two ordered-history coordinates.
  funext z
  simp [iicEquivFinLocal]

/-- Helper for Corollary 21.25: split an ordered successor history into its prefix history and
its final state. -/
private noncomputable def succHistoryEquivLocal (n : ℕ) :
    (Π _ : Finset.Iic (n + 1), Fin 1 → ℝ) ≃ᵐ
      ((Π _ : Finset.Iic n, Fin 1 → ℝ) × (Fin 1 → ℝ)) :=
  (MeasurableEquiv.IicProdIoc (X := fun _ : ℕ ↦ Fin 1 → ℝ) (Nat.le_succ n)).symm.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin 1 → ℝ) n).symm)

/-- Helper for Corollary 21.25: `succHistoryEquivLocal` records the prefix restriction together
with the terminal state. -/
@[simp] private theorem succHistoryEquivLocal_apply (n : ℕ)
    (z : Π _ : Finset.Iic (n + 1), Fin 1 → ℝ) :
    succHistoryEquivLocal n z =
      (Preorder.frestrictLe₂ (π := fun _ : ℕ ↦ Fin 1 → ℝ) (Nat.le_succ n) z,
        z ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) := by
  -- Proof comment: unfolding the measurable equivalence reveals the standard prefix/last split.
  rfl

/-- Helper for Corollary 21.25: the inverse of `succHistoryEquivLocal` glues a prefix history and
one terminal state back into a successor history. -/
@[simp] private theorem succHistoryEquivLocal_symm_apply (n : ℕ)
    (z : (Π _ : Finset.Iic n, Fin 1 → ℝ) × (Fin 1 → ℝ)) :
    (succHistoryEquivLocal n).symm z =
      _root_.IicProdIoc (X := fun _ : ℕ ↦ Fin 1 → ℝ) n (n + 1)
        (z.1, MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin 1 → ℝ) n z.2) := by
  -- Proof comment: the inverse first restores the singleton tail coordinate and then glues it to
  -- the prefix history.
  rfl

/-- Helper for Corollary 21.25: applying `succHistoryEquivLocal` after gluing a prefix history to
its singleton terminal fiber recovers the stored pair. -/
@[simp] private theorem succHistoryEquivLocal_apply_IicProdIoc (n : ℕ)
    (z : (Π _ : Finset.Iic n, Fin 1 → ℝ) × (Π _ : Finset.Ioc n (n + 1), Fin 1 → ℝ)) :
    succHistoryEquivLocal n
        (_root_.IicProdIoc (X := fun _ : ℕ ↦ Fin 1 → ℝ) n (n + 1) z) =
      Prod.map id (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin 1 → ℝ) n).symm z := by
  -- Proof comment: splitting the glued successor history recovers its prefix restriction and
  -- collapses the singleton terminal fiber back to the final state.
  rcases z with ⟨z₁, z₂⟩
  apply Prod.ext
  · ext i x
    have hi : (i : ℕ) ≤ n := Finset.mem_Iic.mp i.2
    simp [succHistoryEquivLocal_apply, _root_.IicProdIoc_def, MeasurableEquiv.piSingleton, hi]
  · ext x
    simp [succHistoryEquivLocal_apply, _root_.IicProdIoc_def, MeasurableEquiv.piSingleton]

/-- Helper for Corollary 21.25: on ordered three-point histories, the last gap factors through
the canonical split into `(prefix, last)`. -/
private theorem threePointOrderedGap_eq_gapAfterSplit :
    (fun z : (Π _ : Finset.Iic 2, Fin 1 → ℝ) ↦
      z ⟨2, Finset.mem_Iic.2 le_rfl⟩ - z ⟨1, Finset.mem_Iic.2 (by decide : 1 ≤ 2)⟩) =
      (fun p : (Π _ : Finset.Iic 1, Fin 1 → ℝ) × (Fin 1 → ℝ) ↦
        p.2 - p.1 ⟨1, Finset.mem_Iic.2 le_rfl⟩) ∘
        succHistoryEquivLocal 1 := by
  -- Proof comment: after splitting a length-two ordered history, the gap `z₂ - z₁` becomes the
  -- terminal state minus the last prefix state.
  funext z x
  simp [Function.comp, succHistoryEquivLocal_apply, Preorder.frestrictLe₂_apply]

/-- Helper for Corollary 21.25: transporting the ordered successor-history law through
`succHistoryEquivLocal` yields the prefix law composed with the last-step kernel. -/
private theorem consistentFamilyFiniteDimensionalKernel_map_succHistoryEquiv_eq_compProd
    {n : ℕ}
    (K : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin 1 → ℝ) (Fin 1 → ℝ))
    (j : Π _ : Finset.Iic (n + 1), NNReal) (hj : StrictMono j) (x : Fin 1 → ℝ) :
    let jPrefix : Π _ : Finset.Iic n, NNReal := fun i ↦
      j ⟨i.1, Finset.mem_Iic.2
        (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩
    let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
    let lastPrefix : (Π _ : Finset.Iic n, Fin 1 → ℝ) → Fin 1 → ℝ := fun z ↦
      z ⟨n, Finset.mem_Iic.2 le_rfl⟩
    let hLastIdx :
        (⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ : Finset.Iic (n + 1)) <
          ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := lastIic_lt_succLast n
    let hLast :
        j ⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ <
          j ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := hj hLastIdx
    let hlastPrefixMeasurable : Measurable lastPrefix := by
      simpa [lastPrefix] using measurable_lastIicCoordinate (n := n)
    (consistentFamilyFiniteDimensionalKernel K j hj x).map (succHistoryEquivLocal n) =
      (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ
        Kernel.comap (K hLast) lastPrefix hlastPrefixMeasurable := by
  let jPrefix : Π _ : Finset.Iic n, NNReal := fun i ↦
    j ⟨i.1, Finset.mem_Iic.2
      (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩
  let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
  let lastPrefix : (Π _ : Finset.Iic n, Fin 1 → ℝ) → Fin 1 → ℝ := fun z ↦
    z ⟨n, Finset.mem_Iic.2 le_rfl⟩
  let hLastIdx :
      (⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ : Finset.Iic (n + 1)) <
        ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := lastIic_lt_succLast n
  let hLast :
      j ⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ <
        j ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := hj hLastIdx
  let hlastPrefixMeasurable : Measurable lastPrefix := by
    simpa [lastPrefix] using measurable_lastIicCoordinate (n := n)
  let κhist :
      (m : ℕ) → Kernel (Π _ : Finset.Iic m, Fin 1 → ℝ) (Fin 1 → ℝ) :=
    fun m ↦
      if hm : m < n + 1 then
        Kernel.comap
          (K (hj (show (⟨m, Finset.mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic (n + 1)) <
            ⟨m + 1, Finset.mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ from Nat.lt_succ_self m)))
          (fun z : Π _ : Finset.Iic m, Fin 1 → ℝ ↦ z ⟨m, Finset.mem_Iic.2 le_rfl⟩)
          (measurable_lastIicCoordinate (n := m))
      else
        Kernel.deterministic
          (fun z : Π _ : Finset.Iic m, Fin 1 → ℝ ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩)
          (measurable_zeroIicCoordinate (n := m))
  let stepKernel : Kernel (Π _ : Finset.Iic n, Fin 1 → ℝ) (Fin 1 → ℝ) :=
    Kernel.comap (K hLast) lastPrefix hlastPrefixMeasurable
  let splitKernel :
      Kernel (Π i : Finset.Iic n, Fin 1 → ℝ)
        ((Π i : Finset.Iic n, Fin 1 → ℝ) × (Fin 1 → ℝ)) :=
    ((Kernel.id :
        Kernel (Π i : Finset.Iic n, Fin 1 → ℝ) (Π i : Finset.Iic n, Fin 1 → ℝ)) ×ₖ
      stepKernel)
  have hstepKernel :
      κhist n = stepKernel := by
    -- Proof comment: at the terminal prefix index, the history-extension kernel is exactly the
    -- last-step translated row read from the last prefix state.
    simp [κhist, stepKernel, lastPrefix]
  have hcompose :
      succHistoryEquivLocal n ∘
          _root_.IicProdIoc (X := fun _ : ℕ ↦ Fin 1 → ℝ) n (n + 1) =
        Prod.map id (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin 1 → ℝ) n).symm := by
    -- Proof comment: `succHistoryEquivLocal` is the standard `Iic` split followed by collapsing
    -- the singleton tail coordinate.
    funext z
    simpa [Function.comp] using succHistoryEquivLocal_apply_IicProdIoc n z
  have hsplitKernel :
      (ProbabilityTheory.Kernel.partialTraj (κ := κhist) n (n + 1)).map
          (succHistoryEquivLocal n) =
        splitKernel := by
    -- Proof comment: after transporting the final-step extension through the split equivalence,
    -- the partial trajectory becomes `(history, last-step row)`.
    rw [ProbabilityTheory.Kernel.partialTraj_succ_self]
    rw [← Kernel.map_comp_right _ measurable_IicProdIoc
      (measurable_id.prodMap
        (MeasurableEquiv.symm (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin 1 → ℝ) n)).measurable),
      hcompose]
    rw [← Kernel.map_prod_map]
    rw [Kernel.map_id]
    rw [hstepKernel]
    rw [← Kernel.map_comp_right _
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin 1 → ℝ) n).measurable
      (MeasurableEquiv.symm
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Fin 1 → ℝ) n)).measurable]
    simpa using Kernel.map_id stepKernel
  have hsucc :
      consistentFamilyFiniteDimensionalKernel K j hj =
        ProbabilityTheory.Kernel.partialTraj (κ := κhist) n (n + 1) ∘ₖ
          consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix := by
    -- Proof comment: the positive-length history law is built from the prefix law followed by one
    -- last transition step.
    rw [consistentFamilyFiniteDimensionalKernel, consistentFamilyFiniteDimensionalKernel,
      consistentFamilyHistoryTraj, consistentFamilyHistoryTraj]
    rw [ProbabilityTheory.Kernel.partialTraj_succ_eq_comp (κ := κhist) (Nat.zero_le n)]
    rfl
  -- Proof comment: combine the one-step split of the history kernel with the canonical split
  -- equivalence.
  calc
    (consistentFamilyFiniteDimensionalKernel K j hj x).map (succHistoryEquivLocal n)
        = (((ProbabilityTheory.Kernel.partialTraj (κ := κhist) n (n + 1)).map
            (succHistoryEquivLocal n)) ∘ₖ
              consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) x := by
              rw [hsucc, Kernel.map_comp]
    _ = (splitKernel ∘ₖ
          consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) x := by
            rw [hsplitKernel]
    _ = (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ stepKernel := by
          simpa [splitKernel, Measure.compProd_eq_comp_prod]

/-- Helper for Corollary 21.25: if the final state is sampled from the translated increment
kernel based on the last prefix value, then subtracting that prefix value recovers the increment
law. -/
private theorem compProd_map_sub_lastPrefix_eq
    {n : ℕ}
    (ν : ProbabilityMeasure (Fin 1 → ℝ))
    (μ : Measure (Π _ : Finset.Iic n, Fin 1 → ℝ))
    [IsProbabilityMeasure μ]
    (lastPrefix : (Π _ : Finset.Iic n, Fin 1 → ℝ) → Fin 1 → ℝ)
    (hlastPrefixMeasurable : Measurable lastPrefix) :
    let stepKernel : Kernel (Π _ : Finset.Iic n, Fin 1 → ℝ) (Fin 1 → ℝ) :=
      Kernel.comap (dirac_convolution_kernel (ν : Measure (Fin 1 → ℝ))) lastPrefix
        hlastPrefixMeasurable
    (μ ⊗ₘ stepKernel).map
        (fun p : (Π _ : Finset.Iic n, Fin 1 → ℝ) × (Fin 1 → ℝ) ↦ p.2 - lastPrefix p.1) =
      (ν : Measure (Fin 1 → ℝ)) := by
  let stepKernel : Kernel (Π _ : Finset.Iic n, Fin 1 → ℝ) (Fin 1 → ℝ) :=
    Kernel.comap (dirac_convolution_kernel (ν : Measure (Fin 1 → ℝ))) lastPrefix
      hlastPrefixMeasurable
  let gapMap :
      ((Π _ : Finset.Iic n, Fin 1 → ℝ) × (Fin 1 → ℝ)) → Fin 1 → ℝ :=
    fun p ↦ p.2 - lastPrefix p.1
  have hgapMapMeasurable : Measurable gapMap := by
    exact measurable_snd.sub (hlastPrefixMeasurable.comp measurable_fst)
  letI : IsSFiniteKernel stepKernel := by
    dsimp [stepKernel]
    infer_instance
  have hkernel :
      ((Kernel.id ×ₖ stepKernel).map gapMap) =
        Kernel.const (Π _ : Finset.Iic n, Fin 1 → ℝ) (ν : Measure (Fin 1 → ℝ)) := by
    ext z A hA
    -- Proof comment: rowwise, the last state is sampled as `lastPrefix z + ξ`; subtracting the
    -- last prefix cancels this translation.
    rw [Kernel.map_apply _ hgapMapMeasurable, Kernel.prod_apply, Kernel.id_apply]
    rw [Measure.dirac_prod, Measure.map_map hgapMapMeasurable measurable_prodMk_left]
    rw [Kernel.comap_apply, dirac_convolution_kernel_apply]
    rw [Measure.dirac_conv]
    have hcancel :
        Measure.map (fun y : Fin 1 → ℝ ↦ y - lastPrefix z)
            (Measure.map (fun y : Fin 1 → ℝ ↦ lastPrefix z + y) (ν : Measure (Fin 1 → ℝ))) =
          (ν : Measure (Fin 1 → ℝ)) := by
      simpa [Function.comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (Measure.map_map
          (μ := (ν : Measure (Fin 1 → ℝ)))
          (f := fun y : Fin 1 → ℝ ↦ lastPrefix z + y)
          (g := fun y : Fin 1 → ℝ ↦ y - lastPrefix z)
          (measurable_id.sub measurable_const)
          (measurable_const.add measurable_id))
    exact congrArg (fun m : Measure (Fin 1 → ℝ) ↦ m A) hcancel
  -- Proof comment: rewrite the composition-product measure as a composed pair kernel and apply
  -- the rowwise cancellation once.
  calc
    (μ ⊗ₘ stepKernel).map gapMap = (((Kernel.id ×ₖ stepKernel).map gapMap) ∘ₘ μ) := by
      rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ hgapMapMeasurable]
    _ = (Kernel.const (Π _ : Finset.Iic n, Fin 1 → ℝ) (ν : Measure (Fin 1 → ℝ))) ∘ₘ μ := by
          rw [hkernel]
    _ = (ν : Measure (Fin 1 → ℝ)) := by
          simpa using
            (Measure.const_comp
              (μ := μ) (ν := (ν : Measure (Fin 1 → ℝ))))

/-- Helper for Corollary 21.25: the canonical three-point grid `(0, s, t)` on `Fin 3`. -/
private def threePointTimes (s t : NNReal) : Fin 3 → NNReal
  | 0 => 0
  | 1 => s
  | 2 => t

/-- Helper for Corollary 21.25: if `0 < s < t`, then `(0, s, t)` is strictly increasing. -/
private theorem threePointTimes_strictMono {s t : NNReal} (hs : 0 < s) (hst : s < t) :
    StrictMono (threePointTimes s t) := by
  -- Proof comment: the only nontrivial comparisons in `Fin 3` are `0 < 1`, `0 < 2`, and
  -- `1 < 2`, giving exactly `0 < s`, `0 < t`, and `s < t`.
  intro i j hij
  fin_cases i <;> fin_cases j
  · have : False := by simpa using hij
    exact this.elim
  · simpa [threePointTimes] using hs
  · simpa [threePointTimes] using lt_trans hs hst
  · have : False := by simpa using hij
    exact this.elim
  · have : False := by simpa using hij
    exact this.elim
  · simpa [threePointTimes] using hst
  · have : False := by simpa using hij
    exact this.elim
  · have : False := by simpa using hij
    exact this.elim
  · have : False := by simpa using hij
    exact this.elim

/-- Helper for Corollary 21.25: if `s ≤ t`, then `(0, s, t)` is monotone. -/
private theorem threePointTimes_monotone {s t : NNReal} (hst : s ≤ t) :
    Monotone (threePointTimes s t) := by
  -- Proof comment: the only nontrivial comparisons in `Fin 3` are `0 ≤ 1`, `0 ≤ 2`, and
  -- `1 ≤ 2`, which reduce to `0 ≤ s`, `0 ≤ t`, and `s ≤ t`.
  intro i j hij
  fin_cases i <;> fin_cases j
  · simp [threePointTimes]
  · simp [threePointTimes]
  · exact le_trans (show (0 : NNReal) ≤ s from bot_le) hst
  · have : False := by simpa using hij
    exact this.elim
  · simp [threePointTimes]
  · exact hst
  · have : False := by simpa using hij
    exact this.elim
  · have : False := by simpa using hij
    exact this.elim
  · simp [threePointTimes]

/-- Helper for Corollary 21.25: the last adjacent difference of the three-point projection is the
increment `ω t - ω s`. -/
private theorem finiteDimensionalProjection_threePoint_increment (s t : NNReal) :
    (fun ω : NNReal → Fin 1 → ℝ ↦
      (finiteDimensionalProjection (threePointTimes s t) ω) 2 -
        (finiteDimensionalProjection (threePointTimes s t) ω) 1) =
      (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - ω s) := by
  -- Proof comment: the projected tuple stores the path values at `0`, `s`, and `t`, so the last
  -- adjacent difference is exactly the interval increment.
  funext ω
  simp [finiteDimensionalProjection, threePointTimes]

/-- Helper for Corollary 21.25: the canonical `Fin 1` path measure starts from the deterministic
zero vector. -/
private theorem transportedFin1PathMeasure_start_hasLaw
    (ν : NNReal → ProbabilityMeasure ℝ)
    [IsContinuousConvolutionSemigroup ν]
    {P : Measure (NNReal → Fin 1 → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦
                dirac_convolution_kernel (transportedFin1Law ν t : Measure (Fin 1 → ℝ)))
              times htimes ∘ₘ Measure.dirac (0 : Fin 1 → ℝ)) :
    HasLaw (Function.eval 0) (Measure.dirac (0 : Fin 1 → ℝ)) P := by
  let times : Fin 1 → NNReal := fun _ ↦ 0
  let e0 : (Fin 1 → ℝ) → Fin 1 → Fin 1 → ℝ := fun y _ ↦ y
  have htimes : StrictMono times := by
    intro i j hij
    fin_cases i
    fin_cases j
    have : False := by simpa using hij
    exact this.elim
  have he0_measurable : Measurable e0 := by
    refine measurable_pi_lambda _ fun _ ↦ ?_
    exact measurable_id
  have hproj : finiteDimensionalProjection times = e0 ∘ Function.eval 0 := by
    -- Proof comment: the one-point finite-dimensional projection only records the time-zero
    -- coordinate, packaged as a constant singleton tuple.
    funext ω
    funext i
    fin_cases i
    simp [finiteDimensionalProjection, times, e0]
  have htuple : P.map (e0 ∘ Function.eval 0) = (Measure.dirac (0 : Fin 1 → ℝ)).map e0 := by
    -- Proof comment: the `n = 0` finite-dimensional marginal is exactly the starting Dirac law.
    calc
      P.map (e0 ∘ Function.eval 0) = P.map (finiteDimensionalProjection times) := by
        simp [hproj]
      _ =
          markovSemigroupFiniteDimKernelLocal
            (fun t ↦
              dirac_convolution_kernel (transportedFin1Law ν t : Measure (Fin 1 → ℝ)))
            times htimes ∘ₘ Measure.dirac (0 : Fin 1 → ℝ) := hP_fdim times rfl htimes
      _ = (Measure.dirac (0 : Fin 1 → ℝ)).map e0 := by
        rw [markovSemigroupFiniteDimKernelLocal]
        rw [← Measure.map_comp _ _ (by
          refine measurable_pi_lambda _ fun _ ↦ ?_
          exact measurable_pi_apply _)]
        change
          Measure.map _ (consistentFamilyFiniteDimensionalMeasure
            (Measure.dirac (0 : Fin 1 → ℝ))
            (fun {s t : NNReal} _ ↦
              dirac_convolution_kernel (transportedFin1Law ν (t - s) : Measure (Fin 1 → ℝ)))
            _ _) = _
        rw [consistentFamilyFiniteDimensionalMeasure_zero]
        rw [Measure.map_map (by
          refine measurable_pi_lambda _ fun _ ↦ ?_
          exact measurable_pi_apply _)
          (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ Fin 1 → ℝ)).symm.measurable]
        rfl
  refine ⟨(measurable_pi_apply 0).aemeasurable, ?_⟩
  -- Proof comment: postcompose the singleton-tuple law with `Function.eval 0`, which is a left
  -- inverse to the singleton embedding `e0`.
  calc
    P.map (Function.eval 0) =
        P.map ((Function.eval 0) ∘ (e0 ∘ Function.eval 0)) := by
          rfl
    _ = (P.map (e0 ∘ Function.eval 0)).map (Function.eval 0) := by
          rw [Measure.map_map (measurable_pi_apply 0)
            (he0_measurable.comp (measurable_pi_apply 0))]
    _ = ((Measure.dirac (0 : Fin 1 → ℝ)).map e0).map (Function.eval 0) := by
          rw [htuple]
    _ = (Measure.dirac (0 : Fin 1 → ℝ)).map ((Function.eval 0) ∘ e0) := by
          rw [Measure.map_map (measurable_pi_apply 0) he0_measurable]
    _ = Measure.dirac (0 : Fin 1 → ℝ) := by
          simp [e0]

/-- Helper for Corollary 21.25: a zero-length increment of the canonical `Fin 1` path process is
the constant zero random variable. -/
private theorem selfIncrement_hasLaw_diracZero
    {P : Measure (NNReal → Fin 1 → ℝ)} [IsProbabilityMeasure P] (t : NNReal) :
    HasLaw
      (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - ω t)
      (Measure.dirac (0 : Fin 1 → ℝ))
      P := by
  -- Proof comment: the increment is pointwise `0`, so its pushforward law is the Dirac mass at
  -- the zero vector.
  refine ⟨((measurable_pi_apply t).sub (measurable_pi_apply t)).aemeasurable, ?_⟩
  ext A hA
  simp [hA]

/-- Helper for Corollary 21.25: under the two-point finite-dimensional kernel `(0, t)`, the last
coordinate has the translated increment law `x ↦ δ_x ∗ ν_t`. -/
private theorem markovSemigroupFiniteDimKernel_twoPoint_last
    (ν : NNReal → ProbabilityMeasure ℝ) {t : NNReal} (ht : 0 < t) :
    (markovSemigroupFiniteDimKernelLocal
        (fun s ↦ dirac_convolution_kernel (transportedFin1Law ν s : Measure (Fin 1 → ℝ)))
        (twoPointTimes t) (twoPointTimes_strictMono ht)).map (Function.eval 1) =
      dirac_convolution_kernel (transportedFin1Law ν t : Measure (Fin 1 → ℝ)) := by
  let K : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin 1 → ℝ) (Fin 1 → ℝ) :=
    fun {s t} _ ↦ dirac_convolution_kernel (transportedFin1Law ν (t - s) : Measure (Fin 1 → ℝ))
  let j : Π _ : Finset.Iic 1, NNReal := orderedTimeChainLocal (twoPointTimes t)
  let hj : StrictMono j := orderedTimeChainLocal_strictMono (twoPointTimes_strictMono ht)
  let last : (Π _ : Finset.Iic 1, Fin 1 → ℝ) → Fin 1 → ℝ :=
    fun z ↦ z ⟨1, Finset.mem_Iic.2 le_rfl⟩
  have h01idx :
      (⟨0, Finset.mem_Iic.2 (Nat.zero_le 1)⟩ : Finset.Iic 1) <
        ⟨1, Finset.mem_Iic.2 le_rfl⟩ := by
    decide
  have h01 :
      j ⟨0, Finset.mem_Iic.2 (Nat.zero_le 1)⟩ <
        j ⟨1, Finset.mem_Iic.2 le_rfl⟩ := hj h01idx
  have hkernel :
      (consistentFamilyFiniteDimensionalKernel K j hj).map last =
        dirac_convolution_kernel (transportedFin1Law ν t : Measure (Fin 1 → ℝ)) := by
    -- Proof comment: on a two-point ordered history there is exactly one translated step, so the
    -- last coordinate is sampled from the one-step translated kernel.
    rw [consistentFamilyFiniteDimensionalKernel, Kernel.map_comp]
    have htraj :
        (ProbabilityTheory.Kernel.partialTraj
            (κ := ?κ)
            0 1).map last =
          Kernel.comap (K h01)
            (fun z : Π _ : Finset.Iic 0, Fin 1 → ℝ ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le 0)⟩)
            (measurable_zeroIicCoordinate (n := 0)) := by
      simpa [last] using
        (ProbabilityTheory.Kernel.map_partialTraj_succ_self (κ := ?κ) 0)
    rw [htraj]
    have hinitialMeasurable :
        Measurable (fun x : Fin 1 → ℝ ↦ fun _ : Finset.Iic 0 ↦ x) := by
      fun_prop
    have hlastMeasurable : Measurable last := by
      fun_prop
    rw [Kernel.comp_deterministic_eq_comap]
    rw [← Kernel.comap_comp_right
      (κ := K h01) (hf := hinitialMeasurable) (hg := hlastMeasurable)]
    -- Proof comment: on a singleton history, the last coordinate is the unique history value, so
    -- the comap collapses to the identity on the one-step kernel.
    simpa [K, j, orderedTimeChainLocal, twoPointTimes, iicEquivFinLocal, tsub_zero] using
      (Kernel.comap_id (K h01))
  -- Proof comment: after reindexing the ordered two-point history back to `Fin 2`, the last
  -- coordinate is still the last state.
  rw [markovSemigroupFiniteDimKernelLocal]
  rw [← Kernel.map_comp_right
    (κ := consistentFamilyFiniteDimensionalKernel K j hj)
    (f := fun z : Π _ : Finset.Iic 1, Fin 1 → ℝ ↦
      fun i : Fin 2 ↦ z ((iicEquivFinLocal 1).symm i))
    (g := Function.eval 1)
    (hf := by
      refine measurable_pi_lambda _ fun i ↦ ?_
      exact measurable_pi_apply ((iicEquivFinLocal 1).symm i))
    (hg := measurable_pi_apply 1)]
  rw [reindexTwoPoint_last]
  exact hkernel

/-- Helper for Corollary 21.25: every one-time canonical marginal has the translated convolution
law `δ₀ ∗ ν_t`. -/
private theorem transportedFin1PathMeasure_coordinateHasLaw
    (ν : NNReal → ProbabilityMeasure ℝ)
    [IsContinuousConvolutionSemigroup ν]
    {P : Measure (NNReal → Fin 1 → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦
                dirac_convolution_kernel (transportedFin1Law ν t : Measure (Fin 1 → ℝ)))
              times htimes ∘ₘ Measure.dirac (0 : Fin 1 → ℝ))
    (t : NNReal) :
    HasLaw (Function.eval t)
      (Measure.dirac (0 : Fin 1 → ℝ) ∗ (transportedFin1Law ν t : Measure (Fin 1 → ℝ)))
      P := by
  by_cases ht : t = 0
  · have hzero :
        Measure.dirac (0 : Fin 1 → ℝ) ∗ (transportedFin1Law ν 0 : Measure (Fin 1 → ℝ)) =
          Measure.dirac (0 : Fin 1 → ℝ) := by
      have hν : IsConvolutionSemigroupWithZero (transportedFin1Law ν) :=
        transportedFin1ConvolutionSemigroupWithZero ν
      rw [hν.zero_eq, ProbabilityMeasure.one_eq_diracProba]
      exact Measure.conv_dirac_zero (Measure.dirac (0 : Fin 1 → ℝ))
    -- Proof comment: at time zero the coordinate law is the deterministic start law.
    rw [ht]
    rw [hzero]
    exact transportedFin1PathMeasure_start_hasLaw (ν := ν) hP_fdim
  · have htpos : 0 < t := pos_iff_ne_zero.mpr ht
    have hfdim := hP_fdim (twoPointTimes t) rfl (twoPointTimes_strictMono htpos)
    have hlastLaw :
        HasLaw
          (Function.eval 1)
          (((markovSemigroupFiniteDimKernelLocal
              (fun s ↦ dirac_convolution_kernel (transportedFin1Law ν s : Measure (Fin 1 → ℝ)))
              (twoPointTimes t) (twoPointTimes_strictMono htpos)).map (Function.eval 1)) ∘ₘ
            Measure.dirac (0 : Fin 1 → ℝ))
          (P.map (finiteDimensionalProjection (twoPointTimes t))) := by
      refine ⟨(measurable_pi_apply 1).aemeasurable, ?_⟩
      -- Proof comment: push the two-point marginal law forward to its last coordinate.
      calc
        (P.map (finiteDimensionalProjection (twoPointTimes t))).map (Function.eval 1)
            = ((markovSemigroupFiniteDimKernelLocal
                (fun s ↦ dirac_convolution_kernel (transportedFin1Law ν s : Measure (Fin 1 → ℝ)))
                (twoPointTimes t) (twoPointTimes_strictMono htpos) ∘ₘ
                  Measure.dirac (0 : Fin 1 → ℝ))).map (Function.eval 1) := by
                rw [hfdim]
        _ =
            ((markovSemigroupFiniteDimKernelLocal
                (fun s ↦ dirac_convolution_kernel (transportedFin1Law ν s : Measure (Fin 1 → ℝ)))
                (twoPointTimes t) (twoPointTimes_strictMono htpos)).map
              (Function.eval 1)) ∘ₘ Measure.dirac (0 : Fin 1 → ℝ) := by
                rw [Measure.map_comp _ _ (measurable_pi_apply 1)]
    have hlastMeasure :
        (((markovSemigroupFiniteDimKernelLocal
            (fun s ↦ dirac_convolution_kernel (transportedFin1Law ν s : Measure (Fin 1 → ℝ)))
            (twoPointTimes t) (twoPointTimes_strictMono htpos)).map (Function.eval 1)) ∘ₘ
          Measure.dirac (0 : Fin 1 → ℝ)) =
          Measure.dirac (0 : Fin 1 → ℝ) ∗ (transportedFin1Law ν t : Measure (Fin 1 → ℝ)) := by
      -- Proof comment: evaluating the two-point last-coordinate kernel at the deterministic
      -- starting state yields the translated one-step increment law.
      rw [Measure.dirac_bind (Kernel.measurable _) (0 : Fin 1 → ℝ)]
      rw [markovSemigroupFiniteDimKernel_twoPoint_last (ν := ν) htpos]
      simp [dirac_convolution_kernel_apply]
    have htupleLaw :
        HasLaw
          (Function.eval 1)
          (Measure.dirac (0 : Fin 1 → ℝ) ∗ (transportedFin1Law ν t : Measure (Fin 1 → ℝ)))
          (P.map (finiteDimensionalProjection (twoPointTimes t))) := by
      rw [hlastMeasure] at hlastLaw
      exact hlastLaw
    have hprojLaw :
        HasLaw
          ((Function.eval 1) ∘ finiteDimensionalProjection (twoPointTimes t))
          (Measure.dirac (0 : Fin 1 → ℝ) ∗ (transportedFin1Law ν t : Measure (Fin 1 → ℝ)))
          P :=
      HasLaw.comp htupleLaw
        ⟨(measurable_finiteDimensionalProjection (twoPointTimes t)).aemeasurable, rfl⟩
    -- Proof comment: identify the last coordinate of the two-point projection with `ω ↦ ω t`.
    simpa [finiteDimensionalProjection_twoPoint_last] using hprojLaw

/-- Helper for Corollary 21.25: the anchored increment `[0, t]` under the canonical path law has
law `transportedFin1Law ν t`. -/
private theorem transportedFin1PathMeasure_anchoredIncrementHasLaw
    (ν : NNReal → ProbabilityMeasure ℝ)
    [IsContinuousConvolutionSemigroup ν]
    {P : Measure (NNReal → Fin 1 → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦
                dirac_convolution_kernel (transportedFin1Law ν t : Measure (Fin 1 → ℝ)))
              times htimes ∘ₘ Measure.dirac (0 : Fin 1 → ℝ))
    (t : NNReal) :
    HasLaw
      (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - ω 0)
      (transportedFin1Law ν t : Measure (Fin 1 → ℝ))
      P := by
  letI : IsProbabilityMeasure P :=
    (transportedFin1PathMeasure_start_hasLaw (ν := ν) hP_fdim).isProbabilityMeasure
  by_cases ht : t = 0
  · have hν : IsConvolutionSemigroupWithZero (transportedFin1Law ν) :=
      transportedFin1ConvolutionSemigroupWithZero ν
    -- Proof comment: the anchored increment over `[0, 0]` is identically zero.
    simpa [ht, hν.zero_eq, ProbabilityMeasure.one_eq_diracProba] using
      (selfIncrement_hasLaw_diracZero (P := P) 0)
  · have hcoord := transportedFin1PathMeasure_coordinateHasLaw (ν := ν) hP_fdim t
    have hstart := transportedFin1PathMeasure_start_hasLaw (ν := ν) hP_fdim
    have hzero_ae : ∀ᵐ ω ∂P, ω 0 = 0 := by
      exact (hstart.ae_iff (p := fun y : Fin 1 → ℝ ↦ y = 0)
        (measurable_id.eq measurable_const)).2 (by simp)
    have htranslate :
        HasLaw
          (fun y : Fin 1 → ℝ ↦ y - 0)
          (transportedFin1Law ν t : Measure (Fin 1 → ℝ))
          (Measure.dirac (0 : Fin 1 → ℝ) ∗ (transportedFin1Law ν t : Measure (Fin 1 → ℝ))) := by
      refine ⟨(measurable_id.sub measurable_const).aemeasurable, ?_⟩
      -- Proof comment: `δ₀ ∗ ν_t` is translation by zero, so subtracting zero recovers `ν_t`.
      rw [Measure.dirac_conv]
      have hcancel :
          Measure.map (fun y : Fin 1 → ℝ ↦ y - (0 : Fin 1 → ℝ))
              (Measure.map (fun y : Fin 1 → ℝ ↦ (0 : Fin 1 → ℝ) + y)
                (transportedFin1Law ν t : Measure (Fin 1 → ℝ))) =
            (transportedFin1Law ν t : Measure (Fin 1 → ℝ)) := by
        rw [Measure.map_map
          (μ := (transportedFin1Law ν t : Measure (Fin 1 → ℝ)))
          (f := fun y : Fin 1 → ℝ ↦ (0 : Fin 1 → ℝ) + y)
          (g := fun y : Fin 1 → ℝ ↦ y - (0 : Fin 1 → ℝ))
          (measurable_id.sub measurable_const)
          (measurable_const.add measurable_id)]
        simpa [Function.comp, sub_eq_add_neg, add_assoc]
      simpa using hcancel
    have hshifted :
        HasLaw
          (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - 0)
          (transportedFin1Law ν t : Measure (Fin 1 → ℝ))
          P :=
      by simpa [Function.comp] using HasLaw.comp htranslate hcoord
    have hcongr :
        (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - ω 0) =ᵐ[P]
          (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - 0) := by
      -- Proof comment: the time-zero coordinate is almost surely the deterministic zero vector.
      filter_upwards [hzero_ae] with ω hω
      simp [hω]
    exact hshifted.congr hcongr

/-- Helper for Corollary 21.25: for `0 < s < t`, the canonical increment over `[s, t]` has law
`transportedFin1Law ν (t - s)`. -/
private theorem transportedFin1IntervalIncrementHasLawOfLt
    (ν : NNReal → ProbabilityMeasure ℝ)
    [IsContinuousConvolutionSemigroup ν]
    {P : Measure (NNReal → Fin 1 → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦
                dirac_convolution_kernel (transportedFin1Law ν t : Measure (Fin 1 → ℝ)))
              times htimes ∘ₘ Measure.dirac (0 : Fin 1 → ℝ))
    {s t : NNReal} (hs : 0 < s) (hst : s < t) :
    HasLaw
      (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - ω s)
      (transportedFin1Law ν (t - s) : Measure (Fin 1 → ℝ))
      P := by
  let times : Fin 3 → NNReal := threePointTimes s t
  let htimes : StrictMono times := threePointTimes_strictMono hs hst
  let K : ∀ ⦃u v : NNReal⦄, u < v → Kernel (Fin 1 → ℝ) (Fin 1 → ℝ) :=
    fun {u v} _ ↦ dirac_convolution_kernel (transportedFin1Law ν (v - u) : Measure (Fin 1 → ℝ))
  let j : Π _ : Finset.Iic 2, NNReal := orderedTimeChainLocal times
  let hj : StrictMono j := orderedTimeChainLocal_strictMono htimes
  let jPrefix : Π _ : Finset.Iic 1, NNReal := fun i ↦
    j ⟨i.1, Finset.mem_Iic.2
      (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ 1))⟩
  let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
  let lastPrefix : (Π _ : Finset.Iic 1, Fin 1 → ℝ) → Fin 1 → ℝ := fun z ↦
    z ⟨1, Finset.mem_Iic.2 le_rfl⟩
  let hLastIdx :
      (⟨1, Finset.mem_Iic.2 (Nat.le_succ 1)⟩ : Finset.Iic 2) <
        ⟨2, Finset.mem_Iic.2 le_rfl⟩ := by
          decide
  let hLast :
      j ⟨1, Finset.mem_Iic.2 (Nat.le_succ 1)⟩ <
        j ⟨2, Finset.mem_Iic.2 le_rfl⟩ := hj hLastIdx
  let gap : (Fin 3 → Fin 1 → ℝ) → Fin 1 → ℝ := fun z ↦ z 2 - z 1
  let orderedGap : (Π _ : Finset.Iic 2, Fin 1 → ℝ) → Fin 1 → ℝ := fun z ↦
    z ⟨2, Finset.mem_Iic.2 le_rfl⟩ - z ⟨1, Finset.mem_Iic.2 (by decide : 1 ≤ 2)⟩
  let splitGap :
      ((Π _ : Finset.Iic 1, Fin 1 → ℝ) × (Fin 1 → ℝ)) → Fin 1 → ℝ := fun p ↦
    p.2 - p.1 ⟨1, Finset.mem_Iic.2 le_rfl⟩
  have hfdim := hP_fdim times rfl htimes
  have hsplitGapMeasurable : Measurable splitGap := by
    exact measurable_snd.sub ((measurable_lastIicCoordinate (n := 1)).comp measurable_fst)
  have hgapMeasure :
      ((markovSemigroupFiniteDimKernelLocal
          (fun u ↦ dirac_convolution_kernel (transportedFin1Law ν u : Measure (Fin 1 → ℝ)))
          times htimes).map gap) ∘ₘ Measure.dirac (0 : Fin 1 → ℝ) =
        (transportedFin1Law ν (t - s) : Measure (Fin 1 → ℝ)) := by
    rw [Measure.dirac_bind (Kernel.measurable _) (0 : Fin 1 → ℝ)]
    rw [markovSemigroupFiniteDimKernelLocal]
    rw [← Kernel.map_comp_right
      (κ := consistentFamilyFiniteDimensionalKernel K j hj)
      (f := fun z : Π _ : Finset.Iic 2, Fin 1 → ℝ ↦
        fun i : Fin 3 ↦ z ((iicEquivFinLocal 2).symm i))
      (g := gap)
      (hf := by
        refine measurable_pi_lambda _ fun i ↦ ?_
        exact measurable_pi_apply ((iicEquivFinLocal 2).symm i))
      (hg := (measurable_pi_apply 2).sub (measurable_pi_apply 1))]
    rw [reindexThreePoint_increment]
    calc
      (consistentFamilyFiniteDimensionalKernel K j hj (0 : Fin 1 → ℝ)).map orderedGap
          = (consistentFamilyFiniteDimensionalKernel K j hj (0 : Fin 1 → ℝ)).map
              (splitGap ∘ succHistoryEquivLocal 1) := by
                congr 1
                exact threePointOrderedGap_eq_gapAfterSplit.symm
      _ = ((consistentFamilyFiniteDimensionalKernel K j hj (0 : Fin 1 → ℝ)).map
            (succHistoryEquivLocal 1)).map splitGap := by
              rw [← Measure.map_map hsplitGapMeasurable
                (succHistoryEquivLocal 1).measurable]
      _ =
          ((consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix (0 : Fin 1 → ℝ)) ⊗ₘ
            Kernel.comap (K hLast) lastPrefix
              (measurable_lastIicCoordinate (n := 1))).map splitGap := by
              simpa [jPrefix, hjPrefix, lastPrefix, hLast] using
                (consistentFamilyFiniteDimensionalKernel_map_succHistoryEquiv_eq_compProd
                  (K := K) (j := j) (hj := hj) (x := (0 : Fin 1 → ℝ)))
      _ = (transportedFin1Law ν (t - s) : Measure (Fin 1 → ℝ)) := by
            simpa [K, j, orderedTimeChainLocal, times, threePointTimes, iicEquivFinLocal,
              lastPrefix] using
              (compProd_map_sub_lastPrefix_eq
                (ν := transportedFin1Law ν (t - s))
                (μ := consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix (0 : Fin 1 → ℝ))
                (lastPrefix := lastPrefix)
                (hlastPrefixMeasurable := by
                  simpa [lastPrefix] using measurable_lastIicCoordinate (n := 1)))
  have htupleLaw :
      HasLaw
        gap
        (transportedFin1Law ν (t - s) : Measure (Fin 1 → ℝ))
        (P.map (finiteDimensionalProjection times)) := by
    refine ⟨((measurable_pi_apply 2).sub (measurable_pi_apply 1)).aemeasurable, ?_⟩
    calc
      (P.map (finiteDimensionalProjection times)).map gap
          = (((markovSemigroupFiniteDimKernelLocal
                (fun u ↦ dirac_convolution_kernel (transportedFin1Law ν u : Measure (Fin 1 → ℝ)))
                times htimes).map gap) ∘ₘ Measure.dirac (0 : Fin 1 → ℝ)) := by
                rw [hfdim, Measure.map_comp _ _ ((measurable_pi_apply 2).sub (measurable_pi_apply 1))]
      _ = (transportedFin1Law ν (t - s) : Measure (Fin 1 → ℝ)) := hgapMeasure
  have hprojLaw :
      HasLaw
        (gap ∘ finiteDimensionalProjection times)
        (transportedFin1Law ν (t - s) : Measure (Fin 1 → ℝ))
        P :=
    HasLaw.comp htupleLaw
      ⟨(measurable_finiteDimensionalProjection times).aemeasurable, rfl⟩
  -- Proof comment: identify the gap read from the three-point tuple with the path increment
  -- `ω t - ω s`.
  simpa [gap, times, finiteDimensionalProjection_threePoint_increment] using hprojLaw

/-- Helper for Corollary 21.25: convert the canonical finite-dimensional marginal specification
into the one-interval increment law on `NNReal → Fin 1 → ℝ`. -/
private theorem transportedFin1CanonicalIncrementHasLaw
    (ν : NNReal → ProbabilityMeasure ℝ)
    [IsContinuousConvolutionSemigroup ν]
    {P : Measure (NNReal → Fin 1 → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦
                dirac_convolution_kernel (transportedFin1Law ν t : Measure (Fin 1 → ℝ)))
              times htimes ∘ₘ Measure.dirac (0 : Fin 1 → ℝ))
    {s t : NNReal} (hst : s ≤ t) :
    HasLaw
      (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - ω s)
      (transportedFin1Law ν (t - s) : Measure (Fin 1 → ℝ))
      P := by
  letI : IsProbabilityMeasure P :=
    (transportedFin1PathMeasure_start_hasLaw (ν := ν) hP_fdim).isProbabilityMeasure
  let hν : IsConvolutionSemigroupWithZero (transportedFin1Law ν) :=
    transportedFin1ConvolutionSemigroupWithZero ν
  rcases lt_or_eq_of_le hst with hst' | rfl
  · -- Route correction: the zero-length case is now closed directly; the remaining positive-length
    -- interval case is split into the anchored branch `s = 0` and the genuine interior branch
    -- `0 < s < t`, both handled by the dedicated two-point/three-point helpers above.
    by_cases hs : s = 0
    · subst hs
      simpa using transportedFin1PathMeasure_anchoredIncrementHasLaw (ν := ν) hP_fdim t
    · exact transportedFin1IntervalIncrementHasLawOfLt (ν := ν) hP_fdim
        (pos_iff_ne_zero.mpr hs) hst'
  · -- Proof comment: a zero-length increment is identically `0`, so its law is the time-zero
    -- Dirac mass of the transported semigroup.
    simpa [hν.zero_eq, ProbabilityMeasure.one_eq_diracProba] using
      (selfIncrement_hasLaw_diracZero (P := P) s)

/-- Helper for Corollary 21.25: once every interval increment has law `transportedFin1Law ν`,
the canonical path law has stationary increment laws. -/
private theorem transportedFin1CanonicalPathMeasure_hasStationaryIncrementLaws
    (ν : NNReal → ProbabilityMeasure ℝ)
    {P : Measure (NNReal → Fin 1 → ℝ)}
    (hInc :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        HasLaw
          (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - ω s)
          (transportedFin1Law ν (t - s) : Measure (Fin 1 → ℝ))
          P) :
    HasStationaryIncrementLaws Function.eval P := by
  intro r s t
  have hleft_le : t + r ≤ (s + t) + r := by
    have hbase : t ≤ t + s := le_add_of_nonneg_right (show 0 ≤ s from bot_le)
    simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hbase r
  have hright_le : r ≤ s + r := by
    have hbase : r ≤ r + s := le_add_of_nonneg_right (show 0 ≤ s from bot_le)
    simpa [add_assoc, add_left_comm, add_comm] using hbase
  have hleftRaw :
      HasLaw
        (fun ω : NNReal → Fin 1 → ℝ ↦ ω ((s + t) + r) - ω (t + r))
        (transportedFin1Law ν (((s + t) + r) - (t + r)) : Measure (Fin 1 → ℝ))
        P := by
    -- Proof comment: the shifted interval `[(t + r), (s + t) + r]` has lag `s`.
    simpa [add_assoc, add_left_comm, add_comm] using
      (hInc (s := t + r) (t := (s + t) + r) hleft_le)
  have hrightRaw :
      HasLaw
        (fun ω : NNReal → Fin 1 → ℝ ↦ ω (s + r) - ω r)
        (transportedFin1Law ν ((s + r) - r) : Measure (Fin 1 → ℝ))
        P := by
    -- Proof comment: the translated anchored interval `[r, s + r]` has the same lag `s`.
    simpa [add_assoc, add_left_comm, add_comm] using
      (hInc (s := r) (t := s + r) hright_le)
  have hleftGap : ((s + t) + r) - (t + r) = s := by
    rw [add_assoc, add_tsub_cancel_right]
  have hrightGap : (s + r) - r = s := by
    rw [add_tsub_cancel_right]
  have hleft :
      HasLaw
        (fun ω : NNReal → Fin 1 → ℝ ↦ ω ((s + t) + r) - ω (t + r))
        (transportedFin1Law ν s : Measure (Fin 1 → ℝ))
        P := by
    rwa [hleftGap] at hleftRaw
  have hright :
      HasLaw
        (fun ω : NNReal → Fin 1 → ℝ ↦ ω (s + r) - ω r)
        (transportedFin1Law ν s : Measure (Fin 1 → ℝ))
        P := by
    rwa [hrightGap] at hrightRaw
  exact hleft.identDistrib hright

/-- Helper for Corollary 21.25: the deterministic finite-grid increment vector attached to a time
tuple `times`. -/
private def incrementVector {n : ℕ} (times : Fin (n + 1) → NNReal) :
    (NNReal → Fin 1 → ℝ) → Fin n → Fin 1 → ℝ :=
  fun ω i ↦ ω (times i.succ) - ω (times i.castSucc)

/-- Helper for Corollary 21.25: the finite-grid increment vector is measurable. -/
private theorem incrementVector_measurable {n : ℕ}
    (times : Fin (n + 1) → NNReal) :
    Measurable (incrementVector times) := by
  -- Proof comment: each coordinate is a measurable difference of two path evaluations.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact (measurable_pi_apply _).sub (measurable_pi_apply _)

/-- Helper for Corollary 21.25: the adjacent-difference map on a finite coordinate tuple. -/
private def tupleIncrementVector {n : ℕ} :
    (Fin (n + 1) → Fin 1 → ℝ) → Fin n → Fin 1 → ℝ :=
  fun z i ↦ z i.succ - z i.castSucc

/-- Helper for Corollary 21.25: the adjacent-difference map on finite tuples is measurable. -/
private theorem measurable_tupleIncrementVector {n : ℕ} :
    Measurable (tupleIncrementVector (n := n)) := by
  -- Proof comment: each output coordinate is the difference of two measurable tuple coordinates.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [tupleIncrementVector] using
    (measurable_pi_apply i.succ).sub (measurable_pi_apply i.castSucc)

/-- Helper for Corollary 21.25: taking adjacent differences after the finite-dimensional
projection recovers the path-space increment vector. -/
private theorem tupleIncrementVector_comp_finiteDimensionalProjection {n : ℕ}
    (times : Fin (n + 1) → NNReal) :
    tupleIncrementVector (n := n) ∘ finiteDimensionalProjection times =
      incrementVector times := by
  -- Proof comment: both sides read the same adjacent coordinate differences from the projected
  -- path tuple.
  funext ω
  ext i
  simp [tupleIncrementVector, incrementVector, finiteDimensionalProjection]

/-- Helper for Corollary 21.25: reindex an ordered history by `Fin` and record its adjacent
increments. -/
private def orderedHistoryIncrementVector {n : ℕ} :
    (Π _ : Finset.Iic n, Fin 1 → ℝ) → Fin n → Fin 1 → ℝ :=
  fun z i ↦ z ((iicEquivFinLocal n).symm i.succ) - z ((iicEquivFinLocal n).symm i.castSucc)

/-- Helper for Corollary 21.25: the ordered-history increment vector is measurable. -/
private theorem measurable_orderedHistoryIncrementVector {n : ℕ} :
    Measurable (orderedHistoryIncrementVector (n := n)) := by
  -- Proof comment: after the canonical `Iic`-to-`Fin` reindexing, each coordinate is a
  -- measurable adjacent difference.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [orderedHistoryIncrementVector] using
    (measurable_pi_apply ((iicEquivFinLocal n).symm i.succ)).sub
      (measurable_pi_apply ((iicEquivFinLocal n).symm i.castSucc))

/-- Helper for Corollary 21.25: after splitting off the last coordinate from a finite tuple, the
second component is exactly the `Fin.castSucc` prefix. -/
private theorem piFinSuccAboveLast_snd_eq_castSucc {n : ℕ} :
    Prod.snd ∘ MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) ↦ Fin 1 → ℝ) (Fin.last n) =
      fun z : Fin (n + 1) → Fin 1 → ℝ ↦ fun i : Fin n ↦ z i.castSucc := by
  funext z i
  -- Proof comment: for `Fin.last`, `succAbove` is definitionally `Fin.castSucc`.
  simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.init_def]

/-- Helper for Corollary 21.25: `piFinSuccAbove` splits the last coordinate off a finite-grid
increment vector into the terminal increment and the prefix increment vector. -/
private theorem incrementVector_piFinSuccAbove_last {n : ℕ}
    (times : Fin (n + 2) → NNReal) :
    (fun ω ↦
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin 1 → ℝ) (Fin.last n)
        (incrementVector times ω)) =
      fun ω ↦
        (ω (times (Fin.last n).succ) - ω (times (Fin.last n).castSucc),
          incrementVector (fun i : Fin (n + 1) ↦ times i.castSucc) ω) := by
  -- Proof comment: `piFinSuccAbove` isolates the terminal increment, and the remaining
  -- coordinates are precisely the increment vector of the dropped-last prefix grid.
  funext ω
  have htail :
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin 1 → ℝ) (Fin.last n))
        (incrementVector times ω)).2 =
        fun i : Fin n ↦ incrementVector times ω i.castSucc := by
    ext i x
    simpa [MeasurableEquiv.piFinSuccAbove_apply, Fin.init_def, Fin.succAbove_last]
  apply Prod.ext
  · ext x
    simp [incrementVector, MeasurableEquiv.piFinSuccAbove_apply]
  · ext i x
    rw [htail]
    change ω (times (i.castSucc).succ) x - ω (times (i.castSucc).castSucc) x =
      ω (times i.succ.castSucc) x - ω (times i.castSucc.castSucc) x
    rw [Fin.succ_castSucc]

/-- Helper for Corollary 21.25: splitting the increment product law at the last coordinate gives
the terminal marginal together with the prefix product law. -/
private theorem incrementLawPi_map_piFinSuccAbove_last {n : ℕ}
    (ν : NNReal → ProbabilityMeasure ℝ)
    (times : Fin (n + 2) → NNReal) :
    (Measure.pi (fun i : Fin (n + 1) ↦
      (transportedFin1Law ν (times i.succ - times i.castSucc) : Measure (Fin 1 → ℝ)))).map
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin 1 → ℝ) (Fin.last n)) =
    (transportedFin1Law ν (times (Fin.last n).succ - times (Fin.last n).castSucc) :
        Measure (Fin 1 → ℝ)).prod
      (Measure.pi (fun i : Fin n ↦
        (transportedFin1Law ν
          ((fun j : Fin (n + 1) ↦ times j.castSucc) i.succ -
            (fun j : Fin (n + 1) ↦ times j.castSucc) i.castSucc) :
            Measure (Fin 1 → ℝ)))) := by
  let μ : Fin (n + 1) → Measure (Fin 1 → ℝ) := fun i ↦
    (transportedFin1Law ν (times i.succ - times i.castSucc) : Measure (Fin 1 → ℝ))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin 1 → ℝ) (Fin.last n)
  have hMapEq :
      (Measure.pi μ).map e =
        (μ (Fin.last n)).prod (Measure.pi fun i : Fin n ↦ μ ((Fin.last n).succAbove i)) :=
    (measurePreserving_piFinSuccAbove μ (Fin.last n)).map_eq
  have hprefixFamily :
      (fun i : Fin n ↦ μ ((Fin.last n).succAbove i)) =
        (fun i : Fin n ↦
          (transportedFin1Law ν
            ((fun j : Fin (n + 1) ↦ times j.castSucc) i.succ -
              (fun j : Fin (n + 1) ↦ times j.castSucc) i.castSucc) :
            Measure (Fin 1 → ℝ))) := by
    funext i
    simp [μ, Fin.succAbove_last]
  -- Proof comment: `measurePreserving_piFinSuccAbove` already isolates the last factor; after
  -- `Fin.last`, the surviving coordinates are exactly the `castSucc` prefix gaps.
  rw [hMapEq, hprefixFamily]

/-- Helper for Corollary 21.25: after reindexing an ordered successor history to `Fin`, splitting
off the last increment is the same as recording the final gap together with the prefix increment
vector. -/
private theorem orderedHistoryIncrementVector_piFinSuccAbove_last {n : ℕ} :
    (fun z : Π _ : Finset.Iic (n + 1), Fin 1 → ℝ ↦
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin 1 → ℝ) (Fin.last n)
        (orderedHistoryIncrementVector (n := n + 1) z)) =
      fun z ↦
        let p := succHistoryEquivLocal n z
        (p.2 - p.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩,
          orderedHistoryIncrementVector (n := n) p.1) := by
  funext z
  apply Prod.ext
  · ext x
    simp [orderedHistoryIncrementVector, MeasurableEquiv.piFinSuccAbove_apply,
      succHistoryEquivLocal_apply, iicEquivFinLocal]
  · ext i x
    simp [orderedHistoryIncrementVector, MeasurableEquiv.piFinSuccAbove_apply,
      succHistoryEquivLocal_apply, Fin.init_def, Fin.succAbove_last, iicEquivFinLocal]

/-- Helper for Corollary 21.25: after separating the final translated step into `(history, gap)`,
pushing the history through a measurable prefix statistic yields the product of the centered gap
law and the pushed-forward prefix law. -/
private theorem compProd_map_gapAndPrefix_eq_prod
    {n : ℕ} {Y : Type*} [MeasurableSpace Y]
    (νGap : ProbabilityMeasure (Fin 1 → ℝ))
    (μ : Measure (Π _ : Finset.Iic n, Fin 1 → ℝ))
    [IsProbabilityMeasure μ]
    (lastPrefix : (Π _ : Finset.Iic n, Fin 1 → ℝ) → Fin 1 → ℝ)
    (hlastPrefixMeasurable : Measurable lastPrefix)
    (prefixMap : (Π _ : Finset.Iic n, Fin 1 → ℝ) → Y)
    (hprefixMap : Measurable prefixMap) :
    let stepKernel : Kernel (Π _ : Finset.Iic n, Fin 1 → ℝ) (Fin 1 → ℝ) :=
      Kernel.comap (dirac_convolution_kernel (νGap : Measure (Fin 1 → ℝ))) lastPrefix
        hlastPrefixMeasurable
    (μ ⊗ₘ stepKernel).map
        (fun p : (Π _ : Finset.Iic n, Fin 1 → ℝ) × (Fin 1 → ℝ) ↦
          (p.2 - lastPrefix p.1, prefixMap p.1)) =
      (νGap : Measure (Fin 1 → ℝ)).prod (μ.map prefixMap) := by
  let stepKernel : Kernel (Π _ : Finset.Iic n, Fin 1 → ℝ) (Fin 1 → ℝ) :=
    Kernel.comap (dirac_convolution_kernel (νGap : Measure (Fin 1 → ℝ))) lastPrefix
      hlastPrefixMeasurable
  let historyGap :
      ((Π _ : Finset.Iic n, Fin 1 → ℝ) × (Fin 1 → ℝ)) →
        (Π _ : Finset.Iic n, Fin 1 → ℝ) × (Fin 1 → ℝ) :=
    fun p ↦ (p.1, p.2 - lastPrefix p.1)
  have hhistoryGapMeasurable : Measurable historyGap := by
    exact measurable_fst.prodMk (measurable_snd.sub (hlastPrefixMeasurable.comp measurable_fst))
  have hswapPrefixMeasurable :
      Measurable
        (fun q : (Π _ : Finset.Iic n, Fin 1 → ℝ) × (Fin 1 → ℝ) ↦
          (q.2, prefixMap q.1)) := by
    exact measurable_snd.prodMk (hprefixMap.comp measurable_fst)
  letI : IsSFiniteKernel stepKernel := by
    dsimp [stepKernel]
    infer_instance
  have hhistoryGapKernel :
      ((Kernel.id ×ₖ stepKernel).map historyGap) =
        Kernel.id ×ₖ
          Kernel.const (Π _ : Finset.Iic n, Fin 1 → ℝ) (νGap : Measure (Fin 1 → ℝ)) := by
    ext z s hs
    let shift : (Fin 1 → ℝ) → Fin 1 → ℝ := fun y ↦ y - lastPrefix z
    have hshiftMeasurable : Measurable shift := by
      simpa [shift] using (measurable_id.sub measurable_const)
    have htranslateMeasurable :
        Measurable (fun y : Fin 1 → ℝ ↦ lastPrefix z + y) := by
      simpa using (measurable_const.add measurable_id)
    have hshift :
        (stepKernel z).map shift = (νGap : Measure (Fin 1 → ℝ)) := by
      -- Proof comment: each row of `stepKernel` is `δ_{lastPrefix z} * νGap`; subtracting the
      -- prefix endpoint centers it back to `νGap`.
      rw [Kernel.comap_apply, dirac_convolution_kernel_apply]
      rw [Measure.dirac_conv]
      simpa [shift, Function.comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (Measure.map_map
          (μ := (νGap : Measure (Fin 1 → ℝ)))
          (f := fun y ↦ lastPrefix z + y) (g := shift)
          hshiftMeasurable htranslateMeasurable)
    have hmap :
        ((Kernel.id ×ₖ stepKernel).map historyGap) z s =
          (((stepKernel z).map shift).map (Prod.mk z)) s := by
      -- Proof comment: after fixing the history, the mapped pair row inserts that history and
      -- centers the fresh increment.
      rw [Kernel.map_apply' _ hhistoryGapMeasurable _ hs]
      rw [Kernel.id_prod_apply' stepKernel z (hhistoryGapMeasurable hs)]
      rw [Measure.map_apply measurable_prodMk_left hs]
      rw [Measure.map_apply hshiftMeasurable (measurable_prodMk_left hs)]
      congr 1
    calc
      (((Kernel.id ×ₖ stepKernel).map historyGap) z) s
          = (((stepKernel z).map shift).map (Prod.mk z)) s := hmap
      _ = (Measure.map (Prod.mk z) (νGap : Measure (Fin 1 → ℝ))) s := by
            rw [hshift]
      _ =
          ((Kernel.id ×ₖ
              Kernel.const (Π _ : Finset.Iic n, Fin 1 → ℝ) (νGap : Measure (Fin 1 → ℝ))) z) s := by
            rw [Kernel.id_prod_apply'
              (Kernel.const (Π _ : Finset.Iic n, Fin 1 → ℝ) (νGap : Measure (Fin 1 → ℝ))) z hs]
            rw [Kernel.const_apply, Measure.map_apply (by fun_prop) hs]
  have hhistoryGapMeasure :
      (μ ⊗ₘ stepKernel).map historyGap = μ.prod (νGap : Measure (Fin 1 → ℝ)) := by
    -- Proof comment: the mapped pair law keeps the history and makes the centered fresh gap an
    -- independent second coordinate with law `νGap`.
    calc
      (μ ⊗ₘ stepKernel).map historyGap =
          (((Kernel.id ×ₖ stepKernel).map historyGap) ∘ₘ μ) := by
            rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ (by fun_prop)]
      _ =
          ((Kernel.id ×ₖ
              Kernel.const (Π _ : Finset.Iic n, Fin 1 → ℝ) (νGap : Measure (Fin 1 → ℝ))) ∘ₘ μ) := by
            rw [hhistoryGapKernel]
      _ =
          μ ⊗ₘ Kernel.const (Π _ : Finset.Iic n, Fin 1 → ℝ) (νGap : Measure (Fin 1 → ℝ)) := by
            rw [Measure.compProd_eq_comp_prod]
      _ = μ.prod (νGap : Measure (Fin 1 → ℝ)) := by
            simpa using
              (Measure.compProd_const
                (μ := μ) (ν := (νGap : Measure (Fin 1 → ℝ))))
  -- Proof comment: map the history coordinate through `prefixMap`, then swap the pair factors to
  -- obtain `(gap, prefix statistic)`.
  calc
    (μ ⊗ₘ stepKernel).map
        (fun p : (Π _ : Finset.Iic n, Fin 1 → ℝ) × (Fin 1 → ℝ) ↦
          (p.2 - lastPrefix p.1, prefixMap p.1))
        = ((μ ⊗ₘ stepKernel).map historyGap).map
            (fun q : (Π _ : Finset.Iic n, Fin 1 → ℝ) × (Fin 1 → ℝ) ↦
              (q.2, prefixMap q.1)) := by
              simpa [historyGap, Function.comp] using
                (Measure.map_map
                  (μ := μ ⊗ₘ stepKernel)
                  (f := historyGap)
                  (g := fun q : (Π _ : Finset.Iic n, Fin 1 → ℝ) × (Fin 1 → ℝ) ↦
                    (q.2, prefixMap q.1))
                  hswapPrefixMeasurable
                  hhistoryGapMeasurable).symm
    _ = (μ.prod (νGap : Measure (Fin 1 → ℝ))).map
          (fun q : (Π _ : Finset.Iic n, Fin 1 → ℝ) × (Fin 1 → ℝ) ↦
            (q.2, prefixMap q.1)) := by
              rw [hhistoryGapMeasure]
    _ = (((μ.prod (νGap : Measure (Fin 1 → ℝ))).map (Prod.map prefixMap id)).map Prod.swap) := by
          simpa [Function.comp] using
            (Measure.map_map
              (μ := μ.prod (νGap : Measure (Fin 1 → ℝ)))
              (f := Prod.map prefixMap id)
              (g := Prod.swap)
              measurable_swap
              (hprefixMap.prodMap measurable_id)).symm
    _ = (((μ.map prefixMap).prod (νGap : Measure (Fin 1 → ℝ))).map Prod.swap) := by
          rw [← Measure.map_prod_map
            (μa := μ) (μc := (νGap : Measure (Fin 1 → ℝ))) hprefixMap measurable_id]
          simp
    _ = (νGap : Measure (Fin 1 → ℝ)).prod (μ.map prefixMap) := by
          simpa [Measure.map_id] using
            (Measure.prod_swap
              (μ := μ.map prefixMap) (ν := (νGap : Measure (Fin 1 → ℝ))))

/-- Helper for Corollary 21.25: on a strict time grid, the ordered-history increment vector under
the owner finite-dimensional kernel has the product law of the successive transported gaps. -/
private theorem orderedHistoryIncrementVector_map_eq_pi_of_strict
    {n : ℕ} (ν : NNReal → ProbabilityMeasure ℝ)
    (times : Fin (n + 1) → NNReal) (htimes : StrictMono times) (x : Fin 1 → ℝ) :
    let K : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin 1 → ℝ) (Fin 1 → ℝ) :=
      fun {s t} _ ↦ dirac_convolution_kernel (transportedFin1Law ν (t - s) : Measure (Fin 1 → ℝ))
    let j : Π _ : Finset.Iic n, NNReal := orderedTimeChainLocal times
    let hj : StrictMono j := orderedTimeChainLocal_strictMono htimes
    (consistentFamilyFiniteDimensionalKernel K j hj x).map
        (orderedHistoryIncrementVector (n := n)) =
      Measure.pi (fun i : Fin n ↦
        (transportedFin1Law ν (times i.succ - times i.castSucc) : Measure (Fin 1 → ℝ))) := by
  induction n with
  | zero =>
      -- Proof comment: a one-point history has no nontrivial increments.
      have hconst :
          orderedHistoryIncrementVector (n := 0) =
            fun _ : (Π _ : Finset.Iic 0, Fin 1 → ℝ) ↦ (isEmptyElim : Fin 0 → Fin 1 → ℝ) := by
        funext z i
        exact Fin.elim0 i
      simpa [hconst] using
        (show
          Measure.map
              (fun _ : (Π _ : Finset.Iic 0, Fin 1 → ℝ) ↦ (isEmptyElim : Fin 0 → Fin 1 → ℝ))
              ((consistentFamilyFiniteDimensionalKernel
                (fun {s t} _ ↦
                  dirac_convolution_kernel
                    (transportedFin1Law ν (t - s) : Measure (Fin 1 → ℝ)))
                (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes)) x) =
            Measure.pi (fun i : Fin 0 ↦
              (transportedFin1Law ν (times i.succ - times i.castSucc) :
                Measure (Fin 1 → ℝ))) from by
            rw [Measure.map_const]
            simpa using
              (Measure.pi_of_empty
                (fun i : Fin 0 ↦
                  (transportedFin1Law ν (times i.succ - times i.castSucc) :
                    Measure (Fin 1 → ℝ)))
                (isEmptyElim : Fin 0 → Fin 1 → ℝ)).symm)
  | succ n ih =>
      let K : ∀ ⦃s t : NNReal⦄, s < t → Kernel (Fin 1 → ℝ) (Fin 1 → ℝ) :=
        fun {s t} _ ↦ dirac_convolution_kernel (transportedFin1Law ν (t - s) : Measure (Fin 1 → ℝ))
      let prefixTimes : Fin (n + 1) → NNReal := fun i ↦ times i.castSucc
      let hprefixStrict : StrictMono prefixTimes := by
        intro i k hik
        exact htimes (by simpa [prefixTimes] using hik)
      let νHist : Measure (Π _ : Finset.Iic (n + 1), Fin 1 → ℝ) :=
        consistentFamilyFiniteDimensionalKernel K
          (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes) x
      let νPrefix : Measure (Π _ : Finset.Iic n, Fin 1 → ℝ) :=
        consistentFamilyFiniteDimensionalKernel K
          (orderedTimeChainLocal prefixTimes)
          (orderedTimeChainLocal_strictMono hprefixStrict) x
      let e :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin 1 → ℝ) (Fin.last n)
      let νGap : ProbabilityMeasure (Fin 1 → ℝ) :=
        transportedFin1Law ν (times (Fin.last n).succ - times (Fin.last n).castSucc)
      have hκMarkov : ∀ {s t : NNReal} (hst : s < t), IsMarkovKernel (K hst) := by
        intro s t hst
        dsimp [K]
        infer_instance
      letI :
          IsMarkovKernel
            (consistentFamilyFiniteDimensionalKernel K
              (orderedTimeChainLocal prefixTimes)
              (orderedTimeChainLocal_strictMono hprefixStrict)) :=
        consistentFamilyFiniteDimensionalKernel_isMarkov K
          (fun {_ _} hst ↦ hκMarkov hst)
          (orderedTimeChainLocal prefixTimes)
          (orderedTimeChainLocal_strictMono hprefixStrict)
      letI : IsProbabilityMeasure νPrefix := by
        dsimp [νPrefix]
        infer_instance
      have hsplit :
          νHist.map (succHistoryEquivLocal n) =
            νPrefix ⊗ₘ
              Kernel.comap (dirac_convolution_kernel (νGap : Measure (Fin 1 → ℝ)))
                (fun z : Π _ : Finset.Iic n, Fin 1 → ℝ ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
                (measurable_lastIicCoordinate (n := n)) := by
        -- Proof comment: split the ordered history into its prefix and the final translated step.
        simpa [νHist, νPrefix, K, νGap, prefixTimes, orderedTimeChainLocal, iicEquivFinLocal]
          using
            (consistentFamilyFiniteDimensionalKernel_map_succHistoryEquiv_eq_compProd
              (K := K) (j := orderedTimeChainLocal times)
              (hj := orderedTimeChainLocal_strictMono htimes) (x := x))
      have hpair :
          ((νHist.map (orderedHistoryIncrementVector (n := n + 1))).map e) =
            (νGap : Measure (Fin 1 → ℝ)).prod
              (Measure.pi
                (fun i : Fin n ↦
                  (transportedFin1Law ν
                    (prefixTimes i.succ - prefixTimes i.castSucc) :
                      Measure (Fin 1 → ℝ)))) := by
        -- Proof comment: isolate the terminal increment with `piFinSuccAbove`; the split-history
        -- law then factors this last gap from the prefix increment vector.
        calc
          ((νHist.map (orderedHistoryIncrementVector (n := n + 1))).map e) =
              (νHist.map
                (fun z : Π _ : Finset.Iic (n + 1), Fin 1 → ℝ ↦
                  e (orderedHistoryIncrementVector (n := n + 1) z))) := by
                    simpa [Function.comp] using
                      (Measure.map_map
                        (μ := νHist)
                        (f := orderedHistoryIncrementVector (n := n + 1))
                        (g := e)
                        e.measurable
                        (measurable_orderedHistoryIncrementVector (n := n + 1)))
          _ =
              (νHist.map
                (fun z : Π _ : Finset.Iic (n + 1), Fin 1 → ℝ ↦
                  let p := succHistoryEquivLocal n z
                  (p.2 - p.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩,
                    orderedHistoryIncrementVector (n := n) p.1))) := by
                      congr 1
                      exact orderedHistoryIncrementVector_piFinSuccAbove_last (n := n)
          _ =
              ((νHist.map (succHistoryEquivLocal n)).map
                (fun p : (Π _ : Finset.Iic n, Fin 1 → ℝ) × (Fin 1 → ℝ) ↦
                  (p.2 - p.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩,
                    orderedHistoryIncrementVector (n := n) p.1))) := by
                      symm
                      exact
                        Measure.map_map
                          ((measurable_snd.sub
                            ((measurable_lastIicCoordinate (n := n)).comp measurable_fst)).prodMk
                            ((measurable_orderedHistoryIncrementVector (n := n)).comp
                              measurable_fst))
                          (succHistoryEquivLocal n).measurable
          _ =
              ((νPrefix ⊗ₘ
                Kernel.comap (dirac_convolution_kernel (νGap : Measure (Fin 1 → ℝ)))
                  (fun z : Π _ : Finset.Iic n, Fin 1 → ℝ ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
                  (measurable_lastIicCoordinate (n := n))).map
                (fun p : (Π _ : Finset.Iic n, Fin 1 → ℝ) × (Fin 1 → ℝ) ↦
                  (p.2 - p.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩,
                    orderedHistoryIncrementVector (n := n) p.1))) := by
                      rw [hsplit]
          _ =
              (νGap : Measure (Fin 1 → ℝ)).prod
                (νPrefix.map (orderedHistoryIncrementVector (n := n))) := by
                simpa [νGap, νPrefix] using
                  (compProd_map_gapAndPrefix_eq_prod
                    (νGap := νGap) (μ := νPrefix)
                    (lastPrefix := fun z : Π _ : Finset.Iic n, Fin 1 → ℝ ↦
                      z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
                    (hlastPrefixMeasurable := measurable_lastIicCoordinate (n := n))
                    (prefixMap := orderedHistoryIncrementVector (n := n))
                    (hprefixMap := measurable_orderedHistoryIncrementVector (n := n)))
          _ =
              (νGap : Measure (Fin 1 → ℝ)).prod
                (Measure.pi
                  (fun i : Fin n ↦
                    (transportedFin1Law ν
                      (prefixTimes i.succ - prefixTimes i.castSucc) :
                        Measure (Fin 1 → ℝ)))) := by
                rw [ih prefixTimes hprefixStrict]
      have hpairPi :
          (Measure.pi (fun i : Fin (n + 1) ↦
            (transportedFin1Law ν (times i.succ - times i.castSucc) :
              Measure (Fin 1 → ℝ)))).map e =
              (νGap : Measure (Fin 1 → ℝ)).prod
                (Measure.pi
                  (fun i : Fin n ↦
                    (transportedFin1Law ν
                      (prefixTimes i.succ - prefixTimes i.castSucc) :
                        Measure (Fin 1 → ℝ)))) := by
        simpa [e, νGap, prefixTimes] using
          incrementLawPi_map_piFinSuccAbove_last ν times
      -- Proof comment: both sides have the same image under `piFinSuccAbove`; mapping back by
      -- the inverse equivalence recovers the full product law.
      calc
        νHist.map (orderedHistoryIncrementVector (n := n + 1)) =
            ((νHist.map (orderedHistoryIncrementVector (n := n + 1))).map e).map e.symm := by
              simpa [e] using
                (MeasurableEquiv.map_map_symm
                  (ν := νHist.map (orderedHistoryIncrementVector (n := n + 1)))
                  e.symm).symm
        _ =
            ((Measure.pi (fun i : Fin (n + 1) ↦
              (transportedFin1Law ν (times i.succ - times i.castSucc) :
                Measure (Fin 1 → ℝ)))).map e).map e.symm := by
                  rw [hpair, hpairPi.symm]
        _ =
            Measure.pi (fun i : Fin (n + 1) ↦
              (transportedFin1Law ν (times i.succ - times i.castSucc) :
                Measure (Fin 1 → ℝ))) := by
                  simpa [e] using
                    (MeasurableEquiv.map_map_symm
                      (ν := Measure.pi (fun i : Fin (n + 1) ↦
                        (transportedFin1Law ν (times i.succ - times i.castSucc) :
                          Measure (Fin 1 → ℝ))))
                      e.symm)

/-- Helper for Corollary 21.25: on an anchored strict time grid, the canonical path measure sends
the finite increment vector to the product law of the successive transported gaps. -/
private theorem canonicalIncrementVector_map_eq_pi_of_strict_start_zero
    (ν : NNReal → ProbabilityMeasure ℝ)
    {P : Measure (NNReal → Fin 1 → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦
                dirac_convolution_kernel (transportedFin1Law ν t : Measure (Fin 1 → ℝ)))
              times htimes ∘ₘ Measure.dirac (0 : Fin 1 → ℝ))
    {n : ℕ} (times : Fin (n + 1) → NNReal)
    (hzero : times 0 = 0) (htimes : StrictMono times) :
    P.map (incrementVector times) =
      Measure.pi (fun i : Fin n ↦
        (transportedFin1Law ν (times i.succ - times i.castSucc) : Measure (Fin 1 → ℝ))) := by
  letI : IsProbabilityMeasure P :=
    (transportedFin1PathMeasure_start_hasLaw (ν := ν) hP_fdim).isProbabilityMeasure
  have hcomp :
      tupleIncrementVector (n := n) ∘ finiteDimensionalProjection times =
        incrementVector times := by
    -- Proof comment: the public increment vector is adjacent differences of the finite tuple.
    exact tupleIncrementVector_comp_finiteDimensionalProjection times
  let νHist : Measure (Π _ : Finset.Iic n, Fin 1 → ℝ) :=
    consistentFamilyFiniteDimensionalKernel
      (fun {s t : NNReal} _ ↦
        dirac_convolution_kernel (transportedFin1Law ν (t - s) : Measure (Fin 1 → ℝ)))
      (orderedTimeChainLocal times) (orderedTimeChainLocal_strictMono htimes) (0 : Fin 1 → ℝ)
  have hpublic :
      ((markovSemigroupFiniteDimKernelLocal
        (fun t ↦ dirac_convolution_kernel (transportedFin1Law ν t : Measure (Fin 1 → ℝ)))
        times htimes) ∘ₘ Measure.dirac (0 : Fin 1 → ℝ)).map
          (tupleIncrementVector (n := n)) =
        νHist.map (orderedHistoryIncrementVector (n := n)) := by
    -- Proof comment: `markovSemigroupFiniteDimKernelLocal` is the ordered-history law reindexed to
    -- `Fin`, and `orderedHistoryIncrementVector` records the same adjacent differences there.
    change
      Measure.map (tupleIncrementVector (n := n))
          (Measure.map
            (fun z : Π _ : Finset.Iic n, Fin 1 → ℝ ↦
              fun i : Fin (n + 1) ↦ z ((iicEquivFinLocal n).symm i))
            νHist) =
        _
    simpa [orderedHistoryIncrementVector, Function.comp] using
      (Measure.map_map
        (μ := νHist)
        (f := fun z : Π _ : Finset.Iic n, Fin 1 → ℝ ↦
          fun i : Fin (n + 1) ↦ z ((iicEquivFinLocal n).symm i))
        (g := tupleIncrementVector (n := n))
        (measurable_tupleIncrementVector (n := n))
        (by
          refine measurable_pi_lambda _ fun i ↦ ?_
          exact measurable_pi_apply ((iicEquivFinLocal n).symm i))).symm
  -- Proof comment: rewrite the public increment vector as adjacent differences of the
  -- finite-dimensional tuple, replace that tuple law using `hP_fdim`, and transport the strict
  -- owner-side product law back to the public path space.
  calc
    P.map (incrementVector times) =
        P.map (tupleIncrementVector (n := n) ∘ finiteDimensionalProjection times) := by
          simpa [Function.comp] using
            congrArg
              (fun f : (NNReal → Fin 1 → ℝ) → Fin n → Fin 1 → ℝ ↦ P.map f)
              hcomp.symm
    _ =
        (P.map (finiteDimensionalProjection times)).map
          (tupleIncrementVector (n := n)) := by
            symm
            exact
              Measure.map_map
                (measurable_tupleIncrementVector (n := n))
                (measurable_finiteDimensionalProjection times)
    _ =
        (((markovSemigroupFiniteDimKernelLocal
          (fun t ↦ dirac_convolution_kernel (transportedFin1Law ν t : Measure (Fin 1 → ℝ)))
          times htimes) ∘ₘ Measure.dirac (0 : Fin 1 → ℝ))).map
            (tupleIncrementVector (n := n)) := by
              rw [hP_fdim times hzero htimes]
    _ = νHist.map (orderedHistoryIncrementVector (n := n)) := hpublic
    _ =
        Measure.pi (fun i : Fin n ↦
          (transportedFin1Law ν (times i.succ - times i.castSucc) : Measure (Fin 1 → ℝ))) := by
            exact orderedHistoryIncrementVector_map_eq_pi_of_strict ν times htimes (0 : Fin 1 → ℝ)

/-- Helper for Corollary 21.25: deleting the later endpoint of one adjacent duplicate from a
finite time grid. -/
private def deleteAdjacentDuplicateTimes {n : ℕ}
    (times : Fin (n + 2) → NNReal) (k : Fin (n + 1)) : Fin (n + 1) → NNReal :=
  fun i ↦ times (k.succ.succAbove i)

/-- Helper for Corollary 21.25: deleting the later endpoint of an adjacent duplicate preserves
the anchored zero start. -/
private theorem deleteAdjacentDuplicateTimes_zero {n : ℕ}
    {times : Fin (n + 2) → NNReal} {k : Fin (n + 1)} (hzero : times 0 = 0) :
    deleteAdjacentDuplicateTimes times k 0 = 0 := by
  -- Proof comment: the deleted coordinate is always positive, so time `0` survives untouched.
  simpa [deleteAdjacentDuplicateTimes] using hzero

/-- Helper for Corollary 21.25: deleting the later endpoint of an adjacent duplicate preserves
monotonicity. -/
private theorem deleteAdjacentDuplicateTimes_monotone {n : ℕ}
    {times : Fin (n + 2) → NNReal} {k : Fin (n + 1)} (htimes : Monotone times) :
    Monotone (deleteAdjacentDuplicateTimes times k) := by
  intro i j hij
  -- Proof comment: `Fin.succAbove` preserves the order of all surviving coordinates.
  exact htimes (by simpa [deleteAdjacentDuplicateTimes] using hij)

/-- Helper for Corollary 21.25: on the shortened grid, the successor coordinate is the successor
of the corresponding surviving long-grid increment index. -/
private theorem deleteAdjacentDuplicateTimes_succ {n : ℕ}
    (times : Fin (n + 2) → NNReal) (k : Fin (n + 1)) (i : Fin n) :
    deleteAdjacentDuplicateTimes times k i.succ = times (k.succAbove i).succ := by
  -- Proof comment: `succAbove` commutes with `succ` when deleting the right endpoint of the
  -- duplicated adjacent pair.
  simp [deleteAdjacentDuplicateTimes]

/-- Helper for Corollary 21.25: on the shortened grid, the surviving left endpoint matches the
corresponding long-grid increment index. -/
private theorem deleteAdjacentDuplicateTimes_castSucc {n : ℕ}
    (times : Fin (n + 2) → NNReal) (k : Fin (n + 1))
    (hdup : times k.castSucc = times k.succ) (i : Fin n) :
    deleteAdjacentDuplicateTimes times k i.castSucc = times (k.succAbove i).castSucc := by
  -- Proof comment: before the duplicate, both index constructions are literal; after it, either
  -- the duplicate equality `hdup` or the same successor shift identifies the endpoints.
  change times (k.succ.succAbove i.castSucc) = times (k.succAbove i).castSucc
  by_cases hik : i.castSucc < k
  · rw [show k.succ.succAbove i.castSucc = i.castSucc.castSucc by
        exact Fin.succAbove_succ_of_le k i.castSucc (le_of_lt hik)]
    rw [Fin.succAbove_of_castSucc_lt k i hik]
  · have hk : k ≤ i.castSucc := le_of_not_gt hik
    rcases lt_or_eq_of_le hk with hki | hEq
    · rw [show k.succ.succAbove i.castSucc = i.castSucc.succ by
          exact Fin.succAbove_of_le_castSucc k.succ i.castSucc
            (Fin.succ_le_castSucc_iff.mpr hki)]
      rw [Fin.succAbove_of_le_castSucc k i hk, Fin.succ_castSucc]
    · subst hEq
      rw [Fin.succAbove_succ_self, Fin.succAbove_castSucc_self]
      exact hdup.trans (congrArg times (Fin.succ_castSucc i))

/-- Helper for Corollary 21.25: if two adjacent times coincide, then separating that increment
coordinate exposes a deterministic `0` together with the shortened increment vector. -/
private theorem incrementVector_piFinSuccAbove_of_adjacentDuplicate {n : ℕ}
    (times : Fin (n + 2) → NNReal) (k : Fin (n + 1))
    (hdup : times k.castSucc = times k.succ) :
    (fun ω ↦
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin 1 → ℝ) k
        (incrementVector times ω)) =
      fun ω ↦ (0, incrementVector (deleteAdjacentDuplicateTimes times k) ω) := by
  -- Proof comment: the separated increment is the duplicated zero gap, and every surviving
  -- coordinate matches the shortened-grid increment vector.
  funext ω
  apply Prod.ext
  · simp [incrementVector, MeasurableEquiv.piFinSuccAbove_apply, hdup]
  · ext i
    change
      ω (times (k.succAbove i).succ) - ω (times (k.succAbove i).castSucc) =
        ω (deleteAdjacentDuplicateTimes times k i.succ) -
          ω (deleteAdjacentDuplicateTimes times k i.castSucc)
    rw [deleteAdjacentDuplicateTimes_succ, deleteAdjacentDuplicateTimes_castSucc _ _ hdup]

/-- Helper for Corollary 21.25: the transported increment product law on a grid with one adjacent
duplicate is the zero-insertion of the shortened-grid product law. -/
private theorem incrementLawPi_map_piFinSuccAbove_of_adjacentDuplicate {n : ℕ}
    (ν : NNReal → ProbabilityMeasure ℝ) [IsContinuousConvolutionSemigroup ν]
    (times : Fin (n + 2) → NNReal) (k : Fin (n + 1))
    (hdup : times k.castSucc = times k.succ) :
    (Measure.pi (fun i : Fin (n + 1) ↦
      (transportedFin1Law ν (times i.succ - times i.castSucc) : Measure (Fin 1 → ℝ)))).map
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin 1 → ℝ) k) =
        (Measure.dirac (0 : Fin 1 → ℝ)).prod
          (Measure.pi (fun i : Fin n ↦
            (transportedFin1Law ν
              ((deleteAdjacentDuplicateTimes times k) i.succ -
                (deleteAdjacentDuplicateTimes times k) i.castSucc) :
              Measure (Fin 1 → ℝ)))) := by
  let μ : Fin (n + 1) → Measure (Fin 1 → ℝ) := fun i ↦
    (transportedFin1Law ν (times i.succ - times i.castSucc) : Measure (Fin 1 → ℝ))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin 1 → ℝ) k
  have hMapEq :
      (Measure.pi μ).map e = (μ k).prod (Measure.pi fun i : Fin n ↦ μ (k.succAbove i)) :=
    (measurePreserving_piFinSuccAbove μ k).map_eq
  have hν : IsConvolutionSemigroupWithZero (transportedFin1Law ν) :=
    transportedFin1ConvolutionSemigroupWithZero ν
  have hk : μ k = Measure.dirac (0 : Fin 1 → ℝ) := by
    -- Proof comment: the duplicated adjacent gap has length `0`, so its transported law is the
    -- time-zero Dirac mass.
    have hzero :
        transportedFin1Law ν (times k.succ - times k.castSucc) = diracProba (0 : Fin 1 → ℝ) := by
      calc
        transportedFin1Law ν (times k.succ - times k.castSucc)
            = transportedFin1Law ν 0 := by simp [hdup]
        _ = diracProba (0 : Fin 1 → ℝ) := by
              simpa [ProbabilityMeasure.one_eq_diracProba] using hν.zero_eq
    exact congrArg (fun ρ : ProbabilityMeasure (Fin 1 → ℝ) ↦ (ρ : Measure (Fin 1 → ℝ))) hzero
  have htail :
      (fun i : Fin n ↦ μ (k.succAbove i)) =
        (fun i : Fin n ↦
          (transportedFin1Law ν
            ((deleteAdjacentDuplicateTimes times k) i.succ -
              (deleteAdjacentDuplicateTimes times k) i.castSucc) :
            Measure (Fin 1 → ℝ))) := by
    -- Proof comment: every surviving marginal is the transported gap law on the shortened grid.
    funext i
    simp [μ, deleteAdjacentDuplicateTimes_succ, deleteAdjacentDuplicateTimes_castSucc, hdup]
  rw [hMapEq, hk, htail]

/-- Helper for Corollary 21.25: the strict-grid increment product law extends to monotone
anchored grids by repeatedly deleting adjacent duplicate times. -/
private theorem canonicalIncrementVector_map_eq_pi_of_monotone_start_zero
    (ν : NNReal → ProbabilityMeasure ℝ) [IsContinuousConvolutionSemigroup ν]
    {P : Measure (NNReal → Fin 1 → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦
                dirac_convolution_kernel (transportedFin1Law ν t : Measure (Fin 1 → ℝ)))
              times htimes ∘ₘ Measure.dirac (0 : Fin 1 → ℝ)) :
    ∀ {n : ℕ} (times : Fin (n + 1) → NNReal), times 0 = 0 → Monotone times →
      P.map (incrementVector times) =
        Measure.pi (fun i : Fin n ↦
          (transportedFin1Law ν (times i.succ - times i.castSucc) : Measure (Fin 1 → ℝ))) := by
  letI : IsProbabilityMeasure P :=
    (transportedFin1PathMeasure_start_hasLaw (ν := ν) hP_fdim).isProbabilityMeasure
  intro n times hzero htimes
  induction n with
  | zero =>
      -- Proof comment: an anchored grid with no increments has the trivial empty product law.
      have hconst :
          incrementVector times =
            fun _ : NNReal → Fin 1 → ℝ ↦ (isEmptyElim : Fin 0 → Fin 1 → ℝ) := by
        funext ω i
        exact Fin.elim0 i
      rw [hconst, Measure.map_const]
      simpa using
        (Measure.pi_of_empty
          (fun i : Fin 0 ↦
            (transportedFin1Law ν (times i.succ - times i.castSucc) :
              Measure (Fin 1 → ℝ)))
          (isEmptyElim : Fin 0 → Fin 1 → ℝ)).symm
  | succ n ih =>
      by_cases hstrict : StrictMono times
      · -- Proof comment: once the grid is strict, the strict-grid theorem applies directly.
        exact canonicalIncrementVector_map_eq_pi_of_strict_start_zero (ν := ν) hP_fdim times
          hzero hstrict
      · have hnotlt : ¬ ∀ i : Fin (n + 1), times i.castSucc < times i.succ := by
          simpa [Fin.strictMono_iff_lt_succ] using hstrict
        push_neg at hnotlt
        obtain ⟨k, hk⟩ := hnotlt
        have hdup : times k.castSucc = times k.succ := by
          -- Proof comment: on a monotone grid, failure of strict increase forces an adjacent
          -- equality.
          exact le_antisymm (htimes Fin.castSucc_lt_succ.le) hk
        let times' : Fin (n + 1) → NNReal := deleteAdjacentDuplicateTimes times k
        have hzero' : times' 0 = 0 := deleteAdjacentDuplicateTimes_zero hzero
        have htimes' : Monotone times' := deleteAdjacentDuplicateTimes_monotone htimes
        have hshort :
            P.map (incrementVector times') =
              Measure.pi (fun i : Fin n ↦
                (transportedFin1Law ν (times' i.succ - times' i.castSucc) :
                  Measure (Fin 1 → ℝ))) :=
          ih times' hzero' htimes'
        let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin 1 → ℝ) k
        have hpair :
            (P.map (incrementVector times)).map e =
              (P.map (incrementVector times')).map (Prod.mk (0 : Fin 1 → ℝ)) := by
          -- Proof comment: splitting at the duplicated increment exposes a deterministic zero and
          -- the shortened increment vector.
          calc
            (P.map (incrementVector times)).map e =
                P.map (fun ω ↦ e (incrementVector times ω)) := by
                  simpa [Function.comp] using
                    (Measure.map_map e.measurable (incrementVector_measurable times))
            _ = P.map (fun ω ↦ (0, incrementVector times' ω)) := by
                  congr 1
                  exact incrementVector_piFinSuccAbove_of_adjacentDuplicate times k hdup
            _ = (P.map (incrementVector times')).map (Prod.mk (0 : Fin 1 → ℝ)) := by
                  simpa [Function.comp] using
                    (Measure.map_map
                      (μ := P)
                      (f := incrementVector times')
                      (g := Prod.mk (0 : Fin 1 → ℝ))
                      ((measurable_const).prodMk measurable_id)
                      (incrementVector_measurable times')).symm
        have hpairPi :
            (Measure.pi (fun i : Fin (n + 1) ↦
              (transportedFin1Law ν (times i.succ - times i.castSucc) :
                Measure (Fin 1 → ℝ)))).map e =
                (Measure.pi (fun i : Fin n ↦
                  (transportedFin1Law ν (times' i.succ - times' i.castSucc) :
                    Measure (Fin 1 → ℝ)))).map
                    (Prod.mk (0 : Fin 1 → ℝ)) := by
          -- Proof comment: the product gap law undergoes the same zero-insertion normalization.
          calc
            (Measure.pi (fun i : Fin (n + 1) ↦
              (transportedFin1Law ν (times i.succ - times i.castSucc) :
                Measure (Fin 1 → ℝ)))).map e =
                (Measure.dirac (0 : Fin 1 → ℝ)).prod
                  (Measure.pi (fun i : Fin n ↦
                    (transportedFin1Law ν (times' i.succ - times' i.castSucc) :
                      Measure (Fin 1 → ℝ)))) := by
                      simpa [times'] using
                        incrementLawPi_map_piFinSuccAbove_of_adjacentDuplicate
                          (ν := ν) times k hdup
            _ =
                (Measure.pi (fun i : Fin n ↦
                  (transportedFin1Law ν (times' i.succ - times' i.castSucc) :
                    Measure (Fin 1 → ℝ)))).map
                      (Prod.mk (0 : Fin 1 → ℝ)) := by
                        rw [Measure.dirac_prod]
        -- Proof comment: compare both image laws after deleting the duplicated coordinate, then
        -- map back through the measurable equivalence `e`.
        calc
          P.map (incrementVector times) =
              ((P.map (incrementVector times)).map e).map e.symm := by
                simpa [e] using
                  (MeasurableEquiv.map_map_symm
                    (ν := P.map (incrementVector times)) e.symm).symm
          _ = (((P.map (incrementVector times')).map (Prod.mk (0 : Fin 1 → ℝ))).map e.symm) := by
                rw [hpair]
          _ =
              (((Measure.pi (fun i : Fin n ↦
                (transportedFin1Law ν (times' i.succ - times' i.castSucc) :
                  Measure (Fin 1 → ℝ)))).map
                  (Prod.mk (0 : Fin 1 → ℝ))).map e.symm) := by
                    rw [hshort]
          _ =
              (((Measure.pi (fun i : Fin (n + 1) ↦
                (transportedFin1Law ν (times i.succ - times i.castSucc) :
                  Measure (Fin 1 → ℝ)))).map e)).map e.symm := by
                    rw [hpairPi.symm]
          _ =
              Measure.pi (fun i : Fin (n + 1) ↦
                (transportedFin1Law ν (times i.succ - times i.castSucc) :
                  Measure (Fin 1 → ℝ))) := by
                    simpa [e] using
                      (MeasurableEquiv.map_map_symm
                        (ν := Measure.pi (fun i : Fin (n + 1) ↦
                          (transportedFin1Law ν (times i.succ - times i.castSucc) :
                            Measure (Fin 1 → ℝ))))
                        e.symm)

/-- Helper for Corollary 21.25: convert the canonical finite-dimensional marginal specification
into independent increments for the coordinate process on `NNReal → Fin 1 → ℝ`. -/
private theorem transportedFin1CanonicalPathMeasure_hasIndepIncrements
    (ν : NNReal → ProbabilityMeasure ℝ)
    [IsContinuousConvolutionSemigroup ν]
    {P : Measure (NNReal → Fin 1 → ℝ)}
    (hP_fdim :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernelLocal
              (fun t ↦
                dirac_convolution_kernel (transportedFin1Law ν t : Measure (Fin 1 → ℝ)))
              times htimes ∘ₘ Measure.dirac (0 : Fin 1 → ℝ)) :
    HasIndepIncrements Function.eval P := by
  classical
  letI : IsProbabilityMeasure P :=
    (transportedFin1PathMeasure_start_hasLaw (ν := ν) hP_fdim).isProbabilityMeasure
  rw [hasIndepIncrements_iff_nat]
  intro t ht
  -- Route correction: package each monotone `ℕ`-grid through a finite anchored prefix, prove the
  -- full prefix increment product law there, and restrict back to the requested finite family.
  refine iIndepFun_iff_finset.2 ?_
  intro s
  by_cases hs : s.Nonempty
  · let N : ℕ := s.max' hs + 1
    let times : Fin (N + 2) → NNReal := Fin.cases 0 fun i ↦ t i
    have htimes : Monotone times := by
      intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero =>
              simp [times]
          | succ j =>
              simp [times]
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              cases hij
          | succ j =>
              simpa [times] using ht (show i ≤ j by simpa using hij)
    have hgrid :
        P.map (incrementVector times) =
          Measure.pi (fun i : Fin (N + 1) ↦
            (transportedFin1Law ν (times i.succ - times i.castSucc) :
              Measure (Fin 1 → ℝ))) :=
      canonicalIncrementVector_map_eq_pi_of_monotone_start_zero (ν := ν) hP_fdim times
        (by simp [times]) htimes
    have hcoord (i : Fin (N + 1)) :
        P.map (fun ω : NNReal → Fin 1 → ℝ ↦ incrementVector times ω i) =
            (transportedFin1Law ν (times i.succ - times i.castSucc) :
              Measure (Fin 1 → ℝ)) := by
      calc
        P.map (fun ω : NNReal → Fin 1 → ℝ ↦ incrementVector times ω i) =
            (P.map (incrementVector times)).map (Function.eval i) := by
              symm
              simpa [Function.comp] using
                (Measure.map_map
                  (μ := P)
                  (f := incrementVector times)
                  (g := Function.eval i)
                  (measurable_pi_apply i)
                  (incrementVector_measurable times))
        _ = (transportedFin1Law ν (times i.succ - times i.castSucc) :
              Measure (Fin 1 → ℝ)) := by
              simpa [Measure.pi_map_eval] using
                congrArg
                  (fun m : Measure (Fin (N + 1) → Fin 1 → ℝ) ↦ m.map (Function.eval i))
                  hgrid
    have hfull :
        iIndepFun
          (fun i : Fin (N + 1) ↦ fun ω : NNReal → Fin 1 → ℝ ↦ incrementVector times ω i)
          P := by
      -- Proof comment: the finite-grid product-law equality is exactly the `iIndepFun` criterion
      -- on the anchored full increment vector.
      refine (iIndepFun_iff_map_fun_eq_pi_map ?_).2 ?_
      · intro i
        exact ((measurable_pi_apply i).comp (incrementVector_measurable times)).aemeasurable
      · calc
          P.map (incrementVector times) =
              Measure.pi (fun i : Fin (N + 1) ↦
                (transportedFin1Law ν (times i.succ - times i.castSucc) :
                  Measure (Fin 1 → ℝ))) := hgrid
          _ = Measure.pi (fun i : Fin (N + 1) ↦
                P.map (fun ω : NNReal → Fin 1 → ℝ ↦ incrementVector times ω i)) := by
                congr 1
                funext i
                exact (hcoord i).symm
    have htail :
        iIndepFun
          (fun i : Fin N ↦ fun ω : NNReal → Fin 1 → ℝ ↦ incrementVector times ω i.succ)
          P := by
      -- Proof comment: removing the leading anchored increment preserves independence.
      exact hfull.precomp (g := Fin.succ) fun a b h ↦ by simpa using h
    let g : s → Fin N := fun x ↦
      ⟨x.1, Nat.lt_of_le_of_lt (s.le_max' x.1 x.2) (Nat.lt_succ_self _)⟩
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      exact Fin.ext_iff.mp hab
    -- Proof comment: every requested finite family of increments is a restriction of the
    -- anchored finite-grid tail family.
    simpa [times, g, Finset.restrict, incrementVector] using htail.precomp (g := g) hg
  · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs'
    -- Proof comment: the empty family is independent for trivial reasons.
    simpa using
      (iIndepFun.of_subsingleton
        (μ := P)
        (f := (∅ : Finset ℕ).restrict
          (fun i ω ↦ Function.eval (t (i + 1)) ω - Function.eval (t i) ω)))

-/

-- Route correction: the copied local Chapter 14 proof spine above no longer elaborates cleanly.
-- Reuse the canonical owner theorem from `Theorem_14_47`, then keep only the Chap21
-- transport layer.
/-- Helper for Corollary 21.25: Theorem 14.47 already realizes the transported `Fin 1`-valued
convolution semigroup on the canonical path space with deterministic start, stationary
independent increments, and the correct increment laws. -/
private theorem transportedFin1PathMeasureWithStartLaw
    (ν : NNReal → ProbabilityMeasure ℝ) [IsContinuousConvolutionSemigroup ν] (x : Fin 1 → ℝ) :
    ∃ Pbase : ProbabilityMeasure (NNReal → Fin 1 → ℝ),
      HasLaw (Function.eval 0) (Measure.dirac x)
        (Pbase : Measure (NNReal → Fin 1 → ℝ)) ∧
      HasStationaryIndependentIncrements Function.eval
        (Pbase : Measure (NNReal → Fin 1 → ℝ)) ∧
        ∀ ⦃s t : NNReal⦄, s ≤ t →
          HasLaw
            (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - ω s)
            ((transportedFin1Law ν) (t - s) : Measure (Fin 1 → ℝ))
            (Pbase : Measure (NNReal → Fin 1 → ℝ)) := by
  let hνvec : IsConvolutionSemigroupWithZero (transportedFin1Law ν) :=
    transportedFin1ConvolutionSemigroupWithZero ν
  -- Proof comment: the Chapter 14 owner theorem already packages exactly the start law and
  -- increment properties needed for the later Chap21 transports.
  simpa using
    exists_pathMeasure_of_isConvolutionSemigroup
      (ν := transportedFin1Law ν) hνvec x

/-- Helper for Corollary 21.25: realize the transported one-dimensional convolution semigroup on
the canonical base path space `NNReal → Fin 1 → ℝ` by reusing the zero-start canonical owner law.
-/
private theorem existsBaseFin1PathMeasure_of_transportedSemigroup
    (ν : NNReal → ProbabilityMeasure ℝ) [IsContinuousConvolutionSemigroup ν] (x : Fin 1 → ℝ) :
    ∃ Pbase : ProbabilityMeasure (NNReal → Fin 1 → ℝ),
      HasStationaryIndependentIncrements Function.eval
        (Pbase : Measure (NNReal → Fin 1 → ℝ)) ∧
        ∀ ⦃s t : NNReal⦄, s ≤ t →
          HasLaw
            (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - ω s)
            ((transportedFin1Law ν) (t - s) : Measure (Fin 1 → ℝ))
            (Pbase : Measure (NNReal → Fin 1 → ℝ)) := by
  -- Proof comment: the downstream Chap21 transport only uses the increment package, so we drop
  -- the deterministic start-law field from the Chapter 14 owner theorem.
  exact
    existsBasePathMeasure_of_existsPathMeasureWithStartLaw
      (ν := transportedFin1Law ν) x
      (transportedFin1PathMeasureWithStartLaw (ν := ν) x)

/-- Helper for Corollary 21.25: pushing the base path law forward along `ULift.up` preserves the
law of a single path increment. -/
private theorem liftedFin1Path_incrementMap
    (Pbase : ProbabilityMeasure (NNReal → Fin 1 → ℝ)) (s t : NNReal) :
    (ProbabilityMeasure.map Pbase measurable_up.aemeasurable : Measure LiftedFin1PathSpace).map
      (fun ω : LiftedFin1PathSpace ↦ ω.down t - ω.down s) =
      (Pbase : Measure (NNReal → Fin 1 → ℝ)).map
        (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - ω s) := by
  let f : LiftedFin1PathSpace → Fin 1 → ℝ := fun ω ↦ ω.down t - ω.down s
  let g : (NNReal → Fin 1 → ℝ) → Fin 1 → ℝ := fun ω ↦ ω t - ω s
  have hf : Measurable f := by
    -- Proof comment: the lifted increment is a measurable difference of two evaluations after
    -- reading the underlying base path.
    exact ((measurable_pi_apply t).comp measurable_down).sub
      ((measurable_pi_apply s).comp measurable_down)
  -- Proof comment: collapse the pushforward by `ULift.up` with the increment map and rewrite the
  -- composition pointwise as the base increment.
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_map hf measurable_up]
  exact Measure.map_congr <| Filter.EventuallyEq.of_eq <| by
    funext ω
    rfl

/-- Helper for Corollary 21.25: pushing the base path law forward along `ULift.up` preserves the
joint law of every finite increment tuple. -/
private theorem liftedFin1Path_incrementTupleMap
    (Pbase : ProbabilityMeasure (NNReal → Fin 1 → ℝ))
    {n : ℕ} (times : Fin (n + 1) → NNReal) :
    (ProbabilityMeasure.map Pbase measurable_up.aemeasurable : Measure LiftedFin1PathSpace).map
      (fun ω : LiftedFin1PathSpace ↦
        fun i : Fin n ↦ ω.down (times i.succ) - ω.down (times i.castSucc)) =
      (Pbase : Measure (NNReal → Fin 1 → ℝ)).map
        (fun ω : NNReal → Fin 1 → ℝ ↦
          fun i : Fin n ↦ ω (times i.succ) - ω (times i.castSucc)) := by
  let f : LiftedFin1PathSpace → Fin n → Fin 1 → ℝ :=
    fun ω i ↦ ω.down (times i.succ) - ω.down (times i.castSucc)
  let g : (NNReal → Fin 1 → ℝ) → Fin n → Fin 1 → ℝ :=
    fun ω i ↦ ω (times i.succ) - ω (times i.castSucc)
  have hf : Measurable f := by
    -- Proof comment: each tuple coordinate is again a measurable increment of the lifted path.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact ((measurable_pi_apply (times i.succ)).comp measurable_down).sub
      ((measurable_pi_apply (times i.castSucc)).comp measurable_down)
  -- Proof comment: first compose the two measurable maps, then identify the composite tuple map
  -- with the base increment tuple coordinatewise.
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_map hf measurable_up]
  exact Measure.map_congr <| Filter.EventuallyEq.of_eq <| by
    funext ω
    ext i
    rfl

/-- Helper for Corollary 21.25: pushing the base path law forward along `ULift.up` preserves
independent increments of the coordinate process. -/
private theorem liftedFin1Path_hasIndepIncrements
    (Pbase : ProbabilityMeasure (NNReal → Fin 1 → ℝ))
    (hbase : HasIndepIncrements Function.eval (Pbase : Measure (NNReal → Fin 1 → ℝ))) :
    HasIndepIncrements
      (fun t ↦ fun ω : LiftedFin1PathSpace ↦ ω.down t)
      ((ProbabilityMeasure.map Pbase measurable_up.aemeasurable : ProbabilityMeasure
          LiftedFin1PathSpace) : Measure LiftedFin1PathSpace) := by
  intro n times htimes
  let f : Fin n → LiftedFin1PathSpace → Fin 1 → ℝ :=
    fun i ω ↦ ω.down (times i.succ) - ω.down (times i.castSucc)
  let g : Fin n → (NNReal → Fin 1 → ℝ) → Fin 1 → ℝ :=
    fun i ω ↦ ω (times i.succ) - ω (times i.castSucc)
  have hg : iIndepFun g (Pbase : Measure (NNReal → Fin 1 → ℝ)) := by
    -- Proof comment: the base path measure already has independent increments for the canonical
    -- coordinate process.
    simpa [g, Function.eval] using hbase n times htimes
  have hmap :
      ((ProbabilityMeasure.map Pbase measurable_up.aemeasurable : ProbabilityMeasure
          LiftedFin1PathSpace) : Measure LiftedFin1PathSpace).map
        (fun ω ↦ fun i ↦ f i ω) =
        (Pbase : Measure (NNReal → Fin 1 → ℝ)).map
          (fun ω ↦ fun i ↦ g i ω) := by
    -- Proof comment: normalize the tuple-valued pushforward once via the dedicated ULift bridge.
    simpa [f, g] using liftedFin1Path_incrementTupleMap Pbase times
  have hmarg :
      ∀ i,
        ((ProbabilityMeasure.map Pbase measurable_up.aemeasurable : ProbabilityMeasure
            LiftedFin1PathSpace) : Measure LiftedFin1PathSpace).map (f i) =
          (Pbase : Measure (NNReal → Fin 1 → ℝ)).map (g i) := by
    intro i
    -- Proof comment: each coordinate marginal is the one-increment specialization of the same
    -- ULift transport.
    simpa [f, g] using
      liftedFin1Path_incrementMap Pbase (times i.castSucc) (times i.succ)
  refine (iIndepFun_iff_map_fun_eq_pi_map fun i : Fin n ↦
    (((measurable_pi_apply (times i.succ)).comp measurable_down).sub
      ((measurable_pi_apply (times i.castSucc)).comp measurable_down)).aemeasurable).2 ?_
  calc
    ((ProbabilityMeasure.map Pbase measurable_up.aemeasurable : ProbabilityMeasure
        LiftedFin1PathSpace) : Measure LiftedFin1PathSpace).map
        (fun ω ↦ fun i ↦ f i ω)
        =
          (Pbase : Measure (NNReal → Fin 1 → ℝ)).map
            (fun ω ↦ fun i ↦ g i ω) := hmap
    _ = Measure.pi (fun i ↦ (Pbase : Measure (NNReal → Fin 1 → ℝ)).map (g i)) := by
          exact
            (iIndepFun_iff_map_fun_eq_pi_map fun i : Fin n ↦
              (((measurable_pi_apply (times i.succ)).sub
                (measurable_pi_apply (times i.castSucc))).aemeasurable)).1 hg
    _ = Measure.pi
          (fun i ↦
            ((ProbabilityMeasure.map Pbase measurable_up.aemeasurable : ProbabilityMeasure
                LiftedFin1PathSpace) : Measure LiftedFin1PathSpace).map (f i)) := by
          congr 1
          funext i
          exact (hmarg i).symm

/-- Helper for Corollary 21.25: pushing the base path law forward along `ULift.up` preserves the
law of one increment. -/
private theorem liftedFin1Path_increment_hasLaw
    (Pbase : ProbabilityMeasure (NNReal → Fin 1 → ℝ))
    {νt : Measure (Fin 1 → ℝ)} {s t : NNReal}
    (hbase :
      HasLaw
        (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - ω s)
        νt
        (Pbase : Measure (NNReal → Fin 1 → ℝ))) :
    HasLaw
      (fun ω : LiftedFin1PathSpace ↦ ω.down t - ω.down s)
      νt
      ((ProbabilityMeasure.map Pbase measurable_up.aemeasurable : ProbabilityMeasure
          LiftedFin1PathSpace) : Measure LiftedFin1PathSpace) := by
  refine
    { aemeasurable :=
        (((measurable_pi_apply t).comp measurable_down).sub
          ((measurable_pi_apply s).comp measurable_down)).aemeasurable
      map_eq := ?_ }
  -- Proof comment: the dedicated single-increment transport lemma rewrites the pushed-forward law
  -- to the original base increment law.
  calc
    ((ProbabilityMeasure.map Pbase measurable_up.aemeasurable : ProbabilityMeasure
        LiftedFin1PathSpace) : Measure LiftedFin1PathSpace).map
        (fun ω : LiftedFin1PathSpace ↦ ω.down t - ω.down s)
        =
          (Pbase : Measure (NNReal → Fin 1 → ℝ)).map
            (fun ω : NNReal → Fin 1 → ℝ ↦ ω t - ω s) := by
              simpa using liftedFin1Path_incrementMap Pbase s t
    _ = νt := hbase.map_eq

/-- Helper for Corollary 21.25: package the canonical base path-space owner after pushing it
through `ULift.up`; the main theorem already knows how to transport the resulting vector-valued
increment laws back to the scalar coordinate process. -/
private theorem exists_pathMeasure_of_transportedFin1ConvolutionSemigroup
    (ν : NNReal → ProbabilityMeasure ℝ) [IsContinuousConvolutionSemigroup ν] (x : Fin 1 → ℝ) :
    ∃ P : ProbabilityMeasure LiftedFin1PathSpace,
      HasIndepIncrements
        (fun t ↦ fun ω : LiftedFin1PathSpace ↦ ω.down t)
        (P : Measure LiftedFin1PathSpace) ∧
        ∀ ⦃s t : NNReal⦄, s ≤ t →
          HasLaw
            (fun ω : LiftedFin1PathSpace ↦ ω.down t - ω.down s)
            ((transportedFin1Law ν) (t - s) : Measure (Fin 1 → ℝ))
            (P : Measure LiftedFin1PathSpace) := by
  rcases existsBaseFin1PathMeasure_of_transportedSemigroup (ν := ν) x with
    ⟨Pbase, hBaseStatIndep, hBaseLaw⟩
  let P : ProbabilityMeasure LiftedFin1PathSpace :=
    ProbabilityMeasure.map Pbase measurable_up.aemeasurable
  refine ⟨P, ?_, ?_⟩
  · -- Proof comment: the ULift pushforward preserves independent increments of the base
    -- coordinate process.
    simpa [P] using liftedFin1Path_hasIndepIncrements Pbase hBaseStatIndep.1
  · intro s t hst
    -- Proof comment: the same ULift pushforward also preserves the law of each single increment.
    simpa [P] using liftedFin1Path_increment_hasLaw Pbase (hBaseLaw hst)

/-- Corollary 21.25: after transporting the Chapter 14 canonical path-space realization from
`Fin 1 → ℝ` back to `ℝ`, the coordinate process has the prescribed increment laws and stationary
independent increments under every initial law. -/
theorem exists_cadlagMarkovRealization_of_continuousConvolutionSemigroup
    (ν : NNReal → ProbabilityMeasure ℝ) [IsContinuousConvolutionSemigroup ν] :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ X : NNReal → Ω → ℝ,
      ∃ P : ℝ → ProbabilityMeasure Ω, ∃ pathKernel : Kernel ℝ (NNReal → ℝ),
        IsFellerProcessRealization (translatedConvolutionKernel ν) P X pathKernel ∧
          (∀ x : ℝ, ∀ ⦃s t : NNReal⦄, s ≤ t →
            HasLaw (fun ω ↦ X t ω - X s ω) (ν (t - s) : Measure ℝ) (P x : Measure Ω)) ∧
          ∀ x : ℝ, HasStationaryIndependentIncrements X (P x : Measure Ω) := by
  let Ω' : Type u := LiftedFin1PathSpace
  let X : NNReal → Ω' → ℝ := realCoordinateProcess
  let P : ℝ → ProbabilityMeasure Ω' := fun x ↦
    Classical.choose <|
      exists_pathMeasure_of_transportedFin1ConvolutionSemigroup
        (ν := ν) (fin1RealMeasEquiv.symm x)
  let pathKernel : Kernel ℝ (NNReal → ℝ) :=
    Kernel.deterministic (fun x : ℝ ↦ fun _ : NNReal ↦ x) measurable_constRealPath
  have hVecPackage :
      ∀ x : ℝ,
        HasIndepIncrements
          (fun t ↦ fun ω : Ω' ↦ ω.down t)
          (P x : Measure Ω') ∧
          ∀ ⦃s t : NNReal⦄, s ≤ t →
            HasLaw (fun ω : Ω' ↦ ω.down t - ω.down s)
              ((transportedFin1Law ν) (t - s) : Measure (Fin 1 → ℝ))
              (P x : Measure Ω') := by
    intro x
    simpa [P, Ω'] using
      Classical.choose_spec
        (exists_pathMeasure_of_transportedFin1ConvolutionSemigroup
          (ν := ν) (fin1RealMeasEquiv.symm x))
  have hIncReal :
      ∀ x : ℝ, ∀ ⦃s t : NNReal⦄, s ≤ t →
        HasLaw (fun ω ↦ X t ω - X s ω) (ν (t - s) : Measure ℝ) (P x : Measure Ω') := by
    intro x s t hst
    rcases hVecPackage x with ⟨_, hIncVec⟩
    have hCoordLaw :
        HasLaw fin1RealMeasEquiv (ν (t - s) : Measure ℝ)
          ((transportedFin1Law ν (t - s)) : Measure (Fin 1 → ℝ)) := by
      -- Proof comment: pushing the transported vector law back through the measurable equivalence
      -- cancels the original transport from `ℝ` to `Fin 1 → ℝ`.
      refine ⟨fin1RealMeasEquiv.measurable.aemeasurable, ?_⟩
      simpa [transportedFin1Law, ProbabilityMeasure.map] using
        congrArg (fun ρ : ProbabilityMeasure ℝ ↦ (ρ : Measure ℝ))
          (mapBackTransportedFin1Law (μ := ν (t - s)))
    have hCompLaw :
        HasLaw
          (fun ω : Ω' ↦ fin1RealMeasEquiv (ω.down t - ω.down s))
          (ν (t - s) : Measure ℝ)
          (P x : Measure Ω') := by
      -- Proof comment: compose the vector increment law with the scalar coordinate equivalence
      -- before rewriting it to the chosen process `X`.
      simpa [Function.comp] using HasLaw.comp hCoordLaw (hIncVec hst)
    have hEq :
        (fun ω ↦ X t ω - X s ω)
          =ᵐ[(P x : Measure Ω')]
        (fun ω : Ω' ↦ fin1RealMeasEquiv (ω.down t - ω.down s)) := by
      exact Filter.EventuallyEq.of_eq <| by
        funext ω
        simpa [X, fin1RealMeasEquiv] using (realCoordinateProcess_sub_eq s t ω).symm
    exact hCompLaw.congr hEq
  refine ⟨Ω', inferInstance, X, P, pathKernel, ⟨trivial⟩, ?_, ?_⟩
  · intro x s t hst
    exact hIncReal x hst
  · intro x
    rcases hVecPackage x with ⟨hVecIndep, _⟩
    have hRealIndep : HasIndepIncrements X (P x : Measure Ω') := by
      -- Proof comment: apply the unique scalar coordinate to each vector-valued increment.
      simpa [X, realCoordinateProcess] using
        hVecIndep.map fin1RealEquiv.toContinuousLinearMap
    have hRealStat : HasStationaryIncrementLaws X (P x : Measure Ω') := by
      intro r s t
      -- Proof comment: both shifted increments have the same law `ν s`, hence they are
      -- identically distributed.
      have hleft_le : t + r ≤ (s + t) + r := by
        have hbase : t ≤ t + s := le_add_of_nonneg_right (show 0 ≤ s from bot_le)
        simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hbase r
      have hright_le : r ≤ s + r := by
        have hbase : r ≤ r + s := le_add_of_nonneg_right (show 0 ≤ s from bot_le)
        simpa [add_assoc, add_left_comm, add_comm] using hbase
      have hleft_le_coe : r + t ≤ r + (s + t) := by
        have hbase : t ≤ s + t := le_add_of_nonneg_left (show 0 ≤ s from bot_le)
        simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left hbase r
      have hright_le_coe : r ≤ r + s := by
        exact le_add_of_nonneg_right (show 0 ≤ s from bot_le)
      have hleftLag : (r + (s + t)) - (r + t) = s := by
        refine (tsub_eq_iff_eq_add_of_le hleft_le_coe).2 ?_
        simp [add_assoc, add_left_comm, add_comm]
      have hrightLag : (r + s) - r = s := by
        refine (tsub_eq_iff_eq_add_of_le hright_le_coe).2 ?_
        simp [add_assoc, add_left_comm, add_comm]
      have hLeft :
          HasLaw
            (fun ω ↦ X ((s + t) + r) ω - X (t + r) ω)
            (ν s : Measure ℝ)
            (P x : Measure Ω') := by
        -- Proof comment: rewrite the lag of the shifted interval explicitly to `s`.
        simpa [hleftLag, add_assoc, add_left_comm, add_comm] using
          (hIncReal x (s := t + r) (t := (s + t) + r) hleft_le)
      have hRight :
          HasLaw
            (fun ω ↦ X (s + r) ω - X r ω)
            (ν s : Measure ℝ)
            (P x : Measure Ω') := by
        -- Proof comment: the translated interval `[r, s + r]` has the same lag `s`.
        simpa [hrightLag, add_assoc, add_left_comm, add_comm] using
          (hIncReal x (s := r) (t := s + r) hright_le)
      exact hLeft.identDistrib hRight
    exact ⟨hRealIndep, hRealStat⟩

end ProbabilityTheory
