/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Kernel.IonescuTulcea.Traj

open Finset MeasureTheory ProbabilityTheory Preorder
open ProbabilityTheory.Kernel
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace FiniteDimensionalKernelLocal

section

variable {I : Type u} [Preorder I]
variable {E : Type v} [MeasurableSpace E]

/-- The projection of a path in `I → E` to the finite chain of times encoded by `j`. -/
def finiteCoordinateProjection {n : ℕ} (j : Π _ : Finset.Iic n, I) :
    (I → E) → Π _ : Finset.Iic n, E :=
  fun ω k ↦ ω (j k)

/-- The projection to a finite chain of coordinates is measurable. -/
theorem measurable_finiteCoordinateProjection {n : ℕ} (j : Π _ : Finset.Iic n, I) :
    Measurable (finiteCoordinateProjection j : (I → E) → Π _ : Finset.Iic n, E) := by
  -- Proof comment: each finite coordinate is just evaluation on the product path space.
  refine measurable_pi_lambda _ ?_
  intro k
  exact measurable_pi_apply (j k)

private def historyHead {n : ℕ} : (Π _ : Finset.Iic n, E) → E :=
  fun x ↦ x ⟨0, mem_Iic.2 (Nat.zero_le n)⟩

private theorem measurable_historyHead {n : ℕ} :
    Measurable (historyHead : (Π _ : Finset.Iic n, E) → E) := by
  -- Proof comment: the head of the history tuple is a single coordinate projection.
  simpa [historyHead] using
    measurable_pi_apply ((⟨0, mem_Iic.2 (Nat.zero_le n)⟩ : Finset.Iic n))

private def historyLast {n : ℕ} : (Π _ : Finset.Iic n, E) → E :=
  fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩

private theorem measurable_historyLast {n : ℕ} :
    Measurable (historyLast : (Π _ : Finset.Iic n, E) → E) := by
  -- Proof comment: the terminal history state is again a coordinate projection.
  simpa [historyLast] using
    measurable_pi_apply ((⟨n, mem_Iic.2 le_rfl⟩ : Finset.Iic n))

private def initialHistory : E → Π _ : Finset.Iic 0, E :=
  fun x _ ↦ x

private theorem measurable_initialHistory :
    Measurable (initialHistory : E → Π _ : Finset.Iic 0, E) := by
  -- Proof comment: on the singleton index type, the initial history map is coordinatewise `id`.
  refine measurable_pi_lambda _ ?_
  intro i
  simpa [initialHistory] using measurable_id

private noncomputable def consistentFamilyHistoryKernels
    (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) :
    (m : ℕ) → Kernel (Π _ : Finset.Iic m, E) E :=
  fun m ↦
    if hm : m < n then
      Kernel.comap
        (κ (hj (show (⟨m, mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic n) <
            ⟨m + 1, mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ from Nat.lt_succ_self m)))
        historyLast measurable_historyLast
    else
      Kernel.deterministic historyHead measurable_historyHead

private noncomputable def consistentFamilyHistoryTraj {n : ℕ}
    (κhist : (m : ℕ) → Kernel (Π _ : Finset.Iic m, E) E) :
    Kernel (Π _ : Finset.Iic 0, E) (Π _ : Finset.Iic n, E) :=
  ((@partialTraj (fun _ : ℕ ↦ E) _ κhist 0 n) :
    Kernel (Π _ : Finset.Iic 0, E) (Π _ : Finset.Iic n, E))

/-- The finite-dimensional kernel attached to the ordered chain of kernels picked out by `j`,
viewed as a stochastic kernel in the initial state. This is the owner construction over
`Kernel.partialTraj`; the measure-valued finite-dimensional laws are obtained from it by
composition with an initial law. -/
noncomputable def consistentFamilyFiniteDimensionalKernel
    (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) :
    Kernel E (Π _ : Finset.Iic n, E) :=
  consistentFamilyHistoryTraj (consistentFamilyHistoryKernels κ j hj) ∘ₖ
    Kernel.deterministic initialHistory measurable_initialHistory

/-- The finite-dimensional law attached to an initial measure `μ` and the ordered chain of kernels
picked out by `j`. This is the bridge/view API obtained from
`consistentFamilyFiniteDimensionalKernel` by composing with the initial law. -/
noncomputable def consistentFamilyFiniteDimensionalMeasure
    (μ : Measure E) (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) :
    Measure (Π _ : Finset.Iic n, E) :=
  consistentFamilyFiniteDimensionalKernel κ j hj ∘ₘ μ

/-- At level `n = 0`, the finite-dimensional law is just the initial law viewed on the
one-point-history space. -/
theorem consistentFamilyFiniteDimensionalMeasure_zero
    (μ : Measure E) (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (j : Π _ : Finset.Iic 0, I) (hj : StrictMono j) :
    consistentFamilyFiniteDimensionalMeasure μ κ j hj =
      μ.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ E)).symm := by
  have hinitial :
      initialHistory = (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ E)).symm := by
    funext x i
    simp [initialHistory]
  -- Proof comment: `partialTraj ... 0 0` is the identity kernel, so only the initial-history
  -- pushforward remains.
  rw [consistentFamilyFiniteDimensionalMeasure, consistentFamilyFiniteDimensionalKernel,
    ← Measure.comp_assoc]
  rw [consistentFamilyHistoryTraj, ProbabilityTheory.Kernel.partialTraj_self, Measure.id_comp]
  rw [Measure.deterministic_comp_eq_map]
  rw [hinitial]

/-- Evaluating the finite-dimensional kernel at `x` recovers the finite-dimensional law with
initial distribution `δ_x`. -/
theorem consistentFamilyFiniteDimensionalKernel_apply
    (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E) (x : E) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) :
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

/-- The finite-dimensional kernel attached to an ordered chain of Markov kernels is itself
Markov. -/
theorem consistentFamilyFiniteDimensionalKernel_isMarkov
    (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (κ hst)) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) :
    IsMarkovKernel (consistentFamilyFiniteDimensionalKernel κ j hj) := by
  let κhist := consistentFamilyHistoryKernels κ j hj
  have hκhist : ∀ m, IsMarkovKernel (κhist m) := by
    intro m
    dsimp [κhist, consistentFamilyHistoryKernels]
    split_ifs with hm
    · let hstep :
          j (⟨m, mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic n) <
            j ⟨m + 1, mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ := by
          exact hj (show
            (⟨m, mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic n) <
              ⟨m + 1, mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ from Nat.lt_succ_self m)
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
      Kernel (Π _ : Finset.Iic 0, E) (Π _ : Finset.Iic n, E) :=
    ((@partialTraj (fun _ : ℕ ↦ E) _ κhist 0 n) :
      Kernel (Π _ : Finset.Iic 0, E) (Π _ : Finset.Iic n, E))
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

/-- Evaluating a finite-dimensional Markov kernel on a measurable set is measurable in the initial
state. -/
theorem measurable_consistentFamilyFiniteDimensionalKernel_apply
    (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (κ hst)) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j)
    {s : Set (Π _ : Finset.Iic n, E)} (hs : MeasurableSet s) :
    Measurable (fun x ↦ consistentFamilyFiniteDimensionalKernel κ j hj x s) := by
  have hKernelMarkov :
      IsMarkovKernel (consistentFamilyFiniteDimensionalKernel κ j hj) :=
    consistentFamilyFiniteDimensionalKernel_isMarkov κ hMarkov j hj
  letI : IsMarkovKernel (consistentFamilyFiniteDimensionalKernel κ j hj) := hKernelMarkov
  -- Proof comment: this is the owner measurability of evaluations of a Markov kernel.
  simpa using Kernel.measurable_coe (consistentFamilyFiniteDimensionalKernel κ j hj) hs

end

end FiniteDimensionalKernelLocal
