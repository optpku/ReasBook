/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open Set

universe u v w

/- Definition 8.25: A transition kernel from `(Ω₁, 𝓐₁)` to `(Ω₂, 𝓐₂)` is the canonical
measurable family of measures `ProbabilityTheory.Kernel Ω₁ Ω₂`. -/
recall ProbabilityTheory.Kernel

/- Mathlib also provides the stronger uniformly bounded notion
`ProbabilityTheory.IsFiniteKernel`. -/
recall ProbabilityTheory.IsFiniteKernel

/- Mathlib's `ProbabilityTheory.IsSFiniteKernel` is the distinct s-finite kernel notion; it is not
the rowwise σ-finiteness from Definition 8.25. -/
recall ProbabilityTheory.IsSFiniteKernel

namespace ProbabilityTheory

variable {Ω₁ : Type u} {Ω₂ : Type v} {Ω₃ : Type w}
variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]

/-- Definition 8.25: a finite transition kernel is a kernel whose fibers are finite measures. This
is a rowwise finiteness condition, distinct from the stronger uniformly bounded class
`ProbabilityTheory.IsFiniteKernel`. -/
def IsFiniteTransitionKernel (κ : Kernel Ω₁ Ω₂) : Prop :=
  ∀ ω₁, IsFiniteMeasure (κ ω₁)

theorem IsFiniteTransitionKernel.isFiniteMeasure {κ : Kernel Ω₁ Ω₂}
    (hκ : IsFiniteTransitionKernel κ) (ω₁ : Ω₁) : IsFiniteMeasure (κ ω₁) :=
  hκ ω₁

theorem isFiniteTransitionKernel_of_isFiniteKernel (κ : Kernel Ω₁ Ω₂) [IsFiniteKernel κ] :
    IsFiniteTransitionKernel κ :=
  fun _ ↦ inferInstance

/-- Definition 8.25: a σ-finite transition kernel is a kernel whose fibers are σ-finite measures.
This is a rowwise σ-finiteness condition, distinct from mathlib's s-finite kernel class
`ProbabilityTheory.IsSFiniteKernel`. -/
def IsSigmaFiniteTransitionKernel (κ : Kernel Ω₁ Ω₂) : Prop :=
  ∀ ω₁, SigmaFinite (κ ω₁)

theorem IsSigmaFiniteTransitionKernel.sigmaFinite {κ : Kernel Ω₁ Ω₂}
    (hκ : IsSigmaFiniteTransitionKernel κ) (ω₁ : Ω₁) : SigmaFinite (κ ω₁) :=
  hκ ω₁

theorem isSigmaFiniteTransitionKernel_of_isFiniteTransitionKernel {κ : Kernel Ω₁ Ω₂}
    (hκ : IsFiniteTransitionKernel κ) : IsSigmaFiniteTransitionKernel κ :=
  fun ω₁ ↦ by
    let _ := hκ.isFiniteMeasure ω₁
    infer_instance

/-- Definition 8.25: a sub-Markov or substochastic kernel is a kernel whose fibers have total
mass at most `1`. -/
def IsSubMarkovKernel (κ : Kernel Ω₁ Ω₂) : Prop :=
  ∀ ω₁, κ ω₁ univ ≤ 1

theorem IsSubMarkovKernel.measure_univ_le_one {κ : Kernel Ω₁ Ω₂}
    (hκ : IsSubMarkovKernel κ) (ω₁ : Ω₁) : κ ω₁ univ ≤ 1 :=
  hκ ω₁

theorem IsSubMarkovKernel.isFiniteKernel {κ : Kernel Ω₁ Ω₂}
    (hκ : IsSubMarkovKernel κ) : IsFiniteKernel κ :=
  ⟨⟨1, ENNReal.one_lt_top, hκ⟩⟩

theorem IsSubMarkovKernel.isFiniteTransitionKernel {κ : Kernel Ω₁ Ω₂}
    (hκ : IsSubMarkovKernel κ) : IsFiniteTransitionKernel κ :=
  fun ω₁ ↦ ⟨lt_of_le_of_lt (hκ.measure_univ_le_one ω₁) ENNReal.one_lt_top⟩

theorem IsSubMarkovKernel.comp {κ : Kernel Ω₁ Ω₂} {η : Kernel Ω₂ Ω₃}
    (hη : IsSubMarkovKernel η) (hκ : IsSubMarkovKernel κ) :
    IsSubMarkovKernel (η ∘ₖ κ) := by
  intro ω₁
  rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  refine (lintegral_mono fun ω₂ ↦ hη.measure_univ_le_one ω₂).trans ?_
  simpa using hκ.measure_univ_le_one ω₁

theorem IsSubMarkovKernel.map {κ : Kernel Ω₁ Ω₂}
    (hκ : IsSubMarkovKernel κ) {f : Ω₂ → Ω₃} (hf : Measurable f) :
    IsSubMarkovKernel (κ.map f) := by
  intro ω₁
  rw [Kernel.map_apply' _ hf _ MeasurableSet.univ]
  simpa using hκ.measure_univ_le_one ω₁

theorem IsSubMarkovKernel.comap {κ : Kernel Ω₁ Ω₂}
    (hκ : IsSubMarkovKernel κ) {g : Ω₃ → Ω₁} (hg : Measurable g) :
    IsSubMarkovKernel (κ.comap g hg) := by
  intro ω₃
  simpa [Kernel.comap_apply'] using hκ.measure_univ_le_one (g ω₃)

theorem IsSubMarkovKernel.id_prod {κ : Kernel Ω₁ Ω₂}
    (hκ : IsSubMarkovKernel κ) : IsSubMarkovKernel (Kernel.id ×ₖ κ) := by
  letI : IsFiniteKernel κ := hκ.isFiniteKernel
  intro ω₁
  rw [Kernel.id_prod_apply' κ ω₁ MeasurableSet.univ]
  simpa using hκ.measure_univ_le_one ω₁

/- The textbook stochastic or Markov kernels are the canonical predicate
`ProbabilityTheory.IsMarkovKernel`. -/
recall ProbabilityTheory.IsMarkovKernel

theorem isSubMarkovKernel_of_isMarkovKernel (κ : Kernel Ω₁ Ω₂) [IsMarkovKernel κ] :
    IsSubMarkovKernel κ := by
  intro ω₁
  let hω : IsProbabilityMeasure (κ ω₁) := inferInstance
  exact le_of_eq hω.measure_univ

end ProbabilityTheory
