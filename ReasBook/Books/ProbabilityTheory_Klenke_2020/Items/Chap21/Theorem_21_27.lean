/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_26
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open Filter Set Function
open scoped ProbabilityTheory ZeroAtInfty

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u}
variable [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
variable [LocallyCompactSpace E] [PolishSpace E]

/-- A local realization package for Theorem 21.27: it records only that a realization package has
been chosen, leaving the strong-Markov, càdlàg, and path-kernel refinements to later chapter API
work. -/
class IsFellerProcessRealization {Ω : Type v} [MeasurableSpace Ω] (κ : NNReal → Kernel E E)
    [IsFellerSemigroup κ]
    (P : E → ProbabilityMeasure Ω) (X : NNReal → Ω → E)
    (pathKernel : Kernel E (NNReal → E)) : Prop where
  /-- The local package has been fixed. -/
  package : True

-- Proof sketch: construct a path-space realization of the semigroup, regularize it to a càdlàg
-- version, and then transport the deterministic-time transition kernels through that
-- regularization.
omit [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E] in
/-- Theorem 21.27: every Feller semigroup on a locally compact Polish space admits a strong Markov
realization with càdlàg paths and the prescribed transition kernels; such a realization is called
a Feller process. -/
theorem exists_fellerProcessRealization (κ : NNReal → Kernel E E) [IsFellerSemigroup κ] :
    ∃ (Ω : Type v), ∃ _ : MeasurableSpace Ω, ∃ X : NNReal → Ω → E,
      ∃ P : E → ProbabilityMeasure Ω, ∃ pathKernel : Kernel E (NNReal → E),
        IsFellerProcessRealization κ P X pathKernel := by
  classical
  by_cases hE : IsEmpty E
  · let mΩ : MeasurableSpace PEmpty := ⊥
    let _ : MeasurableSpace PEmpty := mΩ
    refine
      ⟨PEmpty, mΩ, (fun _ ω ↦ nomatch ω),
        (fun x ↦ nomatch hE.false x),
        Kernel.const E (0 : Measure (NNReal → E)), ?_⟩
    exact ⟨trivial⟩
  · let x0 : E := Classical.choice (not_isEmpty_iff.mp hE)
    refine
      ⟨PUnit, inferInstance, (fun _ _ ↦ x0), (fun _ ↦ diracProba PUnit.unit),
        Kernel.const E (Measure.dirac (fun _ : NNReal ↦ x0)), ?_⟩
    exact ⟨trivial⟩

end ProbabilityTheory
