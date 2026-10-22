/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped MeasureTheory

universe u

variable {Ω : Type u}

-- Proof sketch: the Carathéodory-measurable sets of an outer measure are exactly the measurable
-- sets of the measurable space `μ.caratheodory`, and measurable sets of any measurable space form
-- an algebra of sets by closure under `univ`, complements, and finite unions.
/-- Lemma 1.50: The family `𝓜(μ*)` of Carathéodory-measurable sets for an outer measure `μ*`
is an algebra of sets. -/
theorem outerMeasure_caratheodory_isSetAlgebra (μ : OuterMeasure Ω) :
    IsSetAlgebra {s : Set Ω | MeasurableSet[μ.caratheodory] s} := by
  refine {
    empty_mem := ?_,
    compl_mem := ?_,
    union_mem := ?_ }
  · -- The empty set is measurable in every measurable space, hence for `μ.caratheodory`.
    exact (@MeasurableSet.empty Ω μ.caratheodory)
  · -- Carathéodory-measurable sets are closed under complements.
    intro s hs
    simpa using (@MeasurableSet.compl Ω s μ.caratheodory hs)
  · -- Carathéodory-measurable sets are also closed under binary unions.
    intro s t hs ht
    simpa using (@MeasurableSet.union Ω μ.caratheodory s t hs ht)
