/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

/-
Remark 14.5: each coordinate projection from the product space `∀ i, Ω i` is continuous in the
canonical product topology.
-/
recall continuous_apply

/- A map into a product space is continuous exactly when all of its coordinate maps are
continuous. -/
recall continuous_pi_iff

universe u v

variable {I : Type u} {Ω : I → Type v} [∀ i, TopologicalSpace (Ω i)]

/-- Remark 14.5: if `τ` makes every coordinate map `fun x ↦ x i` continuous, then `τ` is finer
than the canonical product topology `Pi.topologicalSpace`. Equivalently, the latter is the
coarsest topology with continuous coordinate projections. -/
theorem le_pi_topology_of_continuous_coordinate_maps
    {τ : TopologicalSpace (∀ i, Ω i)}
    (hτ : ∀ i, Continuous[τ, inferInstance] (fun x : ∀ i, Ω i ↦ x i)) :
    τ ≤ Pi.topologicalSpace := by
  simpa using (continuous_pi_iff.2 hτ : Continuous[τ, Pi.topologicalSpace] id).coinduced_le
