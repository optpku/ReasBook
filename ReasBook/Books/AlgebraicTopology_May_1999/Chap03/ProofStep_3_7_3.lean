/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {E : Type u} {B : Type v} {X : Type w}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]

namespace IsFundamentalNeighborhood

variable {p : E → B} {f : C(X, B)} {g : X → E} {x : X} {V : Set B}

/-- ProofStep 3.7.3: a set-theoretic lift is continuous at `x` once, on some neighborhood of `x`,
it stays in a single inverse-image sheet over a fundamental neighborhood of `f x`. -/
-- Proof sketch: on the neighborhood `U`, the chosen sheet homeomorphism identifies the restricted
-- lift with the map `y ↦ (f y, e₀)` into `V × p⁻¹' {f x}`. This map is continuous, so composing
-- with the inverse homeomorphism gives continuity of the restricted lift, hence continuity of `g`
-- at `x`.
theorem continuousAt_of_locally_landing_in_inverseImageSheet
    {H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({f x} : Set B))}
    (hH : ∀ e, (H e).1.1 = p e)
    (hg : p ∘ g = f)
    {U : Set X} (hxU : x ∈ U) (hU : IsOpen U) (hgU : U ⊆ g ⁻¹' (p ⁻¹' V))
    (e₀ : p ⁻¹' ({f x} : Set B))
    (hsheet : ∀ y : U, (H ⟨g y.1, hgU y.2⟩).2 = e₀) :
    ContinuousAt g x := by
  have hbase : ∀ y : U, f y.1 ∈ V := by
    intro y
    have hyV : p (g y.1) ∈ V := hgU y.2
    rw [show p (g y.1) = f y.1 by simpa using congrFun hg y.1] at hyV
    exact hyV
  let gU : U → E := fun y ↦ H.symm ((⟨f y.1, hbase y⟩ : V), e₀)
  have hgU_eq : U.restrict g = gU := by
    funext y
    have hy : (⟨g y.1, hgU y.2⟩ : p ⁻¹' V) = H.symm ((⟨f y.1, hbase y⟩ : V), e₀) := by
      apply H.injective
      apply Prod.ext
      · apply Subtype.ext
        simpa using (hH ⟨g y.1, hgU y.2⟩).trans (congrFun hg y.1)
      · exact (hsheet y).trans <| by
          exact (congrArg Prod.snd (H.right_inv ((⟨f y.1, hbase y⟩ : V), e₀))).symm
    change g y.1 = gU y
    simpa [gU] using congrArg Subtype.val hy
  have hgU_cont : Continuous gU := by
    have hfirst : Continuous (fun y : U ↦ (⟨f y.1, hbase y⟩ : V)) :=
      (f.continuous.comp continuous_subtype_val).subtype_mk hbase
    have hsymm : Continuous H.symm := H.symm.continuous
    exact continuous_subtype_val.comp <|
      hsymm.comp (hfirst.prodMk continuous_const)
  have hcont_restrict : ContinuousAt (U.restrict g) ⟨x, hxU⟩ := by
    simpa [hgU_eq] using hgU_cont.continuousAt
  have hwithin : ContinuousWithinAt g U x :=
    (continuousWithinAt_iff_continuousAt_restrict g hxU).2 hcont_restrict
  exact hwithin.continuousAt (hU.mem_nhds hxU)

end IsFundamentalNeighborhood
