/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open Filter Set
open scoped Topology

/-- Strict positivity on a compact frequency set persists in a common right
neighborhood of the parameter. Applied to the minors of `H - κ I`, this keeps
the same fixed `κ` throughout the continuation. -/
theorem strict_pos_right_continuation {X : Type} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (f : ℝ × X → ℝ) (hf : Continuous f)
    (L U : ℝ) (hLU : L < U) (hpos : ∀ x ∈ K, 0 < f (L, x)) :
    ∃ δ : ℝ, 0 < δ ∧ L + δ < U ∧
      ∀ γ ∈ Icc L (L + δ), ∀ x ∈ K, 0 < f (γ, x) := by
  have he : ∀ᶠ γ in 𝓝 L, ∀ x ∈ K, 0 < f (γ, x) := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    exact (isOpen_lt continuous_const hf).mem_nhds (hpos x hx)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
  let δ := min (ε / 2) ((U - L) / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨δ, hδ, ?_, ?_⟩
  · have hδU : δ ≤ (U - L) / 2 := min_le_right _ _
    linarith
  · intro γ hγ x hx
    apply he _ x hx
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hγ.1)]
    have hγδ : γ - L ≤ δ := by linarith [hγ.2]
    exact hγδ.trans_lt hδε

end ADMM.UnitCircle.LowerCertificate
