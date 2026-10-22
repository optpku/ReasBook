/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Analysis/Calculus/LocalCutoff/GraphJetTransform/SectionContraction.lean
-/

module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Contracting

public section

open scoped NNReal

universe u v

namespace BoundedContinuousFunction

/-!
This module packages the sup-metric contraction step used for the highest
coefficient section in a finite-order graph-jet induction.  The map itself is
left abstract: callers only have to prove its pointwise estimate.
-/

/-- A pointwise contraction estimate on bounded continuous functions upgrades to
the canonical `ContractingWith` structure for the sup metric. -/
theorem contractingWith_of_dist_apply_le_mul
    {α : Type u} {β : Type v} [TopologicalSpace α] [Nonempty α]
    [NormedAddCommGroup β] [CompleteSpace β]
    {K : ℝ≥0} {T : (α →ᵇ β) → (α →ᵇ β)}
    (hK : K < 1)
    (hT : ∀ f g x, dist (T f x) (T g x) ≤ K * dist f g) :
    ContractingWith K T := by
  refine ⟨hK, LipschitzWith.of_dist_le_mul fun f g ↦ ?_⟩
  exact BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr (hT f g)

/-- A pointwise contraction on bounded continuous functions has a unique fixed
point, with the witness supplied by Mathlib's `ContractingWith` API. -/
theorem existsUnique_fixedPoint_of_dist_apply_le_mul
    {α : Type u} {β : Type v} [TopologicalSpace α] [Nonempty α]
    [NormedAddCommGroup β] [CompleteSpace β]
    {K : ℝ≥0} {T : (α →ᵇ β) → (α →ᵇ β)}
    (hK : K < 1)
    (hT : ∀ f g x, dist (T f x) (T g x) ≤ K * dist f g) :
    ∃! f, T f = f := by
  let hcontract : ContractingWith K T :=
    contractingWith_of_dist_apply_le_mul hK hT
  refine ⟨ContractingWith.fixedPoint T hcontract, hcontract.fixedPoint_isFixedPt, ?_⟩
  intro f hf
  exact hcontract.fixedPoint_unique hf

end BoundedContinuousFunction
