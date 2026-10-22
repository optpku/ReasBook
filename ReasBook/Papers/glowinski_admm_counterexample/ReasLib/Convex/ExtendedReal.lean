/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import Mathlib.Data.EReal.Basic

@[expose] public section

namespace ConsensusADMM

/-- The pointwise lift of a real-valued objective to the extended reals. -/
def ofReal {E : Type u} (f : E → ℝ) : E → EReal :=
  fun x ↦ f x

/-- Evaluating the extended-real lift is real coercion. -/
theorem ofReal_apply {E : Type u} (f : E → ℝ) (x : E) :
    ofReal f x = (f x : EReal) := by
  -- Unfolding the pointwise lift exposes the same canonical coercion.
  rfl

/-- The extended-real indicator of a feasible set, equal to zero on the set
and `⊤` away from it. -/
noncomputable def extendedIndicator {E : Type u} (X : Set E) : E → EReal :=
  fun x ↦ @ite EReal (x ∈ X) (Classical.propDecidable _) 0 ⊤

/-- The extended indicator vanishes at every member of the feasible set. -/
theorem extendedIndicator_of_mem {E : Type u} {X : Set E} {x : E} (hx : x ∈ X) :
    extendedIndicator X x = 0 := by
  -- Membership selects the zero branch of the defining conditional.
  simp only [extendedIndicator, if_pos hx]

/-- The extended indicator is infinite away from the feasible set. -/
theorem extendedIndicator_of_not_mem {E : Type u} {X : Set E} {x : E} (hx : x ∉ X) :
    extendedIndicator X x = ⊤ := by
  -- Nonmembership selects the infinite branch of the defining conditional.
  simp only [extendedIndicator, if_neg hx]

end ConsensusADMM
