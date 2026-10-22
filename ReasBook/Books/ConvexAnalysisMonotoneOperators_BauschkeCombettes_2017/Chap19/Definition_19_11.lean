/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_33

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section ParametricDuality

variable {H : Type u} {K : Type v}

section Primal

variable [Zero K]

/-- The objective function of the primal perturbation problem associated with `F`. -/
def perturbationPrimalObjective (F : H × K → Set.Ioi (⊥ : EReal)) : H → EReal :=
  fun x ↦ (F (x, 0) : EReal)

/-- Evaluating the primal objective gives the value `F (x, 0)`. -/
@[simp] theorem perturbationPrimalObjective_apply (F : H × K → Set.Ioi (⊥ : EReal)) (x : H) :
    perturbationPrimalObjective F x = (F (x, 0) : EReal) := rfl

end Primal

/- Definition 19.11: the value function associated with a perturbation function `F` is the
canonical infimal postcomposition `Prod.snd ▷ F`. -/

/-- Evaluating the canonical value-function owner `Prod.snd ▷ F` at `y` gives the infimum of the
slice `x ↦ F (x, y)`, written in the canonical `iInf` form from the Chapter 13 partial-infimum
API. -/
@[simp] theorem infimalPostcomposition_snd_apply (F : H × K → Set.Ioi (⊥ : EReal)) (y : K) :
    (Prod.snd ▷ F) y = ⨅ x : H, (F (x, y) : EReal) := by
  change
    sInf ((fun p : H × K ↦ (F p : EReal)) '' (Prod.snd ⁻¹' ({y} : Set K))) =
      ⨅ x : H, (F (x, y) : EReal)
  rw [show
      (fun p : H × K ↦ (F p : EReal)) '' (Prod.snd ⁻¹' ({y} : Set K)) =
        Set.range (fun x : H ↦ (F (x, y) : EReal)) by
      ext z
      constructor
      · rintro ⟨⟨x, y'⟩, hy', rfl⟩
        refine ⟨x, ?_⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy'
        simp [hy']
      · rintro ⟨x, rfl⟩
        exact ⟨(x, y), by simp, rfl⟩]
  exact sInf_range

-- Proof sketch: `(Prod.snd ▷ F) y` is the infimum of the range of the slice `x ↦ F (x, y)`,
-- so it is bounded above by every value attained by that slice.
/-- The value function `Prod.snd ▷ F` is a lower bound for every value on the slice
`x ↦ F (x, y)`. -/
theorem infimalPostcomposition_snd_le_slice
    (F : H × K → Set.Ioi (⊥ : EReal)) (x : H) (y : K) :
    (Prod.snd ▷ F) y ≤ (F (x, y) : EReal) := by
  rw [infimalPostcomposition_snd_apply]
  exact iInf_le _ x

section Dual

variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The objective function of the dual perturbation problem associated with `F`, written in the
explicit supremum form of `F^*(0, v)`. -/
noncomputable def perturbationDualObjective (F : H × K → Set.Ioi (⊥ : EReal)) : K → EReal :=
  fun v ↦ ⨆ p : H × K, ((⟪p.2, v⟫_ℝ : ℝ) : EReal) - (F p : EReal)

/-- Evaluating the dual objective gives the explicit `F^*(0, v)` supremum formula. -/
@[simp] theorem perturbationDualObjective_apply (F : H × K → Set.Ioi (⊥ : EReal)) (v : K) :
    perturbationDualObjective F v =
      ⨆ p : H × K, ((⟪p.2, v⟫_ℝ : ℝ) : EReal) - (F p : EReal) := rfl

end Dual

end ParametricDuality

end ERealFunction
