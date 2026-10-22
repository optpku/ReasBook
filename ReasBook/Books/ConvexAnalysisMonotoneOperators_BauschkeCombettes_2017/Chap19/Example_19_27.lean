/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Proposition_19_25

open Set
open scoped InnerProductSpace Pointwise

noncomputable section

universe u

namespace ERealFunction

attribute [local instance] Classical.propDecidable

section TranslatedConeDuality

variable {H : Type u}

section Basic

variable [AddCommGroup H]

/-- Example 19.27: the perturbation attached to minimizing `f` over the translated cone `z + K`,
implemented as the canonical inequality-constraint perturbation for the translation map
`x ↦ x - z`. -/
abbrev translatedConePerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (z : H) (K : Set H) :
    H × H → Set.Ioi (⊥ : EReal) :=
  inequalityConstraintPerturbation f (fun x ↦ x - z) K

-- Proof sketch: unfold `translatedConePerturbation`, rewrite
-- `x - z + y ∈ K ↔ x ∈ ({z - y} : Set H) + K`, and then simplify the indicator term via the
-- canonical owner `inequalityConstraintPerturbation`.
/-- Evaluating `translatedConePerturbation f z K` gives the piecewise formula from
Example 19.27. -/
@[simp] theorem translatedConePerturbation_apply
    (f : H → Set.Ioi (⊥ : EReal)) (z : H) (K : Set H) (x y : H) :
    (translatedConePerturbation f z K (x, y) : EReal) =
      if x ∈ ({z - y} : Set H) + K then (f x : EReal) else ⊤ := sorry

-- Proof sketch: evaluate the perturbation at `(x, 0)` and rewrite the membership condition
-- `x ∈ ({z} : Set H) + K`.
/-- The primal objective attached to `translatedConePerturbation f z K` is `f` on the translated
cone `z + K` and `+∞` outside it. -/
theorem perturbationPrimalObjective_translatedConePerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (z : H) (K : Set H) :
    perturbationPrimalObjective (translatedConePerturbation f z K) =
      fun x : H ↦ if x ∈ ({z} : Set H) + K then (f x : EReal) else ⊤ := sorry

end Basic

section Regularity

variable [NormedAddCommGroup H] [NormedSpace ℝ H]

-- Proof sketch: rewrite the translated-cone perturbation as the inequality-constraint
-- perturbation with `R x = x - z`, then apply Proposition 19.25 (1). The hypothesis
-- `z ∈ effectiveDomain f - K` is exactly the feasibility condition needed there.
/-- If `f ∈ Γ₀(H)`, if `K` is a closed convex cone, and if `z ∈ effectiveDomain f - K`, then the
translated-cone perturbation belongs to `Γ₀(H × H)`. -/
theorem translatedConePerturbation_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (z : H) (K : Set H)
    (hK_closed : IsClosed K) (hK_convex : Convex ℝ K) (hK_cone : IsCone K)
    (hz : z ∈ effectiveDomain f - K) :
    translatedConePerturbation f z K ∈ Γ₀(H × H) := sorry

end Regularity

section DualFormula

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: rewrite the perturbation as the special case of Proposition 19.25 with
-- `R x = x - z`, then simplify the resulting supremum formula into
-- `(f∗[hf]) (-u) + ⟪z, u⟫` on `Kᵒ⊖`.
/-- If `K` is a nonempty cone, then the dual objective attached to the translated-cone
perturbation is `f^*(-u) + ⟪z, u⟫` on the polar cone `Kᵒ⊖` and `+∞` outside it. -/
theorem perturbationDualObjective_translatedConePerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (z : H) (K : Set H) (hK_nonempty : K.Nonempty) (hK_cone : IsCone K) :
    perturbationDualObjective (translatedConePerturbation f z K) =
      fun u : H ↦
        if u ∈ Kᵒ⊖ then
          (f∗[hf] (-u) : EReal) + (⟪z, u⟫_ℝ : EReal)
        else
          ⊤ := sorry

-- Proof sketch: specialize Proposition 19.25 (4) to `R x = x - z`, then rewrite
-- `⟪x - z, u⟫ = ⟪R x, u⟫`.
/-- If `K` is a nonempty cone, then the Lagrangian of the translated-cone perturbation is the
piecewise function from Example 19.27. -/
theorem lagrangian_translatedConePerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (z : H) (K : Set H)
    (hK_nonempty : K.Nonempty) (hK_cone : IsCone K)
    (x u : H) :
    ℒ[translatedConePerturbation f z K] x u =
      if hx : x ∈ effectiveDomain f then
        if hu : u ∈ Kᵒ⊖ then
          (f x : EReal) + (⟪x - z, u⟫_ℝ : EReal)
        else
          ⊥
      else
        ⊤ := sorry

end DualFormula

section ParametricDuality

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: specialize Proposition 19.25 (5) to `R x = x - z`, then rewrite the constraint
-- `x - z ∈ K` as `x ∈ ({z} : Set H) + K` and the infimum condition as membership in
-- `Argmin (fun x ↦ f x + ⟪x, ū⟫)`.
/-- A pair `(x̄, ū)` is a saddle point of the translated-cone Lagrangian exactly when `x̄` lies in
`effectiveDomain f ∩ (z + K)`, `ū` lies in `Kᵒ⊖`, and `x̄` minimizes `x ↦ f x + ⟪x, ū⟫`. -/
theorem isSaddlePointOn_lagrangian_translatedConePerturbation_iff
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (z : H) (K : Set H)
    (hK_closed : IsClosed K) (hK_convex : Convex ℝ K) (hK_cone : IsCone K)
    (hz : z ∈ effectiveDomain f - K)
    (xbar ubar : H) :
    IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set H)
        (ℒ[translatedConePerturbation f z K]) xbar ubar ↔
      xbar ∈ effectiveDomain f ∧
        xbar ∈ ({z} : Set H) + K ∧
        ubar ∈ Kᵒ⊖ ∧
        xbar ∈ Argmin (fun x : H ↦ (f x : EReal) + (⟪x, ubar⟫_ℝ : EReal)) := sorry

-- Proof sketch: Proposition 19.25 (6) yields `⟪x̄ - z, ū⟫ = 0` and primal optimality; expand the
-- inner product and rearrange to obtain `⟪x̄, ū⟫ = ⟪z, ū⟫`.
/-- Any saddle point of the translated-cone Lagrangian satisfies
`⟪x̄, ū⟫ = ⟪z, ū⟫`, and its first component is a primal solution. -/
theorem
    inner_eq_inner_and_mem_argmin_perturbationPrimalObjective_of_isSaddlePointOn_lagrangian_translatedConePerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (z : H) (K : Set H)
    (hK_closed : IsClosed K) (hK_convex : Convex ℝ K) (hK_cone : IsCone K)
    (hz : z ∈ effectiveDomain f - K)
    {xbar ubar : H}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set H)
        (ℒ[translatedConePerturbation f z K]) xbar ubar) :
    ⟪xbar, ubar⟫_ℝ = ⟪z, ubar⟫_ℝ ∧
      xbar ∈ Argmin (perturbationPrimalObjective (translatedConePerturbation f z K)) := sorry

end ParametricDuality

end TranslatedConeDuality

end ERealFunction
