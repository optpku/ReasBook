/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.ScaledProximityOperator

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: the scaled proximity operator is the ordinary proximity operator of `γ • f`; a
-- proximal point of a proper function cannot have value `⊤`, since the proximal objective would
-- then be `⊤` and hence could not attain the finite minimum value guaranteed by properness.
/-- For `f ∈ Γ₀(H)`, every scaled proximal point belongs to the effective domain of `f`. -/
theorem scaledProximityOperator_mem_effectiveDomain_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) (γ : PosReal) :
    Prox[γ, f, hf] x ∈ effectiveDomain f := sorry

-- Proof sketch: apply Proposition 12.26 to the proximal points at parameters `γ` and `μ`, add the
-- two variational inequalities, use finiteness of the proximal values to pass to `toReal`, and
-- rearrange to obtain monotonicity in the parameter.
/-- Proposition 12.27 (1): for `f ∈ Γ₀(H)` and `x ∈ H`, the proximal value function
`γ ↦ f (Prox_{γ f} x)` is decreasing on `ℝ_{++}`. -/
theorem antitone_proxValue_along_parameter_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    Antitone (fun γ : PosReal ↦ (f (Prox[γ, f, hf] x) : EReal).toReal) := sorry

-- Proof sketch: use the pointwise estimate from clause (3) to bound every value of
-- `γ ↦ f (Prox_{γ f} x)` by `f x`, then apply `sSup_le`.
/-- Proposition 12.27 (2): for `f ∈ Γ₀(H)` and `x ∈ H`, the supremum of the proximal values
`f (Prox_{γ f} x)` over `γ ∈ ℝ_{++}` is bounded above by `f x`. -/
theorem sSup_proxValue_range_le_self_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    sSup (Set.range (fun γ : PosReal ↦ f.asEReal (Prox[γ, f, hf] x))) ≤
      f.asEReal x := sorry

-- Proof sketch: specialize the proximal-point variational inequality from Proposition 12.26 at
-- `y = x` for the scaled function `γ • f`, then rewrite the resulting inequality in the textbook
-- form.
/-- Proposition 12.27 (3): for `f ∈ Γ₀(H)`, `x ∈ H`, and `γ ∈ ℝ_{++}`, the proximal point
`Prox_{γ f} x` satisfies the estimate
`‖x - Prox_{γ f} x‖² + γ f (Prox_{γ f} x) ≤ γ f x`. -/
theorem sqDist_add_smul_proxValue_le_smul_self_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) (γ : PosReal) :
    (((‖x - Prox[γ, f, hf] x‖ ^ 2 : ℝ) : EReal) +
        (γ • f).asEReal (Prox[γ, f, hf] x)) ≤
      (γ • f).asEReal x := sorry

end ERealFunction
