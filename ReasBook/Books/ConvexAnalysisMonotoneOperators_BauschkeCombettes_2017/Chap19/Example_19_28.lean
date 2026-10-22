/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Proposition_19_25

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set

namespace ERealFunction

open scoped InnerProductSpace Pointwise

attribute [local instance] Classical.propDecidable

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

section

variable (φ : ℝ → Set.Ioi (⊥ : EReal))

/-- The infimum `γ = inf φ(ℝ)` appearing in Example 19.28. -/
noncomputable def phiRangeInfimum : EReal :=
  sInf (Set.range fun t : ℝ ↦ (φ t : EReal))

/-- Expanding `phiRangeInfimum φ` yields the infimum of the range of `φ`. -/
@[simp] theorem phiRangeInfimum_def :
    phiRangeInfimum φ = sInf (Set.range fun t : ℝ ↦ (φ t : EReal)) := rfl

/-- The perturbation function `F` defined in equation (19.67) of Example 19.28, expressed as the
canonical inequality-constraint perturbation for `ξ ↦ φ(ξ₂)` and `R(ξ) = ‖ξ‖ - ξ₁`. -/
abbrev lorentzConstraintPerturbation : (ℝ × ℝ) × ℝ → Set.Ioi (⊥ : EReal) :=
  inequalityConstraintPerturbation (fun ξ ↦ φ ξ.2) (fun ξ ↦ ‖ξ‖ - ξ.1) (Set.Iic (0 : ℝ))

-- Proof sketch: unfold `lorentzConstraintPerturbation` through the canonical owner and simplify
-- the indicator branch on `Set.Iic 0`.
/-- Evaluating `lorentzConstraintPerturbation φ` gives the branch formula from (19.67). -/
@[simp] theorem lorentzConstraintPerturbation_apply (ξ : ℝ × ℝ) (y : ℝ) :
    (lorentzConstraintPerturbation φ (ξ, y) : EReal) =
      if ξ.1 - ‖ξ‖ ≥ y then (φ ξ.2 : EReal) else ⊤ := sorry

-- Proof sketch: `‖ξ‖ ≤ ξ.1` is equivalent to `ξ.2 = 0` and `0 ≤ ξ.1`, so the feasible set is
-- exactly the nonnegative horizontal axis.
/-- The Lorentz-type constraint `‖(ξ₁, ξ₂)‖ ≤ ξ₁` is equivalent to membership in
`ℝ₊ × {0}`. -/
theorem lorentz_feasible_iff (ξ : ℝ × ℝ) :
    ‖ξ‖ ≤ ξ.1 ↔ ξ ∈ Set.Ici (0 : ℝ) ×ˢ ({0} : Set ℝ) := sorry

-- Proof sketch: the polar cone of `ℝ₋ = Set.Iic 0` is `ℝ₊ = Set.Ici 0`.
/-- The polar cone of the nonpositive ray is the nonnegative ray. -/
theorem mem_polarCone_Iic_zero_iff_nonneg (v : ℝ) :
    v ∈ (Set.Iic (0 : ℝ))ᵒ⊖ ↔ 0 ≤ v := sorry

-- Proof sketch: specialize Proposition 19.25 (1) to the canonical owner underlying
-- `lorentzConstraintPerturbation φ`, namely the inequality-constraint perturbation with
-- `f(ξ₁, ξ₂) = φ(ξ₂)`, `R(ξ₁, ξ₂) = ‖(ξ₁, ξ₂)‖ - ξ₁`, and `K = ℝ₋`.
/-- Example 19.28 (1): clause (i). If `φ ∈ Γ₀(ℝ)` and `0 ∈ dom φ`, then the perturbation
function `F` from (19.67) belongs to `Γ₀(ℝ² × ℝ)`. -/
theorem lorentzConstraintPerturbation_mem_gammaZero
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ) :
    lorentzConstraintPerturbation φ ∈ Γ₀((ℝ × ℝ) × ℝ) := sorry

-- Proof sketch: specialize Proposition 19.25 (2), then rewrite the feasibility condition
-- `‖ξ‖ - ξ.1 ∈ Set.Iic 0` as `‖ξ‖ ≤ ξ.1`.
/-- Example 19.28 (2): clause (ii), first part. The primal objective is
`ξ ↦ φ(ξ₂)` on the feasible set `‖ξ‖ ≤ ξ₁` and `+∞` outside it. -/
theorem perturbationPrimalObjective_lorentzConstraintPerturbation :
    perturbationPrimalObjective (lorentzConstraintPerturbation φ) =
      fun ξ : ℝ × ℝ ↦ if ‖ξ‖ ≤ ξ.1 then (φ ξ.2 : EReal) else ⊤ := sorry

-- Proof sketch: by the previous formula, every feasible point has second coordinate `0`, so the
-- primal objective takes the constant value `φ(0)` on the feasible set and `+∞` elsewhere.
/-- Example 19.28 (3): clause (ii), second part. The optimal primal value is `φ(0)`. -/
theorem sInf_perturbationPrimalObjective_lorentzConstraintPerturbation :
    sInf (Set.range (perturbationPrimalObjective (lorentzConstraintPerturbation φ))) = φ 0 := sorry

-- Proof sketch: combine the primal objective formula with `lorentz_feasible_iff`; the feasible
-- set is exactly `ℝ₊ × {0}`, and the primal objective is constant there.
/-- Example 19.28 (4): clause (ii), third part. The set of primal solutions is
`ℝ₊ × {0}`. -/
theorem argmin_perturbationPrimalObjective_lorentzConstraintPerturbation :
    Argmin (perturbationPrimalObjective (lorentzConstraintPerturbation φ)) =
      Set.Ici (0 : ℝ) ×ˢ ({0} : Set ℝ) := sorry

-- Proof sketch: rewrite the explicit perturbation through Proposition 19.25 (3), identify the
-- polar cone of `Set.Iic 0` with `Set.Ici 0`, and simplify the pairing on `ℝ` to scalar
-- multiplication.
/-- Example 19.28 (5): clause (iii), first part. The dual objective is
`v ↦ sup_ξ (v (ξ₁ - ‖ξ‖) - φ(ξ₂))` on `ℝ₊` and `+∞` on `(-∞,0)`. -/
theorem perturbationDualObjective_lorentzConstraintPerturbation :
    perturbationDualObjective (lorentzConstraintPerturbation φ) =
      fun v : ℝ ↦
        if 0 ≤ v then
          ⨆ ξ : ℝ × ℝ, ((v * (ξ.1 - ‖ξ‖) : ℝ) : EReal) - (φ ξ.2 : EReal)
        else
          ⊤ := sorry

-- Proof sketch: on `ℝ₊`, the dual objective equals the displayed supremum. That supremum is at
-- most `-γ` because `ξ.1 - ‖ξ‖ ≤ 0`, and it reaches `-γ` by sending `ξ₁ → +∞`.
/-- Example 19.28 (6): clause (iii), second part. The optimal dual value is `-γ`, where
`γ = inf φ(ℝ)`. -/
theorem sInf_perturbationDualObjective_lorentzConstraintPerturbation :
    sInf (Set.range (perturbationDualObjective (lorentzConstraintPerturbation φ))) =
      -phiRangeInfimum φ := sorry

-- Proof sketch: the previous formula shows that the dual objective is constant on `ℝ₊` with
-- value `-γ`, while it is `+∞` on `(-∞,0)`.
/-- Example 19.28 (7): clause (iii), third part. The set of dual solutions is `ℝ₊`. -/
theorem argmin_perturbationDualObjective_lorentzConstraintPerturbation :
    Argmin (perturbationDualObjective (lorentzConstraintPerturbation φ)) = Set.Ici (0 : ℝ) := sorry

-- Proof sketch: specialize Proposition 19.25 (4), then rewrite
-- `ξ ∈ effectiveDomain (fun η : ℝ × ℝ ↦ φ η.2)` as `ξ.2 ∈ effectiveDomain φ` and
-- `v ∈ (Set.Iic 0)ᵒ⊖` as `0 ≤ v`.
/-- Example 19.28 (8): clause (iv). The Lagrangian has the branch formula displayed in (19.70). -/
theorem lagrangian_lorentzConstraintPerturbation
    (ξ : ℝ × ℝ) (v : ℝ) :
    ℒ[lorentzConstraintPerturbation φ] ξ v =
      if hξ : ξ.2 ∈ effectiveDomain φ then
        if 0 ≤ v then
          (φ ξ.2 : EReal) + ((v * (‖ξ‖ - ξ.1) : ℝ) : EReal)
        else
          ⊥
      else
        ⊤ := sorry

-- Proof sketch: combine clause (1) with Proposition 19.25 (5), then specialize the primal and
-- dual solution descriptions from clauses (4) and (7); existence of a saddle point is equivalent
-- to the coincidence of the primal and dual values `φ(0)` and `γ`.
/-- Example 19.28 (9): clause (v), first part. The Lagrangian has a saddle point if and only if
`φ(0) = γ`. -/
theorem exists_saddlePoint_lorentzConstraintPerturbation_iff
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ) :
    (∃ ξ : ℝ × ℝ, ∃ v : ℝ,
      IsSaddlePointOn (Set.univ : Set (ℝ × ℝ)) (Set.univ : Set ℝ)
        (ℒ[lorentzConstraintPerturbation φ]) ξ v) ↔
      (φ 0 : EReal) = phiRangeInfimum φ := sorry

-- Proof sketch: under the equality `φ(0) = γ`, clause (9) gives existence, and the
-- saddle-point criterion from Proposition 19.25 (5) reduces the set of saddle points to the
-- product of the primal and dual solution sets from clauses (4) and (7).
/-- Example 19.28 (10): clause (v), second part. When `φ(0) = γ`, the saddle points are exactly
`(ℝ₊ × {0}) × ℝ₊`. -/
theorem saddlePoints_lorentzConstraintPerturbation
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ)
    (hγ : (φ 0 : EReal) = phiRangeInfimum φ) :
    {p : (ℝ × ℝ) × ℝ |
        IsSaddlePointOn (Set.univ : Set (ℝ × ℝ)) (Set.univ : Set ℝ)
          (ℒ[lorentzConstraintPerturbation φ]) p.1 p.2} =
      (Set.Ici (0 : ℝ) ×ˢ ({0} : Set ℝ)) ×ˢ Set.Ici (0 : ℝ) := sorry

-- Proof sketch: evaluate the value function directly from the primal slices. For `y < 0`, the
-- feasible set allows the residual to approach `0`, yielding `γ`; for `y = 0`, feasibility forces
-- `ξ₂ = 0`; and for `y > 0`, the slice is infeasible, so the value is `+∞`.
/-- Example 19.28 (11): clause (vi). The value function equals `γ` on `(-∞,0)`, equals `φ(0)` at
`0`, and equals `+∞` on `(0,+∞)`. -/
theorem valueFunction_lorentzConstraintPerturbation :
    Prod.snd ▷ lorentzConstraintPerturbation φ =
      fun y : ℝ ↦
        if y < 0 then
          phiRangeInfimum φ
        else if y = 0 then
          (φ 0 : EReal)
        else
          ⊤ := sorry

end

end ERealFunction
