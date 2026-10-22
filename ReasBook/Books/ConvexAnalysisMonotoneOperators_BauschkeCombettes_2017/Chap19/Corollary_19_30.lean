/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Corollary_12_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Corollary_19_23
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Proposition_19_25

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators InnerProductSpace

universe u

namespace ERealFunction

section MixedConstraints

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {m p : ℕ} {hp : p ≤ m}

/- Source-facing convention: `m` is the total number of constraints and `p` is the size of the
inequality block, so the equality block is indexed by `Fin (m - p)`. -/
local notation "ConstraintSpace" => EuclideanSpace ℝ (Fin p ⊕ Fin (m - p))

attribute [local instance] Classical.propDecidable

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-- The mixed constraint cone `ℝ_-^p × {0}` in the split-coordinate model used in
Corollary 19.30. -/
def mixedConstraintCone : Set ConstraintSpace :=
  {η | (∀ i : Fin p, η (Sum.inl i) ≤ 0) ∧ ∀ j : Fin (m - p), η (Sum.inr j) = 0}

/-- The canonical constraint map whose first block records the inequality functions `g_i` and
whose second block records the affine residuals of the Chapter 19 owner
`equalityCoordinateMap u x - ρ`. -/
def mixedConstraintMap
    (g : Fin p → H → ℝ) (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ) :
    H → ConstraintSpace :=
  fun x ↦
    (EuclideanSpace.equiv (Fin p ⊕ Fin (m - p)) ℝ).symm <|
      Sum.elim (fun i ↦ g i x) (fun j ↦ equalityCoordinateMap u x j - ρ j)

@[simp] theorem mixedConstraintMap_apply_inl
    (g : Fin p → H → ℝ) (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ)
    (x : H) (i : Fin p) :
    mixedConstraintMap g u ρ x (Sum.inl i) = g i x :=
  by simp [mixedConstraintMap]

@[simp] theorem mixedConstraintMap_apply_inr
    (g : Fin p → H → ℝ) (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ)
    (x : H) (j : Fin (m - p)) :
    mixedConstraintMap g u ρ x (Sum.inr j) = ⟪x, u j⟫_ℝ - ρ j := by
  simp [mixedConstraintMap]

/-- Membership in the mixed cone is exactly blockwise nonpositivity on the inequality coordinates
and vanishing on the equality coordinates. -/
@[simp] theorem mem_mixedConstraintCone_iff {η : ConstraintSpace} :
    η ∈ mixedConstraintCone ↔
      (∀ i : Fin p, η (Sum.inl i) ≤ 0) ∧ ∀ j : Fin (m - p), η (Sum.inr j) = 0 :=
  Iff.rfl

/-- The shifted constraint vector `mixedConstraintMap g u ρ x + η` lies in the mixed cone exactly
when the inequality and equality constraints of Corollary 19.30 hold at `(x, η)`. -/
@[simp] theorem mixedConstraintMap_add_mem_mixedConstraintCone_iff
    (g : Fin p → H → ℝ) (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ)
    (x : H) (η : ConstraintSpace) :
    mixedConstraintMap g u ρ x + η ∈ mixedConstraintCone ↔
      (∀ i : Fin p, g i x ≤ -η (Sum.inl i)) ∧
        (∀ j : Fin (m - p), ⟪x, u j⟫_ℝ = -η (Sum.inr j) + ρ j) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      have hi : g i x + η (Sum.inl i) ≤ 0 := by
        simpa using h.1 i
      linarith
    · intro j
      have hj : (⟪x, u j⟫_ℝ - ρ j) + η (Sum.inr j) = 0 := by
        simpa using h.2 j
      linarith
  · rintro ⟨hineq, heq⟩
    refine ⟨?_, ?_⟩
    · intro i
      have hi : g i x + η (Sum.inl i) ≤ 0 := by
        linarith [hineq i]
      simpa using hi
    · intro j
      have hj : (⟪x, u j⟫_ℝ - ρ j) + η (Sum.inr j) = 0 := by
        linarith [heq j]
      simpa using hj

/-- The unshifted mixed constraint vector lies in the mixed cone exactly when the primal point
satisfies all inequality and equality constraints. -/
@[simp] theorem mixedConstraintMap_mem_mixedConstraintCone_iff
    (g : Fin p → H → ℝ) (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ) (x : H) :
    mixedConstraintMap g u ρ x ∈ mixedConstraintCone ↔
      (∀ i : Fin p, g i x ≤ 0) ∧
        (∀ j : Fin (m - p), ⟪x, u j⟫_ℝ = ρ j) := by
  simpa using (mixedConstraintMap_add_mem_mixedConstraintCone_iff g u ρ x 0)

/-- The feasibility hypothesis for the mixed system of convex inequalities and affine equalities
appearing in Corollary 19.30. -/
def HasMixedConstraintFeasiblePoint
    (f : H → Set.Ioi (⊥ : EReal)) (g : Fin p → H → ℝ)
    (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ) : Prop :=
  ∃ x : H,
    x ∈ effectiveDomain f ∧
      (∀ i : Fin p, g i x ≤ 0) ∧
      ∀ j : Fin (m - p), ⟪x, u j⟫_ℝ = ρ j

/-- The source-facing feasibility hypothesis is equivalent to the canonical feasibility condition
for the mixed map and mixed cone. -/
theorem hasMixedConstraintFeasiblePoint_iff
    (f : H → Set.Ioi (⊥ : EReal)) (g : Fin p → H → ℝ)
    (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ) :
    HasMixedConstraintFeasiblePoint f g u ρ ↔
      ∃ x : H, x ∈ effectiveDomain f ∧ mixedConstraintMap g u ρ x ∈ mixedConstraintCone := by
  constructor
  · rintro ⟨x, hx, hineq, heq⟩
    exact ⟨x, hx, (mixedConstraintMap_mem_mixedConstraintCone_iff g u ρ x).2 ⟨hineq, heq⟩⟩
  · rintro ⟨x, hx, hxK⟩
    rcases (mixedConstraintMap_mem_mixedConstraintCone_iff g u ρ x).1 hxK with ⟨hineq, heq⟩
    exact ⟨x, hx, hineq, heq⟩

/-- The perturbation function `F` from Corollary 19.30 for convex inequality constraints
`g_i(x) ≤ 0` and affine equality constraints `⟪x, u_j⟫ = ρ_j`. -/
abbrev mixedConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (g : Fin p → H → ℝ)
    (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ) :
    H × ConstraintSpace → Set.Ioi (⊥ : EReal) :=
  inequalityConstraintPerturbation f (mixedConstraintMap g u ρ) mixedConstraintCone

-- Proof sketch: unfold `mixedConstraintPerturbation` and simplify the branch selected by the
-- feasibility hypothesis on `(x, (η, ζ))`.
/-- Evaluating the mixed-constraint perturbation on a feasible perturbation fiber returns `f x`. -/
@[simp] theorem mixedConstraintPerturbation_apply_of_feasible
    (f : H → Set.Ioi (⊥ : EReal)) (g : Fin p → H → ℝ)
    (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ)
    {x : H} {η : ConstraintSpace}
    (hfeas :
      (∀ i : Fin p, g i x ≤ -η (Sum.inl i)) ∧
        (∀ j : Fin (m - p), ⟪x, u j⟫_ℝ = -η (Sum.inr j) + ρ j)) :
    mixedConstraintPerturbation f g u ρ (x, η) = f x := by
  exact
    inequalityConstraintPerturbation_apply_of_mem f (mixedConstraintMap g u ρ)
      mixedConstraintCone
      ((mixedConstraintMap_add_mem_mixedConstraintCone_iff g u ρ x η).2 hfeas)

/-- The unconstrained affine perturbation minimized in Corollary 19.30(v). -/
def mixedConstraintAffineObjective
    (f : H → Set.Ioi (⊥ : EReal)) (g : Fin p → H → ℝ) (u : Fin (m - p) → H)
    (ν : ConstraintSpace) : H → EReal :=
  fun x ↦
    (f x : EReal) +
      (((∑ i : Fin p, ν (Sum.inl i) * g i x) : ℝ) : EReal) +
        (((∑ j : Fin (m - p), ν (Sum.inr j) * ⟪x, u j⟫_ℝ) : ℝ) : EReal)

-- Proof sketch: Corollary 19.30 is a specialization of Proposition 19.25 with codomain
-- `EuclideanSpace ℝ (Fin p ⊕ Fin (m - p))`, whose left block encodes the inequalities and whose
-- right block encodes the affine equalities.
/-- Corollary 19.30 (1): if `f ∈ Γ₀(H)`, each real-valued `g_i` belongs to `Γ₀(H)` after
coercion, and the mixed inequality/equality system is feasible, then the perturbation function
from formula `(19.74)` belongs to `Γ₀(H × ℝ^m)` in the split-coordinate model
`EuclideanSpace ℝ (Fin p ⊕ Fin (m - p))`. -/
theorem mixedConstraintPerturbation_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : Fin p → H → ℝ) (hg : ∀ i : Fin p, (g i).toEReal ∈ Γ₀(H))
    (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ)
    (hfeas : HasMixedConstraintFeasiblePoint f g u ρ) :
    mixedConstraintPerturbation f g u ρ ∈
      Γ₀(H × ConstraintSpace) := sorry

-- Proof sketch: evaluate `perturbationPrimalObjective` at the zero perturbation and simplify the
-- resulting feasibility conditions `g_i(x) ≤ -0` and `⟪x, u_j⟫ = -0 + ρ_j`.
/-- Corollary 19.30 (2): the primal problem attached to `F` is the minimization of `f(x)` under
`g_i(x) ≤ 0` for every inequality index and `⟪x, u_j⟫ = ρ_j` for every equality index. -/
theorem perturbationPrimalObjective_mixedConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (g : Fin p → H → ℝ)
    (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ) :
    perturbationPrimalObjective (mixedConstraintPerturbation f g u ρ) =
      fun x : H ↦
        if
          (∀ i : Fin p, g i x ≤ 0) ∧
            (∀ j : Fin (m - p), ⟪x, u j⟫_ℝ = ρ j) then
          (f x : EReal)
        else
          ⊤ := by
  funext x
  simpa [mixedConstraintMap_mem_mixedConstraintCone_iff, sub_eq_zero] using
    congrFun
      (perturbationPrimalObjective_inequalityConstraintPerturbation
        f (mixedConstraintMap g u ρ) mixedConstraintCone) x

-- Proof sketch: specialize Proposition 19.25 (3) to the cone `ℝ_-^p × {0}` and rewrite
-- membership in its polar cone as nonnegativity of the first block of multipliers.
/-- Corollary 19.30 (3): the dual objective is the explicit supremum formula `(19.76)`, with
nonnegative multipliers on the inequality block and unrestricted multipliers on the equality
block. -/
theorem perturbationDualObjective_mixedConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (g : Fin p → H → ℝ)
    (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ) :
    perturbationDualObjective (mixedConstraintPerturbation f g u ρ) =
      fun ν : ConstraintSpace ↦
        if ∀ i : Fin p, 0 ≤ ν (Sum.inl i) then
          ⨆ x : H,
            -((((∑ i : Fin p, ν (Sum.inl i) * g i x) : ℝ) : EReal)) +
              ((((∑ j : Fin (m - p), ν (Sum.inr j) * (ρ j - ⟪x, u j⟫_ℝ)) : ℝ) : EReal)) -
              (f x : EReal)
        else
          ⊤ := sorry

-- Proof sketch: specialize Proposition 19.25 (4) to the mixed constraint map and rewrite the
-- polar-cone condition as nonnegativity of the inequality multipliers.
/-- Corollary 19.30 (4): the Lagrangian of the mixed perturbation is the piecewise function from
formula `(19.77)`: `+∞` off `dom f`, the affine-perturbed objective on `dom f` when the
inequality multipliers are nonnegative, and `-∞` otherwise. -/
theorem lagrangian_mixedConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (g : Fin p → H → ℝ)
    (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ)
    (x : H) (ν : ConstraintSpace) :
    ℒ[mixedConstraintPerturbation f g u ρ] x ν =
      if hx : x ∈ effectiveDomain f then
        if ∀ i : Fin p, 0 ≤ ν (Sum.inl i) then
          (f x : EReal) +
            ((((∑ i : Fin p, ν (Sum.inl i) * g i x) : ℝ) : EReal) +
              (((∑ j : Fin (m - p), ν (Sum.inr j) * (⟪x, u j⟫_ℝ - ρ j)) : ℝ) : EReal))
        else
          ⊥
      else
        ⊤ := sorry

variable [CompleteSpace H]

-- Proof sketch: specialize Proposition 19.25 (6) to the mixed constraint map. This gives the
-- primal-solution conclusion for the specialized perturbation problem.
/-- Corollary 19.30 (5): every saddle point of the Lagrangian yields a solution of the primal
problem `(19.75)`. -/
theorem mem_argmin_perturbationPrimalObjective_of_mixedConstraintPerturbation_isSaddlePoint
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : Fin p → H → ℝ) (hg : ∀ i : Fin p, (g i).toEReal ∈ Γ₀(H))
    (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ)
    (hfeas : HasMixedConstraintFeasiblePoint f g u ρ)
    {xbar : H} {νbar : ConstraintSpace}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H)
        (Set.univ : Set ConstraintSpace)
        (ℒ[mixedConstraintPerturbation f g u ρ]) xbar νbar) :
    xbar ∈ Argmin (perturbationPrimalObjective (mixedConstraintPerturbation f g u ρ)) := sorry

-- Proof sketch: use the saddle-point characterization from Proposition 19.25 together with the
-- specialized affine formula for the Lagrangian to identify the unconstrained minimization
-- problem solved by the primal component.
/-- Corollary 19.30 (6): every saddle point of the Lagrangian makes its primal component solve the
unconstrained minimization problem `min_x f(x) + Σ_i ν_i g_i(x) + Σ_j ν_j ⟪x, u_j⟫`. -/
theorem mem_argmin_mixedConstraintAffineObjective_of_mixedConstraintPerturbation_isSaddlePoint
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : Fin p → H → ℝ) (hg : ∀ i : Fin p, (g i).toEReal ∈ Γ₀(H))
    (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ)
    (hfeas : HasMixedConstraintFeasiblePoint f g u ρ)
    {xbar : H} {νbar : ConstraintSpace}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H)
        (Set.univ : Set ConstraintSpace)
        (ℒ[mixedConstraintPerturbation f g u ρ]) xbar νbar) :
    xbar ∈ Argmin (mixedConstraintAffineObjective f g u νbar) := sorry

-- Proof sketch: the specialized saddle-point optimality system gives feasibility of the primal
-- point, which here means membership in `dom f` together with all inequality constraints.
/-- Corollary 19.30 (7): at a saddle point, the primal component belongs to `dom f` and satisfies
every inequality constraint `g_i(x̄) ≤ 0`. -/
theorem effectiveDomain_and_inequalities_of_mixedConstraintPerturbation_isSaddlePoint
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : Fin p → H → ℝ) (hg : ∀ i : Fin p, (g i).toEReal ∈ Γ₀(H))
    (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ)
    (hfeas : HasMixedConstraintFeasiblePoint f g u ρ)
    {xbar : H} {νbar : ConstraintSpace}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H)
        (Set.univ : Set ConstraintSpace)
        (ℒ[mixedConstraintPerturbation f g u ρ]) xbar νbar) :
    xbar ∈ effectiveDomain f ∧
      (∀ i : Fin p, g i xbar ≤ 0) := sorry

-- Proof sketch: the dual block of the specialized saddle-point system lies in the polar cone of
-- `ℝ_-^p × {0}`, which is exactly the nonnegative orthant on the inequality multipliers, and the
-- complementary-slackness identity reduces to `ν_i g_i(x̄) = 0`.
/-- Corollary 19.30 (8): at a saddle point, every inequality multiplier is nonnegative and
satisfies the complementary-slackness identity `ν_i g_i(x̄) = 0`. -/
theorem complementarySlackness_of_mixedConstraintPerturbation_isSaddlePoint
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : Fin p → H → ℝ) (hg : ∀ i : Fin p, (g i).toEReal ∈ Γ₀(H))
    (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ)
    (hfeas : HasMixedConstraintFeasiblePoint f g u ρ)
    {xbar : H} {νbar : ConstraintSpace}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H)
        (Set.univ : Set ConstraintSpace)
        (ℒ[mixedConstraintPerturbation f g u ρ]) xbar νbar) :
    ∀ i : Fin p, 0 ≤ νbar (Sum.inl i) ∧ νbar (Sum.inl i) * g i xbar = 0 := sorry

end MixedConstraints

end ERealFunction
