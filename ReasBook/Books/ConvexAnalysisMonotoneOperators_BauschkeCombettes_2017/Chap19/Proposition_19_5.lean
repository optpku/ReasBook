/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.ProximityOperator
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Proposition_19_20

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

noncomputable section

universe u v

namespace ERealFunction

section Basic

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

/- Source/core/bridge triage:
- `source-facing`: Proposition 19.5 is the perturbation attached to the proximal composite
  objective `x ↦ φ(x) + ψ(Lx - r) + (1 / 2) ‖x - z‖²`.
- `core/canonical`: the owner abstractions are `compositePerturbationFunction`,
  `perturbationPrimalObjective`, `perturbationDualObjective`, and `Prox[φ, hφ]`.
- `bridge/view`: the formula lemmas below rewrite the owner perturbation back to the textbook
  primal and dual expressions. -/

-- Proof sketch: `proximalObjective φ z x` is `φ(x) + (1 / 2) ‖x - z‖²`, so it stays strictly
-- above `⊥`.
private theorem proximalObjective_value_mem_Ioi_bot
    (φ : H → Set.Ioi (⊥ : EReal)) (z x : H) :
    proximalObjective φ z x ∈ Set.Ioi (⊥ : EReal) := sorry

/- The unit proximal objective, repackaged in `]⊥, +∞]` so that the canonical composite
perturbation owner applies directly. -/
private def proximalObjectiveIoi
    (φ : H → Set.Ioi (⊥ : EReal)) (z : H) :
    H → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    ⟨proximalObjective φ z x,
      proximalObjective_value_mem_Ioi_bot φ z x⟩

@[simp] private theorem proximalObjectiveIoi_apply
    (φ : H → Set.Ioi (⊥ : EReal)) (z x : H) :
    (proximalObjectiveIoi φ z x : EReal) =
      (φ x : EReal) + ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal)) :=
  by
    simp [proximalObjectiveIoi, proximalObjective, norm_sub_rev]

/- The translated second factor `y ↦ ψ(y - r)`, repackaged in `]⊥, +∞]` for the canonical
composite perturbation owner. -/
private def translatedIoi
    (ψ : K → Set.Ioi (⊥ : EReal)) (r : K) :
    K → Set.Ioi (⊥ : EReal) :=
  fun y ↦ ψ (y - r)

omit [NormedSpace ℝ K] in
@[simp] private theorem translatedIoi_apply
    (ψ : K → Set.Ioi (⊥ : EReal)) (r y : K) :
    (translatedIoi ψ r y : EReal) = (ψ (y - r) : EReal) :=
  rfl

/-- The perturbation attached to Proposition 19.5, obtained by feeding the regularized first term
`x ↦ φ(x) + (1 / 2) ‖x - z‖²` and the translated second term `y ↦ ψ(y - r)` into the canonical
composite perturbation owner. -/
def proximalCompositePerturbationFunction
    (φ : H → Set.Ioi (⊥ : EReal)) (ψ : K → Set.Ioi (⊥ : EReal))
    (z : H) (r : K) (L : H →L[ℝ] K) :
    H × K → Set.Ioi (⊥ : EReal) :=
  compositePerturbationFunction (proximalObjectiveIoi φ z) (translatedIoi ψ r) L

-- Proof sketch: unfold the composite perturbation and the two source-facing bridge factors.
/-- Evaluating the Proposition 19.5 perturbation gives
`φ(x) + ψ(Lx + y - r) + (1 / 2) ‖x - z‖²`. -/
@[simp] theorem proximalCompositePerturbationFunction_apply
    (φ : H → Set.Ioi (⊥ : EReal)) (ψ : K → Set.Ioi (⊥ : EReal))
    (z : H) (r : K) (L : H →L[ℝ] K) (x : H) (y : K) :
    (proximalCompositePerturbationFunction φ ψ z r L (x, y) : EReal) =
      (φ x : EReal) + (ψ (L x + y - r) : EReal) +
        ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal)) := by
  rw [proximalCompositePerturbationFunction, compositePerturbationFunction_apply,
    proximalObjectiveIoi_apply, translatedIoi_apply]
  abel

-- Proof sketch: evaluate the perturbation at `(x, 0)` and simplify `Lx + 0 - r` to `Lx - r`.
/-- The primal objective attached to `proximalCompositePerturbationFunction` is the textbook
objective `x ↦ φ(x) + ψ(Lx - r) + (1 / 2) ‖x - z‖²`. -/
theorem perturbationPrimalObjective_proximalCompositePerturbationFunction
    (φ : H → Set.Ioi (⊥ : EReal)) (ψ : K → Set.Ioi (⊥ : EReal))
    (z : H) (r : K) (L : H →L[ℝ] K) :
    perturbationPrimalObjective (proximalCompositePerturbationFunction φ ψ z r L) =
      fun x : H ↦
        (φ x : EReal) + (ψ (L x - r) : EReal) +
          ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal)) := sorry

end Basic

section PrimalSolutionsViaDualSolutions

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Proof sketch: specialize Proposition 19.20 (3) to the perturbation above, then rewrite the
-- conjugate of the regularized factor as the unit Moreau envelope of `φ*` and the conjugate of
-- the translated factor as `ψ* + ⟪·, r⟫`, using the canonical packaged conjugate `ψ∗[hψ]`.
/-- The dual objective attached to `proximalCompositePerturbationFunction` is the textbook
formula `(19.9)`. -/
theorem perturbationDualObjective_proximalCompositePerturbationFunction
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))
    (ψ : K → Set.Ioi (⊥ : EReal)) (hψ : ψ ∈ Γ₀(K))
    (z : H) (r : K) (L : H →L[ℝ] K) :
    perturbationDualObjective (proximalCompositePerturbationFunction φ ψ z r L) =
      fun v : K ↦
        ({}^[(1 : PosReal)] (φ∗[hφ])) (z - L.adjoint v) +
          (ψ∗[hψ] v : EReal) +
            ((⟪v, r⟫_ℝ : ℝ) : EReal) := sorry

-- Proof sketch: apply the unit-parameter Moreau decomposition identity to `φ` at
-- `z - L.adjoint v`, then substitute the result into the dual formula above.
/-- The Proposition 19.5 dual objective can also be written in the quadratic-minus-Moreau
form `(19.10)`. -/
theorem
    perturbationDualObjective_proximalComposite_eq_quadratic_sub_moreauEnvelope
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))
    (ψ : K → Set.Ioi (⊥ : EReal)) (hψ : ψ ∈ Γ₀(K))
    (z : H) (r : K) (L : H →L[ℝ] K) (v : K) :
    perturbationDualObjective (proximalCompositePerturbationFunction φ ψ z r L) v =
      ((((1 / 2 : ℝ) * ‖z - L.adjoint v‖ ^ 2 : ℝ) : EReal) -
        ({}^[(1 : PosReal)] φ) (z - L.adjoint v)) +
          (ψ∗[hψ] v : EReal) +
            ((⟪v, r⟫_ℝ : ℝ) : EReal) := sorry

-- Proof sketch: apply the Chapter 15 strong-duality/dual-attainment owner theorem to the
-- perturbation `proximalCompositePerturbationFunction φ ψ z r L`, then use the Chapter 19.4
-- singleton-argmin bridge with the Gâteaux derivative formula for the conjugate of the
-- regularized first factor to identify the unique primal minimizer as `Prox_φ (z - L^* v)`.
/-- Proposition 19.5: if `φ ∈ Γ₀(ℋ)`, `ψ ∈ Γ₀(𝒦)`, and
`r ∈ sri (L (dom φ) - dom ψ)`, then the dual problem
`v ↦ (1 / 2) ‖z - L^* v‖² - {}¹φ(z - L^* v) + ψ^*(v) + ⟪v, r⟫`
has a solution. Moreover, for every dual solution `v`, the unique minimizer of
`x ↦ φ(x) + ψ(Lx - r) + (1 / 2) ‖x - z‖²` is `Prox_φ (z - L^* v)`. The companion bridge theorem
`perturbationDualObjective_proximalCompositePerturbationFunction` records the equivalent dual
formula `(19.9)` with the canonical conjugate surface `ψ∗[hψ]`. -/
theorem
    argmin_proximalCompositeDual_nonempty_and_argmin_primal_eq_singleton_proximityOperator
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    {ψ : K → Set.Ioi (⊥ : EReal)} (hψ : ψ ∈ Γ₀(K))
    (z : H) (r : K) (L : H →L[ℝ] K)
    (hsri : r ∈ sri (L '' effectiveDomain φ - effectiveDomain ψ)) :
    (Argmin
      (fun v : K ↦
        ((((1 / 2 : ℝ) * ‖z - L.adjoint v‖ ^ 2 : ℝ) : EReal) -
          ({}^[(1 : PosReal)] φ) (z - L.adjoint v)) +
            (ψ∗[hψ] v : EReal) +
              ((⟪v, r⟫_ℝ : ℝ) : EReal))).Nonempty ∧
      ∀ {v : K},
        v ∈
            Argmin
              (fun v : K ↦
                ((((1 / 2 : ℝ) * ‖z - L.adjoint v‖ ^ 2 : ℝ) : EReal) -
                  ({}^[(1 : PosReal)] φ) (z - L.adjoint v)) +
                    (ψ∗[hψ] v : EReal) +
                      ((⟪v, r⟫_ℝ : ℝ) : EReal)) →
        Argmin
          (fun x : H ↦
            (φ x : EReal) + (ψ (L x - r) : EReal) +
              ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal))) =
          ({Prox[φ, hφ] (z - L.adjoint v)} : Set H) := sorry

end PrimalSolutionsViaDualSolutions

end ERealFunction
