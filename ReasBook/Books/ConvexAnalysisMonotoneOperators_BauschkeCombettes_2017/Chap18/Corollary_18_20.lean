/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_20
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_23
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.ProximityOperator
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Proposition_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section StrongerDifferentiabilityNotions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {I : Type v} [Fintype I]

/-- The real-valued potential `∑ i, α i (f_i^* □ q)` from Moreau's formula, written using the
unit Moreau envelopes of the Fenchel conjugates `f_i^*`. -/
noncomputable def weightedConjugateMoreauAverage
    (f : I → H → Set.Ioi (⊥ : EReal)) (hf : ∀ i, f i ∈ Γ₀(H)) (α : I → ℝ) : H → ℝ :=
  fun x ↦
    ∑ i, α i *
      (({}^[⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩] (gammaZeroConjugate (f i) (hf i))) x).toReal

-- Proof sketch: unfold `weightedConjugateMoreauAverage`.
/-- Evaluating `weightedConjugateMoreauAverage` gives the finite weighted sum of the unit Moreau
envelopes of the conjugates `f_i^*`. -/
theorem weightedConjugateMoreauAverage_apply
    (f : I → H → Set.Ioi (⊥ : EReal)) (hf : ∀ i, f i ∈ Γ₀(H)) (α : I → ℝ) (x : H) :
    weightedConjugateMoreauAverage f hf α x =
      ∑ i, α i *
        (({}^[⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩] (gammaZeroConjugate (f i) (hf i))) x).toReal :=
  sorry

/-- The `Γ₀(H)` candidate
`h = (∑ i, α i (f_i^* □ q))^* - q`
from Moreau's formula, encoded by `conjugateSubInvHalfSquaredNorm`. -/
noncomputable abbrev weightedProxGenerator
    (f : I → H → Set.Ioi (⊥ : EReal)) (hf : ∀ i, f i ∈ Γ₀(H)) (α : I → ℝ) :
    H → Set.Ioi (⊥ : EReal) :=
  conjugateSubInvHalfSquaredNorm (weightedConjugateMoreauAverage f hf α)
    ⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩

-- Proof sketch: unfold `weightedProxGenerator` and `weightedConjugateMoreauAverage`, then rewrite
-- `conjugateSubInvHalfSquaredNorm` at the unit Moreau parameter `γ = 1`.
/-- Coercing `weightedProxGenerator` to `EReal` gives the shifted conjugate
`(∑ i, α i (f_i^* □ q))^* - q`, with the source potential expressed through unit Moreau
envelopes. -/
theorem weightedProxGenerator_coe
    (f : I → H → Set.Ioi (⊥ : EReal)) (hf : ∀ i, f i ∈ Γ₀(H)) (α : I → ℝ) (x : H) :
    (weightedProxGenerator f hf α x : EReal) =
      conjugate (fun y : H ↦ ((weightedConjugateMoreauAverage f hf α y : ℝ) : EReal)) x -
        ((((1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) : ℝ) : EReal)) := sorry

-- Proof sketch: Proposition 8.17 and Proposition 12.15 keep the weighted Moreau-average
-- potential convex and finite-valued, Proposition 12.30 identifies its gradient with the weighted
-- sum of the proximal operators, Proposition 12.28 makes that gradient nonexpansive, and Theorem
-- 18.15 with `β = 1` then shows that the shifted conjugate belongs to `Γ₀(H)`.
/-- The Moreau candidate `weightedProxGenerator f hf α` belongs to `Γ₀(H)` when the coefficients
form a finite convex combination. -/
theorem weightedProxGenerator_mem_gammaZero
    (f : I → H → Set.Ioi (⊥ : EReal)) (hf : ∀ i, f i ∈ Γ₀(H)) (α : I → ℝ)
    (hα_nonneg : ∀ i, 0 ≤ α i) (hα_sum : ∑ i, α i = 1) :
    weightedProxGenerator f hf α ∈ Γ₀(H) := sorry

-- Proof sketch: form the real-valued potential
-- `g = weightedConjugateMoreauAverage f hf α = ∑ i, α i (f_i^* □ q)`, use Proposition 12.30 to
-- identify `∇ g` with the weighted sum of the proximal operators, note from Proposition 12.28
-- that this gradient is nonexpansive as a convex combination of nonexpansive maps, and then apply
-- the implication `(i) → (ix)` of Theorem 18.15 at `β = 1`.
/-- Corollary 18.20: for a finite family `(f_i)` in `Γ₀(H)` and nonnegative coefficients `α i`
with `∑ i, α i = 1`, the convex combination `∑ i, α i Prox_{f_i}` is the proximity operator of
`weightedProxGenerator f hf α`, that is, of
`h = (∑ i, α i (f_i^* □ q))^* - q`. -/
theorem weightedSum_proximityOperator_eq_proximityOperator_weightedProxGenerator
    (f : I → H → Set.Ioi (⊥ : EReal)) (hf : ∀ i, f i ∈ Γ₀(H)) (α : I → ℝ)
    (hα_nonneg : ∀ i, 0 ≤ α i) (hα_sum : ∑ i, α i = 1) :
    (fun x : H ↦
      ∑ i, α i • Prox[f i, hf i] x) =
      Prox[weightedProxGenerator f hf α,
        weightedProxGenerator_mem_gammaZero f hf α hα_nonneg hα_sum] := sorry

end StrongerDifferentiabilityNotions

end ERealFunction
