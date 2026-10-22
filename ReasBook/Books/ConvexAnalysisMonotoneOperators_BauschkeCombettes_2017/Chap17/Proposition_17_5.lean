/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_23
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_33

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The contact set `C = {x | f x = {}^γ f x}` of `f` with its `γ`-Moreau envelope. -/
def moreauEnvelopeContactSet
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) : Set H :=
  {x | (f x : EReal) = ({}^[γ] f) x}

-- Proof sketch: unfold `moreauEnvelopeContactSet`; membership is exactly the defining equality
-- `f x = {}^γ f x`.
/-- Membership in the Moreau-envelope contact set is exactly the equality `f x = {}^γ f x`. -/
theorem mem_moreauEnvelopeContactSet_iff
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) {x : H} :
    x ∈ moreauEnvelopeContactSet f γ ↔ (f x : EReal) = ({}^[γ] f) x := sorry

-- Proof sketch: combine the explicit proximal-point formula for the `γ`-Moreau envelope with the
-- gradient formula for `x ↦ ({}^γ f x).toReal`, and use Proposition 17.4 on the smooth convex
-- function `{}^γ f` to identify its minimizers with the fixed points of `Prox_{γ f}`. The
-- resulting minimizer condition is exactly the equality `f x = {}^γ f x`.
/-- Proposition 17.5: for `f ∈ Γ₀(H)` and `γ ∈ ℝ_{++}`, the fixed points of `Prox_{γ f}` are
exactly the points `x` where `f x = {}^γ f x`, i.e. the textbook set `C`. -/
theorem fixedPoints_scaledProximityOperator_eq_moreauEnvelopeContactSet_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    Function.fixedPoints (Prox[γ, f, hf]) = moreauEnvelopeContactSet f γ := sorry

-- Proof sketch: view `Prox[γ, f, hf]` as the ordinary proximity operator of the
-- scaled function `γ f`, then apply the Chapter 12 fixed-point/argmin identification for the
-- ordinary proximity operator of `γ • f`.
/-- The fixed points of `Prox_{γ f}` are exactly the global minimizers of the scaled function
`γ f`. -/
theorem fixedPoints_scaledProximityOperator_eq_argmin_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    Function.fixedPoints (Prox[γ, f, hf]) = Argmin (γ • f).asEReal := sorry

-- Proof sketch: positive pointwise scaling by `γ ∈ ℝ_{++}` preserves the order relation on
-- `EReal`, so the minimizers of `γ f` and `f` coincide.
/-- Positive scaling does not change the global minimizers of a function. -/
theorem argmin_posReal_smul_eq_argmin
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) :
    Argmin (γ • f).asEReal = Argmin f.asEReal := sorry

-- Proof sketch: combine the scaled-argmin clause above with the invariance of argmin sets under
-- positive scaling.
/-- The fixed points of `Prox_{γ f}` are exactly the global minimizers of `f`. -/
theorem fixedPoints_scaledProximityOperator_eq_argmin_original_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    Function.fixedPoints (Prox[γ, f, hf]) = Argmin f.asEReal := by
  rw [fixedPoints_scaledProximityOperator_eq_argmin_of_mem_gammaZero,
    argmin_posReal_smul_eq_argmin f γ]

-- Proof sketch: Proposition 17.4 identifies the minimizers of the differentiable convex function
-- `{}^γ f` with the zeros of its gradient, and Proposition 12.30 rewrites that gradient as the
-- residual `γ⁻¹ • (Id - Prox_{γ f})`. The vanishing-gradient condition is therefore exactly
-- `f x = {}^γ f x`.
/-- The Moreau-envelope contact set is exactly the set of minimizers of the `γ`-Moreau envelope. -/
theorem moreauEnvelopeContactSet_eq_argmin_moreauEnvelope_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (_hf : f ∈ Γ₀(H)) (γ : PosReal) :
    moreauEnvelopeContactSet f γ = Argmin ({}^[γ] f) := sorry

-- Proof sketch: combine Proposition 12.30 with Proposition 17.4 to identify
-- `Argmin ({}^γ f)` with `Function.fixedPoints (Prox[γ, f, hf])`, then use the
-- previous fixed-point description by minimizers of `f`.
/-- The minimizers of the `γ`-Moreau envelope coincide with the minimizers of `f`. -/
theorem argmin_moreauEnvelope_eq_argmin_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (_hf : f ∈ Γ₀(H)) (γ : PosReal) :
    Argmin ({}^[γ] f) = Argmin f.asEReal := sorry

-- Proof sketch: apply the unit-parameter fixed-point/minimizer identity to the Fenchel conjugate
-- `f*`, encoded by the canonical owner `f∗[hf]`, and rewrite `Function.fixedPoints` for the
-- proximity operator of `f*` as the zero set of `Prox_{f*}`.
/-- The zeros of the proximity operator of the Fenchel conjugate `f*` are exactly the minimizers
of `f`. -/
theorem conjugateProximityOperator_zeroSet_eq_argmin_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    (Function.toSetValuedOperator (Prox⋆[f, hf])).zeros = Argmin f.asEReal := sorry

/- Proposition 17.5, final clause: the minimizers of `f` are exactly the subgradients of the
Fenchel conjugate `f*` at `0`. This is the earlier canonical owner theorem
`argmin_eq_subdifferential_gammaZeroConjugate_zero`. -/
recall argmin_eq_subdifferential_gammaZeroConjugate_zero

end

end ERealFunction
