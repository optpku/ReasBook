/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Proposition_3_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Example_17_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Corollary_12_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Example_12_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped ContinuousLinearMap Gradient InnerProductSpace

universe u

namespace ContinuousLinearMap

noncomputable section

variable {H : Type u}

/- Source/core/bridge triage:
- `source-facing`: Proposition 17.36 records convex-analytic properties of the quadratic potential
  `q[A]` and its Fenchel conjugate.
- `core/canonical`: the owner abstractions are the chapter-level quadratic-potential owner `q[A]`
  and the canonical `Γ₀(H)`-valued conjugate owner `q⋆[A, hA_mono]`.
- `bridge/view`: this file should therefore use the existing conjugate owner from
  `Corollary_13_38`, not a parallel local `quadraticPotentialConjugate` wrapper.
-/

section QuadraticPotential

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: `q[A]` is continuous as a quadratic form built from a bounded
-- linear operator, so its `EReal` coercion is lower semicontinuous. Convexity is the monotone
-- quadratic-form criterion from Example 17.8, with the scalar factor `1 / 2` preserving convexity.
/-- The quadratic potential of a monotone bounded operator, viewed as a `]-∞,+∞]`-valued
function, belongs to `Γ₀(H)`. -/
theorem quadraticPotential_mem_gammaZero_of_isMonotone
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone) :
    (q[A]).toEReal ∈ Γ₀(H) := sorry

/- Lean cannot parse the textbook subscripted star `q_A^*`, so we use the bracketed surface
`q⋆[A, hA_mono]` for the canonical `Γ₀(H)`-valued conjugate of the quadratic potential `q_A`. -/
scoped notation:max "q⋆[" A:max ", " hA_mono:max "]" =>
  (Function.toEReal (q[A]))∗[quadraticPotential_mem_gammaZero_of_isMonotone A hA_mono]

-- Proof sketch: rewrite `q[A]` as the positive scalar multiple
-- `(1 / 2) • (fun x ↦ ⟪x, A x⟫_ℝ)` and apply the monotone quadratic-form characterization from
-- Example 17.8.
/-- Proposition 17.36 (1): clause (i). If `A` is monotone, then its quadratic potential
`q_A(x) = (1 / 2) ⟪x, A x⟫_ℝ` is convex on all of `H`. -/
theorem quadraticPotential_convexOn_univ_of_isMonotone
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone) :
    ConvexOn ℝ Set.univ (q[A]) := sorry

-- Proof sketch: `q[A]` is a continuous bilinear expression in `x` built from the
-- continuous linear map `A`.
/-- Proposition 17.36 (2): clause (i). The quadratic potential `q_A` is continuous. -/
theorem quadraticPotential_continuous
    (A : H →L[ℝ] H) :
    Continuous (q[A]) := sorry

-- Proof sketch: differentiate the quadratic form using Example 2.57, specialized to the affine
-- term `u = 0` and then scaled by `1 / 2`.
/-- Proposition 17.36 (3): clause (i). The quadratic potential `q_A` is Fréchet differentiable on
`H`. -/
theorem quadraticPotential_differentiable
    (A : H →L[ℝ] H) :
    Differentiable ℝ (q[A]) := sorry

end QuadraticPotential

section Hilbert

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: Example 2.57 gives the gradient of `x ↦ ⟪x, A x⟫_ℝ` as
-- `x ↦ (A + A.adjoint) x`; divide by `2` and use self-adjointness to simplify to `A x`.
/-- Proposition 17.36 (4): clause (i). If `A` is self-adjoint, then the gradient of `q_A` is the
operator `A`. -/
theorem gradient_quadraticPotential_eq_of_isSelfAdjoint
    (A : H →L[ℝ] H) (hA_self : IsSelfAdjoint A) :
    ∇ (q[A]) = A := sorry

-- Proof sketch: use the identities `A A⁺ = P_(range A)` and `(A⁺)⁺ = A` for closed-range
-- self-adjoint operators, then rewrite the quadratic form of `A⁺` at `u` as the quadratic form of
-- `A` at `A⁺ u`.
/-- Proposition 17.36 (5): clause (ii), first identity. For a closed-range self-adjoint operator,
the quadratic potential of `A⁺` is `q_A ∘ A⁺`. -/
theorem quadraticPotential_moorePenroseInverse_eq_comp_moorePenroseInverse
    (A : H →L[ℝ] H) (hA_self : IsSelfAdjoint A) (hA_closed : IsClosed (A.range : Set H)) :
    q[A⁺[hA_closed]] = (q[A]) ∘ A⁺[hA_closed] :=
  sorry

-- Proof sketch: combine the conjugate formula for `q_A` on `range A` with the orthogonal
-- decomposition `H = ker A ⊕ (ker A)ᗮ`, then identify the exact infimal convolution with the
-- indicator of `ker A` and the conjugate `q_A^*`.
/-- Proposition 17.36 (6): clause (ii), second identity. For a monotone self-adjoint
closed-range operator, `q_{A⁺}` is the infimal convolution of `ι_(ker A)` with `q_A^*`. -/
theorem quadraticPotential_moorePenroseInverse_eq_setIndicator_ker_infimalConvolution_conjugate
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone) (hA_self : IsSelfAdjoint A)
    (hA_closed : IsClosed (A.range : Set H)) :
    (q[A⁺[hA_closed]]).toEReal.asEReal =
      ι[(A.ker : Set H)] □ q⋆[A, hA_mono] := sorry

-- Proof sketch: outside `range A`, the conjugate of `q_A` is infinite by translation along
-- `ker A`; on `range A`, write `u = A z` and apply the Fenchel--Young equality together with the
-- projection identity `A A⁺ = P_(range A)`.
/-- Proposition 17.36 (7): clause (iii). For a monotone self-adjoint closed-range operator, the
Fenchel conjugate of `q_A` is `ι_(range A) + q_{A⁺}`. -/
theorem quadraticPotentialConjugate_eq_setIndicator_range_add_moorePenroseInverse
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone) (hA_self : IsSelfAdjoint A)
    (hA_closed : IsClosed (A.range : Set H)) :
    (q⋆[A, hA_mono]).asEReal =
      (ι[(A.range : Set H)]).asEReal +
        (q[A⁺[hA_closed]]).toEReal.asEReal :=
  sorry

-- Proof sketch: evaluate the identity from clause (iii) at `A x`, where the range indicator
-- vanishes, then use clause (ii) together with `(A⁺)⁺ = A` for closed-range operators.
/-- Proposition 17.36 (8): clause (iv). For a monotone self-adjoint closed-range operator, the
Fenchel conjugate of `q_A` composed with `A` is `q_A`. -/
theorem conjugate_quadraticPotential_comp_eq_quadraticPotential
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone) (hA_self : IsSelfAdjoint A)
    (hA_closed : IsClosed (A.range : Set H)) :
    (q⋆[A, hA_mono]).asEReal ∘ A = (q[A]).toEReal.asEReal := sorry

end Hilbert

end

end ContinuousLinearMap
