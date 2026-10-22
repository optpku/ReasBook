/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Corollary_3_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Theorem_6_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient InnerProductSpace Pointwise Set

universe u

local instance : OfNat (Set.Ioi (0 : ℝ)) 1 := ⟨⟨1, by
  change (0 : ℝ) < 1
  norm_num
⟩⟩

namespace ERealFunction

section MoreauDecomposition

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: specialize Theorem 14.3 (1) to the unit parameter `γ = 1`, so that both Moreau
-- envelopes are regularized by the kernel `q = (1 / 2) ‖·‖²`.
/-- Remark 14.4 (1): for `f ∈ Γ₀(H)` and `q = (1 / 2) ‖·‖²`, Moreau's decomposition gives
`(f □ q) + (f^* □ q) = q`, written here as an identity between the unit Moreau envelopes of `f`
and `f^*` and the unit quadratic kernel. -/
theorem moreauEnvelope_add_conjugateMoreauEnvelope_eq_unitMoreauQuadraticKernel
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    ({}^[1] f) + ({}^[1] (gammaZeroConjugate f hf)) =
      (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal := sorry

-- Proof sketch: specialize Theorem 14.3 (2) to `γ = 1` and identify the resulting unit scaled
-- proximal operators with the ordinary proximal operators of `f` and `f^*`.
/-- Remark 14.4 (2): for `f ∈ Γ₀(H)`, Moreau's decomposition gives the operator identity
`Prox_f + Prox_{f^*} = Id`. -/
theorem proximityOperator_add_conjugateProximityOperator_eq_id_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Prox[f, hf] + Prox⋆[f, hf] = id := sorry

-- Proof sketch: combine Proposition 12.30 at the unit parameter with Remark 14.4 (2), which
-- rewrites the residual map `Id - Prox_f` as the gradient of the unit Moreau envelope.
/-- Remark 14.4 (3): using Proposition 12.30, the proximal operator is the residual
`Id - ∇ (f □ q)` of the gradient of the unit Moreau envelope. -/
theorem proximityOperator_eq_id_sub_gradient_moreauEnvelope_toReal_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Prox[f, hf] =
      id - ∇ (fun y : H ↦ (({}^[1] f) y).toReal) := sorry

-- Proof sketch: apply Proposition 12.30 to `f^*`, use `γ = 1`, and substitute the identity from
-- Remark 14.4 (2) to replace `Id - Prox_{f^*}` by `Prox_f`.
/-- Remark 14.4 (4): using Proposition 12.30, the proximal operator of `f` is also the gradient of
the unit Moreau envelope of `f^*`. -/
theorem proximityOperator_eq_gradient_conjugateMoreauEnvelope_toReal_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Prox[f, hf] =
      ∇ (fun y : H ↦ (({}^[1] (gammaZeroConjugate f hf)) y).toReal) :=
  sorry

end MoreauDecomposition

end ERealFunction

section

open ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- For a proper cone, the Chebyshev theorem for the negative polar reads equally as the
Chebyshev theorem for the textbook polar-cone notation `Kᵒ⊖`. -/
theorem isChebyshev_polarCone_of_properCone (K : ProperCone ℝ H) :
    IsChebyshev ((K : Set H)ᵒ⊖) := by
  rw [Set.polarCone_eq_innerDual_neg]
  simpa [Set.negativePolar] using isChebyshev_negativePolar K

-- Proof sketch: specialize Theorem 6.30 (1) from its pointwise form to a function equality. This
-- is exactly the conical decomposition recovered from Remark 14.4 by taking `f = ι_K`.
/-- Remark 14.4 (5): when `f = ι_K` for a nonempty closed convex cone `K`, Moreau's decomposition
recovers the conical identity `P_K + P_{Kᵒ⊖} = Id`. -/
theorem projectionPoint_add_projectionPoint_negativePolar_eq_id
    (K : ProperCone ℝ H) :
    projectionPoint (K : Set H) (isChebyshev_of_properCone K) +
        projectionPoint ((K : Set H)ᵒ⊖) (isChebyshev_polarCone_of_properCone K) =
      id := by
  have hpolar : ((K : Set H)ᵒ⊖ : Set H) = Set.negativePolar (K : Set H) := by
    rw [Set.polarCone_eq_innerDual_neg]
  ext x
  simpa [hpolar, isChebyshev_polarCone_of_properCone] using
    (eq_projectionPoint_add_projectionPoint_negativePolar K x).symm

-- Proof sketch: combine Corollary 3.24's distance formulas
-- `d(x,V) = ‖P_{Vᗮ} x‖` and `d(x,Vᗮ) = ‖P_V x‖` with the Pythagorean identity
-- `‖x‖² = ‖P_V x‖² + ‖P_{Vᗮ} x‖²`.
/-- Remark 14.4 (6): if `V` is a closed linear subspace, then the squared distances to `V` and
`Vᗮ` add up to the squared norm: `d_V^2 + d_{Vᗮ}^2 = ‖·‖^2`. -/
theorem sq_infDist_add_sq_infDist_orthogonal_eq_norm_sq
    (V : ClosedSubmodule ℝ H) :
    (fun x : H ↦ Metric.infDist x (V : Set H) ^ 2 + Metric.infDist x (Vᗮ : Set H) ^ 2) =
      fun x : H ↦ ‖x‖ ^ 2 := by
  ext x
  rw [infDist_eq_norm_orthogonalProjection_orthogonal V x,
    infDist_orthogonal_eq_norm_orthogonalProjection V x]
  simpa [add_comm] using
    (norm_sq_eq_add_norm_sq_orthogonalProjection V x).symm

-- Proof sketch: rewrite Corollary 3.24 (7), namely `P_{Vᗮ} = Id - P_V`, into the equivalent
-- projector decomposition `P_V + P_{Vᗮ} = Id`.
/-- Remark 14.4 (7): if `V` is a closed linear subspace, then the orthogonal projectors satisfy
`P_V + P_{Vᗮ} = Id`. -/
theorem starProjection_add_starProjection_orthogonal_eq_one
    (V : ClosedSubmodule ℝ H) :
    V.starProjection + Vᗮ.starProjection = 1 := by
  ext x
  change V.starProjection x + Vᗮ.starProjection x = x
  exact (V : Submodule ℝ H).starProjection_add_starProjection_orthogonal x

end
