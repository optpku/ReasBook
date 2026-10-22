/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_6
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap18.Proposition_18_7

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Gradient
open scoped InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityOfInfimalConvolutions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [FiniteDimensional ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Corollary 18.8 is the global differentiability consequence for the finite real
  representative of `f □ g` under the source hypotheses on `f`.
- `core/canonical`: the owner abstractions are `Supercoercive f.asEReal`, the Chapter 12 exactness
  and properness owners for `f □ g`, and the pointwise differentiability theorem from Proposition
  18.7.
- `bridge/view`: the source-facing finiteness hypothesis `hfin` is used only to place every
  `x : H` in `dom (f □ g)` through `dom_infimalConvolution`; the proof then routes entirely
  through the existing owner API. -/

-- Proof sketch: Proposition 12.14 gives that the infimal convolution is exact under the
-- supercoercive hypothesis and that a finite-valued representative of `f □ g` belongs to
-- `Γ₀(H)`. Since `f` is finite everywhere, Proposition 12.6(ii) makes the effective domain of
-- `f □ g` all of `H`, so every `x : H` admits a minimizer `y` with
-- `(f □ g) x = f y + g (x - y)`. Apply the finite-dimensional Fréchet conclusion of Proposition
-- 18.7 pointwise, using the Fréchet differentiability of `f` at `y`, and conclude global
-- differentiability.
/-- Corollary 18.8: on a finite-dimensional real Hilbert space, if `f, g ∈ Γ₀(H)`, if `f` is
finite everywhere, supercoercive, and Fréchet differentiable on `H`, then the finite-valued
representative of `f □ g` is Fréchet differentiable on `H`. -/
theorem differentiable_infimalConvolution_toReal_of_mem_gammaZero_of_supercoercive_of_differentiable
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hfin : ∀ x : H, (f x : EReal) < ⊤)
    (hsuper : Supercoercive f.asEReal)
    (hdiff : Differentiable ℝ (fun x ↦ (f x : EReal).toReal)) :
    Differentiable ℝ (fun x ↦ ((f □ g) x).toReal) := by
  intro x
  have _ :
      Supercoercive f.asEReal ∨
        (Coercive f.asEReal ∧ ∃ η : ℝ, ∀ x : H, (η : EReal) ≤ g.asEReal x) :=
    Or.inl hsuper
  have hproper_gamma :
      IsProper (f □ g) ∧ (f □ g) ∈ gamma H :=
    isProper_and_mem_gamma_infimalConvolution_of_supercoercive_or_coercive_bddBelow f g
  have hexact : infimalConvolution.Exact f g :=
    infimalConvolution_exact_of_supercoercive_or_coercive_bddBelow f g
  have hg_nonempty : (effectiveDomain g).Nonempty :=
    (mem_gammaZero_iff.mp hg).2.nonempty
  rcases hg_nonempty with ⟨z, hz⟩
  have hx_dom : x ∈ dom (f □ g) := by
    rw [dom_infimalConvolution f g]
    refine ⟨x - z, mem_effectiveDomain_iff.mpr (hfin (x - z)), z, hz, ?_⟩
    simp [sub_add_cancel]
  rcases hexact hx_dom with ⟨y, hEq⟩
  have hgradAt :
      HasGradientAt (fun z ↦ (f z : EReal).toReal)
        (∇ (fun z ↦ (f z : EReal).toReal) y) y :=
    (hdiff y).hasGradientAt
  have hgateaux :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal)
        (toDualMap ℝ H (∇ (fun z ↦ (f z : EReal).toReal) y)) y :=
    hgradAt.hasFDerivAt.hasGateauxDerivativeAt
  exact differentiableAt_infimalConvolution_of_value_eq_of_hasGateauxDerivativeAt
    hf hg hproper_gamma.1 hproper_gamma.2 hEq hgateaux

end DifferentiabilityOfInfimalConvolutions

end ERealFunction
