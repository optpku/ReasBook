/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_45
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap18.Proposition_18_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap18.Proposition_18_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityOfInfimalConvolutions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {f g : H → Set.Ioi (⊥ : EReal)}
variable {x y gradf : H}

section

variable [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 18.7 asserts that an exact minimizer `y` for `f □ g` forces the
  canonical finite-valued representative of the infimal convolution to be continuous at `x` in the
  textbook sense `x ∈ cont (...)`, and then differentiable there with gradient `gradf`.
- `core/canonical`: the owner abstractions are the raw infimal convolution `f □ g`, its properness
  and `Γ(H)` membership, the source continuity set `cont`, `∂`, and `HasGateauxDerivativeAt`.
- `bridge/view`: `properIoi (f □ g) hproper` is the canonical `Γ₀(H)` repackaging of the raw owner,
  and `ContinuousAtOnEffectiveDomain.of_mem_cont` is used internally to feed the Chapter 16/17
  differentiability bridge.

Primitive data vs. derived API:
- primitive data: `IsProper (f □ g)`, `(f □ g) ∈ Γ(H)`, the exactness witness `hEq`, and the
  Gâteaux derivative of `f` at the minimizing point `y`;
- derived API: `x ∈ cont (properIoi (f □ g) hproper)`, then Gâteaux differentiability of the
  finite real representative of `f □ g` at `x`. -/

-- Proof sketch: Proposition 17.50 places `y` in `interior (effectiveDomain f)`. The exact
-- equality `hEq` then forces `x - y ∈ effectiveDomain g`, so Proposition 12.6 identifies `x`
-- with a point of `effectiveDomain f + effectiveDomain g`. Since `y` is already an interior point
-- of `effectiveDomain f`, the same sum identity puts `x` in `interior (effectiveDomain (f □ g))`.
-- Repackage the raw owner through `properIoi (f □ g) hproper`, then Corollary 8.39 identifies that
-- interior-domain membership with the source continuity predicate
-- `x ∈ cont (properIoi (f □ g) hproper)`.
/-- The canonical `Γ₀(H)` repackaging of `f □ g` is continuous at every exact infimal convolution
point `x` arising from a Gâteaux differentiability point `y` of `f`, in the source sense
`x ∈ cont (...)`. -/
theorem mem_cont_properIoi_infimalConvolution_of_value_eq_of_hasGateauxDerivativeAt
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hproper : IsProper (f □ g)) (hgamma : (f □ g) ∈ Γ(H))
    (hEq : (f □ g) x = (f y : EReal) + (g (x - y) : EReal))
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H gradf) y) :
    x ∈ cont (properIoi (f □ g) hproper) := sorry

-- Proof sketch: the previous theorem supplies
-- `x ∈ cont (properIoi (f □ g) hproper)`, hence
-- `ContinuousAtOnEffectiveDomain (properIoi (f □ g) hproper) x`. Proposition 16.27 then places
-- `x` in the subdifferential domain of that canonical repackaging, which is definitionally the
-- subdifferential domain of `f □ g`; Proposition 18.6 identifies `∂ (f □ g) x` with the singleton
-- `{gradf}`. Proposition 17.31 then yields the Gâteaux derivative of the finite representative of
-- `f □ g` at `x`.
/-- Proposition 18.7: if `f, g ∈ Γ₀(H)`, if the raw infimal convolution `f □ g` is proper and lies
in `Γ(H)`, if it is exact at `x` with minimizer `y`, and if `f` has Gâteaux gradient `gradf` at
`y`, then the finite real representative of `f □ g` inherits the same Gâteaux gradient at `x`. -/
theorem hasGateauxDerivativeAt_infimalConvolution_of_value_eq_of_hasGateauxDerivativeAt
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hproper : IsProper (f □ g)) (hgamma : (f □ g) ∈ Γ(H))
    (hEq : (f □ g) x = (f y : EReal) + (g (x - y) : EReal))
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H gradf) y) :
    HasGateauxDerivativeAt
      (fun z ↦ ((f □ g) z).toReal) (toDualMap ℝ H gradf) x := sorry

end

section

variable [CompleteSpace H] [FiniteDimensional ℝ H]

-- Proof sketch: Proposition 18.6 again gives the singleton subdifferential
-- `∂ (f □ g) x = {gradf}`, and the source continuity theorem above gives
-- `x ∈ cont (properIoi (f □ g) hproper)`, hence an interior effective-domain point of the
-- canonical `Γ₀(H)` repackaging of `f □ g`. Proposition 17.45 then upgrades the resulting Gâteaux
-- differentiability to the finite-dimensional Fréchet-gradient owner `HasGradientAt`.
/-- Finite-dimensional Fréchet-gradient companion to Proposition 18.7. -/
theorem hasGradientAt_infimalConvolution_of_value_eq_of_hasGateauxDerivativeAt
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hproper : IsProper (f □ g)) (hgamma : (f □ g) ∈ Γ(H))
    (hEq : (f □ g) x = (f y : EReal) + (g (x - y) : EReal))
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H gradf) y) :
    HasGradientAt (fun z ↦ ((f □ g) z).toReal) gradf x := sorry

/-- Finite-dimensional Fréchet-differentiability companion to Proposition 18.7. -/
theorem differentiableAt_infimalConvolution_of_value_eq_of_hasGateauxDerivativeAt
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hproper : IsProper (f □ g)) (hgamma : (f □ g) ∈ Γ(H))
    (hEq : (f □ g) x = (f y : EReal) + (g (x - y) : EReal))
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H gradf) y) :
    DifferentiableAt ℝ (fun z ↦ ((f □ g) z).toReal) x := sorry

end

end DifferentiabilityOfInfimalConvolutions

end ERealFunction
