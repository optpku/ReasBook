/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_17
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section HilbertSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) (p : Set.Ici (1 : ℝ))

-- Proof sketch: specialize Proposition 12.14 to `normPowerKernel p γ`. This places
-- `normPowerEnvelope f p γ` in `gamma H`; combine that with Proposition 12.9 (1),
-- `dom (normPowerEnvelope f p γ) = Set.univ`, to rewrite convexity on the effective domain as
-- convexity on all of `H` and then pass to `toReal`.
/-- Proposition 12.15 (1): if `f ∈ Γ₀(H)`, `γ ∈ ℝ_{++}`, and `p > 1`, then the real-valued
representative of the `p`-power envelope is convex on `H`. -/
theorem convexOn_univ_toReal_normPowerEnvelope_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (hp : (1 : ℝ) < p) :
    _root_.ConvexOn ℝ Set.univ (fun x : H ↦ (normPowerEnvelope f p γ x).toReal) := sorry

-- Proof sketch: Proposition 12.14 excludes the value `-∞` by putting the envelope in `gamma H`,
-- while Proposition 12.9 (1) excludes the value `+∞` by identifying the domain with `Set.univ`.
/-- Proposition 12.15 (2): if `f ∈ Γ₀(H)`, `γ ∈ ℝ_{++}`, and `p > 1`, then the `p`-power
envelope is real-valued at every point of `H`. -/
theorem normPowerEnvelope_mem_Ioo_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (hp : (1 : ℝ) < p) (x : H) :
    normPowerEnvelope f p γ x ∈ Set.Ioo (⊥ : EReal) ⊤ := sorry

-- Proof sketch: combine the global convexity from clause (1) with the real-valuedness from clause
-- (2) and apply the Chapter 8 local boundedness-to-continuity principle for convex real-valued
-- functions.
/-- Proposition 12.15 (3): if `f ∈ Γ₀(H)`, `γ ∈ ℝ_{++}`, and `p > 1`, then the real-valued
representative of the `p`-power envelope is continuous on `H`. -/
theorem continuous_toReal_normPowerEnvelope_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (hp : (1 : ℝ) < p) :
    Continuous (fun x : H ↦ (normPowerEnvelope f p γ x).toReal) := sorry

-- Proof sketch: Proposition 12.14 gives exact attainment for the translated sum, while Example
-- 8.23 makes the `p`-power kernel strictly convex for `p > 1`; Corollary 11.16 then upgrades the
-- translated objective to a unique global minimizer. We record the result using the canonical
-- exactness owner `infimalConvolution.ExactAt` together with the canonical minimizer set `Argmin`.
/-- Proposition 12.15 (4): for `f ∈ Γ₀(H)`, `γ ∈ ℝ_{++}`, `p > 1`, and every `x ∈ H`, the
infimal convolution defining the `p`-power regularization is exact at `x`, and the translated
objective `y ↦ f y + ‖x - y‖^p / (γ p)` has a unique global minimizer. -/
theorem exactAt_and_existsUnique_mem_argmin_normPowerEnvelope_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (hp : (1 : ℝ) < p)
    (x : H) :
    infimalConvolution.ExactAt f (normPowerKernel p γ) x ∧
      ∃! y : H,
        y ∈ Argmin
          (fun z : H ↦ (f z : EReal) + (normPowerKernel p γ (x - z) : EReal)) := sorry

end HilbertSpace

end ERealFunction
