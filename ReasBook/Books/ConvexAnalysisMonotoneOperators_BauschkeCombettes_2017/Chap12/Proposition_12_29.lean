/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.ProximityOperator
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_26

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: use Proposition 12.26 to rewrite `x = Prox_f x` as the variational inequality
-- `∀ y, f x ≤ f y`, since the inner-product term vanishes at a fixed point. Then identify the
-- latter condition with membership in `Argmin`.
/-- For `f ∈ Γ₀(H)`, a point is fixed by the proximity operator `Prox_f` exactly when it is a
global minimizer of `f`. -/
theorem mem_fixedPoints_proximityOperator_iff_mem_argmin_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H} :
    x ∈ Function.fixedPoints (Prox[f, hf]) ↔ x ∈ Argmin f.asEReal := by
  have hprox : HasUniqueProxPoint f := hasUniqueProxPoint_of_mem_gammaZero f hf
  rw [Function.mem_fixedPoints_iff, mem_argmin_iff, isMinOn_univ_iff]
  constructor
  · intro hx y
    have hx_prox : IsProxPoint f x x := by
      simpa [hprox, hx] using proximityOperator_isProxPoint f hprox x
    simpa using (isProxPoint_iff_forall_inner_add_le f hf.2 x x).1 hx_prox y
  · intro hx
    have hx_prox : IsProxPoint f x x := by
      rw [isProxPoint_iff_forall_inner_add_le f hf.2 x x]
      intro y
      simpa using hx y
    simpa [hprox, eq_comm] using eq_proximityOperator_of_isProxPoint f hprox hx_prox

-- Proof sketch: extensionality reduces the equality of sets to the pointwise characterization
-- above.
/-- Proposition 12.29: for `f ∈ Γ₀(H)`, the fixed points of the proximity operator `Prox_f`
coincide with the global minimizers of `f`. -/
theorem fixedPoints_proximityOperator_eq_argmin_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Function.fixedPoints (Prox[f, hf]) = Argmin f.asEReal := by
  ext x
  exact mem_fixedPoints_proximityOperator_iff_mem_argmin_of_mem_gammaZero hf

end ERealFunction
