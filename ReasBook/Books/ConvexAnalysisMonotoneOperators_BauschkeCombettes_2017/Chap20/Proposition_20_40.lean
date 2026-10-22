/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped InnerProductSpace

universe u

namespace SetValuedOperator

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: evaluate the `y = 0` term in the defining supremum; since `0 : D`, the supremum
-- is bounded below by the real value `0`, hence it is strictly above `⊥`.
/-- The supremum defining `supremalPotential D T` always lies in `]-∞,+∞]`. -/
private theorem supremalPotential_mem_Ioi
    (D : Submodule ℝ H) (T : D →ₗ[ℝ] H) (x : H) :
    (⊥ : EReal) <
      ⨆ y : D, (((⟪x, T y⟫_ℝ - (1 / 2 : ℝ) * ⟪(y : H), T y⟫_ℝ) : ℝ) : EReal) := sorry

/-- The function `h` from Proposition 20.40, attached to a linear map `T` defined on a subspace
`D`, equal to `(1 / 2) ⟪x, T x⟫_ℝ` on `D` and `+∞` off `D`. -/
noncomputable def domainQuadraticPotential
    (D : Submodule ℝ H) (T : D →ₗ[ℝ] H) : H → Set.Ioi (⊥ : EReal) :=
  let _ : DecidablePred fun x : H ↦ x ∈ D := Classical.decPred fun x : H ↦ x ∈ D
  fun x ↦
    if hx : x ∈ D then
      ⟨(((1 / 2 : ℝ) * ⟪x, T ⟨x, hx⟩⟫_ℝ) : EReal), EReal.bot_lt_coe _⟩
    else
      ⟨⊤, show (⊥ : EReal) < ⊤ from bot_lt_iff_ne_bot.mpr top_ne_bot⟩

-- Proof sketch: unfold `domainQuadraticPotential`; on `D` the definition takes the finite
-- quadratic value associated with `T`.
/-- On the subspace `D`, `domainQuadraticPotential D T` equals `(1 / 2) ⟪x, T x⟫_ℝ`. -/
@[simp] theorem domainQuadraticPotential_apply_of_mem
    (D : Submodule ℝ H) (T : D →ₗ[ℝ] H) {x : H} (hx : x ∈ D) :
    (domainQuadraticPotential D T x : EReal) =
      (((1 / 2 : ℝ) * ⟪x, T ⟨x, hx⟩⟫_ℝ) : EReal) := sorry

-- Proof sketch: unfold `domainQuadraticPotential`; off `D` the definition is the constant value
-- `⊤`.
/-- Outside the subspace `D`, `domainQuadraticPotential D T` equals `+∞`. -/
@[simp] theorem domainQuadraticPotential_apply_of_not_mem
    (D : Submodule ℝ H) (T : D →ₗ[ℝ] H) {x : H} (hx : x ∉ D) :
    (domainQuadraticPotential D T x : EReal) = ⊤ := sorry

/-- The function `f` from Proposition 20.40, defined as the supremum of the affine defects
`⟪x, T y⟫_ℝ - h(y)` over `y ∈ D`. -/
noncomputable def supremalPotential
    (D : Submodule ℝ H) (T : D →ₗ[ℝ] H) : H → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    ⟨⨆ y : D, (((⟪x, T y⟫_ℝ - (1 / 2 : ℝ) * ⟪(y : H), T y⟫_ℝ) : ℝ) : EReal),
      supremalPotential_mem_Ioi D T x⟩

-- Proof sketch: unfold `supremalPotential`; its coercion to `EReal` is the defining supremum.
/-- Coercing `supremalPotential D T x` to `EReal` recovers the displayed supremum over `D`. -/
@[simp] theorem supremalPotential_apply
    (D : Submodule ℝ H) (T : D →ₗ[ℝ] H) (x : H) :
    (supremalPotential D T x : EReal) =
      ⨆ y : D, (((⟪x, T y⟫_ℝ - (1 / 2 : ℝ) * ⟪(y : H), T y⟫_ℝ) : ℝ) : EReal) := sorry

section LinearSingleValuedOperators

variable (D : Submodule ℝ H) (T : D →ₗ[ℝ] H)

-- Proof sketch: identify `A` with the graph of `T` on `D`, rewrite monotonicity of `A` as the
-- quadratic inequality for `T`, and compare the supremum defining `f` with the value at `y = x`
-- and with the monotonicity bound obtained from `0 ≤ ⟪x - y, T x - T y⟫`.
/-- Proposition 20.40 (1): if `A = ofFunction D T` is monotone and `T` is symmetric on `D`, then
the supremal potential `f` satisfies `f + ι_D = h`. -/
theorem supremalPotential_add_indicator_eq_domainQuadraticPotential
    (hsymm : ∀ x y : D, ⟪(x : H), T y⟫_ℝ = ⟪T x, (y : H)⟫_ℝ)
    (hT_mono : (ofFunction (D : Set H) T).IsMonotone) :
    (supremalPotential D T).asEReal + (ι[(D : Set H)]).asEReal =
      (domainQuadraticPotential D T).asEReal := sorry

-- Proof sketch: each term in the defining supremum of `f` is a continuous affine `EReal`-valued
-- function of `x`, so Proposition 9.3 gives membership in `Γ(H)` for the supremum. Properness
-- comes from the value at `0 ∈ D`, which is `0`, and clause (1) identifies the indicator-corrected
-- function with `h`.
/-- Proposition 20.40 (2): if `A = ofFunction D T` is monotone and `T` is symmetric on `D`, then
the supremal potential belongs to `Γ₀(H)`. -/
theorem supremalPotential_mem_gammaZero_of_monotone
    (hsymm : ∀ x y : D, ⟪(x : H), T y⟫_ℝ = ⟪T x, (y : H)⟫_ℝ)
    (hT_mono : (ofFunction (D : Set H) T).IsMonotone) :
    supremalPotential D T ∈ Γ₀(H) := sorry

-- Proof sketch: for `x ∈ D`, clause (1) gives `f x = h x`, so the affine minorant inequality with
-- slope `T x` is exactly the defining supremum bound; hence `T x ∈ ∂ f(x)` and the graph of
-- `A = ofFunction D T` is contained in `gra ∂f`. Maximal monotonicity of `A`, together with the
-- monotonicity of `∂f` from Example 20.3, forces equality of the two operators.
/-- Proposition 20.40 (3): if `A = ofFunction D T` is maximally monotone and `T` is symmetric on
`D`, then the subdifferential of the supremal potential is exactly `A`. -/
theorem subdifferential_supremalPotential_eq
    (hsymm : ∀ x y : D, ⟪(x : H), T y⟫_ℝ = ⟪T x, (y : H)⟫_ℝ)
    (hT_max : Maximal IsMonotone (ofFunction (D : Set H) T)) :
    ∂ (supremalPotential D T) = ofFunction (D : Set H) T := sorry

-- Proof sketch: clause (2) puts `f` in `Γ₀(H)`, so Corollary 16.41 identifies `f` with the
-- biconjugate of `f` plus the indicator of its subdifferentiability domain. Clause (3) rewrites
-- that domain as `D`, and clause (1) identifies the resulting function with `h`.
/-- Proposition 20.40 (4): if `A = ofFunction D T` is maximally monotone and `T` is symmetric on
`D`, then the supremal potential is the Fenchel biconjugate of `h`. -/
theorem supremalPotential_eq_biconjugate_domainQuadraticPotential
    (hsymm : ∀ x y : D, ⟪(x : H), T y⟫_ℝ = ⟪T x, (y : H)⟫_ℝ)
    (hT_max : Maximal IsMonotone (ofFunction (D : Set H) T)) :
    (supremalPotential D T).asEReal = (domainQuadraticPotential D T).asEReal∗∗ := sorry

end LinearSingleValuedOperators

end

end SetValuedOperator
