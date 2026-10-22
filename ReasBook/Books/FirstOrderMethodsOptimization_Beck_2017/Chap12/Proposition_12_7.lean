/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Remark_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Proposition_12_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u

/- Proposition 12.7 is `source-facing`: it records the norm, adjoint, and coordinatewise proximal
formula for the block model with diagonal map `z ↦ (z, ..., z)` and separable regularizer
`(y₁, ..., y_p) ↦ ∑ i, g (y_i)`.

Domain sampling identifies the existing owners:
- `core/canonical`: Chapter 6 `prox[...]` and `proximal_objective`;
- `core/canonical`: Chapter 6 `PiLp.separableSum`;
- `core/canonical`: Chapter 12 `dual_block_duplication`;
- `bridge/view`: the constant block family `fun _ : Fin p ↦ g`.

Primitive data are therefore only `g` and the block number `p`; the block regularizer and the
duplication map are derived from those owners rather than defined again locally. -/

section Proposition127Part1

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

/- Proposition 12.7 (1): the diagonal duplication operator `𝒜(z) = (z, …, z)` satisfies
`‖𝒜‖² = p`. -/
recall dual_block_duplication_opNorm_sq

end Proposition127Part1

section Proposition127Adjoint

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: use the defining adjoint identity
-- `⟪A z, y⟫ = ⟪z, A† y⟫`, expand the product inner product on `PiLp 2`, and rewrite the left-hand
-- side as `∑ i, ⟪z, y i⟫ = ⟪z, ∑ i, y i⟫`.
/-- Proposition 12.7 (2): the Hilbert adjoint of the diagonal duplication operator sends
`y = (y₁, ..., y_p)` to the block sum `∑ i, y_i`. -/
@[simp]
theorem dual_block_duplication_adjoint_apply
    {p : ℕ} (y : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)) :
    (dual_block_duplication E p).adjoint y =
      ∑ i : Fin p, y i := by
  apply ext_inner_left ℝ
  intro z
  -- Move the adjoint across the inner product so only the duplication map acts on `z`.
  calc
    inner ℝ z ((dual_block_duplication E p).adjoint y) =
        inner ℝ (dual_block_duplication E p z) y := by
          simpa using
            (ContinuousLinearMap.adjoint_inner_right (dual_block_duplication E p) z y)
    _ = ∑ i : Fin p, inner ℝ z (y i) := by
          -- Expand the `PiLp` inner product and simplify each duplicated coordinate to `z`.
          simp [PiLp.inner_apply]
    _ = inner ℝ z (∑ i : Fin p, y i) := by
          -- Reassemble the coordinate sum as the inner product against the block sum.
          simpa using
            (inner_sum (s := Finset.univ) (f := fun i : Fin p ↦ y i) (x := z)).symm

end Proposition127Adjoint

section Proposition127LinearAdjoint

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Companion bridge for Proposition 12.7 (2): the Hilbert adjoint formula for the diagonal
duplication operator, restated for the `LinearMap.adjoint` of the underlying linear map. -/
theorem dual_block_duplication_linear_adjoint_apply
    {p : ℕ} (y : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)) :
    ((dual_block_duplication E p).toLinearMap).adjoint y =
      ∑ i : Fin p, y i := by
  rw [LinearMap.adjoint_eq_toCLM_adjoint]
  change (dual_block_duplication E p).adjoint y = ∑ i : Fin p, y i
  exact dual_block_duplication_adjoint_apply y

end Proposition127LinearAdjoint

section Proposition127Prox

variable {E : Type u} [NormedAddCommGroup E]

-- Verified owner theorem: `prox_separableSum_eq_singleton_iff_coordinatewise`.
-- Proof sketch: specialize that Chapter 6 singleton theorem
-- to the constant block family `fun _ : Fin p ↦ g`.
/-- Proposition 12.7 (3): for the block-separable regularizer
`(y₁, ..., y_p) ↦ ∑ i, g (y_i)`, the Chapter 6 proximal mapping on the Hilbert product is the
tuple of the coordinate proximal points exactly when each coordinate proximal set is the singleton
`{y_i}`. -/
theorem prox_block_separable_regularizer_eq_singleton_iff_coordinatewise
    {p : ℕ} (g : E → EReal) (hg_proper : IsProperExtendedRealFunction g)
    (v y : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)) :
    prox[PiLp.separableSum (fun _ : Fin p ↦ g)] v = {y} ↔
      ∀ i : Fin p, prox[g] (v i) = {y i} := by
  simpa using
    (prox_separableSum_eq_singleton_iff_coordinatewise
      (fun _ : Fin p ↦ g) (fun _ : Fin p ↦ hg_proper) v y)

/-- Helper for Proposition 12.7: the proximal set of the constant block-separable regularizer is
the product of the coordinate proximal sets. -/
theorem prox_block_separable_regularizer_eq_coordinatewise
    {p : ℕ} (g : E → EReal) (hg_proper : IsProperExtendedRealFunction g)
    (v : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)) :
    prox[PiLp.separableSum (fun _ : Fin p ↦ g)] v =
      {y : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E) | ∀ i : Fin p, y i ∈ prox[g] (v i)} := by
  simpa using
    (prox_separableSum_eq_coordinatewise
      (fun _ : Fin p ↦ g) (fun _ : Fin p ↦ hg_proper) v)

end Proposition127Prox
