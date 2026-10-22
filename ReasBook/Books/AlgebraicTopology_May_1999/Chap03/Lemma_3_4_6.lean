/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Pointwise
open QuotientGroup

variable {G : Type u} [Group G] {H K : Subgroup G}

/-- Lemma 3.4.6: a `G`-equivariant map `α : G ⧸ H → G ⧸ K` is determined by the image of the base
coset `eH`; if `α(eH) = γK`, then `α(gH) = gγK` for every `g : G`. -/
-- Proof sketch: every coset `gH` is `g • eH`, so equivariance gives
-- `α (gH) = g • α (eH) = g • γK`, and the quotient action identifies `g • γK` with `(g * γ)K`.
theorem quotient_mulActionHom_apply_coe_eq_coe_mul_of_apply_one
    (α : G ⧸ H →[G] G ⧸ K) (γ : G) (g : G)
    (hα : α ((1 : G) : G ⧸ H) = (γ : G ⧸ K)) :
    α (g : G ⧸ H) = ((g * γ : G) : G ⧸ K) := by
  -- Rewrite `gH` as `g • eH` and use equivariance to move `g` through `α`.
  calc
    α (g : G ⧸ H) = α (g • ((1 : G) : G ⧸ H)) := by simp
    _ = (g : G) • α ((1 : G) : G ⧸ H) := by
      simpa using α.map_smul g (((1 : G) : G ⧸ H))
    -- Substitute the prescribed value of `α(eH)` and simplify the quotient action.
    _ = ((g * γ : G) : G ⧸ K) := by
      simp [hα]

/-- Helper for Lemma 3.4.6: evaluating a `G`-equivariant map `G ⧸ H → G ⧸ K` at the identity
coset gives an `H`-fixed point of `G ⧸ K`. -/
theorem quotient_mulActionHom_apply_one_mem_fixedPoints (α : G ⧸ H →[G] G ⧸ K) :
    α ((1 : G) : G ⧸ H) ∈ MulAction.fixedPoints H (G ⧸ K) := by
  rw [MulAction.mem_fixedPoints]
  intro h
  -- The identity coset of `G ⧸ H` is fixed by every element of `H`.
  have hh : (h : G) • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
    simpa using
      (QuotientGroup.eq.mpr (show ((h : G)⁻¹ * 1) ∈ H by
        simp [H.inv_mem h.2]) : ((h : G) : G ⧸ H) = ((1 : G) : G ⧸ H))
  -- Transport that fixed-point relation across the equivariant map `α`.
  calc
    (h : G) • α ((1 : G) : G ⧸ H) = α ((h : G) • ((1 : G) : G ⧸ H)) := by
      symm
      simpa using α.map_smul (h : G) (((1 : G) : G ⧸ H))
    _ = α ((1 : G) : G ⧸ H) := by
      simp [hh]

/-- Helper for Lemma 3.4.6: if a `G`-equivariant map `G ⧸ H → G ⧸ K` sends `eH` to `γK`, then
`γ⁻¹ H γ` is contained in `K`. -/
-- Proof sketch: `α(eH)` is `H`-fixed by `quotient_mulActionHom_apply_one_mem_fixedPoints`.
-- Instantiating the fixed-point condition on the representative `γK` at `h⁻¹ ∈ H` yields
-- `(h⁻¹ * γ)K = γK`, and rewriting equality of left cosets gives `γ⁻¹ * h * γ ∈ K`.
theorem subgroup_map_conj_inv_le_of_quotient_mulActionHom_apply_one
    (α : G ⧸ H →[G] G ⧸ K) (γ : G)
    (hα : α ((1 : G) : G ⧸ H) = (γ : G ⧸ K)) :
    MulAut.conj γ⁻¹ • H ≤ K := by
  -- Replace `α(eH)` by `γK` in the fixed-point statement coming from equivariance.
  have hfixed : (γ : G ⧸ K) ∈ MulAction.fixedPoints H (G ⧸ K) := by
    simpa [hα] using quotient_mulActionHom_apply_one_mem_fixedPoints α
  rw [Subgroup.pointwise_smul_def]
  rintro _ ⟨h, hh, rfl⟩
  -- Apply fixedness to `h⁻¹ ∈ H` so that the resulting coset equality reads `(h⁻¹ * γ)K = γK`.
  have hq : (((h⁻¹ : G) * γ : G) : G ⧸ K) = (γ : G ⧸ K) := by
    simpa using (MulAction.mem_fixedPoints.1 hfixed ⟨h⁻¹, H.inv_mem hh⟩)
  -- Convert equality of left cosets into the desired conjugacy membership statement.
  simpa [MulAut.conj_apply, mul_assoc] using
    (show γ⁻¹ * h * γ ∈ K by
      simpa [mul_assoc] using (QuotientGroup.eq.mp hq))
