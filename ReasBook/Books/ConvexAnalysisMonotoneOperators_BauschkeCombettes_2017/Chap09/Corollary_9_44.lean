/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_42

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u v

namespace ERealFunction

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Helper for Corollary 9.44: the recession function vanishes at `0` because every translated
increment `φ (x + 0) - φ x` is zero on the effective domain. -/
lemma recessionFunction_zero
    (φ : K → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain φ).Nonempty) :
    (recessionFunction φ hdom 0 : EReal) = 0 := by
  -- Rewrite the defining supremum as the supremum of the singleton `{0}`.
  rw [recessionFunction_apply]
  have hzero_image :
      ((fun x : K ↦ (φ x : EReal) - (φ x : EReal)) '' effectiveDomain φ) =
        ({0} : Set EReal) := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx_top : (φ x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
      have hx_bot : (φ x : EReal) ≠ ⊥ := ne_of_gt (φ x).2
      have hself : ((φ x : EReal) - (φ x : EReal)) = 0 :=
        EReal.sub_self (x := (φ x : EReal)) hx_top hx_bot
      simp [hself]
    · intro ha
      rcases hdom with ⟨x, hx⟩
      rw [Set.mem_singleton_iff] at ha
      subst a
      have hx_top : (φ x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
      have hx_bot : (φ x : EReal) ≠ ⊥ := ne_of_gt (φ x).2
      have hself : ((φ x : EReal) - (φ x : EReal)) = 0 :=
        EReal.sub_self (x := (φ x : EReal)) hx_top hx_bot
      refine ⟨x, hx, ?_⟩
      simpa [hself]
  simpa [hzero_image]

/-- Helper for Corollary 9.44: the substitution
`x ↦ (⟪x, u⟫_ℝ - ρ, L x - r)` is continuous. -/
lemma continuous_perspective_substitution
    (L : H →L[ℝ] K) (r : K) (u : H) (ρ : ℝ) :
    Continuous (fun x : H ↦ (⟪x, u⟫_ℝ - ρ, L x - r)) := by
  -- The first component is a shifted continuous linear functional.
  have hfst : Continuous (fun x : H ↦ ⟪x, u⟫_ℝ - ρ) := by
    simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      ((InnerProductSpace.toDual ℝ H u).continuous.sub continuous_const)
  -- The second component is `L` followed by translation by `-r`.
  have hsnd : Continuous (fun x : H ↦ L x - r) := L.continuous.sub continuous_const
  -- Continuity of the product map follows componentwise.
  exact hfst.prodMk hsnd

/-- Helper for Corollary 9.44: the substitution map splits into its linear part plus its value at
the origin. -/
lemma perspective_substitution_linear_decomp
    (L : H →L[ℝ] K) (r : K) (u : H) (ρ : ℝ) :
    ∀ x : H,
      (fun y : H ↦ (⟪y, u⟫_ℝ - ρ, L y - r)) x =
        (((InnerProductSpace.toDual ℝ H u).toLinearMap.prod L.toLinearMap) (x -ᵥ (0 : H))) +ᵥ
          (fun y : H ↦ (⟪y, u⟫_ℝ - ρ, L y - r)) 0 := by
  intro x
  -- Expanding the linear part at the origin recovers the affine formula.
  simpa [vsub_eq_sub, vadd_eq_add, LinearMap.prod_apply, sub_eq_add_neg, real_inner_comm]

/-- Helper for Corollary 9.44: the substitution
`x ↦ (⟪x, u⟫_ℝ - ρ, L x - r)` is affine. -/
lemma perspective_substitution_affine
    (L : H →L[ℝ] K) (r : K) (u : H) (ρ : ℝ) :
    ∃ A : H →ᵃ[ℝ] (ℝ × K), (A : H → (ℝ × K)) = fun x ↦ (⟪x, u⟫_ℝ - ρ, L x - r) := by
  -- Package the explicit affine formula into the bundled `AffineMap` expected by Proposition 8.20.
  let A : H →ᵃ[ℝ] (ℝ × K) :=
    AffineMap.mk'
      (fun x : H ↦ (⟪x, u⟫_ℝ - ρ, L x - r))
      (((InnerProductSpace.toDual ℝ H u).toLinearMap.prod L.toLinearMap))
      (0 : H)
      (perspective_substitution_linear_decomp (L := L) (r := r) (u := u) (ρ := ρ))
  exact ⟨A, rfl⟩

/-- Helper for Corollary 9.44: a point in `ξ • effectiveDomain φ` with `ξ ≥ 0` gives a finite
point of the closed perspective. -/
lemma mem_effectiveDomain_closedPerspective_of_mem_smul_effectiveDomain
    (φ : K → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain φ).Nonempty)
    {ξ : ℝ} {y : K} (hξ : 0 ≤ ξ) (hy : y ∈ ξ • effectiveDomain φ) :
    (ξ, y) ∈ effectiveDomain (closedPerspective φ hdom) := by
  by_cases hξ_pos : 0 < ξ
  · rcases Set.mem_smul_set.mp hy with ⟨x, hx, rfl⟩
    -- On the positive slice, the closed perspective agrees with the ordinary perspective.
    rw [mem_effectiveDomain_iff, closedPerspective_coe,
      closedPerspectiveEReal_apply_of_ne_zero (φ := φ) (hdom := hdom) hξ_pos.ne',
      perspective_apply_of_pos (fun z : K ↦ (φ z : EReal)) hξ_pos]
    have hξ_nonnegE : (0 : EReal) ≤ (ξ : EReal) := by
      exact_mod_cast hξ_pos.le
    have hφx_not_top : (φ x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    rw [lt_top_iff_ne_top, EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot ξ), Or.inl hξ_nonnegE, Or.inl (EReal.coe_ne_top ξ), ?_⟩
    exact Or.inr (by simpa [inv_smul_smul₀ hξ_pos.ne'] using hφx_not_top)
  · have hξ_zero : ξ = 0 := le_antisymm (le_of_not_gt hξ_pos) hξ
    have hy_zero : y = 0 := by
      rw [hξ_zero] at hy
      simpa [Set.zero_smul_set hdom] using hy
    -- On the zero slice, the closed perspective becomes the recession function, which is `0` at
    -- the origin.
    rw [hξ_zero, hy_zero, mem_effectiveDomain_iff, closedPerspective_coe,
      closedPerspectiveEReal_apply_zero, recessionFunction_zero]
    simp

-- Proof sketch: Proposition 9.42 places `closedPerspective φ hφ.2.nonempty` in `Γ₀(ℝ × K)`.
-- Pull back
-- lower semicontinuity and convexity along the continuous affine map
-- `x ↦ (⟪x, u⟫_ℝ - ρ, L x - r)`, and use the hypothesis to obtain a point in the
-- effective domain of the composite, hence properness. The assumption
-- `[IsTopologicalAddGroup K]` guarantees that the translation `y ↦ y - r` is continuous, so the
-- second component is a continuous affine map.
/-- Corollary 9.44: if there exists `z` with `ρ ≤ ⟪z, u⟫_ℝ` and
`L z - r ∈ (⟪z, u⟫_ℝ - ρ) • effectiveDomain φ`, then the function obtained from the closed
perspective of `φ` by the substitution `x ↦ (⟪x, u⟫_ℝ - ρ, L x - r)` belongs to `Γ₀(H)`. -/
theorem closedPerspective_comp_mem_gammaZero
    (φ : K → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(K))
    (L : H →L[ℝ] K) (r : K) (u : H) (ρ : ℝ)
    (hz : ∃ z : H, ρ ≤ ⟪z, u⟫_ℝ ∧
      L z - r ∈ (⟪z, u⟫_ℝ - ρ) • effectiveDomain φ) :
    closedPerspective φ hφ.2.nonempty ∘
      (fun x : H ↦ (⟪x, u⟫_ℝ - ρ, L x - r)) ∈ Γ₀(H) := by
  rcases perspective_substitution_affine (L := L) (r := r) (u := u) (ρ := ρ) with ⟨A, hA⟩
  have hA_apply : ∀ x : H, A x = (⟪x, u⟫_ℝ - ρ, L x - r) := by
    intro x
    simpa using congrFun hA x
  have hclosed : closedPerspective φ hφ.2.nonempty ∈ Γ₀(ℝ × K) :=
    closedPerspective_mem_gammaZero φ hφ
  rw [mem_gammaZero_iff] at hclosed ⊢
  constructor
  · -- Lower semicontinuity is preserved by composition with the continuous substitution map.
    have hA_cont : Continuous A := by
      rw [hA]
      exact continuous_perspective_substitution (L := L) (r := r) (u := u) (ρ := ρ)
    have hcomp_lsc :
        LowerSemicontinuous (fun x : H ↦ (closedPerspective φ hφ.2.nonempty (A x) : EReal)) :=
      hclosed.1.comp hA_cont
    simpa [Function.comp, hA_apply] using hcomp_lsc
  · refine ⟨?_, subset_rfl, ?_⟩
    · rcases hz with ⟨z, hz_inner, hz_dom⟩
      have hz_nonneg : 0 ≤ ⟪z, u⟫_ℝ - ρ := sub_nonneg.mpr hz_inner
      have hz_closed :
          (⟪z, u⟫_ℝ - ρ, L z - r) ∈ effectiveDomain (closedPerspective φ hφ.2.nonempty) :=
        mem_effectiveDomain_closedPerspective_of_mem_smul_effectiveDomain
          (φ := φ) (hdom := hφ.2.nonempty) hz_nonneg hz_dom
      -- The hypothesis produces one point in the effective domain of the composite.
      refine ⟨z, ?_⟩
      simpa [effectiveDomain, dom, Function.comp, hA_apply z] using hz_closed
    · intro x hx y hy α hα hα_lt_one
      have hx_closed : A x ∈ effectiveDomain (closedPerspective φ hφ.2.nonempty) := by
        simpa [effectiveDomain, Function.comp, hA_apply x] using hx
      have hy_closed : A y ∈ effectiveDomain (closedPerspective φ hφ.2.nonempty) := by
        simpa [effectiveDomain, Function.comp, hA_apply y] using hy
      have hmap :
          α • A x + (1 - α) • A y = A (α • x + (1 - α) • y) := by
        simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
          (A.apply_lineMap y x α).symm
      have hineq := hclosed.2.ineq hx_closed hy_closed hα hα_lt_one
      -- Rewrite the affine-combined argument back into the bundled map `A`, then unfold `A`
      -- pointwise to recover the explicit substitution formula.
      rw [hmap] at hineq
      simpa [Function.comp, hA_apply (α • x + (1 - α) • y), hA_apply x, hA_apply y] using hineq

end ERealFunction
