/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_25

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u

namespace ERealFunction

section Function

variable {H : Type u} [SMul ℝ H]

/-- The extended-real function attached to a set `C`, sending `(ξ, x)` to `ξ` when `ξ > 0` and
`x ∈ ξ • C`, and to `+∞` otherwise. -/
noncomputable def positiveScalingIndicator (C : Set H) : ℝ × H → EReal :=
  fun p ↦
    @ite EReal (0 < p.1 ∧ p.2 ∈ p.1 • C)
      (Classical.propDecidable (0 < p.1 ∧ p.2 ∈ p.1 • C)) (p.1 : EReal) ⊤

end Function

section Convexity

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- Helper for Example 8.32: for a positive scalar, membership in the scaled set is equivalent to
membership of the normalized point in the original set. -/
lemma mem_smul_set_iff_inv_smul_mem_pos {C : Set H} {ξ : ℝ} (hξ : 0 < ξ) {x : H} :
    x ∈ ξ • C ↔ ξ⁻¹ • x ∈ C := by
  -- This is the standard pointwise-set normalization for nonzero scalars.
  simpa using (Set.mem_smul_set_iff_inv_smul_mem₀ hξ.ne' C x)

omit [AddCommGroup H] [Module ℝ H] in
/-- Helper for Example 8.32: on points of `C`, the function `1 + ι_{Cᶜ}` takes the value `1`. -/
private lemma one_add_indicator_eq_one_of_mem {C : Set H} {x : H} (hx : x ∈ C) :
    (1 : EReal) + indicator Cᶜ (fun _ : H ↦ (⊤ : EReal)) x = 1 := by
  -- Membership in `C` forces the complement indicator to vanish.
  simp [hx]

omit [AddCommGroup H] [Module ℝ H] in
/-- Helper for Example 8.32: outside `C`, the function `1 + ι_{Cᶜ}` takes the value `⊤`. -/
private lemma one_add_indicator_eq_top_of_not_mem {C : Set H} {x : H} (hx : x ∉ C) :
    (1 : EReal) + indicator Cᶜ (fun _ : H ↦ (⊤ : EReal)) x = ⊤ := by
  -- Outside `C`, the complement indicator contributes `⊤`.
  have hindicator : indicator Cᶜ (fun _ : H ↦ (⊤ : EReal)) x = ⊤ := by
    simp [hx]
  simpa [hindicator] using (EReal.coe_add_top (1 : ℝ))

-- Proof sketch: for `ξ > 0`, rewrite `x ∈ ξ • C` as `ξ⁻¹ • x ∈ C`, so the indicator term
-- `indicator Cᶜ (fun _ ↦ ⊤)` vanishes exactly on the admissible points; the nonpositive branch is
-- `⊤` on both sides by definition of `perspective`.
/-- Helper for Example 8.32: the set-scaling function is the perspective of `1 + ι_{Cᶜ}`. -/
theorem positiveScalingIndicator_eq_perspective_one_add_indicator (C : Set H) :
    positiveScalingIndicator C =
      perspective (fun x ↦ (1 : EReal) + indicator Cᶜ (fun _ : H ↦ (⊤ : EReal)) x) := by
  funext p
  rcases p with ⟨ξ, x⟩
  by_cases hξ : 0 < ξ
  · have hmem : x ∈ ξ • C ↔ ξ⁻¹ • x ∈ C :=
      mem_smul_set_iff_inv_smul_mem_pos (C := C) hξ
    -- On the positive branch, the admissible points are exactly those where the complement
    -- indicator vanishes after normalization.
    rw [perspective_apply_of_pos _ hξ]
    by_cases hx : ξ⁻¹ • x ∈ C
    · -- When the normalized point lies in `C`, both sides reduce to the finite value `ξ`.
      rw [one_add_indicator_eq_one_of_mem hx]
      simp [positiveScalingIndicator, hξ, hx, hmem]
    · -- Outside `C`, the indicator contributes `⊤`, so the positive branch evaluates to `⊤`.
      rw [one_add_indicator_eq_top_of_not_mem hx]
      simp [positiveScalingIndicator, hξ, hx, hmem, EReal.coe_mul_top_of_pos hξ]
  · have hξ_nonpos : ξ ≤ 0 := le_of_not_gt hξ
    -- At nonpositive height, both definitions take the `⊤` branch.
    rw [perspective_apply_of_nonpos _ hξ_nonpos]
    simp [positiveScalingIndicator, hξ]

omit [AddCommGroup H] [Module ℝ H] in
/-- Helper for Example 8.32: the epigraph of `1 + ι_{Cᶜ}` is exactly `C ×ˢ Ici 1`. -/
private lemma mem_epigraph_one_add_indicator_iff {C : Set H} {x : H} {t : ℝ} :
    (x, t) ∈ epigraph (fun x : H ↦ (1 : EReal) + indicator Cᶜ (fun _ : H ↦ (⊤ : EReal)) x) ↔
      x ∈ C ∧ 1 ≤ t := by
  constructor
  · intro hp
    by_cases hx : x ∈ C
    · -- On `C`, the epigraph inequality is exactly the lower bound `1 ≤ t`.
      constructor
      · exact hx
      · rw [mem_epigraph_iff] at hp
        have hle : ((1 : ℝ) : EReal) ≤ (t : EReal) := by
          rw [one_add_indicator_eq_one_of_mem hx] at hp
          simpa using hp
        exact EReal.coe_le_coe_iff.mp hle
    · -- Outside `C`, the function value is `⊤`, which no real epigraph height can dominate.
      rw [mem_epigraph_iff, one_add_indicator_eq_top_of_not_mem hx] at hp
      exact False.elim (EReal.coe_ne_top t (top_le_iff.mp hp))
  · rintro ⟨hx, ht⟩
    -- Once `x ∈ C`, the epigraph condition is the real inequality `1 ≤ t`.
    rw [mem_epigraph_iff]
    simpa [one_add_indicator_eq_one_of_mem hx] using
      (EReal.coe_le_coe ht : ((1 : ℝ) : EReal) ≤ (t : EReal))

omit [AddCommGroup H] [Module ℝ H] in
/-- Helper for Example 8.32: the epigraph of `1 + ι_{Cᶜ}` is exactly `C ×ˢ Ici 1`. -/
lemma epigraph_one_add_indicator_eq_prod_Ici (C : Set H) :
    epigraph (fun x : H ↦ (1 : EReal) + indicator Cᶜ (fun _ : H ↦ (⊤ : EReal)) x) =
      C ×ˢ Set.Ici (1 : ℝ) := by
  ext p
  rcases p with ⟨x, t⟩
  -- The previous membership lemma is exactly the product-set description.
  simpa [Set.mem_prod, Set.mem_Ici] using
    (mem_epigraph_one_add_indicator_iff (C := C) (x := x) (t := t))

/-- Helper for Example 8.32: if `C` is convex, then `1 + ι_{Cᶜ}` has convex epigraph. -/
lemma convex_epigraph_one_add_indicator (C : Set H) (hC : Convex ℝ C) :
    Convex ℝ (epigraph (fun x : H ↦ (1 : EReal) + indicator Cᶜ (fun _ : H ↦ (⊤ : EReal)) x)) := by
  -- The explicit epigraph description turns the problem into convexity of a product set.
  rw [epigraph_one_add_indicator_eq_prod_Ici C]
  exact hC.prod (convex_Ici (1 : ℝ))

-- Proof sketch: rewrite the function as the perspective of `1 + ι_{Cᶜ}` using the previous
-- theorem, then apply Proposition 8.25 to that base function, whose epigraph is convex when `C` is
-- convex.
/-- Example 8.32: if `C` is convex, then the function sending `(ξ, x)` to `ξ` for `ξ > 0` and
`x ∈ ξ • C`, and to `+∞` otherwise, has convex epigraph on `ℝ × H`. -/
theorem convex_epigraph_positiveScalingIndicator (C : Set H) (hC : Convex ℝ C) :
    Convex ℝ (epigraph (positiveScalingIndicator C)) := by
  -- Rewrite the textbook function as the perspective from Proposition 8.25.
  rw [positiveScalingIndicator_eq_perspective_one_add_indicator]
  -- The base function has the product epigraph `C ×ˢ Ici 1`, hence a convex epigraph.
  exact convex_epigraph_perspective _ (convex_epigraph_one_add_indicator C hC)

end Convexity

end ERealFunction
