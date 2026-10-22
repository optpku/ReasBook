/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
private theorem toEReal_toReal_eq {f : H → Set.Ioi (⊥ : EReal)} {x : H}
    (hx : x ∈ effectiveDomain f) :
    (Function.toEReal (fun y : H ↦ (f y : EReal).toReal) x : EReal) = (f x : EReal) := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
  simp [Function.toEReal_apply, EReal.coe_toReal hx_top hx_bot]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
private theorem coe_toReal_eq {f : H → Set.Ioi (⊥ : EReal)} {x : H}
    (hx : x ∈ effectiveDomain f) :
    (((f x : EReal).toReal : ℝ) : EReal) = (f x : EReal) := by
  exact EReal.coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hx)) (ne_of_gt (f x).2)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
private theorem weightedJensenSum_ne_top {f : H → Set.Ioi (⊥ : EReal)} {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) ≠ ⊤ := by
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hα_nonneg : 0 ≤ (α : EReal) := by
    exact_mod_cast hα0.le
  have h1α0 : 0 < 1 - α := by
    linarith
  have h1α_nonneg : 0 ≤ (1 - α : EReal) := by
    exact_mod_cast h1α0.le
  have hα_mul_ne_top : (α : EReal) * (f x : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot α), Or.inl hα_nonneg, Or.inl (EReal.coe_ne_top α),
      Or.inr hfx_top⟩
  have h1α_mul_ne_top : (1 - α : EReal) * (f y : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (1 - α)), Or.inl h1α_nonneg,
      Or.inl (EReal.coe_ne_top (1 - α)), Or.inr hfy_top⟩
  exact EReal.add_ne_top hα_mul_ne_top h1α_mul_ne_top

/-- A source-facing strongly convex `]-∞,+∞]`-valued function yields the canonical mathlib
strong-convexity statement for its finite real representative on the effective domain. -/
theorem StronglyConvex.toStrongConvexOn_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ} (hf : StronglyConvex f β) :
    StrongConvexOn (effectiveDomain f) β (fun x ↦ (f x : EReal).toReal) := by
  let g : H → ℝ := fun x ↦ (f x : EReal).toReal
  have hconv : ConvexOn f (effectiveDomain f) := hf.uniformlyConvex.convexOn
  have hC : Convex ℝ (effectiveDomain f) := hconv.convex_effectiveDomain
  have hfU :
      UniformlyConvexOn f (effectiveDomain f) (strongConvexityModulus β) := by
    simpa [UniformlyConvex] using hf.uniformlyConvex
  have hgU :
      UniformlyConvexOn g.toEReal (effectiveDomain f) (strongConvexityModulus β) := by
    refine ⟨hfU.nonempty, ?_, hfU.monotone, hfU.modulus_eq_zero_iff, ?_⟩
    · intro x hx
      simp [Function.effectiveDomain_toEReal]
    · intro x hx y hy α hα0 hα1
      have hxy : α • x + (1 - α) • y ∈ effectiveDomain f := by
        exact hC hx hy hα0.le (sub_nonneg.mpr hα1.le) (by ring)
      simpa [strongConvexityModulus, g, jensenGap, Function.toEReal_apply, coe_toReal_eq hx,
        coe_toReal_eq hy, coe_toReal_eq hxy] using hfU.gap_le hx hy hα0 hα1
  simpa [StrongConvexOn, strongConvexityModulus, g] using
    UniformlyConvexOn.toUniformConvexOn hC hgU

/-- The canonical mathlib strong-convexity statement for the finite representative on the effective
domain recovers the source-facing strong convexity of the original `]-∞,+∞]`-valued function. -/
theorem StrongConvexOn.toStronglyConvex_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ}
    (hf : StrongConvexOn (effectiveDomain f) β (fun x ↦ (f x : EReal).toReal))
    (hβ : 0 < β) (hdom : (effectiveDomain f).Nonempty) :
    StronglyConvex f β := by
  let g : H → ℝ := fun x ↦ (f x : EReal).toReal
  have hreal :
      UniformConvexOn (effectiveDomain f) (fun r : ℝ ↦ β / 2 * r ^ (2 : ℕ)) g := by
    simpa [StrongConvexOn, g] using hf
  have hC : Convex ℝ (effectiveDomain f) := hreal.1
  have hgU :
      UniformlyConvexOn g.toEReal (effectiveDomain f) (strongConvexityModulus β) := by
    refine ⟨hdom, ?_, strongConvexityModulus_monotone hβ,
      strongConvexityModulus_eq_zero_iff hβ, ?_⟩
    · intro x hx
      simp [Function.effectiveDomain_toEReal]
    · intro x hx y hy α hα0 hα1
      have hα_nonneg : 0 ≤ α := hα0.le
      have h1α_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα1.le
      have hα_sum : α + (1 - α) = 1 := by ring
      have hbase :
          g (α • x + (1 - α) • y) ≤
            α * g x + (1 - α) * g y - α * (1 - α) * (β / 2 * ‖x - y‖ ^ (2 : ℕ)) := by
        simpa using hreal.2 hx hy hα_nonneg h1α_nonneg hα_sum
      have hineq :
          g (α • x + (1 - α) • y) + α * (1 - α) * (β / 2 * ‖x - y‖ ^ (2 : ℕ)) ≤
            α * g x + (1 - α) * g y := by
        linarith
      have hineqE :
          (((g (α • x + (1 - α) • y) + α * (1 - α) * (β / 2 * ‖x - y‖ ^ (2 : ℕ)) : ℝ) :
            EReal)) ≤ (((α * g x + (1 - α) * g y : ℝ) : EReal)) := by
        exact_mod_cast hineq
      have hx_dom : x ∈ effectiveDomain g.toEReal := by
        simp [Function.effectiveDomain_toEReal]
      have hy_dom : y ∈ effectiveDomain g.toEReal := by
        simp [Function.effectiveDomain_toEReal]
      have hcombo_ne_bot : (g.toEReal (α • x + (1 - α) • y) : EReal) ≠ ⊥ :=
        ne_of_gt (g.toEReal _).2
      have hsum_ne_top :
          (α : EReal) * (g.toEReal x : EReal) + (1 - α : EReal) * (g.toEReal y : EReal) ≠ ⊤ :=
        weightedJensenSum_ne_top hx_dom hy_dom hα0 hα1
      have hgap :
          ((α * (1 - α) : ℝ) : EReal) * strongConvexityModulus β ‖x - y‖₊ ≤
            (α : EReal) * (g.toEReal x : EReal) + (1 - α : EReal) * (g.toEReal y : EReal) -
              (g.toEReal (α • x + (1 - α) • y) : EReal) := by
        rw [EReal.le_sub_iff_add_le (Or.inl hcombo_ne_bot) (Or.inr hsum_ne_top)]
        simpa [strongConvexityModulus, Function.toEReal_apply, EReal.coe_add, EReal.coe_mul,
          mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hineqE
      simpa [jensenGap] using hgap
  have hfU :
      UniformlyConvexOn f (effectiveDomain f)
        (strongConvexityModulus β) := by
    refine ⟨hdom, ?_, hgU.monotone, hgU.modulus_eq_zero_iff, ?_⟩
    · intro x hx
      exact hx
    · intro x hx y hy α hα0 hα1
      have hxy : α • x + (1 - α) • y ∈ effectiveDomain f := by
        exact hC hx hy hα0.le (sub_nonneg.mpr hα1.le) (by ring)
      simpa [strongConvexityModulus, g, jensenGap, Function.toEReal_apply, coe_toReal_eq hx,
        coe_toReal_eq hy, coe_toReal_eq hxy] using hgU.gap_le hx hy hα0 hα1
  exact (show UniformlyConvex f (strongConvexityModulus β) from
      by simpa [UniformlyConvex] using hfU).stronglyConvex hβ

-- Proof sketch: transfer the source-facing `StronglyConvex` statement to the finite real
-- representative on `effectiveDomain f`, apply mathlib's owner theorem
-- `strongConvexOn_iff_convex`, and transfer the result back.
/-- Proposition 10.8: a proper `]-∞,+∞]`-valued function is strongly convex with constant `β` iff
its finite representative on the effective domain becomes convex after subtracting
`(β / 2)‖·‖²`. -/
theorem stronglyConvex_iff_convexOn_toReal_sub_sq
    {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ} (hdom : (effectiveDomain f).Nonempty) :
    StronglyConvex f β ↔
      0 < β ∧
        _root_.ConvexOn ℝ (effectiveDomain f)
          (fun x ↦ (f x : EReal).toReal - β / 2 * ‖x‖ ^ (2 : ℕ)) := by
  constructor
  · intro hf
    refine ⟨hf.pos, ?_⟩
    exact (strongConvexOn_iff_convex).1 hf.toStrongConvexOn_effectiveDomain
  · rintro ⟨hβ, hconv⟩
    have hstrong :
        StrongConvexOn (effectiveDomain f) β (fun x ↦ (f x : EReal).toReal) := by
      exact (strongConvexOn_iff_convex).2 hconv
    exact StrongConvexOn.toStronglyConvex_effectiveDomain hstrong hβ hdom

end

end ERealFunction
