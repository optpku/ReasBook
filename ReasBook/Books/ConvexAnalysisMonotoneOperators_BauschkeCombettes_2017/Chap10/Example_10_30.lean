/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_27

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open ERealFunction

variable {H : Type u} [AddCommMonoid H] [Module ℝ H]

private theorem convexCombo_le_max {a u v : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    a * u + (1 - a) * v ≤ max u v := by
  by_cases huv : u ≤ v
  · have h1a_nonneg : 0 ≤ 1 - a := sub_nonneg.mpr ha1.le
    calc
      a * u + (1 - a) * v ≤ a * v + (1 - a) * v := by
        gcongr
      _ = v := by ring
      _ = max u v := by simp [huv]
  · have hvu : v ≤ u := le_of_not_ge huv
    have h1a_nonneg : 0 ≤ 1 - a := sub_nonneg.mpr ha1.le
    calc
      a * u + (1 - a) * v ≤ a * u + (1 - a) * u := by
        gcongr
      _ = u := by ring
      _ = max u v := by simp [hvu]

/-- Example 10.30 (1): composing a strictly quasiconvex real-valued function with a strictly
increasing function on its range preserves strict quasiconvexity. -/
-- Proof sketch: apply the strict quasiconvex inequality for `f.toEReal` to the
-- strict convex combination of `x` and `y`, then transport that strict inequality through the
-- strictly increasing range map `φ ∘ Set.rangeFactorization f`.
theorem strictlyQuasiconvex_comp_strictMono_range
    {f : H → ℝ} {φ : Set.range f → ℝ}
    (hf : StrictlyQuasiconvex f.toEReal.asEReal)
    (hφ : StrictMono φ) :
    StrictlyQuasiconvex (φ ∘ Set.rangeFactorization f).toEReal.asEReal := by
  let ψ : H → ℝ := φ ∘ Set.rangeFactorization f
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ⟨0, ?_⟩⟩
    · intro x
      simp
    · simp [ERealFunction.dom]
  · intro x y _ _ hxy α hα0 hα1
    have hstrict :
        (((f (α • x + (1 - α) • y) : ℝ) : EReal)) <
          max ((f x : ℝ) : EReal) ((f y : ℝ) : EReal) := by
      simpa [Function.toEReal_apply, Function.asEReal_apply] using
        hf.ineq (by simp [ERealFunction.dom]) (by simp [ERealFunction.dom]) hxy hα0 hα1
    by_cases hxy' : f x ≤ f y
    · have hz_lt_yE : (((f (α • x + (1 - α) • y) : ℝ) : EReal)) < ((f y : ℝ) : EReal) := by
        have hmax :
            max ((f x : ℝ) : EReal) ((f y : ℝ) : EReal) = ((f y : ℝ) : EReal) := by
          exact max_eq_right (by exact_mod_cast hxy')
        rwa [hmax] at hstrict
      have hz_lt_y : f (α • x + (1 - α) • y) < f y := by
        exact_mod_cast hz_lt_yE
      have hψ_zy : ψ (α • x + (1 - α) • y) < ψ y := hφ hz_lt_y
      have hψ_zyE : (((ψ (α • x + (1 - α) • y) : ℝ) : EReal)) < ((ψ y : ℝ) : EReal) := by
        exact_mod_cast hψ_zy
      exact lt_of_lt_of_le hψ_zyE (le_max_right _ _)
    · have hyx' : f y ≤ f x := le_of_not_ge hxy'
      have hz_lt_xE : (((f (α • x + (1 - α) • y) : ℝ) : EReal)) < ((f x : ℝ) : EReal) := by
        have hmax :
            max ((f x : ℝ) : EReal) ((f y : ℝ) : EReal) = ((f x : ℝ) : EReal) := by
          exact max_eq_left (by exact_mod_cast hyx')
        rwa [hmax] at hstrict
      have hz_lt_x : f (α • x + (1 - α) • y) < f x := by
        exact_mod_cast hz_lt_xE
      have hψ_zx : ψ (α • x + (1 - α) • y) < ψ x := hφ hz_lt_x
      have hψ_zxE : (((ψ (α • x + (1 - α) • y) : ℝ) : EReal)) < ((ψ x : ℝ) : EReal) := by
        exact_mod_cast hψ_zx
      exact lt_of_lt_of_le hψ_zxE (le_max_left _ _)

/-- Example 10.30 (2): if an increasing function on the range of `f` yields a strictly convex
composition, then the original real-valued function is strictly quasiconvex. -/
-- Proof sketch: the `IsProper` field for `f.toEReal` is automatic, since a real-valued function
-- is finite everywhere. Strict convexity of the composition gives a strict
-- Jensen inequality on `univ`. Bound the weighted average of the endpoint values by their maximum,
-- then use monotonicity of `φ ∘ Set.rangeFactorization f` to descend the strict inequality back
-- to the values of `f`.
theorem strictlyQuasiconvex_of_strictConvexOn_comp_range
    {f : H → ℝ} {φ : Set.range f → ℝ} (hφ : Monotone φ)
    (hcomp : StrictConvexOn ℝ Set.univ (φ ∘ Set.rangeFactorization f)) :
    StrictlyQuasiconvex f.toEReal.asEReal := by
  let ψ : H → ℝ := φ ∘ Set.rangeFactorization f
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ⟨0, ?_⟩⟩
    · intro x
      simp
    · simp [ERealFunction.dom]
  · intro x y _ _ hxy α hα0 hα1
    have h1α0 : 0 < 1 - α := sub_pos.mpr hα1
    have hα_sum : α + (1 - α) = 1 := by ring
    have hψ_strict :
        ψ (α • x + (1 - α) • y) < α * ψ x + (1 - α) * ψ y := by
      exact hcomp.2 (by simp) (by simp) hxy hα0 h1α0 hα_sum
    by_cases hxy' : f x ≤ f y
    · have hψ_xy : ψ x ≤ ψ y := hφ hxy'
      have hψ_avg : α * ψ x + (1 - α) * ψ y ≤ ψ y := by
        calc
          α * ψ x + (1 - α) * ψ y ≤ max (ψ x) (ψ y) := convexCombo_le_max hα0 hα1
          _ = ψ y := by simp [hψ_xy]
      have hψ_zy : ψ (α • x + (1 - α) • y) < ψ y :=
        lt_of_lt_of_le hψ_strict hψ_avg
      have hz_lt_y : f (α • x + (1 - α) • y) < f y := by
        by_contra hz_ge_y
        exact not_le_of_gt hψ_zy (hφ (le_of_not_gt hz_ge_y))
      have hz_lt_yE : (((f (α • x + (1 - α) • y) : ℝ) : EReal)) < ((f y : ℝ) : EReal) := by
        exact_mod_cast hz_lt_y
      exact lt_of_lt_of_le hz_lt_yE (le_max_right _ _)
    · have hyx' : f y ≤ f x := le_of_not_ge hxy'
      have hψ_yx : ψ y ≤ ψ x := hφ hyx'
      have hψ_avg : α * ψ x + (1 - α) * ψ y ≤ ψ x := by
        calc
          α * ψ x + (1 - α) * ψ y ≤ max (ψ x) (ψ y) := convexCombo_le_max hα0 hα1
          _ = ψ x := by simp [hψ_yx]
      have hψ_zx : ψ (α • x + (1 - α) • y) < ψ x :=
        lt_of_lt_of_le hψ_strict hψ_avg
      have hz_lt_x : f (α • x + (1 - α) • y) < f x := by
        by_contra hz_ge_x
        exact not_le_of_gt hψ_zx (hφ (le_of_not_gt hz_ge_x))
      have hz_lt_xE : (((f (α • x + (1 - α) • y) : ℝ) : EReal)) < ((f x : ℝ) : EReal) := by
        exact_mod_cast hz_lt_x
      exact lt_of_lt_of_le hz_lt_xE (le_max_left _ _)
