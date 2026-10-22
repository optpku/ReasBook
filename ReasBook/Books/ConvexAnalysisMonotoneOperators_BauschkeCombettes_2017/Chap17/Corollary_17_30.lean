/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_29

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

private lemma hasDirectionalDerivativeAt_zero
    {f : ℝ → Set.Ioi (⊥ : EReal)} {x : ℝ} (hx : x ∈ effectiveDomain f) :
    HasDirectionalDerivativeAt f x 0 0 := by
  refine ⟨hx, ?_⟩
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hquot :
      (fun α : ℝ ↦ ((f (x + α • (0 : ℝ)) : EReal) - (f x : EReal)) / α) = fun _ ↦ (0 : EReal) := by
    ext α
    simp [EReal.sub_self hfx_top hfx_bot]
  rw [hquot]
  simp

private lemma hasDirectionalDerivativeAt_mul_pos
    {f : ℝ → Set.Ioi (⊥ : EReal)} {x y : ℝ} {ξ : EReal} {c : ℝ}
    (h : HasDirectionalDerivativeAt f x y ξ) (hc : 0 < c) :
    HasDirectionalDerivativeAt f x (c * y) (ξ * c) := by
  rcases h with ⟨hx, hξ⟩
  refine ⟨hx, ?_⟩
  let q : ℝ → EReal := fun α ↦ ((f (x + α * y) : EReal) - (f x : EReal)) / α
  have htendsto_id :
      Filter.Tendsto id (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) :=
    Filter.tendsto_id
  have hcomp : Filter.Tendsto (fun α : ℝ ↦ q (α * c)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ξ) := by
    refine hξ.comp ?_
    simpa using Filter.TendstoNhdsWithinIoi.mul_const hc htendsto_id
  have hmul : Filter.Tendsto (fun α : ℝ ↦ q (α * c) * c) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ξ * c)) := by
    exact EReal.Tendsto.mul_const hcomp (Or.inr (by simp)) (Or.inr (by simp))
  have hEq : Filter.EventuallyEq (nhdsWithin 0 (Set.Ioi 0))
      (fun α : ℝ ↦ ((f (x + α * (c * y)) : EReal) - (f x : EReal)) / α)
      (fun α ↦ q (α * c) * c) := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro α hα
    have hc0 : c ≠ 0 := hc.ne'
    have hcoeff : ((((α * c : ℝ) : EReal)⁻¹) * c) = ((α : EReal)⁻¹) := by
      rw [← EReal.coe_inv (α * c), ← EReal.coe_mul, ← EReal.coe_inv α]
      exact congrArg (fun t : ℝ ↦ (t : EReal)) <| by
        calc
          (α * c)⁻¹ * c = c / (α * c) := by rw [div_eq_mul_inv, mul_comm]
          _ = α⁻¹ := by simpa [mul_comm] using (div_mul_cancel_left₀ hc0 α)
    calc
      ((f (x + α * (c * y)) : EReal) - (f x : EReal)) / α
          = (((f (x + (α * c) * y) : EReal) - (f x : EReal)) / α) := by ring_nf
      _ = ((f (x + (α * c) * y) : EReal) - (f x : EReal)) * ((α : EReal)⁻¹) := by
        rw [div_eq_mul_inv]
      _ = ((f (x + (α * c) * y) : EReal) - (f x : EReal)) * ((((α * c : ℝ) : EReal)⁻¹) * c) := by
        rw [hcoeff]
      _ = ((((f (x + (α * c) * y) : EReal) - (f x : EReal)) / ((α * c : ℝ) : EReal)) * c) := by
        rw [div_eq_mul_inv]
        exact (mul_assoc _ _ _).symm
      _ = q (α * c) * c := by simp [q]
  exact Filter.Tendsto.congr' hEq.symm hmul

private lemma mul_le_mul_of_pos_right
    {a b : EReal} {c : ℝ} (h : a ≤ b) (hc : 0 < c) :
    a * c ≤ b * c := by
  have hmono := (EReal.strictMono_div_right_of_pos
    (show (0 : EReal) < ((c : EReal)⁻¹) by
      rw [← EReal.coe_inv c]
      exact_mod_cast inv_pos.mpr hc)
    (by
      rw [← EReal.coe_inv c]
      exact EReal.coe_ne_top _)).monotone
  have hcinv : (((c : EReal)⁻¹)⁻¹) = (c : EReal) := by
    rw [EReal.inv_inv] <;> simp
  simpa [div_eq_mul_inv, hcinv] using hmono h

-- Proof sketch: reduce to the one-dimensional specialization of Proposition 17.29. The nonempty
-- effective-domain hypothesis supplies the `ConvexOn` side condition required in this project.
-- The hypothesis on the canonical one-sided derivatives `f′₊` and `f′₋` yields directional
-- derivatives along each segment direction `y - x` and its opposite `x - y`; the comparison
-- `f′₊(x) ≤ f′₋(y)` for `x < y` translates to the antisymmetry inequality required there.
/-- Corollary 17.30: an `]-∞,+∞]`-valued function on `ℝ` is convex on its effective domain if that
domain is a nonempty interval, if the finite-valued restriction is lower semicontinuous on the
effective domain, and if every strict pair `x < y` of effective-domain points admits a right
derivative at `x` and a left derivative at `y` with `f'_+(x) ≤ f'_-(y)`. -/
theorem convexOn_effectiveDomain_of_rightDerivative_le_leftDerivative_of_lt
    (f : ℝ → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain f).Nonempty)
    (hdom_convex : Convex ℝ (effectiveDomain f))
    (hlsc : LowerSemicontinuousOn f.asEReal (effectiveDomain f))
    (honeSided :
      ∀ ⦃x y : ℝ⦄, x ∈ effectiveDomain f → y ∈ effectiveDomain f → x < y →
        HasRightDerivativeAt f x (f′₊(x)) ∧
          HasLeftDerivativeAt f y (f′₋(y)) ∧
          f′₊(x) ≤ f′₋(y)) :
    ConvexOn f (effectiveDomain f) := by
  refine convexOn_effectiveDomain_of_directionalDerivative_antisymmetry f hdom hdom_convex hlsc ?_
  intro x y hx hy
  by_cases hxy : x = y
  · subst hxy
    refine ⟨0, 0, ?_, ?_, by simp⟩
    · simpa using hasDirectionalDerivativeAt_zero hx
    · simpa using hasDirectionalDerivativeAt_zero hx
  · rcases lt_or_gt_of_ne hxy with hxy_lt | hxy_gt
    · rcases honeSided hx hy hxy_lt with ⟨hξ, hη, hle⟩
      have hxy' : 0 < y - x := sub_pos.mpr hxy_lt
      refine ⟨f′₊(x) * (y - x), (-f′₋(y)) * (y - x), ?_, ?_, ?_⟩
      · simpa [HasRightDerivativeAt, one_mul] using hasDirectionalDerivativeAt_mul_pos hξ hxy'
      · convert hasDirectionalDerivativeAt_mul_pos hη hxy' using 1
        ring
      · have hmul : f′₊(x) * (y - x) ≤ f′₋(y) * (y - x) := mul_le_mul_of_pos_right hle hxy'
        simpa [neg_mul] using hmul
    · rcases honeSided hy hx hxy_gt with ⟨hη, hξ, hle⟩
      have hyx : 0 < x - y := sub_pos.mpr hxy_gt
      refine ⟨(-f′₋(x)) * (x - y), f′₊(y) * (x - y), ?_, ?_, ?_⟩
      · convert hasDirectionalDerivativeAt_mul_pos hξ hyx using 1
        ring
      · simpa [HasRightDerivativeAt, one_mul] using hasDirectionalDerivativeAt_mul_pos hη hyx
      · have hbase : f′(x; -1) ≤ -f′₊(y) := by
          rw [EReal.le_neg]
          simpa [leftDerivative] using hle
        have hmul : f′(x; -1) * (x - y) ≤ (-f′₊(y)) * (x - y) :=
          mul_le_mul_of_pos_right hbase hyx
        simpa [neg_mul] using hmul

end ERealFunction
