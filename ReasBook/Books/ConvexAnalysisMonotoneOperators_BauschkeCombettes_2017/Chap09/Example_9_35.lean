/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_34

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set
open scoped Topology

namespace ERealFunction

attribute [local instance] Classical.propDecidable

/-- The `]-∞,+∞]`-valued extension of `x ↦ x \log x - x` that equals `0` at `0` and `+∞` on the
negative half-line. -/
noncomputable def boltzmannEntropy : ℝ → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    if 0 < x then
      ⟨((x * Real.log x - x : ℝ) : EReal), EReal.bot_lt_coe _⟩
    else if x = 0 then
      ⟨(0 : EReal), EReal.bot_lt_coe 0⟩
    else
      ⟨(⊤ : EReal), Set.mem_Ioi.mpr bot_lt_top⟩

-- Proof sketch: unfold `boltzmannEntropy`; the positivity hypothesis selects the first branch, and
-- coercing from `Set.Ioi (⊥ : EReal)` to `EReal` removes the proof field.
/-- On `(0,+∞)`, `boltzmannEntropy` is given by the real formula `x \log x - x`. -/
@[simp] theorem boltzmannEntropy_apply_of_pos {x : ℝ} (hx : 0 < x) :
    (boltzmannEntropy x : EReal) = ((x * Real.log x - x : ℝ) : EReal) := by
  -- The positive branch of the defining `if` is active at `x`.
  simp [boltzmannEntropy, hx]

-- Proof sketch: unfold `boltzmannEntropy`; `0` does not satisfy the positive branch, and the
-- second branch is exactly the prescribed value `0`.
/-- At `0`, `boltzmannEntropy` takes the value `0`. -/
@[simp] theorem boltzmannEntropy_apply_zero :
    (boltzmannEntropy 0 : EReal) = 0 := by
  -- At the origin the piecewise definition selects the middle branch.
  simp [boltzmannEntropy]

-- Proof sketch: unfold `boltzmannEntropy`; a negative argument fails both the positive and zero
-- tests, so the final `+∞` branch applies.
/-- On `(-∞,0)`, `boltzmannEntropy` takes the value `+∞`. -/
@[simp] theorem boltzmannEntropy_apply_of_neg {x : ℝ} (hx : x < 0) :
    (boltzmannEntropy x : EReal) = ⊤ := by
  -- A negative argument reaches the last branch of the definition.
  simp [boltzmannEntropy, not_lt.mpr hx.le, hx.ne]

-- Proof sketch: combine the three branch formulas. Positive and zero inputs give finite real
-- values, while negative inputs give `+∞`, so the effective domain is exactly `[0,+∞)`.
/-- The effective domain of `boltzmannEntropy` is the closed half-line `[0,+∞)`. -/
theorem effectiveDomain_boltzmannEntropy :
    effectiveDomain boltzmannEntropy = Set.Ici (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    by_cases hxneg : x < 0
    · -- Negative points are excluded because the value is `+∞`.
      have htop : (boltzmannEntropy x : EReal) = ⊤ := boltzmannEntropy_apply_of_neg hxneg
      exact False.elim <| by
        rw [mem_effectiveDomain_iff, htop] at hx
        exact (lt_irrefl (⊤ : EReal)) hx
    · -- Every nonnegative point lies in `[0,+∞)`.
      exact le_of_not_gt hxneg
  · intro hx
    rw [mem_effectiveDomain_iff]
    by_cases hx0 : x = 0
    · -- At the origin the value is `0`, hence finite.
      simp [hx0]
    · -- Positive points use the finite real branch.
      have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      simpa [boltzmannEntropy_apply_of_pos hxpos] using
        (EReal.coe_lt_top (x * Real.log x - x))

-- Proof sketch: the subtype codomain already excludes the value `-∞`; the point `0` belongs to
-- the domain because `boltzmannEntropy 0 = 0`, so the effective domain is nonempty.
/-- `boltzmannEntropy` is proper as an extended-real-valued function. -/
theorem boltzmannEntropy_isProper :
    IsProper (fun x : ℝ ↦ (boltzmannEntropy x : EReal)) := by
  refine ⟨?_, ⟨0, ?_⟩⟩
  · -- The codomain `Set.Ioi (⊥)` rules out the value `-∞` everywhere.
    intro x
    exact ne_of_gt (show (⊥ : EReal) < (boltzmannEntropy x : EReal) from (boltzmannEntropy x).2)
  · -- The point `0` lies in the ordinary domain because the value there is finite.
    simp [dom, boltzmannEntropy_apply_zero]

/-- Helper for Example 9.35: the finite branch on `]0,+∞[` viewed as an `]-∞,+∞]`-valued
function and extended by `+∞` off the interval. -/
private noncomputable def boltzmannEntropyOpenInterval : ℝ → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    if x ∈ erealOpenInterval (0 : EReal) ⊤ then
      ⟨((x * Real.log x - x : ℝ) : EReal), EReal.bot_lt_coe _⟩
    else
      ⟨(⊤ : EReal), Set.mem_Ioi.mpr bot_lt_top⟩

/-- Helper for Example 9.35: on the open interval `]0,+∞[`, the auxiliary function agrees with the
finite formula `x \log x - x`. -/
@[simp] private theorem boltzmannEntropyOpenInterval_apply_of_mem {x : ℝ}
    (hx : x ∈ erealOpenInterval (0 : EReal) ⊤) :
    (boltzmannEntropyOpenInterval x : EReal) = ((x * Real.log x - x : ℝ) : EReal) := by
  -- Inside the interval, the first branch of the auxiliary definition is active.
  simp [boltzmannEntropyOpenInterval, hx]

/-- Helper for Example 9.35: the effective domain of the open-interval auxiliary function is
exactly `]0,+∞[`. -/
private theorem effectiveDomain_boltzmannEntropyOpenInterval :
    effectiveDomain boltzmannEntropyOpenInterval = erealOpenInterval (0 : EReal) ⊤ := by
  ext x
  by_cases hx : x ∈ erealOpenInterval (0 : EReal) ⊤
  · -- On the interval the auxiliary function takes a finite real value.
    rw [mem_effectiveDomain_iff]
    simpa [boltzmannEntropyOpenInterval, hx] using
      (EReal.coe_lt_top (x * Real.log x - x))
  · -- Off the interval the auxiliary function is `+∞`, hence outside the effective domain.
    rw [mem_effectiveDomain_iff]
    simp [boltzmannEntropyOpenInterval, hx]

/-- Helper for Example 9.35: the right-hand liminf of the open-interval auxiliary function at `0`
is exactly `0`. -/
private theorem boltzmannEntropyOpenInterval_zero_liminf_eq_zero :
    Filter.liminf (fun y : ℝ ↦ (boltzmannEntropyOpenInterval y : EReal))
      (nhdsWithin 0 (Set.Ioi 0)) = 0 := by
  have hEq :
      (fun y : ℝ ↦ (boltzmannEntropyOpenInterval y : EReal)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        fun y : ℝ ↦ ((y * Real.log y - y : ℝ) : EReal) := by
    -- Along the right-sided filter every point already belongs to `]0,+∞[`.
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hmem : y ∈ erealOpenInterval (0 : EReal) ⊤ := by
      simpa [erealOpenInterval] using hy
    simp [boltzmannEntropyOpenInterval, hmem]
  have hcont :
      Continuous fun y : ℝ ↦ ((y * Real.log y - y : ℝ) : EReal) := by
    -- The finite branch is continuous as a real function, then continuous after coercion to
    -- `EReal`.
    exact continuous_coe_real_ereal.comp (Real.continuous_mul_log.sub continuous_id)
  have htendsto :
      Tendsto (fun y : ℝ ↦ ((y * Real.log y - y : ℝ) : EReal))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (((0 : ℝ) : EReal))) := by
    -- The continuity at `0` yields the right-sided limit.
    have hcw :
        ContinuousWithinAt (fun y : ℝ ↦ ((y * Real.log y - y : ℝ) : EReal))
          (Set.Ioi 0) 0 :=
      hcont.continuousAt.continuousWithinAt
    simpa [ContinuousWithinAt] using hcw
  calc
    Filter.liminf (fun y : ℝ ↦ (boltzmannEntropyOpenInterval y : EReal))
        (nhdsWithin 0 (Set.Ioi 0))
      = Filter.liminf (fun y : ℝ ↦ ((y * Real.log y - y : ℝ) : EReal))
          (nhdsWithin 0 (Set.Ioi 0)) :=
        Filter.liminf_congr hEq
    _ = 0 := htendsto.liminf_eq

/-- Helper for Example 9.35: the left-endpoint liminf needed by Proposition 9.34 is strictly above
`-∞`. -/
private theorem boltzmannEntropyOpenInterval_zero_liminf_gt_bot (x : ℝ)
    (hx : (0 : EReal) = (x : EReal)) :
    ⊥ < Filter.liminf (fun y : ℝ ↦ (boltzmannEntropyOpenInterval y : EReal))
      (nhdsWithin x (Set.Ioi x)) := by
  -- The endpoint condition forces `x = 0`, and the exact liminf value is `0`.
  have hx0 : x = 0 := by
    have hx0' : 0 = x := by
      exact_mod_cast hx
    exact hx0'.symm
  subst x
  rw [boltzmannEntropyOpenInterval_zero_liminf_eq_zero]
  exact EReal.bot_lt_coe 0

/-- Helper for Example 9.35: the right endpoint `β = ⊤` never equals the coercion of a real
number, so the corresponding liminf hypothesis is vacuous. -/
private theorem liminf_gt_bot_of_eq_top_right
    (g : ℝ → Set.Ioi (⊥ : EReal)) (x : ℝ) (hx : (⊤ : EReal) = (x : EReal)) :
    ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Iio x)) := by
  -- A real number never coerces to `⊤`.
  exact False.elim (EReal.top_ne_coe x hx)

/-- Helper for Example 9.35: the open-interval auxiliary function is strictly convex on its
effective domain `]0,+∞[`. -/
private theorem boltzmannEntropyOpenInterval_strictlyConvex :
    StrictlyConvex boltzmannEntropyOpenInterval := by
  have hkl :
      StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x ↦ InformationTheory.klFun x - 1) := by
    -- On `]0,+∞[`, strict convexity comes from the standard KL-function and translation by a
    -- constant.
    have h0 :
        StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) InformationTheory.klFun :=
      InformationTheory.strictConvexOn_klFun.subset (by
        intro x hx
        have hx' : 0 < x := by
          simpa [Set.mem_Ioi] using hx
        simpa [Set.mem_Ici] using hx'.le) (convex_Ioi 0)
    simpa [sub_eq_add_neg] using h0.add_const (-1 : ℝ)
  have hreal :
      StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x ↦ x * Real.log x - x) := by
    -- Route correction: reuse the canonical strict-convexity theorem for `klFun` instead of
    -- rebuilding a derivative argument locally.
    refine hkl.congr ?_
    intro x hx
    have hEq : InformationTheory.klFun x - 1 = x * Real.log x - x := by
      rw [InformationTheory.klFun_apply]
      ring
    simpa using hEq
  intro x hx y hy hxy α hα0 hα1
  rw [effectiveDomain_boltzmannEntropyOpenInterval] at hx hy
  have hxpos : 0 < x := by
    simpa [erealOpenInterval] using hx
  have hypos : 0 < y := by
    simpa [erealOpenInterval] using hy
  have hβ0 : 0 < 1 - α := by
    linarith
  have hcombo_pos : 0 < α * x + (1 - α) * y := by
    nlinarith
  have hreal_ineq :
      ((α * x + (1 - α) * y) * Real.log (α * x + (1 - α) * y) -
          (α * x + (1 - α) * y) : ℝ) <
        α * (x * Real.log x - x) + (1 - α) * (y * Real.log y - y) := by
    simpa [smul_eq_mul, sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using
      hreal.2 hxpos hypos hxy hα0 hβ0 (by ring : α + (1 - α) = 1)
  have hcombo_mem : α • x + (1 - α) • y ∈ erealOpenInterval (0 : EReal) ⊤ := by
    rw [mem_erealOpenInterval_iff]
    constructor
    · exact_mod_cast hcombo_pos
    · exact EReal.coe_lt_top _
  -- Translate the strict real Jensen inequality into the `EReal`-valued formulation.
  have hineq_ereal :
      (((α * x + (1 - α) * y) * Real.log (α * x + (1 - α) * y) -
          (α * x + (1 - α) * y) : ℝ) : EReal) <
        (α : EReal) * (((x * Real.log x - x : ℝ) : EReal)) +
          (1 - α : EReal) * (((y * Real.log y - y : ℝ) : EReal)) := by
    exact_mod_cast hreal_ineq
  calc
    (boltzmannEntropyOpenInterval (α • x + (1 - α) • y) : EReal)
      = (((α * x + (1 - α) * y) * Real.log (α * x + (1 - α) * y) -
            (α * x + (1 - α) * y) : ℝ) : EReal) := by
          simpa [smul_eq_mul] using boltzmannEntropyOpenInterval_apply_of_mem hcombo_mem
    _ < (α : EReal) * (((x * Real.log x - x : ℝ) : EReal)) +
          (1 - α : EReal) * (((y * Real.log y - y : ℝ) : EReal)) :=
        hineq_ereal
    _ = (α : EReal) * (boltzmannEntropyOpenInterval x : EReal) +
          (1 - α : EReal) * (boltzmannEntropyOpenInterval y : EReal) := by
          simp [boltzmannEntropyOpenInterval_apply_of_mem hx,
            boltzmannEntropyOpenInterval_apply_of_mem hy]

/-- Helper for Example 9.35: the piecewise textbook definition agrees with the one-sided-limit
extension from Proposition 9.34. -/
private theorem boltzmannEntropy_eq_oneSidedLimitExtension :
    boltzmannEntropy =
      oneSidedLimitExtension boltzmannEntropyOpenInterval 0 ⊤
        (fun {x} hx ↦ boltzmannEntropyOpenInterval_zero_liminf_gt_bot x hx)
        (fun {x} hx ↦ liminf_gt_bot_of_eq_top_right boltzmannEntropyOpenInterval x hx) := by
  funext x
  apply Subtype.ext
  by_cases hxpos : 0 < x
  · -- On the interior interval, both definitions agree with the finite branch.
    have hmem : x ∈ erealOpenInterval (0 : EReal) ⊤ := by
      simpa [erealOpenInterval] using hxpos
    rw [oneSidedLimitExtension_coe]
    simp [oneSidedLimitExtensionEReal, hmem, boltzmannEntropy_apply_of_pos hxpos,
      boltzmannEntropyOpenInterval_apply_of_mem]
  · by_cases hx0 : x = 0
    · -- At the left endpoint, the extension inserts the computed right liminf `0`.
      subst x
      rw [oneSidedLimitExtension_coe]
      simp [oneSidedLimitExtensionEReal, boltzmannEntropy_apply_zero,
        boltzmannEntropyOpenInterval_zero_liminf_eq_zero, erealOpenInterval]
    · -- Outside `[0,+∞)`, both definitions are `+∞`.
      have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx0
      have hxnotmem : x ∉ erealOpenInterval (0 : EReal) ⊤ := by
        intro h
        rw [mem_erealOpenInterval_iff] at h
        exact (not_lt.mpr (show (x : EReal) ≤ 0 by exact_mod_cast hxneg.le)) h.1
      have hxzero : ¬ (0 : EReal) = (x : EReal) := by
        intro h
        have h0 : x = 0 := by
          have h0' : 0 = x := by
            exact_mod_cast h
          exact h0'.symm
        exact hx0 h0
      have hxtop : ¬ (⊤ : EReal) = (x : EReal) := by
        exact EReal.top_ne_coe x
      rw [oneSidedLimitExtension_coe]
      simp [oneSidedLimitExtensionEReal, boltzmannEntropy_apply_of_neg hxneg, hxnotmem, hxzero,
        hxtop]

/-- Helper for Example 9.35: the extension identification and Proposition 9.34 place
`boltzmannEntropy` in `Γ₀(ℝ)`. -/
private theorem boltzmannEntropy_mem_gammaZero_aux :
    boltzmannEntropy ∈ Γ₀(ℝ) := by
  have hmem :
      oneSidedLimitExtension boltzmannEntropyOpenInterval 0 ⊤
          (fun {x} hx ↦ boltzmannEntropyOpenInterval_zero_liminf_gt_bot x hx)
          (fun {x} hx ↦ liminf_gt_bot_of_eq_top_right boltzmannEntropyOpenInterval x hx) ∈
        Γ₀(ℝ) := by
    -- Proposition 9.34 applies to the finite branch on `]0,+∞[`.
    exact oneSidedLimitExtension_mem_gammaZero boltzmannEntropyOpenInterval 0 ⊤
      (by simp)
      effectiveDomain_boltzmannEntropyOpenInterval
      boltzmannEntropyOpenInterval_strictlyConvex
      (fun {x} hx ↦ boltzmannEntropyOpenInterval_zero_liminf_gt_bot x hx)
      (fun {x} hx ↦ liminf_gt_bot_of_eq_top_right boltzmannEntropyOpenInterval x hx)
  -- Rewrite the extension theorem back to the textbook function.
  simpa [boltzmannEntropy_eq_oneSidedLimitExtension] using hmem

-- Proof sketch: on `(0,+∞)`, the function is continuous because it is given by the smooth real
-- expression `x ↦ x log x - x`; at `0`, use `x log x → 0` as `x ↓ 0`; on `(-∞,0)`, the function
-- is identically `+∞`, so the lower-semicontinuity inequality is automatic there.
/-- The extended-real-valued representative of `boltzmannEntropy` is lower semicontinuous on
`ℝ`. -/
theorem boltzmannEntropy_lowerSemicontinuous :
    LowerSemicontinuous (fun x : ℝ ↦ (boltzmannEntropy x : EReal)) := by
  -- Membership in `Γ₀(ℝ)` packages lower semicontinuity directly.
  exact (mem_gammaZero_iff.mp boltzmannEntropy_mem_gammaZero_aux).1

-- Proof sketch: first show `x ↦ x log x - x` is strictly convex on `(0,+∞)` using the derivative
-- criterion of Proposition 8.14, since its derivative is `log x` and its second derivative is
-- `1 / x > 0`. Then extend across the boundary point `0` exactly as in Proposition 9.34.
/-- `boltzmannEntropy` is strictly convex on its effective domain `[0,+∞)`. -/
theorem boltzmannEntropy_strictlyConvex :
    StrictlyConvex boltzmannEntropy := by
  -- Rewrite to the one-sided extension and invoke the strict-convexity conclusion of Proposition
  -- 9.34.
  rw [boltzmannEntropy_eq_oneSidedLimitExtension]
  exact oneSidedLimitExtension_strictlyConvex boltzmannEntropyOpenInterval 0 ⊤
    (by simp)
    effectiveDomain_boltzmannEntropyOpenInterval
    boltzmannEntropyOpenInterval_strictlyConvex
    (fun {x} hx ↦ boltzmannEntropyOpenInterval_zero_liminf_gt_bot x hx)
    (fun {x} hx ↦ liminf_gt_bot_of_eq_top_right boltzmannEntropyOpenInterval x hx)

-- Proof sketch: combine `boltzmannEntropy_lowerSemicontinuous` with the convexity on the effective
-- domain implied by `boltzmannEntropy_strictlyConvex`, and package the result in the definition of
-- `Γ₀(ℝ)`.
/-- Example 9.35: the function equal to `x \log x - x` on `(0,+∞)`, equal to `0` at `0`, and equal
to `+∞` on `(-∞,0)` belongs to `Γ₀(ℝ)`; equivalently, it is proper, lower semicontinuous, and
strictly convex on its effective domain `[0,+∞)`. -/
theorem boltzmannEntropy_mem_gammaZero :
    boltzmannEntropy ∈ Γ₀(ℝ) := by
  -- The auxiliary `Γ₀` proof already matches the target function.
  exact boltzmannEntropy_mem_gammaZero_aux

end ERealFunction
