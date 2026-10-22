/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Proposition_10_26

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section QuasiconvexBridge

variable {H : Type u} [AddCommMonoid H] [Module ℝ H]
variable {f : H → EReal} {C : Set H}

private theorem quasiconvexOn_univ_of_le_max_on_dom_strictCoeffs
    (hineq : ∀ ⦃x y : H⦄, x ∈ dom f → y ∈ dom f → ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
      f (α • x + (1 - α) • y) ≤ max (f x) (f y)) :
    QuasiconvexOn ℝ Set.univ f := by
  refine quasiconvexOn_univ_iff_le_max_on_dom.2 ?_
  intro x y hx hy α hα
  exact hineq hx hy hα.1 hα.2

private theorem quasiconvexOn_of_le_max_on_strictCoeffs
    (hC : Convex ℝ C)
    (hineq : ∀ ⦃x y : H⦄, x ∈ C → y ∈ C → ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
      f (α • x + (1 - α) • y) ≤ max (f x) (f y)) :
    QuasiconvexOn ℝ C f := by
  refine quasiconvexOn_iff_le_max.2 ⟨hC, ?_⟩
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp [ha0, hb1]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp [hb0, ha1]
  have ha_pos : 0 < a := lt_of_le_of_ne ha <| Ne.symm ha0
  have hb_pos : 0 < b := lt_of_le_of_ne hb <| Ne.symm hb0
  have ha_lt_one : a < 1 := by
    linarith
  have hb_eq : b = 1 - a := by linarith
  simpa [hb_eq] using hineq hx hy ha_pos ha_lt_one

end QuasiconvexBridge

section Strict

variable {H : Type u} [AddCommMonoid H] [Module ℝ H]
variable {f : H → EReal}

/-- Definition 10.27 (1): a proper function is strictly quasiconvex when every strict convex
combination of two distinct points of `dom f` has value strictly below the larger endpoint value.
-/
def StrictlyQuasiconvex (f : H → EReal) : Prop :=
  IsProper f ∧
    ∀ ⦃x y : H⦄, x ∈ dom f → y ∈ dom f → x ≠ y →
      ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
        f (α • x + (1 - α) • y) < max (f x) (f y)

/-- A strictly quasiconvex function is proper. -/
theorem StrictlyQuasiconvex.isProper (hf : StrictlyQuasiconvex f) : IsProper f :=
  hf.1

/-- A strictly quasiconvex function satisfies its defining strict max inequality on `dom f`. -/
-- Proof sketch: unfold `StrictlyQuasiconvex` and apply the final conjunct.
theorem StrictlyQuasiconvex.ineq
    (hf : StrictlyQuasiconvex f) {x y : H} (hx : x ∈ dom f) (hy : y ∈ dom f)
    (hxy : x ≠ y) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    f (α • x + (1 - α) • y) < max (f x) (f y) :=
  hf.2 hx hy hxy hα0 hα1

/-- Strict quasiconvexity yields the canonical quasiconvexity owner on `Set.univ`. -/
theorem StrictlyQuasiconvex.quasiconvexOn
    (hf : StrictlyQuasiconvex f) :
    QuasiconvexOn ℝ Set.univ f := by
  refine quasiconvexOn_univ_of_le_max_on_dom_strictCoeffs ?_
  intro x y hx hy α hα0 hα1
  by_cases hxy : x = y
  · subst y
    rw [← add_smul, add_sub_cancel, one_smul]
    simp
  · exact (hf.ineq hx hy hxy hα0 hα1).le

end Strict

section Uniform

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {f : H → EReal} {φ : NNReal → EReal}

/-- A monotone modulus that vanishes only at `0` is nonnegative. -/
private theorem modulus_nonneg
    (hφ_mono : Monotone φ) (hφ_zero : ∀ r : NNReal, φ r = 0 ↔ r = 0) (r : NNReal) :
    0 ≤ φ r := by
  rw [← (hφ_zero 0).2 rfl]
  exact hφ_mono bot_le

omit [NormedSpace ℝ H] in
private theorem modulusTerm_nonneg
    (hφ_mono : Monotone φ) (hφ_zero : ∀ r : NNReal, φ r = 0 ↔ r = 0)
    {α : ℝ} (hα_nonneg : 0 ≤ α * (1 - α)) (x y : H) :
    (0 : EReal) ≤ ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ := by
  exact mul_nonneg (by exact_mod_cast hα_nonneg) (modulus_nonneg hφ_mono hφ_zero _)

/-- Definition 10.27 (2): a proper function is uniformly quasiconvex with modulus `φ` when `φ`
is increasing, vanishes only at `0`, and the uniform max inequality holds on `dom f`. -/
def UniformlyQuasiconvex (f : H → EReal) (φ : NNReal → EReal) : Prop :=
  IsProper f ∧
    Monotone φ ∧
    (∀ r : NNReal, φ r = 0 ↔ r = 0) ∧
    ∀ ⦃x y : H⦄, x ∈ dom f → y ∈ dom f →
      ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
        f (α • x + (1 - α) • y) +
            ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≤
          max (f x) (f y)

/-- A uniformly quasiconvex function is proper. -/
theorem UniformlyQuasiconvex.isProper
    (hf : UniformlyQuasiconvex f φ) :
    IsProper f :=
  hf.1

/-- A uniformly quasiconvex modulus is monotone. -/
theorem UniformlyQuasiconvex.monotone
    (hf : UniformlyQuasiconvex f φ) :
    Monotone φ :=
  hf.2.1

/-- A uniformly quasiconvex modulus vanishes exactly at `0`. -/
theorem UniformlyQuasiconvex.modulus_eq_zero_iff
    (hf : UniformlyQuasiconvex f φ) (r : NNReal) :
    φ r = 0 ↔ r = 0 :=
  hf.2.2.1 r

/-- A uniformly quasiconvex function satisfies its defining max inequality on `dom f`. -/
-- Proof sketch: unfold `UniformlyQuasiconvex` and apply the final conjunct.
theorem UniformlyQuasiconvex.ineq
    (hf : UniformlyQuasiconvex f φ)
    {x y : H} (hx : x ∈ dom f) (hy : y ∈ dom f) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    f (α • x + (1 - α) • y) +
        ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≤
      max (f x) (f y) :=
  hf.2.2.2 hx hy hα0 hα1

/-- Uniform quasiconvexity yields the canonical quasiconvexity owner on `Set.univ`. -/
theorem UniformlyQuasiconvex.quasiconvexOn
    (hf : UniformlyQuasiconvex f φ) :
    QuasiconvexOn ℝ Set.univ f := by
  refine quasiconvexOn_univ_of_le_max_on_dom_strictCoeffs ?_
  intro x y hx hy α hα0 hα1
  have hα_nonneg : 0 ≤ α * (1 - α) := by
    nlinarith [hα0, hα1]
  have hterm_nonneg : (0 : EReal) ≤ ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ :=
    modulusTerm_nonneg hf.monotone hf.modulus_eq_zero_iff hα_nonneg x y
  calc
    f (α • x + (1 - α) • y)
        ≤ f (α • x + (1 - α) • y) + ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ :=
      le_add_of_nonneg_right hterm_nonneg
    _ ≤ max (f x) (f y) :=
      hf.ineq hx hy hα0 hα1

end Uniform

section StrictOn

variable {H : Type u} [AddCommMonoid H] [Module ℝ H]
variable {f : H → EReal} {C : Set H}

/-- Definition 10.27 (3): a proper function is strictly quasiconvex on `C` when `C` is a subset of
`dom f` and the strict max inequality holds for every two distinct points of `C`. -/
def StrictlyQuasiconvexOn (f : H → EReal) (C : Set H) : Prop :=
  IsProper f ∧
    C ⊆ dom f ∧
    ∀ ⦃x y : H⦄, x ∈ C → y ∈ C → x ≠ y →
      ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
        f (α • x + (1 - α) • y) < max (f x) (f y)

/-- A strictly quasiconvex-on function is proper. -/
theorem StrictlyQuasiconvexOn.isProper
    (hf : StrictlyQuasiconvexOn f C) :
    IsProper f :=
  hf.1

/-- A strictly quasiconvex-on set is contained in `dom f`. -/
theorem StrictlyQuasiconvexOn.subset_dom
    (hf : StrictlyQuasiconvexOn f C) :
    C ⊆ dom f :=
  hf.2.1

/-- A function strictly quasiconvex on `C` satisfies the defining strict max inequality on `C`. -/
-- Proof sketch: unfold `StrictlyQuasiconvexOn` and apply the final conjunct.
theorem StrictlyQuasiconvexOn.ineq
    (hf : StrictlyQuasiconvexOn f C)
    {x y : H} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    f (α • x + (1 - α) • y) < max (f x) (f y) :=
  hf.2.2 hx hy hxy hα0 hα1

/-- Under an explicit convexity hypothesis on `C`, strict quasiconvexity on `C` yields the
canonical quasiconvexity owner on `C`. -/
theorem StrictlyQuasiconvexOn.quasiconvexOn
    (hC : Convex ℝ C) (hf : StrictlyQuasiconvexOn f C) :
    QuasiconvexOn ℝ C f := by
  refine quasiconvexOn_of_le_max_on_strictCoeffs hC ?_
  intro x y hx hy α hα0 hα1
  by_cases hxy : x = y
  · subst y
    rw [← add_smul, add_sub_cancel, one_smul]
    simp
  · exact (hf.ineq hx hy hxy hα0 hα1).le

end StrictOn

section UniformOn

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {f : H → EReal} {C : Set H} {φ : NNReal → EReal}

/-- Definition 10.27 (4): a proper function is uniformly quasiconvex on `C` with modulus `φ`
when `C` is a subset of `dom f`, `φ` is increasing, vanishes only at `0`, and the uniform max
inequality holds on `C`. -/
def UniformlyQuasiconvexOn (f : H → EReal) (C : Set H) (φ : NNReal → EReal) : Prop :=
  IsProper f ∧
    C ⊆ dom f ∧
    Monotone φ ∧
    (∀ r : NNReal, φ r = 0 ↔ r = 0) ∧
    ∀ ⦃x y : H⦄, x ∈ C → y ∈ C →
      ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
        f (α • x + (1 - α) • y) +
            ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≤
          max (f x) (f y)

/-- A uniformly quasiconvex-on function is proper. -/
theorem UniformlyQuasiconvexOn.isProper
    (hf : UniformlyQuasiconvexOn f C φ) :
    IsProper f :=
  hf.1

/-- A uniformly quasiconvex-on set is contained in `dom f`. -/
theorem UniformlyQuasiconvexOn.subset_dom
    (hf : UniformlyQuasiconvexOn f C φ) :
    C ⊆ dom f :=
  hf.2.1

/-- A uniformly quasiconvex-on modulus is monotone. -/
theorem UniformlyQuasiconvexOn.monotone
    (hf : UniformlyQuasiconvexOn f C φ) :
    Monotone φ :=
  hf.2.2.1

/-- A uniformly quasiconvex-on modulus vanishes exactly at `0`. -/
theorem UniformlyQuasiconvexOn.modulus_eq_zero_iff
    (hf : UniformlyQuasiconvexOn f C φ) (r : NNReal) :
    φ r = 0 ↔ r = 0 :=
  hf.2.2.2.1 r

/-- A function uniformly quasiconvex on `C` satisfies the defining max inequality on `C`. -/
-- Proof sketch: unfold `UniformlyQuasiconvexOn` and apply the final conjunct.
theorem UniformlyQuasiconvexOn.ineq
    (hf : UniformlyQuasiconvexOn f C φ)
    {x y : H} (hx : x ∈ C) (hy : y ∈ C) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    f (α • x + (1 - α) • y) +
        ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≤
      max (f x) (f y) :=
  hf.2.2.2.2 hx hy hα0 hα1

/-- Under an explicit convexity hypothesis on `C`, uniform quasiconvexity on `C` yields the
canonical quasiconvexity owner on `C`. -/
theorem UniformlyQuasiconvexOn.quasiconvexOn
    (hC : Convex ℝ C) (hf : UniformlyQuasiconvexOn f C φ) :
    QuasiconvexOn ℝ C f := by
  refine quasiconvexOn_of_le_max_on_strictCoeffs hC ?_
  intro x y hx hy α hα0 hα1
  have hα_nonneg : 0 ≤ α * (1 - α) := by
    nlinarith [hα0, hα1]
  have hterm_nonneg : (0 : EReal) ≤ ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ :=
    modulusTerm_nonneg hf.monotone hf.modulus_eq_zero_iff hα_nonneg x y
  calc
    f (α • x + (1 - α) • y)
        ≤ f (α • x + (1 - α) • y) + ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ :=
      le_add_of_nonneg_right hterm_nonneg
    _ ≤ max (f x) (f y) :=
      hf.ineq hx hy hα0 hα1

end UniformOn

end ERealFunction
