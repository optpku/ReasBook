/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Data.EReal.Operations
import Mathlib.Algebra.Module.Basic
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

namespace ERealFunction

variable {H : Type u}

/-- The effective domain of an `]-∞,+∞]`-valued function. -/
def effectiveDomain (f : H → Set.Ioi (⊥ : EReal)) : Set H :=
  {x | (f x : EReal) < ⊤}

/-- Membership in the effective domain means that the function value is finite. -/
theorem mem_effectiveDomain_iff {f : H → Set.Ioi (⊥ : EReal)} {x : H} :
    x ∈ effectiveDomain f ↔ (f x : EReal) < ⊤ :=
  Iff.rfl

end ERealFunction

namespace Function

/-- The `]-∞,+∞]`-valued function obtained by viewing a real-valued map as finite everywhere. -/
noncomputable def toEReal {X : Type*} (f : X → ℝ) : X → Set.Ioi (⊥ : EReal) :=
  fun x ↦ ⟨(f x : EReal), EReal.bot_lt_coe _⟩

/-- Coercing `f.toEReal` to `EReal` recovers the original real-valued formula. -/
@[simp] theorem toEReal_apply {X : Type*} (f : X → ℝ) (x : X) :
    (f.toEReal x : EReal) = (f x : EReal) :=
  rfl

/-- A real-valued function viewed through `toEReal` is finite everywhere. -/
@[simp] theorem effectiveDomain_toEReal {X : Type*} (f : X → ℝ) :
    ERealFunction.effectiveDomain f.toEReal = Set.univ := by
  ext x
  simp [ERealFunction.effectiveDomain]

/-- Forgetting the `]-∞,+∞]` witness yields the underlying `EReal`-valued function. -/
abbrev asEReal {X : Type*} (f : X → Set.Ioi (⊥ : EReal)) : X → EReal :=
  fun x ↦ (f x : EReal)

/-- Evaluating `asEReal` is just the subtype coercion to `EReal`. -/
@[simp] theorem asEReal_apply {X : Type*} (f : X → Set.Ioi (⊥ : EReal)) (x : X) :
    f.asEReal x = (f x : EReal) :=
  rfl

end Function

namespace ERealFunction

section RealVectorSpace

variable [AddCommGroup H] [Module ℝ H]

/-- Definition 8.7 (1): a proper `]-∞,+∞]`-valued function is strictly convex when the strict
Jensen inequality holds on its effective domain for every distinct pair of domain points and every
coefficient `α ∈ ]0,1[`. -/
def StrictlyConvex (f : H → Set.Ioi (⊥ : EReal)) : Prop :=
  ∀ ⦃x : H⦄, x ∈ effectiveDomain f → ∀ ⦃y : H⦄, y ∈ effectiveDomain f → x ≠ y →
    ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
      (f (α • x + (1 - α) • y) : EReal) <
        (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal)

/-- Definition 8.7 (2): a proper `]-∞,+∞]`-valued function is convex on a nonempty subset `C` of
its effective domain when Jensen's inequality holds for every pair of points of `C` and every
coefficient `α ∈ ]0,1[`. -/
def ConvexOn (f : H → Set.Ioi (⊥ : EReal)) (C : Set H) : Prop :=
  C.Nonempty ∧ C ⊆ effectiveDomain f ∧
    ∀ ⦃x : H⦄, x ∈ C → ∀ ⦃y : H⦄, y ∈ C → ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
      (f (α • x + (1 - α) • y) : EReal) ≤
        (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal)

/-- Definition 8.7 (3): a proper `]-∞,+∞]`-valued function is strictly convex on a nonempty subset
`C` of its effective domain when the strict Jensen inequality holds on `C` for distinct points and
every coefficient `α ∈ ]0,1[`. -/
def StrictlyConvexOn (f : H → Set.Ioi (⊥ : EReal)) (C : Set H) : Prop :=
  C.Nonempty ∧ C ⊆ effectiveDomain f ∧
    ∀ ⦃x : H⦄, x ∈ C → ∀ ⦃y : H⦄, y ∈ C → x ≠ y → ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
      (f (α • x + (1 - α) • y) : EReal) <
        (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal)

/-- A strictly convex function satisfies the strict Jensen inequality at any two distinct
effective-domain points. -/
-- Proof sketch: unfold `StrictlyConvex` and apply its defining inequality.
theorem StrictlyConvex.ineq {f : H → Set.Ioi (⊥ : EReal)} (hf : StrictlyConvex f)
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (hxy : x ≠ y)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (f (α • x + (1 - α) • y) : EReal) <
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
  -- Apply the defining strict Jensen inequality on the two effective-domain points.
  simpa [StrictlyConvex] using hf hx hy hxy hα0 hα1

/-- Restricting a strictly convex function to a nonempty subset of its effective domain yields a
strictly convex-on function. -/
-- Proof sketch: keep the same strict Jensen inequality and use the subset hypothesis to promote
-- the two points of `C` to effective-domain points of `f`.
theorem StrictlyConvex.strictlyConvexOn {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hf : StrictlyConvex f) (hC_nonempty : C.Nonempty) (hC_dom : C ⊆ effectiveDomain f) :
    StrictlyConvexOn f C := by
  refine ⟨hC_nonempty, hC_dom, ?_⟩
  intro x hx y hy hxy α hα0 hα1
  exact hf.ineq (hC_dom hx) (hC_dom hy) hxy hα0 hα1

/-- A convex-on set is nonempty. -/
-- Proof sketch: unfold `ConvexOn` and extract the first conjunct.
theorem ConvexOn.nonempty {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} (hf : ConvexOn f C) :
    C.Nonempty := by
  -- Extract the nonemptiness component stored in the definition.
  exact hf.1

/-- A convex-on set is contained in the effective domain. -/
-- Proof sketch: unfold `ConvexOn` and extract the domain-inclusion conjunct.
theorem ConvexOn.subset_effectiveDomain {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hf : ConvexOn f C) : C ⊆ effectiveDomain f := by
  -- Extract the domain-inclusion component stored in the definition.
  exact hf.2.1

/-- A function convex on `C` satisfies Jensen's inequality for points of `C`. -/
-- Proof sketch: unfold `ConvexOn` and apply the defining inequality clause.
theorem ConvexOn.ineq {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} (hf : ConvexOn f C)
    {x y : H} (hx : x ∈ C) (hy : y ∈ C) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (f (α • x + (1 - α) • y) : EReal) ≤
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
  -- Apply the Jensen-inequality clause stored in the definition.
  exact hf.2.2 hx hy hα0 hα1

/-- A convex function on its effective domain has a convex effective domain. -/
theorem ConvexOn.convex_effectiveDomain {f : H → Set.Ioi (⊥ : EReal)}
    (hf : ConvexOn f (effectiveDomain f)) :
    Convex ℝ (effectiveDomain f) := by
  refine (convex_iff_forall_pos).2 ?_
  intro x hx y hy a b ha hb hab
  have ha_lt_one : a < 1 := by
    linarith
  have hsub_cast : (((1 - a : ℝ) : EReal)) = 1 - (a : EReal) := by
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
  have hb_eq : (1 - a : ℝ) = b := by
    linarith
  have hineq₀ := hf.ineq hx hy ha ha_lt_one
  have hineq₁ :
      (f (a • x + (1 - a) • y) : EReal) ≤
        (a : EReal) * (f x : EReal) + (((1 - a : ℝ) : EReal) * (f y : EReal)) := by
    simpa [hsub_cast] using hineq₀
  have hineq :
      (f (a • x + b • y) : EReal) ≤
        (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) := by
    simpa [hb_eq] using hineq₁
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hsum :
      (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) =
        ((a * (f x : EReal).toReal + b * (f y : EReal).toReal : ℝ) : EReal) := by
    rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    simp
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt (hineq.trans_eq hsum) (EReal.coe_lt_top _)

/-- A function convex on its effective domain has convex real-height epigraph. -/
theorem ConvexOn.convex_epigraph_asEReal {f : H → Set.Ioi (⊥ : EReal)}
    (hf : ConvexOn f (effectiveDomain f)) :
    Convex ℝ (epigraph f.asEReal) := by
  refine (convex_epigraph_iff_jensen_on_dom f.asEReal).2 ?_
  intro x y hx hy α hα0 hα1
  have hx' : x ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hx
  have hy' : y ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hy
  simpa using hf.ineq hx' hy' hα0 hα1

/-- The finite representative of a convex function is mathlib-convex on its effective domain. -/
theorem ConvexOn.toReal_convexOn_effectiveDomain {f : H → Set.Ioi (⊥ : EReal)}
    (hf : ConvexOn f (effectiveDomain f)) :
    _root_.ConvexOn ℝ (effectiveDomain f) (fun x ↦ (f x : EReal).toReal) := by
  rw [convexOn_iff_forall_pos]
  constructor
  · exact hf.convex_effectiveDomain
  · intro x hx y hy a b ha hb hab
    have ha_lt_one : a < 1 := by
      linarith
    have hsub_cast : (((1 - a : ℝ) : EReal)) = 1 - (a : EReal) := by
      rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
    have hb_eq : (1 - a : ℝ) = b := by
      linarith
    have hineq₀ := hf.ineq hx hy ha ha_lt_one
    have hineq₁ :
        (f (a • x + (1 - a) • y) : EReal) ≤
          (a : EReal) * (f x : EReal) + (((1 - a : ℝ) : EReal) * (f y : EReal)) := by
      simpa [hsub_cast] using hineq₀
    have hineq :
        (f (a • x + b • y) : EReal) ≤
          (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) := by
      simpa [hb_eq] using hineq₁
    have hxy : a • x + b • y ∈ effectiveDomain f :=
      hf.convex_effectiveDomain hx hy ha.le hb.le hab
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (f y : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    have hxy_bot : (f (a • x + b • y) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (a • x + b • y) : EReal) from
        (f (a • x + b • y)).2)
    have hsum :
        (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) =
          ((a * (f x : EReal).toReal + b * (f y : EReal).toReal : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot,
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      simp
    have hright_top :
        (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) ≠ ⊤ := by
      rw [hsum]
      exact ne_of_lt (EReal.coe_lt_top _)
    simpa [hsum] using EReal.toReal_le_toReal hineq hxy_bot hright_top

/-- A strictly convex-on set is nonempty. -/
-- Proof sketch: unfold `StrictlyConvexOn` and extract the first conjunct.
theorem StrictlyConvexOn.nonempty {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hf : StrictlyConvexOn f C) : C.Nonempty := by
  -- Extract the nonemptiness component stored in the definition.
  exact hf.1

/-- A strictly convex-on set is contained in the effective domain. -/
-- Proof sketch: unfold `StrictlyConvexOn` and extract the domain-inclusion conjunct.
theorem StrictlyConvexOn.subset_effectiveDomain {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hf : StrictlyConvexOn f C) : C ⊆ effectiveDomain f := by
  -- Extract the domain-inclusion component stored in the definition.
  exact hf.2.1

/-- A function strictly convex on `C` satisfies the strict Jensen inequality for distinct points of
`C`. -/
-- Proof sketch: unfold `StrictlyConvexOn` and apply the defining strict inequality clause.
theorem StrictlyConvexOn.ineq {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hf : StrictlyConvexOn f C) {x y : H} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (f (α • x + (1 - α) • y) : EReal) <
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
  -- Apply the strict Jensen-inequality clause stored in the definition.
  exact hf.2.2 hx hy hxy hα0 hα1

end RealVectorSpace

end ERealFunction
