/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_36

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {X : Type u}

/-- Definition 11.3: `argminOn f C` is the set of minimizers of `f` over the constraint set `C`,
written `Argmin[C] f`. The global argmin set is the special case `argminOn f Set.univ`, written
`Argmin f`. -/
def argminOn (f : X → EReal) (C : Set X) : Set X :=
  {x | x ∈ C ∧ IsMinOn f C x}

/- Definition 11.3: the constrained minimizer set `argminOn f C` is written `Argmin[C] f`. -/
notation "Argmin[" C "] " f:max => argminOn f C

/-- A point belongs to `Argmin[C] f` exactly when it lies in `C` and minimizes `f` over `C`. -/
@[simp] theorem mem_argminOn_iff {f : X → EReal} {C : Set X} {x : X} :
    x ∈ Argmin[C] f ↔ x ∈ C ∧ IsMinOn f C x :=
  Iff.rfl

/-- Every constrained minimizer belongs to the constraint set. -/
theorem mem_of_mem_argminOn {f : X → EReal} {C : Set X} {x : X}
    (hx : x ∈ Argmin[C] f) :
    x ∈ C :=
  hx.1

/- Definition 11.3: the textbook global minimizer set `Argmin f` is `argminOn f Set.univ`. -/
notation "Argmin " f:arg => argminOn f Set.univ

/-- A point belongs to `Argmin f` exactly when it is a global minimizer of `f`. -/
@[simp] theorem mem_argmin_iff {f : X → EReal} {x : X} :
    x ∈ Argmin f ↔ IsMinOn f Set.univ x :=
  by simp [argminOn]

-- Proof sketch: `IsMinOn f Set.univ x` says `f x` is a lower bound for `Set.range f`, and since
-- `f x` itself lies in the range, it is the infimum of that range.
/-- A point lies in `Argmin f` exactly when its value equals the infimum of the range of `f`. -/
theorem mem_argmin_iff_eq_sInf {f : X → EReal} {x : X} :
    x ∈ Argmin f ↔ f x = sInf (Set.range f) := by
  constructor
  · intro hx
    have hxmin : IsMinOn f Set.univ x := (mem_argmin_iff).1 hx
    simpa only [Set.image_univ] using eq_sInf_image_of_isMinOn (by simp) hxmin
  · intro hx
    rw [mem_argmin_iff, isMinOn_univ_iff]
    intro y
    have hsInf_le : sInf (Set.range f) ≤ f y :=
      (isGLB_sInf (Set.range f)).1 (Set.mem_range_self y)
    simpa [hx] using hsInf_le

/-- Every global minimizer of a proper extended-real-valued function lies in the domain. -/
theorem mem_dom_of_mem_argmin_of_isProper {f : X → EReal} (hf : IsProper f) {x : X}
    (hx : x ∈ Argmin f) :
    x ∈ dom f := by
  obtain ⟨y, hy⟩ := hf.2
  rw [mem_argmin_iff, isMinOn_univ_iff] at hx
  change f x < ⊤
  exact lt_of_le_of_lt (hx y) ((ERealFunction.mem_dom_iff f y).1 hy)

/-- The global argmin set is the sublevel set at the infimum of the range of `f`. -/
theorem argmin_eq_setOf_le_sInf_range {f : X → EReal} :
    Argmin f = {x | f x ≤ sInf (Set.range f)} := by
  ext x
  rw [mem_argmin_iff_eq_sInf]
  constructor
  · intro hx
    exact hx.le
  · intro hx
    exact le_antisymm hx <| (isGLB_sInf (Set.range f)).1 (Set.mem_range_self x)

/-- The textbook indicator `ι[C]` of a set, viewed as a `]-∞,+∞]`-valued function. -/
noncomputable def indicator (C : Set X) : X → Set.Ioi (⊥ : EReal) :=
  let _ : DecidablePred (fun y ↦ y ∈ C) := Classical.decPred (fun y ↦ y ∈ C)
  fun x ↦ if hx : x ∈ C then ⟨0, by simp⟩ else ⟨⊤, by simp⟩

notation "ι[" C "]" => ERealFunction.indicator C

/-- Coercing `ι[C]` to `EReal` gives the ordinary extended-real indicator of `C`. -/
@[simp] theorem indicator_apply
    (C : Set X) (x : X) :
    (ι[C] x : EReal) = Cᶜ.indicator (fun _ : X ↦ (⊤ : EReal)) x := by
  by_cases hx : x ∈ C <;> simp [indicator, hx]

/-- The effective domain of the textbook indicator `ι[C]` is exactly `C`. -/
@[simp] theorem effectiveDomain_indicator (C : Set X) :
    effectiveDomain (ι[C]) = C := by
  ext x
  by_cases hx : x ∈ C <;> simp [ERealFunction.effectiveDomain, indicator, hx]

/- Definition 11.3: the constrained objective from the textbook notation `f + ι_C` is the
canonical pointwise sum `f + (ι[C]).asEReal` in Lean. -/
/-- Evaluating the canonical constrained objective `f + (ι[C]).asEReal` adds the indicator value
pointwise. -/
@[simp] theorem add_indicator_apply
    (f : X → EReal) (C : Set X) (x : X) :
    (f + (ι[C]).asEReal) x = f x + (ι[C] x : EReal) :=
  rfl

/-- On `C`, the indicator-augmented function `f + (ι[C]).asEReal` agrees with `f`. -/
theorem add_indicator_eqOn
    (f : X → EReal) (C : Set X) :
    Set.EqOn (f + (ι[C]).asEReal) f C := by
  intro x hx
  simp [hx]

-- Proof sketch: outside `C`, the complement indicator contributes `⊤`; only those points can
-- create the indeterminate sum `⊥ + ⊤`, so it suffices to exclude `⊥` on `Cᶜ`. Then minimizing
-- over `C` is the same as globally minimizing the indicator-augmented function.
/-- Minimizers of `f` over `C` are exactly the global minimizers of `f + ι_C`, written here as
the canonical indicator `ι[C]`, that lie in `C`. -/
theorem argminOn_eq_inter_argmin_add_indicator
    (f : X → EReal) (C : Set X) (hbot : ∀ x ∉ C, f x ≠ ⊥) :
    Argmin[C] f = C ∩ Argmin (f + (ι[C]).asEReal) := sorry

section PseudoMetricSpace

variable [PseudoMetricSpace X]

-- Proof sketch: if `x` minimizes `f` on `Metric.ball x ρ` with `ρ > 0`, then that ball is a
-- neighborhood of `x`; convert the ballwise minimum into the neighborhood-filter statement
-- `IsLocalMin f x`.
/-- Any minimizer of `f` on some open ball centered at `x` is a local minimizer of `f`. -/
theorem isLocalMin_of_mem_argminOn_ball {f : X → EReal} {x : X} {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ Argmin[Metric.ball x ρ] f) :
    IsLocalMin f x :=
  hx.2.isLocalMin (Metric.ball_mem_nhds x hρ)

end PseudoMetricSpace

end ERealFunction
