/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {α : Type u}

section

variable [TopologicalSpace α]

/- Definition 2.2: the textbook notion of a closed extended-real-valued function is the
canonical predicate `LowerSemicontinuous`; for `EReal`-valued functions, mathlib identifies this
with closedness of the epigraph. -/
#check (LowerSemicontinuous : (α → EReal) → Prop)

/- Closed epigraphs are the canonical source-facing characterization of lower semicontinuity for
`EReal`-valued functions. -/
recall lowerSemicontinuous_iff_isClosed_epigraph

end

/-- The extended-real-valued indicator function of a set, equal to `0` on the set and `⊤`
outside it. -/
noncomputable def extendedIndicator (C : Set α) : α → EReal :=
  open scoped Classical in
  Set.indicator Cᶜ (fun _ ↦ (⊤ : EReal))

@[inherit_doc] notation "δ_ " C:arg => extendedIndicator C

@[simp] theorem extendedIndicator_of_mem {C : Set α} {x : α} (hx : x ∈ C) :
    (δ_ C) x = 0 := by
  simp [extendedIndicator, hx]

@[simp] theorem extendedIndicator_of_not_mem {C : Set α} {x : α} (hx : x ∉ C) :
    (δ_ C) x = ⊤ := by
  simp [extendedIndicator, hx]

/-- `δ_C` is the standard indicator of `Cᶜ` with value `⊤`. -/
theorem extendedIndicator_eq_indicator_compl (C : Set α) :
    δ_ C = Set.indicator Cᶜ (fun _ ↦ (⊤ : EReal)) :=
  rfl

-- Proof sketch: unfold both owners; on `C` the indicator value is `0 < ⊤`, while outside `C` the
-- value is `⊤`, so the effective-domain inequality fails.
/-- The effective domain of the indicator function `δ_C` is exactly the set `C`. -/
@[simp] theorem effective_domain_extendedIndicator (C : Set α) :
    effective_domain (δ_ C) = C := by
  ext x
  by_cases hx : x ∈ C <;> simp [effective_domain, extendedIndicator, hx]

@[simp] theorem mem_effective_domain_extendedIndicator {C : Set α} {x : α} :
    x ∈ effective_domain (δ_ C) ↔ x ∈ C := by
  simp [effective_domain_extendedIndicator]

section

variable [TopologicalSpace α]

-- Proof sketch: if `extendedIndicator C` is lower semicontinuous, then the zero slice of its
-- closed epigraph recovers `C`; conversely, if `C` is closed then `Cᶜ` is open, so the indicator
-- presentation `Set.indicator Cᶜ (fun _ ↦ ⊤)` is lower semicontinuous by the canonical mathlib
-- indicator theorem.
/-- The indicator function `δ_C` is closed, equivalently lower
semicontinuous, if and only if the underlying set `C` is closed. -/
theorem extendedIndicator_lowerSemicontinuous_iff_isClosed (C : Set α) :
    LowerSemicontinuous (δ_ C) ↔ IsClosed C := by
  constructor
  · intro h
    have hslice :
        (fun x : α ↦ (x, (0 : EReal))) ⁻¹'
            {p : α × EReal | (δ_ C) p.1 ≤ p.2} = C := by
      ext x
      by_cases hx : x ∈ C <;> simp [extendedIndicator, hx]
    have hclosed :
        IsClosed ((fun x : α ↦ (x, (0 : EReal))) ⁻¹'
          {p : α × EReal | (δ_ C) p.1 ≤ p.2}) :=
      h.isClosed_epigraph.preimage (by continuity)
    simpa [hslice] using hclosed
  · intro hC
    have hopen : IsOpen Cᶜ := hC.isOpen_compl
    simpa [extendedIndicator_eq_indicator_compl] using
      hopen.lowerSemicontinuous_indicator (by simp)

/-- A closed set has a lower semicontinuous extended indicator function. -/
theorem IsClosed.lowerSemicontinuous_extendedIndicator {C : Set α} (hC : IsClosed C) :
    LowerSemicontinuous (δ_ C) :=
  (extendedIndicator_lowerSemicontinuous_iff_isClosed C).2 hC

end
