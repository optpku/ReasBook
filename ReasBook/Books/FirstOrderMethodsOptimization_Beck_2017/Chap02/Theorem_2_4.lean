/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [TopologicalSpace E]

-- Proof sketch: apply `LowerSemicontinuousOn.exists_isMinOn` on the compact set `C`; then compare
-- the minimizer with a point of `C ∩ effective_domain f` to show
-- that the minimizing point also lies in `effective_domain f`.
/-- Theorem 2.4 (2): if `f` is lower semicontinuous on a compact set `C` and `C` meets the
effective domain of `f`, then `f` attains its minimum on `C`, and the minimizer can be chosen in
the effective domain. -/
theorem exists_isMinOn_on_compact (f : E → EReal) (C : Set E)
    (h_lsc : LowerSemicontinuousOn f C)
    (hC : IsCompact C)
    (hCdom : (C ∩ effective_domain f).Nonempty) :
    ∃ x ∈ C ∩ effective_domain f, IsMinOn f C x := by
  obtain ⟨y, hyC, hy_dom⟩ := hCdom
  obtain ⟨x, hxC, hxmin⟩ := h_lsc.exists_isMinOn ⟨y, hyC⟩ hC
  refine ⟨x, ⟨hxC, ?_⟩, hxmin⟩
  exact lt_of_le_of_lt (isMinOn_iff.mp hxmin y hyC) hy_dom

-- Proof sketch: if `C` is empty, any real number is a lower bound. Otherwise choose a minimizer
-- `x⋆` from the owner theorem `LowerSemicontinuousOn.exists_isMinOn`. If `f x⋆ = ⊤`, then
-- minimality forces `f = ⊤` on `C`, so again any real number is a lower bound. If `f x⋆ ≠ ⊤`,
-- the local non-`⊥` hypothesis on `C` makes `(f x⋆).toReal` a genuine real number whose coercion
-- back to `EReal` equals `f x⋆`, and minimality gives the desired lower bound.
/-- Theorem 2.4 (1): if `f` is lower semicontinuous on a compact set `C`, never takes the value
`-∞` on `C`, then `f` admits a real lower bound on `C`. -/
theorem exists_real_lower_bound_on_compact (f : E → EReal) (C : Set E)
    (h_lsc : LowerSemicontinuousOn f C)
    (h_ne_bot : ∀ x ∈ C, f x ≠ ⊥)
    (hC : IsCompact C) :
    ∃ m : ℝ, ∀ x ∈ C, (m : EReal) ≤ f x := by
  by_cases hCne : C.Nonempty
  · obtain ⟨x, hxC, hxmin⟩ := h_lsc.exists_isMinOn hCne hC
    by_cases hx_top : f x = ⊤
    · refine ⟨0, ?_⟩
      intro y hyC
      have hxy : f x ≤ f y := isMinOn_iff.mp hxmin y hyC
      have hy_top : f y = ⊤ := by simpa [hx_top] using hxy
      simp [hy_top]
    · refine ⟨(f x).toReal, ?_⟩
      intro y hyC
      have hxcoe : ((f x).toReal : EReal) = f x := EReal.coe_toReal hx_top (h_ne_bot x hxC)
      simpa [hxcoe] using isMinOn_iff.mp hxmin y hyC
  · refine ⟨0, ?_⟩
    intro x hxC
    exact (hCne ⟨x, hxC⟩).elim

section

variable {E : Type u} [PseudoMetricSpace E] [ProperSpace E]

-- Proof sketch: choose `x₀ ∈ effective_domain f` from properness and minimize `f` on the closed
-- bounded real sublevel set `{x | f x ≤ (f x₀).toReal}`. Properness makes that sublevel set
-- compact, and points outside it have strictly larger objective value, so the same minimizer is
-- global.
/-- A proper lower-semicontinuous extended-real-valued function on a proper pseudometric space,
whose real sublevel sets are all bounded, attains its minimum on `univ`. The minimizer can be
chosen in the effective domain. -/
theorem exists_isMinOn_univ_of_bounded_real_sublevelSets (f : E → EReal)
    (hproper : IsProperExtendedRealFunction f) (h_lsc : LowerSemicontinuous f)
    (hlevel : ∀ a : ℝ, Bornology.IsBounded {x | f x ≤ (a : EReal)}) :
    ∃ x ∈ effective_domain f, IsMinOn f Set.univ x := by
  obtain ⟨x₀, hx₀⟩ := hproper.effective_domain_nonempty
  have hx₀_eq : (((f x₀).toReal : ℝ) : EReal) = f x₀ :=
    EReal.coe_toReal hx₀.ne (hproper.ne_bot x₀)
  let C : Set E := {x | f x ≤ (((f x₀).toReal : ℝ) : EReal)}
  have hC_closed : IsClosed C := by
    simpa [C] using
      (lowerSemicontinuous_iff_isClosed_real_sublevelSets f).mp h_lsc (f x₀).toReal
  have hC_bounded : Bornology.IsBounded C := by
    simpa [C] using hlevel (f x₀).toReal
  have hC_compact : IsCompact C := Metric.isCompact_of_isClosed_isBounded hC_closed hC_bounded
  have hx₀C : x₀ ∈ C := by
    simp [C, hx₀_eq]
  obtain ⟨x, hxC, hxmin⟩ :=
    exists_isMinOn_on_compact f C (h_lsc.lowerSemicontinuousOn C) hC_compact ⟨x₀, hx₀C, hx₀⟩
  refine ⟨x, hxC.2, ?_⟩
  intro y _
  by_cases hyC : y ∈ C
  · exact isMinOn_iff.mp hxmin y hyC
  · have hlt : (((f x₀).toReal : ℝ) : EReal) < f y := by
      exact lt_of_not_ge (by simpa [C] using hyC)
    exact hxC.1.trans hlt.le

end
