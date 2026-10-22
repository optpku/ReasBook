/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set Filter

variable {E : Type u} [NormedAddCommGroup E] [ProperSpace E]

section

-- Proof sketch: choose `x₀ ∈ S ∩ effective_domain f`. The chapter owner abstraction
-- `IsCoerciveExtendedRealFunction f` supplies `Tendsto f (cocompact E) (𝓝 (⊤ : EReal))`; applying
-- `EReal.tendsto_nhds_top_iff_real` at the finite value `f x₀` gives
-- `∀ᶠ x in cocompact E ⊓ 𝓟 S, f x₀ ≤ f x`. Apply `LowerSemicontinuousOn.exists_isMinOn` to the
-- compact closed subset obtained by adjoining `x₀` to that compact part of `S`, then compare with
-- points outside the compact set using the eventual lower bound.
/-- Theorem 2.5: a proper closed coercive extended-real-valued function, equivalently here a lower
semicontinuous coercive function, attains its minimum on every closed set `S` meeting its
effective domain. -/
theorem attains_min_on_closed_set_of_coercive (f : E → EReal) {S : Set E}
    (hf : LowerSemicontinuous f) (hcoercive : IsCoerciveExtendedRealFunction f)
    (hS_closed : IsClosed S) (hS_dom : (S ∩ effective_domain f).Nonempty) :
    ∃ x ∈ S, IsMinOn f S x := by
  obtain ⟨x₀, hx₀S, hx₀dom⟩ := hS_dom
  have hx₀_top : f x₀ ≠ ⊤ := hx₀dom.ne
  have hx₀_bot : f x₀ ≠ ⊥ := hcoercive.ne_bot x₀
  have hx₀_eq : (((f x₀).toReal : ℝ) : EReal) = f x₀ := EReal.coe_toReal hx₀_top hx₀_bot
  have htop :
      ∀ᶠ x in cocompact E, (((f x₀).toReal : ℝ) : EReal) < f x :=
    (EReal.tendsto_nhds_top_iff_real.mp hcoercive.tendsto_top_cocompact) (f x₀).toReal
  have hbound : ∀ᶠ x in cocompact E ⊓ 𝓟 S, f x₀ ≤ f x := by
    filter_upwards [htop.filter_mono inf_le_left] with x hx
    exact (by simpa [hx₀_eq] using hx : f x₀ < f x).le
  rcases (hasBasis_cocompact.inf_principal S).eventually_iff.1 hbound with ⟨K, hK, hKf⟩
  let T : Set E := insert x₀ (K ∩ S)
  have hTS : T ⊆ S := insert_subset_iff.2 ⟨hx₀S, inter_subset_right⟩
  have hT_compact : IsCompact T := (hK.inter_right hS_closed).insert x₀
  obtain ⟨x, hxT, hxmin⟩ := (hf.lowerSemicontinuousOn T).exists_isMinOn (insert_nonempty x₀ _) hT_compact
  refine ⟨x, hTS hxT, ?_⟩
  intro y hyS
  by_cases hyK : y ∈ K
  · exact isMinOn_iff.mp hxmin y (Or.inr ⟨hyK, hyS⟩)
  · exact (isMinOn_iff.mp hxmin x₀ (Or.inl rfl)).trans (hKf ⟨hyK, hyS⟩)

end
