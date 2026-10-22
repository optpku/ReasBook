/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Theorem_7_26

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped InnerProductSpace

universe u

noncomputable section

section

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Helper for Corollary 7.28: on real `L²(μ)`, the inner product with the second argument on the
right is the integral of the pointwise product. -/
private lemma l2_inner_right_eq_integral_mul (f g : Lp ℝ 2 μ) :
    inner ℝ g f = ∫ x, f x * g x ∂μ := by
  simpa [Lp.toLp_coeFn f (Lp.memLp f), Lp.toLp_coeFn g (Lp.memLp g), mul_comm] using
    (inner_toLp_eq_integral_mul (Lp.memLp g) (Lp.memLp f))

-- Proof sketch: apply the chapter's Hilbert-space Fréchet-Riesz owner theorem to `L²(μ)`, then
-- rewrite the resulting inner-product representation using the canonical `L²` integral formula.
/-- Every continuous linear functional on `L²(μ)` is integration against a unique `L²(μ)`
representative. This is the `L²` form of the Fréchet-Riesz theorem, stated directly for
continuous linear maps. -/
theorem exists_l2_integral_representation_of_continuousLinearMap
    (F : Lp ℝ 2 μ →L[ℝ] ℝ) :
    ∃! f : Lp ℝ 2 μ, ∀ g : Lp ℝ 2 μ, F g = ∫ x, f x * g x ∂μ := by
  obtain ⟨f, hf, huniq⟩ := existsUnique_inner_right_eq_of_continuousLinearMap F
  refine ⟨f, ?_, ?_⟩
  · intro g
    calc
      F g = inner ℝ g f := hf g
      _ = ∫ x, f x * g x ∂μ := l2_inner_right_eq_integral_mul f g
  · intro g hg
    apply huniq g
    intro h
    calc
      F h = ∫ x, g x * h x ∂μ := hg h
      _ = inner ℝ h g := (l2_inner_right_eq_integral_mul g h).symm

-- Proof sketch: on the forward direction, bundle the assumed map as a continuous linear map and
-- apply `exists_l2_integral_representation_of_continuousLinearMap`; on the reverse direction, the
-- representing function `f` defines the functional `g ↦ ∫ x, f x * g x ∂μ`, so the corollary is
-- just the coercion-free textbook reformulation of the continuous-linear-map theorem above.
/-- Corollary 7.28: a map on `L²(μ)` is continuous and linear exactly when it is given by
integration against some `f ∈ L²(μ)`. This is the textbook wording, presented as a thin bridge
from the canonical continuous-linear-map statement. -/
theorem continuous_linear_iff_exists_l2_integral_representation
    (F : Lp ℝ 2 μ → ℝ) :
    (∃ L : Lp ℝ 2 μ →L[ℝ] ℝ, F = L) ↔
      ∃ f : Lp ℝ 2 μ, F = fun g ↦ ∫ x, f x * g x ∂μ := by
  constructor
  · rintro ⟨L, rfl⟩
    obtain ⟨f, hf, -⟩ := exists_l2_integral_representation_of_continuousLinearMap L
    refine ⟨f, ?_⟩
    ext g
    exact hf g
  · rintro ⟨f, rfl⟩
    refine ⟨InnerProductSpace.toDual ℝ (Lp ℝ 2 μ) f, ?_⟩
    ext g
    calc
      ∫ x, f x * g x ∂μ = inner ℝ g f := (l2_inner_right_eq_integral_mul f g).symm
      _ = inner ℝ f g := real_inner_comm _ _
      _ = (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ) f) g := by
        rw [InnerProductSpace.toDual_apply_apply]

end
