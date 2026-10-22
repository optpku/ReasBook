/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Order.Filter.Extr

open Filter
open SignType
open scoped Topology

section Chapter01Definition143

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- The source-facing predicate for Chapter01 Definition 1.4.3 names descent directions.
The core/canonical owner underneath is mathlib's gradient API on real complete inner-product
spaces. Since `gradient f x = 0` when `f` is not differentiable at `x`, the negativity of
`inner ℝ (gradient f x) d` already forces differentiability, so that theorem belongs in the
derived API rather than as primitive data of the definition. -/

/-- The source-facing descent-direction predicate for Chapter01 Definition 1.4.3 says that a
vector `d` is a descent direction of `f` at `x` when the gradient pairing
`inner ℝ (gradient f x) d` is negative. -/
def IsDescentDirectionAt (f : E → ℝ) (x d : E) : Prop :=
  inner ℝ (gradient f x) d < 0

/-- The predicate `IsDescentDirectionAt` is proof-irrelevant. -/
instance isDescentDirectionAt_subsingleton (f : E → ℝ) (x d : E) :
    Subsingleton (IsDescentDirectionAt f x d) := inferInstance

/-- A descent direction at `x` has negative gradient pairing. -/
theorem IsDescentDirectionAt.inner_gradient_neg {f : E → ℝ} {x d : E}
    (h : IsDescentDirectionAt f x d) :
    inner ℝ (gradient f x) d < 0 :=
  h

/-- A descent direction at `x` is nonzero. -/
theorem IsDescentDirectionAt.direction_ne {f : E → ℝ} {x d : E}
    (h : IsDescentDirectionAt f x d) :
    d ≠ 0 := by
  intro hd
  simpa [hd] using h.inner_gradient_neg

/-- A descent direction at `x` forces the gradient at `x` to be nonzero. -/
theorem IsDescentDirectionAt.gradient_ne {f : E → ℝ} {x d : E}
    (h : IsDescentDirectionAt f x d) :
    gradient f x ≠ 0 := by
  intro hgrad
  simpa [hgrad] using h.inner_gradient_neg

/-- A descent direction at `x` is automatically a point of differentiability of `f`. -/
theorem IsDescentDirectionAt.differentiableAt {f : E → ℝ} {x d : E}
    (h : IsDescentDirectionAt f x d) :
    DifferentiableAt ℝ f x := by
  by_contra hdiff
  have hgrad : gradient f x = 0 := gradient_eq_zero_of_not_differentiableAt hdiff
  have : ¬ inner ℝ (gradient f x) d < 0 := by simp [hgrad]
  exact this h

/-- Unfolding formula for `IsDescentDirectionAt`. -/
theorem isDescentDirectionAt_iff (f : E → ℝ) (x d : E) :
    IsDescentDirectionAt f x d ↔ inner ℝ (gradient f x) d < 0 :=
  Iff.rfl

/-- For every direction `d`, at least one of `d` and `-d` has nonpositive gradient pairing. -/
theorem inner_gradient_nonpos_or_neg_nonpos (f : E → ℝ) (x d : E) :
    inner ℝ (gradient f x) d ≤ 0 ∨ inner ℝ (gradient f x) (-d) ≤ 0 := by
  rcases le_total (inner ℝ (gradient f x) d) 0 with h | h
  · exact Or.inl h
  · right
    rw [inner_neg_right]
    exact neg_nonpos.mpr h

/-- If the gradient pairing with `d` is nonzero, then one of `d` and `-d` is a strict descent
direction at `x`. -/
theorem isDescentDirectionAt_or_neg (f : E → ℝ) (x d : E)
    (h_nonorth : inner ℝ (gradient f x) d ≠ 0) :
    IsDescentDirectionAt f x d ∨ IsDescentDirectionAt f x (-d) := by
  rcases inner_gradient_nonpos_or_neg_nonpos f x d with h | h
  · left
    rcases eq_or_lt_of_le h with hEq | hlt
    · exact False.elim (h_nonorth hEq)
    · exact hlt
  · right
    have hneg_nonorth : inner ℝ (gradient f x) (-d) ≠ 0 := by
      simpa [inner_neg_right, neg_eq_zero] using h_nonorth
    rcases eq_or_lt_of_le h with hEq | hlt
    · exact False.elim (hneg_nonorth hEq)
    · exact hlt

/-- Helper for Chapter01 Definition 1.4.3: a real function with negative derivative at a root is
strictly negative on a sufficiently small interval `(0, δ)`. -/
lemma exists_posInterval_lt_zero_of_hasDerivAt_neg_zero {g : ℝ → ℝ} {g' : ℝ}
    (hg : HasDerivAt g g' 0) (hg' : g' < 0) (h0 : g 0 = 0) :
    ∃ δ > 0, ∀ α : ℝ, 0 < α → α < δ → g α < 0 := by
  -- Restrict the derivative-test sign information to the right-neighborhood filter.
  have hsign : ∀ᶠ α in 𝓝[>] (0 : ℝ), sign (g α) = sign (0 - α) := by
    exact
      (eventually_nhdsWithin_sign_eq_of_deriv_neg
        (f := g) (x₀ := 0) (by simpa [hg.deriv] using hg') h0).filter_mono nhdsWithin_le_nhds
  have hneg : {α : ℝ | g α < 0} ∈ 𝓝[>] (0 : ℝ) := by
    filter_upwards [hsign, self_mem_nhdsWithin] with α hαsign hαpos
    have hsignRight : sign (0 - α) = -1 := by
      exact sign_eq_neg_one_iff.mpr (sub_neg.mpr hαpos)
    have hsignG : sign (g α) = -1 := by rw [hαsign, hsignRight]
    exact sign_eq_neg_one_iff.mp hsignG
  -- Extract a concrete right interval contained in the negativity set.
  rcases mem_nhdsGT_iff_exists_Ioo_subset.mp hneg with ⟨δ, hδ, hδmem⟩
  refine ⟨δ, hδ, ?_⟩
  intro α hαpos hαδ
  exact hδmem ⟨hαpos, hαδ⟩

/-- Helper for Chapter01 Definition 1.4.3: the slice `α ↦ f (x + α • d) - f x` has derivative
`inner ℝ (gradient f x) d` at `0`. -/
lemma descentSlice_hasDerivAt {f : E → ℝ} {x d : E}
    (h : IsDescentDirectionAt f x d) :
    HasDerivAt (fun α : ℝ => f (x + α • d) - f x) (inner ℝ (gradient f x) d) 0 := by
  -- Differentiate the affine ray `α ↦ x + α • d`.
  have hray : HasDerivAt (fun α : ℝ => x + α • d) d 0 := by
    simpa using ((hasDerivAt_id' (x := (0 : ℝ))).smul_const d).const_add x
  -- Compose the Fréchet derivative of `f` at `x` with that ray.
  have hfd :
      HasFDerivAt f (fderiv ℝ f x) ((fun α : ℝ => x + α • d) 0) := by
    simpa using h.differentiableAt.hasFDerivAt
  have hsliceComp :
      HasDerivAt (f ∘ fun α : ℝ => x + α • d) (fderiv ℝ f x d) 0 := by
    exact hfd.comp_hasDerivAt (x := (0 : ℝ)) hray
  have hslice :
      HasDerivAt (fun α : ℝ => f (x + α • d)) (fderiv ℝ f x d) 0 := by
    change HasDerivAt (f ∘ fun α : ℝ => x + α • d) (fderiv ℝ f x d) 0
    exact hsliceComp
  -- Subtracting the constant value `f x` keeps the same derivative.
  simpa using hslice.sub_const (f x)

/-- Chapter01 Definition 1.4.3: a descent direction strictly decreases the objective along
sufficiently small positive steps in that direction. -/
theorem IsDescentDirectionAt.exists_localDecrease {f : E → ℝ} {x d : E}
    (h : IsDescentDirectionAt f x d) :
    ∃ δ > 0, ∀ α : ℝ, 0 < α → α < δ → f (x + α • d) < f x := by
  -- Reduce the multivariate statement to the scalar slice along the ray `x + α • d`.
  let g : ℝ → ℝ := fun α => f (x + α • d) - f x
  have hg : HasDerivAt g (inner ℝ (gradient f x) d) 0 := by
    simpa [g] using descentSlice_hasDerivAt h
  have hg' : inner ℝ (gradient f x) d < 0 := h.inner_gradient_neg
  have h0 : g 0 = 0 := by
    simp [g]
  rcases exists_posInterval_lt_zero_of_hasDerivAt_neg_zero hg hg' h0 with ⟨δ, hδ, hδneg⟩
  refine ⟨δ, hδ, ?_⟩
  intro α hαpos hαδ
  have hgα : g α < 0 := hδneg α hαpos hαδ
  simpa [g, sub_lt_iff_lt_add] using hgα

/-- The source textbook wording is equivalent to the canonical owner because the strict negative
gradient pairing already forces differentiability. -/
theorem isDescentDirectionAt_iff_differentiableAt_and_inner_gradient_neg
    (f : E → ℝ) (x d : E) :
    IsDescentDirectionAt f x d ↔
      DifferentiableAt ℝ f x ∧ inner ℝ (gradient f x) d < 0 := by
  constructor
  · intro h
    exact ⟨h.differentiableAt, h.inner_gradient_neg⟩
  · rintro ⟨_, hneg⟩
    exact hneg

end Chapter01Definition143
