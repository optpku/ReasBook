/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Lemma_2_1
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper for Lemma 2.6: an inner-product upper bound on every `b ∈ B` yields the corresponding
upper bound on the primal support function `σ[B]`. -/
lemma supportFunctionPrimal_le_of_inner_sub_nonpos (B : Set E) (u p : E)
    (hsep : ∀ b ∈ B, inner ℝ u (b - p) ≤ 0) :
    σ[B] u ≤ (inner ℝ u p : EReal) := by
  -- Normalize `σ[B]` to the `sSup` formula and bound each pointwise pairing by `⟪u, p⟫`.
  rw [support_function_eq_sSup]
  refine sSup_le ?_
  rintro _ ⟨b, hb, rfl⟩
  have hsub : inner ℝ u b - inner ℝ u p ≤ 0 := by
    simpa [inner_sub_right] using hsep b hb
  have hreal : inner ℝ u b ≤ inner ℝ u p := by
    linarith
  have hereal : ((inner ℝ u b : ℝ) : EReal) ≤ ((inner ℝ u p : ℝ) : EReal) := by
    exact_mod_cast hreal
  simpa using hereal

/-- Helper for Lemma 2.6: a point of `A` lying outside a nonempty closed convex set `B` produces
some direction whose primal support function is strictly larger on `A` than on `B`. -/
lemma existsSupportFunctionGapOfMemNotMemClosedConvex (A B : Set E) {x : E} (hxA : x ∈ A)
    (hxB : x ∉ B) (hB_nonempty : B.Nonempty) (hB_closed : IsClosed B) (hB_convex : Convex ℝ B) :
    ∃ u, σ[B] u < σ[A] u := by
  -- Choose the metric projection of `x` onto `B`; mathlib's projection theorem gives the
  -- variational inequality needed to control the support function of `B`.
  obtain ⟨p, hpB, hpmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hB_nonempty hB_closed.isComplete hB_convex x
  let u : E := x - p
  have hsep : ∀ b ∈ B, inner ℝ u (b - p) ≤ 0 := by
    exact (norm_eq_iInf_iff_real_inner_le_zero hB_convex hpB).1 (by simpa [u] using hpmin)
  have hB_le : σ[B] u ≤ (inner ℝ u p : EReal) :=
    supportFunctionPrimal_le_of_inner_sub_nonpos B u p hsep
  -- The witness `x ∈ A` gives the lower bound on `σ[A]`.
  have hA_ge : (inner ℝ u x : EReal) ≤ σ[A] u := by
    simpa [support_function_primal_apply, InnerProductSpace.toDualMap_apply_apply] using
      (le_support_function_of_mem hxA (InnerProductSpace.toDualMap ℝ E u))
  have hx_ne_p : x ≠ p := by
    intro hxp
    exact hxB (hxp ▸ hpB)
  have hu_ne_zero : u ≠ 0 := by
    exact sub_ne_zero.mpr hx_ne_p
  have hu_sq_pos : 0 < ‖u‖ ^ (2 : ℕ) := by
    nlinarith [norm_pos_iff.mpr hu_ne_zero]
  -- Rewrite `⟪u, x⟫` as `⟪u, p⟫ + ‖u‖²` to obtain the strict gap.
  have hinner : inner ℝ u x = inner ℝ u p + ‖u‖ ^ (2 : ℕ) := by
    calc
      inner ℝ u x = inner ℝ u (p + u) := by
        have hx_expr : x = p + u := by
          simp [u]
        rw [hx_expr]
      _ = inner ℝ u p + inner ℝ u u := by
        rw [inner_add_right]
      _ = inner ℝ u p + ‖u‖ ^ (2 : ℕ) := by
        simp
  have hp_lt_hx : inner ℝ u p < inner ℝ u x := by
    linarith
  have hcoef_lt : ((inner ℝ u p : ℝ) : EReal) < (inner ℝ u x : EReal) := by
    exact_mod_cast hp_lt_hx
  exact ⟨u, lt_of_le_of_lt hB_le (lt_of_lt_of_le hcoef_lt hA_ge)⟩

/-- Helper for Lemma 2.6: if two primal support functions agree and the right-hand set is closed
and convex, then the left-hand set is contained in the right-hand set. -/
lemma subset_of_support_function_eq_of_closed_convex_right
    (A B : Set E) (hB_closed : IsClosed B) (hB_convex : Convex ℝ B) (hσ : σ[A] = σ[B]) :
    A ⊆ B := by
  intro x hxA
  by_cases hB_nonempty : B.Nonempty
  · by_contra hxB
    -- A counterexample `x ∈ A \ B` yields a strict support-function gap, contradicting `hσ`.
    obtain ⟨u, hgap⟩ :=
      existsSupportFunctionGapOfMemNotMemClosedConvex A B hxA hxB hB_nonempty hB_closed hB_convex
    have hu_eq : σ[A] u = σ[B] u := congrArg (fun f : E → EReal ↦ f u) hσ
    have hself : σ[B] u < σ[B] u := by
      have hgap' := hgap
      rw [hu_eq] at hgap'
      exact hgap'
    exact lt_irrefl _ hself
  · have hB_empty : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB_nonempty
    -- If `B = ∅`, then equality of support functions forces `A = ∅` as well.
    have hA_ne_bot : σ[A] (0 : E) ≠ ⊥ := by
      have hA_nonempty : A.Nonempty := ⟨x, hxA⟩
      simpa [support_function_primal_apply] using
        support_function_ne_bot A hA_nonempty (InnerProductSpace.toDualMap ℝ E (0 : E))
    have hzero_eq : σ[A] (0 : E) = σ[B] (0 : E) := congrArg (fun f : E → EReal ↦ f 0) hσ
    have hB_bot : σ[B] (0 : E) = ⊥ := by
      rw [hB_empty, support_function_primal_apply, support_function_apply]
      simp
    exact (hA_ne_bot (hzero_eq.trans hB_bot)).elim

-- Proof sketch: if `A = B`, then the primal-space support functions `σ[A]` and `σ[B]` agree by
-- substitution. Conversely, if `σ[A] = σ[B]`, then completeness identifies every continuous linear
-- functional with an inner-product functional via `InnerProductSpace.toDual`. If one set is empty,
-- the common support function is constantly `⊥`, so both sets are empty. Otherwise, if `x ∈ A \ B`,
-- apply strict separation to the closed convex set `B` and the point `x`; transport the
-- separating functional across Fréchet-Riesz to get a vector representation, yielding a
-- contradiction to support-function equality. Symmetry gives the reverse inclusion.
/-- Lemma 2.6: two closed convex sets in a real inner product space are equal if and only if their
primal-space support functions `σ[A]` and `σ[B]` agree. This uses the chapter owner
`support_function_primal`, the source-facing specialization of `support_function` along
`InnerProductSpace.toDualMap`; the finite-dimensional Euclidean hypothesis supplies the
Fréchet-Riesz identification with the continuous dual used in the converse direction. -/
theorem eq_iff_support_function_eq_of_closed_convex
    (A B : Set E) (hA_closed : IsClosed A) (hA_convex : Convex ℝ A)
    (hB_closed : IsClosed B) (hB_convex : Convex ℝ B) :
    A = B ↔ σ[A] = σ[B] := by
  constructor
  · -- The forward direction is immediate by substitution.
    intro hAB
    subst hAB
    rfl
  · -- Route correction: instead of a later-chapter dual wrapper, use the dependency-ordered
    -- projection argument from mathlib and prove the two set inclusions separately.
    intro hσ
    apply Set.Subset.antisymm
    · exact subset_of_support_function_eq_of_closed_convex_right A B hB_closed hB_convex hσ
    · exact subset_of_support_function_eq_of_closed_convex_right B A hA_closed hA_convex hσ.symm

/-- Converse direction of Lemma 2.6, exposed as a direct callable theorem: equality of the
primal-space support functions of two closed convex sets forces equality of the sets. -/
theorem eq_of_support_function_eq_of_closed_convex
    (A B : Set E) (hA_closed : IsClosed A) (hA_convex : Convex ℝ A)
    (hB_closed : IsClosed B) (hB_convex : Convex ℝ B)
    (hσ : σ[A] = σ[B]) :
    A = B :=
  (eq_iff_support_function_eq_of_closed_convex
    A B hA_closed hA_convex hB_closed hB_convex).2 hσ

end
