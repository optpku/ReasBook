/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

module

public import OptimizationTheoryAndMethods_SunYuan_2006.Compat

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation

noncomputable section

public section

-- Semantic recall hits verified for this item: mathlib provides the more general locally convex
-- separation theorem `geometric_hahn_banach_closed_point`. The source-facing declarations below
-- keep the textbook's explicit separating-vector and `sSup` surfaces while using the chapter's
-- abstract real inner-product-space owner level.

section Theorem1321

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Helper for Chapter01 Theorem 1.3.21: transport the closed-point Hahn-Banach separator to an
explicit vector normal in the inner-product space. -/
lemma existsInnerStrictSeparationOfClosedPoint
    (S : Set E) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S) (y : E) (hy : y ∉ S) :
    ∃ p : E, ∃ α : ℝ, (∀ x ∈ S, inner ℝ p x < α) ∧ α < inner ℝ p y := by
  -- Use the owner theorem to separate `y` from `S` by a continuous linear functional.
  obtain ⟨f, α, hSlt, hylt⟩ := geometric_hahn_banach_closed_point hS_convex hS_closed hy
  refine ⟨(InnerProductSpace.toDual ℝ E).symm f, α, ?_, ?_⟩
  · -- Rewrite the functional separator as an inner-product separator on points of `S`.
    intro x hx
    simpa [InnerProductSpace.toDual_symm_apply] using hSlt x hx
  · -- The point-side strict inequality rewrites through the same Fréchet-Riesz equivalence.
    simpa [InnerProductSpace.toDual_symm_apply] using hylt

omit [CompleteSpace E] in
/-- Helper for Chapter01 Theorem 1.3.21: a strict separating inequality on a nonempty set cannot
come from the zero vector. -/
lemma nonzero_of_strictPointSeparation
    (S : Set E) (hS_nonempty : S.Nonempty) {p y : E} {α : ℝ}
    (hSlt : ∀ x ∈ S, inner ℝ p x < α) (hylt : α < inner ℝ p y) :
    p ≠ 0 := by
  -- If `p = 0`, the set-side and point-side strict inequalities collapse to `0 < α` and `α < 0`.
  intro hp
  obtain ⟨x, hx⟩ := hS_nonempty
  have hzero_lt : (0 : ℝ) < α := by
    simpa [hp] using hSlt x hx
  have hlt_zero : α < (0 : ℝ) := by
    simpa [hp] using hylt
  exact (lt_irrefl (0 : ℝ)) (hzero_lt.trans hlt_zero)

omit [CompleteSpace E] in
/-- Helper for Chapter01 Theorem 1.3.21: an upper bound on `inner ℝ p x` over `S` also bounds the
supremum of the image set `((fun x ↦ inner ℝ p x) '' S)`. -/
lemma sSup_innerImage_le_of_upperBound
    (S : Set E) (hS_nonempty : S.Nonempty) {p : E} {α : ℝ}
    (hbound : ∀ x ∈ S, inner ℝ p x ≤ α) :
    sSup ((fun x : E ↦ inner ℝ p x) '' S) ≤ α := by
  -- Produce a witness so `csSup_le` can be applied to the image set.
  have himage_nonempty : ((fun x : E ↦ inner ℝ p x) '' S).Nonempty := by
    obtain ⟨x, hx⟩ := hS_nonempty
    exact ⟨inner ℝ p x, ⟨x, hx, rfl⟩⟩
  -- Every element of the image set is bounded by the same `α`.
  exact csSup_le himage_nonempty fun z hz ↦ by
    rcases hz with ⟨x, hx, rfl⟩
    exact hbound x hx

/-- Chapter01 Theorem 1.3.21: if `S` is a nonempty closed convex subset of a complete real
inner-product space and `y ∉ S`, then there exist a nonzero vector `p` and a real number `α`
such that `α < inner ℝ p y` and `inner ℝ p x ≤ α` for every `x ∈ S`. The source states this on
`ℝ^n`; here the owner theorem is stated on the chapter's abstract real inner-product-space level,
which preserves the same separation semantics. -/
theorem existsNonzeroSeparatingVector
    (S : Set E) (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S)
    (hS_convex : Convex ℝ S) (y : E) (hy : y ∉ S) :
    ∃ p : E, p ≠ 0 ∧ ∃ α : ℝ, α < inner ℝ p y ∧ ∀ x ∈ S, inner ℝ p x ≤ α := by
  -- First obtain the strict separating sunYuanHyperplane on the source-facing inner-product surface.
  obtain ⟨p, α, hSlt, hylt⟩ :=
    existsInnerStrictSeparationOfClosedPoint S hS_closed hS_convex y hy
  -- Nonemptiness of `S` rules out the trivial separator `p = 0`.
  have hp_ne : p ≠ 0 := nonzero_of_strictPointSeparation S hS_nonempty hSlt hylt
  refine ⟨p, hp_ne, α, hylt, ?_⟩
  -- The theorem only needs a nonstrict upper bound on `S`, so we weaken the strict inequality.
  intro x hx
  exact (hSlt x hx).le

/-- Theorem 1.3.21 yields a nonzero `p` whose support
functional is bounded above on `S` and whose value at `y` is strictly larger than the
corresponding `sSup`. -/
theorem existsNonzeroSeparatingVector_gt_sSup
    (S : Set E) (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S)
    (hS_convex : Convex ℝ S) (y : E) (hy : y ∉ S) :
    ∃ p : E, p ≠ 0 ∧
      BddAbove ((fun x : E ↦ inner ℝ p x) '' S) ∧
        inner ℝ p y > sSup ((fun x : E ↦ inner ℝ p x) '' S) := by
  -- Reuse the separating vector from the first theorem and keep its upper bound `α`.
  obtain ⟨p, hp_ne, α, hylt, hbound⟩ :=
    existsNonzeroSeparatingVector S hS_nonempty hS_closed hS_convex y hy
  have hbdd : BddAbove ((fun x : E ↦ inner ℝ p x) '' S) := by
    -- The same separating level `α` is an upper bound for the image set.
    refine ⟨α, ?_⟩
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact hbound x hx
  have hsSup_le : sSup ((fun x : E ↦ inner ℝ p x) '' S) ≤ α :=
    sSup_innerImage_le_of_upperBound S hS_nonempty hbound
  refine ⟨p, hp_ne, hbdd, ?_⟩
  -- Compare the supremum with `α`, then use the strict point-side separation.
  simpa using hsSup_le.trans_lt hylt

end Theorem1321

end
