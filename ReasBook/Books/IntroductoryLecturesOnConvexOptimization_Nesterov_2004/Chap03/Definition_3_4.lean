/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_4

noncomputable section

open scoped BigOperators
open ConvexSpace

universe u v w

-- Declarations for this item will be appended below by the statement pipeline.

/-
Definition 3.4 lies in the finite convex-combination domain over an ordered scalar ring, with the
extra source-facing requirement that every coefficient be strictly positive.

Sampled owner-style declarations:
- `StdSimplex`
- `StdSimplex.IsStrict`
- `is_convex_combination_of`
- `StdSimplex.map`
- `ConvexSpace.convexCombination`
- `convexCombination_eq_sum`

Best owner abstraction:
- `convexCombination (w.1.map points)` for `w : StdSimplex.Strict R ι`

Primitive data:
- a strict simplex weight vector `w : StdSimplex.Strict R ι`
- a finite family `points : ι → E`

Derived API:
- the owner predicate `StdSimplex.IsStrict`
- the reusable strict subtype view `StdSimplex.Strict`
- the derived finiteness lemma `StdSimplex.Strict.finite`
- the source-facing strict-convex-combination predicate
- the bridge to the earlier owner predicate `is_convex_combination_of`
- the coefficient bridge theorem

Source/core/bridge triage:
- source-facing: `is_strict_convex_combination_of R points x`
- core/canonical: `w : StdSimplex.Strict R ι` and `convexCombination (w.1.map points)`
- bridge/view:
  `is_strict_convex_combination_of.is_convex_combination_of`
  and
  `is_strict_convex_combination_of_iff_exists_coefficients`

The earlier chapter file `Definition_3_1_1_4` already owns the finite convex-combination notion,
so this file reuses that finite-family owner directly, with `StdSimplex.IsStrict` as the
strictness predicate and `StdSimplex.Strict` as the corresponding strict owner view. The strict
simplex witness already forces `ι` to be finite, so the source-facing predicate derives finiteness
internally instead of storing it as separate public data. Later files with strictly positive
simplex data should reuse this owner-based API instead of reintroducing a parallel top-level
alias. -/

namespace StdSimplex

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

/-- A simplex weight vector is strict when every coefficient is strictly positive. -/
def IsStrict {ι : Type*} (w : StdSimplex R ι) : Prop :=
  ∀ i, 0 < w.weights i

/-- The subtype of strict simplex weight vectors. -/
abbrev Strict (R : Type u) [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] (ι : Type*) :=
  {w : StdSimplex R ι // w.IsStrict}

theorem Strict.finite {ι : Type*} (w : StdSimplex.Strict R ι) : Finite ι := by
  classical
  let f : ι ↪ {i // i ∈ w.1.weights.support} :=
    ⟨fun i ↦ ⟨i, by
        rw [Finsupp.mem_support_iff]
        exact ne_of_gt (w.2 i)⟩,
      fun _ _ h ↦ Subtype.mk.inj h⟩
  exact Finite.of_injective f f.injective

end StdSimplex

section Owner

variable (R : Type u) [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
variable {ι : Type v}
variable {E : Type w} [ConvexSpace R E]

/-- Definition 3.4: a point is a strict convex combination of a finite family of points when it is
the canonical convex combination associated to a strict simplex weight vector. -/
def is_strict_convex_combination_of (points : ι → E) (x : E) : Prop :=
  ∃ w : StdSimplex.Strict R ι, x = convexCombination (w.1.map points)

/-- A strict convex combination is, in particular, an ordinary convex combination of the same
family. -/
theorem is_strict_convex_combination_of.is_convex_combination_of
    {points : ι → E} {x : E}
    (h : is_strict_convex_combination_of R points x) :
    is_convex_combination_of R points x := by
  rcases h with ⟨w, hw⟩
  letI : Finite ι := w.finite
  let _ : Fintype ι := Fintype.ofFinite ι
  exact ⟨w, hw⟩

end Owner

section Module

variable {ι : Type v} [Fintype ι]
variable {R : Type u} [PartialOrder R] [Ring R] [IsStrictOrderedRing R]
variable {E : Type w} [AddCommGroup E] [Module R E]

/-- Unpacking a strict convex combination into coefficient data gives exactly the textbook formula
with positive coefficients summing to `1`. -/
-- Proof sketch: unpack a strict `StdSimplex` weight vector into its coefficient function, read off
-- normalization from the underlying `StdSimplex`, rewrite the canonical convex combination by
-- `StdSimplex.convexCombination_map_eq_sum`, and read strict positivity from `w.IsStrict`;
-- conversely,
-- package the coefficient family into a `StdSimplex`, prove it strict using the positivity
-- hypothesis, and then recover the canonical convex combination.
theorem is_strict_convex_combination_of_iff_exists_coefficients
    (points : ι → E) (x : E) :
    is_strict_convex_combination_of R points x ↔
      ∃ α : ι → R, (∀ i, 0 < α i) ∧ (∑ i, α i) = 1 ∧ x = ∑ i, α i • points i := by
  unfold is_strict_convex_combination_of
  constructor
  · rintro ⟨w, hwx⟩
    refine ⟨w.1.weights, w.2, ?_, ?_⟩
    · simpa [Finsupp.sum_fintype] using w.1.total
    · simpa [StdSimplex.convexCombination_map_eq_sum R w.1 points] using hwx
  · rintro ⟨α, hα_pos, hα_sum, rfl⟩
    let w : StdSimplex.Strict R ι :=
      ⟨⟨Finsupp.equivFunOnFinite.symm α,
          by simpa using fun i ↦ (hα_pos i).le,
          by simpa using (Finsupp.equivFunOnFinite_symm_sum α).trans hα_sum⟩,
        hα_pos⟩
    refine ⟨w, ?_⟩
    simpa [w] using (StdSimplex.convexCombination_map_eq_sum R w.1 points).symm

end Module
