/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Text_2_0_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corollary_8_5

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

/-- Helper for Theorem 9.1: the real lower level set of the weak-space companion of `f` is exactly
the weak-space image of the original real lower level set. -/
private lemma lowerLevelSet_comp_toWeakSpace_symm_eq_image {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (ξ : ℝ) :
    lowerLevelSet (f ∘ (toWeakSpace ℝ H).symm) ξ =
      (toWeakSpace ℝ H) '' lowerLevelSet f ξ := by
  ext y
  constructor
  · intro hy
    -- Pull the weak-space point back along the canonical equivalence.
    refine ⟨(toWeakSpace ℝ H).symm y, ?_, (toWeakSpace ℝ H).apply_symm_apply y⟩
    simpa [lowerLevelSet, Function.comp] using hy
  · rintro ⟨x, hx, rfl⟩
    -- Pushing forward a strong-space point preserves the lower level inequality.
    simpa [lowerLevelSet, Function.comp] using hx

/-- Helper for Theorem 9.1: the weak sequential liminf condition is equivalent to sequential
closedness of all weak lower level sets. -/
private lemma weak_seq_lsc_iff_forall_isSeqClosed_weak_lowerLevelSet {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : H → EReal) :
    (∀ ⦃xₙ : ℕ → H⦄ ⦃x : H⦄,
        Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x)) →
          f x ≤ liminf (f ∘ xₙ) atTop) ↔
      ∀ ξ : ℝ, IsSeqClosed ((toWeakSpace ℝ H) '' lowerLevelSet f ξ) := by
  let g : WeakSpace ℝ H → EReal := f ∘ (toWeakSpace ℝ H).symm
  have htransport :
      (∀ ⦃xₙ : ℕ → H⦄ ⦃x : H⦄,
          Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x)) →
            f x ≤ liminf (f ∘ xₙ) atTop) ↔
        (∀ ⦃u : ℕ → WeakSpace ℝ H⦄ ⦃x : WeakSpace ℝ H⦄,
          Tendsto u atTop (𝓝 x) →
            g x ≤ liminf (g ∘ u) atTop) := by
    constructor
    · intro h xₙ x hx
      -- Reinterpret weak convergence in `H` as ordinary convergence in `WeakSpace`.
      simpa [g, Function.comp] using
        h (xₙ := fun n ↦ (toWeakSpace ℝ H).symm (xₙ n)) (x := (toWeakSpace ℝ H).symm x) hx
    · intro h xₙ x hx
      -- Push a strong-space sequence into `WeakSpace` to recover the weak formulation.
      simpa [g, Function.comp] using
        h (u := fun n ↦ toWeakSpace ℝ H (xₙ n)) (x := toWeakSpace ℝ H x) hx
  have hg :
      (∀ ⦃u : ℕ → WeakSpace ℝ H⦄ ⦃x : WeakSpace ℝ H⦄,
          Tendsto u atTop (𝓝 x) →
            g x ≤ liminf (g ∘ u) atTop) ↔
        ∀ ξ : ℝ, IsSeqClosed (lowerLevelSet g ξ) := by
    exact
      List.TFAE.out
        (sequentialLowerSemicontinuous_real_epigraph_seqClosed_lowerLevelSet_seqClosed_tfae g)
        0 2
  -- Combine the transport equivalence with the lower-level-set identification in `WeakSpace`.
  exact htransport.trans <|
    by
      simpa [g, lowerLevelSet_comp_toWeakSpace_symm_eq_image] using hg

/-- Helper for Theorem 9.1: the strong sequential liminf condition is equivalent to sequential
closedness of all strong lower level sets. -/
private lemma seq_lsc_iff_forall_isSeqClosed_lowerLevelSet {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) :
    (∀ ⦃xₙ : ℕ → H⦄ ⦃x : H⦄,
        Tendsto xₙ atTop (𝓝 x) →
          f x ≤ liminf (f ∘ xₙ) atTop) ↔
      ∀ ξ : ℝ, IsSeqClosed (lowerLevelSet f ξ) := by
  -- This is exactly the lower-level-set formulation from Lemma 1.36.
  exact
    List.TFAE.out
      (sequentialLowerSemicontinuous_real_epigraph_seqClosed_lowerLevelSet_seqClosed_tfae f)
      0 2

/-- Helper for Theorem 9.1: weak lower semicontinuity is equivalent to closedness of all weak
lower level sets. -/
private lemma weak_lsc_iff_forall_isClosed_weak_lowerLevelSet {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : H → EReal) :
    WeaklyLowerSemicontinuous f ↔
      ∀ ξ : ℝ, IsClosed ((toWeakSpace ℝ H) '' lowerLevelSet f ξ) := by
  let g : WeakSpace ℝ H → EReal := f ∘ (toWeakSpace ℝ H).symm
  -- Unfold weak lower semicontinuity as ordinary lower semicontinuity on `WeakSpace`.
  simpa [WeaklyLowerSemicontinuous, g, lowerLevelSet_comp_toWeakSpace_symm_eq_image] using
    (lowerSemicontinuous_iff_isClosed_lowerLevelSet g)

/-- Helper for Theorem 9.1: convexity of the lower level sets identifies strong and weak
sequential closedness pointwise. -/
private lemma forall_isSeqClosed_lowerLevelSet_iff_forall_isSeqClosed_weak_lowerLevelSet
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {f : H → EReal}
    (hlevel : ∀ ξ : ℝ, Convex ℝ (lowerLevelSet f ξ)) :
    (∀ ξ : ℝ, IsSeqClosed (lowerLevelSet f ξ)) ↔
      ∀ ξ : ℝ, IsSeqClosed ((toWeakSpace ℝ H) '' lowerLevelSet f ξ) := by
  constructor
  · intro h ξ
    -- Theorem 3.34 compares strong and weak sequential closedness for convex sets.
    exact
      (isSeqClosed_iff_weak_image_isSeqClosed_of_convex
        (hlevel ξ)).1 (h ξ)
  · intro h ξ
    -- Pull weak sequential closedness back to the original lower level set.
    exact
      (isSeqClosed_iff_weak_image_isSeqClosed_of_convex
        (hlevel ξ)).2 (h ξ)

/-- Helper for Theorem 9.1: in a Hilbert space, sequential closedness and closedness agree for the
strong lower level sets. -/
private lemma forall_isSeqClosed_lowerLevelSet_iff_forall_isClosed_lowerLevelSet {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : H → EReal) :
    (∀ ξ : ℝ, IsSeqClosed (lowerLevelSet f ξ)) ↔
      ∀ ξ : ℝ, IsClosed (lowerLevelSet f ξ) := by
  constructor
  · intro h ξ
    -- The norm topology is metrizable, so sequential closedness is closedness.
    exact
      (isSeqClosed_iff_isClosed : IsSeqClosed (lowerLevelSet f ξ) ↔
        IsClosed (lowerLevelSet f ξ)).1 (h ξ)
  · intro h ξ
    -- Closed sets are sequentially closed in the strong topology.
    exact
      (isSeqClosed_iff_isClosed : IsSeqClosed (lowerLevelSet f ξ) ↔
        IsClosed (lowerLevelSet f ξ)).2 (h ξ)

/-- Helper for Theorem 9.1: convexity of the lower level sets identifies strong and weak
closedness pointwise. -/
private lemma forall_isClosed_lowerLevelSet_iff_forall_isClosed_weak_lowerLevelSet {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {f : H → EReal}
    (hlevel : ∀ ξ : ℝ, Convex ℝ (lowerLevelSet f ξ)) :
    (∀ ξ : ℝ, IsClosed (lowerLevelSet f ξ)) ↔
      ∀ ξ : ℝ, IsClosed ((toWeakSpace ℝ H) '' lowerLevelSet f ξ) := by
  constructor
  · intro h ξ
    -- Theorem 3.34 compares strong and weak closedness for convex sets.
    exact
      (isClosed_iff_weak_image_isClosed_of_convex
        (hlevel ξ)).1 (h ξ)
  · intro h ξ
    -- Pull weak closedness back to the original lower level set.
    exact
      (isClosed_iff_weak_image_isClosed_of_convex
        (hlevel ξ)).2 (h ξ)

-- Proof sketch: express each of the four lower semicontinuity conditions through closedness or
-- sequential closedness of the real lower level sets, then compare strong and weak versions of
-- those set-theoretic conditions with Theorem 3.34 using the convexity hypothesis on every lower
-- level set.
/-- For an extended-real-valued function whose real lower level sets are convex, weak sequential
lower semicontinuity, strong sequential lower semicontinuity, strong lower semicontinuity, and
weak lower semicontinuity are equivalent. -/
theorem lowerSemicontinuity_tfae_of_convex_lowerLevelSet {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {f : H → EReal}
    (hlevel : ∀ ξ : ℝ, Convex ℝ (lowerLevelSet f ξ)) :
    List.TFAE
      [ (∀ ⦃xₙ : ℕ → H⦄ ⦃x : H⦄,
            Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x)) →
              f x ≤ liminf (f ∘ xₙ) atTop),
        (∀ ⦃xₙ : ℕ → H⦄ ⦃x : H⦄,
            Tendsto xₙ atTop (𝓝 x) →
              f x ≤ liminf (f ∘ xₙ) atTop),
        LowerSemicontinuous f,
        WeaklyLowerSemicontinuous f ] := by
  -- Compare the weak and strong sequential clauses through the convex lower level sets.
  tfae_have 1 ↔ 2 := by
    exact
      (weak_seq_lsc_iff_forall_isSeqClosed_weak_lowerLevelSet (H := H) f).trans <|
        (forall_isSeqClosed_lowerLevelSet_iff_forall_isSeqClosed_weak_lowerLevelSet
          (H := H) (f := f) hlevel).symm.trans <|
          (seq_lsc_iff_forall_isSeqClosed_lowerLevelSet (H := H) f).symm
  -- In the strong topology, sequential lower semicontinuity is equivalent to lower semicontinuity.
  tfae_have 2 ↔ 3 := by
    exact
      (seq_lsc_iff_forall_isSeqClosed_lowerLevelSet (H := H) f).trans <|
        (forall_isSeqClosed_lowerLevelSet_iff_forall_isClosed_lowerLevelSet
          (H := H) f).trans <|
          (lowerSemicontinuous_iff_isClosed_lowerLevelSet f).symm
  -- Compare the strong and weak closedness clauses through the same convex lower level sets.
  tfae_have 3 ↔ 4 := by
    exact
      (lowerSemicontinuous_iff_isClosed_lowerLevelSet f).trans <|
        (forall_isClosed_lowerLevelSet_iff_forall_isClosed_weak_lowerLevelSet
          (H := H) (f := f) hlevel).trans <|
          (weak_lsc_iff_forall_isClosed_weak_lowerLevelSet (H := H) f).symm
  tfae_finish

-- Proof sketch: by Lemma 1.24 and Lemma 1.36, each lower semicontinuity notion is equivalent to
-- closedness or sequential closedness of the real-height epigraph. Since `epigraph f` is convex by
-- hypothesis, Theorem 3.34 identifies its weak and strong closedness and sequential closedness.
/-- Theorem 9.1: for a convex extended-real-valued function on a real Hilbert space, weak
sequential lower semicontinuity, strong sequential lower semicontinuity, strong lower
semicontinuity, and weak lower semicontinuity are equivalent. The weak conditions are expressed
through `toWeakSpace ℝ H` and `WeaklyLowerSemicontinuous`. -/
theorem convex_lowerSemicontinuity_tfae {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {f : H → EReal} (hconv : Convex ℝ (epigraph f)) :
    List.TFAE
      [ (∀ ⦃xₙ : ℕ → H⦄ ⦃x : H⦄,
            Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x)) →
              f x ≤ liminf (f ∘ xₙ) atTop),
        (∀ ⦃xₙ : ℕ → H⦄ ⦃x : H⦄,
            Tendsto xₙ atTop (𝓝 x) →
              f x ≤ liminf (f ∘ xₙ) atTop),
        LowerSemicontinuous f,
        WeaklyLowerSemicontinuous f ] := by
  exact lowerSemicontinuity_tfae_of_convex_lowerLevelSet
    (H := H) (f := f) (fun ξ ↦ convex_lowerLevelSet_of_convex_epigraph f hconv ξ)

end ERealFunction
