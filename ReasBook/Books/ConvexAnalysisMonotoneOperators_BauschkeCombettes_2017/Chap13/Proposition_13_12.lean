/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_5
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: expand epigraph membership into `conjugate f u ≤ μ`, unfold the supremum
-- definition of `conjugate f u`, and rewrite the resulting pointwise inequalities into the affine
-- minorant form `⟪x,u⟫ - μ ≤ f x`.
/-- Proposition 13.12 (1): clause (i). A point `(u, μ)` lies in the epigraph of the conjugate if
and only if the continuous affine functional `x ↦ ⟪x, u⟫ - μ` is a minorant of `f`. -/
theorem mem_epigraph_conjugate_iff
    (f : H → EReal) (u : H) (μ : ℝ) :
    (u, μ) ∈ epigraph f∗ ↔
      ∀ x : H, (((⟪x, u⟫_ℝ - μ : ℝ) : EReal) ≤ f x) := sorry

/-- A slope `u` belongs to the domain of `f*` exactly when `f` admits a continuous affine
minorant with that slope. -/
theorem mem_dom_conjugate_iff_hasContinuousAffineMinorantWithSlope
    (f : H → EReal) (u : H) :
    u ∈ dom f∗ ↔ HasContinuousAffineMinorantWithSlope f u := by
  constructor
  · intro hu
    have hnot : ¬ ∀ μ : ℝ, (μ : EReal) < f∗ u := by
      intro hμ
      exact (mem_dom_iff_ne_top _ _).1 hu <| (EReal.eq_top_iff_forall_lt (f∗ u)).2 hμ
    rcases not_forall.mp hnot with ⟨μ, hμ⟩
    have hmem : (u, μ) ∈ epigraph f∗ := by
      rw [mem_epigraph_iff]
      exact le_of_not_gt hμ
    refine ⟨-μ, ?_⟩
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (mem_epigraph_conjugate_iff f u μ).1 hmem
  · rintro ⟨η, hη⟩
    have hmem : (u, -η) ∈ epigraph f∗ := by
      refine (mem_epigraph_conjugate_iff f u (-η)).2 ?_
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hη
    rw [mem_dom_iff]
    exact lt_of_le_of_lt ((mem_epigraph_iff _ _ _).1 hmem)
      (EReal.coe_lt_top (-η))

-- Proof sketch: the pointwise bridge `u ∈ dom (conjugate f) ↔ HasContinuousAffineMinorantWithSlope
-- f u` identifies the absence of continuous affine minorants with `dom (conjugate f) = ∅`, which
-- is equivalent to `conjugate f = fun _ ↦ ⊤`.
/-- Proposition 13.12 (2): clause (ii). The conjugate is identically `+∞` exactly when `f`
admits no continuous affine minorant. -/
theorem conjugate_eq_top_iff_no_continuousAffineMinorant
    (f : H → EReal) :
    f∗ = (fun _ : H ↦ (⊤ : EReal)) ↔
      ¬ ∃ u : H, HasContinuousAffineMinorantWithSlope f u := by
  constructor
  · intro htop
    rintro ⟨u, hu⟩
    have hu' : u ∈ dom f∗ :=
      (mem_dom_conjugate_iff_hasContinuousAffineMinorantWithSlope f u).2 hu
    exact (mem_dom_iff_ne_top _ _).1 hu' <| by
      simpa using congrFun htop u
  · intro hminorant
    ext u
    by_contra hu
    exact hminorant ⟨u,
      (mem_dom_conjugate_iff_hasContinuousAffineMinorantWithSlope f u).1
        ((mem_dom_iff_ne_top _ _).2 hu)⟩

-- Proof sketch: if `dom (conjugate f)` is nonempty, the domain bridge above gives a continuous
-- affine minorant `x ↦ ⟪x,u⟫ + η` of `f`. On a bounded set `C`, Cauchy-Schwarz bounds `⟪x,u⟫`
-- uniformly from below, yielding a real constant `m` with `m ≤ f x` for all `x ∈ C`.
/-- Proposition 13.12 (3): clause (iii). If the conjugate has nonempty domain, then `f` is bounded
below on every bounded subset of the Hilbert space. -/
theorem exists_real_lowerBound_on_bounded_set_of_dom_conjugate_nonempty
    (f : H → EReal) (hdom : (dom f∗).Nonempty) (C : Set H) (hC : Bornology.IsBounded C) :
    ∃ m : ℝ, ∀ x ∈ C, (m : EReal) ≤ f x := sorry

end Conjugation

end ERealFunction
