/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_34

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

noncomputable section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗]

/-- The metric closed unit ball centered at `0` is the norm unit ball. -/
private lemma closedBall_zero_one_eq :
    (Metric.closedBall (0 : 𝓗) 1 : Set 𝓗) = {x : 𝓗 | ‖x‖ ≤ 1} := by
  ext x
  simp [Metric.mem_closedBall, dist_eq_norm]

variable [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

/-- Helper for Lemma 2.36: compactness of the weak image bounds each scalar evaluation coming from
the Riesz family. -/
private lemma pointwise_bounded_riesz_family_of_isCompact
    {C : Set 𝓗} (hC : IsCompact ((toWeakSpace ℝ 𝓗) '' C)) :
    ∀ u : 𝓗, ∃ M : ℝ, ∀ x ∈ C, ‖(InnerProductSpace.toDual ℝ 𝓗 x) u‖ ≤ M := by
  intro u
  let evalAt : WeakSpace ℝ 𝓗 → ℝ :=
    fun z ↦ (InnerProductSpace.toDual ℝ 𝓗 u) ((toWeakSpace ℝ 𝓗).symm z)
  have heval : Continuous evalAt := by
    -- Weak-space coordinates are exactly evaluations against continuous linear functionals.
    simpa [evalAt, WeakSpace, LinearMap.flip_apply, topDualPairing_apply] using
      (WeakBilin.eval_continuous ((topDualPairing ℝ 𝓗).flip)
        (InnerProductSpace.toDual ℝ 𝓗 u))
  obtain ⟨M, hM⟩ := (hC.image heval).isBounded.exists_norm_le
  refine ⟨M, ?_⟩
  intro x hx
  have hxImage : evalAt (toWeakSpace ℝ 𝓗 x) ∈ evalAt '' ((toWeakSpace ℝ 𝓗) '' C) := by
    exact ⟨toWeakSpace ℝ 𝓗 x, ⟨x, hx, rfl⟩, rfl⟩
  have hbound : ‖evalAt (toWeakSpace ℝ 𝓗 x)‖ ≤ M := hM _ hxImage
  -- For real Hilbert spaces, swapping the two arguments of the inner product does not change the
  -- value, so the bound matches the desired Riesz functional.
  simpa [evalAt, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hbound

/-- Helper for Lemma 2.36: a weakly compact set in a real Hilbert space is norm-bounded. -/
private lemma isBounded_of_isCompact_weakImage
    {C : Set 𝓗} (hC : IsCompact ((toWeakSpace ℝ 𝓗) '' C)) :
    Bornology.IsBounded C := by
  let T : C → 𝓗 →L[ℝ] ℝ := fun x ↦ InnerProductSpace.toDual ℝ 𝓗 x.1
  have hpointwise : ∀ u : 𝓗, ∃ M : ℝ, ∀ x : C, ‖T x u‖ ≤ M := by
    intro u
    rcases pointwise_bounded_riesz_family_of_isCompact hC u with ⟨M, hM⟩
    exact ⟨M, fun x ↦ hM x x.2⟩
  obtain ⟨M, hM⟩ := banach_steinhaus hpointwise
  rw [isBounded_iff_forall_norm_le]
  refine ⟨M, ?_⟩
  intro x hx
  have hTx : ‖InnerProductSpace.toDual ℝ 𝓗 x‖ ≤ M := by
    simpa [T] using hM ⟨x, hx⟩
  rw [(InnerProductSpace.toDual ℝ 𝓗).norm_map x] at hTx
  exact hTx

/-- The weak image of any scalar multiple of the closed unit ball is compact. -/
lemma isCompact_weakImage_smul_unit_ball (a : ℝ) :
    IsCompact ((toWeakSpace ℝ 𝓗) '' (a • {x : 𝓗 | ‖x‖ ≤ 1})) := by
  have hunit :
      IsCompact ((toWeakSpace ℝ 𝓗) '' {x : 𝓗 | ‖x‖ ≤ 1} : Set (WeakSpace ℝ 𝓗)) :=
    by
      simpa [closedBall_zero_one_eq] using
        (isCompact_unitBall_weakSpace :
          IsCompact
            ((toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)))
  have hsmul :
      IsCompact
        (a • ((toWeakSpace ℝ 𝓗) '' {x : 𝓗 | ‖x‖ ≤ 1} : Set (WeakSpace ℝ 𝓗))) :=
    IsCompact.smul a hunit
  -- The canonical weak embedding is linear, so it commutes with scalar multiplication on sets.
  convert hsmul using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨toWeakSpace ℝ 𝓗 y, ⟨y, hy, rfl⟩, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    rcases hw with ⟨y, hy, rfl⟩
    exact ⟨a • y, ⟨y, hy, rfl⟩, by simp⟩

/-- Lemma 2.36: a subset of a real Hilbert space is weakly compact if and only if it is weakly
closed and norm-bounded. Here weak compactness and weak closedness are expressed by viewing the set
inside `WeakSpace ℝ 𝓗`. -/
-- Proof sketch: for the forward implication, compact subsets of the weak topology are weakly
-- closed because `WeakSpace ℝ 𝓗` is Hausdorff, and compactness of all scalar evaluation images
-- gives pointwise boundedness, which the uniform boundedness principle upgrades to norm
-- boundedness. For the converse, place the bounded set inside a closed ball, use weak compactness
-- of that closed ball in a Hilbert space, and then apply closedness in the weak topology.
theorem weaklyCompact_iff_weaklyClosed_and_bounded {C : Set 𝓗} :
    IsCompact ((toWeakSpace ℝ 𝓗) '' C) ↔
      IsClosed ((toWeakSpace ℝ 𝓗) '' C) ∧ Bornology.IsBounded C := by
  constructor
  · intro hC
    -- Compact subsets of the weak topology are closed, and Banach-Steinhaus upgrades the
    -- coordinatewise compactness bounds to a uniform norm bound.
    exact ⟨hC.isClosed, isBounded_of_isCompact_weakImage hC⟩
  · rintro ⟨hclosed, hbounded⟩
    rcases (NormedSpace.isBounded_iff_subset_smul_closedBall ℝ).1 hbounded with ⟨a, ha⟩
    have hsubset :
        C ⊆ a • {x : 𝓗 | ‖x‖ ≤ 1} := by
      simpa [closedBall_zero_one_eq] using ha
    have hcompactAmbient :
        IsCompact ((toWeakSpace ℝ 𝓗) '' (a • {x : 𝓗 | ‖x‖ ≤ 1})) :=
      isCompact_weakImage_smul_unit_ball a
    -- The weakly closed set sits inside a weakly compact scaled unit ball, hence is weakly
    -- compact as a closed subset.
    refine IsCompact.of_isClosed_subset hcompactAmbient hclosed ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hsubset hx, rfl⟩
