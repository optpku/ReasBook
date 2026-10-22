/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Example_2_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology InnerProductSpace
open Filter

universe u

-- Proof sketch: the norm is continuous for the strong topology, so the unit sphere is the
-- preimage of the closed set `{1}` under `x ↦ ‖x‖`, hence strongly closed. For the weak statement,
-- choose an orthonormal sequence in the infinite-dimensional Hilbert space; each term lies on the
-- unit sphere and the preceding weak-convergence result shows that this sequence converges weakly
-- to `0`, which does not belong to the sphere.
/-- Helper for Example 2.32.2: every infinite-dimensional real Hilbert space contains an
orthonormal sequence indexed by `ℕ`. -/
lemma exists_orthonormal_sequence_of_not_finiteDimensional
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (h_infinite : ¬ FiniteDimensional ℝ 𝓗) :
    ∃ e : ℕ → 𝓗, Orthonormal ℝ e := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℝ 𝓗
  -- A finite Hilbert-basis index set would force finite dimensionality, contradicting the hypothesis.
  have hw_infinite : w.Infinite := by
    by_contra hw_infinite
    have hw_finite : Set.Finite w := (Set.finite_or_infinite w).resolve_right hw_infinite
    haveI : Fintype w := hw_finite.fintype
    have hfd : FiniteDimensional ℝ 𝓗 :=
      Module.Basis.finiteDimensional_of_finite (b.toOrthonormalBasis.toBasis)
    exact h_infinite hfd
  -- Extract a countable orthonormal subfamily by embedding `ℕ` into the infinite basis index set.
  let f : ℕ ↪ w := Set.Infinite.natEmbedding w hw_infinite
  refine ⟨fun n ↦ b (f n), ?_⟩
  simpa [Function.comp] using b.orthonormal.comp f f.injective

/-- Helper for Example 2.32.2: orthonormal vectors lie on the weak unit sphere. -/
private lemma orthonormal_sequence_mem_weak_unitSphere
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (e : ℕ → 𝓗) (he : Orthonormal ℝ e) :
    ∀ n, toWeakSpace ℝ 𝓗 (e n) ∈
      ((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)) := by
  intro n
  refine ⟨e n, ?_, rfl⟩
  -- Each term of an orthonormal family has norm `1`.
  simpa [Metric.mem_sphere, dist_eq_norm] using he.norm_eq_one n

/-- Helper for Example 2.32.2: the weak unit sphere excludes the origin. -/
private lemma zero_not_mem_weak_unitSphere
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗] :
    (0 : WeakSpace ℝ 𝓗) ∉
      ((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)) := by
  -- The origin has norm `0`, so it cannot lie on the norm-one sphere.
  rintro ⟨x, hx, hx0⟩
  have : x = 0 := (toWeakSpace ℝ 𝓗).injective hx0
  subst this
  simp at hx

/-- Example 2.32.2: in an infinite-dimensional real Hilbert space, the image of the unit sphere in
`WeakSpace ℝ 𝓗` is not sequentially closed. -/
theorem not_isSeqClosed_image_unitSphere_toWeakSpace
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (h_infinite : ¬ FiniteDimensional ℝ 𝓗) :
    ¬ IsSeqClosed (((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗))) := by
  -- Use an orthonormal sequence in the unit sphere converging weakly to `0`.
  intro h_seqClosed
  obtain ⟨e, he⟩ := exists_orthonormal_sequence_of_not_finiteDimensional h_infinite
  have hmem :
      ∀ n, toWeakSpace ℝ 𝓗 (e n) ∈
        ((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)) :=
    orthonormal_sequence_mem_weak_unitSphere e he
  have hweak :
      Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (e n)) atTop (𝓝 (0 : WeakSpace ℝ 𝓗)) :=
    orthonormal_sequence_tendsto_zero_weakly e he
  have hzero_mem :
      (0 : WeakSpace ℝ 𝓗) ∈
        ((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)) :=
    h_seqClosed hmem hweak
  -- Sequential closedness would force the weak limit `0` back into the sphere, contradiction.
  exact zero_not_mem_weak_unitSphere hzero_mem

/-- Example 2.32.2: in an infinite-dimensional real Hilbert space, the unit sphere is closed for
the strong topology, but its image in `WeakSpace ℝ 𝓗` is not sequentially closed. -/
theorem unitSphere_isClosed_in_strongTopology_and_not_seqClosed_in_weakTopology
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (h_infinite : ¬ FiniteDimensional ℝ 𝓗) :
    IsClosed (Metric.sphere (0 : 𝓗) 1) ∧
      ¬ IsSeqClosed (((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗))) := by
  refine ⟨?_, not_isSeqClosed_image_unitSphere_toWeakSpace h_infinite⟩
  simpa using (Metric.isClosed_sphere : IsClosed (Metric.sphere (0 : 𝓗) (1 : ℝ)))
