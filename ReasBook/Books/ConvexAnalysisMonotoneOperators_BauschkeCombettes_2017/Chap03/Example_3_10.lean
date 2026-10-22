/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped InnerProductSpace

variable {I : Type v} [Fintype I] [DecidableEq I]
variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

omit [DecidableEq I] [CompleteSpace 𝓗] in
private lemma orthogonal_coordinate_sum_mem_span (e : I → 𝓗) (x : 𝓗) :
    (∑ i : I, ⟪x, e i⟫_ℝ • e i) ∈ Submodule.span ℝ (Set.range e) := by
  -- Each summand is a scalar multiple of a generator of the span.
  simpa using
    (Submodule.sum_mem (Submodule.span ℝ (Set.range e)) fun i _ ↦
      Submodule.smul_mem (Submodule.span ℝ (Set.range e)) _ <|
        Submodule.subset_span ⟨i, rfl⟩)

omit [DecidableEq I] [CompleteSpace 𝓗] in
private lemma orthonormal_span_error_sq_decomposition
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) (α : I → ℝ) :
    ‖x - ∑ i : I, α i • e i‖ ^ 2 =
      ‖x‖ ^ 2 - ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2 + ∑ i : I, |α i - ⟪x, e i⟫_ℝ| ^ 2 := by
  -- Expand the squared norm and evaluate the mixed and quadratic terms in orthonormal
  -- coordinates.
  rw [norm_sub_sq_real]
  have h_inner : ⟪x, ∑ i : I, α i • e i⟫_ℝ = ∑ i : I, α i * ⟪x, e i⟫_ℝ := by
    simp [inner_sum, inner_smul_right]
  have h_norm : ‖∑ i : I, α i • e i‖ ^ 2 = ∑ i : I, |α i| ^ 2 := by
    calc
      ‖∑ i : I, α i • e i‖ ^ 2 = ⟪∑ i : I, α i • e i, ∑ i : I, α i • e i⟫_ℝ := by
        rw [real_inner_self_eq_norm_sq]
      _ = ∑ i : I, α i * α i := by
        simpa using he.inner_sum α α Finset.univ
      _ = ∑ i : I, |α i| ^ 2 := by
        simp [sq]
  rw [h_inner, h_norm]
  have h_expand :
      ∑ i : I, |α i - ⟪x, e i⟫_ℝ| ^ 2 =
        ∑ i : I, |α i| ^ 2 - 2 * ∑ i : I, α i * ⟪x, e i⟫_ℝ +
          ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2 := by
    -- Complete the square pointwise and then sum the resulting identity.
    have h_pointwise :
        ∀ i : I,
          |α i - ⟪x, e i⟫_ℝ| ^ 2 =
            |α i| ^ 2 - (2 * (α i * ⟪x, e i⟫_ℝ)) + |⟪x, e i⟫_ℝ| ^ 2 := by
      intro i
      rw [sq_abs, sq_abs, sq_abs, sub_sq]
      ring
    calc
      ∑ i : I, |α i - ⟪x, e i⟫_ℝ| ^ 2 =
          ∑ i : I, (|α i| ^ 2 - (2 * (α i * ⟪x, e i⟫_ℝ)) + |⟪x, e i⟫_ℝ| ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact h_pointwise i
      _ = ∑ i : I, |α i| ^ 2 - ∑ i : I, 2 * (α i * ⟪x, e i⟫_ℝ) +
            ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = ∑ i : I, |α i| ^ 2 - 2 * ∑ i : I, α i * ⟪x, e i⟫_ℝ +
            ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2 := by
        rw [← Finset.mul_sum]
  linarith

omit [DecidableEq I] [CompleteSpace 𝓗] in
private lemma orthonormal_span_error_sq_min_le
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    ∀ β : I → ℝ,
      ‖x - ∑ i : I, ⟪x, e i⟫_ℝ • e i‖ ^ 2 ≤ ‖x - ∑ i : I, β i • e i‖ ^ 2 := by
  intro β
  -- The completed-square identity leaves only a sum of squares on the right-hand side.
  rw [orthonormal_span_error_sq_decomposition e he x (fun i ↦ ⟪x, e i⟫_ℝ),
    orthonormal_span_error_sq_decomposition e he x β]
  have hnonneg : 0 ≤ ∑ i : I, |β i - ⟪x, e i⟫_ℝ| ^ 2 := by
    exact Finset.sum_nonneg fun i hi ↦ sq_nonneg _
  simp at *
  linarith

omit [DecidableEq I] [CompleteSpace 𝓗] in
private lemma orthonormal_span_coefficients_eq_of_error_sq_eq_min
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    ∀ β : I → ℝ,
      ‖x - ∑ i : I, β i • e i‖ ^ 2 = ‖x - ∑ i : I, ⟪x, e i⟫_ℝ • e i‖ ^ 2 →
        β = fun i ↦ ⟪x, e i⟫_ℝ := by
  intro β hβ
  -- Equality of the total errors forces the nonnegative sum of squares to vanish termwise.
  have hdecompβ := orthonormal_span_error_sq_decomposition e he x β
  have hdecomp0 := orthonormal_span_error_sq_decomposition e he x (fun i ↦ ⟪x, e i⟫_ℝ)
  rw [hβ] at hdecompβ
  rw [hdecomp0] at hdecompβ
  have hsum : ∑ i : I, |β i - ⟪x, e i⟫_ℝ| ^ 2 = 0 := by
    simpa using hdecompβ
  have hzero : ∀ i : I, |β i - ⟪x, e i⟫_ℝ| ^ 2 = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j hj ↦ sq_nonneg _)).1 hsum i (Finset.mem_univ i)
  funext i
  have hi : β i - ⟪x, e i⟫_ℝ = 0 := by
    apply abs_eq_zero.mp
    exact sq_eq_zero_iff.mp (hzero i)
  linarith

omit [DecidableEq I] [CompleteSpace 𝓗] in
private lemma finite_orthonormal_span_sum_inner_mem_span_and_sub_mem_orthogonal
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    (∑ i : I, ⟪x, e i⟫_ℝ • e i) ∈ Submodule.span ℝ (Set.range e) ∧
      x - ∑ i : I, ⟪x, e i⟫_ℝ • e i ∈
        (Submodule.span ℝ (Set.range e) : Submodule ℝ 𝓗)ᗮ := by
  let V : Submodule ℝ 𝓗 := Submodule.span ℝ (Set.range e)
  let p0 : 𝓗 := ∑ i : I, ⟪x, e i⟫_ℝ • e i
  have hp0 : p0 ∈ V := by
    simpa [V, p0] using orthogonal_coordinate_sum_mem_span e x
  letI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range e)
  letI : CompleteSpace V := by infer_instance
  have hp0proj : V.starProjection x = p0 := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hp0
    intro y hy
    rcases (Submodule.mem_span_range_iff_exists_fun ℝ).mp hy with ⟨β, rfl⟩
    rw [inner_sub_left, inner_sum]
    simp [p0, inner_sum, inner_smul_right, he.inner_left_fintype]
  refine ⟨by simpa [V, p0] using hp0, ?_⟩
  simpa [V, p0, hp0proj] using V.sub_starProjection_mem_orthogonal x

omit [DecidableEq I] [CompleteSpace 𝓗] in
private lemma orthonormal_span_sum_inner_isBestApproximation
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    IsBestApproximation x (((Submodule.span ℝ (Set.range e) : Submodule ℝ 𝓗) : Set 𝓗))
      (∑ i : I, ⟪x, e i⟫_ℝ • e i) := by
  let V : Submodule ℝ 𝓗 := Submodule.span ℝ (Set.range e)
  let p0 : 𝓗 := ∑ i : I, ⟪x, e i⟫_ℝ • e i
  have hmain := finite_orthonormal_span_sum_inner_mem_span_and_sub_mem_orthogonal e he x
  have hp0 : p0 ∈ V := by
    simpa [V, p0] using hmain.1
  letI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range e)
  letI : CompleteSpace V := by infer_instance
  have hp0_dist :
      dist x p0 = Metric.infDist x (V : Set 𝓗) := by
    have hp0proj : V.starProjection x = p0 := by
      apply Submodule.eq_starProjection_of_mem_orthogonal hp0
      simpa [V, p0] using hmain.2
    simpa [Metric.infDist_eq_iInf, dist_eq_norm, hp0proj] using V.starProjection_minimal x
  exact ⟨by simpa [V, p0] using hp0, by simpa [V] using hp0_dist⟩

-- Proof sketch: a finite-dimensional subspace of a Hilbert space is nonempty, closed, and convex,
-- so Theorem 3.16.1 applies directly.
omit [DecidableEq I] in
/-- The span of a finite family in a real Hilbert space is a Chebyshev set. -/
theorem finite_span_range_isChebyshev
    (e : I → 𝓗) :
    IsChebyshev (((Submodule.span ℝ (Set.range e) : Submodule ℝ 𝓗) : Set 𝓗)) := by
  let V : Submodule ℝ 𝓗 := Submodule.span ℝ (Set.range e)
  letI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range e)
  exact isChebyshev_of_nonempty_isClosed_convex
    ⟨0, by simp⟩
    (Submodule.closed_of_finiteDimensional V)
    V.convex

-- Proof sketch: identify the explicit orthogonal-coordinate sum as a best approximation and then
-- use uniqueness in the Chebyshev span.
omit [DecidableEq I] in
/-- Example 3.10: the projection onto the span of a finite orthonormal family is the orthogonal
coordinate sum. -/
theorem projectionPoint_finite_orthonormal_span_eq_sum_inner
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    projectionPoint (((Submodule.span ℝ (Set.range e) : Submodule ℝ 𝓗) : Set 𝓗))
      (finite_span_range_isChebyshev e) x =
      ∑ i : I, ⟪x, e i⟫_ℝ • e i := by
  exact ((finite_span_range_isChebyshev e) x).unique
    (projectionPoint_isBestApproximation
      (((Submodule.span ℝ (Set.range e) : Submodule ℝ 𝓗) : Set 𝓗))
      (finite_span_range_isChebyshev e) x)
    (orthonormal_span_sum_inner_isBestApproximation e he x)

omit [DecidableEq I] [CompleteSpace 𝓗] in
/-- The orthogonal-coordinate sum `∑ i, ⟪x, e i⟫_ℝ • e i` is a best approximation to `x` from the
span of a finite orthonormal family. -/
theorem finite_orthonormal_span_sum_inner_isBestApproximation
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    IsBestApproximation x (((Submodule.span ℝ (Set.range e) : Submodule ℝ 𝓗) : Set 𝓗))
      (∑ i : I, ⟪x, e i⟫_ℝ • e i) := by
  exact orthonormal_span_sum_inner_isBestApproximation e he x

-- Proof sketch: combine the best-approximation equality for the orthogonal-coordinate sum with the
-- Pythagorean identity for `x` decomposed into that sum and its orthogonal remainder.
omit [DecidableEq I] [CompleteSpace 𝓗] in
/-- The distance from `x` to the span of a finite orthonormal family is the square root of the
Pythagorean remainder. -/
theorem finite_orthonormal_span_infDist_eq_sqrt_sub_sum_inner_sq
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    Metric.infDist x (((Submodule.span ℝ (Set.range e) : Submodule ℝ 𝓗) : Set 𝓗)) =
      Real.sqrt (‖x‖ ^ 2 - ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2) := by
  let V : Set 𝓗 := (((Submodule.span ℝ (Set.range e) : Submodule ℝ 𝓗) : Set 𝓗))
  let p0 : 𝓗 := ∑ i : I, ⟪x, e i⟫_ℝ • e i
  have hp0dist : dist x p0 = Metric.infDist x V := by
    simpa [V, p0] using (finite_orthonormal_span_sum_inner_isBestApproximation e he x).2
  -- Specializing the decomposition to the orthogonal coordinates removes the final error term.
  have hsq : dist x p0 ^ 2 = ‖x‖ ^ 2 - ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2 := by
    have hbase := orthonormal_span_error_sq_decomposition e he x (fun i ↦ ⟪x, e i⟫_ℝ)
    simpa [p0, dist_eq_norm] using hbase
  have hinf_sq : Metric.infDist x V ^ 2 = ‖x‖ ^ 2 - ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2 := by
    rw [← hp0dist]
    exact hsq
  have hinf_nonneg : 0 ≤ Metric.infDist x V := Metric.infDist_nonneg
  calc
    Metric.infDist x V = Real.sqrt ((Metric.infDist x V) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hinf_nonneg]
    _ = Real.sqrt (‖x‖ ^ 2 - ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2) := by
      rw [hinf_sq]

-- Proof sketch: expand `‖x - ∑ i, α i • e i‖ ^ 2` using the real inner product, evaluate the
-- mixed terms by orthonormality with `Orthonormal.inner_right_fintype`, and collect the resulting
-- squares to obtain the stated identity.
omit [DecidableEq I] [CompleteSpace 𝓗] in
/-- The squared norm of the error from an arbitrary linear combination splits into the orthogonal
projection remainder and the coefficient error term. -/
theorem finite_orthonormal_span_norm_sub_sum_smul_sq
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) (α : I → ℝ) :
    ‖x - ∑ i : I, α i • e i‖ ^ 2 =
      ‖x‖ ^ 2 - ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2 + ∑ i : I, |α i - ⟪x, e i⟫_ℝ| ^ 2 := by
  -- This is exactly the completed-square helper established above.
  exact orthonormal_span_error_sq_decomposition e he x α

-- Proof sketch: apply `finite_orthonormal_span_norm_sub_sum_smul_sq` to `β`; the last summand is
-- a sum of squares and is therefore nonnegative, so the value at the coefficient family
-- `i ↦ ⟪x, e i⟫_ℝ` is minimal.
omit [DecidableEq I] [CompleteSpace 𝓗] in
/-- The orthogonal-coordinate family minimizes the squared distance to the span. -/
theorem finite_orthonormal_span_sum_inner_smul_sq_le
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    ∀ β : I → ℝ,
      ‖x - ∑ i : I, ⟪x, e i⟫_ℝ • e i‖ ^ 2 ≤ ‖x - ∑ i : I, β i • e i‖ ^ 2 := by
  -- The coefficient error is a nonnegative sum of squares.
  exact orthonormal_span_error_sq_min_le e he x

-- Proof sketch: use `finite_orthonormal_span_norm_sub_sum_smul_sq` for `β`; if the squared error
-- attains the minimum value, the final sum of squares must vanish, hence every coordinate satisfies
-- `β i = ⟪x, e i⟫_ℝ`.
omit [DecidableEq I] [CompleteSpace 𝓗] in
/-- Equality of the minimal squared error forces the coefficient family to be the orthogonal
coordinates of `x`. -/
theorem finite_orthonormal_span_eq_inner_of_sq_eq_minimum
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    ∀ β : I → ℝ,
      ‖x - ∑ i : I, β i • e i‖ ^ 2 = ‖x - ∑ i : I, ⟪x, e i⟫_ℝ • e i‖ ^ 2 →
        β = fun i ↦ ⟪x, e i⟫_ℝ := by
  -- Equality in the minimizing identity determines every coefficient.
  exact orthonormal_span_coefficients_eq_of_error_sq_eq_min e he x
