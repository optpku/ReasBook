/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

section

variable {I : Type u}

/-- Helper for Example 6.25: a vector is in the dual of the `ℓ²` positive orthant exactly when all
of its coordinates are nonnegative. -/
private theorem mem_innerDual_ell2PositiveOrthant_iff (x : lp (fun _ : I ↦ ℝ) 2) :
    x ∈ (ProperCone.innerDual
      ({y : lp (fun _ : I ↦ ℝ) 2 | ∀ i, 0 ≤ y i} : Set (lp (fun _ : I ↦ ℝ) 2)) :
      Set (lp (fun _ : I ↦ ℝ) 2)) ↔ ∀ i, 0 ≤ x i := by
  classical
  constructor
  · intro hx i
    -- Test the dual inequality on the `i`-th standard basis vector of `ℓ²(I, ℝ)`.
    have hvec : lp.single 2 i (1 : ℝ) ∈
        ({y : lp (fun _ : I ↦ ℝ) 2 | ∀ i, 0 ≤ y i} : Set (lp (fun _ : I ↦ ℝ) 2)) := by
      intro j
      by_cases h : j = i
      · subst h
        simp
      · simp [h]
    have hinner : 0 ≤ ⟪lp.single 2 i (1 : ℝ), x⟫_ℝ := (ProperCone.mem_innerDual.mp hx) hvec
    have hsingle : ⟪lp.single 2 i (1 : ℝ), x⟫_ℝ = ⟪(1 : ℝ), x i⟫_ℝ :=
      lp.inner_single_left (𝕜 := ℝ) i (1 : ℝ) x
    rw [hsingle] at hinner
    change 0 ≤ x i * 1 at hinner
    simpa using hinner
  · intro hx
    -- Expand the inner product as a sum of nonnegative coordinate products.
    exact ProperCone.mem_innerDual.mpr <| by
      intro y hy
      rw [lp.inner_eq_tsum]
      exact tsum_nonneg fun i ↦ by
        simpa [RCLike.inner_apply, mul_comm] using mul_nonneg (hy i) (hx i)

-- Route correction: the Chapter 6 dependency file packages the orthant on `PiLp`, while the
-- target statement here is written in mathlib's `lp` model of `ℓ²`; the proof therefore works
-- directly in `lp` by reading coordinates with `lp.single` and summing nonnegative terms.
/-- Example 6.25: the coordinatewise nonnegative cone `ℓ²₊(I)` in `ℓ²(I, ℝ)` is self-dual. -/
theorem ell2PositiveOrthant_isSelfDual :
    ({x : lp (fun _ : I ↦ ℝ) 2 | ∀ i, 0 ≤ x i} :
      Set (lp (fun _ : I ↦ ℝ) 2)).IsSelfDual := by
  rw [Set.isSelfDual_iff, Set.dualCone_eq_innerDual]
  ext x
  have hiff := mem_innerDual_ell2PositiveOrthant_iff (x := x)
  constructor
  · intro hx
    exact hiff.mpr hx
  · intro hx
    exact hiff.mp hx

/-- Helper for Example 6.25: a Euclidean vector is in the dual of the positive orthant exactly when
all of its coordinates are nonnegative. -/
private theorem mem_innerDual_euclideanPositiveOrthant_iff {N : ℕ}
    (x : EuclideanSpace ℝ (Fin N)) :
    x ∈ (ProperCone.innerDual ({y : EuclideanSpace ℝ (Fin N) | ∀ i, 0 ≤ y i} :
      Set (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N))) ↔
      ∀ i, 0 ≤ x i := by
  constructor
  · intro hx i
    -- Test the dual inequality on the `i`-th Euclidean basis vector.
    have hbasis : EuclideanSpace.basisFun (Fin N) ℝ i ∈
        ({y : EuclideanSpace ℝ (Fin N) | ∀ j, 0 ≤ y j} : Set (EuclideanSpace ℝ (Fin N))) := by
      intro j
      by_cases h : j = i
      · subst h
        simp [EuclideanSpace.basisFun_apply]
      · simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single, h]
    calc
      0 ≤ ⟪EuclideanSpace.basisFun (Fin N) ℝ i, x⟫_ℝ :=
        (ProperCone.mem_innerDual.mp hx) hbasis
      _ = x i := EuclideanSpace.basisFun_inner (ι := Fin N) (𝕜 := ℝ) x i
  · intro hx
    -- Expand the Euclidean inner product as a finite sum of nonnegative coordinate products.
    exact ProperCone.mem_innerDual.mpr <| by
      intro y hy
      rw [PiLp.inner_apply]
      have hsum : 0 ≤ ∑ i, y i * x i := by
        exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hy i) (hx i)
      simpa [RCLike.inner_apply, mul_comm] using hsum

/-- In the canonical model `ℝ^N = EuclideanSpace ℝ (Fin N)`, the positive orthant is self-dual. -/
theorem euclideanPositiveOrthant_isSelfDual (N : ℕ) :
    ({x : EuclideanSpace ℝ (Fin N) | ∀ i, 0 ≤ x i} : Set (EuclideanSpace ℝ (Fin N))).IsSelfDual :=
  by
  rw [Set.isSelfDual_iff, Set.dualCone_eq_innerDual]
  ext x
  have hiff := mem_innerDual_euclideanPositiveOrthant_iff (x := x)
  constructor
  · intro hx
    exact hiff.mpr hx
  · intro hx
    exact hiff.mp hx

end
