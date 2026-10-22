/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.FirmlyNonexpansiveOn

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap
open scoped InnerProductSpace

universe u v

section

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Rewrite the compressed inner product on `H` as the corresponding inner product on `K`.
private lemma inner_sub_adjoint_apply_eq (L : H →L[ℝ] K) (x y : H) (z : K) :
    inner ℝ (x - y) (L.adjoint z) = inner ℝ (L x - L y) z := by
  rw [adjoint_inner_right, map_sub]

-- If `‖L‖ ≤ 1`, then applying `L.adjoint` preserves the squared contraction bound.
private lemma norm_sq_adjoint_apply_le_of_norm_le_one
    (L : H →L[ℝ] K) (hL : ‖L‖ ≤ 1) (z : K) :
    ‖L.adjoint z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  have hNorm : ‖L.adjoint z‖ ≤ ‖z‖ := by
    calc
      ‖L.adjoint z‖ ≤ ‖L.adjoint‖ * ‖z‖ := le_opNorm _ _
      _ = ‖L‖ * ‖z‖ := by simp [adjoint.norm_map]
      _ ≤ 1 * ‖z‖ := by gcongr
      _ = ‖z‖ := by ring
  nlinarith [hNorm, norm_nonneg (L.adjoint z), norm_nonneg z]

-- Proof sketch: apply the Hilbert-space firm nonexpansiveness inequality for `T` to `L x` and
-- `L y`, rewrite the resulting inner product using the adjoint identity for `L`, and use
-- `‖L.adjoint z‖ ≤ ‖L‖ * ‖z‖ ≤ ‖z‖` from `‖L‖ ≤ 1`.
/-- Corollary 4.13: if `T` is firmly nonexpansive on the real Hilbert space `K` in the standard
inner-product form and `L : H →L[ℝ] K` has operator norm at most `1`, then the compressed map
`L.adjoint ∘ T ∘ L` is firmly nonexpansive on `H`. -/
theorem adjoint_comp_firmlyNonexpansive_of_norm_le_one
    (T : K → K)
    (hT : FirmlyNonexpansiveOn (Set.univ : Set K) (fun x : Set.univ ↦ T x))
    (L : H →L[ℝ] K) (hL : ‖L‖ ≤ 1) :
    FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ (L.adjoint ∘ T ∘ L) x) := by
  intro x y
  set z : K := T (L x) - T (L y)
  have hTxy : ‖z‖ ^ 2 ≤ ⟪z, L x - L y⟫_ℝ := by
    have hT' : ‖T (L x) - T (L y)‖ ^ 2 ≤ ⟪T (L x) - T (L y), L x - L y⟫_ℝ :=
      by
        simpa [real_inner_comm] using hT ⟨L x, by simp⟩ ⟨L y, by simp⟩
    simpa [z, map_sub] using hT'
  calc
    ‖(L.adjoint ∘ T ∘ L) x - (L.adjoint ∘ T ∘ L) y‖ ^ 2 = ‖L.adjoint z‖ ^ 2 := by
      simp [Function.comp, z, map_sub]
    _ ≤ ‖z‖ ^ 2 := norm_sq_adjoint_apply_le_of_norm_le_one L hL z
    _ ≤ ⟪z, L x - L y⟫_ℝ := hTxy
    _ = ⟪L x - L y, z⟫_ℝ := by rw [real_inner_comm]
    _ = ⟪(x : H) - y, L.adjoint z⟫_ℝ := by
      symm
      exact inner_sub_adjoint_apply_eq L (x : H) (y : H) z
    _ = ⟪(x : H) - y, (L.adjoint ∘ T ∘ L) x - (L.adjoint ∘ T ∘ L) y⟫_ℝ := by
      simp [Function.comp, z, map_sub]

end
