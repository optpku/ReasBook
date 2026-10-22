/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_5_2

open Matrix

noncomputable section

-- Semantic recall: mathlib exposes the ordered Hermitian eigenvalue API as
-- `Matrix.IsHermitian.eigenvalues : Fin n → ℝ`, reusing the matrix index type directly. Since
-- Theorem 5.5.5 is an ordered-eigenvalue statement for the representative specialization
-- `ssvmInverseUpdate R r r φ γ`, this item states its interlacing conclusions on that canonical
-- owner rather than reintroducing a duplicate local ordered-eigenvalue API.

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- Chapter05 Theorem 5.5.5 (1): if `φ ∈ Set.Icc (0 : ℝ) 1`, `0 < γ`, the SSVM
denominators `dotProduct r r` and `dotProduct r (R.mulVec r)` are valid with
`0 < dotProduct r (R.mulVec r)`, and the smallest eigenvalue of `γ • R` is at least `1`, then
the smallest eigenvalue of the self-scaling SSVM representative update is `1`, and each
remaining updated eigenvalue lies between consecutive eigenvalues of `γ • R`. -/
theorem ssvmInverseUpdate_self_eigenvalues_case_ge_one
    {R : MatrixN} (hR : R.IsHermitian) (r : Point)
    (hrr : dotProduct r r ≠ 0) (hrRr : 0 < dotProduct r (R.mulVec r)) {φ γ : ℝ}
    (hn : 0 < n) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) (hγ : 0 < γ)
    (hLast : 1 ≤ γ * hR.eigenvalues ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩) :
    let hRφ : (ssvmInverseUpdate R r r φ γ).IsHermitian :=
      ssvmInverseUpdate_self_isHermitian hR r φ γ
    hRφ.eigenvalues ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩ = 1 ∧
      ∀ i : ℕ, ∀ hi : i + 1 < n,
        1 ≤ γ * hR.eigenvalues ⟨i + 1, hi⟩ ∧
          γ * hR.eigenvalues ⟨i + 1, hi⟩ ≤ hRφ.eigenvalues ⟨i, Nat.lt_of_succ_lt hi⟩ ∧
            hRφ.eigenvalues ⟨i, Nat.lt_of_succ_lt hi⟩ ≤
              γ * hR.eigenvalues ⟨i, Nat.lt_of_succ_lt hi⟩ := sorry

/-- Chapter05 Theorem 5.5.5 (2): if `φ ∈ Set.Icc (0 : ℝ) 1`, `0 < γ`, the SSVM
denominators `dotProduct r r` and `dotProduct r (R.mulVec r)` are valid with
`0 < dotProduct r (R.mulVec r)`, and the largest eigenvalue of `γ • R` is at most `1`, then the
largest eigenvalue of the self-scaling SSVM representative update is `1`, and each remaining
updated eigenvalue lies between consecutive eigenvalues of `γ • R`. -/
theorem ssvmInverseUpdate_self_eigenvalues_case_le_one
    {R : MatrixN} (hR : R.IsHermitian) (r : Point)
    (hrr : dotProduct r r ≠ 0) (hrRr : 0 < dotProduct r (R.mulVec r)) {φ γ : ℝ}
    (hn : 0 < n) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) (hγ : 0 < γ)
    (hFirst : γ * hR.eigenvalues ⟨0, hn⟩ ≤ 1) :
    let hRφ : (ssvmInverseUpdate R r r φ γ).IsHermitian :=
      ssvmInverseUpdate_self_isHermitian hR r φ γ
    hRφ.eigenvalues ⟨0, hn⟩ = 1 ∧
      ∀ i : ℕ, ∀ hi : i + 1 < n,
        γ * hR.eigenvalues ⟨i + 1, hi⟩ ≤ hRφ.eigenvalues ⟨i + 1, hi⟩ ∧
          hRφ.eigenvalues ⟨i + 1, hi⟩ ≤ γ * hR.eigenvalues ⟨i, Nat.lt_of_succ_lt hi⟩ ∧
            γ * hR.eigenvalues ⟨i, Nat.lt_of_succ_lt hi⟩ ≤ 1 := sorry

/-- Chapter05 Theorem 5.5.5 (3): if `φ ∈ Set.Icc (0 : ℝ) 1`, `0 < γ`, the SSVM
denominators `dotProduct r r` and `dotProduct r (R.mulVec r)` are valid with
`0 < dotProduct r (R.mulVec r)`, `γ * λₙ ≤ 1 ≤ γ * λ₁`, and the zero-based crossing index `k`
(representing the textbook index `i₀ = k + 1`) satisfies
`γ * λ_(k + 2) ≤ 1 ≤ γ * λ_(k + 1)`, then the updated eigenvalues interlace with the scaled
eigenvalues on the left side of that crossing, with `μ_(k + 1)` and `μ_(k + 2)` straddling `1`,
the scaled eigenvalue tail continuing on the right down to `γ * λₙ`, and one of those two
updated eigenvalues equal to `1`. -/
theorem ssvmInverseUpdate_self_eigenvalues_case_crossing_one
    {R : MatrixN} (hR : R.IsHermitian) (r : Point)
    (hrr : dotProduct r r ≠ 0) (hrRr : 0 < dotProduct r (R.mulVec r)) {φ γ : ℝ}
    (hn : 0 < n) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) (hγ : 0 < γ)
    (hLast : γ * hR.eigenvalues ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩ ≤ 1)
    (hFirst : 1 ≤ γ * hR.eigenvalues ⟨0, hn⟩)
    (k : ℕ) (hk : k + 1 < n)
    (hCrossLower : γ * hR.eigenvalues ⟨k + 1, hk⟩ ≤ 1)
    (hCrossUpper : 1 ≤ γ * hR.eigenvalues ⟨k, Nat.lt_of_succ_lt hk⟩) :
    let hRφ : (ssvmInverseUpdate R r r φ γ).IsHermitian :=
      ssvmInverseUpdate_self_isHermitian hR r φ γ
    (∀ j : ℕ, ∀ hj : j + 1 < k + 1,
      γ * hR.eigenvalues ⟨j + 1, Nat.lt_trans hj hk⟩ ≤
          hRφ.eigenvalues ⟨j, Nat.lt_of_succ_lt (Nat.lt_trans hj hk)⟩ ∧
        hRφ.eigenvalues ⟨j, Nat.lt_of_succ_lt (Nat.lt_trans hj hk)⟩ ≤
          γ * hR.eigenvalues ⟨j, Nat.lt_of_succ_lt (Nat.lt_trans hj hk)⟩) ∧
      1 ≤ hRφ.eigenvalues ⟨k, Nat.lt_of_succ_lt hk⟩ ∧
        hRφ.eigenvalues ⟨k, Nat.lt_of_succ_lt hk⟩ ≤ γ * hR.eigenvalues ⟨k, Nat.lt_of_succ_lt hk⟩ ∧
          γ * hR.eigenvalues ⟨k + 1, hk⟩ ≤ hRφ.eigenvalues ⟨k + 1, hk⟩ ∧
            hRφ.eigenvalues ⟨k + 1, hk⟩ ≤ 1 ∧
              (∀ j : ℕ, ∀ hj_lower : k + 1 ≤ j, ∀ hj_upper : j + 1 < n,
                γ * hR.eigenvalues ⟨j + 1, hj_upper⟩ ≤ hRφ.eigenvalues ⟨j + 1, hj_upper⟩ ∧
                  hRφ.eigenvalues ⟨j + 1, hj_upper⟩ ≤
                    γ * hR.eigenvalues ⟨j, Nat.lt_of_succ_lt hj_upper⟩) ∧
                (hRφ.eigenvalues ⟨k, Nat.lt_of_succ_lt hk⟩ = 1 ∨
                  hRφ.eigenvalues ⟨k + 1, hk⟩ = 1) := sorry

end
