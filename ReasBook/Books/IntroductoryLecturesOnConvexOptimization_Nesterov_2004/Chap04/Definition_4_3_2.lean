/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

variable {n k : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem fk_prefix_len_le (hk : 0 < k) (hkn : k ≤ n) : (k - 1) + 1 ≤ n := by
  omega

private def fkPrefixEmb (hk : 0 < k) (hkn : k ≤ n) : Fin ((k - 1) + 1) ↪ Fin n :=
  Fin.castLEEmb (fk_prefix_len_le hk hkn)

private def fkTailEmb : Fin (n - k) ↪ Fin n :=
  Fin.natAdd_castLEEmb (Nat.sub_le n k)

private def fkPrefixCoords (hk : 0 < k) (hkn : k ≤ n) (x : E) : Fin ((k - 1) + 1) → ℝ :=
  x ∘ fkPrefixEmb hk hkn

private def fkTailCoords (x : E) : Fin (n - k) → ℝ :=
  x ∘ fkTailEmb

/-- Definition 4.3.2: for `k ≤ n`, `fk hkn` extends the textbook hard-instance objective
`f_k : ℝ^n → ℝ`; when `0 < k`, it is given by the cubic sum of adjacent-coordinate differences
over the first `k - 1` coordinates, the cubic tail sum from coordinate `k` onward, and the linear
term `-x^{(1)}`, while the degenerate case `k = 0` keeps only the cubic tail term so the owner is
defined for all `k ≤ n`. -/
def fk (hkn : k ≤ n) : E → ℝ :=
  fun x ↦
    if hk : 0 < k then
      (1 / 3 : ℝ) *
          ((∑ i : Fin (k - 1),
              |fkPrefixCoords hk hkn x (Fin.castSucc i) - fkPrefixCoords hk hkn x i.succ| ^
                  (3 : ℕ)) +
            |fkPrefixCoords hk hkn x (Fin.last (k - 1))| ^ (3 : ℕ)) -
        fkPrefixCoords hk hkn x 0 +
        (1 / 3 : ℝ) * ∑ i : Fin (n - k), |fkTailCoords x i| ^ (3 : ℕ)
    else
      (1 / 3 : ℝ) * ∑ i : Fin n, |x i| ^ (3 : ℕ)

/-- Expanding `fk` recovers the textbook coordinate formula for the hard-instance objective
`f_k`. -/
@[simp]
theorem fk_apply (hkn : k ≤ n) (x : E) :
    fk hkn x =
      if hk : 0 < k then
        (1 / 3 : ℝ) *
            ((∑ i : Fin (k - 1),
                |x (Fin.castLE (fk_prefix_len_le hk hkn) (Fin.castSucc i)) -
                    x (Fin.castLE (fk_prefix_len_le hk hkn) i.succ)| ^ (3 : ℕ)) +
              |x (Fin.castLE (fk_prefix_len_le hk hkn) (Fin.last (k - 1)))| ^ (3 : ℕ)) -
          x (Fin.castLE (fk_prefix_len_le hk hkn) 0) +
          (1 / 3 : ℝ) *
            ∑ i : Fin (n - k),
              |x (Fin.natAdd_castLEEmb (Nat.sub_le n k) i)| ^ (3 : ℕ)
      else
        (1 / 3 : ℝ) * ∑ i : Fin n, |x i| ^ (3 : ℕ) := by
  by_cases hk : 0 < k
  · simp [fk, hk, fkPrefixCoords, fkPrefixEmb, fkTailCoords, fkTailEmb]
  · simp [fk, hk]

end
