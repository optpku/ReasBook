/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped Matrix

section

variable {m n : ℕ}

/- Algorithm 8.8 is `source-facing`: the textbook specializes the alternating projection idea to
the feasibility problem `A x = b`, `x ≥ 0`, and writes the affine projection step in the explicit
matrix form `x - Aᵀ (A Aᵀ)⁻¹ (A x - b)`. The canonical owners already present in the project for
the two pieces of the update are the nonnegative orthant `Set.Ici (0 : Fin n → ℝ)` and the
coordinatewise positive part `x⁺`. Because the displayed recursion itself is the mathematical
content of the item, the public API records that specialized iterate sequence directly. -/

-- Proof sketch: the positive part is the pointwise supremum `x ⊔ 0`, so every coordinate of `x⁺`
-- is nonnegative and hence `x⁺` belongs to the orthant `Set.Ici 0`.
/-- The coordinatewise positive part of a real vector lies in the nonnegative orthant. -/
theorem posPart_mem_nonnegative_orthant (x : Fin n → ℝ) :
    x⁺ ∈ Set.Ici (0 : Fin n → ℝ) := by
  -- Membership in the orthant is exactly pointwise nonnegativity.
  simpa [Set.mem_Ici] using posPart_nonneg x

/-- Algorithm 8.8: given a real matrix `A` with `A Aᵀ` invertible, a right-hand side `b`, and an
initial point `x0 ∈ ℝ^n_+`, Algorithm 1 generates the sequence
`x^{k+1} = [x^k - Aᵀ (A Aᵀ)⁻¹ (A x^k - b)]_+`, where `[·]_+` is the coordinatewise positive part.
-/
def nonnegative_affine_feasibility_method
    (A : Matrix (Fin m) (Fin n) ℝ) [Invertible (A * A.transpose)] (b : Fin m → ℝ)
    (x0 : Set.Ici (0 : Fin n → ℝ)) : ℕ → Set.Ici (0 : Fin n → ℝ)
  | 0 => x0
  | k + 1 =>
      let xk := nonnegative_affine_feasibility_method A b x0 k
      ⟨((xk : Fin n → ℝ) - Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ (A *ᵥ (xk : Fin n → ℝ) - b)))⁺,
        posPart_mem_nonnegative_orthant
          ((xk : Fin n → ℝ) - Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ (A *ᵥ (xk : Fin n → ℝ) - b)))⟩

section

variable (A : Matrix (Fin m) (Fin n) ℝ) [Invertible (A * A.transpose)] (b : Fin m → ℝ)
variable (x0 : Set.Ici (0 : Fin n → ℝ))

local notation "x[" k "]" => nonnegative_affine_feasibility_method A b x0 k

-- Proof sketch: unfold the recursive definition of `nonnegative_affine_feasibility_method` at
-- `0`.
/-- The nonnegative affine-feasibility sequence starts at the prescribed initial point. -/
theorem nonnegative_affine_feasibility_method_zero :
    x[0] = x0 := by
  -- The initial iterate is the `0` branch of the recursion.
  rfl

-- Proof sketch: unfold the recursive definition of `nonnegative_affine_feasibility_method` at
-- `k + 1`; the coercion from the subtype `Set.Ici (0 : Fin n → ℝ)` to `Fin n → ℝ` reveals the
-- displayed affine-correction update followed by coordinatewise positive part.
/-- One step of the method applies coordinatewise positive part to the affine correction
`x^k - Aᵀ (A Aᵀ)⁻¹ (A x^k - b)`. -/
theorem nonnegative_affine_feasibility_method_succ (k : ℕ) :
    (x[k + 1] : Fin n → ℝ) =
      ((x[k] : Fin n → ℝ) - Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ (A *ᵥ (x[k] : Fin n → ℝ) - b)))⁺ := by
  -- Unfolding the successor branch exposes the affine correction followed by positive part.
  rfl

end

end
