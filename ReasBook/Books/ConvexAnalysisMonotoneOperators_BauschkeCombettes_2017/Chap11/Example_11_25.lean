/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_48
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_42
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

namespace ERealFunction

/-- The source-facing function from Example 11.25. The `source-facing` owner is this two-variable
relative-entropy formula, while the `core/canonical` primitive data is the Chapter 9 closed
perspective of `closed_relative_entropy_generator`; the only `bridge/view` layer is the coordinate
swap `(ξ₁, ξ₂) ↦ (ξ₂, ξ₁)` together with the affine correction `ξ₂ - ξ₁`. -/
noncomputable def closedScalarRelativeEntropy : ℝ × ℝ → Set.Ioi (⊥ : EReal) :=
  fun p ↦
    let hdom := closed_relative_entropy_generator_mem_gammaZero.2.nonempty
    ⟨(closedPerspective closed_relative_entropy_generator hdom (p.2, p.1) : EReal) +
        (p.2 - p.1 : ℝ),
      bot_lt_iff_ne_bot.mpr <|
        (EReal.add_ne_bot_iff).2
          ⟨(closedPerspective closed_relative_entropy_generator hdom (p.2, p.1)).2.ne',
            EReal.coe_ne_bot _⟩⟩

/-- The source-facing scalar relative entropy is the Chapter 9 closed perspective of the closed
relative-entropy generator, viewed on swapped coordinates and corrected by the affine term
`ξ₂ - ξ₁`. -/
@[simp] theorem closedScalarRelativeEntropy_coe (p : ℝ × ℝ) :
    (closedScalarRelativeEntropy p : EReal) =
      (closedPerspective closed_relative_entropy_generator
        closed_relative_entropy_generator_mem_gammaZero.2.nonempty (p.2, p.1) : EReal) +
        (p.2 - p.1 : ℝ) := by
  simp [closedScalarRelativeEntropy]

local notation "f" => closedScalarRelativeEntropy.asEReal

/- Example 11.25: evaluating `closedScalarRelativeEntropy` gives the three-branch textbook formula:
the logarithmic expression on the positive orthant, the vertical branch `{0} × ℝ₊`, and `+∞`
otherwise. -/
@[simp] theorem closedScalarRelativeEntropy_apply (ξ₁ ξ₂ : ℝ) :
    (closedScalarRelativeEntropy (ξ₁, ξ₂) : EReal) =
      if 0 < ξ₁ ∧ 0 < ξ₂ then
        ((ξ₁ * Real.log (ξ₁ / ξ₂) - ξ₁ + ξ₂ : ℝ) : EReal)
      else if ξ₁ = 0 ∧ 0 ≤ ξ₂ then
        ξ₂
      else
        ⊤ := by
  sorry

/- On the strictly positive orthant, `closedScalarRelativeEntropy` is
`ξ₁ log (ξ₁ / ξ₂) - ξ₁ + ξ₂`. -/
-- Proof sketch: this is the positive branch of `closedScalarRelativeEntropy_apply`.
theorem closedScalarRelativeEntropy_apply_of_pos {ξ₁ ξ₂ : ℝ} (hξ₁ : 0 < ξ₁) (hξ₂ : 0 < ξ₂) :
    (closedScalarRelativeEntropy (ξ₁, ξ₂) : EReal) =
      ((ξ₁ * Real.log (ξ₁ / ξ₂) - ξ₁ + ξ₂ : ℝ) : EReal) := by
  rw [closedScalarRelativeEntropy_apply, if_pos ⟨hξ₁, hξ₂⟩]

/- On the vertical half-line `{0} × ℝ₊`, `closedScalarRelativeEntropy` is the second coordinate. -/
-- Proof sketch: this is the second branch of `closedScalarRelativeEntropy_apply`.
theorem closedScalarRelativeEntropy_apply_zero_left {ξ₂ : ℝ} (hξ₂ : 0 ≤ ξ₂) :
    (closedScalarRelativeEntropy (0, ξ₂) : EReal) = ξ₂ := by
  rw [closedScalarRelativeEntropy_apply, if_neg (by simp), if_pos ⟨rfl, hξ₂⟩]

/- Away from the positive orthant and the branch `{0} × ℝ₊`, `closedScalarRelativeEntropy` is
`+∞`. -/
-- Proof sketch: this is the final branch of `closedScalarRelativeEntropy_apply`.
theorem closedScalarRelativeEntropy_apply_of_otherwise {ξ₁ ξ₂ : ℝ}
    (hpos : ¬ (0 < ξ₁ ∧ 0 < ξ₂)) (hzero : ¬ (ξ₁ = 0 ∧ 0 ≤ ξ₂)) :
    (closedScalarRelativeEntropy (ξ₁, ξ₂) : EReal) = ⊤ := by
  rw [closedScalarRelativeEntropy_apply, if_neg hpos, if_neg hzero]

/- The source-facing scalar relative entropy belongs to `Γ₀(ℝ × ℝ)`. -/
-- Proof sketch: realize the textbook piecewise formula as the closed perspective of the
-- Chapter 9 closed relative-entropy generator, then add the affine correction `ξ₂ - ξ₁`.
theorem closedScalarRelativeEntropy_mem_gammaZero :
    closedScalarRelativeEntropy ∈ Γ₀(ℝ × ℝ) := sorry

/- The infimum of `closedScalarRelativeEntropy` is `0`. -/
-- Proof sketch: evaluate the function at `(0, 0)` using the zero-left branch, and show every value
-- is bounded below by `0` through the nonnegativity of `InformationTheory.klFun`.
theorem closedScalarRelativeEntropy_sInf_eq_zero :
    sInf (Set.range f) = 0 := sorry

/- The minimizers of `closedScalarRelativeEntropy` form the nonnegative diagonal ray. -/
-- Proof sketch: rewrite the positive-height branch as `ξ₂ * klFun (ξ₁ / ξ₂)` and use that
-- `InformationTheory.klFun` attains its minimum `0` exactly at `1`; the zero slice contributes
-- only the origin.
theorem closedScalarRelativeEntropy_argmin_eq :
    Argmin f =
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.2 = p.1} := sorry

/-- The sequence `xₙ = (εₙ, εₙ)` from Example 11.25. -/
def example11_25xSequence (ε : ℕ → ℝ) : ℕ → ℝ × ℝ :=
  fun n ↦ (ε n, ε n)

/-- The sequence `yₙ = (εₙ, exp (-1 / εₙ))` from Example 11.25. -/
noncomputable def example11_25ySequence (ε : ℕ → ℝ) : ℕ → ℝ × ℝ :=
  fun n ↦ (ε n, Real.exp (-(1 / ε n)))

/-- The sequence `zₙ = (εₙ, exp (-1 / εₙ²))` from Example 11.25. -/
noncomputable def example11_25zSequence (ε : ℕ → ℝ) : ℕ → ℝ × ℝ :=
  fun n ↦ (ε n, Real.exp (-(1 / (ε n) ^ 2)))

/-- The diagonal sequence `xₙ` converges to the origin when `εₙ → 0`. -/
-- Proof sketch: both coordinates of `xₙ` are exactly `εₙ`, so product convergence follows from
-- the assumed scalar convergence.
theorem example11_25xSequence_tendsto_zero {ε : ℕ → ℝ}
    (hε_tendsto : Tendsto ε atTop (nhds 0)) :
    Tendsto (example11_25xSequence ε) atTop (nhds (0 : ℝ × ℝ)) := sorry

/-- The exponentially perturbed sequence `yₙ` converges to the origin when `εₙ > 0` and
`εₙ → 0`. -/
-- Proof sketch: the first coordinate is `εₙ → 0`, while the second coordinate is
-- `exp (-(1 / εₙ))`, which tends to `0` because `1 / εₙ → +∞`.
theorem example11_25ySequence_tendsto_zero {ε : ℕ → ℝ} (hε_pos : ∀ n, 0 < ε n)
    (hε_tendsto : Tendsto ε atTop (nhds 0)) :
    Tendsto (example11_25ySequence ε) atTop (nhds (0 : ℝ × ℝ)) := sorry

/-- The faster-decaying sequence `zₙ` also converges to the origin when `εₙ > 0` and
`εₙ → 0`. -/
-- Proof sketch: the first coordinate is again `εₙ → 0`, and the second coordinate is
-- `exp (-(1 / εₙ²))`, which tends to `0` because `1 / εₙ² → +∞`.
theorem example11_25zSequence_tendsto_zero {ε : ℕ → ℝ} (hε_pos : ∀ n, 0 < ε n)
    (hε_tendsto : Tendsto ε atTop (nhds 0)) :
    Tendsto (example11_25zSequence ε) atTop (nhds (0 : ℝ × ℝ)) := sorry

/- Along the diagonal sequence `xₙ`, `closedScalarRelativeEntropy` is constantly `0`. -/
-- Proof sketch: if `εₙ > 0`, evaluate the positive branch at `ξ₁ = ξ₂ = εₙ`; if `εₙ = 0`, use
-- the zero-left branch. Nonnegativity is the exact hypothesis needed to stay on the diagonal
-- minimizer ray.
theorem closedScalarRelativeEntropy_value_xSequence {ε : ℕ → ℝ}
    (hε_nonneg : ∀ n, 0 ≤ ε n) (n : ℕ) :
    (closedScalarRelativeEntropy (example11_25xSequence ε n) : EReal) = 0 := sorry

/- Along the diagonal sequence `xₙ`, the `closedScalarRelativeEntropy` values converge to `0`. -/
-- Proof sketch: the previous theorem shows that the sequence of values is constantly `0`.
theorem closedScalarRelativeEntropy_value_xSequence_tendsto_zero {ε : ℕ → ℝ}
    (hε_nonneg : ∀ n, 0 ≤ ε n) :
    Tendsto (fun n ↦ (closedScalarRelativeEntropy (example11_25xSequence ε n) : EReal))
      atTop (nhds (0 : EReal)) := by
  have hconst :
      (fun n ↦ (closedScalarRelativeEntropy (example11_25xSequence ε n) : EReal)) =
        fun _ : ℕ ↦ (0 : EReal) := by
    funext n
    exact closedScalarRelativeEntropy_value_xSequence hε_nonneg n
  rw [hconst]
  simp

/- Along the sequence `yₙ`, the `closedScalarRelativeEntropy` values converge to `1`. -/
-- Proof sketch: evaluate the positive branch at
-- `(εₙ, exp (-(1 / εₙ)))`, simplify the logarithm to obtain `1 - εₙ + exp (-(1 / εₙ))`, and
-- pass to the limit using `εₙ → 0`.
theorem closedScalarRelativeEntropy_value_ySequence_tendsto_one {ε : ℕ → ℝ}
    (hε_pos : ∀ n, 0 < ε n)
    (hε_tendsto : Tendsto ε atTop (nhds 0)) :
    Tendsto (fun n ↦ (closedScalarRelativeEntropy (example11_25ySequence ε n) : EReal))
      atTop (nhds (1 : EReal)) := sorry

/- Along the sequence `zₙ`, the `closedScalarRelativeEntropy` values diverge to `+∞`. -/
-- Proof sketch: evaluate the positive branch at
-- `(εₙ, exp (-(1 / εₙ²)))`, simplify to `1 / εₙ - εₙ + exp (-(1 / εₙ²))`, and use
-- `εₙ → 0` to force `1 / εₙ → +∞`.
theorem closedScalarRelativeEntropy_value_zSequence_tendsto_top {ε : ℕ → ℝ}
    (hε_pos : ∀ n, 0 < ε n)
    (hε_tendsto : Tendsto ε atTop (nhds 0)) :
    Tendsto (fun n ↦ (closedScalarRelativeEntropy (example11_25zSequence ε n) : EReal))
      atTop (nhds (⊤ : EReal)) := sorry

/- The origin lies in the minimizer set of `closedScalarRelativeEntropy`. -/
-- Proof sketch: rewrite `Argmin` using `closedScalarRelativeEntropy_argmin_eq` and evaluate the
-- defining set
-- predicate at `(0, 0)`.
theorem closedScalarRelativeEntropy_origin_mem_argmin :
    (0 : ℝ × ℝ) ∈ Argmin f := sorry

/-- Example 11.25: for every positive sequence `εₙ → 0`, the sequences
`xₙ = (εₙ, εₙ)`, `yₙ = (εₙ, exp (-1 / εₙ))`, and `zₙ = (εₙ, exp (-1 / εₙ²))`
all converge to the minimizer `(0, 0)`, while the corresponding function values converge to
`0`, `1`, and `+∞`, respectively. -/
-- Proof sketch: use `closedScalarRelativeEntropy_origin_mem_argmin` for the minimizer claim,
-- combine the three
-- sequence convergence theorems with the three separate value-limit theorems.
theorem example11_25_same_limit_different_value_limits {ε : ℕ → ℝ} (hε_pos : ∀ n, 0 < ε n)
    (hε_tendsto : Tendsto ε atTop (nhds 0)) :
    (0 : ℝ × ℝ) ∈ Argmin f ∧
      Tendsto (example11_25xSequence ε) atTop (nhds (0 : ℝ × ℝ)) ∧
      Tendsto (example11_25ySequence ε) atTop (nhds (0 : ℝ × ℝ)) ∧
      Tendsto (example11_25zSequence ε) atTop (nhds (0 : ℝ × ℝ)) ∧
      Tendsto (fun n ↦ (closedScalarRelativeEntropy (example11_25xSequence ε n) : EReal))
        atTop (nhds (0 : EReal)) ∧
      Tendsto (fun n ↦ (closedScalarRelativeEntropy (example11_25ySequence ε n) : EReal))
        atTop (nhds (1 : EReal)) ∧
      Tendsto (fun n ↦ (closedScalarRelativeEntropy (example11_25zSequence ε n) : EReal))
        atTop (nhds (⊤ : EReal)) := by
  refine ⟨closedScalarRelativeEntropy_origin_mem_argmin,
    example11_25xSequence_tendsto_zero hε_tendsto,
    example11_25ySequence_tendsto_zero hε_pos hε_tendsto,
    example11_25zSequence_tendsto_zero hε_pos hε_tendsto,
    closedScalarRelativeEntropy_value_xSequence_tendsto_zero (fun n ↦ (hε_pos n).le),
    closedScalarRelativeEntropy_value_ySequence_tendsto_one hε_pos hε_tendsto,
    closedScalarRelativeEntropy_value_zSequence_tendsto_top hε_pos hε_tendsto⟩

end ERealFunction
