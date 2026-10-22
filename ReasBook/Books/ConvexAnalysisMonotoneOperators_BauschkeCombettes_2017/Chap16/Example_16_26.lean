/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Example_12_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Example_17_46

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "L2Nat" => lp (fun _ : ℕ ↦ ℝ) 2

omit [CompleteSpace H] in
/-- Coercing the Example 16.26 function to `EReal` recovers the supremum of the coordinate ratios.
-/
@[simp] theorem hilbertBasisCoordinateSupremum_apply
    (b : HilbertBasis ℕ ℝ H) (α : ℕ → ℝ) (x : H) :
    (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0 x : EReal) =
      ⨆ n : ℕ, (((⟪x, b n⟫_ℝ) / α n : ℝ) : EReal) := by
  trans ⨆ n : ℕ, ((⟪x, (α n)⁻¹ • b n⟫_ℝ - 0 : ℝ) : EReal)
  · simpa using affineInnerSupremum_apply (fun n ↦ (α n)⁻¹ • b n) 0 x
  · simp only [sub_zero]
    refine iSup_congr fun n ↦ ?_
    have hratio : ⟪x, (α n)⁻¹ • b n⟫_ℝ = ⟪x, b n⟫_ℝ / α n := by
      simp [div_eq_mul_inv, inner_smul_right, mul_comm]
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hratio

/-- The witness `z = -∑ α_n e_n` from Example 16.26, encoded through the Hilbert-basis
identification with `ℓ²(ℕ, ℝ)`. -/
noncomputable def hilbertBasisCoordinateSupremumWitness
    (b : HilbertBasis ℕ ℝ H) (α : L2Nat) : H :=
  -(b.repr.symm α)

-- Proof sketch: each coordinate map `x ↦ ⟪x, b n⟫ / α_n` is a continuous affine functional. The
-- supremum of continuous affine minorants is lower semicontinuous and convex, and the origin
-- belongs to the effective domain because every coordinate ratio vanishes there.
/-- The Example 16.26 function belongs to `Γ₀(H)`. -/
theorem hilbertBasisCoordinateSupremum_mem_gammaZero
    (b : HilbertBasis ℕ ℝ H) (α : ℕ → ℝ) :
    affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0 ∈ Γ₀(H) := sorry

section

variable (b : HilbertBasis ℕ ℝ H)
local notation "Cₛ" => (Submodule.span ℝ (Set.range b) : Submodule ℝ H)
local notation "C" => (Cₛ : Set H)

-- Proof sketch: a vector in the span of the basis has only finitely many nonzero basis
-- coordinates, so the supremum of the coordinate ratios is finite there.
/-- The span `C = span{e_n}` lies in the effective domain of the Example 16.26 function. -/
theorem hilbertBasisCoordinateSupremumSpan_subset_effectiveDomain
    (α : ℕ → ℝ) :
    C ⊆ effectiveDomain (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0) :=
  sorry

/- The span `C = span{e_n}` is convex by the canonical submodule convexity theorem. -/
#check Submodule.convex Cₛ

/- The span `C = span{e_n}` is dense by the canonical Hilbert-basis span theorem. -/
#check b.dense_span

-- Proof sketch: on the span `C`, the coordinate ratios include the zero tail and therefore have
-- nonnegative supremum; off `C`, the indicator contributes `⊤`. Thus `f + ι_C` is pointwise
-- nonnegative.
/-- The indicator-augmented Example 16.26 function satisfies `0 ≤ f + ι_C` pointwise. -/
theorem zero_le_hilbertBasisCoordinateSupremumWithIndicator
    (α : ℕ → ℝ) :
    (fun _ : H ↦ (0 : EReal)) ≤
      (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal +
        (ι[C]).asEReal := sorry

-- Proof sketch: the basis coefficients of `z = -∑ α_n e_n` are exactly `-α_n`, so every ratio
-- `⟪z, e_n⟫ / α_n` equals `-1` because `α_n ≠ 0`; taking the supremum gives `f(z) = -1`.
/-- The Example 16.26 witness `z = -∑ α_n e_n` satisfies `f(z) = -1`. -/
theorem hilbertBasisCoordinateSupremum_apply_witness
    (α : L2Nat) (hα_ne : ∀ n : ℕ, α n ≠ 0) :
    (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal
        (hilbertBasisCoordinateSupremumWitness b α) =
      (-1 : EReal) := sorry

-- Proof sketch: every vector in `span{e_n}` has finite support in its basis coordinates, whereas
-- the witness `z = -∑ α_n e_n` has every coordinate equal to `-α_n ≠ 0` because `α_n ≠ 0`.
/-- The Example 16.26 witness does not belong to the span `C = span{e_n}`. -/
theorem hilbertBasisCoordinateSupremumWitness_not_mem_span
    (α : L2Nat) (hα_ne : ∀ n : ℕ, α n ≠ 0) :
    hilbertBasisCoordinateSupremumWitness b α ∉ C := sorry

-- Proof sketch: the previous helper theorem gives `0 ≤ f + ι_C`, so Proposition 13.16(ii)
-- yields `0 = 0** ≤ (f + ι_C)**`. Evaluating at the witness `z = -∑ α_n e_n`, the function value
-- is `f(z) = -1`, so `(f + ι_C)** z ≠ f z`; hence the two functions are not equal.
/-- Example 16.26: for the Hilbert-basis coefficient supremum `f(x) = sup_n ⟪x,e_n⟫ / α_n` and
the span `C = span{e_n}`, the Fenchel biconjugate of `f + ι_C` does not coincide with `f`. -/
theorem hilbertBasisCoordinateSupremumWithIndicator_biconjugate_ne
    (α : L2Nat) (hα_ne : ∀ n : ℕ, α n ≠ 0) :
    ((affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal +
        (ι[C]).asEReal)∗∗ ≠
      (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal := sorry

end

end

end ERealFunction
