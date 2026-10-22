/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Tactic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace Pointwise

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

local notation "σ[" C "]" => fun u ↦ sSup ((fun x ↦ (⟪x, u⟫_ℝ : EReal)) '' C)

/-- Helper for Exercise 7.1: evaluating the support-function image after scaling the argument is the
same as evaluating it on the scaled set. -/
lemma inner_image_right_smul_eq_image_smul_set
    (C : Set 𝓗) (ρ : ℝ) (u : 𝓗) :
    ((fun x : 𝓗 ↦ (⟪x, ρ • u⟫_ℝ : EReal)) '' C) =
      ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' (ρ • C)) := by
  -- Transport the scalar from the second inner-product slot to the first one.
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨ρ • x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · simp [real_inner_smul_left, real_inner_smul_right]
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp [real_inner_smul_left, real_inner_smul_right]

/-- Helper for Exercise 7.1: scaling the set by a positive scalar multiplies every inner-product
value by the corresponding positive `EReal` scalar. -/
lemma inner_image_smul_set_eq_ereal_mul_image
    (C : Set 𝓗) (γ : ℝ) (u : 𝓗) :
    ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' (γ • C)) =
      ((fun t : EReal ↦ (γ : EReal) * t) '' ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C)) := by
  -- Rewrite the left-hand image by pulling the scalar out of the first inner-product slot.
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨x, hx, rfl⟩
    refine ⟨(⟪x, u⟫_ℝ : EReal), ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · simp [real_inner_smul_left]
  · rintro ⟨s, hs, rfl⟩
    rcases hs with ⟨x, hx, rfl⟩
    refine ⟨γ • x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · simp [real_inner_smul_left]

/-- Helper for Exercise 7.1: multiplication by a positive real scalar preserves suprema in
`EReal`. -/
lemma ereal_pos_mul_sSup (S : Set EReal) {γ : ℝ} (hγ : 0 < γ) :
    sSup ((fun t : EReal ↦ (γ : EReal) * t) '' S) = (γ : EReal) * sSup S := by
  have hγE : (0 : EReal) < (γ : EReal) := by
    exact_mod_cast hγ
  have hγ_top : (γ : EReal) ≠ ⊤ := EReal.coe_ne_top γ
  -- Show each side is the least upper bound of the scaled image by comparing upper bounds.
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (monotone_mul_left_of_nonneg hγE.le) (le_sSup hx)
  · refine (le_sSup_iff).2 ?_
    intro b hb
    have hsSup_le : sSup S ≤ b / (γ : EReal) := by
      refine sSup_le ?_
      intro a ha
      have hscaled : (γ : EReal) * a ≤ b := hb ⟨a, ha, rfl⟩
      exact (EReal.le_div_iff_mul_le hγE hγ_top).2 (by simpa [mul_comm] using hscaled)
    have hmul : sSup S * (γ : EReal) ≤ b :=
      (EReal.le_div_iff_mul_le hγE hγ_top).1 hsSup_le
    simpa [mul_comm] using hmul

/-- Helper for Exercise 7.1: reflecting the interval `[-1,1]` through the origin preserves it. -/
lemma neg_one_smul_Icc_neg_one_one : ((-1 : ℝ) • Set.Icc (-1 : ℝ) 1) = Set.Icc (-1 : ℝ) 1 := by
  -- The interval is symmetric, so multiplying by `-1` does not change it.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨hy1, hy2⟩
    constructor <;> simp at * <;> linarith
  · intro hx
    refine ⟨-x, ?_, ?_⟩
    · rcases hx with ⟨hx1, hx2⟩
      constructor <;> linarith
    · simp

/-- Helper for Exercise 7.1: the support function of `[-1,1] ⊆ ℝ` takes the value `1` at `1`. -/
lemma supportFunction_Icc_neg_one_one_at_one : σ[(Set.Icc (-1 : ℝ) 1)] (1 : ℝ) = 1 := by
  -- Bound the support function above by `1` using Cauchy-Schwarz on the interval.
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨hx1, hx2⟩
    have hnormx : ‖x‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, hx2⟩
    have hmul : ‖x‖ * ‖(1 : ℝ)‖ ≤ 1 := by
      simpa using mul_le_mul_of_nonneg_right hnormx (norm_nonneg (1 : ℝ))
    have hinner : ⟪x, (1 : ℝ)⟫_ℝ ≤ 1 := by
      exact (real_inner_le_norm x 1).trans hmul
    change ((⟪x, (1 : ℝ)⟫_ℝ : ℝ) : EReal) ≤ (1 : EReal)
    exact_mod_cast hinner
  · -- The endpoint `x = 1` attains this upper bound.
    refine le_sSup ?_
    refine ⟨1, by simp, ?_⟩
    have hself : ⟪(1 : ℝ), (1 : ℝ)⟫_ℝ = 1 := by
      norm_num [real_inner_self_eq_norm_sq]
    have hselfE : (((⟪(1 : ℝ), (1 : ℝ)⟫_ℝ : ℝ) : EReal)) = (1 : EReal) := by
      exact_mod_cast hself
    exact hselfE

-- Proof sketch: expand `σ[C]` as the supremum of `c ↦ ⟪c, ρ • u⟫`, rewrite this as
-- `c ↦ ⟪ρ • c, u⟫`, and identify the resulting image with `(ρ • C)` under the map `c ↦ ρ • c`.
/-- Exercise 7.1 (1): composing the support function of `C` with scalar multiplication by `ρ`
on the ambient Hilbert space yields the support function of the dilated set `ρ • C`. -/
theorem supportFunction_comp_smul_eq_supportFunction_smul_set
    (C : Set 𝓗) (ρ : ℝ) :
    σ[C] ∘ (fun u : 𝓗 ↦ ρ • u) = σ[ρ • C] := by
  -- Compare the two support functions pointwise at an arbitrary vector `u`.
  funext u
  -- The only difference is the indexing set of the supremum.
  change sSup ((fun x : 𝓗 ↦ (⟪x, ρ • u⟫_ℝ : EReal)) '' C) =
    sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' (ρ • C))
  exact congrArg sSup (inner_image_right_smul_eq_image_smul_set C ρ u)

-- Proof sketch: apply part (1) with `ρ = γ`, then use `γ > 0` to pull the positive scalar through
-- the supremum defining the support function.
/-- Exercise 7.1 (2): for a positive scalar `γ`, composing the support function with `γ • Id`
agrees with multiplying the support function by `γ`. -/
theorem supportFunction_comp_pos_smul_eq_mul_supportFunction
    (C : Set 𝓗) {γ : ℝ} (hγ : 0 < γ) :
    σ[C] ∘ (fun u : 𝓗 ↦ γ • u) = fun u : 𝓗 ↦ (γ : EReal) * σ[C] u := by
  -- First rewrite the composition as the support function of the scaled set.
  funext u
  rw [supportFunction_comp_smul_eq_supportFunction_smul_set (C := C) (ρ := γ)]
  -- Then rewrite the image of the scaled set and move the positive scalar through the supremum.
  change sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' (γ • C)) =
    (γ : EReal) * sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C)
  rw [inner_image_smul_set_eq_ereal_mul_image C γ u]
  exact ereal_pos_mul_sSup _ hγ

-- Proof sketch: take `C = [-1, 1] ⊆ ℝ`, for which `σ[C] u = |u|`. Evaluating at `u = 1` gives
-- `σ[C] (-1) = 1`, while `(-1) * σ[C] 1 = -1`, so the two functions are different.
/-- Exercise 7.1 (3): the interval `[-1, 1]` in `ℝ` with scalar `ρ = -1` gives a counterexample to
the identity `σ_C ∘ ρ Id = ρ σ_C`. -/
theorem supportFunction_comp_neg_smul_ne_neg_mul_supportFunction :
    σ[(Set.Icc (-1 : ℝ) 1)] ∘ (fun u : ℝ ↦ (-1 : ℝ) • u) ≠
      fun u : ℝ ↦ ((-1 : ℝ) : EReal) * σ[(Set.Icc (-1 : ℝ) 1)] u := by
  intro hEq
  -- Evaluate both functions at `u = 1` after rewriting the left-hand side with part (1).
  have hLeft :
      (σ[(Set.Icc (-1 : ℝ) 1)] ∘ (fun u : ℝ ↦ (-1 : ℝ) • u)) 1 = 1 := by
    rw [supportFunction_comp_smul_eq_supportFunction_smul_set
      (C := Set.Icc (-1 : ℝ) 1) (ρ := (-1 : ℝ))]
    rw [neg_one_smul_Icc_neg_one_one]
    exact supportFunction_Icc_neg_one_one_at_one
  have hRight :
      (fun u : ℝ ↦ ((-1 : ℝ) : EReal) * σ[(Set.Icc (-1 : ℝ) 1)] u) 1 = (-1 : EReal) := by
    change ((-1 : ℝ) : EReal) * σ[(Set.Icc (-1 : ℝ) 1)] (1 : ℝ) = (-1 : EReal)
    rw [supportFunction_Icc_neg_one_one_at_one]
    norm_num
  have hEval :
      (σ[(Set.Icc (-1 : ℝ) 1)] ∘ (fun u : ℝ ↦ (-1 : ℝ) • u)) 1 =
        (fun u : ℝ ↦ ((-1 : ℝ) : EReal) * σ[(Set.Icc (-1 : ℝ) 1)] u) 1 := by
    simpa using congrArg (fun f : ℝ → EReal ↦ f 1) hEq
  rw [hLeft, hRight] at hEval
  have hne : (1 : EReal) ≠ (-1 : EReal) := by
    intro h
    have hre : (1 : ℝ) = -1 := by
      exact EReal.coe_injective (by simpa using h)
    norm_num at hre
  exact hne hEval
