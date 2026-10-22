/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u

section

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

omit [Module ℝ X] in
/-- Helper for Proposition 6.3: unpack pointwise addition closure into an elementwise addition
law. -/
lemma add_mem_of_add_subset {C : Set X} (hAdd : C + C ⊆ C) {x y : X} (hx : x ∈ C) (hy : y ∈ C) :
    x + y ∈ C := by
  -- Turn the elementwise assumptions into membership in the pointwise sum `C + C`.
  exact hAdd (Set.add_mem_add hx hy)

omit [Module ℝ X] in
/-- Helper for Proposition 6.3: a set containing `0` and closed under pointwise addition contains
all natural multiples of each of its points. -/
lemma nsmul_mem_of_zero_add_subset {C : Set X} (h0C : (0 : X) ∈ C) (hAdd : C + C ⊆ C)
    {x : X} (hx : x ∈ C) : ∀ n : ℕ, n • x ∈ C := by
  intro n
  induction n with
  | zero =>
      -- The zeroth multiple is `0`, which belongs to `C` by assumption.
      simpa using h0C
  | succ n ihn =>
      -- Pass from `n • x` to `(n + 1) • x` by one more application of additive closure.
      simpa [succ_nsmul] using add_mem_of_add_subset hAdd ihn hx

/-- Helper for Proposition 6.3: convexity from the origin upgrades additive closure to full
closure under nonnegative real scalars. -/
lemma nonneg_smul_mem_of_convex_zero_add_subset {C : Set X} (hC_convex : Convex ℝ C)
    (h0C : (0 : X) ∈ C) (hAdd : C + C ⊆ C) {x : X} (hx : x ∈ C) {a : ℝ} (ha : 0 ≤ a) :
    a • x ∈ C := by
  obtain ⟨n, hna⟩ := exists_nat_ge a
  have hNx_nat : ((n + 1 : ℕ) • x) ∈ C := by
    -- First build a large natural multiple of `x` that still stays in `C`.
    exact nsmul_mem_of_zero_add_subset h0C hAdd hx (n + 1)
  have hNx : ((((n + 1 : ℕ) : ℝ)) • x) ∈ C := by
    -- Rewrite that natural multiple as a real scalar multiple.
    rw [Nat.cast_smul_eq_nsmul ℝ (n + 1) x]
    exact hNx_nat
  have hfrac : a / (((n + 1 : ℕ) : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · -- The rescaling factor is nonnegative because both numerator and denominator are.
      exact div_nonneg ha (by positivity)
    · -- It is at most `1` because `n + 1` was chosen to dominate `a`.
      have hle : a ≤ (((n + 1 : ℕ) : ℝ)) := by
        exact le_trans hna (by exact_mod_cast Nat.le_succ n)
      exact div_le_one_of_le₀ hle (by positivity)
  have hmem : (a / (((n + 1 : ℕ) : ℝ))) • ((((n + 1 : ℕ) : ℝ)) • x) ∈ C := by
    -- Convexity from `0` now contracts the large multiple back down.
    exact hC_convex.smul_mem_of_zero_mem h0C hNx hfrac
  have hscale : (a / (((n + 1 : ℕ) : ℝ))) • ((((n + 1 : ℕ) : ℝ)) • x) = a • x := by
    -- The chosen contraction exactly recovers the target scalar multiple.
    rw [smul_smul]
    have h : (a / (((n + 1 : ℕ) : ℝ))) * (((n + 1 : ℕ) : ℝ)) = a := by
      field_simp
    rw [h]
  exact hscale ▸ hmem

/-- Helper for Proposition 6.3: a project cone is stable under positive scalar multiplication. -/
private lemma smul_mem_of_isCone {C : Set X} (hC_cone : IsCone C) {x : X} (hx : x ∈ C)
    {a : ℝ} (ha : 0 < a) :
    a • x ∈ C := by
  rw [Set.isCone_iff_nonneg_smul_mem] at hC_cone
  rw [hC_cone]
  exact Set.mem_smul.mpr ⟨a, ha, x, hx, rfl⟩

-- Proof sketch: for the forward implication, use the standard pointwise characterization of
-- convexity with coefficients `1 / 2` and `1 / 2`, then rescale by the cone property to pass from
-- midpoint closure to full additivity; for the reverse implication, combine additivity with the
-- cone scaling law to show closure under all positive convex combinations.
/-- Proposition 6.3 (1): a cone in a real vector space is convex exactly when it is closed under
pointwise addition. -/
theorem IsCone.convex_iff_add_subset {C : Set X} (hC_cone : IsCone C) :
    Convex ℝ C ↔ C + C ⊆ C := by
  constructor
  · intro hC_convex
    intro z hz
    rcases Set.mem_add.1 hz with ⟨x, hx, y, hy, rfl⟩
    have hmid : ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ∈ C := by
      -- Convexity gives midpoint closure for any two points in `C`.
      exact (convex_iff_add_mem.1 hC_convex) hx hy (by positivity) (by positivity) (by norm_num)
    have hsum : (2 : ℝ) • (((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) ∈ C := by
      -- The cone law rescales the midpoint back to the full sum `x + y`.
      exact smul_mem_of_isCone hC_cone hmid (by positivity)
    simpa [smul_add, smul_smul] using hsum
  · intro hAdd
    rw [convex_iff_add_mem]
    intro x hx y hy a b ha hb hab
    by_cases ha_zero : a = 0
    · subst ha_zero
      have hb_one : b = 1 := by linarith
      subst hb_one
      simpa using hy
    by_cases hb_zero : b = 0
    · subst hb_zero
      have ha_one : a = 1 := by linarith
      subst ha_one
      simpa using hx
    have ha_pos : 0 < a := lt_of_le_of_ne ha fun h ↦ ha_zero h.symm
    have hb_pos : 0 < b := lt_of_le_of_ne hb fun h ↦ hb_zero h.symm
    -- Positive scalar closure from the cone hypothesis reduces convexity to additive closure.
    exact add_mem_of_add_subset hAdd
      (smul_mem_of_isCone hC_cone hx ha_pos)
      (smul_mem_of_isCone hC_cone hy hb_pos)

-- Proof sketch: if `C` is a cone then part (1) gives additive closure. Conversely, assume
-- convexity, `0 ∈ C`, and `C + C ⊆ C`; use additive closure to get closure under natural-number
-- multiples, then combine convexity with the presence of `0` to obtain closure under positive
-- dilations, yielding the textbook cone condition.
/-- Proposition 6.3 (2): for a convex subset containing `0`, being a cone is equivalent to being
closed under pointwise addition. -/
theorem Convex.isCone_iff_add_subset {C : Set X} (hC_convex : Convex ℝ C) (h0C : (0 : X) ∈ C) :
    IsCone C ↔ C + C ⊆ C := by
  constructor
  · intro hC_cone
    -- Reuse part (1) once convexity is already known.
    exact (IsCone.convex_iff_add_subset hC_cone).1 hC_convex
  · intro hAdd
    rw [Set.isCone_iff_nonneg_smul_mem]
    refine Subset.antisymm ?_ ?_
    · intro x hx
      exact Set.mem_smul.mpr ⟨1, by simp, x, hx, by simp⟩
    · intro x hx
      rcases Set.mem_smul.mp hx with ⟨a, ha, y, hy, rfl⟩
      exact nonneg_smul_mem_of_convex_zero_add_subset hC_convex h0C hAdd hy ha.le

end
