/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Convex.Gauge
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_lattice_free
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_definition_6_3_2_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

section Lemma628

-- This lemma reuses the chapter's canonical lattice-free owner `is_lattice_free` from
-- Section 6.2 and writes the translate `B - f` in the same set-builder form used elsewhere in
-- Chapter 6.

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ
local notation "ContAssignment" => Rq →₀ NNReal

open Set
open scoped IntegerVectorNotation

/-- Helper for Lemma 6.28: translation by `f` carries the interior of `{r | f + r ∈ B}` onto the
interior of `B`. -/
lemma memInterior_setOf_add_mem_iff
    (B : Set Rq) (f r : Rq) :
    r ∈ interior {s : Rq | f + s ∈ B} ↔ f + r ∈ interior B := by
  -- Rewrite the translated set as the preimage under the additive homeomorphism `x ↦ f + x`.
  simpa [Set.preimage] using
    show r ∈ interior ((Homeomorph.addLeft f) ⁻¹' B) ↔
        r ∈ (Homeomorph.addLeft f) ⁻¹' interior B by
      rw [← (Homeomorph.addLeft f).preimage_interior B]

/-- Helper for Lemma 6.28: the gauge of a convex set with `0` in its interior is bounded above by
the finite weighted sum of the pointwise gauges. -/
lemma gauge_le_continuousAssignmentSum
    {K : Set Rq}
    (hK_convex : Convex ℝ K)
    (hK_zero : (0 : Rq) ∈ interior K)
    (y : ContAssignment) :
    gauge K (y.sum (fun r a ↦ (a : ℝ) • r)) ≤
      y.sum (fun r a ↦ gauge K r * (a : ℝ)) := by
  have hK_abs : Absorbent ℝ K :=
    absorbent_nhds_zero (mem_interior_iff_mem_nhds.1 hK_zero)
  -- Rewrite the finitely supported sum as a `Finset` sum so `gauge_sum_le` applies directly.
  calc
    gauge K (y.sum (fun r a ↦ (a : ℝ) • r)) =
        gauge K (y.support.sum (fun r ↦ (y r : ℝ) • r)) := by
          rw [Finsupp.sum]
    _ ≤ y.support.sum (fun r ↦ gauge K ((y r : ℝ) • r)) :=
          gauge_sum_le (s := K) hK_convex hK_abs y.support (fun r ↦ (y r : ℝ) • r)
    _ = y.support.sum (fun r ↦ gauge K r * (y r : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          have hr_nonneg : 0 ≤ (y r : ℝ) := by
            exact_mod_cast (y r).2
          simpa [smul_eq_mul, mul_comm] using
            (gauge_smul_of_nonneg (s := K) (a := (y r : ℝ)) hr_nonneg r)
    _ = y.sum (fun r a ↦ gauge K r * (a : ℝ)) := by
          rw [Finsupp.sum]

/-- Helper for Lemma 6.28: an integer point translated into `B - f` cannot have gauge strictly
less than `1`, because that would place the original integer point in `interior B`. -/
lemma one_le_gauge_sub_of_integerPoint
    {B : Set Rq}
    {f z : Rq}
    (hB_convex : Convex ℝ B)
    (hB_free : is_lattice_free B)
    (hf : f ∈ interior B)
    (hz : z ∈ ℤ^q) :
    1 ≤ gauge {r : Rq | f + r ∈ B} (z - f) := by
  let K : Set Rq := {r : Rq | f + r ∈ B}
  have hK_zero : (0 : Rq) ∈ interior K := by
    -- The translate `B - f` contains the origin in its interior because `f ∈ interior B`.
    rw [memInterior_setOf_add_mem_iff B f (0 : Rq)]
    simpa using hf
  have hK_convex : Convex ℝ K := by
    -- Convexity is preserved by translation.
    intro x hx y hy a b ha hb hab
    have hxy : a • (f + x) + b • (f + y) ∈ B :=
      hB_convex hx hy ha hb hab
    have hsumf : a • f + b • f = f := by
      calc
        a • f + b • f = (a + b) • f := by rw [← add_smul]
        _ = f := by simp [hab]
    have htranslate :
        a • (f + x) + b • (f + y) = f + (a • x + b • y) := by
      calc
        a • (f + x) + b • (f + y) = (a • f + b • f) + (a • x + b • y) := by
          simp [smul_add, add_assoc, add_left_comm]
        _ = f + (a • x + b • y) := by rw [hsumf]
    rw [htranslate] at hxy
    exact hxy
  have hK_nhds : K ∈ nhds (0 : Rq) :=
    mem_interior_iff_mem_nhds.1 hK_zero
  have hnot_lt : ¬ gauge K (z - f) < 1 := by
    intro hlt
    have hz_sub_int : z - f ∈ interior K :=
      (gauge_lt_one_iff_mem_interior hK_convex hK_nhds).1 hlt
    have hz_int : z ∈ interior B := by
      simpa using (memInterior_setOf_add_mem_iff B f (z - f)).1 hz_sub_int
    exact (is_lattice_free.not_mem_interior hB_free hz) hz_int
  -- The strict-gauge contradiction yields the desired lower bound.
  exact not_lt.mp hnot_lt

/-- Lemma 6.28. If `B` is a `ℤ^q`-free closed convex set and `f ∈ interior B`, then the gauge of
the translated set `B - f = {r | f + r ∈ B}` is a valid function for the continuous infinite
relaxation `R_f`. -/
theorem lemma_6_28_gauge_is_valid_function
    (B : Set Rq)
    (f : Rq)
    (hB_closed : IsClosed B)
    (hB_convex : Convex ℝ B)
    (hB_free : is_lattice_free B)
    (hf : f ∈ interior B) :
    IsValidFunctionForContinuousInfiniteRelaxation f (gauge {r | f + r ∈ B}) := by
  let K : Set Rq := {r : Rq | f + r ∈ B}
  let _ := hB_closed
  have hK_zero : (0 : Rq) ∈ interior K := by
    -- The translated set inherits an interior origin from `f ∈ interior B`.
    rw [memInterior_setOf_add_mem_iff B f (0 : Rq)]
    simpa [K] using hf
  have hK_convex : Convex ℝ K := by
    -- Translation preserves convexity, which is the sublinearity input for the gauge.
    intro x hx y hy a b ha hb hab
    have hxy : a • (f + x) + b • (f + y) ∈ B :=
      hB_convex hx hy ha hb hab
    have hsumf : a • f + b • f = f := by
      calc
        a • f + b • f = (a + b) • f := by rw [← add_smul]
        _ = f := by simp [hab]
    have htranslate :
        a • (f + x) + b • (f + y) = f + (a • x + b • y) := by
      calc
        a • (f + x) + b • (f + y) = (a • f + b • f) + (a • x + b • y) := by
          simp [smul_add, add_assoc, add_left_comm]
        _ = f + (a • x + b • y) := by rw [hsumf]
    rw [htranslate] at hxy
    exact hxy
  refine ⟨?_⟩
  intro y hy
  have hz : continuous_infinite_balance f y ∈ ℤ^q :=
    hy.balance_mem_integerVectors
  have hbalance :
      continuous_infinite_balance f y - f =
        y.sum (fun r a ↦ (a : ℝ) • r) := by
    -- Expanding the feasible balance removes the shift by `f`.
    simp [continuous_infinite_balance, sub_eq_add_neg, add_assoc]
  -- Compare the gauge at the lattice balance with the gauge-sum upper bound.
  calc
    1 ≤ gauge K (continuous_infinite_balance f y - f) :=
      one_le_gauge_sub_of_integerPoint hB_convex hB_free hf hz
    _ = gauge K (y.sum (fun r a ↦ (a : ℝ) • r)) := by
      rw [hbalance]
    _ ≤ y.sum (fun r a ↦ gauge K r * (a : ℝ)) :=
      gauge_le_continuousAssignmentSum hK_convex hK_zero y
    _ = y.sum (fun r a ↦ gauge K r * a) := by
      simp

namespace IsValidFunctionForContinuousInfiniteRelaxation

/-- If `ψ` is the gauge of the translated set `B - f = {r | f + r ∈ B}` for a closed convex
`ℤ^q`-free set `B` with `f ∈ interior B`, then `ψ` is valid for `R_f`. -/
theorem of_eq_gauge_translate
    {B : Set Rq}
    {f : Rq}
    {ψ : Rq → ℝ}
    (hψ : ψ = gauge {r | f + r ∈ B})
    (hB_closed : IsClosed B)
    (hB_convex : Convex ℝ B)
    (hB_free : is_lattice_free B)
    (hf : f ∈ interior B) :
    IsValidFunctionForContinuousInfiniteRelaxation f ψ := by
  simpa [hψ] using
    lemma_6_28_gauge_is_valid_function B f hB_closed hB_convex hB_free hf

end IsValidFunctionForContinuousInfiniteRelaxation

end Lemma628
