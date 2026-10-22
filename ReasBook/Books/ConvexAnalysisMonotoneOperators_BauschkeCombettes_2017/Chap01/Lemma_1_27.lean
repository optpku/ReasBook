/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped BigOperators

variable {X : Type u} [TopologicalSpace X]

private lemma lowerSemicontinuous_const_mul_of_pos {a : ℝ} (ha : 0 < a) {g : X → EReal}
    (hg : LowerSemicontinuous g) :
    LowerSemicontinuous (fun x ↦ (a : EReal) * g x) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro x
  have ha_nonneg : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast (le_of_lt ha : 0 ≤ a)
  calc
    (a : EReal) * g x ≤ (a : EReal) * Filter.liminf g (nhds x) :=
      (monotone_mul_left_of_nonneg ha_nonneg) (hg.le_liminf x)
    _ = Filter.liminf (fun y ↦ (a : EReal) * g y) (nhds x) := by
      symm
      exact EReal.liminf_const_mul_of_nonneg_of_ne_top ha_nonneg (EReal.coe_ne_top a)

private lemma lowerSemicontinuous_add_ereal {g h : X → EReal} (hg : LowerSemicontinuous g)
    (hh : LowerSemicontinuous h) :
    LowerSemicontinuous (fun x ↦ g x + h x) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro x
  calc
    g x + h x ≤ Filter.liminf g (nhds x) + Filter.liminf h (nhds x) :=
      add_le_add (hg.le_liminf x) (hh.le_liminf x)
    _ ≤ Filter.liminf (fun y ↦ g y + h y) (nhds x) := by
      simpa using (EReal.le_liminf_add : Filter.liminf g (nhds x) + Filter.liminf h (nhds x) ≤
        Filter.liminf (g + h) (nhds x))

private lemma lowerSemicontinuous_finset_sum_ereal {ι : Type v} {s : Finset ι}
    {f : ι → X → EReal} (hf : ∀ i ∈ s, LowerSemicontinuous (f i)) :
    LowerSemicontinuous (fun x ↦ s.sum fun i ↦ f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : X ↦ (0 : EReal)))
  | @insert i s hi ih =>
      have hi_term : LowerSemicontinuous (f i) := hf i (Finset.mem_insert_self i s)
      have hs_sum : LowerSemicontinuous (fun x ↦ s.sum fun j ↦ f j x) :=
        ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
      simpa [Finset.sum_insert, hi] using lowerSemicontinuous_add_ereal hi_term hs_sum

/-- Lemma 1.27: a finite positive weighted sum of lower semicontinuous extended-real-valued
functions is lower semicontinuous.

This formulation is valid on any topological space, hence in particular on a Hausdorff space. -/
theorem lowerSemicontinuous_weighted_sum
    {ι : Type v} [Finite ι] {f : ι → X → EReal} {α : ι → ℝ}
    (hα : ∀ i, 0 < α i) (hf : ∀ i, LowerSemicontinuous (f i)) :
    let _ : Fintype ι := Fintype.ofFinite ι
    LowerSemicontinuous (fun x ↦ ∑ i, ((α i : EReal) * f i x)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hweighted :
      ∀ i ∈ (Finset.univ : Finset ι), LowerSemicontinuous (fun x ↦ (α i : EReal) * f i x) :=
    fun i _ ↦ lowerSemicontinuous_const_mul_of_pos (hα i) (hf i)
  simpa using lowerSemicontinuous_finset_sum_ereal hweighted
