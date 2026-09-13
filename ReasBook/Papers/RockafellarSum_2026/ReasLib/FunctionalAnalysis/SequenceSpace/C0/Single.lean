/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.Coordinate

/-!
# Single-coordinate vectors in `C0Seq`

This module defines the canonical finitely supported coordinate vectors and
their evaluation and norm identities.
-/

public section

open Topology

/-- A function supported at one natural-number coordinate tends to zero along the cocompact
filter. -/
private theorem piSingleTendstoCocompact (n : ℕ) (r : ℝ) :
    Filter.Tendsto (Pi.single n r : ℕ → ℝ) (Filter.cocompact ℕ) (nhds 0) := by
  -- The singleton function has support contained in the finite set `{n}`.
  have hSupport : (Pi.single n r : ℕ → ℝ).HasFiniteSupport :=
    (Set.finite_singleton n).subset Pi.support_single_subset
  -- Finite support gives convergence to `pure 0`, hence to every neighborhood of zero.
  rw [Filter.cocompact_eq_cofinite]
  exact (tendsto_cofinite_pure_iff.2 hSupport).mono_right (pure_le_nhds 0)

/-- The element of `C0Seq` whose value is `r` at coordinate `n` and zero at every other
coordinate. -/
def c0Single (n : ℕ) (r : ℝ) : C0Seq where
  toFun := Pi.single n r
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := piSingleTendstoCocompact n r

/-- The coordinate formula for `c0Single`. -/
@[simp]
theorem c0Single_apply (n : ℕ) (r : ℝ) (m : ℕ) :
    c0Single n r m = if m = n then r else 0 := by
  -- Project the bundled sequence to the underlying `Pi.single` coordinate formula.
  change (Pi.single n r : ℕ → ℝ) m = if m = n then r else 0
  rw [Pi.single_apply]

/-- A standard coordinate vector has finite support. -/
theorem c0Single_hasFiniteSupport (n : ℕ) (r : ℝ) :
    (fun m ↦ c0Single n r m).HasFiniteSupport := by
  -- Bound the coordinate support by the finite singleton `{n}`.
  rw [Function.HasFiniteSupport]
  refine (Set.finite_singleton n).subset ?_
  intro m hm
  simp only [Function.mem_support] at hm
  simp only [Set.mem_singleton_iff]
  by_contra hmn
  rw [c0Single_apply, if_neg hmn] at hm
  exact hm rfl

/-- The norm of a standard coordinate vector is the absolute value of its entry. -/
@[simp]
theorem norm_c0Single (n : ℕ) (r : ℝ) : ‖c0Single n r‖ = |r| := by
  -- Bound the coordinate supremum above by the only possibly nonzero entry.
  apply le_antisymm
  · rw [C0Seq.norm_eq_iSup_abs]
    refine ciSup_le fun m ↦ ?_
    rw [c0Single_apply]
    split_ifs
    · exact le_rfl
    · simpa only [abs_zero] using abs_nonneg r
  -- The selected coordinate supplies the matching lower bound for the norm.
  · have hCoordinate := C0Seq.abs_apply_le_norm (c0Single n r) n
    rw [c0Single_apply, if_pos rfl] at hCoordinate
    exact hCoordinate
