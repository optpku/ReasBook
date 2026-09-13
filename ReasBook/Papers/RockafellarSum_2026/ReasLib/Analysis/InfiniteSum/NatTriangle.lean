/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Triangular decompositions of double sums

This module records the diagonal, strict-upper, and strict-lower decomposition
of a summable family indexed by `ℕ × ℕ`.
-/

universe u

/-- A summable family on `ℕ × ℕ` decomposes into its diagonal, strict-upper, and
strict-lower triangular parts. -/
public theorem Summable.tsum_prod_split_triangles
    {E : Type u} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
    [CompleteSpace E] [T0Space E] {f : ℕ × ℕ → E} (hf : Summable f) :
    ∑' p, f p =
      (∑' n, f (n, n)) +
        (∑' n, ∑' m, if n < m then f (n, m) else 0) +
          ∑' n, ∑' m, if m < n then f (n, m) else 0 := by
  -- Restrict the original summable family to the three disjoint regions.
  have hdiag : Summable (fun p : ℕ × ℕ ↦ if p.1 = p.2 then f p else 0) := by
    refine hf.summable_of_eq_zero_or_self fun p ↦ ?_
    by_cases h : p.1 = p.2
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  have hupper : Summable (fun p : ℕ × ℕ ↦ if p.1 < p.2 then f p else 0) := by
    refine hf.summable_of_eq_zero_or_self fun p ↦ ?_
    by_cases h : p.1 < p.2
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  have hlower : Summable (fun p : ℕ × ℕ ↦ if p.2 < p.1 then f p else 0) := by
    refine hf.summable_of_eq_zero_or_self fun p ↦ ?_
    by_cases h : p.2 < p.1
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  -- Trichotomy places each pair in exactly one of the three regions.
  have hsplit (p : ℕ × ℕ) :
      f p = (if p.1 = p.2 then f p else 0) +
        (if p.1 < p.2 then f p else 0) +
          (if p.2 < p.1 then f p else 0) := by
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp only [if_neg (ne_of_lt h), if_pos h,
        if_neg (not_lt_of_ge (Nat.le_of_lt h)), zero_add, add_zero]
    · simp only [h, lt_self_iff_false, if_false, if_true, add_zero]
    · simp only [if_neg (Ne.symm (ne_of_lt h)),
        if_neg (not_lt_of_ge (Nat.le_of_lt h)), if_pos h, zero_add]
  -- Fubini converts the restricted product sums to the target iterated sums.
  have hdiagSum :
      (∑' p : ℕ × ℕ, if p.1 = p.2 then f p else 0) = ∑' n, f (n, n) := by
    calc
      (∑' p : ℕ × ℕ, if p.1 = p.2 then f p else 0) =
          ∑' n, ∑' m, if n = m then f (n, m) else 0 := hdiag.tsum_prod
      _ = ∑' n, f (n, n) := tsum_congr fun n ↦ by
        simpa only [eq_comm] using (tsum_ite_eq n (fun m ↦ f (n, m)))
  have hupperSum :
      (∑' p : ℕ × ℕ, if p.1 < p.2 then f p else 0) =
        ∑' n, ∑' m, if n < m then f (n, m) else 0 := hupper.tsum_prod
  have hlowerSum :
      (∑' p : ℕ × ℕ, if p.2 < p.1 then f p else 0) =
        ∑' n, ∑' m, if m < n then f (n, m) else 0 := hlower.tsum_prod
  -- Sum the pointwise decomposition and then normalize its three pieces.
  calc
    (∑' p, f p) = tsum (fun p : ℕ × ℕ ↦
        ((if p.1 = p.2 then f p else 0) +
          (if p.1 < p.2 then f p else 0)) +
            (if p.2 < p.1 then f p else 0)) := tsum_congr hsplit
    _ = tsum (fun p : ℕ × ℕ ↦
          (if p.1 = p.2 then f p else 0) +
            (if p.1 < p.2 then f p else 0)) +
        ∑' p, if p.2 < p.1 then f p else 0 :=
      (hdiag.add hupper).tsum_add hlower
    _ = ((∑' p, if p.1 = p.2 then f p else 0) +
          ∑' p, if p.1 < p.2 then f p else 0) +
        ∑' p, if p.2 < p.1 then f p else 0 := by
      rw [hdiag.tsum_add hupper]
    _ = (∑' n, f (n, n)) +
          (∑' n, ∑' m, if n < m then f (n, m) else 0) +
            ∑' n, ∑' m, if m < n then f (n, m) else 0 := by
      rw [hdiagSum, hupperSum, hlowerSum]

/-- An absolutely summable normed-group-valued family on `ℕ × ℕ` decomposes into its
diagonal, strict-upper, and strict-lower triangular parts. -/
public theorem Summable.tsum_prod_split_triangles_of_norm
    {E : Type u} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ × ℕ → E} (hf : Summable (fun p ↦ ‖f p‖)) :
    ∑' p, f p =
      (∑' n, f (n, n)) +
        (∑' n, ∑' m, if n < m then f (n, m) else 0) +
          ∑' n, ∑' m, if m < n then f (n, m) else 0 := by
  -- Absolute summability supplies the hypothesis of the structural decomposition.
  exact hf.of_norm.tsum_prod_split_triangles

/-- For a symmetric summable family on `ℕ × ℕ`, the strict-lower and strict-upper
iterated sums agree. -/
public theorem Summable.tsum_lower_eq_upper_of_symm
    {E : Type u} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
    [CompleteSpace E] [T0Space E] {f : ℕ × ℕ → E} (hf : Summable f)
    (h_symm : ∀ n m, f (n, m) = f (m, n)) :
    (∑' n, ∑' m, if m < n then f (n, m) else 0) =
      ∑' n, ∑' m, if n < m then f (n, m) else 0 := by
  -- The lower restriction remains summable, so its two summation orders agree.
  have hlower : Summable (Function.uncurry fun n m : ℕ ↦
      if m < n then f (n, m) else 0) := by
    refine hf.summable_of_eq_zero_or_self fun p ↦ ?_
    by_cases h : p.2 < p.1
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  -- After swapping coordinates, symmetry turns the lower summand into the upper one.
  calc
    (∑' n, ∑' m, if m < n then f (n, m) else 0) =
        ∑' n, ∑' m, if n < m then f (m, n) else 0 := hlower.tsum_comm.symm
    _ = ∑' n, ∑' m, if n < m then f (n, m) else 0 :=
      tsum_congr fun n ↦ tsum_congr fun m ↦ by
        by_cases h : n < m
        · rw [if_pos h, if_pos h, h_symm m n]
        · rw [if_neg h, if_neg h]

/-- A symmetric summable family on `ℕ × ℕ` has total sum equal to its diagonal sum plus
twice its strict-upper triangular sum. -/
public theorem Summable.tsum_prod_eq_diag_add_two_upper_of_symm
    {E : Type u} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
    [CompleteSpace E] [T0Space E] {f : ℕ × ℕ → E} (hf : Summable f)
    (h_symm : ∀ n m, f (n, m) = f (m, n)) :
    ∑' p, f p =
      (∑' n, f (n, n)) +
        2 • (∑' n, ∑' m, if n < m then f (n, m) else 0) := by
  -- Substitute the equality of the two triangles into the general decomposition.
  calc
    (∑' p, f p) = (∑' n, f (n, n)) +
        (∑' n, ∑' m, if n < m then f (n, m) else 0) +
          ∑' n, ∑' m, if m < n then f (n, m) else 0 :=
      hf.tsum_prod_split_triangles
    _ = (∑' n, f (n, n)) +
        (∑' n, ∑' m, if n < m then f (n, m) else 0) +
          ∑' n, ∑' m, if n < m then f (n, m) else 0 := by
      rw [hf.tsum_lower_eq_upper_of_symm h_symm]
    _ = (∑' n, f (n, n)) +
        2 • (∑' n, ∑' m, if n < m then f (n, m) else 0) := by
      rw [two_nsmul, add_assoc]
