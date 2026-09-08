module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

noncomputable section

open scoped BigOperators

namespace LocalCutoff.GraphTransform

/-!
# Finite non-principal residual sums

The graph-jet composition separates one principal composition from finitely many
non-principal terms.  This file records the finite-sum estimate independently of
the concrete composition type and its source-specific coefficient bounds.
-/

/-- Helper for Infrastructure I.16: a finite family whose distinguished term is zero
    inherits a total norm bound from a uniform bound on every other term. -/
theorem norm_sum_if_eq_zero_le
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    (f : ι → E) (i₀ : ι) (δ ε : ℝ)
    (hterm : ∀ i, i ≠ i₀ → ‖f i‖ ≤ δ)
    (hbudget : ((Fintype.card ι : ℝ) - 1) * δ ≤ ε) :
    ‖∑ i, if i = i₀ then 0 else f i‖ ≤ ε := by
  classical
  calc
    ‖∑ i, if i = i₀ then 0 else f i‖ ≤
        ∑ i, ‖if i = i₀ then 0 else f i‖ := by
      exact norm_sum_le Finset.univ (fun i => if i = i₀ then 0 else f i)
    _ ≤ ∑ i, (if i = i₀ then 0 else δ) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases h : i = i₀
      · rw [if_pos h, if_pos h]
        simp
      · rw [if_neg h, if_neg h]
        exact hterm i h
    _ = ((Fintype.card ι : ℝ) - 1) * δ := by
      calc
        (∑ i, (if i = i₀ then 0 else δ)) =
            ∑ i, (δ - if i = i₀ then δ else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h : i = i₀
          · rw [if_pos h, if_pos h]
            simp
          · rw [if_neg h, if_neg h]
            ring
        _ = (∑ i, δ) - ∑ i, (if i = i₀ then δ else 0) := by
          rw [Finset.sum_sub_distrib]
        _ = ((Fintype.card ι : ℝ) - 1) * δ := by
          rw [Finset.sum_const, Finset.sum_ite_eq', Finset.card_univ]
          simp
          ring
    _ ≤ ε := hbudget

end LocalCutoff.GraphTransform
