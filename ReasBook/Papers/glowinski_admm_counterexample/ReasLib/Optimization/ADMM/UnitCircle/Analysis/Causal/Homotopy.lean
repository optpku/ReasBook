/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.Truncation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module

@[expose] public section

open Filter
open scoped ENNReal

namespace ADMM.UnitCircle.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Square summability at a homotopy parameter, for every square-summable
forcing. The causal sequence is defined before membership is asserted. -/
def StableAt (V : ℝ → (ℕ → E) → (ℕ → E)) (τ : ℝ) : Prop :=
  ∀ e : lp (fun _ : ℕ ↦ E) 2, Memℓp (V τ e) 2

/-- One homotopy step uses finitely supported perturbations of the forcing.
The `ℓ₂` a priori estimate is used only on solutions already known to belong
to `ℓ₂`; uniform bounds on every prefix then establish the new membership. -/
theorem stableAt_step
    (F : (ℕ → E) → (ℕ → E)) (V : ℝ → (ℕ → E) → (ℕ → E))
    {C L τ₀ τ : ℝ} (hC : 0 < C) (hL : 0 ≤ L)
    (hτ₀ : τ₀ ∈ Set.Icc (0 : ℝ) 1)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hsolve : ∀ (t : ℝ) (e : ℕ → E) (k : ℕ), V t e k = e k + t • F (V t e) k)
    (hunique : ∀ (t : ℝ) (e : ℕ → E) (T : ℕ) (v w : ℕ → E),
      (∀ k < T, v k = e k + t • F v k) →
      (∀ k < T, w k = e k + t • F w k) →
      ∀ k < T, v k = w k)
    (hF : ∀ v T, ‖truncate T (F v)‖ ≤ L * ‖truncate T v‖)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ e : lp (fun _ : ℕ ↦ E) 2, ∀ hv : Memℓp (V t e) 2,
        ‖(⟨V t e, hv⟩ : lp (fun _ : ℕ ↦ E) 2)‖ ≤ C * ‖e‖)
    (hsmall : C * |τ - τ₀| * L ≤ 1 / 2)
    (hstable : StableAt V τ₀) : StableAt V τ := by
  intro e
  apply memℓp_of_truncate_norm_le (B := 2 * C * ‖e‖)
  intro T
  let v := V τ (e : ℕ → E)
  let eT := truncate T ((e : ℕ → E) + (τ - τ₀) • F v)
  have hv₀ : Memℓp (V τ₀ eT) 2 := hstable eT
  have hsame : truncate T v = truncate T (V τ₀ eT) := by
    apply truncate_congr
    apply hunique τ₀ (eT : ℕ → E) T v (V τ₀ eT)
    · intro k hk
      have h := hsolve τ (e : ℕ → E) k
      change v k = eT k + τ₀ • F v k
      simp only [eT, truncate_apply, if_pos hk, Pi.add_apply, Pi.smul_apply]
      change v k = e k + (τ - τ₀) • F v k + τ₀ • F v k
      change v k = e k + τ • F v k at h
      rw [h]
      module
    · intro k _
      exact hsolve τ₀ (eT : ℕ → E) k
  have hprefix : ‖truncate T v‖ ≤ C * ‖eT‖ := by
    rw [hsame]
    exact (truncate_norm_le T (⟨V τ₀ eT, hv₀⟩ : lp (fun _ : ℕ ↦ E) 2)).trans
      (hbound τ₀ hτ₀ eT hv₀)
  have heT : ‖eT‖ ≤ ‖e‖ + |τ - τ₀| * L * ‖truncate T v‖ := by
    calc
      ‖eT‖ = ‖truncate T (e : ℕ → E) + (τ - τ₀) • truncate T (F v)‖ := by
        change ‖truncate T ((e : ℕ → E) + (τ - τ₀) • F v)‖ = _
        rw [truncate_add, truncate_smul]
      _ ≤ ‖truncate T (e : ℕ → E)‖ + ‖(τ - τ₀) • truncate T (F v)‖ := norm_add_le _ _
      _ = ‖truncate T (e : ℕ → E)‖ + |τ - τ₀| * ‖truncate T (F v)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖e‖ + |τ - τ₀| * (L * ‖truncate T v‖) := by
        exact add_le_add (truncate_norm_le T e)
          (mul_le_mul_of_nonneg_left (hF v T) (abs_nonneg _))
      _ = _ := by ring
  have hcombined := hprefix.trans (mul_le_mul_of_nonneg_left heT hC.le)
  have habsorb := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (truncate T v))
  change ‖truncate T v‖ ≤ 2 * C * ‖e‖
  nlinarith

/-- A fixed small step size reaches the full feedback problem in finitely
many steps. This is the causal `ℓ₂` homotopy argument used in Appendix C.1. -/
theorem stableAt_one
    (F : (ℕ → E) → (ℕ → E)) (V : ℝ → (ℕ → E) → (ℕ → E))
    {C L : ℝ} (hC : 0 < C) (hL : 0 ≤ L)
    (hsolve : ∀ (t : ℝ) (e : ℕ → E) (k : ℕ), V t e k = e k + t • F (V t e) k)
    (hunique : ∀ (t : ℝ) (e : ℕ → E) (T : ℕ) (v w : ℕ → E),
      (∀ k < T, v k = e k + t • F v k) →
      (∀ k < T, w k = e k + t • F w k) →
      ∀ k < T, v k = w k)
    (hF : ∀ v T, ‖truncate T (F v)‖ ≤ L * ‖truncate T v‖)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ e : lp (fun _ : ℕ ↦ E) 2, ∀ hv : Memℓp (V t e) 2,
        ‖(⟨V t e, hv⟩ : lp (fun _ : ℕ ↦ E) 2)‖ ≤ C * ‖e‖) :
    StableAt V 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 * C * L) 1)
  have hNpos : 0 < (N : ℝ) := by linarith [le_max_right (2 * C * L) 1]
  have hNlarge : 2 * C * L < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hgrid : ∀ i : ℕ, i ≤ N → StableAt V ((i : ℝ) / N) := by
    intro i
    induction i with
    | zero =>
        intro _ e
        have hz : V 0 (e : ℕ → E) = e := by
          funext k
          simpa using hsolve 0 (e : ℕ → E) k
        simpa only [Nat.cast_zero, zero_div, hz] using (lp.memℓp e)
    | succ i ih =>
        intro hi
        have hiN : i ≤ N := Nat.le_trans (Nat.le_succ i) hi
        have hτ₀ : (i : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := by
          constructor
          · exact div_nonneg (Nat.cast_nonneg i) hNpos.le
          · exact (div_le_one hNpos).mpr (by exact_mod_cast hiN)
        have hτ : ((i + 1 : ℕ) : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := by
          constructor
          · exact div_nonneg (Nat.cast_nonneg (i + 1)) hNpos.le
          · exact (div_le_one hNpos).mpr (by exact_mod_cast hi)
        have hdiff : |((i + 1 : ℕ) : ℝ) / N - (i : ℝ) / N| = 1 / N := by
          rw [Nat.cast_add, Nat.cast_one, add_div, add_sub_cancel_left,
            abs_of_pos (div_pos (by norm_num) hNpos)]
        have hsmall : C * |((i + 1 : ℕ) : ℝ) / N - (i : ℝ) / N| * L ≤ 1 / 2 := by
          rw [hdiff]
          have h : (2 * C * L) / N < 1 := (div_lt_one hNpos).mpr hNlarge
          have heq : C * (1 / (N : ℝ)) * L = ((2 * C * L) / N) / 2 := by ring
          rw [heq]
          linarith
        exact stableAt_step F V hC hL hτ₀ hτ hsolve hunique hF hbound hsmall (ih hiN)
  simpa only [div_self hNpos.ne'] using hgrid N le_rfl

end ADMM.UnitCircle.Causal
