/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual

open scoped BigOperators InnerProductSpace Matrix

noncomputable section

abbrev CMS (n : ℕ) :=
  EuclideanSpace ℝ (Sum (Fin n) (Fin n × Fin n))

def cm {n : ℕ} (u : Fin n → ℝ) : CMS n :=
  WithLp.toLp 2 fun
    | Sum.inl i => u i
    | Sum.inr ij => u ij.1 * u ij.2

def sv {n : ℕ} (f : StrongDual ℝ (CMS n)) : Fin n → ℝ :=
  fun i ↦ (InnerProductSpace.toDual ℝ (CMS n)).symm f (Sum.inl i)

def sm {n : ℕ} (f : StrongDual ℝ (CMS n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (InnerProductSpace.toDual ℝ (CMS n)).symm f (Sum.inr (i, j))

def tgt (n : ℕ) : CMS n :=
  WithLp.toLp 2 fun
    | Sum.inl _ => 0
    | Sum.inr ij => if ij.1 = ij.2 then (n : ℝ)⁻¹ else 0

theorem test {n : ℕ} (f : StrongDual ℝ (CMS n)) (u : Fin n → ℝ) :
    f (cm u) = sv f ⬝ᵥ u + u ⬝ᵥ (sm f *ᵥ u) := by
  calc
    f (cm u) = inner ℝ ((InnerProductSpace.toDual ℝ (CMS n)).symm f) (cm u) := by
      rw [InnerProductSpace.toDual_symm_apply]
    _ = sv f ⬝ᵥ u + u ⬝ᵥ (sm f *ᵥ u) := by
      simp only [cm, sv, sm, PiLp.inner_apply, RCLike.inner_apply,
        conj_trivial, Matrix.mulVec, dotProduct]
      rw [Fintype.sum_sum_type]
      apply congrArg₂ (.+.)
      · apply Finset.sum_congr rfl
        intro i _
        ring
      · rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

theorem testTarget {n : ℕ} (f : StrongDual ℝ (CMS n)) :
    f (tgt n) = (n : ℝ)⁻¹ * Matrix.trace (sm f) := by
  calc
    f (tgt n) = inner ℝ ((InnerProductSpace.toDual ℝ (CMS n)).symm f) (tgt n) := by
      rw [InnerProductSpace.toDual_symm_apply]
    _ = (n : ℝ)⁻¹ * Matrix.trace (sm f) := by
      simp only [tgt, sm, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Matrix.trace,
        Matrix.diag_apply]
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp only [zero_mul, Finset.sum_const_zero, zero_add]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · ring
      · intro j _ hji
        simp [hji]
      · simp
