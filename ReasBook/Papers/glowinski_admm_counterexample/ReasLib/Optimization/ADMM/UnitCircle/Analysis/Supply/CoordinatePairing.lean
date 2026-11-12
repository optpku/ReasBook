/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Supply.Pairing

@[expose] public section

open scoped BigOperators ComplexConjugate
open ADMM.ConvergenceProof

namespace ADMM.UnitCircle.Supply

/-- One real coordinate of a two-direction lag supply. -/
noncomputable def lagCoordinateSupply {m : ℕ} (x g : ℕ → Fin m → ℝ)
    (A B : ℝ) (a : Fin m) (j k : ℕ) : ℝ :=
  A * (g k a * (x k a - zeroDelay x j k a)) +
    B * (zeroDelay g j k a * (zeroDelay x j k a - x k a))

lemma lagSupply_eq_sum {m : ℕ} (x g : ℕ → Fin m → ℝ) (A B : ℝ) (j k : ℕ) :
    lagSupply x g A B j k = ∑ a : Fin m, lagCoordinateSupply x g A B a j k := by
  simp only [lagSupply, lagCoordinateSupply, dotProduct, Pi.sub_apply,
    Finset.sum_add_distrib, Finset.mul_sum]

/-- Scalar lag terms are absolutely summable under discounted square bounds. -/
theorem summable_weighted_lagCoordinate {m : ℕ} {α : ℝ}
    {x g : ℕ → Fin m → ℝ}
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k)))
    (A B : ℝ) (a : Fin m) (j : ℕ) :
    Summable (fun k ↦ timeWeight α k * lagCoordinateSupply x g A B a j k) := by
  have hxd : Summable (fun k ↦ timeWeight α k * coordinateSquare (zeroDelay x j k)) := by
    simpa only [coordinateSquare_zeroDelay, Function.comp_def] using
      (weighted_zeroDelay hx j).1
  have hgd : Summable (fun k ↦ timeWeight α k * coordinateSquare (zeroDelay g j k)) := by
    simpa only [coordinateSquare_zeroDelay, Function.comp_def] using
      (weighted_zeroDelay hg j).1
  have h₀ := summable_weighted_coordinate_pair hx hg a
  have h₁ := summable_weighted_coordinate_pair hxd hg a
  have h₂ := summable_weighted_coordinate_pair hxd hgd a
  have h₃ := summable_weighted_coordinate_pair hx hgd a
  apply (((h₀.sub h₁).mul_left A).add ((h₂.sub h₃).mul_left B)).congr
  intro k
  dsimp only [lagCoordinateSupply]
  ring

/-- A scalar two-direction lag is exactly the three bilateral pairings whose
symbols are the constant, backward, and forward Fourier characters. -/
theorem weighted_lagCoordinate_pairing {m : ℕ} (α : ℝ)
    (x g : ℕ → Fin m → ℝ)
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k)))
    (A B : ℝ) (a : Fin m) (j : ℕ) :
    ((∑' k, timeWeight α k * lagCoordinateSupply x g A B a j k : ℝ) : ℂ) =
      (A : ℂ) * ((∑' k : ℤ, conj (complexSequence α g a k) * complexSequence α x a k) -
        (α ^ j : ℂ) * ∑' k : ℤ, conj (complexSequence α g a k) *
          complexSequence α x a (k - j)) +
      (B : ℂ) * ((timeWeight α j : ℂ) *
        (∑' k : ℤ, conj (complexSequence α g a k) * complexSequence α x a k) -
        (α ^ j : ℂ) * ∑' k : ℤ, conj (complexSequence α g a (k - j)) *
          complexSequence α x a k) := by
  have hxd : Summable (fun k ↦ timeWeight α k * coordinateSquare (zeroDelay x j k)) := by
    simpa only [coordinateSquare_zeroDelay, Function.comp_def] using
      (weighted_zeroDelay hx j).1
  have hgd : Summable (fun k ↦ timeWeight α k * coordinateSquare (zeroDelay g j k)) := by
    simpa only [coordinateSquare_zeroDelay, Function.comp_def] using
      (weighted_zeroDelay hg j).1
  have h₀ := summable_weighted_coordinate_pair hx hg a
  have h₁ := summable_weighted_coordinate_pair hxd hg a
  have h₂ := summable_weighted_coordinate_pair hxd hgd a
  have h₃ := summable_weighted_coordinate_pair hx hgd a
  have heq : (∑' k, timeWeight α k * lagCoordinateSupply x g A B a j k) =
      A * ((∑' k, timeWeight α k * g k a * x k a) -
        (∑' k, timeWeight α k * g k a * zeroDelay x j k a)) +
      B * ((∑' k, timeWeight α k * zeroDelay g j k a * zeroDelay x j k a) -
        (∑' k, timeWeight α k * zeroDelay g j k a * x k a)) := by
    calc
      _ = ∑' k, (A * (timeWeight α k * g k a * x k a -
          timeWeight α k * g k a * zeroDelay x j k a) +
        B * (timeWeight α k * zeroDelay g j k a * zeroDelay x j k a -
          timeWeight α k * zeroDelay g j k a * x k a)) := by
        apply tsum_congr
        intro k
        dsimp only [lagCoordinateSupply]
        ring
      _ = _ := by
        rw [((h₀.sub h₁).mul_left A).tsum_add ((h₂.sub h₃).mul_left B),
          tsum_mul_left, tsum_mul_left, h₀.tsum_sub h₁, h₂.tsum_sub h₃]
  rw [heq, weighted_both_delayed_pairing α x g hx hg a j]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub]
  rw [weighted_origin_pairing α x g hx hg a,
    weighted_delay_pairing α x g hx hg a j,
    weighted_reverse_pairing α x g hx hg a j]

/-- Summing the scalar formulas yields the full real coordinate pairing. -/
theorem weighted_lagSupply_eq_coordinate_totals {m : ℕ} (α : ℝ)
    (x g : ℕ → Fin m → ℝ)
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k)))
    (A B : ℝ) (j : ℕ) :
    (∑' k, timeWeight α k * lagSupply x g A B j k) =
      ∑ a : Fin m, ∑' k, timeWeight α k * lagCoordinateSupply x g A B a j k := by
  simp only [lagSupply_eq_sum, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun a _ ↦ summable_weighted_lagCoordinate hx hg A B a j)

/-- The origin dot-product pairing is the sum of its genuine bilateral
coordinate pairings. -/
theorem weighted_origin_dot_pairing {m : ℕ} (α : ℝ) (x g : ℕ → Fin m → ℝ)
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k))) :
    ((∑' k, timeWeight α k * dotProduct (g k) (x k) : ℝ) : ℂ) =
      ∑ a : Fin m, ∑' k : ℤ, conj (complexSequence α g a k) *
        complexSequence α x a k := by
  have heq : (∑' k, timeWeight α k * dotProduct (g k) (x k)) =
      ∑ a : Fin m, ∑' k, timeWeight α k * g k a * x k a := by
    simp only [dotProduct, Finset.mul_sum, ← mul_assoc]
    exact Summable.tsum_finsetSum (fun a _ ↦ summable_weighted_coordinate_pair hx hg a)
  rw [heq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact weighted_origin_pairing α x g hx hg a

end ADMM.UnitCircle.Supply
