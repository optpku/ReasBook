/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Supply.CoordinatePairing
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Fourier.LagOperator

@[expose] public section

open scoped BigOperators ComplexConjugate
open ADMM.ConvergenceProof

namespace ADMM.UnitCircle.Supply

/-- Bilateral translation transfers a delay from the normal to the point
with the opposite sign. This is the adjoint relation used by the reverse lag. -/
theorem delay_inner_swap (j : ℤ) (G X : Fourier.TimeSequence) :
    inner ℂ (Fourier.delay j G) X = inner ℂ G (Fourier.delay (-j) X) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [RCLike.inner_apply', Fourier.delay_apply]
  have heq := (Equiv.addRight j).tsum_eq (fun k : ℤ ↦ conj (G (k - j)) * X k)
  change (∑' k : ℤ, conj (G (k + j - j)) * X (k + j)) =
    (∑' k : ℤ, conj (G (k - j)) * X k) at heq
  rw [← heq]
  apply tsum_congr
  intro k
  simp only [add_sub_cancel_right, sub_neg_eq_add]

/-- A scalar lag supply is precisely the Hilbert pairing with the manuscript's
finite lag operator term, including the forward comparison. -/
theorem weighted_lagTerm_inner {m ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2)
    (α : ℝ) (x g : ℕ → Fin m → ℝ)
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k)))
    (a : Fin m) (i : Fin ℓ) :
    ((∑' k, timeWeight α k * lagCoordinateSupply x g
      (c.backward b i) (c.forward b i) a (i.val + 1) k : ℝ) : ℂ) =
      inner ℂ (complexLp α g hg a) (Fourier.lagTerm c α b i (complexLp α x hx a)) := by
  rw [weighted_lagCoordinate_pairing α x g hx hg]
  simp only [Fourier.lagTerm, Fourier.backwardDifference, Fourier.forwardDifference,
    inner_add_right, inner_sub_right, inner_smul_right]
  rw [← delay_inner_swap ((i.val + 1 : ℕ) : ℤ)]
  simp only [lp.inner_eq_tsum, RCLike.inner_apply', complexLp_apply, Fourier.delay_apply,
    timeWeight, Complex.ofReal_pow]

/-- The weighted vector lag is the sum of genuine Hilbert pairings over the
physical coordinates. -/
theorem weighted_lagSupply_inner {m ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2)
    (α : ℝ) (x g : ℕ → Fin m → ℝ)
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k))) (i : Fin ℓ) :
    ((∑' k, timeWeight α k * lagSupply x g
      (c.backward b i) (c.forward b i) (i.val + 1) k : ℝ) : ℂ) =
      ∑ a : Fin m, inner ℂ (complexLp α g hg a)
        (Fourier.lagTerm c α b i (complexLp α x hx a)) := by
  rw [weighted_lagSupply_eq_coordinate_totals α x g hx hg, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact weighted_lagTerm_inner c b α x g hx hg a i

/-- Exact interchange of the finite lag list and the absolutely convergent
time sum. -/
theorem weighted_blockSupply_eq_totals {m ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2)
    (α : ℝ) (x g : ℕ → Fin m → ℝ)
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k))) :
    (∑' k, timeWeight α k * blockSupply c b x g k) =
      c.omega * (∑' k, timeWeight α k * dotProduct (g k) (x k)) +
      ∑ i : Fin ℓ, ∑' k, timeWeight α k *
        lagSupply x g (c.backward b i) (c.forward b i) (i.val + 1) k := by
  have hp := summable_weighted_dot hg hx
  have hl : ∀ i : Fin ℓ, Summable (fun k ↦ timeWeight α k *
      lagSupply x g (c.backward b i) (c.forward b i) (i.val + 1) k) :=
    fun i ↦ summable_weighted_lagSupply hx hg _ _ _
  have hsum := summable_sum (s := Finset.univ) (fun i _ ↦ hl i)
  calc
    _ = ∑' k, (c.omega * (timeWeight α k * dotProduct (g k) (x k)) +
        ∑ i : Fin ℓ, timeWeight α k *
          lagSupply x g (c.backward b i) (c.forward b i) (i.val + 1) k) := by
      apply tsum_congr
      intro k
      simp only [blockSupply, mul_add, Finset.mul_sum]
      ring
    _ = _ := by
      rw [(hp.mul_left c.omega).tsum_add hsum, tsum_mul_left,
        Summable.tsum_finsetSum (fun i _ ↦ hl i)]

/-- The real convex supply and the exact bilateral Fourier lag operator have
identical pairings. No frequency inequality is used in this bridge. -/
theorem weighted_blockSupply_inner {m ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2)
    (α : ℝ) (x g : ℕ → Fin m → ℝ)
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k))) :
    ((∑' k, timeWeight α k * blockSupply c b x g k : ℝ) : ℂ) =
      ∑ a : Fin m, inner ℂ (complexLp α g hg a)
        (Fourier.lagOperator c α b (complexLp α x hx a)) := by
  rw [weighted_blockSupply_eq_totals c b α x g hx hg]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sum]
  rw [weighted_origin_dot_pairing α x g hx hg]
  simp only [weighted_lagSupply_inner c b α x g hx hg]
  simp only [Fourier.lagOperator, inner_add_right, inner_smul_right, inner_sum,
    Finset.sum_add_distrib, Finset.mul_sum, lp.inner_eq_tsum, RCLike.inner_apply',
    complexLp_apply]
  rw [Finset.sum_comm]

end ADMM.UnitCircle.Supply
