/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.DiscountedProx
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Supply.Bilateral

@[expose] public section

open scoped BigOperators ENNReal
open ADMM.ConvergenceProof

namespace ADMM.UnitCircle.Causal

/-- Standard squared norm identity for Hilbert sequence space. -/
theorem lp_norm_sq {ι E : Type*} [NormedAddCommGroup E]
    (v : lp (fun _ : ι ↦ E) 2) : ‖v‖ ^ 2 = ∑' k, ‖v k‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) v

theorem block_square_eq {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    coordinateSquare (WithLp.ofLp x) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [coordinateSquare, dotProduct, pow_two]

theorem block_square_summable {m : ℕ} (v : ℕ → BlockVector m) (hv : Memℓp v 2)
    (b : Fin 2) : Summable (fun k ↦ coordinateSquare (WithLp.ofLp (v k b))) := by
  have hs : Summable (fun k ↦ ‖v k‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hv.summable (by norm_num)
  apply Summable.of_nonneg_of_le (fun k ↦ coordinateSquare_nonneg _) (fun k ↦ ?_) hs
  rw [block_square_eq]
  have h := norm_le_pi_norm (v k) b
  nlinarith [norm_nonneg (v k b), norm_nonneg (v k)]

/-- One coordinate of an already discounted real vector sequence, extended
by zero to bilateral complex Hilbert sequence space. -/
noncomputable def coordinateLp {m : ℕ} (v : ℕ → BlockVector m) (hv : Memℓp v 2)
    (b : Fin 2) (a : Fin m) : lp (fun _ : ℤ ↦ ℂ) 2 :=
  Supply.complexLp 1 (fun k ↦ WithLp.ofLp (v k b))
    (by simpa [Supply.timeWeight] using block_square_summable v hv b) a

@[simp] theorem coordinateLp_nat {m : ℕ} (v : ℕ → BlockVector m) (hv : Memℓp v 2)
    (b : Fin 2) (a : Fin m) (k : ℕ) : coordinateLp v hv b a k = (v k b a : ℂ) := by
  simp [coordinateLp]

@[simp] theorem coordinateLp_negSucc {m : ℕ} (v : ℕ → BlockVector m) (hv : Memℓp v 2)
    (b : Fin 2) (a : Fin m) (k : ℕ) :
    coordinateLp v hv b a (-(k + 1 : ℤ)) = 0 :=
  Supply.complexSequence_negSucc 1 (fun j ↦ WithLp.ofLp (v j b)) a k

theorem coordinate_square_summable {m : ℕ} (v : ℕ → BlockVector m) (hv : Memℓp v 2)
    (b : Fin 2) (a : Fin m) : Summable (fun k ↦ (v k b a) ^ 2) := by
  have h := Supply.summable_weighted_coordinate
    (α := 1) (x := fun k ↦ WithLp.ofLp (v k b))
    (by simpa [Supply.timeWeight] using block_square_summable v hv b) a
  simpa [Supply.timeWeight] using h

/-- Complexification and zero extension preserve each coordinate's norm. -/
theorem coordinateLp_norm_sq {m : ℕ} (v : ℕ → BlockVector m) (hv : Memℓp v 2)
    (b : Fin 2) (a : Fin m) :
    ‖coordinateLp v hv b a‖ ^ 2 = ∑' k : ℕ, (v k b a) ^ 2 := by
  rw [lp_norm_sq]
  have heq : (fun k : ℤ ↦ ‖coordinateLp v hv b a k‖ ^ 2) =
      Supply.extendZero (fun k : ℕ ↦ (v k b a) ^ 2) := by
    funext k
    cases k with
    | ofNat k => simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    | negSucc k =>
      change ‖coordinateLp v hv b a (-(k + 1 : ℤ))‖ ^ 2 =
        Supply.extendZero (fun j : ℕ ↦ (v j b a) ^ 2) (-(k + 1 : ℤ))
      rw [coordinateLp_negSucc, Supply.extendZero_negSucc]
      norm_num
  rw [heq, Supply.tsum_extendZero (coordinate_square_summable v hv b a)]

/-- Sum of scalar-coordinate Fourier energies equals the block energy. -/
theorem coordinateLp_block_energy {m : ℕ} (v : ℕ → BlockVector m) (hv : Memℓp v 2)
    (b : Fin 2) :
    (∑ a : Fin m, ‖coordinateLp v hv b a‖ ^ 2) = ∑' k : ℕ, ‖v k b‖ ^ 2 := by
  simp only [coordinateLp_norm_sq]
  rw [← Summable.tsum_finsetSum (fun a _ ↦ coordinate_square_summable v hv b a)]
  congr 1
  funext k
  exact (EuclideanSpace.real_norm_sq_eq (v k b)).symm

noncomputable def coordinateEnergy {m : ℕ} (v : ℕ → BlockVector m) (hv : Memℓp v 2) : ℝ :=
  ∑ b : Fin 2, ∑ a : Fin m, ‖coordinateLp v hv b a‖ ^ 2

theorem coordinateEnergy_eq {m : ℕ} (v : ℕ → BlockVector m) (hv : Memℓp v 2) :
    coordinateEnergy v hv = ∑' k : ℕ, (‖v k 0‖ ^ 2 + ‖v k 1‖ ^ 2) := by
  simp only [coordinateEnergy, Fin.sum_univ_two, coordinateLp_block_energy]
  have h0 : Summable (fun k ↦ ‖v k 0‖ ^ 2) := by
    simpa only [block_square_eq] using block_square_summable v hv 0
  have h1 : Summable (fun k ↦ ‖v k 1‖ ^ 2) := by
    simpa only [block_square_eq] using block_square_summable v hv 1
  exact (h0.tsum_add h1).symm

/-- Precise comparison between the temporal maximum-block norm and the
coordinate Hilbert energy used in Parseval and Cauchy--Schwarz. -/
theorem coordinateEnergy_bounds {m : ℕ} (v : ℕ → BlockVector m) (hv : Memℓp v 2) :
    ‖(⟨v, hv⟩ : lp (fun _ : ℕ ↦ BlockVector m) 2)‖ ^ 2 ≤ coordinateEnergy v hv ∧
      coordinateEnergy v hv ≤ 2 * ‖(⟨v, hv⟩ : lp (fun _ : ℕ ↦ BlockVector m) 2)‖ ^ 2 := by
  have hfull : Summable (fun k ↦ ‖v k‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hv.summable (by norm_num)
  have h0 : Summable (fun k ↦ ‖v k 0‖ ^ 2) := by
    simpa only [block_square_eq] using block_square_summable v hv 0
  have h1 : Summable (fun k ↦ ‖v k 1‖ ^ 2) := by
    simpa only [block_square_eq] using block_square_summable v hv 1
  rw [coordinateEnergy_eq, lp_norm_sq]
  constructor
  · apply hfull.tsum_le_tsum (fun k ↦ ?_) (h0.add h1)
    by_cases h : ‖v k 0‖ ≤ ‖v k 1‖
    · have hnorm : ‖v k‖ ≤ ‖v k 1‖ := by
        apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
        intro b
        fin_cases b
        · exact h
        · exact le_rfl
      nlinarith [norm_nonneg (v k), norm_nonneg (v k 1), sq_nonneg ‖v k 0‖]
    · have hnorm : ‖v k‖ ≤ ‖v k 0‖ := by
        apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
        intro b
        fin_cases b
        · exact le_rfl
        · exact le_of_not_ge h
      nlinarith [norm_nonneg (v k), norm_nonneg (v k 0), sq_nonneg ‖v k 1‖]
  · rw [← tsum_mul_left]
    apply (h0.add h1).tsum_le_tsum (fun k ↦ ?_) (hfull.mul_left 2)
    have ha := norm_le_pi_norm (v k) 0
    have hb := norm_le_pi_norm (v k) 1
    nlinarith [norm_nonneg (v k 0), norm_nonneg (v k 1), norm_nonneg (v k)]

/-- Convenient norm comparison for the disturbance estimate; the harmless
factor two avoids introducing an irrational constant into the final bound. -/
theorem coordinateEnergy_sqrt_bounds {m : ℕ} (v : ℕ → BlockVector m) (hv : Memℓp v 2) :
    ‖(⟨v, hv⟩ : lp (fun _ : ℕ ↦ BlockVector m) 2)‖ ≤ √(coordinateEnergy v hv) ∧
      √(coordinateEnergy v hv) ≤ 2 * ‖(⟨v, hv⟩ : lp (fun _ : ℕ ↦ BlockVector m) 2)‖ := by
  have h := coordinateEnergy_bounds v hv
  have he : 0 ≤ coordinateEnergy v hv := (sq_nonneg _).trans h.1
  have hs := Real.sq_sqrt he
  constructor <;> nlinarith [Real.sqrt_nonneg (coordinateEnergy v hv),
    norm_nonneg (⟨v, hv⟩ : lp (fun _ : ℕ ↦ BlockVector m) 2)]

end ADMM.UnitCircle.Causal
