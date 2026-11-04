/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_corollary_3_23
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_theorem_6_5

open IntersectionCut
open Filter
open scoped BigOperators Matrix

noncomputable section

section Theorem612RaySeparation

variable {p k : ℕ}

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: the `L1` discrepancy between
the first `p` coordinates of two ambient points. -/
def mixedPrefixL1Dist {n : ℕ} (hpn : p ≤ n) (x y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin p, |x (Fin.castLE hpn i) - y (Fin.castLE hpn i)|

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: the matrix whose columns are
the integer-prefix coordinates of the corner rays. -/
def prefixRayMatrix {n : ℕ} (hpn : p ≤ n) (rays : Fin k → Fin n → ℝ) :
    Matrix (Fin p) (Fin k) ℝ :=
  fun i j ↦ rays j (Fin.castLE hpn i)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: the equality-fiber right-hand
side corresponding to an integer prefix vector. -/
def prefixFiberRhs {n : ℕ} (hpn : p ≤ n) (xbar : Fin n → ℝ) (w : Fin p → ℤ) : Fin p → ℝ :=
  fun i ↦ (w i : ℝ) - xbar (Fin.castLE hpn i)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: the residual of the prefix
matrix fiber is the coordinate discrepancy from the associated integer vector. -/
lemma prefixRayMatrix_residual_apply {n : ℕ}
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (w : Fin p → ℤ)
    (s : Fin k → ℝ)
    (i : Fin p) :
    (prefixRayMatrix hpn rays *ᵥ s - prefixFiberRhs hpn xbar w) i =
      corner_point xbar rays s (Fin.castLE hpn i) - (w i : ℝ) := by
  -- Expand the matrix-vector product and collect the apex term.
  simp only [prefixRayMatrix, prefixFiberRhs, Matrix.mulVec, dotProduct, Pi.sub_apply,
    corner_point_def, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [mul_comm]
  ring

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: a dot product is bounded above
by the product of the coordinatewise `L1` sizes. -/
private lemma dotProduct_le_sumAbs_mul_sumAbs
    (v r : Fin p → ℝ) :
    |v ⬝ᵥ r| ≤ (∑ i : Fin p, |v i|) * ∑ i : Fin p, |r i| := by
  calc
    |v ⬝ᵥ r| ≤ ∑ i : Fin p, |v i * r i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin p, |v i| * |r i| := by simp only [abs_mul]
    _ ≤ ∑ i : Fin p, (∑ j : Fin p, |v j|) * |r i| := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ ↦ abs_nonneg (v j)) (Finset.mem_univ i))
        (abs_nonneg (r i))
    _ = (∑ i : Fin p, |v i|) * ∑ i : Fin p, |r i| := by
      rw [Finset.mul_sum]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: validity on one nonnegative
matrix fiber gives a nonnegative constant controlling inequality slack by the `L1` equality
residual, whether or not that fiber is feasible. -/
lemma existsNonnegativeFiberSlackBound
    (A : Matrix (Fin p) (Fin k) ℝ)
    (b : Fin p → ℝ)
    (a : Fin k → ℝ)
    (ha_nonneg : 0 ≤ a)
    (hvalid :
      ∀ s : Fin k → ℝ, 0 ≤ s → A *ᵥ s = b → 1 ≤ a ⬝ᵥ s) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ s : Fin k → ℝ, 0 ≤ s →
        1 - a ⬝ᵥ s ≤ K * ∑ i : Fin p, |(A *ᵥ s - b) i| := by
  classical
  by_cases hfiber : ∃ s : Fin k → ℝ, A *ᵥ s = b ∧ 0 ≤ s
  · rcases hfiber with ⟨s₀, hs₀eq, hs₀nonneg⟩
    let N : Matrix (Fin k) (Fin k) ℝ := -(1 : Matrix (Fin k) (Fin k) ℝ)
    have hP_nonempty :
        (mixed_constraint_polyhedron N 0 A b).Nonempty := by
      refine ⟨s₀, ?_⟩
      rw [mem_mixed_constraint_polyhedron]
      constructor
      · simpa [N, Matrix.neg_mulVec, Matrix.one_mulVec] using
          (neg_nonpos.mpr hs₀nonneg)
      · exact hs₀eq
    have hvalid_upper :
        is_valid_inequality (mixed_constraint_polyhedron N 0 A b) (-a) (-1) := by
      rw [is_valid_inequality_iff]
      intro s hs
      rw [mem_mixed_constraint_polyhedron] at hs
      have hs_nonneg : 0 ≤ s := by
        have hs_neg : -s ≤ 0 := by
          simpa [N, Matrix.neg_mulVec, Matrix.one_mulVec] using hs.1
        exact neg_nonpos.mp hs_neg
      have has := hvalid s hs_nonneg hs.2
      simpa [neg_dotProduct] using (neg_le_neg has)
    obtain ⟨u, v, hu_nonneg, hrow, hrhs⟩ :=
      (valid_inequality_iff_exists_mixed_row_multiplier
        N 0 A b (-a) (-1) hP_nonempty).mp hvalid_upper
    refine ⟨∑ i : Fin p, |v i|, Finset.sum_nonneg (fun i _ ↦ abs_nonneg (v i)), ?_⟩
    intro s hs_nonneg
    have hu_term_nonpos : u ⬝ᵥ (N *ᵥ s) ≤ 0 := by
      have hNmul : N *ᵥ s = -s := by
        simp [N, Matrix.neg_mulVec, Matrix.one_mulVec]
      rw [hNmul, dotProduct_neg]
      exact neg_nonpos.mpr (dotProduct_nonneg_of_nonneg hu_nonneg hs_nonneg)
    have hrow_eval :
        (-a) ⬝ᵥ s = u ⬝ᵥ (N *ᵥ s) + v ⬝ᵥ (A *ᵥ s) := by
      calc
        (-a) ⬝ᵥ s = (u ᵥ* N + v ᵥ* A) ⬝ᵥ s := by rw [hrow]
        _ = (u ᵥ* N) ⬝ᵥ s + (v ᵥ* A) ⬝ᵥ s := add_dotProduct _ _ _
        _ = u ⬝ᵥ (N *ᵥ s) + v ⬝ᵥ (A *ᵥ s) := by
          rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
    have hrhs' : v ⬝ᵥ b ≤ -1 := by simpa using hrhs
    have hslack_le : 1 - a ⬝ᵥ s ≤ v ⬝ᵥ (A *ᵥ s - b) := by
      rw [dotProduct_sub]
      rw [neg_dotProduct] at hrow_eval
      linarith
    exact hslack_le.trans <|
      (le_abs_self _).trans (dotProduct_le_sumAbs_mul_sumAbs v (A *ᵥ s - b))
  · have hnot_dual :
        ¬ ∀ v : Fin p → ℝ, v ᵥ* A ≤ 0 → v ⬝ᵥ b ≤ 0 := by
      intro hdual
      exact hfiber
        ((feasible_nonnegative_linear_system_iff_nonpositive_row_multipliers A b).mpr hdual)
    push Not at hnot_dual
    rcases hnot_dual with ⟨v, hvrow, hvb_pos⟩
    let K : ℝ := (v ⬝ᵥ b)⁻¹ * ∑ i : Fin p, |v i|
    have hK_nonneg : 0 ≤ K :=
      mul_nonneg (inv_nonneg.mpr hvb_pos.le) (Finset.sum_nonneg (fun i _ ↦ abs_nonneg (v i)))
    refine ⟨K, hK_nonneg, ?_⟩
    intro s hs_nonneg
    have hvAs_nonpos : v ⬝ᵥ (A *ᵥ s) ≤ 0 := by
      calc
        v ⬝ᵥ (A *ᵥ s) = (v ᵥ* A) ⬝ᵥ s := Matrix.dotProduct_mulVec _ _ _
        _ ≤ 0 ⬝ᵥ s := dotProduct_le_dotProduct_of_nonneg_right hvrow hs_nonneg
        _ = 0 := zero_dotProduct s
    have hvb_le_abs : v ⬝ᵥ b ≤ |v ⬝ᵥ (A *ᵥ s - b)| := by
      rw [dotProduct_sub]
      have hneg : v ⬝ᵥ (A *ᵥ s) - v ⬝ᵥ b < 0 := by linarith
      rw [abs_of_neg hneg]
      linarith
    have hvb_le_product :
        v ⬝ᵥ b ≤ (∑ i : Fin p, |v i|) * ∑ i : Fin p, |(A *ᵥ s - b) i| :=
      hvb_le_abs.trans (dotProduct_le_sumAbs_mul_sumAbs v (A *ᵥ s - b))
    have hone_le_product :
        1 ≤ K * ∑ i : Fin p, |(A *ᵥ s - b) i| := by
      have hscaled := mul_le_mul_of_nonneg_left hvb_le_product (inv_nonneg.mpr hvb_pos.le)
      simpa [K, hvb_pos.ne', mul_assoc] using hscaled
    have hadot_nonneg : 0 ≤ a ⬝ᵥ s :=
      dotProduct_nonneg_of_nonneg ha_nonneg hs_nonneg
    exact (sub_le_self 1 hadot_nonneg).trans hone_le_product

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: subtracting natural multiples
of positive lattice periods reduces every nonnegative coefficient vector to the period box while
preserving its prefix discrepancy from a suitably translated integer vector. -/
lemma existsPeriodReducedPrefixData {n : ℕ}
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (t : Fin k → ℝ)
    (ht : ∀ j : Fin k, 0 < t j)
    (htLattice : ∀ j : Fin k, t j • rays j ∈ mixed_integer_prefix_lattice hpn)
    (s : Fin k → ℝ)
    (hs_nonneg : 0 ≤ s)
    (z : Fin n → ℝ)
    (hzLattice : z ∈ mixed_integer_prefix_lattice hpn) :
    ∃ q : Fin k → ℝ, ∃ w : Fin p → ℤ,
      0 ≤ q ∧ q ≤ s ∧ (∀ j : Fin k, q j < t j) ∧
        mixedPrefixL1Dist hpn z (corner_point xbar rays s) =
          ∑ i : Fin p,
            |(prefixRayMatrix hpn rays *ᵥ q - prefixFiberRhs hpn xbar w) i| := by
  classical
  let m : Fin k → ℕ := fun j ↦ ⌊s j / t j⌋₊
  let q : Fin k → ℝ := fun j ↦ s j - (m j : ℝ) * t j
  rw [mem_mixed_integer_prefix_lattice_iff] at hzLattice
  have htLattice' :
      ∀ j : Fin k, ∀ i : Fin p,
        ∃ z : ℤ, (t j • rays j) (Fin.castLE hpn i) = (z : ℝ) :=
    fun j ↦ (mem_mixed_integer_prefix_lattice_iff hpn (t j • rays j)).mp (htLattice j)
  choose zInt hzInt using hzLattice
  choose periodInt hperiodInt using htLattice'
  let w : Fin p → ℤ :=
    fun i ↦ zInt i - ∑ j : Fin k, (m j : ℤ) * periodInt j i
  have hm_le (j : Fin k) : (m j : ℝ) * t j ≤ s j := by
    have hratio_nonneg : 0 ≤ s j / t j := div_nonneg (hs_nonneg j) (ht j).le
    exact (le_div_iff₀ (ht j)).mp (Nat.floor_le hratio_nonneg)
  have hq_nonneg : 0 ≤ q := by
    intro j
    exact sub_nonneg.mpr (hm_le j)
  have hq_le : q ≤ s := by
    intro j
    exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (ht j).le)
  have hq_lt (j : Fin k) : q j < t j := by
    have hratio_lt : s j / t j < (m j : ℝ) + 1 := Nat.lt_floor_add_one _
    have hs_lt : s j < ((m j : ℝ) + 1) * t j :=
      (div_lt_iff₀ (ht j)).mp hratio_lt
    dsimp only [q]
    nlinarith
  refine ⟨q, w, hq_nonneg, hq_le, hq_lt, ?_⟩
  unfold mixedPrefixL1Dist
  apply Finset.sum_congr rfl
  intro i hi
  rw [prefixRayMatrix_residual_apply]
  have hperiodCast (j : Fin k) :
      ((periodInt j i : ℤ) : ℝ) = t j * rays j (Fin.castLE hpn i) := by
    simpa [Pi.smul_apply, smul_eq_mul] using (hperiodInt j i).symm
  have hshiftCast :
      ((∑ j : Fin k, (m j : ℤ) * periodInt j i : ℤ) : ℝ) =
        ∑ j : Fin k, (m j : ℝ) * (t j * rays j (Fin.castLE hpn i)) := by
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hperiodCast]
  have hcornerSplit :
      corner_point xbar rays s (Fin.castLE hpn i) =
        corner_point xbar rays q (Fin.castLE hpn i) +
          ((∑ j : Fin k, (m j : ℤ) * periodInt j i : ℤ) : ℝ) := by
    simp only [corner_point_def, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hshiftCast]
    have hsumSplit :
        ∑ j : Fin k, s j * rays j (Fin.castLE hpn i) =
          (∑ j : Fin k, q j * rays j (Fin.castLE hpn i)) +
            ∑ j : Fin k, (m j : ℝ) * (t j * rays j (Fin.castLE hpn i)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [q]
      ring
    rw [hsumSplit]
    ring
  have hwCast :
      (w i : ℝ) = z (Fin.castLE hpn i) -
        ((∑ j : Fin k, (m j : ℤ) * periodInt j i : ℤ) : ℝ) := by
    rw [hzInt i]
    simp only [w, Int.cast_sub]
  rw [abs_sub_comm]
  congr 1
  rw [hcornerSplit, hwCast]
  ring

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: coefficients in a period box
give a uniform coordinatewise bound on their corner points. -/
lemma abs_prefix_cornerPoint_le_periodBoxBound {n : ℕ}
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (t q : Fin k → ℝ)
    (hq_nonneg : 0 ≤ q)
    (hq_le : q ≤ t)
    (i : Fin p) :
    |corner_point xbar rays q (Fin.castLE hpn i)| ≤
      |xbar (Fin.castLE hpn i)| +
        ∑ j : Fin k, t j * |rays j (Fin.castLE hpn i)| := by
  have hsum_abs :
      |∑ j : Fin k, q j * rays j (Fin.castLE hpn i)| ≤
        ∑ j : Fin k, |q j * rays j (Fin.castLE hpn i)| :=
    Finset.abs_sum_le_sum_abs _ _
  have hweighted :
      (∑ j : Fin k, |q j * rays j (Fin.castLE hpn i)|) ≤
        ∑ j : Fin k, t j * |rays j (Fin.castLE hpn i)| := by
    apply Finset.sum_le_sum
    intro j hj
    rw [abs_mul, abs_of_nonneg (hq_nonneg j)]
    exact mul_le_mul_of_nonneg_right (hq_le j) (abs_nonneg _)
  rw [corner_point_def]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact (abs_add_le _ _).trans
    (add_le_add (le_refl _) (hsum_abs.trans hweighted))

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: positive lattice periods and
normalized validity yield one prefix-distance penalty that separates every mixed-integer point
from every nonnegative corner representation. -/
lemma existsPeriodicPrefixSlackBound {n : ℕ}
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (t : Fin k → ℝ)
    (ht : ∀ j : Fin k, 0 < t j)
    (htLattice : ∀ j : Fin k, t j • rays j ∈ mixed_integer_prefix_lattice hpn)
    (a : Fin k → ℝ)
    (ha_nonneg : 0 ≤ a)
    (hvalid :
      ∀ ⦃s : Fin k → ℝ⦄,
        s ∈ corner_polyhedron hpn xbar rays → 1 ≤ a ⬝ᵥ s) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (s : Fin k → ℝ) (z : Fin n → ℝ),
        0 ≤ s → z ∈ mixed_integer_prefix_lattice hpn →
          1 ≤ a ⬝ᵥ s + κ * mixedPrefixL1Dist hpn z (corner_point xbar rays s) := by
  classical
  let bound : Fin p → ℤ := fun i ↦
    ⌈|xbar (Fin.castLE hpn i)| +
      (∑ j : Fin k, t j * |rays j (Fin.castLE hpn i)|) + 1⌉
  let W : Set (Fin p → ℤ) :=
    {w | ∀ i : Fin p, w i ∈ Set.Icc (-bound i) (bound i)}
  have hW_finite : W.Finite := by
    simpa [W, Set.pi] using
      (Set.Finite.pi (t := fun i : Fin p ↦ Set.Icc (-bound i) (bound i))
        fun i ↦ Set.finite_Icc (-bound i) (bound i))
  have hfiberBound :
      ∀ w : Fin p → ℤ, ∃ K : ℝ, 0 ≤ K ∧
        ∀ s : Fin k → ℝ, 0 ≤ s →
          1 - a ⬝ᵥ s ≤
            K * ∑ i : Fin p,
              |(prefixRayMatrix hpn rays *ᵥ s - prefixFiberRhs hpn xbar w) i| := by
    intro w
    apply existsNonnegativeFiberSlackBound (prefixRayMatrix hpn rays)
      (prefixFiberRhs hpn xbar w) a ha_nonneg
    intro s hs_nonneg hsFiber
    apply hvalid
    rw [mem_corner_polyhedron_iff]
    refine ⟨hs_nonneg, ?_⟩
    rw [mem_mixed_integer_prefix_lattice_iff]
    intro i
    refine ⟨w i, ?_⟩
    have hresidual :
        (prefixRayMatrix hpn rays *ᵥ s - prefixFiberRhs hpn xbar w) i = 0 := by
      rw [hsFiber]
      simp
    rw [prefixRayMatrix_residual_apply] at hresidual
    exact sub_eq_zero.mp hresidual
  choose K hK_nonneg hK_bound using hfiberBound
  let κ : ℝ := 1 + ∑ w ∈ hW_finite.toFinset, K w
  have hκ_pos : 0 < κ := by
    have hsum_nonneg : 0 ≤ ∑ w ∈ hW_finite.toFinset, K w := by
      exact Finset.sum_nonneg fun w hw ↦ hK_nonneg w
    dsimp only [κ]
    linarith
  refine ⟨κ, hκ_pos, ?_⟩
  intro s z hs_nonneg hzLattice
  obtain ⟨q, w, hq_nonneg, hq_le_s, hq_lt_t, hdist⟩ :=
    existsPeriodReducedPrefixData hpn xbar rays t ht htLattice s hs_nonneg z hzLattice
  have hq_le_t : q ≤ t := fun j ↦ (hq_lt_t j).le
  have ha_q_le_s : a ⬝ᵥ q ≤ a ⬝ᵥ s :=
    dotProduct_le_dotProduct_of_nonneg_left hq_le_s ha_nonneg
  have hdist_nonneg : 0 ≤ mixedPrefixL1Dist hpn z (corner_point xbar rays s) := by
    unfold mixedPrefixL1Dist
    exact Finset.sum_nonneg fun i hi ↦ abs_nonneg _
  have hκ_one : 1 ≤ κ := by
    have hsum_nonneg : 0 ≤ ∑ w ∈ hW_finite.toFinset, K w := by
      exact Finset.sum_nonneg fun w hw ↦ hK_nonneg w
    dsimp only [κ]
    linarith
  by_cases hdist_large : 1 ≤ mixedPrefixL1Dist hpn z (corner_point xbar rays s)
  · have hadot_nonneg : 0 ≤ a ⬝ᵥ s :=
      dotProduct_nonneg_of_nonneg ha_nonneg hs_nonneg
    nlinarith
  · have hdist_lt : mixedPrefixL1Dist hpn z (corner_point xbar rays s) < 1 :=
      lt_of_not_ge hdist_large
    have hw_mem : w ∈ W := by
      intro i
      have hcoordinate_le_sum :
          |(prefixRayMatrix hpn rays *ᵥ q - prefixFiberRhs hpn xbar w) i| ≤
            ∑ l : Fin p,
              |(prefixRayMatrix hpn rays *ᵥ q - prefixFiberRhs hpn xbar w) l| :=
        Finset.single_le_sum
          (fun l _ ↦ abs_nonneg
            ((prefixRayMatrix hpn rays *ᵥ q - prefixFiberRhs hpn xbar w) l))
          (Finset.mem_univ i)
      have hresidual_lt :
          |corner_point xbar rays q (Fin.castLE hpn i) - (w i : ℝ)| < 1 := by
        rw [← prefixRayMatrix_residual_apply]
        exact hcoordinate_le_sum.trans_lt (hdist ▸ hdist_lt)
      have hcorner_bound :=
        abs_prefix_cornerPoint_le_periodBoxBound hpn xbar rays t q hq_nonneg hq_le_t i
      have hw_abs_lt :
          |(w i : ℝ)| <
            |xbar (Fin.castLE hpn i)| +
              (∑ j : Fin k, t j * |rays j (Fin.castLE hpn i)|) + 1 := by
        calc
          |(w i : ℝ)| ≤
              |corner_point xbar rays q (Fin.castLE hpn i)| +
                |(w i : ℝ) - corner_point xbar rays q (Fin.castLE hpn i)| := by
            simpa [add_comm] using
              (abs_add_le (corner_point xbar rays q (Fin.castLE hpn i))
                ((w i : ℝ) - corner_point xbar rays q (Fin.castLE hpn i)))
          _ <
              |xbar (Fin.castLE hpn i)| +
                (∑ j : Fin k, t j * |rays j (Fin.castLE hpn i)|) + 1 := by
            rw [abs_sub_comm]
            linarith
      have hw_abs_le_bound : |(w i : ℝ)| ≤ (bound i : ℝ) :=
        hw_abs_lt.le.trans (Int.le_ceil _)
      constructor
      · exact_mod_cast (neg_le_of_abs_le hw_abs_le_bound)
      · exact_mod_cast (le_of_abs_le hw_abs_le_bound)
    have hw_finset : w ∈ hW_finite.toFinset := by simpa using hw_mem
    have hK_le_sum : K w ≤ ∑ v ∈ hW_finite.toFinset, K v := by
      exact Finset.single_le_sum
        (fun v hv ↦ hK_nonneg v)
        hw_finset
    have hK_le_κ : K w ≤ κ := by
      dsimp only [κ]
      linarith
    have hlocal := hK_bound w q hq_nonneg
    rw [← hdist] at hlocal
    have hpenalty :
        K w * mixedPrefixL1Dist hpn z (corner_point xbar rays s) ≤
          κ * mixedPrefixL1Dist hpn z (corner_point xbar rays s) :=
      mul_le_mul_of_nonneg_right hK_le_κ hdist_nonneg
    linarith

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: prefix `L1` discrepancy is
convex under simultaneous convex combinations of its two arguments. -/
lemma mixedPrefixL1Dist_convexCombo {n : ℕ}
    (hpn : p ≤ n)
    (x y u v : Fin n → ℝ)
    (c d : ℝ)
    (hc : 0 ≤ c)
    (hd : 0 ≤ d) :
    mixedPrefixL1Dist hpn (c • x + d • y) (c • u + d • v) ≤
      c * mixedPrefixL1Dist hpn x u + d * mixedPrefixL1Dist hpn y v := by
  -- Apply the scalar triangle inequality coordinatewise and then sum it over the prefix.
  unfold mixedPrefixL1Dist
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hcoordinate :
      c * x (Fin.castLE hpn i) + d * y (Fin.castLE hpn i) -
          (c * u (Fin.castLE hpn i) + d * v (Fin.castLE hpn i)) =
        c * (x (Fin.castLE hpn i) - u (Fin.castLE hpn i)) +
          d * (y (Fin.castLE hpn i) - v (Fin.castLE hpn i)) := by
    ring
  rw [hcoordinate]
  calc
    |c * (x (Fin.castLE hpn i) - u (Fin.castLE hpn i)) +
        d * (y (Fin.castLE hpn i) - v (Fin.castLE hpn i))| ≤
        |c * (x (Fin.castLE hpn i) - u (Fin.castLE hpn i))| +
          |d * (y (Fin.castLE hpn i) - v (Fin.castLE hpn i))| := abs_add_le _ _
    _ = c * |x (Fin.castLE hpn i) - u (Fin.castLE hpn i)| +
          d * |y (Fin.castLE hpn i) - v (Fin.castLE hpn i)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hd]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: the corner-point map preserves
convex combinations of coefficient vectors. -/
lemma cornerPoint_convexCombo {n : ℕ}
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (s q : Fin k → ℝ)
    (c d : ℝ)
    (hcd : c + d = 1) :
    corner_point xbar rays (c • s + d • q) =
      c • corner_point xbar rays s + d • corner_point xbar rays q := by
  -- Expand the affine ray map; `c + d = 1` supplies the apex coefficient.
  ext i
  simp only [corner_point_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
    add_mul, Finset.sum_add_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hxbar : xbar i = c * xbar i + d * xbar i := by
    calc
      xbar i = (c + d) * xbar i := by rw [hcd]; simp
      _ = c * xbar i + d * xbar i := by ring
  nth_rewrite 1 [hxbar]
  ring

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: the open prefix tube consists
of points admitting a nonnegative corner representation whose normalized slack dominates the
prefix discrepancy. -/
def periodicPrefixTube {n : ℕ}
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (a : Fin k → ℝ)
    (κ : ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ s : Fin k → ℝ,
    0 ≤ s ∧ a ⬝ᵥ s + κ * mixedPrefixL1Dist hpn x (corner_point xbar rays s) < 1}

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: the prefix discrepancy from a
fixed ambient point varies continuously. -/
lemma continuous_mixedPrefixL1Dist_left {n : ℕ}
    (hpn : p ≤ n)
    (y : Fin n → ℝ) :
    Continuous fun x : Fin n → ℝ ↦ mixedPrefixL1Dist hpn x y := by
  -- Each summand is the absolute value of a continuous coordinate difference.
  unfold mixedPrefixL1Dist
  refine continuous_finsetSum Finset.univ ?_
  intro i hi
  exact ((continuous_apply (Fin.castLE hpn i)).sub continuous_const).abs

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: every periodic prefix tube is
open. -/
lemma isOpen_periodicPrefixTube {n : ℕ}
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (a : Fin k → ℝ)
    (κ : ℝ) :
    IsOpen (periodicPrefixTube hpn xbar rays a κ) := by
  -- Fixing a witness exposes an open strict sublevel set contained in the whole tube.
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hx with ⟨s, hs_nonneg, hs_lt⟩
  have hcontinuous : Continuous fun y : Fin n → ℝ ↦
      a ⬝ᵥ s + κ * mixedPrefixL1Dist hpn y (corner_point xbar rays s) :=
    continuous_const.add
      (continuous_const.mul (continuous_mixedPrefixL1Dist_left hpn (corner_point xbar rays s)))
  have hopen : IsOpen {y : Fin n → ℝ |
      a ⬝ᵥ s + κ * mixedPrefixL1Dist hpn y (corner_point xbar rays s) < 1} :=
    isOpen_lt hcontinuous continuous_const
  apply Filter.mem_of_superset (hopen.mem_nhds hs_lt)
  intro y hy
  exact ⟨s, hs_nonneg, hy⟩

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: a tube with nonnegative prefix
penalty is convex. -/
lemma convex_periodicPrefixTube {n : ℕ}
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (a : Fin k → ℝ)
    (κ : ℝ)
    (hκ_nonneg : 0 ≤ κ) :
    Convex ℝ (periodicPrefixTube hpn xbar rays a κ) := by
  intro x hx y hy c d hc hd hcd
  rcases hx with ⟨s, hs_nonneg, hs_lt⟩
  rcases hy with ⟨q, hq_nonneg, hq_lt⟩
  refine ⟨c • s + d • q, ?_, ?_⟩
  · -- Convex combinations preserve coefficientwise nonnegativity.
    intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hc (hs_nonneg j)) (mul_nonneg hd (hq_nonneg j))
  · -- Combine affine linearity of the corner map with convexity of the prefix `L1` penalty.
    have hdist := mixedPrefixL1Dist_convexCombo hpn x y
      (corner_point xbar rays s) (corner_point xbar rays q) c d hc hd
    rw [← cornerPoint_convexCombo xbar rays s q c d hcd] at hdist
    have hdist_scaled := mul_le_mul_of_nonneg_left hdist hκ_nonneg
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
    simp only [smul_eq_mul]
    have hweighted :
        c * (a ⬝ᵥ s + κ * mixedPrefixL1Dist hpn x (corner_point xbar rays s)) +
            d * (a ⬝ᵥ q + κ * mixedPrefixL1Dist hpn y (corner_point xbar rays q)) < 1 := by
      by_cases hc_zero : c = 0
      · subst c
        have hd_one : d = 1 := by linarith
        subst d
        simpa using hq_lt
      · have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc_zero)
        have hs_weighted := mul_lt_mul_of_pos_left hs_lt hc_pos
        have hq_weighted := mul_le_mul_of_nonneg_left hq_lt.le hd
        nlinarith
    have hobjective_le :
        c * (a ⬝ᵥ s) + d * (a ⬝ᵥ q) +
            κ * mixedPrefixL1Dist hpn (c • x + d • y)
              (corner_point xbar rays (c • s + d • q)) ≤
          c * (a ⬝ᵥ s + κ * mixedPrefixL1Dist hpn x (corner_point xbar rays s)) +
            d * (a ⬝ᵥ q + κ * mixedPrefixL1Dist hpn y (corner_point xbar rays q)) := by
      nlinarith
    exact hobjective_le.trans_lt hweighted

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: the affine corner-point map is
continuous in its coefficient vector. -/
lemma continuous_cornerPoint {n : ℕ}
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ) :
    Continuous (corner_point xbar rays) := by
  -- Express the ray combination as a finite sum of continuous scalar multiples.
  unfold corner_point
  apply continuous_const.add
  refine continuous_finsetSum Finset.univ ?_
  intro j hj
  exact (continuous_apply j).smul continuous_const

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: the apex belongs to every
periodic prefix tube. -/
lemma apex_mem_periodicPrefixTube {n : ℕ}
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (a : Fin k → ℝ)
    (κ : ℝ) :
    xbar ∈ periodicPrefixTube hpn xbar rays a κ := by
  -- Use the zero coefficient vector, whose corner point is exactly the apex.
  refine ⟨0, fun j ↦ le_rfl, ?_⟩
  simp [mixedPrefixL1Dist, corner_point_def]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: every corner point in the
closed normalized coefficient sublevel lies in the closure of the periodic prefix tube. -/
lemma cornerPoint_mem_closure_periodicPrefixTube {n : ℕ}
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (a : Fin k → ℝ)
    (κ : ℝ)
    (ha_nonneg : 0 ≤ a)
    (s : Fin k → ℝ)
    (hs_nonneg : 0 ≤ s)
    (hs_sublevel : a ⬝ᵥ s ≤ 1) :
    corner_point xbar rays s ∈ closure (periodicPrefixTube hpn xbar rays a κ) := by
  -- Contract the coefficients by factors tending upward to one; every contraction has strict
  -- normalized slack and its corner point converges to the desired boundary point.
  let c : ℕ → ℝ := fun m ↦ 1 - 1 / ((m : ℝ) + 1)
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun m ↦ corner_point xbar rays (c m • s), ?_, ?_⟩
  · intro m
    have hden_pos : 0 < (m : ℝ) + 1 := by positivity
    have hc_nonneg : 0 ≤ c m := by
      have hc_eq : c m = (m : ℝ) / ((m : ℝ) + 1) := by
        dsimp only [c]
        field_simp
        ring
      rw [hc_eq]
      exact div_nonneg (Nat.cast_nonneg m) hden_pos.le
    have hc_lt : c m < 1 := by
      have hinv_pos : 0 < 1 / ((m : ℝ) + 1) := one_div_pos.mpr hden_pos
      dsimp only [c]
      linarith
    have hadot_nonneg : 0 ≤ a ⬝ᵥ s :=
      dotProduct_nonneg_of_nonneg ha_nonneg hs_nonneg
    have hscaled_lt : c m * (a ⬝ᵥ s) < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left hc_nonneg hc_lt hs_sublevel
    refine ⟨c m • s, ?_, ?_⟩
    · intro j
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg hc_nonneg (hs_nonneg j)
    · rw [dotProduct_smul]
      simp only [mixedPrefixL1Dist, sub_self, abs_zero, Finset.sum_const_zero, mul_zero,
        add_zero, smul_eq_mul]
      exact hscaled_lt
  · have hzero :
        Tendsto (fun m : ℕ ↦ (1 : ℝ) / ((m : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc_tendsto : Tendsto c Filter.atTop (nhds 1) := by
      have hone : Tendsto (fun _m : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds 1) :=
        tendsto_const_nhds
      simpa [c] using hone.sub hzero
    have hcoeff_tendsto :
        Tendsto (fun m ↦ c m • s) Filter.atTop (nhds s) := by
      simpa using hc_tendsto.smul (tendsto_const_nhds : Tendsto (fun _m : ℕ ↦ s)
        Filter.atTop (nhds s))
    exact (continuous_cornerPoint xbar rays).continuousAt.tendsto.comp hcoeff_tendsto

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: an open nonempty convex set is
the interior of its closure. -/
private lemma interior_closure_eq_self_of_open_convex {n : ℕ}
    (T : Set (Fin n → ℝ))
    (hopen : IsOpen T)
    (hconvex : Convex ℝ T)
    (hne : T.Nonempty) :
    interior (closure T) = T := by
  -- Openness first turns the supplied point into a point of the interior.
  have hinterior_nonempty : (interior T).Nonempty := by
    rw [hopen.interior_eq]
    exact hne
  -- Convexity preserves that interior on taking the closure, and openness identifies it with `T`.
  calc
    interior (closure T) = interior T :=
      hconvex.interior_closure_eq_interior_of_nonempty_interior hinterior_nonempty
    _ = T := hopen.interior_eq

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12/RaySeparation.lean

The closure of a separated
periodic prefix tube is a closed convex mixed-integer-free witness containing the full normalized
corner sublevel. -/
lemma closedPeriodicPrefixTubeWitness {n : ℕ}
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (a : Fin k → ℝ)
    (κ : ℝ)
    (hκ_pos : 0 < κ)
    (ha_nonneg : 0 ≤ a)
    (hseparate :
      ∀ (s : Fin k → ℝ) (z : Fin n → ℝ),
        0 ≤ s → z ∈ mixed_integer_prefix_lattice hpn →
          1 ≤ a ⬝ᵥ s + κ * mixedPrefixL1Dist hpn z (corner_point xbar rays s)) :
    IsClosed (closure (periodicPrefixTube hpn xbar rays a κ)) ∧
      Convex ℝ (closure (periodicPrefixTube hpn xbar rays a κ)) ∧
        xbar ∈ interior (closure (periodicPrefixTube hpn xbar rays a κ)) ∧
          Disjoint
            (interior (closure (periodicPrefixTube hpn xbar rays a κ)))
            (mixed_integer_prefix_lattice hpn) ∧
            ∀ (s : Fin k → ℝ), 0 ≤ s → a ⬝ᵥ s ≤ 1 →
              corner_point xbar rays s ∈ closure (periodicPrefixTube hpn xbar rays a κ) := by
  let T := periodicPrefixTube hpn xbar rays a κ
  have hopen : IsOpen T := by
    simpa [T] using isOpen_periodicPrefixTube hpn xbar rays a κ
  have hconvex : Convex ℝ T := by
    simpa [T] using convex_periodicPrefixTube hpn xbar rays a κ hκ_pos.le
  have hapex : xbar ∈ T := by
    simpa [T] using apex_mem_periodicPrefixTube hpn xbar rays a κ
  -- The generic open-convex closure lemma supplies the stable normal form for the remaining goals.
  have hinterior_closure : interior (closure T) = T := by
    exact interior_closure_eq_self_of_open_convex T hopen hconvex ⟨xbar, hapex⟩
  refine ⟨isClosed_closure, hconvex.closure, ?_, ?_, ?_⟩
  · -- The tube is precisely the interior of its closure, so the apex stays interior.
    rw [hinterior_closure]
    exact hapex
  · -- The strict separation estimate excludes every mixed-integer point from the tube.
    rw [hinterior_closure, Set.disjoint_left]
    intro z hzTube hzLattice
    rcases hzTube with ⟨s, hs_nonneg, hs_lt⟩
    exact (not_lt_of_ge (hseparate s z hs_nonneg hzLattice)) hs_lt
  · intro s hs_nonneg hs_sublevel
    simpa [T] using
      cornerPoint_mem_closure_periodicPrefixTube
        hpn xbar rays a κ ha_nonneg s hs_nonneg hs_sublevel

#print axioms closedPeriodicPrefixTubeWitness

end Theorem612RaySeparation
