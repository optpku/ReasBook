/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_11
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_8
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open WithLp (toLp)

noncomputable section

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

local notation "Δ" => stdSimplex ℝ ι
local notation "E" => EuclideanSpace ℝ ι

/- Lemma 6.69 is `source-facing` in the simplex variational formula for the squared `ℓ¹` norm.
The owner-level domain sampling for this file is:

1. `quadratic_over_linear` from Definition 6.11, with notation `φ`, is the chapter's
   `core/canonical` scalar owner for the textbook summand `x_j² / λ_j`;
2. mathlib's `stdSimplex ℝ ι` is the canonical simplex owner for the feasible set on a finite
   nonempty index type;
3. `separableSum` from Theorem 6.6 is the chapter's `core/canonical` owner for the finite
   coordinatewise simplex objective;
4. the finite-product `ℓ¹` norm written as `‖x‖₁` is the source-facing norm on
   `EuclideanSpace ℝ ι`, specializing to `ℝ^n` when `ι = Fin n`;
5. `IsMinOn` is the owner property for an explicit minimizer of the simplex objective;
6. `l1_norm_eq_one_of_mem_stdSimplex` from Remark 5.18 is the nearby simplex-side `bridge/view`
   showing how `‖x‖₁²` reduces on simplex-constrained models.

Primitive data:
- `source-facing`: only `x` and the simplex variable `λ`;
- `core/canonical`: the separable objective `separableSum (fun j ↦ φ (x j, ·))` on the
  `PiLp` realization of the simplex variable;
- `bridge/view`: the explicit minimizing simplex point used to witness the infimum.

The optimizer is therefore auxiliary derived data, not a second public owner. The public API keeps
the textbook coordinate statement, while the internal objective is understood through the existing
owner `separableSum` and the canonical bridge `toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι`. -/

/-- The textbook simplex minimizer for the squared `ℓ¹` variational objective: the uniform simplex
point at `x = 0`, and otherwise the vector of normalized absolute values. -/
private def l1SquareVariationalOptimizer (x : E) : ι → ℝ :=
  if x = 0 then
    fun _ ↦ (Fintype.card ι : ℝ)⁻¹
  else
    fun j ↦ |x j| / ‖x‖₁

/-- Helper for Lemma 6.69: a nonzero vector has strictly positive `ℓ¹` norm. -/
private lemma l1_norm_pos_of_ne_zero (x : E) (hx : x ≠ 0) : 0 < ‖x‖₁ := by
  -- Rewrite the `ℓ¹` norm as a sum of coordinate absolute values and rule out total cancellation.
  by_contra hnonpos
  have hnorm_nonneg : 0 ≤ ‖x‖₁ := by
    rw [EuclideanSpace.l1Norm_eq_sum_abs]
    exact Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hnorm_eq : ‖x‖₁ = 0 := by
    linarith
  have hzero_abs :
      (fun i ↦ |x i|) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (f := fun i ↦ |x i|)
      (show 0 ≤ fun i ↦ |x i| from fun i ↦ abs_nonneg _)).1 <| by
        simpa [EuclideanSpace.l1Norm_eq_sum_abs] using hnorm_eq
  have hx0 : x = 0 := by
    -- Every coordinate must vanish once its absolute value is forced to be zero.
    ext i
    have hi : |x i| = 0 := by
      simpa using congrFun hzero_abs i
    simpa [abs_eq_zero] using hi
  exact hx hx0

/-- Helper for Lemma 6.69: finite sums of real numbers embed coordinatewise into `EReal`. -/
private lemma ereal_coe_finset_sum (s : Finset ι) (f : ι → ℝ) :
    Finset.sum s (fun i ↦ ((f i : ℝ) : EReal)) = ((Finset.sum s f : ℝ) : EReal) := by
  classical
  -- The statement is stable under adjoining one term because coercion preserves addition.
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s hi ih =>
      simp [hi, ih, EReal.coe_add]

/-- Helper for Lemma 6.69: the algebraic value of the positive-branch optimizer denominator
collapses to `|x| * n`. -/
private lemma sq_div_abs_div_eq_abs_mul {x n : ℝ} (hn : n ≠ 0) :
    x ^ (2 : ℕ) / (|x| / n) = |x| * n := by
  -- Split off the trivial zero case; otherwise clear denominators and use `|x|² = x²`.
  by_cases hx : x = 0
  · simp [hx]
  · have hax : |x| ≠ 0 := abs_ne_zero.mpr hx
    field_simp [hn, hax]
    rw [← sq_abs]

/-- Helper for Lemma 6.69: the quadratic-over-linear function never takes the value `⊥`. -/
private lemma quadratic_over_linear_ne_bot (s t : ℝ) : φ (s, t) ≠ ⊥ := by
  -- Unfold the piecewise definition and check each branch directly.
  by_cases ht : 0 < t
  · rw [quadratic_over_linear_of_pos ht]
    exact EReal.coe_ne_bot _
  · by_cases hzero : s = 0 ∧ t = 0
    · simp [quadratic_over_linear, ht, hzero]
    · simp [quadratic_over_linear, ht, hzero]

/-- Helper for Lemma 6.69: the explicit normalized absolute-value vector lies in the standard
simplex. -/
private lemma l1SquareVariationalOptimizer_mem_stdSimplex (x : E) :
    l1SquareVariationalOptimizer x ∈ Δ := by
  by_cases hx : x = 0
  · -- In the zero branch the optimizer is the uniform simplex point.
    have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty ι›
    rw [l1SquareVariationalOptimizer, if_pos hx, stdSimplex]
    constructor
    · intro j
      exact inv_nonneg.mpr hcard_pos.le
    · simp [Finset.card_univ, hcard_pos.ne']
  · -- In the nonzero branch the optimizer is the normalized coordinatewise absolute value.
    have hnorm_pos : 0 < ‖x‖₁ := l1_norm_pos_of_ne_zero x hx
    rw [l1SquareVariationalOptimizer, if_neg hx, stdSimplex]
    constructor
    · intro j
      exact div_nonneg (abs_nonneg _) hnorm_pos.le
    · calc
        ∑ j, |x j| / ‖x‖₁ = (∑ j, |x j|) / ‖x‖₁ := by
          rw [Finset.sum_div]
        _ = ‖x‖₁ / ‖x‖₁ := by
          rw [← EuclideanSpace.l1Norm_eq_sum_abs]
        _ = 1 := by
          exact div_self hnorm_pos.ne'

/-- Helper for Lemma 6.69: every simplex point yields a variational value at least `‖x‖₁²`. -/
private lemma sq_l1_norm_le_sum_quadratic_over_linear_of_mem_stdSimplex
    (x : E) (lam : ι → ℝ) (hΔ : lam ∈ Δ) :
    ((‖x‖₁ ^ (2 : ℕ) : ℝ) : EReal) ≤ ∑ j, φ (x j, lam j) := by
  classical
  by_cases hbad : ∃ i, lam i = 0 ∧ x i ≠ 0
  · -- A zero weight on a nonzero coordinate forces one summand to be `⊤`, so the whole sum is `⊤`.
    rcases hbad with ⟨i, hlam_zero, hxi_ne⟩
    have hphi_top : φ (x i, lam i) = ⊤ := by
      refine quadratic_over_linear_of_nonpos_of_ne_origin ?_ ?_
      · simpa [hlam_zero]
      · intro hpair
        have hxi_zero : x i = 0 := by
          simpa using congrArg Prod.fst hpair
        exact hxi_ne hxi_zero
    have hsum_top : ∑ j, φ (x j, lam j) = ⊤ := by
      have hrest_ne_bot :
          Finset.sum (Finset.univ \ {i}) (fun j ↦ φ (x j, lam j)) ≠ ⊥ := by
        intro hbot
        have hbot' :
            ∃ j ∈ Finset.univ \ {i}, φ (x j, lam j) = (⊥ : EReal) := by
          simpa using
            (WithBot.sum_eq_bot_iff
              (s := Finset.univ \ {i}) (f := fun j ↦ φ (x j, lam j))).1 hbot
        rcases hbot' with ⟨j, hj, hjbot⟩
        exact quadratic_over_linear_ne_bot (x j) (lam j) hjbot
      rw [Finset.sum_eq_add_sum_diff_singleton
        (s := Finset.univ) (i := i) (f := fun j ↦ φ (x j, lam j)) (by simp)]
      rw [hphi_top]
      simpa using EReal.top_add_of_ne_bot hrest_ne_bot
    calc
      ((‖x‖₁ ^ (2 : ℕ) : ℝ) : EReal) ≤ ⊤ := by simp
      _ = ∑ j, φ (x j, lam j) := hsum_top.symm
  · -- On the positive support, apply Titu's lemma exactly as in the source proof.
    have hzero_coord : ∀ i, lam i = 0 → x i = 0 := by
      intro i hlam_zero
      by_contra hxi_ne
      exact hbad ⟨i, hlam_zero, hxi_ne⟩
    set s : Finset ι := Finset.univ.filter (fun i ↦ 0 < lam i) with hs
    have hs_sum_one : Finset.sum s lam = 1 := by
      have hsum_zero :
          Finset.sum (Finset.univ.filter (fun i ↦ ¬ 0 < lam i)) lam = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hle : lam i ≤ 0 := le_of_not_gt (Finset.mem_filter.mp hi).2
        have hnonneg : 0 ≤ lam i := hΔ.1 i
        linarith
      have hsplit := Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ) (p := fun i ↦ 0 < lam i) (f := lam)
      rw [← hs, hΔ.2, hsum_zero] at hsplit
      linarith
    have hs_abs_sum : Finset.sum s (fun i ↦ |x i|) = ‖x‖₁ := by
      rw [EuclideanSpace.l1Norm_eq_sum_abs]
      have hsum_zero :
          Finset.sum (Finset.univ.filter (fun i ↦ ¬ 0 < lam i)) (fun i ↦ |x i|) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hle : lam i ≤ 0 := le_of_not_gt (Finset.mem_filter.mp hi).2
        have hnonneg : 0 ≤ lam i := hΔ.1 i
        have hlam_zero : lam i = 0 := by
          linarith
        simp [hzero_coord i hlam_zero]
      have hsplit := Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ) (p := fun i ↦ 0 < lam i) (f := fun i ↦ |x i|)
      rw [← hs, hsum_zero] at hsplit
      simpa using hsplit
    have hs_pos : ∀ i ∈ s, 0 < lam i := by
      intro i hi
      have hi' : i ∈ Finset.univ.filter (fun j ↦ 0 < lam j) := by
        simpa [hs] using hi
      exact (Finset.mem_filter.mp hi').2
    have hreal :
        ‖x‖₁ ^ (2 : ℕ) ≤ Finset.sum s (fun i ↦ x i ^ (2 : ℕ) / lam i) := by
      have hsq := Finset.sq_sum_div_le_sum_sq_div
        (s := s) (f := fun i ↦ |x i|) (g := lam) hs_pos
      have habs_sq :
          Finset.sum s (fun i ↦ |x i| ^ (2 : ℕ) / lam i) =
            Finset.sum s (fun i ↦ x i ^ (2 : ℕ) / lam i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [sq_abs]
      rw [hs_sum_one, div_one, hs_abs_sum] at hsq
      simpa [habs_sq] using hsq
    have hobjective_eq :
        ∑ j, φ (x j, lam j) =
          ((Finset.sum s (fun j ↦ x j ^ (2 : ℕ) / lam j) : ℝ) : EReal) := by
      have hsplit :
          Finset.sum Finset.univ (fun j ↦ φ (x j, lam j)) =
            Finset.sum s (fun j ↦ φ (x j, lam j)) +
              Finset.sum (Finset.univ.filter (fun j ↦ ¬ 0 < lam j)) (fun j ↦ φ (x j, lam j)) := by
        simpa [hs] using
          (Finset.sum_filter_add_sum_filter_not
            (s := Finset.univ) (p := fun j ↦ 0 < lam j)
            (f := fun j ↦ φ (x j, lam j))).symm
      have hsum_zero :
          Finset.sum (Finset.univ.filter (fun j ↦ ¬ 0 < lam j)) (fun j ↦ φ (x j, lam j)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j hj
        have hle : lam j ≤ 0 := le_of_not_gt (Finset.mem_filter.mp hj).2
        have hnonneg : 0 ≤ lam j := hΔ.1 j
        have hlam_zero : lam j = 0 := by
          linarith
        simp [hzero_coord j hlam_zero, hlam_zero]
      calc
        ∑ j, φ (x j, lam j) = Finset.sum s (fun j ↦ φ (x j, lam j)) := by
          rw [hsplit, hsum_zero, add_zero]
        _ = Finset.sum s (fun j ↦ ((x j ^ (2 : ℕ) / lam j : ℝ) : EReal)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact quadratic_over_linear_of_pos (hs_pos j hj)
        _ = ((Finset.sum s (fun j ↦ x j ^ (2 : ℕ) / lam j) : ℝ) : EReal) := by
          simpa using ereal_coe_finset_sum s (fun j ↦ x j ^ (2 : ℕ) / lam j)
    -- Cast the real Cauchy--Schwarz lower bound into `EReal` and compare with the exact objective.
    have hrealE :
        ((‖x‖₁ ^ (2 : ℕ) : ℝ) : EReal) ≤
          ((Finset.sum s (fun i ↦ x i ^ (2 : ℕ) / lam i) : ℝ) : EReal) := by
      exact_mod_cast hreal
    calc
      ((‖x‖₁ ^ (2 : ℕ) : ℝ) : EReal) ≤
          ((Finset.sum s (fun i ↦ x i ^ (2 : ℕ) / lam i) : ℝ) : EReal) := hrealE
      _ = ∑ j, φ (x j, lam j) := hobjective_eq.symm

/-- Helper for Lemma 6.69: the explicit optimizer attains objective value `‖x‖₁²`. -/
private lemma sum_quadratic_over_linear_at_l1SquareVariationalOptimizer (x : E) :
    ∑ j, φ (x j, l1SquareVariationalOptimizer x j) =
      ((‖x‖₁ ^ (2 : ℕ) : ℝ) : EReal) := by
  classical
  by_cases hx : x = 0
  · -- At the zero vector, every summand vanishes at the uniform simplex point.
    have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty ι›
    have hterm : ∀ j, φ (x j, l1SquareVariationalOptimizer x j) = 0 := by
      intro j
      have hxj : x j = 0 := by
        simpa using congrArg (fun y : E ↦ y j) hx
      rw [l1SquareVariationalOptimizer, if_pos hx, hxj,
        quadratic_over_linear_of_pos (inv_pos.mpr hcard_pos)]
      simp
    have hl1_zero : ‖x‖₁ = 0 := by
      rw [hx, EuclideanSpace.l1Norm_eq_sum_abs]
      simp
    calc
      ∑ j, φ (x j, l1SquareVariationalOptimizer x j) = ∑ j, (0 : EReal) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact hterm j
      _ = ((‖x‖₁ ^ (2 : ℕ) : ℝ) : EReal) := by
        simp [hl1_zero]
  · -- Away from zero, each positive-branch summand simplifies to `|x_j| * ‖x‖₁`.
    have hnorm_pos : 0 < ‖x‖₁ := l1_norm_pos_of_ne_zero x hx
    have hterm :
        ∀ j, φ (x j, l1SquareVariationalOptimizer x j) = ((|x j| * ‖x‖₁ : ℝ) : EReal) := by
      intro j
      by_cases hxj : x j = 0
      · rw [l1SquareVariationalOptimizer, if_neg hx]
        simp [hxj]
      · have hj_pos : 0 < l1SquareVariationalOptimizer x j := by
          rw [l1SquareVariationalOptimizer, if_neg hx]
          exact div_pos (abs_pos.mpr hxj) hnorm_pos
        rw [quadratic_over_linear_of_pos hj_pos]
        rw [l1SquareVariationalOptimizer, if_neg hx]
        norm_num
        simpa using congrArg (fun t : ℝ ↦ (t : EReal))
          (sq_div_abs_div_eq_abs_mul hnorm_pos.ne')
    calc
      ∑ j, φ (x j, l1SquareVariationalOptimizer x j) =
          ∑ j, ((|x j| * ‖x‖₁ : ℝ) : EReal) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            exact hterm j
      _ = ((∑ j, |x j| * ‖x‖₁ : ℝ) : EReal) := by
            simpa using ereal_coe_finset_sum Finset.univ (fun j ↦ |x j| * ‖x‖₁)
      _ = (((∑ j, |x j| : ℝ) * ‖x‖₁ : ℝ) : EReal) := by
            congr 1
            rw [Finset.sum_mul]
      _ = ((‖x‖₁ ^ (2 : ℕ) : ℝ) : EReal) := by
            congr 1
            rw [EuclideanSpace.l1Norm_eq_sum_abs]
            ring

-- Proof sketch: on the zero vector, the uniform point belongs to `Δ` and every summand vanishes.
-- For `x ≠ 0`, use Cauchy--Schwarz on the positive coordinates of a simplex vector to show every
-- feasible value is at least `‖x‖₁²`, then evaluate the objective at
-- `l1SquareVariationalOptimizer x` to obtain equality.
/-- The explicit optimizer from the variational representation of the squared `ℓ¹` norm attains
its minimum over the standard simplex. -/
private theorem l1SquareVariationalOptimizer_isMinOn (x : E) :
    IsMinOn
      (fun lam : ι → ℝ ↦ separableSum (fun j : ι ↦ fun t ↦ φ (x j, t)) (toLp 2 lam)) Δ
      (l1SquareVariationalOptimizer x) := by
  -- Compare any feasible simplex point with the explicit optimizer through the common value `‖x‖₁²`.
  intro lam hlam
  calc
    separableSum (fun j : ι ↦ fun t ↦ φ (x j, t)) (toLp 2 (l1SquareVariationalOptimizer x)) =
        ∑ j, φ (x j, l1SquareVariationalOptimizer x j) := by
          simp [separableSum]
    _ = ((‖x‖₁ ^ (2 : ℕ) : ℝ) : EReal) :=
      sum_quadratic_over_linear_at_l1SquareVariationalOptimizer x
    _ ≤ ∑ j, φ (x j, lam j) :=
      sq_l1_norm_le_sum_quadratic_over_linear_of_mem_stdSimplex x lam hlam
    _ = separableSum (fun j : ι ↦ fun t ↦ φ (x j, t)) (toLp 2 lam) := by
          simp [separableSum]

-- Proof sketch: combine `l1SquareVariationalOptimizer_isMinOn x` with a direct evaluation of the
-- objective at `l1SquareVariationalOptimizer x`. For `x ≠ 0`, the value is `‖x‖₁²`; for `x = 0`,
-- every summand vanishes at the uniform simplex point.
/-- Lemma 6.69: for a finite nonempty index type `ι`, the minimum over the standard simplex
`Δ = stdSimplex ℝ ι` of the coordinate presentation
`λ ↦ ∑ j, φ(x_j, λ_j)` of the separable variational objective is the squared `ℓ¹` norm
`‖x‖₁²`. Specializing to `ι = Fin n` recovers the textbook `Δ_n ⊆ ℝ^n` statement. -/
theorem l1SquareVariationalObjective_sInf_eq_sq_l1_norm (x : E) :
    sInf ((fun lam : ι → ℝ ↦ ∑ j, φ (x j, lam j)) '' Δ) =
      ((‖x‖₁ ^ (2 : ℕ) : ℝ) : EReal) := by
  have hmem : l1SquareVariationalOptimizer x ∈ Δ :=
    l1SquareVariationalOptimizer_mem_stdSimplex x
  have hmin :
      IsMinOn (fun lam : ι → ℝ ↦ ∑ j, φ (x j, lam j)) Δ (l1SquareVariationalOptimizer x) := by
    -- The private separable-sum minimizer theorem is definitionally the coordinatewise objective.
    simpa [separableSum] using l1SquareVariationalOptimizer_isMinOn x
  -- Rewrite the infimum over the image set as an infimum over simplex points and evaluate it at the minimizer.
  rw [sInf_image]
  calc
    (⨅ a, ⨅ (_ : a ∈ Δ), ∑ j, φ (x j, a j)) = ∑ j, φ (x j, l1SquareVariationalOptimizer x j) := by
      simpa [iInf_subtype] using IsMinOn.iInf_eq hmem hmin
    _ = ((‖x‖₁ ^ (2 : ℕ) : ℝ) : EReal) :=
      sum_quadratic_over_linear_at_l1SquareVariationalOptimizer x

end
