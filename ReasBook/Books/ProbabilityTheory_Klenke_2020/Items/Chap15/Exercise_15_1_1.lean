/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open BoundedContinuousFunction
open scoped BoundedContinuousFunction Topology

noncomputable section

private def arctanBCF : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup Real.arctan Real.continuous_arctan (Real.pi / 2)
    fun x ↦ by
      rw [Real.norm_eq_abs]
      refine abs_le.2 ?_
      constructor
      · linarith [Real.neg_pi_div_two_lt_arctan x]
      · linarith [Real.arctan_lt_pi_div_two x]

private def sinBCF : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup Real.sin Real.continuous_sin 1 fun x ↦ by
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one x

private theorem eval_aeval_bcf (g : ℝ →ᵇ ℝ) (p : Polynomial ℝ) (x : ℝ) :
    (Polynomial.aeval g p : ℝ →ᵇ ℝ) x = p.eval (g x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [Polynomial.eval_add, hp, hq]
  | monomial n a =>
      simp [Polynomial.eval_monomial]

private theorem arctanBCF_injective : Function.Injective arctanBCF := by
  intro x y hxy
  exact Real.arctan_injective hxy

private theorem arctan_adjoin_separatesPoints :
    ((Algebra.adjoin ℝ ({arctanBCF} : Set (ℝ →ᵇ ℝ))).map (toContinuousMapₐ ℝ)).SeparatesPoints := by
  intro x y hxy
  refine ⟨toContinuousMapₐ ℝ arctanBCF, ?_, ?_⟩
  · refine ⟨toContinuousMapₐ ℝ arctanBCF, ?_, rfl⟩
    refine Subalgebra.mem_map.2 ?_
    exact ⟨(arctanBCF : ℝ →ᵇ ℝ), Algebra.self_mem_adjoin_singleton ℝ arctanBCF, rfl⟩
  · simpa using fun h : arctanBCF x = arctanBCF y ↦ hxy (arctanBCF_injective h)

private theorem tendsto_atTop_of_mem_arctanAdjoin {f : ℝ →ᵇ ℝ}
    (hf : f ∈ Algebra.adjoin ℝ ({arctanBCF} : Set (ℝ →ᵇ ℝ))) :
    ∃ l : ℝ, Filter.Tendsto (fun x ↦ f x) Filter.atTop (𝓝 l) := by
  rcases Algebra.adjoin_mem_exists_aeval ℝ arctanBCF hf with ⟨p, rfl⟩
  refine ⟨p.eval (Real.pi / 2), ?_⟩
  have harctan : Filter.Tendsto (fun x ↦ arctanBCF x) Filter.atTop (𝓝 (Real.pi / 2)) := by
    simpa [arctanBCF] using
      tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop
  have hpoly :
      Filter.Tendsto (fun x ↦ p.eval (arctanBCF x)) Filter.atTop (𝓝 (p.eval (Real.pi / 2))) :=
    p.continuous.tendsto _ |>.comp harctan
  simpa [eval_aeval_bcf] using hpoly

private theorem sin_far_from_arctanAdjoin {f : ℝ →ᵇ ℝ}
    (hf : f ∈ Algebra.adjoin ℝ ({arctanBCF} : Set (ℝ →ᵇ ℝ))) :
    1 / 4 ≤ dist sinBCF f := by
  refine le_of_not_gt ?_
  intro hdist
  rcases tendsto_atTop_of_mem_arctanAdjoin hf with ⟨l, hl⟩
  have hzero : ∀ n : ℕ, |f ((2 * Real.pi) * n)| < 1 / 4 := by
    intro n
    have hpoint :=
      lt_of_le_of_lt
        (dist_coe_le_dist ((2 * Real.pi) * n) : dist (sinBCF ((2 * Real.pi) * n)) (f ((2 * Real.pi) * n)) ≤ _)
        hdist
    have hsin : Real.sin ((2 * Real.pi) * n) = 0 := by
      have h := Real.sin_add_int_mul_two_pi 0 (n : ℤ)
      simpa [Int.cast_natCast, zero_add, zero_mul, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using h
    simpa [sinBCF, Real.dist_eq, hsin] using hpoint
  have hone : ∀ n : ℕ, |1 - f (Real.pi / 2 + (2 * Real.pi) * n)| < 1 / 4 := by
    intro n
    have hpoint :=
      lt_of_le_of_lt
        (dist_coe_le_dist (Real.pi / 2 + (2 * Real.pi) * n) :
          dist (sinBCF (Real.pi / 2 + (2 * Real.pi) * n))
            (f (Real.pi / 2 + (2 * Real.pi) * n)) ≤ _)
        hdist
    have hsin : Real.sin (Real.pi / 2 + (2 * Real.pi) * n) = 1 := by
      have h := Real.sin_add_int_mul_two_pi (Real.pi / 2) (n : ℤ)
      simpa [Int.cast_natCast, add_assoc, mul_comm, mul_left_comm, mul_assoc] using h
    simpa [sinBCF, Real.dist_eq, hsin, abs_sub_comm] using hpoint
  have hseq0 : Filter.Tendsto (fun n : ℕ ↦ (2 * Real.pi : ℝ) * n) Filter.atTop Filter.atTop := by
    simpa [two_mul, mul_comm] using
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : 0 < (2 * Real.pi : ℝ))
  have hseq1 :
      Filter.Tendsto (fun n : ℕ ↦ Real.pi / 2 + (2 * Real.pi : ℝ) * n) Filter.atTop
        Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    have hb : ∀ᶠ n : ℕ in Filter.atTop, b - Real.pi / 2 ≤ (2 * Real.pi : ℝ) * n :=
      hseq0 <| Filter.Ici_mem_atTop (b - Real.pi / 2)
    filter_upwards [hb] with n hn
    linarith
  have hl0 : Filter.Tendsto (fun n : ℕ ↦ f ((2 * Real.pi : ℝ) * n)) Filter.atTop (𝓝 l) :=
    hl.comp hseq0
  have hl1 :
      Filter.Tendsto (fun n : ℕ ↦ f (Real.pi / 2 + (2 * Real.pi : ℝ) * n)) Filter.atTop
        (𝓝 l) :=
    hl.comp hseq1
  have hlt0 : ∀ᶠ n : ℕ in Filter.atTop, |f ((2 * Real.pi : ℝ) * n) - l| < 1 / 8 := by
    have hball : {y : ℝ | |y - l| < 1 / 8} ∈ 𝓝 l := by
      simpa [Metric.ball, Real.dist_eq] using Metric.ball_mem_nhds l (by positivity)
    simpa using hl0 hball
  have hlt1 :
      ∀ᶠ n : ℕ in Filter.atTop, |f (Real.pi / 2 + (2 * Real.pi : ℝ) * n) - l| < 1 / 8 := by
    have hball : {y : ℝ | |l - y| < 1 / 8} ∈ 𝓝 l := by
      simpa [Metric.ball, Real.dist_eq, abs_sub_comm] using Metric.ball_mem_nhds l (by positivity)
    simpa [abs_sub_comm] using hl1 hball
  rcases Filter.Eventually.exists (hlt0.and hlt1) with ⟨n, hn0, hn1⟩
  have hclose :
      |f ((2 * Real.pi : ℝ) * n) - f (Real.pi / 2 + (2 * Real.pi) * n)| < 1 / 4 := by
    calc
      |f ((2 * Real.pi : ℝ) * n) - f (Real.pi / 2 + (2 * Real.pi) * n)|
          ≤ |f ((2 * Real.pi : ℝ) * n) - l| + |l - f (Real.pi / 2 + (2 * Real.pi) * n)| := by
            simpa using abs_sub_le (f ((2 * Real.pi : ℝ) * n)) l
              (f (Real.pi / 2 + (2 * Real.pi) * n))
      _ < 1 / 8 + 1 / 8 := add_lt_add hn0 (by simpa [abs_sub_comm] using hn1)
      _ = 1 / 4 := by norm_num
  have hx := abs_lt.mp (hzero n)
  have hy := abs_lt.mp (hone n)
  have hneg :
      f ((2 * Real.pi : ℝ) * n) - f (Real.pi / 2 + (2 * Real.pi) * n) < 0 := by
    linarith
  have hfar :
      1 / 2 < |f ((2 * Real.pi : ℝ) * n) - f (Real.pi / 2 + (2 * Real.pi) * n)| := by
    rw [abs_of_neg hneg]
    linarith
  linarith

-- Proof sketch: take a bounded continuous injective function `ℝ → ℝ`, such as `Real.arctan`,
-- and let `A` be the real subalgebra it generates. A singleton generating family is countable,
-- and polynomial expressions in an injective generator still separate points.
/-- A point-separating real subalgebra of bounded continuous functions on `ℝ` can be generated by
a countable family. -/
theorem exists_countable_generating_set_of_separating_subalgebra_boundedContinuousFunction_real :
    ∃ (A : Subalgebra ℝ (ℝ →ᵇ ℝ)) (s : Set (ℝ →ᵇ ℝ)),
      Set.Countable s ∧
        Algebra.adjoin ℝ s = A ∧
          (A.map (toContinuousMapₐ ℝ)).SeparatesPoints := by
  refine ⟨Algebra.adjoin ℝ ({arctanBCF} : Set (ℝ →ᵇ ℝ)), {arctanBCF}, Set.countable_singleton _,
    rfl, ?_⟩
  simpa using arctan_adjoin_separatesPoints

-- Proof sketch: use a countably generated point-separating real subalgebra as above. If it were
-- dense in `C_b(ℝ)`, then the metric space `ℝ →ᵇ ℝ` would be separable because the algebra
-- generated by a countable family is separable, contradicting the standard nonseparability of
-- `C_b(ℝ)`.
/-- Exercise 15.1.1: compactness is essential in Stone--Weierstrass, since there exists a
point-separating real subalgebra of `C_b(ℝ)` that is not dense in the supremum norm topology. -/
theorem stoneWeierstrass_compactness_counterexample_boundedContinuousFunction_real :
    ∃ A : Subalgebra ℝ (ℝ →ᵇ ℝ),
      (A.map (toContinuousMapₐ ℝ)).SeparatesPoints ∧
        ¬ Dense (A : Set (ℝ →ᵇ ℝ)) := by
  refine ⟨Algebra.adjoin ℝ ({arctanBCF} : Set (ℝ →ᵇ ℝ)), ?_, ?_⟩
  · simpa using arctan_adjoin_separatesPoints
  · intro hA
    obtain ⟨f, hf, hdist⟩ :=
      hA.exists_dist_lt sinBCF (show 0 < (1 / 4 : ℝ) by norm_num)
    have hfar := sin_far_from_arctanAdjoin hf
    linarith
