/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section22_part3

open scoped BigOperators Pointwise
open Topology

section Chap04
section Section22

/-- Helper for Text 22.3.4: the counterexample row family is `t ↦ (t, t^2)` on `[0, 1]`. -/
def helperForText_22_3_4_counterexampleRow (t : Set.Icc (0 : ℝ) 1) : Fin 2 → ℝ :=
  ![(t : ℝ), (t : ℝ) ^ 2]

/-- Helper for Text 22.3.4: the target inequality in the counterexample is the first
coordinate functional. -/
def helperForText_22_3_4_counterexampleTarget : Fin 2 → ℝ :=
  ![(1 : ℝ), (0 : ℝ)]

/-- Helper for Text 22.3.4: the row family has the expected dot-product formula. -/
lemma helperForText_22_3_4_counterexampleRow_dotProduct
    (t : Set.Icc (0 : ℝ) 1) (x : Fin 2 → ℝ) :
    dotProduct (helperForText_22_3_4_counterexampleRow t) x =
      (t : ℝ) * x 0 + (t : ℝ) ^ 2 * x 1 := by
  -- Expand the two coordinates of the counterexample row explicitly.
  simp [helperForText_22_3_4_counterexampleRow, dotProduct, Fin.sum_univ_two]

/-- Helper for Text 22.3.4: the target vector reads off the first coordinate. -/
lemma helperForText_22_3_4_counterexampleTarget_dotProduct
    (x : Fin 2 → ℝ) :
    dotProduct helperForText_22_3_4_counterexampleTarget x = x 0 := by
  -- The second coordinate of the target vector vanishes.
  simp [helperForText_22_3_4_counterexampleTarget, dotProduct, Fin.sum_univ_two]

/-- Helper for Text 22.3.4: the compact curve `t ↦ (t, t^2)` has closed and bounded range
in `ℝ^2`. -/
lemma helperForText_22_3_4_counterexample_range_closed_bounded :
    IsClosed (Set.range helperForText_22_3_4_counterexampleRow) ∧
      Bornology.IsBounded (Set.range helperForText_22_3_4_counterexampleRow) := by
  let g : ℝ → (Fin 2 → ℝ) := fun t => ![t, t ^ 2]
  have hrange :
      Set.range helperForText_22_3_4_counterexampleRow = g '' Set.Icc (0 : ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  have hcont : Continuous g := by
    -- Continuity is coordinatewise: `t` and `t^2` are continuous on `ℝ`.
    refine continuous_pi ?_
    intro i
    fin_cases i
    · simpa [g] using (continuous_id : Continuous fun a : ℝ => a)
    · simpa [g] using (continuous_id.pow 2 : Continuous fun a : ℝ => a ^ 2)
  have hcompact : IsCompact (g '' Set.Icc (0 : ℝ) 1) := isCompact_Icc.image hcont
  constructor
  · -- Closedness follows from compactness of the image.
    simpa [hrange] using hcompact.isClosed
  · -- Boundedness is another compactness consequence.
    simpa [hrange] using hcompact.isBounded

/-- Helper for Text 22.3.4: feasibility for the counterexample family is equivalent to the
two wedge inequalities `x₀ ≤ 0` and `x₀ + x₁ ≤ 0`. -/
lemma helperForText_22_3_4_counterexample_feasible_iff
    (x : Fin 2 → ℝ) :
    (∀ t : Set.Icc (0 : ℝ) 1,
        dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0) ↔
      x 0 ≤ 0 ∧ x 0 + x 1 ≤ 0 := by
  constructor
  · intro hx
    have hsum : x 0 + x 1 ≤ 0 := by
      have h1 : dotProduct
          (helperForText_22_3_4_counterexampleRow ⟨1, by constructor <;> norm_num⟩) x ≤ 0 :=
        hx ⟨1, by constructor <;> norm_num⟩
      simpa [helperForText_22_3_4_counterexampleRow, dotProduct, Fin.sum_univ_two] using h1
    have hx0_nonpos : x 0 ≤ 0 := by
      by_contra hx0_nonpos
      have hx0_pos : 0 < x 0 := by linarith
      have hx1_neg : x 1 < 0 := by linarith
      have hx1_ne : x 1 ≠ 0 := ne_of_lt hx1_neg
      let t : ℝ := -x 0 / (2 * x 1)
      have ht_pos : 0 < t := by
        -- The witness parameter is positive because both numerator and denominator are negative.
        dsimp [t]
        have hnum : -x 0 < 0 := by linarith
        have hden : 2 * x 1 < 0 := by linarith
        exact div_pos_of_neg_of_neg hnum hden
      have ht_le_one : t ≤ 1 := by
        -- The inequality at `t = 1` ensures this witness still lies in `[0, 1]`.
        dsimp [t]
        have hden : 2 * x 1 < 0 := by linarith
        have haux : (1 : ℝ) * (2 * x 1) ≤ -x 0 := by linarith
        exact (div_le_iff_of_neg hden).2 haux
      have hineq :
          dotProduct
              (helperForText_22_3_4_counterexampleRow ⟨t, ⟨le_of_lt ht_pos, ht_le_one⟩⟩) x ≤ 0 :=
        hx ⟨t, ⟨le_of_lt ht_pos, ht_le_one⟩⟩
      have ht_mul : t * x 1 = -x 0 / 2 := by
        -- Multiplying the chosen `t` by `x₁` cancels the denominator.
        dsimp [t]
        field_simp [hx1_ne]
      have hrewrite : t * x 0 + t ^ 2 * x 1 = t * (x 0 / 2) := by
        calc
          t * x 0 + t ^ 2 * x 1 = t * x 0 + t * (t * x 1) := by ring
          _ = t * x 0 + t * (-x 0 / 2) := by rw [ht_mul]
          _ = t * (x 0 / 2) := by ring
      have hpositive : 0 < t * x 0 + t ^ 2 * x 1 := by
        -- The chosen parameter makes the bracket equal to `x₀ / 2`, which is positive.
        rw [hrewrite]
        have hx0_half_pos : 0 < x 0 / 2 := by linarith
        exact mul_pos ht_pos hx0_half_pos
      have : ¬ t * x 0 + t ^ 2 * x 1 ≤ 0 := by linarith
      exact this (by simpa [helperForText_22_3_4_counterexampleRow_dotProduct] using hineq)
    exact ⟨hx0_nonpos, hsum⟩
  · rintro ⟨hx0_nonpos, hsum⟩ t
    -- Rewrite the quadratic expression as a nonnegative combination of two known
    -- nonpositive quantities.
    have ht_nonneg : 0 ≤ (t : ℝ) := t.2.1
    have ht_le_one : (t : ℝ) ≤ 1 := t.2.2
    have hmix :
        x 0 + (t : ℝ) * x 1 ≤ 0 := by
      have hterm0 : (1 - (t : ℝ)) * x 0 ≤ 0 := by
        have h01 : 0 ≤ 1 - (t : ℝ) := by linarith
        exact mul_nonpos_of_nonneg_of_nonpos h01 hx0_nonpos
      have hterm1 : (t : ℝ) * (x 0 + x 1) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos ht_nonneg hsum
      have hcomb : (1 - (t : ℝ)) * x 0 + (t : ℝ) * (x 0 + x 1) ≤ 0 := by
        exact add_nonpos hterm0 hterm1
      have hrewrite :
          (1 - (t : ℝ)) * x 0 + (t : ℝ) * (x 0 + x 1) = x 0 + (t : ℝ) * x 1 := by
        ring
      rw [hrewrite] at hcomb
      exact hcomb
    have hineq :
        (t : ℝ) * x 0 + (t : ℝ) ^ 2 * x 1 ≤ 0 := by
      have hscaled : (t : ℝ) * (x 0 + (t : ℝ) * x 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht_nonneg hmix
      simpa [pow_two, mul_add, mul_assoc, mul_left_comm, mul_comm] using hscaled
    simpa [helperForText_22_3_4_counterexampleRow_dotProduct] using hineq

/-- Helper for Text 22.3.4: the counterexample feasible set has nonempty interior because
it contains the open wedge `x₀ < 0`, `x₀ + x₁ < 0`. -/
lemma helperForText_22_3_4_counterexample_interior_nonempty :
    (interior
      {x : Fin 2 → ℝ |
        ∀ t : Set.Icc (0 : ℝ) 1,
          dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0}).Nonempty := by
  let U : Set (Fin 2 → ℝ) := {x : Fin 2 → ℝ | x 0 < 0 ∧ x 0 + x 1 < 0}
  let xbar : Fin 2 → ℝ := ![-(1 : ℝ), (0 : ℝ)]
  have hU_open : IsOpen U := by
    -- Both strict inequalities are open conditions on `ℝ^2`.
    simpa [U] using
      (isOpen_lt (continuous_apply 0) continuous_const).inter
        (isOpen_lt ((continuous_apply 0).add (continuous_apply 1)) continuous_const)
  have hxbar_mem : xbar ∈ U := by
    simp [U, xbar]
  have hU_subset :
      U ⊆
        {x : Fin 2 → ℝ |
          ∀ t : Set.Icc (0 : ℝ) 1,
            dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0} := by
    intro x hxU
    have hx0_nonpos : x 0 ≤ 0 := by linarith [hxU.1]
    have hsum : x 0 + x 1 ≤ 0 := by linarith [hxU.2]
    exact (helperForText_22_3_4_counterexample_feasible_iff x).2 ⟨hx0_nonpos, hsum⟩
  -- The open wedge sits inside the feasible set, so the feasible set has interior.
  refine ⟨xbar, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact Filter.mem_of_superset (hU_open.mem_nhds hxbar_mem) hU_subset

/-- Helper for Text 22.3.4: every point feasible for the compact family already satisfies
the target inequality `x₀ ≤ 0`. -/
lemma helperForText_22_3_4_counterexample_consequence :
    ∀ ⦃x : Fin 2 → ℝ⦄,
      (∀ t : Set.Icc (0 : ℝ) 1,
        dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0) →
        dotProduct helperForText_22_3_4_counterexampleTarget x ≤ 0 := by
  intro x hx
  -- The feasibility characterization identifies the first coordinate as nonpositive.
  have hx0_nonpos : x 0 ≤ 0 := (helperForText_22_3_4_counterexample_feasible_iff x).1 hx |>.1
  calc
    dotProduct helperForText_22_3_4_counterexampleTarget x = x 0 :=
      helperForText_22_3_4_counterexampleTarget_dotProduct x
    _ ≤ 0 := hx0_nonpos

/-- Helper for Text 22.3.4: the target vector `(1, 0)` is not a finite nonnegative
combination of the rows `(t, t^2)` with `t ∈ [0, 1]`. -/
lemma helperForText_22_3_4_counterexample_no_finite_certificate :
    ¬ ∃ m : ℕ, m ≤ 2 ∧
        ∃ indices : Fin m → Set.Icc (0 : ℝ) 1,
          ∃ coeffs : Fin m → ℝ,
            (∀ k, 0 ≤ coeffs k) ∧
              helperForText_22_3_4_counterexampleTarget =
                ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k) := by
  rintro ⟨m, hm, indices, coeffs, hcoeffs_nonneg, hsum⟩
  have hcoord1 :
      (∑ k : Fin m, coeffs k * ((indices k : ℝ) ^ 2)) = 0 := by
    -- The second coordinate of the vector identity forces the quadratic sum to vanish.
    have h1 := congrArg (fun v : Fin 2 → ℝ => v 1) hsum
    simpa [helperForText_22_3_4_counterexampleTarget,
      helperForText_22_3_4_counterexampleRow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h1.symm
  have hquad_nonneg : ∀ k : Fin m, 0 ≤ coeffs k * ((indices k : ℝ) ^ 2) := by
    intro k
    have htk_nonneg : 0 ≤ ((indices k : ℝ) ^ 2) := sq_nonneg _
    exact mul_nonneg (hcoeffs_nonneg k) htk_nonneg
  have hlin_zero : ∀ k : Fin m, coeffs k * (indices k : ℝ) = 0 := by
    intro k
    have hk_le_sum :
        coeffs k * ((indices k : ℝ) ^ 2) ≤
          ∑ j : Fin m, coeffs j * ((indices j : ℝ) ^ 2) := by
      exact Finset.single_le_sum (fun j _ => hquad_nonneg j) (by simp)
    have hk_zero_term : coeffs k * ((indices k : ℝ) ^ 2) = 0 := by
      refine le_antisymm ?_ (hquad_nonneg k)
      rw [hcoord1] at hk_le_sum
      exact hk_le_sum
    have hk_split := mul_eq_zero.mp hk_zero_term
    rcases hk_split with hk_coeff | hk_sq
    · simp [hk_coeff]
    · have hk_t : (indices k : ℝ) = 0 := sq_eq_zero_iff.mp hk_sq
      simp [hk_t]
  have hcoord0 :
      (∑ k : Fin m, coeffs k * (indices k : ℝ)) = 1 := by
    -- The first coordinate of the same identity says the linear sum must equal `1`.
    have h0 := congrArg (fun v : Fin 2 → ℝ => v 0) hsum
    simpa [helperForText_22_3_4_counterexampleTarget,
      helperForText_22_3_4_counterexampleRow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h0.symm
  have hcoord0_zero :
      (∑ k : Fin m, coeffs k * (indices k : ℝ)) = 0 := by
    -- But every linear term vanishes because the quadratic term already forced `t = 0`
    -- or the coefficient to vanish.
    refine Finset.sum_eq_zero ?_
    intro k hk
    exact hlin_zero k
  linarith

/-- Helper for Text 22.3.4: even in the more natural `Finsupp` formulation, no finitely
supported nonnegative combination of the compact-curve rows can equal the target vector
`(1, 0)`. -/
lemma helperForText_22_3_4_counterexample_no_finsupp_certificate :
    ¬ ∃ l : Set.Icc (0 : ℝ) 1 →₀ ℝ,
        (∀ t, 0 ≤ l t) ∧
          helperForText_22_3_4_counterexampleTarget =
            l.sum (fun t c => c • helperForText_22_3_4_counterexampleRow t) := by
  rintro ⟨l, hl_nonneg, hsum⟩
  have hcoord1 :
      Finset.sum l.support (fun t => l t * ((t : ℝ) ^ 2)) = 0 := by
    -- The second coordinate of the vector identity forces the quadratic sum to vanish.
    have h1 := congrArg (fun v : Fin 2 → ℝ => v 1) hsum
    simpa [helperForText_22_3_4_counterexampleTarget,
      helperForText_22_3_4_counterexampleRow, Finsupp.sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using h1.symm
  have hquad_nonneg : ∀ t : Set.Icc (0 : ℝ) 1, 0 ≤ l t * ((t : ℝ) ^ 2) := by
    intro t
    exact mul_nonneg (hl_nonneg t) (sq_nonneg (t : ℝ))
  have hlin_zero : ∀ t : Set.Icc (0 : ℝ) 1, l t * (t : ℝ) = 0 := by
    intro t
    by_cases ht : t ∈ l.support
    · have ht_le_sum :
          l t * ((t : ℝ) ^ 2) ≤ Finset.sum l.support (fun j => l j * ((j : ℝ) ^ 2)) := by
        exact Finset.single_le_sum (fun j hj => hquad_nonneg j) ht
      have ht_zero_term : l t * ((t : ℝ) ^ 2) = 0 := by
        -- A nonnegative summand in a zero total sum must itself be zero.
        refine le_antisymm ?_ (hquad_nonneg t)
        rw [hcoord1] at ht_le_sum
        exact ht_le_sum
      rcases mul_eq_zero.mp ht_zero_term with ht_coeff | ht_sq
      · simp [ht_coeff]
      · have ht_real : (t : ℝ) = 0 := sq_eq_zero_iff.mp ht_sq
        simp [ht_real]
    · have hl_zero : l t = 0 := Finsupp.notMem_support_iff.mp ht
      -- Outside the support, the linear term already vanishes.
      simp [hl_zero]
  have hcoord0 :
      Finset.sum l.support (fun t => l t * (t : ℝ)) = 1 := by
    -- The first coordinate of the same vector identity says the linear sum must equal `1`.
    have h0 := congrArg (fun v : Fin 2 → ℝ => v 0) hsum
    simpa [helperForText_22_3_4_counterexampleTarget,
      helperForText_22_3_4_counterexampleRow, Finsupp.sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using h0.symm
  have hcoord0_zero :
      Finset.sum l.support (fun t => l t * (t : ℝ)) = 0 := by
    -- But every linear term vanishes because the quadratic-coordinate identity forced
    -- every supported row to have zero coefficient or zero parameter.
    refine Finset.sum_eq_zero ?_
    intro t ht
    exact hlin_zero t
  linarith

/-- Helper for Text 22.3.4: any finite-list nonnegative certificate for the compact-curve
counterexample repackages as a finitely supported certificate on the index set `[0, 1]`. -/
lemma helperForText_22_3_4_counterexample_finite_certificate_yields_finsupp
    {m : ℕ} {indices : Fin m → Set.Icc (0 : ℝ) 1} {coeffs : Fin m → ℝ}
    (hcoeffs_nonneg : ∀ k, 0 ≤ coeffs k)
    (hsum :
      helperForText_22_3_4_counterexampleTarget =
        ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k)) :
    ∃ l : Set.Icc (0 : ℝ) 1 →₀ ℝ,
      (∀ t, 0 ≤ l t) ∧
        helperForText_22_3_4_counterexampleTarget =
          l.sum (fun t c => c • helperForText_22_3_4_counterexampleRow t) := by
  rcases
      helperForText_22_3_3_finiteCoeffs_to_finsupp
        (m := m) (n := 2) (idx := indices) (lam := coeffs) hcoeffs_nonneg
        (a := helperForText_22_3_4_counterexampleRow) (α := fun _ => (0 : ℝ)) with
    ⟨l, hl_nonneg, hrows, _⟩
  refine ⟨l, hl_nonneg, ?_⟩
  -- Replace the finite list of rows by the equivalent finitely supported sum.
  calc
    helperForText_22_3_4_counterexampleTarget
        = ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k) := hsum
    _ = l.sum (fun t c => c • helperForText_22_3_4_counterexampleRow t) := by
      symm
      exact hrows

/-- Helper for Text 22.3.4: the counterexample still has no finite nonnegative certificate
even if one drops the cardinality bound `m ≤ 2`. -/
lemma helperForText_22_3_4_counterexample_no_finite_certificate_any_length :
    ¬ ∃ m : ℕ,
        ∃ indices : Fin m → Set.Icc (0 : ℝ) 1,
          ∃ coeffs : Fin m → ℝ,
            (∀ k, 0 ≤ coeffs k) ∧
              helperForText_22_3_4_counterexampleTarget =
                ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k) := by
  rintro ⟨m, indices, coeffs, hcoeffs_nonneg, hsum⟩
  rcases
      helperForText_22_3_4_counterexample_finite_certificate_yields_finsupp
        hcoeffs_nonneg hsum with
    ⟨l, hl_nonneg, hlsum⟩
  -- The stronger `Finsupp` obstruction rules out every finite list certificate at once.
  exact helperForText_22_3_4_counterexample_no_finsupp_certificate ⟨l, hl_nonneg, hlsum⟩

/-- Helper for Text 22.3.4: the zero vector is feasible for the homogeneous compact-curve
system, so the Section 17 closure argument applies to its zero-lifted rows. -/
lemma helperForText_22_3_4_counterexample_zero_feasible :
    ∃ x : Fin 2 → ℝ,
      ∀ t : Set.Icc (0 : ℝ) 1,
        dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0 := by
  refine ⟨0, ?_⟩
  intro t
  -- Evaluating the homogeneous inequalities at the zero vector gives equality.
  simp [helperForText_22_3_4_counterexampleRow_dotProduct]

/-- Helper for Text 22.3.4: the lifted target pair belongs to the closure of the cone
generated by the zero-lifted counterexample rows, because the target inequality is valid on
the whole feasible set. -/
lemma helperForText_22_3_4_counterexample_target_mem_closure_coneK :
    (helperForText_22_3_4_counterexampleTarget, (0 : ℝ)) ∈
      closure
        (coneK (n := 2)
          (Set.range fun t => (helperForText_22_3_4_counterexampleRow t, (0 : ℝ)))) := by
  -- Specialize the Section 22.3.3 closure lemma to the homogeneous data `α t = 0`.
  refine
    helperForText_22_3_3_target_mem_closure_coneK
      (a₀ := helperForText_22_3_4_counterexampleTarget) (α₀ := 0)
      (a := helperForText_22_3_4_counterexampleRow) (α := fun _ => (0 : ℝ)) ?_ ?_ ?_
  · intro hzero
    -- The first coordinate of `(1, 0)` shows that the target vector is nonzero.
    have hcoord := congrArg (fun v : Fin 2 → ℝ => v 0) hzero
    norm_num [helperForText_22_3_4_counterexampleTarget] at hcoord
  · exact helperForText_22_3_4_counterexample_zero_feasible
  · -- The already proved consequence lemma is exactly the required implication.
    exact helperForText_22_3_4_counterexample_consequence

/-- Helper for Text 22.3.4: the lifted target pair is not actually in `coneK`; otherwise the
conic representation theorem would yield a forbidden finite nonnegative certificate for
`(1, 0)` from the rows `(t, t^2)`. -/
lemma helperForText_22_3_4_counterexample_target_not_mem_coneK :
    (helperForText_22_3_4_counterexampleTarget, (0 : ℝ)) ∉
      coneK (n := 2)
        (Set.range fun t => (helperForText_22_3_4_counterexampleRow t, (0 : ℝ))) := by
  intro hmem
  rcases
      (mem_coneK_iff_exists_conicCombination
        (Sstar := Set.range fun t => (helperForText_22_3_4_counterexampleRow t, (0 : ℝ)))
        (xStar := helperForText_22_3_4_counterexampleTarget) (muStar := (0 : ℝ))).1 hmem with
    ⟨m, p, lam0, lam, hp, hlam0, hlam, hEq⟩
  choose indices hindices using hp
  have hx :
      helperForText_22_3_4_counterexampleTarget =
        ∑ k : Fin m, lam k • helperForText_22_3_4_counterexampleRow (indices k) := by
    -- Read the first `ℝ²` component of the conic representation after unpacking each lifted row.
    have hx0 :=
      (conicCombination_components
        (n := 2) (xStar := helperForText_22_3_4_counterexampleTarget) (muStar := (0 : ℝ))
        (p := p) (lam0 := lam0) (lam := lam) hlam0 hEq).1
    calc
      helperForText_22_3_4_counterexampleTarget = ∑ k : Fin m, lam k • (p k).1 := hx0
      _ = ∑ k : Fin m, lam k • helperForText_22_3_4_counterexampleRow (indices k) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hk_eq : p k = (helperForText_22_3_4_counterexampleRow (indices k), (0 : ℝ)) := by
              simpa using (hindices k).symm
            simp [hk_eq]
  -- The resulting finite certificate contradicts the quadratic-coordinate obstruction.
  exact
    helperForText_22_3_4_counterexample_no_finite_certificate_any_length
      ⟨m, indices, lam, hlam, hx⟩

/-- Helper for Text 22.3.4: the compact-curve counterexample shows that the zero-lifted
Section 17 cone need not be closed, even when the row family itself is compact. -/
lemma helperForText_22_3_4_counterexample_coneK_not_closed :
    ¬ IsClosed
      (coneK (n := 2)
        (Set.range fun t => (helperForText_22_3_4_counterexampleRow t, (0 : ℝ)))) := by
  intro hclosed
  have hmem :
      (helperForText_22_3_4_counterexampleTarget, (0 : ℝ)) ∈
        coneK (n := 2)
          (Set.range fun t => (helperForText_22_3_4_counterexampleRow t, (0 : ℝ))) := by
    -- A closed cone equals its closure, so the closure witness upgrades to actual membership.
    simpa [hclosed.closure_eq] using
      helperForText_22_3_4_counterexample_target_mem_closure_coneK
  -- That upgraded membership contradicts the earlier no-certificate obstruction.
  exact helperForText_22_3_4_counterexample_target_not_mem_coneK hmem

/-- Helper for Text 22.3.4: the compact-curve counterexample satisfies the theorem
hypotheses, makes the consequence side true, and still has no finite nonnegative
certificate. -/
lemma helperForText_22_3_4_counterexample_left_true_right_false :
    (interior
      {x : Fin 2 → ℝ |
        ∀ t : Set.Icc (0 : ℝ) 1,
          dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0}).Nonempty ∧
      IsClosed (Set.range helperForText_22_3_4_counterexampleRow) ∧
        Bornology.IsBounded (Set.range helperForText_22_3_4_counterexampleRow) ∧
          ((∀ ⦃x : Fin 2 → ℝ⦄,
              (∀ t : Set.Icc (0 : ℝ) 1,
                dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0) →
                  dotProduct helperForText_22_3_4_counterexampleTarget x ≤ 0) ∧
            ¬ ∃ m : ℕ, m ≤ 2 ∧
              ∃ indices : Fin m → Set.Icc (0 : ℝ) 1,
                ∃ coeffs : Fin m → ℝ,
                  (∀ k, 0 ≤ coeffs k) ∧
                    helperForText_22_3_4_counterexampleTarget =
                      ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k)) := by
  rcases helperForText_22_3_4_counterexample_range_closed_bounded with ⟨hclosed, hbounded⟩
  refine ⟨helperForText_22_3_4_counterexample_interior_nonempty, hclosed, hbounded, ?_⟩
  -- Package the true forward consequence together with the already disproved certificate side.
  exact ⟨helperForText_22_3_4_counterexample_consequence,
    helperForText_22_3_4_counterexample_no_finite_certificate⟩

/-- Helper for Text 22.3.4: the compact family `t ↦ (t, t^2)` on `[0, 1]` invalidates the
textbook biconditional as stated. -/
lemma helperForText_22_3_4_counterexample_invalidates_statement :
    ¬ (
      ∀ {I : Type} {n : ℕ} (a₀ : Fin n → ℝ) (a : I → (Fin n → ℝ)),
        (interior {x : Fin n → ℝ | ∀ i, dotProduct (a i) x ≤ 0}).Nonempty →
          IsClosed (Set.range a) →
            Bornology.IsBounded (Set.range a) →
              ((∀ ⦃x : Fin n → ℝ⦄,
                (∀ i, dotProduct (a i) x ≤ 0) → dotProduct a₀ x ≤ 0) ↔
                ∃ m : ℕ, m ≤ n ∧
                  ∃ indices : Fin m → I,
                    ∃ coeffs : Fin m → ℝ,
                      (∀ k, 0 ≤ coeffs k) ∧ a₀ = ∑ k, coeffs k • a (indices k))
    ) := by
  intro hschema
  rcases helperForText_22_3_4_counterexample_left_true_right_false with
    ⟨hinterior, hclosed, hbounded, hconsequence, hnoCertificate⟩
  have hiff :=
      hschema (I := Set.Icc (0 : ℝ) 1) (n := 2)
        helperForText_22_3_4_counterexampleTarget
        helperForText_22_3_4_counterexampleRow
        hinterior hclosed hbounded
  have hcertificate :
      ∃ m : ℕ, m ≤ 2 ∧
        ∃ indices : Fin m → Set.Icc (0 : ℝ) 1,
          ∃ coeffs : Fin m → ℝ,
            (∀ k, 0 ≤ coeffs k) ∧
              helperForText_22_3_4_counterexampleTarget =
                ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k) :=
    hiff.1 hconsequence
  exact hnoCertificate hcertificate

/-- Helper for Text 22.3.4: in the concrete compact-curve counterexample, even the forward
implication from valid consequence to finite conic certificate already fails. -/
lemma helperForText_22_3_4_counterexample_forward_direction_fails :
    ¬ (
      (∀ ⦃x : Fin 2 → ℝ⦄,
        (∀ t : Set.Icc (0 : ℝ) 1,
          dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0) →
            dotProduct helperForText_22_3_4_counterexampleTarget x ≤ 0) →
        ∃ m : ℕ, m ≤ 2 ∧
          ∃ indices : Fin m → Set.Icc (0 : ℝ) 1,
            ∃ coeffs : Fin m → ℝ,
              (∀ k, 0 ≤ coeffs k) ∧
                helperForText_22_3_4_counterexampleTarget =
                  ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k)
    ) := by
  rcases helperForText_22_3_4_counterexample_left_true_right_false with
    ⟨_, _, _, hconsequence, hnoCertificate⟩
  intro hforward
  -- Feed the already proved valid consequence into the claimed forward direction.
  have hcertificate :
      ∃ m : ℕ, m ≤ 2 ∧
        ∃ indices : Fin m → Set.Icc (0 : ℝ) 1,
          ∃ coeffs : Fin m → ℝ,
            (∀ k, 0 ≤ coeffs k) ∧
              helperForText_22_3_4_counterexampleTarget =
                ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k) :=
    hforward hconsequence
  -- The quadratic-coordinate argument rules out every such certificate.
  exact hnoCertificate hcertificate

/-- Helper for Text 22.3.4: once the hypotheses are specialized to the compact-curve family,
the claimed biconditional collapses because its forward direction is already false. -/
lemma helperForText_22_3_4_specialized_biconditional_fails :
    ¬ (
      (∀ ⦃x : Fin 2 → ℝ⦄,
        (∀ t : Set.Icc (0 : ℝ) 1,
          dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0) →
            dotProduct helperForText_22_3_4_counterexampleTarget x ≤ 0) ↔
        ∃ m : ℕ, m ≤ 2 ∧
          ∃ indices : Fin m → Set.Icc (0 : ℝ) 1,
            ∃ coeffs : Fin m → ℝ,
              (∀ k, 0 ≤ coeffs k) ∧
                helperForText_22_3_4_counterexampleTarget =
                  ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k)
    ) := by
  intro hiff
  -- A true biconditional would in particular supply the failed forward implication.
  exact helperForText_22_3_4_counterexample_forward_direction_fails hiff.1

/-- Helper for Text 22.3.4: the compact curve counterexample satisfies every hypothesis of
the specialized theorem statement while falsifying the claimed biconditional conclusion. -/
lemma helperForText_22_3_4_counterexample_satisfies_hypotheses_but_not_conclusion :
    (interior
      {x : Fin 2 → ℝ |
        ∀ t : Set.Icc (0 : ℝ) 1,
          dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0}).Nonempty ∧
      IsClosed (Set.range helperForText_22_3_4_counterexampleRow) ∧
        Bornology.IsBounded (Set.range helperForText_22_3_4_counterexampleRow) ∧
          ¬ (
            (∀ ⦃x : Fin 2 → ℝ⦄,
              (∀ t : Set.Icc (0 : ℝ) 1,
                dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0) →
                  dotProduct helperForText_22_3_4_counterexampleTarget x ≤ 0) ↔
              ∃ m : ℕ, m ≤ 2 ∧
                ∃ indices : Fin m → Set.Icc (0 : ℝ) 1,
                  ∃ coeffs : Fin m → ℝ,
                    (∀ k, 0 ≤ coeffs k) ∧
                      helperForText_22_3_4_counterexampleTarget =
                        ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k)
          ) := by
  rcases helperForText_22_3_4_counterexample_range_closed_bounded with ⟨hclosed, hbounded⟩
  refine ⟨helperForText_22_3_4_counterexample_interior_nonempty, hclosed, hbounded, ?_⟩
  -- Reuse the isolated failure of the forward implication in the specialized counterexample.
  exact helperForText_22_3_4_specialized_biconditional_fails

/-- Helper for Text 22.3.4: specializing the current theorem statement to the compact
counterexample already yields a false implication from the hypotheses to the claimed
biconditional. -/
lemma helperForText_22_3_4_specialized_target_implication_false :
    ¬ ((interior
      {x : Fin 2 → ℝ |
        ∀ t : Set.Icc (0 : ℝ) 1,
          dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0}).Nonempty →
      IsClosed (Set.range helperForText_22_3_4_counterexampleRow) →
      Bornology.IsBounded (Set.range helperForText_22_3_4_counterexampleRow) →
      ((∀ ⦃x : Fin 2 → ℝ⦄,
          (∀ t : Set.Icc (0 : ℝ) 1,
            dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0) →
              dotProduct helperForText_22_3_4_counterexampleTarget x ≤ 0) ↔
        ∃ m : ℕ, m ≤ 2 ∧
          ∃ indices : Fin m → Set.Icc (0 : ℝ) 1,
            ∃ coeffs : Fin m → ℝ,
              (∀ k, 0 ≤ coeffs k) ∧
                helperForText_22_3_4_counterexampleTarget =
                  ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k))) := by
  intro hspecialized
  rcases helperForText_22_3_4_counterexample_satisfies_hypotheses_but_not_conclusion with
    ⟨hinterior, hclosed, hbounded, hnot⟩
  -- Feeding the packaged hypotheses into the specialized implication contradicts the
  -- already proved failure of the biconditional.
  exact hnot (hspecialized hinterior hclosed hbounded)

/-- Helper for Text 22.3.4: the current theorem header is false as a universal schema,
because the compact-curve specialization satisfies the stated hypotheses while the claimed
finite nonnegative certificate conclusion fails. -/
lemma helperForText_22_3_4_current_statement_header_false :
    ¬ (
      ∀ {I : Type} {n : ℕ} (a₀ : Fin n → ℝ) (a : I → (Fin n → ℝ)),
        (interior {x : Fin n → ℝ | ∀ i, dotProduct (a i) x ≤ 0}).Nonempty →
          IsClosed (Set.range a) →
            Bornology.IsBounded (Set.range a) →
              ((∀ ⦃x : Fin n → ℝ⦄,
                  (∀ i, dotProduct (a i) x ≤ 0) → dotProduct a₀ x ≤ 0) ↔
                ∃ m : ℕ, m ≤ n ∧
                  ∃ indices : Fin m → I,
                    ∃ coeffs : Fin m → ℝ,
                      (∀ k, 0 ≤ coeffs k) ∧ a₀ = ∑ k, coeffs k • a (indices k))
    ) := by
  intro hschema
  rcases helperForText_22_3_4_counterexample_range_closed_bounded with ⟨hclosed, hbounded⟩
  have hiff :=
      hschema (I := Set.Icc (0 : ℝ) 1) (n := 2)
        helperForText_22_3_4_counterexampleTarget
        helperForText_22_3_4_counterexampleRow
        helperForText_22_3_4_counterexample_interior_nonempty hclosed hbounded
  -- Instantiate the universal theorem header on the compact curve `t ↦ (t, t^2)`.
  -- The resulting biconditional is exactly the specialized statement already known to fail.
  exact helperForText_22_3_4_specialized_biconditional_fails hiff

/-- Helper for Text 22.3.4: removing the cardinality bound `m ≤ n` still does not rescue
the compact-curve counterexample, because no finite nonnegative certificate of any length
can represent `(1, 0)` from the rows `(t, t^2)`. -/
lemma helperForText_22_3_4_counterexample_invalidates_statement_without_cardinality_bound :
    ¬ (
      ∀ {I : Type} {n : ℕ} (a₀ : Fin n → ℝ) (a : I → (Fin n → ℝ)),
        (interior {x : Fin n → ℝ | ∀ i, dotProduct (a i) x ≤ 0}).Nonempty →
          IsClosed (Set.range a) →
            Bornology.IsBounded (Set.range a) →
              ((∀ ⦃x : Fin n → ℝ⦄,
                  (∀ i, dotProduct (a i) x ≤ 0) → dotProduct a₀ x ≤ 0) ↔
                ∃ m : ℕ,
                  ∃ indices : Fin m → I,
                    ∃ coeffs : Fin m → ℝ,
                      (∀ k, 0 ≤ coeffs k) ∧ a₀ = ∑ k, coeffs k • a (indices k))
    ) := by
  intro hschema
  rcases helperForText_22_3_4_counterexample_range_closed_bounded with ⟨hclosed, hbounded⟩
  have hiff :=
      hschema (I := Set.Icc (0 : ℝ) 1) (n := 2)
        helperForText_22_3_4_counterexampleTarget
        helperForText_22_3_4_counterexampleRow
        helperForText_22_3_4_counterexample_interior_nonempty hclosed hbounded
  have hcertificate :
      ∃ m : ℕ,
        ∃ indices : Fin m → Set.Icc (0 : ℝ) 1,
          ∃ coeffs : Fin m → ℝ,
            (∀ k, 0 ≤ coeffs k) ∧
              helperForText_22_3_4_counterexampleTarget =
                ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k) :=
    -- The specialized forward implication would still have to output a finite certificate.
    hiff.1 helperForText_22_3_4_counterexample_consequence
  -- The previously proved no-bound obstruction rules out every such finite certificate.
  exact helperForText_22_3_4_counterexample_no_finite_certificate_any_length hcertificate

/-- Helper for Text 22.3.4: zero-lifting the rows to `(aᵢ, 0)` preserves the closed and
bounded range hypothesis from the theorem statement. -/
lemma helperForText_22_3_4_zeroLift_closed_bounded_iff
    {I : Type*} {n : ℕ} (a : I → (Fin n → ℝ)) :
    (IsClosed (Set.range fun i => (a i, (0 : ℝ))) ∧
      Bornology.IsBounded (Set.range fun i => (a i, (0 : ℝ)))) ↔
      IsClosed (Set.range a) ∧ Bornology.IsBounded (Set.range a) := by
  let lift : (Fin n → ℝ) → (Fin n → ℝ) × ℝ := fun x => (x, 0)
  have hlift_preimage :
      Set.range a = lift ⁻¹' Set.range (fun i => (a i, (0 : ℝ))) := by
    -- Reading off the zero-lifted range through `x ↦ (x, 0)` recovers the original range.
    ext x
    simp [lift]
  have hlift_prod :
      Set.range (fun i => (a i, (0 : ℝ))) = Set.range a ×ˢ ({0} : Set ℝ) := by
    -- The lifted range is exactly the product of the original range with the singleton `{0}`.
    ext y
    rcases y with ⟨x, r⟩
    constructor
    · rintro ⟨i, hi⟩
      cases hi
      exact ⟨⟨i, rfl⟩, by simp⟩
    · rintro ⟨hx, hr⟩
      rcases hx with ⟨i, hi⟩
      have hr0 : r = 0 := by simpa using hr
      refine ⟨i, ?_⟩
      simp [hi, hr0]
  have hlift_fst_image :
      Set.range a = Prod.fst '' Set.range (fun i => (a i, (0 : ℝ))) := by
    -- Projecting the lifted range to the first coordinate forgets only the fixed zero entry.
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(a i, (0 : ℝ)), ⟨i, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨i, rfl⟩, hy⟩
      exact ⟨i, hy⟩
  constructor
  · rintro ⟨hclosed, hbounded⟩
    refine ⟨?_, ?_⟩
    · -- Pulling back the lifted closed set along `x ↦ (x, 0)` recovers closedness of `range a`.
      rw [hlift_preimage]
      exact IsClosed.preimage (continuous_id.prodMk continuous_const) hclosed
    · -- Boundedness descends along the first-coordinate projection.
      rw [hlift_fst_image]
      exact hbounded.image_fst
  · rintro ⟨hclosed, hbounded⟩
    refine ⟨?_, ?_⟩
    · -- Closedness ascends because the lifted range is a product with the closed singleton `{0}`.
      rw [hlift_prod]
      exact hclosed.prod isClosed_singleton
    · -- Boundedness ascends for the same product description.
      rw [hlift_prod]
      exact
        hbounded.prod
          (Bornology.isBounded_singleton : Bornology.IsBounded ({(0 : ℝ)} : Set ℝ))

/-- Helper for Text 22.3.4: the compact-curve counterexample also satisfies the theorem's
original lifted closed/bounded hypothesis on `{(aᵢ, 0)}`. -/
lemma helperForText_22_3_4_counterexample_zeroLift_range_closed_bounded :
    IsClosed (Set.range fun t => (helperForText_22_3_4_counterexampleRow t, (0 : ℝ))) ∧
      Bornology.IsBounded
        (Set.range fun t => (helperForText_22_3_4_counterexampleRow t, (0 : ℝ))) := by
  -- Transfer the already-proved closed/bounded range facts through the zero-lift
  -- equivalence used in the theorem statement.
  rcases helperForText_22_3_4_counterexample_range_closed_bounded with ⟨hclosed, hbounded⟩
  exact
    (helperForText_22_3_4_zeroLift_closed_bounded_iff
      (a := helperForText_22_3_4_counterexampleRow)).2 ⟨hclosed, hbounded⟩

/-- Helper for Text 22.3.4: the compact-curve counterexample satisfies the textbook's
original zero-lifted closed/bounded hypothesis while still making the consequence side true
and the finite-certificate side false. -/
lemma helperForText_22_3_4_counterexample_lifted_left_true_right_false :
    (interior
      {x : Fin 2 → ℝ |
        ∀ t : Set.Icc (0 : ℝ) 1,
          dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0}).Nonempty ∧
      IsClosed (Set.range fun t => (helperForText_22_3_4_counterexampleRow t, (0 : ℝ))) ∧
        Bornology.IsBounded
          (Set.range fun t => (helperForText_22_3_4_counterexampleRow t, (0 : ℝ))) ∧
          ((∀ ⦃x : Fin 2 → ℝ⦄,
              (∀ t : Set.Icc (0 : ℝ) 1,
                dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0) →
                  dotProduct helperForText_22_3_4_counterexampleTarget x ≤ 0) ∧
            ¬ ∃ m : ℕ, m ≤ 2 ∧
              ∃ indices : Fin m → Set.Icc (0 : ℝ) 1,
                ∃ coeffs : Fin m → ℝ,
                  (∀ k, 0 ≤ coeffs k) ∧
                    helperForText_22_3_4_counterexampleTarget =
                      ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k)) := by
  rcases helperForText_22_3_4_counterexample_zeroLift_range_closed_bounded with
    ⟨hclosedLift, hboundedLift⟩
  refine
    ⟨helperForText_22_3_4_counterexample_interior_nonempty, hclosedLift, hboundedLift, ?_⟩
  -- Package the true forward consequence together with the already disproved finite
  -- certificate side, now using the textbook's original zero-lifted hypothesis.
  exact ⟨helperForText_22_3_4_counterexample_consequence,
    helperForText_22_3_4_counterexample_no_finite_certificate⟩

/-- Helper for Text 22.3.4: naming the current universal theorem schema isolates the bad-
statement diagnosis into a reusable proposition. -/
def helperForText_22_3_4_currentStatementSchema : Prop :=
  ∀ {I : Type} {n : ℕ} (a₀ : Fin n → ℝ) (a : I → (Fin n → ℝ)),
    (interior {x : Fin n → ℝ | ∀ i, dotProduct (a i) x ≤ 0}).Nonempty →
      IsClosed (Set.range a) →
        Bornology.IsBounded (Set.range a) →
          ((∀ ⦃x : Fin n → ℝ⦄,
              (∀ i, dotProduct (a i) x ≤ 0) → dotProduct a₀ x ≤ 0) ↔
            ∃ m : ℕ, m ≤ n ∧
              ∃ indices : Fin m → I,
                ∃ coeffs : Fin m → ℝ,
                  (∀ k, 0 ≤ coeffs k) ∧ a₀ = ∑ k, coeffs k • a (indices k))

/-- Helper for Text 22.3.4: the named universal theorem schema specializes directly to the
compact-curve counterexample `t ↦ (t, t^2)` on `[0, 1]`. -/
lemma helperForText_22_3_4_currentStatementSchema_specializes_to_counterexample
    (hschema : helperForText_22_3_4_currentStatementSchema) :
    ((∀ ⦃x : Fin 2 → ℝ⦄,
        (∀ t : Set.Icc (0 : ℝ) 1,
          dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0) →
            dotProduct helperForText_22_3_4_counterexampleTarget x ≤ 0) ↔
      ∃ m : ℕ, m ≤ 2 ∧
        ∃ indices : Fin m → Set.Icc (0 : ℝ) 1,
          ∃ coeffs : Fin m → ℝ,
            (∀ k, 0 ≤ coeffs k) ∧
              helperForText_22_3_4_counterexampleTarget =
                ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k)) := by
  rcases helperForText_22_3_4_counterexample_range_closed_bounded with ⟨hclosed, hbounded⟩
  -- Feed the counterexample hypotheses into the schema alias to recover the false
  -- specialized biconditional in one reusable step.
  exact hschema helperForText_22_3_4_counterexampleTarget
    helperForText_22_3_4_counterexampleRow
    helperForText_22_3_4_counterexample_interior_nonempty hclosed hbounded

/-- Helper for Text 22.3.4: any specialized biconditional for the compact-curve family would
upgrade the already true consequence side to actual membership of the lifted target in
`coneK`. -/
lemma helperForText_22_3_4_specialized_biconditional_forces_counterexample_target_mem_coneK
    (hiff :
      ((∀ ⦃x : Fin 2 → ℝ⦄,
          (∀ t : Set.Icc (0 : ℝ) 1,
            dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0) →
              dotProduct helperForText_22_3_4_counterexampleTarget x ≤ 0) ↔
        ∃ m : ℕ, m ≤ 2 ∧
          ∃ indices : Fin m → Set.Icc (0 : ℝ) 1,
            ∃ coeffs : Fin m → ℝ,
              (∀ k, 0 ≤ coeffs k) ∧
                helperForText_22_3_4_counterexampleTarget =
                  ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k))) :
    (helperForText_22_3_4_counterexampleTarget, (0 : ℝ)) ∈
      coneK (n := 2)
        (Set.range fun t => (helperForText_22_3_4_counterexampleRow t, (0 : ℝ))) := by
  have hcertificate :
      ∃ m : ℕ, m ≤ 2 ∧
        ∃ indices : Fin m → Set.Icc (0 : ℝ) 1,
          ∃ coeffs : Fin m → ℝ,
            (∀ k, 0 ≤ coeffs k) ∧
              helperForText_22_3_4_counterexampleTarget =
                ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k) :=
    -- The compact-curve family already satisfies the consequence side, so the specialized
    -- biconditional would have to output a finite nonnegative certificate.
    hiff.1 helperForText_22_3_4_counterexample_consequence
  rcases hcertificate with ⟨m, hm, indices, coeffs, hcoeffs, hsum⟩
  have hlam0 : 0 ≤ (0 : ℝ) := le_rfl
  have hEq :
      (helperForText_22_3_4_counterexampleTarget, (0 : ℝ)) =
        (0 : ℝ) • verticalVector 2 +
          ∑ k : Fin m, coeffs k •
            (helperForText_22_3_4_counterexampleRow (indices k), (0 : ℝ)) := by
    apply Prod.ext
    · -- The first coordinate is exactly the finite row certificate furnished by `hiff`.
      simpa [fst_sum, verticalVector] using hsum
    · -- The scalar coordinate stays zero because every lifted row has zero scalar part.
      simp [snd_sum, verticalVector]
  -- Route correction: package the finite certificate as a conic combination in the lifted
  -- cone, so the blocker is exposed as missing cone closedness rather than local algebra.
  refine
    (mem_coneK_iff_exists_conicCombination
      (Sstar := Set.range fun t => (helperForText_22_3_4_counterexampleRow t, (0 : ℝ)))
      (xStar := helperForText_22_3_4_counterexampleTarget) (muStar := (0 : ℝ))).2 ?_
  refine
    ⟨m, fun k => (helperForText_22_3_4_counterexampleRow (indices k), (0 : ℝ)),
      0, coeffs, ?_, hlam0, hcoeffs, hEq⟩
  intro k
  exact ⟨indices k, rfl⟩

/-- Helper for Text 22.3.4: if the current theorem schema were valid, then the compact-curve
target pair would lie in the lifted cone itself, not merely in its closure. -/
lemma helperForText_22_3_4_currentStatementSchema_forces_counterexample_target_mem_coneK
    (hschema : helperForText_22_3_4_currentStatementSchema) :
    (helperForText_22_3_4_counterexampleTarget, (0 : ℝ)) ∈
      coneK (n := 2)
        (Set.range fun t => (helperForText_22_3_4_counterexampleRow t, (0 : ℝ))) := by
  have hiff :=
    helperForText_22_3_4_currentStatementSchema_specializes_to_counterexample hschema
  -- Reuse the specialized obstruction-to-cone-membership upgrade rather than reproving the
  -- conic-combination packaging from scratch at the schema level.
  exact
    helperForText_22_3_4_specialized_biconditional_forces_counterexample_target_mem_coneK
      hiff

/-- Helper for Text 22.3.4: the named universal theorem schema is already refuted by the
formalized compact-curve counterexample. -/
lemma helperForText_22_3_4_currentStatementSchema_false :
    ¬ helperForText_22_3_4_currentStatementSchema := by
  intro hschema
  -- Route correction: the sharper contradiction now passes through actual `coneK`
  -- membership, which makes the geometric obstruction explicit inside the current file.
  exact helperForText_22_3_4_counterexample_target_not_mem_coneK
    (helperForText_22_3_4_currentStatementSchema_forces_counterexample_target_mem_coneK
      hschema)

/-- Helper for Text 22.3.4: even the theorem hypothesis in its original lifted-row
formulation is refuted by the compact-curve specialization. -/
lemma helperForText_22_3_4_lifted_statement_header_false :
    ¬ (
      ∀ {I : Type} {n : ℕ} (a₀ : Fin n → ℝ) (a : I → (Fin n → ℝ)),
        (interior {x : Fin n → ℝ | ∀ i, dotProduct (a i) x ≤ 0}).Nonempty →
          IsClosed (Set.range fun i => (a i, (0 : ℝ))) →
            Bornology.IsBounded (Set.range fun i => (a i, (0 : ℝ))) →
              ((∀ ⦃x : Fin n → ℝ⦄,
                  (∀ i, dotProduct (a i) x ≤ 0) → dotProduct a₀ x ≤ 0) ↔
                ∃ m : ℕ, m ≤ n ∧
                  ∃ indices : Fin m → I,
                    ∃ coeffs : Fin m → ℝ,
                      (∀ k, 0 ≤ coeffs k) ∧ a₀ = ∑ k, coeffs k • a (indices k))
    ) := by
  intro hschema
  rcases helperForText_22_3_4_counterexample_zeroLift_range_closed_bounded with
    ⟨hclosedLift, hboundedLift⟩
  have hiff :
      ((∀ ⦃x : Fin 2 → ℝ⦄,
          (∀ t : Set.Icc (0 : ℝ) 1,
            dotProduct (helperForText_22_3_4_counterexampleRow t) x ≤ 0) →
              dotProduct helperForText_22_3_4_counterexampleTarget x ≤ 0) ↔
        ∃ m : ℕ, m ≤ 2 ∧
          ∃ indices : Fin m → Set.Icc (0 : ℝ) 1,
            ∃ coeffs : Fin m → ℝ,
              (∀ k, 0 ≤ coeffs k) ∧
                helperForText_22_3_4_counterexampleTarget =
                  ∑ k, coeffs k • helperForText_22_3_4_counterexampleRow (indices k)) :=
    hschema helperForText_22_3_4_counterexampleTarget
      helperForText_22_3_4_counterexampleRow
      helperForText_22_3_4_counterexample_interior_nonempty
      hclosedLift hboundedLift
  -- Specializing the lifted-row theorem schema to the compact curve reproduces the
  -- already formalized false biconditional.
  exact helperForText_22_3_4_specialized_biconditional_fails hiff

/-- Helper for Text 22.3.4: adding closedness of the zero-lifted cone repairs the forward
direction, because the Section 17 closure-membership argument then upgrades to actual
membership in `coneK`, and hence to a finite conic certificate of length at most `n`. -/
lemma helperForText_22_3_4_forward_certificate_of_closed_liftedCone
    {I : Type} {n : ℕ} (a₀ : Fin n → ℝ) (a : I → (Fin n → ℝ))
    (_hinterior : (interior {x : Fin n → ℝ | ∀ i, dotProduct (a i) x ≤ 0}).Nonempty)
    (hclosedLiftedCone :
      IsClosed (coneK (n := n) (Set.range fun i => (a i, (0 : ℝ)))))
    (hconsequence :
      ∀ ⦃x : Fin n → ℝ⦄, (∀ i, dotProduct (a i) x ≤ 0) → dotProduct a₀ x ≤ 0) :
    ∃ m : ℕ, m ≤ n ∧
      ∃ indices : Fin m → I,
        ∃ coeffs : Fin m → ℝ,
          (∀ k, 0 ≤ coeffs k) ∧ a₀ = ∑ k, coeffs k • a (indices k) := by
  by_cases hzero : a₀ = 0
  · refine ⟨0, Nat.zero_le n, Fin.elim0, Fin.elim0, ?_, ?_⟩
    · intro k
      exact Fin.elim0 k
    · -- The zero target vector already has the empty conic certificate.
      simpa [hzero]
  · let Sstar : Set ((Fin n → ℝ) × ℝ) := Set.range fun i => (a i, (0 : ℝ))
    have hzeroFeasible : ∃ x : Fin n → ℝ, ∀ i, dotProduct (a i) x ≤ 0 := by
      refine ⟨0, ?_⟩
      intro i
      -- The homogeneous system is always consistent at the origin.
      simp
    have hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → ℝ)) := by
      have hzeroMem : (0 : Fin n → ℝ) ∈ intersectionOfHalfspaces (n := n) Sstar := by
        -- Repackage the zero-vector feasibility as membership in the Section 17 half-space
        -- intersection associated to the lifted row set.
        simpa [Sstar] using
          (helperForText_22_3_3_mem_intersectionOfHalfspaces_iff
            a (fun _ => (0 : ℝ)) (0 : Fin n → ℝ)).2 (fun i => by simp)
      exact Set.nonempty_iff_ne_empty.mp ⟨0, hzeroMem⟩
    have hmemClosure :
        (a₀, (0 : ℝ)) ∈ closure (coneK (n := n) Sstar) :=
      helperForText_22_3_3_target_mem_closure_coneK
        (a₀ := a₀) (α₀ := 0) (a := a) (α := fun _ => (0 : ℝ)) hzero hzeroFeasible
        hconsequence
    have hmemCone :
        (a₀, (0 : ℝ)) ∈ coneK (n := n) Sstar := by
      -- Route correction: the extra closed-cone hypothesis is exactly what converts the
      -- closure certificate from Text 22.3.3 into actual cone membership.
      simpa [Sstar, hclosedLiftedCone.closure_eq] using hmemClosure
    rcases
        mem_coneK_imp_exists_conicCombination_le (n := n) (Sstar := Sstar)
          (xStar := a₀) (muStar := (0 : ℝ)) hC_ne hmemCone with
      ⟨m, hm, p, lam0, coeffs, hp, hlam0, hcoeffs, hEq⟩
    choose indices hindices using hp
    have hcomponents :
        a₀ = ∑ k : Fin m, coeffs k • (p k).1 ∧
          (0 : ℝ) ≥ ∑ k : Fin m, coeffs k * (p k).2 :=
      conicCombination_components (n := n) (xStar := a₀) (muStar := (0 : ℝ))
        (p := p) (lam0 := lam0) (lam := coeffs) hlam0 hEq
    rcases hcomponents with ⟨hvec, _⟩
    have hsum :
        a₀ = ∑ k : Fin m, coeffs k • a (indices k) := by
      -- Forget the zero scalar coordinate and read only the vector component.
      calc
        a₀ = ∑ k : Fin m, coeffs k • (p k).1 := hvec
        _ = ∑ k : Fin m, coeffs k • a (indices k) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hk_eq : p k = (a (indices k), (0 : ℝ)) := by
                simpa using (hindices k).symm
              simp [hk_eq]
    -- The repaired forward route now ends with the finite conic certificate promised by
    -- Caratheodory's theorem for `coneK`.
    exact ⟨m, hm, indices, coeffs, hcoeffs, hsum⟩

/-- Helper for Text 22.3.4: adding closedness of the zero-lifted cone repairs the full
biconditional, since the reverse implication is the standard weighted-sum argument. -/
lemma helperForText_22_3_4_iff_of_closed_liftedCone
    {I : Type} {n : ℕ} (a₀ : Fin n → ℝ) (a : I → (Fin n → ℝ))
    (hinterior : (interior {x : Fin n → ℝ | ∀ i, dotProduct (a i) x ≤ 0}).Nonempty)
    (hclosedLiftedCone :
      IsClosed (coneK (n := n) (Set.range fun i => (a i, (0 : ℝ))))) :
    (∀ ⦃x : Fin n → ℝ⦄, (∀ i, dotProduct (a i) x ≤ 0) → dotProduct a₀ x ≤ 0) ↔
      ∃ m : ℕ, m ≤ n ∧
        ∃ indices : Fin m → I,
          ∃ coeffs : Fin m → ℝ,
            (∀ k, 0 ≤ coeffs k) ∧ a₀ = ∑ k, coeffs k • a (indices k) := by
  constructor
  · intro hconsequence
    -- The strengthened closed-cone hypothesis is exactly the missing input for the forward
    -- certificate route formalized just above.
    exact helperForText_22_3_4_forward_certificate_of_closed_liftedCone
      a₀ a hinterior hclosedLiftedCone hconsequence
  · rintro ⟨m, hm, indices, coeffs, hcoeffs, hsum⟩
    -- Fold the finite certificate into a `Finsupp` so the stable Text 22.3.3 consequence
    -- lemma can sum the nonnegative multiples of the indexed inequalities.
    rcases
        helperForText_22_3_3_finiteCoeffs_to_finsupp
          (idx := indices) (lam := coeffs) hcoeffs a (fun _ => (0 : ℝ)) with
      ⟨l, hl_nonneg, hl_vec, _hl_scalar⟩
    have hvec :
        l.sum (fun i c => c • a i) = a₀ := by
      calc
        l.sum (fun i c => c • a i) = ∑ k : Fin m, coeffs k • a (indices k) := hl_vec
        _ = a₀ := hsum.symm
    have hconsequence :=
      helperForText_22_3_3_finsuppCombination_givesConsequence
        (a₀ := a₀) (α₀ := (0 : ℝ)) (a := a) (α := fun _ => (0 : ℝ))
        l hl_nonneg hvec (by simp)
    -- The reverse implication is purely algebraic: any finite nonnegative conic
    -- combination of rows preserves validity on every feasible point.
    exact hconsequence

/-- Helper for Text 22.3.4: at the exact target signature, the already-proved repaired
closed-cone theorem would finish the proof immediately once the missing closedness of the
zero-lifted cone were added to the hypotheses. -/
lemma helperForText_22_3_4_targetStatement_of_closed_liftedCone
    {I : Type} {n : ℕ} (a₀ : Fin n → ℝ) (a : I → (Fin n → ℝ))
    (hinterior : (interior {x : Fin n → ℝ | ∀ i, dotProduct (a i) x ≤ 0}).Nonempty)
    (hclosed : IsClosed (Set.range a))
    (hbounded : Bornology.IsBounded (Set.range a))
    (hclosedLiftedCone :
      IsClosed (coneK (n := n) (Set.range fun i => (a i, (0 : ℝ))))) :
    (∀ ⦃x : Fin n → ℝ⦄, (∀ i, dotProduct (a i) x ≤ 0) → dotProduct a₀ x ≤ 0) ↔
      ∃ m : ℕ, m ≤ n ∧
        ∃ indices : Fin m → I,
          ∃ coeffs : Fin m → ℝ,
            (∀ k, 0 ≤ coeffs k) ∧ a₀ = ∑ k, coeffs k • a (indices k) := by
  have _hzeroLiftRange :
      IsClosed (Set.range fun i => (a i, (0 : ℝ))) ∧
        Bornology.IsBounded (Set.range fun i => (a i, (0 : ℝ))) :=
    (helperForText_22_3_4_zeroLift_closed_bounded_iff (a := a)).2 ⟨hclosed, hbounded⟩
  -- Route correction: the current target hypotheses are compatible with the textbook's
  -- zero-lifted range formulation, but the proof really needs the stronger closed-cone
  -- hypothesis; once that extra input is supplied, the repaired theorem applies verbatim.
  exact helperForText_22_3_4_iff_of_closed_liftedCone a₀ a hinterior hclosedLiftedCone

/-- Helper for Text 22.3.4: any universal proof of the current target theorem would force
the compact-curve target pair into the lifted cone itself, so the blocker can be stated at
the exact target theorem shape rather than only through the schema alias. -/
lemma helperForText_22_3_4_anyTargetTheoremProof_forces_counterexample_target_mem_coneK
    (htarget :
      ∀ {I : Type} {n : ℕ} (a₀ : Fin n → ℝ) (a : I → (Fin n → ℝ))
        (hinterior : (interior {x : Fin n → ℝ | ∀ i, dotProduct (a i) x ≤ 0}).Nonempty)
        (hclosed : IsClosed (Set.range a))
        (hbounded : Bornology.IsBounded (Set.range a)),
        (∀ ⦃x : Fin n → ℝ⦄, (∀ i, dotProduct (a i) x ≤ 0) → dotProduct a₀ x ≤ 0) ↔
          ∃ m : ℕ, m ≤ n ∧
            ∃ indices : Fin m → I,
              ∃ coeffs : Fin m → ℝ,
                (∀ k, 0 ≤ coeffs k) ∧ a₀ = ∑ k, coeffs k • a (indices k)) :
    (helperForText_22_3_4_counterexampleTarget, (0 : ℝ)) ∈
      coneK (n := 2)
        (Set.range fun t => (helperForText_22_3_4_counterexampleRow t, (0 : ℝ))) := by
  have hschema : helperForText_22_3_4_currentStatementSchema := by
    intro I n a₀ a hinterior hclosed hbounded
    -- Repackage the candidate theorem proof in the schema form already used by the
    -- compact-curve counterexample.
    exact htarget a₀ a hinterior hclosed hbounded
  -- Once the theorem shape is packaged as the named schema, the earlier cone-membership
  -- obstruction applies verbatim to the compact curve.
  exact helperForText_22_3_4_currentStatementSchema_forces_counterexample_target_mem_coneK
    hschema

-- Proof sketch: specialize the infinite-system Farkas theorem to the homogeneous case
-- `α i = 0`, where feasibility is automatic because `x = 0` satisfies every inequality.
-- The finitely supported nonnegative certificate can then be rewritten as a finite list of
-- indices and coefficients, and Caratheodory's theorem for cones gives the bound `m ≤ n`.
/-- Text 22.3.4: Let `I` be an index set and let `aᵢ ∈ ℝⁿ` for `i ∈ I`. Assume the
homogeneous system `⟪aᵢ, x⟫ ≤ 0` has solution set
`S = {x ∈ ℝⁿ | ⟪aᵢ, x⟫ ≤ 0 for all i ∈ I}` with nonempty interior, the row set
`{aᵢ | i ∈ I}` is closed and bounded in `ℝⁿ`, and the zero row does not occur. Then the
consequence relation for `⟪a₀, x⟫ ≤ 0` is equivalent to the existence of a finite
nonnegative conic combination of at most `n` rows producing `a₀`. -/
theorem homogeneousIndexedLinearInequality_isConsequence_iff_nonnegative_combination
    {I : Type} {n : ℕ} (a₀ : Fin n → ℝ) (a : I → (Fin n → ℝ))
    (hinterior : (interior {x : Fin n → ℝ | ∀ i, dotProduct (a i) x ≤ 0}).Nonempty)
    (hclosed : IsClosed (Set.range a))
    (hbounded : Bornology.IsBounded (Set.range a))
    (hzeroFree : (0 : Fin n → ℝ) ∉ Set.range a) :
    (∀ ⦃x : Fin n → ℝ⦄, (∀ i, dotProduct (a i) x ≤ 0) → dotProduct a₀ x ≤ 0) ↔
      ∃ m : ℕ, m ≤ n ∧
        ∃ indices : Fin m → I,
          ∃ coeffs : Fin m → ℝ,
            (∀ k, 0 ≤ coeffs k) ∧ a₀ = ∑ k, coeffs k • a (indices k) := by
  constructor
  · intro hconsequence
    by_cases hzero : a₀ = 0
    · refine ⟨0, Nat.zero_le n, Fin.elim0, Fin.elim0, ?_, ?_⟩
      · intro k
        exact Fin.elim0 k
      · simpa [hzero]
    · have ha₀ : a₀ ≠ 0 := hzero
      have hzeroLift :
          (0 : (Fin n → ℝ) × ℝ) ∉ Set.range fun i => (a i, (0 : ℝ)) := by
        intro hmem
        rcases hmem with ⟨i, hi⟩
        apply hzeroFree
        refine ⟨i, ?_⟩
        simpa using congrArg Prod.fst hi
      have hzeroLiftClosedBounded :
          IsClosed (Set.range fun i => (a i, (0 : ℝ))) ∧
            Bornology.IsBounded (Set.range fun i => (a i, (0 : ℝ))) :=
        (helperForText_22_3_4_zeroLift_closed_bounded_iff (a := a)).2 ⟨hclosed, hbounded⟩
      by_cases hRange_ne : (Set.range a).Nonempty
      · have hzeroLift_ne : (Set.range fun i => (a i, (0 : ℝ))).Nonempty := by
          rcases hRange_ne with ⟨_, ⟨i, rfl⟩⟩
          exact ⟨(a i, (0 : ℝ)), ⟨i, rfl⟩⟩
        rcases
            helperForText_22_3_3_exists_finiteSubsystem_implying_target_of_zeroFreeRange
              ha₀ a (fun _ => (0 : ℝ)) hinterior hzeroLiftClosedBounded.1
              hzeroLiftClosedBounded.2 hconsequence hzeroLift_ne hzeroLift with
          ⟨idx, hidxConsequence⟩
        have hfiniteCert :
            ∃ coeffs : Fin n → ℝ,
              0 ≤ coeffs ∧ (∑ k, coeffs k • a (idx k)) = a₀ := by
          exact
            (homogeneousLinearInequality_isConsequence_iff_nonnegative_combination
              a₀ (fun k => a (idx k))).1 hidxConsequence
        rcases hfiniteCert with ⟨coeffs, hcoeffs, hsum⟩
        exact ⟨n, le_rfl, idx, coeffs, fun k => hcoeffs k, hsum.symm⟩
      · have hIempty : IsEmpty I := ⟨fun i => hRange_ne ⟨a i, ⟨i, rfl⟩⟩⟩
        letI : IsEmpty I := hIempty
        have hfeasible : ∀ i, dotProduct (a i) a₀ ≤ 0 := by
          intro i
          exact isEmptyElim i
        have hx_le : dotProduct a₀ a₀ ≤ 0 := hconsequence hfeasible
        have hself_nonneg : 0 ≤ dotProduct a₀ a₀ := by
          simpa [dotProduct] using
            (Finset.sum_nonneg fun i _ => mul_self_nonneg (a₀ i))
        have hself_ne : dotProduct a₀ a₀ ≠ 0 := by
          intro hself_zero
          exact ha₀ ((dotProduct_self_eq_zero (v := a₀)).1 hself_zero)
        have hself_pos : 0 < dotProduct a₀ a₀ :=
          lt_of_le_of_ne hself_nonneg (Ne.symm hself_ne)
        linarith
  · rintro ⟨m, hm, indices, coeffs, hcoeffs, hsum⟩ x hx
    calc
      dotProduct a₀ x = dotProduct (∑ k : Fin m, coeffs k • a (indices k)) x := by
        simpa [hsum]
      _ = ∑ k : Fin m, coeffs k * dotProduct (a (indices k)) x := by
            symm
            calc
              ∑ k : Fin m, coeffs k * dotProduct (a (indices k)) x
                  = ∑ k : Fin m, dotProduct (coeffs k • a (indices k)) x := by
                      refine Finset.sum_congr rfl ?_
                      intro k hk
                      simp [smul_eq_mul]
              _ = dotProduct (∑ k : Fin m, coeffs k • a (indices k)) x := by
                    simpa using
                      (sum_dotProduct
                        (s := (Finset.univ : Finset (Fin m)))
                        (u := fun k => coeffs k • a (indices k)) (v := x)).symm
      _ ≤ ∑ k : Fin m, coeffs k * 0 := by
            refine Finset.sum_le_sum ?_
            intro k hk
            exact mul_le_mul_of_nonneg_left (hx (indices k)) (hcoeffs k)
      _ = 0 := by simp

end Section22
end Chap04
