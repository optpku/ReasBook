/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_8
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_15
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_9
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_24
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_30

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp (toLp)
open scoped BigOperators

noncomputable section

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "F" =>
  (PiLp.separableSum (fun _ : ι ↦ negative_log_barrier) : E → EReal)

/-- The finite-product negative-log barrier evaluated on the `PiLp` model of Euclidean space. -/
private theorem piLp_sum_negative_log_barrier_apply (x : E) :
    F x =
      if ∀ i, 0 < x i then ((-∑ i, Real.log (x i) : ℝ) : EReal) else ⊤ := by
  classical
  by_cases hx : ∀ i, 0 < x i
  · rw [if_pos hx, PiLp.separableSum_apply]
    calc
      (∑ i, negative_log_barrier (x i)) =
          ∑ i, ((-Real.log (x i) : ℝ) : EReal) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact negative_log_barrier_of_pos (hx i)
      _ = (((∑ i, -Real.log (x i) : ℝ)) : EReal) := by
            symm
            simpa using
              (ereal_coe_finset_sum Finset.univ (fun i : ι ↦ -Real.log (x i)))
      _ = ((-∑ i, Real.log (x i) : ℝ) : EReal) := by
            congr 1
            simp [Finset.sum_neg_distrib]
  · rw [if_neg hx, PiLp.separableSum_apply]
    obtain ⟨i, hi⟩ := not_forall.mp hx
    have hrest_ne_bot :
        Finset.sum (Finset.univ.erase i) (fun j ↦ negative_log_barrier (x j)) ≠ ⊥ := by
      exact finset_ereal_sum_ne_bot (Finset.univ.erase i)
        (fun j ↦ negative_log_barrier (x j)) (fun j hj ↦ by
          by_cases hj' : 0 < x j
          · simp [negative_log_barrier, hj']
          · simp [negative_log_barrier, hj'])
    calc
      (∑ j, negative_log_barrier (x j)) =
          negative_log_barrier (x i) +
            Finset.sum (Finset.univ.erase i) (fun j ↦ negative_log_barrier (x j)) := by
              symm
              exact Finset.add_sum_erase (s := Finset.univ) (a := i)
                (fun j ↦ negative_log_barrier (x j)) (Finset.mem_univ i)
      _ = ⊤ := by
            rw [negative_log_barrier_of_nonpos (le_of_not_gt hi)]
            exact EReal.top_add_of_ne_bot hrest_ne_bot

/- Example 6.35 is `source-facing`: its public object is the positive-product feasible set
`{x ∈ (ℝ_{++})^ι | α ≤ ∏ i, x i}`, specializing to the textbook `ℝ_{++}^n` when `ι = Fin n`.
Domain sampling against Proposition 4.8, Example 6.9, and Theorem 6.30 shows that the
`core/canonical` owners already upstream are the scalar `negative_log_barrier`, its finite-product
owner `F`, the Chapter 4 finite-sum theorem `sum_negative_log_barrier_apply`, the projection owner
`P[...]`, and the level-set residual owner `level_set_projection_residual` from Theorem 6.30.
Primitive data: the source-facing set. Derived API: the textbook `-∑ log` barrier formula and the
explicit active-branch scalar equation, expressed as a theorem evaluating the canonical residual
rather than as a second local root-function owner. -/

/-- The positive-product superlevel set
`{x ∈ (ℝ_{++})^ι | α ≤ ∏ i, x i}` from the projection example, specializing to the textbook
`{x ∈ ℝ_{++}^n | α ≤ ∏ i, x i}` when `ι = Fin n`. -/
def positiveProductSuperlevelSet (α : ℝ) : Set E :=
  {x | (∀ i, 0 < x i) ∧ α ≤ ∏ i, x i}

/-- A vector belongs to `positiveProductSuperlevelSet α` exactly when all of its coordinates are
positive and its coordinate product is at least `α`. -/
@[simp]
theorem mem_positiveProductSuperlevelSet_iff (α : ℝ) (x : E) :
    x ∈ positiveProductSuperlevelSet α ↔
      (∀ i, 0 < x i) ∧ α ≤ ∏ i, x i :=
  Iff.rfl

/-- Helper for Example 6.35: the effective domain of the separable-sum negative-log barrier is
exactly the positive orthant. -/
theorem mem_effective_domain_separableSum_negative_log_barrier_iff (x : E) :
    x ∈ effective_domain F ↔ ∀ i, 0 < x i := by
  -- The finite separable barrier is finite exactly when every coordinate stays on the positive
  -- ray.
  have hsum :
      F x =
        if ∀ i, 0 < x i then ((-∑ i, Real.log (x i) : ℝ) : EReal) else ⊤ := by
    exact piLp_sum_negative_log_barrier_apply x
  rw [mem_effective_domain, hsum]
  by_cases hx : ∀ i, 0 < x i
  · simpa [hx] using (EReal.coe_lt_top (-∑ i, Real.log (x i)))
  · simp [hx]

/-- Helper for Example 6.35: each coordinate of the active proximal point is strictly positive for
the positive multiplier branch. -/
theorem activePoint_coordinate_pos (x : E) (lam : PosReal) (j : ι) :
    0 < (x j + Real.sqrt (x j ^ (2 : ℕ) + 4 * (lam : ℝ))) / 2 := by
  -- The square root dominates `-x j` because the radicand is strictly larger than `x j^2`.
  have hsq :
      x j ^ (2 : ℕ) < x j ^ (2 : ℕ) + 4 * (lam : ℝ) := by
    have hfourlam : 0 < 4 * (lam : ℝ) := by
      exact mul_pos (by norm_num) lam.2
    linarith
  have hsqrt : -Real.sqrt (x j ^ (2 : ℕ) + 4 * (lam : ℝ)) < x j :=
    Real.neg_sqrt_lt_of_sq_lt hsq
  have hnum : 0 < x j + Real.sqrt (x j ^ (2 : ℕ) + 4 * (lam : ℝ)) := by
    linarith
  have htwo : (0 : ℝ) < 2 := by norm_num
  exact div_pos hnum htwo

/-- Helper for Example 6.35: the separable-sum negative-log barrier is proper, lower
semicontinuous, and convex. -/
lemma separableSum_negative_log_barrier_proper_closed_convex :
    IsProperExtendedRealFunction F ∧ LowerSemicontinuous F ∧ is_convex_function F := by
  have hne_bot_all : ∀ x : E, F x ≠ ⊥ := by
    intro x
    -- The barrier either evaluates to a real number or to `⊤`, never to `⊥`.
    have hsum :
        F x =
          if ∀ i, 0 < x i then ((-∑ i, Real.log (x i) : ℝ) : EReal) else ⊤ := by
      exact piLp_sum_negative_log_barrier_apply x
    rw [hsum]
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_⟩
  · -- Properness comes from the absence of `⊥` and the finite value at the all-ones point.
    refine ⟨hne_bot_all, ?_⟩
    refine ⟨toLp 2 (fun _ : ι ↦ (1 : ℝ)), ?_⟩
    rw [mem_effective_domain_separableSum_negative_log_barrier_iff]
    intro i
    simp
  · -- Route correction: rather than proving epigraph closed directly, identify each strict
    -- superlevel set with an open product inequality on the positive parts.
    rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro y
    by_cases hy_top : y = ⊤
    · simpa [hy_top]
    · by_cases hy_bot : y = ⊥
      · have hpreimage : F ⁻¹' Set.Ioi y = Set.univ := by
          ext x
          constructor
          · intro hx
            simp
          · intro hx
            simpa [hy_bot] using (bot_lt_iff_ne_bot.mpr (hne_bot_all x))
        simpa [hpreimage]
      · have hy_coe : (((y.toReal : ℝ)) : EReal) = y := EReal.coe_toReal hy_top hy_bot
        rw [← hy_coe]
        let g : E → ℝ := fun x ↦ ∏ i, max (x i) 0
        have hg : Continuous g := by
          unfold g
          refine continuous_finset_prod Finset.univ ?_
          intro i hi
          exact (PiLp.continuous_apply (2 : ENNReal) (fun _ : ι ↦ ℝ) i).max continuous_const
        have hpreimage :
            F ⁻¹' Set.Ioi (((y.toReal : ℝ)) : EReal) =
              g ⁻¹' Set.Iio (Real.exp (-y.toReal)) := by
          ext x
          constructor
          · intro hx
            by_cases hxpos : ∀ i, 0 < x i
            · have hprod_pos : 0 < ∏ i, x i := by
                exact Finset.prod_pos fun i hi ↦ hxpos i
              have hreal : y.toReal < -∑ i, Real.log (x i) := by
                have hsum :
                    F x = (((-∑ i, Real.log (x i) : ℝ)) : EReal) := by
                  simpa [hxpos] using piLp_sum_negative_log_barrier_apply x
                rw [Set.mem_preimage, hsum] at hx
                have hx' :
                    (((y.toReal : ℝ)) : EReal) <
                      (((-∑ i, Real.log (x i) : ℝ)) : EReal) := hx
                exact_mod_cast hx'
              have hlog : Real.log (∏ i, x i) < -y.toReal := by
                rw [Real.log_prod]
                · linarith
                · intro i hi
                  exact (hxpos i).ne'
              have hprod_lt : ∏ i, x i < Real.exp (-y.toReal) :=
                (Real.log_lt_iff_lt_exp hprod_pos).1 hlog
              have hg_eq : g x = ∏ i, x i := by
                unfold g
                refine Finset.prod_congr rfl ?_
                intro i hi
                exact max_eq_left (le_of_lt (hxpos i))
              simpa [Set.mem_preimage, hg_eq] using hprod_lt
            · obtain ⟨i, hi⟩ := not_forall.mp hxpos
              have hprod_zero : g x = 0 := by
                unfold g
                rw [Finset.prod_eq_zero_iff]
                exact ⟨i, Finset.mem_univ i, by simp [le_of_not_gt hi]⟩
              have hxg : g x < Real.exp (-y.toReal) := by
                simpa [hprod_zero] using Real.exp_pos (-y.toReal)
              simpa [Set.mem_preimage] using hxg
          · intro hx
            by_cases hxpos : ∀ i, 0 < x i
            · have hprod_pos : 0 < ∏ i, x i := by
                exact Finset.prod_pos fun i hi ↦ hxpos i
              have hprod_lt : ∏ i, x i < Real.exp (-y.toReal) := by
                have hg_eq : g x = ∏ i, x i := by
                  unfold g
                  refine Finset.prod_congr rfl ?_
                  intro i hi
                  exact max_eq_left (le_of_lt (hxpos i))
                simpa [Set.mem_preimage, hg_eq] using hx
              have hlog : Real.log (∏ i, x i) < -y.toReal :=
                (Real.log_lt_iff_lt_exp hprod_pos).2 hprod_lt
              have hreal : y.toReal < -∑ i, Real.log (x i) := by
                rw [Real.log_prod] at hlog
                · linarith
                · intro i hi
                  exact (hxpos i).ne'
              have hx' :
                  (((y.toReal : ℝ)) : EReal) <
                    (((-∑ i, Real.log (x i) : ℝ)) : EReal) := by
                exact_mod_cast hreal
              have hsum :
                  F x = (((-∑ i, Real.log (x i) : ℝ)) : EReal) := by
                  simpa [hxpos] using piLp_sum_negative_log_barrier_apply x
              rw [Set.mem_preimage, hsum]
              exact hx'
            · have hx' : (((y.toReal : ℝ)) : EReal) < (⊤ : EReal) := by
                simp
              have hsum : F x = (⊤ : EReal) := by
                simpa [hxpos] using piLp_sum_negative_log_barrier_apply x
              rw [Set.mem_preimage, hsum]
              exact hx'
        simpa [hpreimage] using isOpen_lt hg continuous_const
  · have hne_bot :
        ∀ x ∈ effective_domain F, F x ≠ ⊥ := by
        intro x hx
        exact hne_bot_all x
    rw [is_convex_function_iff_convexOn_toReal hne_bot]
    have hneglog_convex : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun t : ℝ ↦ -Real.log t) := by
      exact
        ((strictConcaveOn_log_Ioi.concaveOn).neg :
          ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun t : ℝ ↦ -Real.log t))
    refine ⟨?_, ?_⟩
    · -- Positivity of each coordinate is preserved under convex combinations.
      intro x hx y hy a b ha hb hab
      rw [mem_effective_domain_separableSum_negative_log_barrier_iff] at hx hy ⊢
      intro i
      have hcomb : (a • x + b • y) i = a * x i + b * y i := by
        simp [smul_eq_mul]
      rw [hcomb]
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        rw [ha0, zero_mul, hb1, one_mul]
        simpa using hy i
      · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hax : 0 < a * x i := mul_pos hapos (hx i)
        have hby : 0 ≤ b * y i := mul_nonneg hb (hy i).le
        nlinarith
    · intro x hx y hy a b ha hb hab
      have hxpos := (mem_effective_domain_separableSum_negative_log_barrier_iff x).1 hx
      have hypos := (mem_effective_domain_separableSum_negative_log_barrier_iff y).1 hy
      have hcomb_pos : ∀ i, 0 < (a • x + b • y) i := by
        intro i
        have hcomb : (a • x + b • y) i = a * x i + b * y i := by
          simp [smul_eq_mul]
        rw [hcomb]
        by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          rw [ha0, zero_mul, hb1, one_mul]
          simpa using hypos i
        · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          have hax : 0 < a * x i := mul_pos hapos (hxpos i)
          have hby : 0 ≤ b * y i := mul_nonneg hb (hypos i).le
          nlinarith
      have hcoord :
          ∀ i,
            -Real.log ((a • x + b • y) i) ≤
              a * (-Real.log (x i)) + b * (-Real.log (y i)) := by
        intro i
        have hineq :=
          hneglog_convex.2 (show x i ∈ Set.Ioi (0 : ℝ) by exact hxpos i)
            (show y i ∈ Set.Ioi (0 : ℝ) by exact hypos i) ha hb hab
        simpa [smul_eq_mul] using hineq
      have hsum :
          ∑ i, -Real.log ((a • x + b • y) i) ≤
            ∑ i, (a * (-Real.log (x i)) + b * (-Real.log (y i))) := by
        exact Finset.sum_le_sum fun i hi ↦ hcoord i
      have hx_toReal : (F x).toReal = ∑ i, -Real.log (x i) := by
        have hsum : F x = (((-∑ i, Real.log (x i) : ℝ)) : EReal) := by
          simpa [hxpos] using piLp_sum_negative_log_barrier_apply x
        rw [hsum]
        simp [Finset.sum_neg_distrib]
      have hy_toReal : (F y).toReal = ∑ i, -Real.log (y i) := by
        have hsum : F y = (((-∑ i, Real.log (y i) : ℝ)) : EReal) := by
          simpa [hypos] using piLp_sum_negative_log_barrier_apply y
        rw [hsum]
        simp [Finset.sum_neg_distrib]
      have hcomb_toReal : (F (a • x + b • y)).toReal = ∑ i, -Real.log ((a • x + b • y) i) := by
        have hsum :
            F (a • x + b • y) =
              if ∀ i, 0 < (a • x + b • y) i then
                (((-∑ i, Real.log ((a • x + b • y) i) : ℝ)) : EReal)
              else ⊤ := by
          exact piLp_sum_negative_log_barrier_apply (a • x + b • y)
        rw [hsum]
        rw [if_pos hcomb_pos]
        simp [Finset.sum_neg_distrib]
      calc
        (F (a • x + b • y)).toReal = ∑ i, -Real.log ((a • x + b • y) i) := hcomb_toReal
        _ ≤ ∑ i, (a * (-Real.log (x i)) + b * (-Real.log (y i))) := hsum
        _ = a * ∑ i, -Real.log (x i) + b * ∑ i, -Real.log (y i) := by
          calc
            ∑ i, (a * (-Real.log (x i)) + b * (-Real.log (y i))) =
                ∑ i, a * (-Real.log (x i)) + ∑ i, b * (-Real.log (y i)) := by
                  rw [Finset.sum_add_distrib]
            _ = a * ∑ i, -Real.log (x i) + b * ∑ i, -Real.log (y i) := by
                  simp_rw [Finset.mul_sum]
        _ = a * (F x).toReal + b * (F y).toReal := by
          rw [hx_toReal, hy_toReal]

/-- Helper for Example 6.35: scaling the finite negative-log sum by a positive scalar is the same
as scaling each summand separately. -/
lemma scaled_negative_log_barrier_sum_real (z : E) (lam : PosReal) :
    ((lam : ℝ) * (-(∑ i, Real.log (z i))) : ℝ) =
      ∑ i, ((lam : ℝ) * (-Real.log (z i))) := by
  -- This is the finite-sum algebra needed on the positive branch.
  simp [Finset.mul_sum]

/-- Helper for Example 6.35: on the positive orthant, both scaled barrier expressions reduce to
the same finite real sum. -/
lemma scaled_separableSum_negative_log_barrier_apply_of_pos
    (z : E) (lam : PosReal) (hz : ∀ i, 0 < z i) :
    (((lam : EReal) • F) z) =
      PiLp.separableSum (fun _ : ι ↦ ((lam : EReal) • negative_log_barrier)) z := by
  -- Both sides are finite on the positive orthant, so we rewrite them to the same coerced real
  -- sum and finish with finite-dimensional algebra.
  rw [Pi.smul_apply, PiLp.separableSum_apply, smul_eq_mul]
  rw [show (∑ i, negative_log_barrier (z i)) =
      (((-(∑ i, Real.log (z i)) : ℝ)) : EReal) by
        simpa [PiLp.separableSum_apply, hz] using piLp_sum_negative_log_barrier_apply z]
  rw [show (((lam : EReal) * (((-(∑ i, Real.log (z i)) : ℝ)) : EReal)) : EReal) =
      (((lam : ℝ) * (-(∑ i, Real.log (z i))) : ℝ) : EReal) by
      rw [← EReal.coe_mul]]
  rw [show PiLp.separableSum (fun _ : ι ↦ (lam : EReal) • negative_log_barrier) z =
      ∑ i, ((((lam : ℝ) * (-Real.log (z i)) : ℝ)) : EReal) by
      simp [PiLp.separableSum_apply, negative_log_barrier, hz, Pi.smul_apply, smul_eq_mul,
        EReal.coe_mul]]
  rw [← ereal_coe_finset_sum Finset.univ (fun i ↦ (lam : ℝ) * (-Real.log (z i)))]
  exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) (scaled_negative_log_barrier_sum_real z lam)

/-- Helper for Example 6.35: off the positive orthant, one nonpositive coordinate forces both
scaled barrier expressions to equal `⊤`. -/
lemma scaled_separableSum_negative_log_barrier_apply_of_not_pos
    (z : E) (lam : PosReal) (hz : ¬ ∀ i, 0 < z i) :
    (((lam : EReal) • F) z) =
      PiLp.separableSum (fun _ : ι ↦ ((lam : EReal) • negative_log_barrier)) z := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hz
  have hF_top : F z = ⊤ := by
    -- The original separable barrier is already infinite once one coordinate is nonpositive.
    simpa [hz] using piLp_sum_negative_log_barrier_apply z
  have hleft : (((lam : EReal) • F) z) = ⊤ := by
    -- Positive scaling preserves the `⊤` value on the inactive branch.
    rw [Pi.smul_apply, smul_eq_mul, hF_top]
    simpa using EReal.mul_top_of_pos (show 0 < (lam : EReal) by exact_mod_cast lam.2)
  have hright_summand : ((lam : EReal) • negative_log_barrier) (z i) = ⊤ := by
    -- The bad coordinate already contributes `⊤` after scaling.
    rw [Pi.smul_apply, negative_log_barrier, if_neg hi, smul_eq_mul]
    simpa using EReal.mul_top_of_pos (show 0 < (lam : EReal) by exact_mod_cast lam.2)
  have hsum_ne_bot :
      ((Finset.univ.erase i).sum fun j ↦ ((lam : EReal) • negative_log_barrier) (z j)) ≠ ⊥ := by
    -- Every remaining summand is either a finite real value or `⊤`, never `⊥`.
    intro hbot
    have hbot' :
        ∃ j ∈ Finset.univ.erase i, ((lam : EReal) • negative_log_barrier) (z j) = ⊥ := by
      exact (WithBot.sum_eq_bot_iff (s := Finset.univ.erase i)
        (f := fun j ↦ ((lam : EReal) • negative_log_barrier) (z j))).mp hbot
    rcases hbot' with ⟨j, hj, hjbot⟩
    by_cases hzj : 0 < z j
    · rw [Pi.smul_apply, negative_log_barrier, if_pos hzj, smul_eq_mul, ← EReal.coe_mul] at hjbot
      exact EReal.coe_ne_bot _ hjbot
    · rw [Pi.smul_apply, negative_log_barrier, if_neg hzj, smul_eq_mul] at hjbot
      rw [EReal.mul_top_of_pos (show 0 < (lam : EReal) by exact_mod_cast lam.2)] at hjbot
      simp at hjbot
  have hright : PiLp.separableSum (fun _ : ι ↦ ((lam : EReal) • negative_log_barrier)) z = ⊤ := by
    -- Isolate the bad coordinate and collapse the remaining sum with `top_add_of_ne_bot`.
    rw [PiLp.separableSum_apply]
    rw [show (∑ j, ((lam : EReal) • negative_log_barrier) (z j)) =
        ((lam : EReal) • negative_log_barrier) (z i) +
          (Finset.univ.erase i).sum (fun j ↦ ((lam : EReal) • negative_log_barrier) (z j)) by
        symm
        exact Finset.add_sum_erase (s := Finset.univ) (a := i)
          (fun j ↦ ((lam : EReal) • negative_log_barrier) (z j)) (Finset.mem_univ i)]
    rw [hright_summand]
    exact EReal.top_add_of_ne_bot hsum_ne_bot
  rw [hleft, hright]

theorem smul_separableSum_negative_log_barrier_eq (lam : PosReal) :
    ((lam : EReal) • F) =
      PiLp.separableSum (fun _ : ι ↦ ((lam : EReal) • negative_log_barrier)) := by
  funext z
  -- Route correction: avoid an abstract `DistribSMul` search on `EReal`; evaluate pointwise and
  -- split by whether `z` lies in the positive orthant.
  by_cases hz : ∀ i, 0 < z i
  · exact scaled_separableSum_negative_log_barrier_apply_of_pos z lam hz
  · exact scaled_separableSum_negative_log_barrier_apply_of_not_pos z lam hz

/-- Positive scaling preserves properness of the scalar negative-log barrier. -/
private lemma scaled_negative_log_barrier_proper (lam : PosReal) :
    IsProperExtendedRealFunction ((lam : EReal) • negative_log_barrier) := by
  refine ⟨?_, ?_⟩
  · intro t
    by_cases ht : 0 < t
    · simp [negative_log_barrier, ht, Pi.smul_apply, smul_eq_mul, ← EReal.coe_mul]
    · rw [Pi.smul_apply, negative_log_barrier, if_neg ht, smul_eq_mul]
      rw [EReal.mul_top_of_pos (show 0 < (lam : EReal) by exact_mod_cast lam.2)]
      simp
  · refine ⟨1, ?_⟩
    rw [mem_effective_domain]
    simp [negative_log_barrier, Pi.smul_apply, smul_eq_mul, ← EReal.coe_mul]

/-- The `PiLp` specialization of the coordinatewise logarithmic-barrier proximal formula. -/
private theorem prox_piLp_log_barrier_penalty_eq_singleton
    (lam : PosReal) (x : E) :
    prox[PiLp.separableSum (fun _ : ι ↦ (lam : EReal) • negative_log_barrier)] x =
      {toLp 2 fun j ↦ (x j + Real.sqrt (x j ^ 2 + 4 * (lam : ℝ))) / 2} := by
  apply
    (prox_separableSum_eq_singleton_iff_coordinatewise
      (fun _ : ι ↦ (lam : EReal) • negative_log_barrier)
      (fun _ ↦ scaled_negative_log_barrier_proper lam) x
      (toLp 2 fun j ↦ (x j + Real.sqrt (x j ^ 2 + 4 * (lam : ℝ))) / 2)).2
  intro i
  simpa using prox_scalar_log_barrier_penalty_eq_singleton (lam : ℝ) lam.2 (x i)

-- Proof sketch: unfold `positiveProductSuperlevelSet` and
-- `sum_negative_log_barrier_apply`. On the positive orthant, the inequality
-- `-∑ j log (x j) ≤ -log α` is equivalent to `α ≤ ∏ j, x j` by logarithm identities, while
-- outside the positive orthant the barrier value is `⊤`, so the sublevel condition fails.
/-- The positive-product superlevel set is the `(-log α)`-sublevel set of the canonical
separable-sum negative-log barrier. -/
theorem positiveProductSuperlevelSet_eq_sublevel_separableSum_negative_log_barrier
    (α : PosReal) :
    positiveProductSuperlevelSet (α : ℝ) =
      F ⁻¹' Set.Iic (((-Real.log (α : ℝ) : ℝ)) : EReal) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxpos, hαx⟩
    -- On the positive orthant, the barrier inequality is equivalent to the product constraint.
    have hsum : F x = (((-∑ i, Real.log (x i) : ℝ)) : EReal) := by
      simpa [hxpos] using piLp_sum_negative_log_barrier_apply x
    have hlog_le : Real.log (α : ℝ) ≤ ∑ i, Real.log (x i) := by
      have hxprod_pos : 0 < ∏ i, x i := by
        exact Finset.prod_pos fun i hi ↦ hxpos i
      have hαlog : Real.log (α : ℝ) ≤ Real.log (∏ i, x i) :=
        Real.log_le_log α.2 hαx
      rwa [Real.log_prod (fun i hi ↦ (hxpos i).ne')] at hαlog
    have hreal : (-∑ i, Real.log (x i) : ℝ) ≤ -Real.log (α : ℝ) := by
      linarith
    rw [Set.mem_preimage, Set.mem_Iic, hsum]
    exact_mod_cast hreal
  · intro hx
    by_cases hxpos : ∀ i, 0 < x i
    · -- Once the barrier value is finite, exponentiating the log inequality recovers the product
      -- lower bound.
      have hsum : F x = (((-∑ i, Real.log (x i) : ℝ)) : EReal) := by
        simpa [hxpos] using piLp_sum_negative_log_barrier_apply x
      have hreal : (-∑ i, Real.log (x i) : ℝ) ≤ -Real.log (α : ℝ) := by
        have hx' : F x ≤ (((-Real.log (α : ℝ) : ℝ)) : EReal) := by
          simpa [Set.mem_preimage, Set.mem_Iic] using hx
        rw [hsum] at hx'
        exact_mod_cast hx'
      have hlog : Real.log (α : ℝ) ≤ ∑ i, Real.log (x i) := by
        linarith
      have hαx : (α : ℝ) ≤ ∏ i, x i := by
        calc
          (α : ℝ) = Real.exp (Real.log (α : ℝ)) := by
            rw [Real.exp_log α.2]
          _ ≤ Real.exp (∑ i, Real.log (x i)) := by
            exact Real.exp_le_exp.mpr hlog
          _ = ∏ i, x i := by
            rw [Real.exp_sum]
            refine Finset.prod_congr rfl ?_
            intro i hi
            rw [Real.exp_log (hxpos i)]
      exact ⟨hxpos, hαx⟩
    · -- Outside the positive orthant, the separable barrier is `⊤`, so the sublevel condition
      -- cannot hold.
      have hsum : F x = (⊤ : EReal) := by
        simpa [hxpos] using piLp_sum_negative_log_barrier_apply x
      have hx' : ¬ x ∈ F ⁻¹' Set.Iic (((-Real.log (α : ℝ) : ℝ)) : EReal) := by
        rw [Set.mem_preimage, Set.mem_Iic, hsum]
        simp
      exact False.elim (hx' hx)

-- Proof sketch: for `λ > 0`, rewrite the displayed function as the level-set residual from
-- Theorem 6.30 for `f = F` at level `-log α`, using `prox_log_barrier_penalty_eq_singleton` from
-- Example 6.9 to evaluate the scaled proximal singleton explicitly.
/-- Evaluating the canonical level-set residual for the separable-sum negative-log barrier at a
positive multiplier gives the explicit active-branch scalar equation from Example 6.35. -/
theorem positiveProductProjectionResidual_eq
    (α : PosReal) (x : E) (lam : PosReal) :
    level_set_projection_residual F (-Real.log (α : ℝ)) x (lam : ℝ) =
      -(∑ j, Real.log ((x j + Real.sqrt (x j ^ (2 : ℕ) + 4 * (lam : ℝ))) / 2)) +
        Real.log (α : ℝ) := by
  let y : E := toLp 2 fun j ↦ (x j + Real.sqrt (x j ^ (2 : ℕ) + 4 * (lam : ℝ))) / 2
  have hy_pos : ∀ j, 0 < y j := by
    intro j
    simpa [y] using activePoint_coordinate_pos x lam j
  have hprox : prox[((lam : EReal) • F)] x = {y} := by
    rw [smul_separableSum_negative_log_barrier_eq (ι := ι) lam]
    simpa [y] using prox_piLp_log_barrier_penalty_eq_singleton lam x
  -- Singleton collapse turns the generic residual into the textbook scalar equation.
  calc
    level_set_projection_residual F (-Real.log (α : ℝ)) x (lam : ℝ) =
        F y - (-Real.log (α : ℝ)) := by
          simpa [y] using
            level_set_projection_residual_eq_of_scaled_prox_eq_singleton
              F (-Real.log (α : ℝ)) x (lam : ℝ) y hprox
    _ = (-(∑ j, Real.log (y j)) + Real.log (α : ℝ) : ℝ) := by
      have hFy : F y = (((-∑ j, Real.log (y j) : ℝ)) : EReal) := by
        simpa [hy_pos] using piLp_sum_negative_log_barrier_apply y
      have hsub :
          (((( -∑ j, Real.log (y j) : ℝ) - (-Real.log (α : ℝ))) : ℝ) : EReal) =
            (((-(∑ j, Real.log (y j)) + Real.log (α : ℝ) : ℝ)) : EReal) := by
        congr 1
        ring
      rw [hFy]
      change (((( -∑ j, Real.log (y j) : ℝ) - (-Real.log (α : ℝ))) : ℝ) : EReal) =
        (((-(∑ j, Real.log (y j)) + Real.log (α : ℝ) : ℝ)) : EReal)
      exact hsub
    _ = -(∑ j, Real.log ((x j + Real.sqrt (x j ^ (2 : ℕ) + 4 * (lam : ℝ))) / 2)) +
          Real.log (α : ℝ) := by
      simp [y]

-- Proof sketch: this is Theorem 6.30 (3) specialized to the separable-sum negative-log barrier
-- owner `F` and the sublevel value `-log α`.
/-- The canonical residual governing the active branch of Example 6.35 is nonincreasing on the
nonnegative multiplier domain. -/
theorem positiveProductProjectionResidual_antitoneOn_nonneg
    (α : PosReal) (x : E) :
    AntitoneOn (level_set_projection_residual F (-Real.log (α : ℝ)) x) (Set.Ici 0) := by
  rcases separableSum_negative_log_barrier_proper_closed_convex (ι := ι) with
    ⟨hf_proper, hf_closed, hf_convex⟩
  -- Theorem 6.30 applies directly once the canonical barrier owner is packaged as proper, closed,
  -- and convex.
  exact level_set_projection_residual_antitoneOn_nonneg
    F (-Real.log (α : ℝ)) hf_proper hf_closed hf_convex x

-- Proof sketch: rewrite `positiveProductSuperlevelSet α` as the sublevel set of `F` using
-- `positiveProductSuperlevelSet_eq_sublevel_separableSum_negative_log_barrier`. If `x ∈ C`, the
-- point `x` is already feasible, and its distance to itself is zero, so it is the unique
-- projected point.
/-- A point already lying in `positiveProductSuperlevelSet α` projects to itself. -/
theorem projection_mapping_positiveProductSuperlevelSet_eq_singleton_of_mem
    (α : ℝ) (x : E) (hx : x ∈ positiveProductSuperlevelSet α) :
    P[positiveProductSuperlevelSet α] x = {x} := by
  have hx_proj : x ∈ P[positiveProductSuperlevelSet α] x := by
    -- Feasibility makes `x` itself a projection point because its distance to itself is zero.
    rw [mem_projection_mapping_iff, isMinOn_iff]
    refine ⟨hx, ?_⟩
    intro y hy
    simp [norm_nonneg]
  ext y
  constructor
  · intro hy
    rw [mem_projection_mapping_iff, isMinOn_iff] at hy
    have hy_le : ‖y - x‖ ≤ ‖x - x‖ := hy.2 x hx
    have hy_norm : ‖y - x‖ = 0 := by
      have : ‖y - x‖ ≤ 0 := by simpa using hy_le
      exact le_antisymm this (norm_nonneg _)
    have hy_eq : y = x := by
      exact sub_eq_zero.mp (norm_eq_zero.mp hy_norm)
    simpa [hy_eq]
  · rintro rfl
    exact hx_proj

-- Proof sketch: rewrite `positiveProductSuperlevelSet α` as the sublevel set of `F` using
-- `positiveProductSuperlevelSet_eq_sublevel_separableSum_negative_log_barrier`. The textbook root
-- condition `α = ∏ j ((x j + √(x j^2 + 4 λ)) / 2)` converts, by logarithm identities together
-- with `positiveProductProjectionResidual_eq`, to the canonical residual equation from
-- Theorem 6.30. It already forces `x ∉ C`, since the coordinatewise formula
-- `(x j + √(x j^2 + 4 λ)) / 2` is strictly larger than `x j` for `λ > 0`, so feasibility of `x`
-- would contradict the displayed product equality. Then apply the level-set projection formula
-- from Theorem 6.30 with positivity built into the branch parameters `α` and `λ`, and
-- specialize `prox_log_barrier_penalty_eq_singleton` from Example 6.9 to identify the projected
-- point.
/-- Example 6.35: for
`C = {x ∈ (ℝ_{++})^ι | α ≤ ∏ i, x i}`, specializing to the textbook `ℝ_{++}^n` when
`ι = Fin n`, if positive reals `α` and `λ` satisfy the textbook active-constraint equation
`α = ∏ j, (x j + √(x j^2 + 4 λ)) / 2`, then the set-valued orthogonal projection onto `C` is the
singleton whose `j`-th coordinate is
`(x j + √(x j^2 + 4 λ)) / 2`; the root condition already forces the active branch `x ∉ C`.
The canonical residual formulation from Theorem 6.30 is kept as the companion bridge
`positiveProductProjectionResidual_eq`. Together with
`projection_mapping_positiveProductSuperlevelSet_eq_singleton_of_mem`, this gives the textbook
piecewise formula for `P_C(x)`. -/
theorem projection_mapping_positiveProductSuperlevelSet_eq_singleton_of_root
    (α : PosReal) (x : E)
    (lam : PosReal)
    (hroot :
      (α : ℝ) =
        ∏ j, (x j + Real.sqrt (x j ^ (2 : ℕ) + 4 * (lam : ℝ))) / 2) :
    P[positiveProductSuperlevelSet (α : ℝ)] x =
      {toLp 2 fun j ↦ (x j + Real.sqrt (x j ^ (2 : ℕ) + 4 * (lam : ℝ))) / 2} := by
  rcases separableSum_negative_log_barrier_proper_closed_convex (ι := ι) with
    ⟨hf_proper, hf_closed, hf_convex⟩
  let y : E := toLp 2 fun j ↦ (x j + Real.sqrt (x j ^ (2 : ℕ) + 4 * (lam : ℝ))) / 2
  have hy_pos : ∀ j, 0 < y j := by
    intro j
    simpa [y] using activePoint_coordinate_pos x lam j
  have hlog :
      Real.log (α : ℝ) = ∑ j, Real.log (y j) := by
    -- The root condition becomes a logarithmic identity because every active coordinate is
    -- strictly positive.
    rw [hroot, show (∏ j, (x j + Real.sqrt (x j ^ (2 : ℕ) + 4 * (lam : ℝ))) / 2) = ∏ j, y j by
      simp [y]]
    rw [Real.log_prod]
    intro j hj
    exact (hy_pos j).ne'
  have hphi : level_set_projection_residual F (-Real.log (α : ℝ)) x (lam : ℝ) = 0 := by
    -- The explicit residual bridge converts the textbook root equation into the canonical zero
    -- residual required by Theorem 6.30.
    have hreal :
        (-(∑ j, Real.log (y j)) + Real.log (α : ℝ) : ℝ) = 0 := by
      linarith
    calc
      level_set_projection_residual F (-Real.log (α : ℝ)) x (lam : ℝ) =
          (-(∑ j, Real.log (y j)) + Real.log (α : ℝ) : ℝ) := by
            simpa [y] using positiveProductProjectionResidual_eq α x lam
      _ = 0 := by
        exact_mod_cast hreal
  have hsublevel :
      P[F ⁻¹' Set.Iic (((-Real.log (α : ℝ) : ℝ)) : EReal)] x =
        prox[((lam : EReal) • F)] x :=
    projection_mapping_sublevel_eq_scaled_prox_of_level_set_projection_residual_eq_zero
      F (-Real.log (α : ℝ)) hf_proper hf_closed hf_convex x lam hphi
  -- Theorem 6.30 reduces the active branch to the scaled proximal singleton from Example 6.9.
  calc
    P[positiveProductSuperlevelSet (α : ℝ)] x =
        P[F ⁻¹' Set.Iic (((-Real.log (α : ℝ) : ℝ)) : EReal)] x := by
          rw [positiveProductSuperlevelSet_eq_sublevel_separableSum_negative_log_barrier α]
    _ = prox[((lam : EReal) • F)] x := hsublevel
    _ = {y} := by
          rw [smul_separableSum_negative_log_barrier_eq (ι := ι) lam]
          simpa [y] using prox_piLp_log_barrier_penalty_eq_singleton lam x
    _ = {toLp 2 fun j ↦ (x j + Real.sqrt (x j ^ (2 : ℕ) + 4 * (lam : ℝ))) / 2} := by
          simp [y]

end
