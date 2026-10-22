/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_18

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousMap Filter Set Topology
open scoped BigOperators

noncomputable section

universe u v

variable {α : Type u} [TopologicalSpace α]
variable {ι : Type v}

/-- The feasible set cut out by the continuous inequalities `f j x ≤ 0`. -/
def constraintSet (f : ι → C(α, ℝ)) : Set α :=
  {x | ∀ j : ι, f j x ≤ 0}

/-- Membership in `constraintSet f` means that every constraint value is nonpositive. -/
@[simp] theorem mem_constraintSet_iff
    (f : ι → C(α, ℝ)) {x : α} :
    x ∈ constraintSet f ↔ ∀ j : ι, f j x ≤ 0 :=
  Iff.rfl

/-- The strict feasible locus cut out by the same inequalities. -/
def strictConstraintSet (f : ι → C(α, ℝ)) : Set α :=
  {x | ∀ j : ι, f j x < 0}

/-- Membership in `strictConstraintSet f` means that every constraint value is strictly negative.
-/
@[simp] theorem mem_strictConstraintSet_iff
    (f : ι → C(α, ℝ)) {x : α} :
    x ∈ strictConstraintSet f ↔ ∀ j : ι, f j x < 0 :=
  Iff.rfl

private theorem continuous_neg_constraint
    (f : ι → C(α, ℝ)) (j : ι) :
    Continuous fun x : strictConstraintSet f ↦ -f j x :=
  ((f j).continuous.comp continuous_subtype_val).neg

private theorem neg_constraint_pos
    (f : ι → C(α, ℝ)) (j : ι) (x : strictConstraintSet f) :
    0 < -f j x :=
  neg_pos.mpr (x.property j)

/-- The feasible set cut out by continuous nonstrict inequalities is closed. -/
private theorem isClosed_constraintSet (f : ι → C(α, ℝ)) :
    IsClosed (constraintSet f) := by
  simpa [constraintSet, Set.setOf_forall] using
    isClosed_iInter fun j ↦ isClosed_le (f j).continuous continuous_const

section FiniteIndex

variable [Finite ι]

/-- Every point satisfying all constraints strictly lies in the interior of the feasible set. -/
theorem strictConstraintSet_subset_interior_constraintSet
    (f : ι → C(α, ℝ)) :
    strictConstraintSet f ⊆ interior (constraintSet f) :=
  (by
    simpa [strictConstraintSet, Set.setOf_forall] using
      (isOpen_iInter_of_finite fun j ↦ isOpen_lt (f j).continuous continuous_const) :
    IsOpen (strictConstraintSet f)).subset_interior_iff.mpr <| by
      intro x hx j
      exact le_of_lt (hx j)

/-- The bridge hypothesis `interior (constraintSet f) ⊆ strictConstraintSet f` says exactly that
the chosen inequality presentation recovers the intrinsic interior of the feasible set. -/
theorem strictConstraintSet_eq_interior_constraintSet
    (f : ι → C(α, ℝ))
    (hinterior : interior (constraintSet f) ⊆ strictConstraintSet f) :
    strictConstraintSet f = interior (constraintSet f) :=
  subset_antisymm
    (strictConstraintSet_subset_interior_constraintSet f)
    hinterior

/-- A frontier point of `constraintSet f` has an active constraint `f j x = 0`. -/
private theorem exists_eq_zero_of_mem_frontier_constraintSet
    (f : ι → C(α, ℝ)) {x : α}
    (hx : x ∈ frontier (constraintSet f)) :
    ∃ j : ι, f j x = 0 := by
  have hx' : x ∈ constraintSet f \ interior (constraintSet f) := by
    simpa [(isClosed_constraintSet f).frontier_eq] using hx
  have hxle : ∀ j : ι, f j x ≤ 0 := by
    simpa [constraintSet] using hx'.1
  have hxnotstrict : x ∉ strictConstraintSet f := by
    intro hxstrict
    exact hx'.2 (strictConstraintSet_subset_interior_constraintSet f hxstrict)
  simp only [mem_strictConstraintSet_iff] at hxnotstrict
  push Not at hxnotstrict
  rcases hxnotstrict with ⟨j, hj⟩
  exact ⟨j, le_antisymm (hxle j) hj⟩

/-- Along a sequence in `interior (constraintSet f)` converging to a frontier point, some
constraint slack tends to `0`. -/
private theorem exists_constraint_tendsto_zero_of_tendsto_frontier_constraintSet
    (f : ι → C(α, ℝ))
    (x : ℕ → interior (constraintSet f)) {xBar : α}
    (hx : Tendsto (fun k ↦ (x k : α)) atTop (nhds xBar))
    (hxBar : xBar ∈ frontier (constraintSet f)) :
    ∃ j : ι, Tendsto (fun k ↦ f j (x k : α)) atTop (nhds 0) := by
  rcases exists_eq_zero_of_mem_frontier_constraintSet f hxBar with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  have ht : Tendsto (fun k ↦ f j (x k : α)) atTop (nhds (f j xBar)) :=
    ((f j).continuousAt xBar).tendsto.comp hx
  simpa [hj] using ht

section ConstraintBarrierExamples

noncomputable local instance instLocalChap01_Proposition_1_10_171 : Fintype ι := Fintype.ofFinite ι

/-
Source/core/bridge triage for Proposition 1.10.17:
- source-facing: the three explicit formulas on `strictConstraintSet f` and the proposition that,
  after identifying that strict locus with `interior (constraintSet f)`, they are barrier
  functions for `constraintSet f`;
- core/canonical: `IsBarrierFunctionOn (constraintSet f)`, whose owner is a continuous map on
  `interior (constraintSet f)`;
- bridge/view: the frontier-to-vanishing-slack lemma and the restriction of a strict-locus
  formula along `ContinuousMap.inclusion hinterior` once the chosen inequality presentation
  recovers the intrinsic interior of `constraintSet f`.

This keeps Proposition 1.10.17 at the source-facing layer. The canonical
`IsBarrierFunctionOn` results below are bridge theorems derived from the same strict-locus
formulas after identifying `strictConstraintSet f` with `interior (constraintSet f)`. The
vanishing-slack growth lemmas remain auxiliary companions; they do not replace the main
barrier-function statement.
-/

/-- The reciprocal-power barrier formula on the strict locus `strictConstraintSet f`. -/
def powerBarrier (f : ι → C(α, ℝ)) (p : ℝ) :
    C(strictConstraintSet f, ℝ) where
  toFun x := ∑ j : ι, 1 / Real.rpow (-f j x) p
  continuous_toFun := by
    refine continuous_finset_sum _ fun j _ ↦ ?_
    have hpow : Continuous fun x : strictConstraintSet f ↦ Real.rpow (-f j x) p :=
      (continuous_neg_constraint f j).rpow_const fun x ↦
        Or.inl <| ne_of_gt <| neg_constraint_pos f j x
    exact continuous_const.div hpow fun x ↦
      ne_of_gt <| Real.rpow_pos_of_pos (neg_constraint_pos f j x) p

/-- The logarithmic barrier formula on `strictConstraintSet f`. -/
def logarithmicBarrier (f : ι → C(α, ℝ)) :
    C(strictConstraintSet f, ℝ) where
  toFun x := -∑ j : ι, Real.log (-f j x)
  continuous_toFun := by
    have hsum : Continuous fun x : strictConstraintSet f ↦
        ∑ j : ι, Real.log (-f j x) := by
      refine continuous_finset_sum _ fun j _ ↦ ?_
      exact (continuous_neg_constraint f j).log fun x ↦
        ne_of_gt <| neg_constraint_pos f j x
    simpa using hsum.neg

/-- The exponential barrier formula on `strictConstraintSet f`. -/
def exponentialBarrier (f : ι → C(α, ℝ)) :
    C(strictConstraintSet f, ℝ) where
  toFun x := ∑ j : ι, Real.exp (1 / (-f j x))
  continuous_toFun := by
    refine continuous_finset_sum _ fun j _ ↦ ?_
    have hrecip : Continuous fun x : strictConstraintSet f ↦ 1 / (-f j x) :=
      continuous_const.div (continuous_neg_constraint f j) fun x ↦
        ne_of_gt <| neg_constraint_pos f j x
    simpa using Real.continuous_exp.comp hrecip

/-- Evaluating `powerBarrier f p` reproduces the reciprocal-power sum of the slacks. -/
@[simp] theorem powerBarrier_apply
    (f : ι → C(α, ℝ)) (p : ℝ)
    (x : strictConstraintSet f) :
    powerBarrier f p x = ∑ j : ι, 1 / Real.rpow (-f j x) p :=
  rfl

/-- Evaluating `logarithmicBarrier f` reproduces the sum of negative logarithms of the slacks. -/
@[simp] theorem logarithmicBarrier_apply
    (f : ι → C(α, ℝ)) (x : strictConstraintSet f) :
    logarithmicBarrier f x = -∑ j : ι, Real.log (-f j x) :=
  rfl

/-- Evaluating `exponentialBarrier f` reproduces the exponential reciprocal-slack sum. -/
@[simp] theorem exponentialBarrier_apply
    (f : ι → C(α, ℝ)) (x : strictConstraintSet f) :
    exponentialBarrier f x = ∑ j : ι, Real.exp (1 / (-f j x)) :=
  rfl

section BoundaryGrowth

/-- Helper for Proposition 1 10 17: a positive real sequence converging to `0` also converges to
`0` within `Set.Ioi 0`. -/
private theorem tendstoNhdsWithinZeroOfForallPos
    (s : ℕ → ℝ)
    (hs : Tendsto s atTop (nhds 0))
    (hsPos : ∀ k : ℕ, 0 < s k) :
    Tendsto s atTop (nhdsWithin 0 (Set.Ioi 0)) := by
  -- Record that the sequence eventually stays in the positive half-line.
  rw [nhdsWithin]
  refine Filter.tendsto_inf.2 ?_
  refine ⟨hs, ?_⟩
  exact Filter.tendsto_principal.2 <| Filter.Eventually.of_forall hsPos

/-- Helper for Proposition 1 10 17: the negative logarithm of a positive sequence tending to `0`
goes to `+∞`. -/
private theorem tendstoNegLogAtTopOfTendstoZeroOfForallPos
    (s : ℕ → ℝ)
    (hs : Tendsto s atTop (nhds 0))
    (hsPos : ∀ k : ℕ, 0 < s k) :
    Tendsto (fun k ↦ -Real.log (s k)) atTop atTop := by
  have hsWithin : Tendsto s atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendstoNhdsWithinZeroOfForallPos s hs hsPos
  have hlog : Tendsto (fun k ↦ Real.log (s k)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hsWithin
  -- Negating a quantity that tends to `-∞` produces a quantity tending to `+∞`.
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [Filter.tendsto_atBot.1 hlog (-b)] with k hk
  linarith

/-- Helper for Proposition 1 10 17: if each constraint image on the strict locus is bounded below,
then the inactive logarithmic summands admit a uniform lower bound. -/
private theorem logarithmicBarrier_lower_bound_of_bddBelow
    (f : ι → C(α, ℝ)) (j : ι)
    (hbounded : ∀ i : ι, BddBelow ((f i) '' strictConstraintSet f)) :
    ∃ C : ℝ, ∀ y : strictConstraintSet f,
      C + (-Real.log (-f j y)) ≤ logarithmicBarrier f y := by
  classical
  by_cases hnonempty : (strictConstraintSet f).Nonempty
  · rcases hnonempty with ⟨x0, hx0⟩
    let x0Strict : strictConstraintSet f := ⟨x0, hx0⟩
    choose c hc using fun i : ι => hbounded i
    let C : ℝ := Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-c i))
    refine ⟨C, ?_⟩
    intro y
    -- Evaluate each lower bound at one strict point to see that every `c i` is still negative.
    have hc_lt_zero : ∀ i : ι, c i < 0 := by
      intro i
      have hci : c i ≤ f i x0 := by
        exact (mem_lowerBounds.mp (hc i)) (f i x0) ⟨x0, hx0, rfl⟩
      exact lt_of_le_of_lt hci (x0Strict.property i)
    have hsum :
        C ≤ Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-f i y)) := by
      -- Each inactive logarithmic term is bounded below by the corresponding constant.
      unfold C
      refine Finset.sum_le_sum ?_
      intro i hi
      have hci : c i ≤ f i y := by
        exact (mem_lowerBounds.mp (hc i)) (f i y) ⟨y, y.property, rfl⟩
      have hy_pos : 0 < -f i y := neg_constraint_pos f i y
      have hc_pos : 0 < -c i := by
        linarith [hc_lt_zero i]
      have hneg_le : -f i y ≤ -c i := by
        linarith
      have hlog : Real.log (-f i y) ≤ Real.log (-c i) :=
        Real.log_le_log hy_pos hneg_le
      linarith
    calc
      C + (-Real.log (-f j y))
          ≤ Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-f i y))
              + (-Real.log (-f j y)) := by
            linarith
      _ = logarithmicBarrier f y := by
        rw [logarithmicBarrier_apply]
        calc
          Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-f i y))
              + (-Real.log (-f j y))
              = ∑ i : ι, -Real.log (-f i y) := by
                  simpa using
                    Finset.sum_erase_add
                      (Finset.univ : Finset ι)
                      (fun i ↦ -Real.log (-f i y))
                      (by simp : j ∈ (Finset.univ : Finset ι))
          _ = -∑ i : ι, Real.log (-f i y) := by
                rw [Finset.sum_neg_distrib]
  · refine ⟨0, ?_⟩
    intro y
    exact (hnonempty ⟨y, y.property⟩).elim

section

omit [Finite ι]

/-- Helper for Proposition 1 10 17: every logarithmic summand along an interior sequence
approaching the frontier is eventually bounded below by a constant. -/
private theorem inactiveNegLogTermEventuallyBoundedBelow
    (f : ι → C(α, ℝ))
    (hinterior : interior (constraintSet f) ⊆ strictConstraintSet f)
    (x : ℕ → interior (constraintSet f)) {xBar : α}
    (hx : Tendsto (fun k ↦ (x k : α)) atTop (nhds xBar))
    (hxBar : xBar ∈ frontier (constraintSet f))
    (i : ι) :
    ∃ c : ℝ, ∀ᶠ k in atTop, c ≤ -Real.log (-f i (x k : α)) := by
  let xStrict : ℕ → strictConstraintSet f := fun k ↦ ⟨x k, hinterior (x k).property⟩
  have hxBar_mem : xBar ∈ constraintSet f := by
    -- Convert frontier membership into feasible-set membership before reading off the inequalities.
    have hxBar' : xBar ∈ constraintSet f \ interior (constraintSet f) := by
      simpa [(isClosed_constraintSet f).frontier_eq] using hxBar
    exact hxBar'.1
  have hxBar_le : ∀ j : ι, f j xBar ≤ 0 := by
    simpa [constraintSet] using hxBar_mem
  have hfi : Tendsto (fun k ↦ f i (x k : α)) atTop (nhds (f i xBar)) :=
    ((f i).continuousAt xBar).tendsto.comp hx
  by_cases hzero : f i xBar = 0
  · refine ⟨0, ?_⟩
    let slack : ℕ → ℝ := fun k ↦ -f i (x k : α)
    have hslack : Tendsto slack atTop (nhds 0) := by
      simpa [slack, hzero] using hfi.neg
    have hlt_one : ∀ᶠ k in atTop, slack k < 1 := by
      have hmem : Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) := Iio_mem_nhds (by norm_num)
      exact hslack hmem
    -- Near an active constraint, the slack is positive and smaller than `1`,
    -- so `-log` is nonnegative.
    filter_upwards
      [Filter.Eventually.of_forall (fun k ↦ neg_constraint_pos f i (xStrict k)), hlt_one] with
      k hkPos hkOne
    have hlog_nonpos : Real.log (slack k) ≤ 0 :=
      Real.log_nonpos (le_of_lt hkPos) (le_of_lt hkOne)
    have hbound : 0 ≤ -Real.log (slack k) := by
      linarith
    simpa [slack] using hbound
  · have hi_neg : f i xBar < 0 :=
      lt_of_le_of_ne (hxBar_le i) hzero
    have hneg_term : Tendsto (fun k ↦ -f i (x k : α)) atTop (nhds (-f i xBar)) := by
      simpa using hfi.neg
    have hterm :
        Tendsto (fun k ↦ -Real.log (-f i (x k : α))) atTop
          (nhds (-Real.log (-f i xBar))) := by
      -- At an inactive constraint, continuity of `-log` around a strictly positive limit
      -- gives a uniform lower bound near the frontier point.
      have hcont : ContinuousAt (fun t : ℝ ↦ -Real.log t) (-f i xBar) := by
        have hpos : 0 < -f i xBar := by
          linarith
        exact (Real.continuousAt_log (ne_of_gt hpos)).neg
      exact hcont.tendsto.comp hneg_term
    refine ⟨-Real.log (-f i xBar) - 1, ?_⟩
    have hmem : Set.Ioi (-Real.log (-f i xBar) - 1) ∈ nhds (-Real.log (-f i xBar)) := by
      exact Ioi_mem_nhds (by linarith)
    filter_upwards [hterm hmem] with k hk
    exact le_of_lt hk

end

/-- Helper for Proposition 1 10 17: the sum of the inactive logarithmic terms along an interior
sequence approaching the frontier is eventually bounded below by a constant. -/
private theorem inactiveNegLogSumEventuallyBoundedBelow
    (f : ι → C(α, ℝ))
    (hinterior : interior (constraintSet f) ⊆ strictConstraintSet f)
    [DecidableEq ι]
    (x : ℕ → interior (constraintSet f)) {xBar : α}
    (hx : Tendsto (fun k ↦ (x k : α)) atTop (nhds xBar))
    (hxBar : xBar ∈ frontier (constraintSet f))
    (j : ι) :
    ∃ C : ℝ,
      ∀ᶠ k in atTop,
        C ≤ Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-f i (x k : α))) := by
  classical
  choose c hc using
    fun i : ι ↦ inactiveNegLogTermEventuallyBoundedBelow f hinterior x hx hxBar i
  refine ⟨Finset.sum (Finset.univ.erase j) c, ?_⟩
  -- Aggregate the eventual lower bounds termwise over the finite family of inactive indices.
  filter_upwards
    [(Finset.eventually_all (Finset.univ.erase j)).2 (fun i hi ↦ hc i)] with k hk
  exact Finset.sum_le_sum (fun i hi ↦ hk i hi)

/-- For `p ≥ 1`, the reciprocal-power formula diverges to `+∞` whenever some constraint slack
along the sequence tends to `0`. -/
theorem powerBarrier_tendsto_atTop_of_exists_constraint_tendsto_zero
    (f : ι → C(α, ℝ))
    {x : ℕ → strictConstraintSet f}
    (p : ℝ) (hp : 1 ≤ p)
    (hvanish :
      ∃ j : ι,
        Tendsto (fun k ↦ f j (x k : α)) atTop (nhds 0)) :
    Tendsto (fun k ↦ powerBarrier f p (x k)) atTop atTop := by
  rcases hvanish with ⟨j, hj⟩
  let slack : ℕ → ℝ := fun k ↦ -f j (x k : α)
  -- The active slack tends to `0` from the positive side along the strict locus.
  have hslack : Tendsto slack atTop (nhds 0) := by
    simpa [slack] using hj.neg
  have hslack_pos : ∀ k : ℕ, 0 < slack k := by
    intro k
    simpa [slack] using neg_constraint_pos f j (x k)
  have hslack_within : Tendsto slack atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendstoNhdsWithinZeroOfForallPos slack hslack hslack_pos
  -- The active reciprocal-power term already blows up to `+∞`.
  have hactive : Tendsto (fun k ↦ 1 / Real.rpow (slack k) p) atTop atTop := by
    have hneg : -p < 0 := by
      linarith
    have hpow : Tendsto (fun k ↦ Real.rpow (slack k) (-p)) atTop atTop :=
      (tendsto_rpow_neg_nhdsGT_zero hneg).comp hslack_within
    simpa [one_div, Real.rpow_neg, le_of_lt (hslack_pos _)] using hpow
  have hdom :
      ∀ k : ℕ, 1 / Real.rpow (slack k) p ≤ powerBarrier f p (x k) := by
    intro k
    -- The full finite sum dominates any one nonnegative summand.
    rw [powerBarrier_apply]
    simpa [slack] using
      (Finset.single_le_sum
        (fun i _ ↦ by
          have hpos : 0 < Real.rpow (-f i (x k)) p :=
            Real.rpow_pos_of_pos (neg_constraint_pos f i (x k)) p
          exact le_of_lt (one_div_pos.mpr hpos))
        (Finset.mem_univ j) :
        1 / Real.rpow (-f j (x k)) p ≤
          ∑ i ∈ (Finset.univ : Finset ι), 1 / Real.rpow (-f i (x k)) p)
  -- Domination transfers the single-summand divergence to the whole barrier.
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [Filter.tendsto_atTop.1 hactive b] with k hk
  exact le_trans hk (hdom k)

/-- If the constraint family is bounded below on the strict locus, then the logarithmic formula
diverges to `+∞` whenever some constraint slack tends to `0`. -/
theorem logarithmicBarrier_tendsto_atTop_of_exists_constraint_tendsto_zero
    (f : ι → C(α, ℝ))
    {x : ℕ → strictConstraintSet f}
    (hbounded : ∀ j : ι, BddBelow ((f j) '' strictConstraintSet f))
    (hvanish :
      ∃ j : ι,
        Tendsto (fun k ↦ f j (x k : α)) atTop (nhds 0)) :
    Tendsto (fun k ↦ logarithmicBarrier f (x k)) atTop atTop := by
  rcases hvanish with ⟨j, hj⟩
  rcases logarithmicBarrier_lower_bound_of_bddBelow f j hbounded with ⟨C, hC⟩
  let slack : ℕ → ℝ := fun k ↦ -f j (x k : α)
  -- The active slack tends to `0` through positive values.
  have hslack : Tendsto slack atTop (nhds 0) := by
    simpa [slack] using hj.neg
  have hslack_pos : ∀ k : ℕ, 0 < slack k := by
    intro k
    simpa [slack] using neg_constraint_pos f j (x k)
  have hactive : Tendsto (fun k ↦ -Real.log (slack k)) atTop atTop :=
    tendstoNegLogAtTopOfTendstoZeroOfForallPos slack hslack hslack_pos
  have hshift : Tendsto (fun k ↦ -Real.log (slack k) + C) atTop atTop := by
    -- Adding a fixed constant preserves divergence to `+∞`.
    have hadd : Tendsto (fun t : ℝ ↦ t + C) atTop atTop := by
      rw [Filter.Tendsto]
      simpa [Filter.map_map] using le_of_eq (Filter.map_add_atTop_eq C)
    exact hadd.comp hactive
  have hdom :
      ∀ k : ℕ, -Real.log (slack k) + C ≤ logarithmicBarrier f (x k) := by
    intro k
    simpa [slack, add_comm, add_left_comm, add_assoc] using hC (x k)
  -- The lower bound from the inactive summands lets the active blow-up control the whole sum.
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [Filter.tendsto_atTop.1 hshift b] with k hk
  exact le_trans hk (hdom k)

/-- The exponential formula diverges to `+∞` whenever some constraint slack tends to `0`. -/
theorem exponentialBarrier_tendsto_atTop_of_exists_constraint_tendsto_zero
    (f : ι → C(α, ℝ))
    {x : ℕ → strictConstraintSet f}
    (hvanish :
      ∃ j : ι,
        Tendsto (fun k ↦ f j (x k : α)) atTop (nhds 0)) :
    Tendsto (fun k ↦ exponentialBarrier f (x k)) atTop atTop := by
  rcases hvanish with ⟨j, hj⟩
  let slack : ℕ → ℝ := fun k ↦ -f j (x k : α)
  -- The active slack tends to `0` through positive values.
  have hslack : Tendsto slack atTop (nhds 0) := by
    simpa [slack] using hj.neg
  have hslack_pos : ∀ k : ℕ, 0 < slack k := by
    intro k
    simpa [slack] using neg_constraint_pos f j (x k)
  have hslack_within : Tendsto slack atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendstoNhdsWithinZeroOfForallPos slack hslack hslack_pos
  -- The reciprocal slack tends to `+∞`, and then the exponential does as well.
  have hrecip : Tendsto (fun k ↦ 1 / slack k) atTop atTop := by
    simpa [one_div] using (tendsto_inv_nhdsGT_zero.comp hslack_within)
  have hactive : Tendsto (fun k ↦ Real.exp (1 / slack k)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hrecip
  have hdom :
      ∀ k : ℕ, Real.exp (1 / slack k) ≤ exponentialBarrier f (x k) := by
    intro k
    -- The full finite sum dominates the active exponential summand.
    rw [exponentialBarrier_apply]
    simpa [slack] using
      (Finset.single_le_sum
        (s := (Finset.univ : Finset ι))
        (a := j)
        (f := fun i ↦ Real.exp (1 / (-f i (x k : α))))
        (fun i _ ↦ le_of_lt (Real.exp_pos (1 / (-f i (x k : α)))))
        (Finset.mem_univ j) :
        Real.exp (1 / (-f j (x k : α))) ≤
          Finset.sum (Finset.univ : Finset ι) (fun i ↦ Real.exp (1 / (-f i (x k : α)))))
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [Filter.tendsto_atTop.1 hactive b] with k hk
  exact le_trans hk (hdom k)

end BoundaryGrowth

section BarrierFunctionBridge

/-- Bridge a strict-locus growth criterion to the owner predicate `IsBarrierFunctionOn` once the
chosen strict constraints recover the intrinsic interior of `constraintSet f`. -/
private theorem isBarrierFunctionOn_of_tendsto_zero
    (f : ι → C(α, ℝ))
    (hinterior : interior (constraintSet f) ⊆ strictConstraintSet f)
    (hint : (interior (constraintSet f)).Nonempty)
    (F : C(strictConstraintSet f, ℝ))
    (hF :
      ∀ (x : ℕ → strictConstraintSet f),
        (∃ j : ι,
          Tendsto (fun k ↦ f j (x k : α)) atTop (nhds 0)) →
          Tendsto (fun k ↦ F (x k)) atTop atTop) :
    IsBarrierFunctionOn (constraintSet f) (F.comp (inclusion hinterior)) := by
  let _ : Fact (IsClosed (constraintSet f)) := ⟨isClosed_constraintSet f⟩
  refine IsBarrierFunctionOn.mk hint ?_
  intro x xBar hx hxBar
  rcases exists_constraint_tendsto_zero_of_tendsto_frontier_constraintSet f x hx hxBar with
    ⟨j, hj⟩
  change Tendsto (fun k ↦ F ⟨x k, hinterior (x k).property⟩) atTop atTop
  exact hF
    (fun k ↦ ⟨x k, hinterior (x k).property⟩)
    (by
      refine ⟨j, ?_⟩
      simpa using hj)

/-- Companion for Proposition 1 10 17: if the chosen strict inequalities recover
`interior (constraintSet f)`, then the reciprocal-power formula, viewed on that interior via the
canonical inclusion, is a barrier function for `constraintSet f`. -/
theorem powerBarrier_isBarrierFunctionOn
    (f : ι → C(α, ℝ))
    (hinterior : interior (constraintSet f) ⊆ strictConstraintSet f)
    (hint : (interior (constraintSet f)).Nonempty)
    (p : ℝ) (hp : 1 ≤ p) :
    IsBarrierFunctionOn (constraintSet f)
      ((powerBarrier f p).comp (inclusion hinterior)) := by
  simpa using
    isBarrierFunctionOn_of_tendsto_zero f hinterior hint (powerBarrier f p)
      (fun x hvanish ↦
        powerBarrier_tendsto_atTop_of_exists_constraint_tendsto_zero f p hp hvanish)

/-- Along a sequence in `interior (constraintSet f)` converging to a frontier point, the
logarithmic barrier tends to `+∞`. -/
private theorem logarithmicBarrier_tendsto_atTop_of_tendsto_frontier_constraintSet
    (f : ι → C(α, ℝ))
    (hinterior : interior (constraintSet f) ⊆ strictConstraintSet f)
    (x : ℕ → interior (constraintSet f)) {xBar : α}
    (hx : Tendsto (fun k ↦ (x k : α)) atTop (nhds xBar))
    (hxBar : xBar ∈ frontier (constraintSet f)) :
    Tendsto
      (fun k ↦ logarithmicBarrier f ⟨x k, hinterior (x k).property⟩)
      atTop atTop := by
  classical
  -- Route correction: isolate the active `-log` blow-up and the inactive finite-sum lower bound
  -- into separate helpers so the frontier proof stays flat and elaborates predictably.
  rcases exists_constraint_tendsto_zero_of_tendsto_frontier_constraintSet f x hx hxBar with
    ⟨j, hj⟩
  let xStrict : ℕ → strictConstraintSet f := fun k ↦ ⟨x k, hinterior (x k).property⟩
  let slack : ℕ → ℝ := fun k ↦ -f j (x k : α)
  have hslack : Tendsto slack atTop (nhds 0) := by
    simpa [slack] using hj.neg
  have hslack_pos : ∀ k : ℕ, 0 < slack k := by
    intro k
    simpa [slack, xStrict] using neg_constraint_pos f j (xStrict k)
  have hactive : Tendsto (fun k ↦ -Real.log (slack k)) atTop atTop :=
    tendstoNegLogAtTopOfTendstoZeroOfForallPos slack hslack hslack_pos
  rcases inactiveNegLogSumEventuallyBoundedBelow f hinterior x hx hxBar j with ⟨C, hC⟩
  have hshift : Tendsto (fun k ↦ C + (-Real.log (slack k))) atTop atTop := by
    -- Adding the finite lower-bound constant preserves divergence to `+∞`.
    have hshift' : Tendsto (fun k ↦ -Real.log (slack k) + C) atTop atTop := by
      have hadd : Tendsto (fun t : ℝ ↦ t + C) atTop atTop := by
        rw [Filter.Tendsto]
        simpa [Filter.map_map] using le_of_eq (Filter.map_add_atTop_eq C)
      exact hadd.comp hactive
    simpa [add_comm] using hshift'
  have hdom :
      ∀ᶠ k in atTop,
        C + (-Real.log (slack k)) ≤ logarithmicBarrier f (xStrict k) := by
    have hmemUniv : j ∈ (Finset.univ : Finset ι) := by
      simp
    filter_upwards [hC] with k hk
    have hleft :
        C + (-Real.log (slack k))
          ≤ Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-f i (x k : α)))
              + (-Real.log (slack k)) := by
      linarith
    calc
      C + (-Real.log (slack k))
          ≤ Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-f i (x k : α)))
              + (-Real.log (slack k)) := hleft
      _ = logarithmicBarrier f (xStrict k) := by
        rw [logarithmicBarrier_apply]
        calc
          Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-f i (x k : α)))
              + (-Real.log (slack k))
              = ∑ i : ι, -Real.log (-f i (x k : α)) := by
                  simpa [slack] using
                    Finset.sum_erase_add
                      (Finset.univ : Finset ι)
                      (fun i ↦ -Real.log (-f i (x k : α)))
                      hmemUniv
          _ = -∑ i : ι, Real.log (-f i (x k : α)) := by
                rw [Finset.sum_neg_distrib]
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [Filter.tendsto_atTop.1 hshift b, hdom] with k hk hk'
  exact le_trans hk hk'

/-- Proposition 1 10 17: if the chosen strict inequalities recover
`interior (constraintSet f)`, then the logarithmic formula, viewed on that interior via the
canonical inclusion, is a barrier function for `constraintSet f`. -/
theorem logarithmicBarrier_isBarrierFunctionOn
    (f : ι → C(α, ℝ))
    (hinterior : interior (constraintSet f) ⊆ strictConstraintSet f)
    (hint : (interior (constraintSet f)).Nonempty) :
    IsBarrierFunctionOn (constraintSet f)
      ((logarithmicBarrier f).comp (inclusion hinterior)) := by
  let _ : Fact (IsClosed (constraintSet f)) := ⟨isClosed_constraintSet f⟩
  refine IsBarrierFunctionOn.mk hint ?_
  intro x xBar hx hxBar
  simpa using
    logarithmicBarrier_tendsto_atTop_of_tendsto_frontier_constraintSet
      f hinterior x hx hxBar

/-- Companion for Proposition 1 10 17: if the chosen strict inequalities recover
`interior (constraintSet f)`, then the exponential formula, viewed on that interior via the
canonical inclusion, is a barrier function for `constraintSet f`. -/
theorem exponentialBarrier_isBarrierFunctionOn
    (f : ι → C(α, ℝ))
    (hinterior : interior (constraintSet f) ⊆ strictConstraintSet f)
    (hint : (interior (constraintSet f)).Nonempty) :
    IsBarrierFunctionOn (constraintSet f)
      ((exponentialBarrier f).comp (inclusion hinterior)) := by
  simpa using
    isBarrierFunctionOn_of_tendsto_zero f hinterior hint (exponentialBarrier f)
      (fun x hvanish ↦
        exponentialBarrier_tendsto_atTop_of_exists_constraint_tendsto_zero f hvanish)

end BarrierFunctionBridge

end ConstraintBarrierExamples
end FiniteIndex
