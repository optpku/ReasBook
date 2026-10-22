/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_27
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_38
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_22

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Module LinearMap
open scoped BigOperators RealInnerProductSpace WithTopConvexAnalysis NormalCone
open scoped ConstrainedArgmin

universe u w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 6.5 lies in the affine variational-inequality / gap-function domain.

Sampled owner-style declarations:
- `AffineVariationalInequalityProblem.IsSolution` in `Chap06/Definition_6_17`, the chapter owner
  for the source-facing variational-inequality predicate;
- `AffineVariationalInequalityProblem.gapFunction` in `Chap06/Definition_6_18`, the chapter owner
  for the repository's affine-VI gap function on the feasible subtype;
- `IsMinOn` and `isMinOn_iff` in mathlib, the canonical minimizer owner used across the project;
- `argmin[Q]` in `Chap01/Definition_1_3_3`, the chapter minimizer-set owner derived from
  `IsMinOn`.

Best owner abstraction:
- source-facing: an explicit linear/inner-product specialization of Lemma 6.5;
- core/canonical: `problem.IsSolution wStar`, `problem.gapFunction`, and `IsMinOn`;
- bridge/view: the owner-level equivalence between the Chapter 6 solution predicate and
  minimizing the canonical gap function on the feasible subtype.

Primitive data:
- `problem : AffineVariationalInequalityProblem E`.

Derived API:
- the minimization statement `IsMinOn problem.gapFunction Set.univ wStar`;
- an attained-maximum companion for the defining payoff at each feasible base point in the
  finite-dimensional source setting;
- the zero-gap consequence at a solution or a minimizer.

Source/core/bridge triage:
- source-facing: Lemma 6.5 itself, stated with an explicit feasible set and linear operator;
- core/canonical in this file: `AffineVariationalInequalityProblem E`, `gapFunction`, and
  `IsMinOn`;
- bridge/view: the owner-level theorem below on the feasible subtype, together with the explicit
  inner-product specialization at the end of the file.

The repository's chapter owner `gapFunction` uses the internal bridge payoff `⟪B(v), w - v⟫`.
This file keeps that owner as an internal helper surface, while the explicit source-facing
specialization at the end uses the repaired payoff `⟪B(v), w - v⟫` from the semantic-defect
report.
-/

-- Semantic recall note: `lean_leansearch` did not surface a directly relevant variational-
-- inequality/gap-function theorem, so this file follows the local Chapter 6 owner API.

namespace AffineVariationalInequalityProblem

/-- Helper for Lemma 6.5: comparing the canonical gap payoff at a feasible point `v` with the
basepoint payoff at `w` isolates the nonnegative diagonal term of the linear part. -/
lemma payoff_eq_basepoint_sub_diagonal
    (problem : AffineVariationalInequalityProblem E) (w v : problem.feasibleSet) :
    problem v ((w : E) - (v : E)) =
      problem w ((w : E) - (v : E)) -
        problem.operator.linear ((w : E) - (v : E)) ((w : E) - (v : E)) := by
  let d : E := (w : E) - (v : E)
  -- Compare the affine values at `w` and `v` through the linear part evaluated on the displacement.
  have hlinear : problem.operator.linear d = problem (w : E) - problem (v : E) := by
    simpa [d, vsub_eq_sub] using problem.operator.linearMap_vsub (w : E) (v : E)
  have happly : problem.operator.linear d d = problem (w : E) d - problem (v : E) d := by
    simpa [d] using congrArg (fun f : Dual ℝ E ↦ f d) hlinear
  linarith

/-- Helper for Lemma 6.5: the affine rewrite gives the canonical pointwise lower bound by
discarding the nonnegative diagonal correction term. -/
lemma payoff_le_basepoint
    (problem : AffineVariationalInequalityProblem E) (w v : problem.feasibleSet) :
    problem v ((w : E) - (v : E)) ≤ problem w ((w : E) - (v : E)) := by
  let d : E := (w : E) - (v : E)
  -- The diagonal correction term is nonnegative by monotonicity of the linear part.
  have hdiag : 0 ≤ problem.operator.linear d d := problem.linear_nonnegative d
  have hrewrite := problem.payoff_eq_basepoint_sub_diagonal w v
  linarith

/-- Helper for Lemma 6.5: in the finite-dimensional source setting, the payoff supremum defining
the canonical gap function is attained by a feasible comparison point. -/
lemma exists_isGreatest_gap_payoff [FiniteDimensional ℝ E]
    (problem : AffineVariationalInequalityProblem E) (w : problem.feasibleSet) :
    ∃ v : problem.feasibleSet,
      IsGreatest
        (Set.range (fun u : problem.feasibleSet ↦ problem (u : E) ((w : E) - (u : E))))
        (problem (v : E) ((w : E) - (v : E))) := by
  let f : E → ℝ := fun u ↦ problem u ((w : E) - u)
  -- Compactness of the feasible set is the finite-dimensional Heine-Borel input.
  have hcompact : IsCompact problem.feasibleSet := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    exact ⟨problem.feasibleSet_closed, problem.feasibleSet_bounded⟩
  have hnonempty : problem.feasibleSet.Nonempty := ⟨w, w.property⟩
  -- The payoff map is continuous because affine evaluation is continuous in finite dimension.
  have hcont : ContinuousOn f problem.feasibleSet := by
    let linearPart : E →ₗ[ℝ] Dual ℝ E := problem.operator.linear
    let bilinearPart : E →L[ℝ] E →L[ℝ] ℝ := linearPart.toContinuousBilinearMap
    have hbilinear : Continuous fun u : E ↦ bilinearPart u ((w : E) - u) := by
      exact bilinearPart.continuous.clm_apply (continuous_const.sub continuous_id)
    have hconstant : Continuous fun u : E ↦ problem 0 ((w : E) - u) := by
      exact (problem 0).continuous_of_finiteDimensional.comp (continuous_const.sub continuous_id)
    have hrepr :
        f = fun u : E ↦ bilinearPart u ((w : E) - u) + problem 0 ((w : E) - u) := by
      funext u
      -- Expand the affine map into its linear part plus the value at `0`.
      have hdecomp : problem u = linearPart u + problem 0 := by
        simpa using congrFun problem.operator.decomp u
      simpa [f, linearPart, bilinearPart] using
        congrArg (fun φ : Dual ℝ E ↦ φ ((w : E) - u)) hdecomp
    rw [hrepr]
    exact (hbilinear.add hconstant).continuousOn
  obtain ⟨x, hx, hxmax⟩ := hcompact.exists_isMaxOn hnonempty hcont
  have hxmax' : ∀ y ∈ problem.feasibleSet, f y ≤ f x := by
    simpa [IsMaxOn, IsMaxFilter] using hxmax
  refine ⟨⟨x, hx⟩, ?_⟩
  constructor
  · exact ⟨⟨x, hx⟩, rfl⟩
  · rintro y ⟨u, rfl⟩
    exact hxmax' u u.property

/-- Helper for Lemma 6.5: in the finite-dimensional source setting, the payoff range used in the
canonical gap function is bounded above because the defining maximum is attained. -/
lemma gap_payoff_range_bddAbove
    [FiniteDimensional ℝ E]
    (problem : AffineVariationalInequalityProblem E) (w : problem.feasibleSet) :
    BddAbove (Set.range (fun v : problem.feasibleSet ↦ problem (v : E) ((w : E) - (v : E)))) := by
  -- The maximizing comparison point from `exists_isGreatest_gap_payoff` provides an upper bound.
  rcases problem.exists_isGreatest_gap_payoff w with ⟨v, hv⟩
  exact ⟨problem (v : E) ((w : E) - (v : E)), fun z hz ↦ hv.2 hz⟩

/-- Helper for Lemma 6.5: in the finite-dimensional source setting, the canonical gap function is
nonnegative at every feasible point because the feasible point itself contributes the value `0` to
the defining maximum/supremum. -/
lemma gapFunction_nonneg
    [FiniteDimensional ℝ E]
    (problem : AffineVariationalInequalityProblem E) (w : problem.feasibleSet) :
    0 ≤ problem.gapFunction w := by
  rw [problem.gapFunction_def]
  -- The base point `w` is an admissible comparison point, and its payoff is exactly `0`.
  let payoffSet : Set ℝ :=
    Set.range fun v : problem.feasibleSet ↦ problem (v : E) ((w : E) - (v : E))
  have hbdd : BddAbove payoffSet := by
    simpa [payoffSet] using problem.gap_payoff_range_bddAbove w
  have hle :
      problem (w : E) ((w : E) - (w : E)) ≤ sSup payoffSet := by
    exact le_csSup hbdd (Set.mem_range_self w)
  simpa [payoffSet] using hle

/-- Every solution of an affine variational inequality problem has canonical gap value `0`. -/
theorem gapFunction_eq_zero_of_isSolution
    [FiniteDimensional ℝ E]
    (problem : AffineVariationalInequalityProblem E) (wStar : problem.feasibleSet)
    (hsol : problem.IsSolution wStar) :
    problem.gapFunction wStar = 0 := by
  apply le_antisymm
  · rw [problem.gapFunction_def]
    -- Every admissible payoff is bounded above by the reversed VI value at `wStar`.
    let payoffSet : Set ℝ :=
      Set.range fun v : problem.feasibleSet ↦ problem (v : E) ((wStar : E) - (v : E))
    have hnonempty : payoffSet.Nonempty := ⟨_, Set.mem_range_self wStar⟩
    change sSup payoffSet ≤ (0 : ℝ)
    refine csSup_le hnonempty ?_
    rintro y ⟨v, rfl⟩
    have hbase_nonpos : problem (wStar : E) ((wStar : E) - (v : E)) ≤ 0 := by
      have hvi : 0 ≤ problem (wStar : E) ((v : E) - (wStar : E)) := hsol.2 v v.property
      have hneg :
          problem (wStar : E) ((wStar : E) - (v : E)) =
            -problem (wStar : E) ((v : E) - (wStar : E)) := by
        rw [show ((wStar : E) - (v : E)) = -((v : E) - (wStar : E)) by abel, map_neg]
      rw [hneg]
      exact neg_nonpos.mpr hvi
    exact (problem.payoff_le_basepoint wStar v).trans hbase_nonpos
  · exact problem.gapFunction_nonneg wStar

/-- Helper for Lemma 6.5: evaluating the affine operator on a convex combination in its first
argument interpolates the resulting scalar payoff affinely. -/
lemma payoff_first_arg_combo
    (problem : AffineVariationalInequalityProblem E) (w v : problem.feasibleSet) (t : ℝ) (h : E) :
    problem ((1 - t) • (w : E) + t • (v : E)) h =
      (1 - t) * problem (w : E) h + t * problem (v : E) h := by
  -- Rewrite the convex combination as an affine line map so the owner interpolation API applies.
  rw [← AffineMap.lineMap_apply_module]
  rw [problem.operator.apply_lineMap]
  rw [AffineMap.lineMap_apply_module]
  simp [smul_eq_mul]

/-- Helper for Lemma 6.5: if a feasible point fails the variational inequality, then a nearby
feasible comparison point contributes a strictly positive value to the gap supremum. -/
lemma exists_positive_gap_payoff_of_not_isSolution
    (problem : AffineVariationalInequalityProblem E) (w : problem.feasibleSet)
    (hnot : ¬ problem.IsSolution w) :
    ∃ u : problem.feasibleSet, 0 < problem u ((w : E) - (u : E)) := by
  -- Extract a feasible comparison point where the variational inequality is violated.
  have hviol : ¬ ∀ v ∈ problem.feasibleSet, 0 ≤ problem (w : E) (v - (w : E)) := by
    intro hvi
    exact hnot ⟨w.property, hvi⟩
  classical
  push Not at hviol
  rcases hviol with ⟨u, hu_mem, hu_neg⟩
  let uSub : problem.feasibleSet := ⟨u, hu_mem⟩
  let a : ℝ := problem (w : E) ((w : E) - u)
  let b : ℝ := problem u ((w : E) - u)
  have ha_pos : 0 < a := by
    -- Reversing the violated VI direction turns the negative residual into a positive one.
    dsimp [a]
    have hneg :
        problem (w : E) ((w : E) - u) =
          -problem (w : E) (u - (w : E)) := by
      rw [show ((w : E) - u) = -(u - (w : E)) by abel, map_neg]
    rw [hneg]
    exact neg_pos.mpr hu_neg
  let c : ℝ := a + |b|
  have hc_pos : 0 < c := by
    -- The control denominator stays positive because `a > 0`.
    dsimp [c]
    exact add_pos_of_pos_of_nonneg ha_pos (abs_nonneg b)
  let τ : ℝ := a / (2 * c)
  have hτ_pos : 0 < τ := by
    -- Choose a small positive interpolation parameter so the affine interpolation stays positive.
    dsimp [τ]
    positivity
  have hτ_mem : τ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_of_lt hτ_pos
    · have hupper : a ≤ 2 * c := by
        dsimp [c]
        nlinarith [ha_pos, abs_nonneg b]
      have hc2_pos : 0 < 2 * c := by positivity
      exact (div_le_one hc2_pos).2 hupper
  let z : problem.feasibleSet :=
    ⟨AffineMap.lineMap (w : E) u τ, by
      simpa [AffineMap.lineMap_apply_module] using
        problem.feasibleSet_convex.lineMap_mem w.property hu_mem hτ_mem⟩
  have hz_diff : (w : E) - (z : E) = τ • ((w : E) - u) := by
    -- Moving from `w` toward `u` scales the displacement `w - u` by `τ`.
    simpa [z] using AffineMap.left_vsub_lineMap (w : E) u τ
  have hz_scale :
      problem (z : E) ((w : E) - (z : E)) =
        τ * problem (z : E) ((w : E) - u) := by
    -- The affine residual is linear in its second argument.
    rw [hz_diff]
    simp [smul_eq_mul]
  have hz_combo :
      problem (z : E) ((w : E) - u) = (1 - τ) * a + τ * b := by
    -- Interpolate the first argument affinely while keeping the second argument fixed.
    simpa [z, uSub, a, b, AffineMap.lineMap_apply_module] using
      problem.payoff_first_arg_combo w uSub τ ((w : E) - u)
  have hmix_pos : 0 < (1 - τ) * a + τ * b := by
    -- The choice of `τ` makes the negative `b` contribution too small to cancel the positive `a`.
    have hb_lower : -|b| ≤ b := neg_abs_le b
    have hτ_nonneg : 0 ≤ τ := le_of_lt hτ_pos
    have hlower :
        a - τ * c ≤ (1 - τ) * a + τ * b := by
      dsimp [c]
      nlinarith
    have hτc : τ * c = a / 2 := by
      have hc_ne : c ≠ 0 := ne_of_gt hc_pos
      dsimp [τ]
      field_simp [hc_ne]
    have hhalf_pos : 0 < a / 2 := by positivity
    have hhalf_le : a / 2 ≤ (1 - τ) * a + τ * b := by
      nlinarith [hlower, hτc]
    exact lt_of_lt_of_le hhalf_pos hhalf_le
  refine ⟨z, ?_⟩
  -- The scaled affine interpolation now yields a strictly positive canonical payoff.
  rw [hz_scale, hz_combo]
  exact mul_pos hτ_pos hmix_pos

/-- Helper for Lemma 6.5: zero gap is equivalent to the source-facing variational-inequality
solution predicate. -/
lemma isSolution_iff_gapFunction_eq_zero
    [FiniteDimensional ℝ E]
    (problem : AffineVariationalInequalityProblem E) (w : problem.feasibleSet) :
    problem.IsSolution w ↔ problem.gapFunction w = 0 := by
  constructor
  · intro hsol
    -- The forward implication is the previously established zero-gap theorem for actual solutions.
    exact problem.gapFunction_eq_zero_of_isSolution w hsol
  · intro hgap
    by_contra hnot
    rcases problem.exists_positive_gap_payoff_of_not_isSolution w hnot with ⟨u, hu_pos⟩
    have hu_le : problem (u : E) ((w : E) - (u : E)) ≤ problem.gapFunction w := by
      -- Any feasible comparison payoff is bounded above by the defining supremum of `gapFunction`.
      rw [problem.gapFunction_def]
      exact le_csSup (problem.gap_payoff_range_bddAbove w) ⟨u, rfl⟩
    linarith

/-- Helper for Lemma 6.5: for a fixed ambient base point `w`, the canonical owner payoff
`v ↦ problem v (w - v)` is concave on the feasible set. -/
lemma payoff_concaveOn
    (problem : AffineVariationalInequalityProblem E) (w : E) :
    ConcaveOn ℝ problem.feasibleSet (fun v : E ↦ problem v (w - v)) := by
  rw [concaveOn_iff_forall_pos]
  constructor
  · exact problem.feasibleSet_convex
  · intro x hx y hy a b ha hb hab
    let xSub : problem.feasibleSet := ⟨x, hx⟩
    let ySub : problem.feasibleSet := ⟨y, hy⟩
    let z : E := AffineMap.lineMap x y b
    have hcoeff : a = 1 - b := by linarith
    have hz : z ∈ problem.feasibleSet := by
      -- The convex feasible set contains every strict convex combination of feasible points.
      refine problem.feasibleSet_convex.lineMap_mem hx hy ?_
      constructor
      · linarith
      · linarith
    let zSub : problem.feasibleSet := ⟨z, hz⟩
    have hwz :
        w - z = AffineMap.lineMap (w - x) (w - y) b := by
      -- Translating by the fixed base point `w` commutes with the affine line map.
      simpa [z] using AffineMap.vsub_lineMap w x y b
    have hz_linear :
        problem (zSub : E) (w - z) =
          (1 - b) * problem (zSub : E) (w - x) +
            b * problem (zSub : E) (w - y) := by
      -- Expand the second argument through the affine interpolation formula.
      rw [hwz, AffineMap.lineMap_apply_module]
      simp [smul_eq_mul]
    have hx_combo :
        problem (zSub : E) (w - x) =
          (1 - b) * problem (xSub : E) (w - x) +
            b * problem (ySub : E) (w - x) := by
      -- Interpolate the first argument while keeping `w - x` fixed.
      simpa [z, zSub, AffineMap.lineMap_apply_module] using
        problem.payoff_first_arg_combo xSub ySub b (w - x)
    have hy_combo :
        problem (zSub : E) (w - y) =
          (1 - b) * problem (xSub : E) (w - y) +
            b * problem (ySub : E) (w - y) := by
      -- Interpolate the first argument while keeping `w - y` fixed.
      simpa [z, zSub, AffineMap.lineMap_apply_module] using
        problem.payoff_first_arg_combo xSub ySub b (w - y)
    have hcross :
        problem (xSub : E) (w - x) + problem (ySub : E) (w - y) ≤
          problem (xSub : E) (w - y) + problem (ySub : E) (w - x) := by
      -- The cross terms dominate the diagonal terms by monotonicity of the linear part.
      let d : E := y - x
      have hrewrite :
          problem.operator.linear d d =
            problem (ySub : E) (y - x) - problem (xSub : E) (y - x) := by
        simpa [d] using congrArg (fun f : Dual ℝ E ↦ f d) (problem.operator.linearMap_vsub y x)
      have hdiag :
          0 ≤ problem (ySub : E) (y - x) - problem (xSub : E) (y - x) := by
        rw [← hrewrite]
        exact problem.linear_nonnegative d
      have hx_shift :
          problem (xSub : E) (w - y) =
            problem (xSub : E) (w - x) - problem (xSub : E) (y - x) := by
        have hdecomp : w - y = (w - x) - (y - x) := by
          simp [sub_eq_add_neg, add_left_comm, add_assoc]
        rw [hdecomp, map_sub]
      have hy_shift :
          problem (ySub : E) (w - x) =
            problem (ySub : E) (w - y) + problem (ySub : E) (y - x) := by
        have hdecomp : w - x = (w - y) + (y - x) := by
          simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        rw [hdecomp, map_add]
      linarith
    have hstep :
        a * problem (xSub : E) (w - x) + b * problem (ySub : E) (w - y) ≤
          problem (zSub : E) (w - z) := by
      -- After expanding both interpolations, the cross terms are bounded below by the diagonal sum.
      rw [hz_linear, hx_combo, hy_combo]
      have h_one_sub_b : 0 ≤ 1 - b := by linarith
      have hcross' :
          (1 - b) * b * (problem (xSub : E) (w - x) + problem (ySub : E) (w - y)) ≤
            (1 - b) * b * (problem (xSub : E) (w - y) + problem (ySub : E) (w - x)) := by
        gcongr
      rw [hcoeff]
      nlinarith [hcross']
    have hz_eq_combo : z = a • x + b • y := by
      dsimp [z]
      rw [AffineMap.lineMap_apply_module, hcoeff]
    simpa [xSub, ySub, zSub, hz_eq_combo] using hstep

/-- Helper for Lemma 6.5: the hard reverse direction reduces to showing that the global infimum
of the canonical gap function is `0`. -/
lemma iInf_gapFunction_eq_zero
    [FiniteDimensional ℝ E]
    (problem : AffineVariationalInequalityProblem E) :
    (⨅ w : problem.feasibleSet, problem.gapFunction w) = 0 := by
  by_cases hne : Nonempty problem.feasibleSet
  · letI : Nonempty problem.feasibleSet := hne
    have hfeas_nonempty : problem.feasibleSet.Nonempty := by
      rcases hne with ⟨w⟩
      exact ⟨w, w.property⟩
    have hcompact : IsCompact problem.feasibleSet := by
      -- Finite-dimensional Heine-Borel makes the feasible set compact.
      rw [Metric.isCompact_iff_isClosed_bounded]
      exact ⟨problem.feasibleSet_closed, problem.feasibleSet_bounded⟩
    have hfy :
        ∀ y ∈ problem.feasibleSet,
          LowerSemicontinuousOn (fun x : E ↦ problem y (x - y)) problem.feasibleSet := by
      intro y hy
      -- For fixed `y`, the payoff is continuous, hence lower semicontinuous.
      let hyCont : Continuous fun x : E ↦ problem y (x - y) :=
        (problem y).continuous_of_finiteDimensional.comp (continuous_id.sub continuous_const)
      exact ContinuousOn.lowerSemicontinuousOn hyCont.continuousOn
    have hfy' :
        ∀ y ∈ problem.feasibleSet,
          QuasiconvexOn ℝ problem.feasibleSet (fun x : E ↦ problem y (x - y)) := by
      intro y hy
      -- For fixed `y`, the payoff is affine in `x`, hence convex and therefore quasiconvex.
      let shift : E →ᵃ[ℝ] E := AffineMap.id ℝ E - AffineMap.const ℝ E y
      have hconv_univ :
          ConvexOn ℝ Set.univ (fun x : E ↦ problem y (x - y)) := by
        simpa [shift] using ((problem y).convexOn convex_univ).comp_affineMap shift
      exact (hconv_univ.subset (Set.subset_univ _) problem.feasibleSet_convex).quasiconvexOn
    have hfx :
        ∀ x ∈ problem.feasibleSet,
          UpperSemicontinuousOn (fun y : E ↦ problem y (x - y)) problem.feasibleSet := by
      intro x hx
      -- For fixed `x`, the payoff is continuous in `y`, hence upper semicontinuous.
      let linearPart : E →ₗ[ℝ] Dual ℝ E := problem.operator.linear
      let bilinearPart : E →L[ℝ] E →L[ℝ] ℝ := linearPart.toContinuousBilinearMap
      have hbilinear :
          Continuous fun y : E ↦ bilinearPart y (x - y) := by
        exact bilinearPart.continuous.clm_apply (continuous_const.sub continuous_id)
      have hconstant :
          Continuous fun y : E ↦ problem 0 (x - y) := by
        exact (problem 0).continuous_of_finiteDimensional.comp (continuous_const.sub continuous_id)
      have hrepr :
          (fun y : E ↦ problem y (x - y)) =
            fun y : E ↦ bilinearPart y (x - y) + problem 0 (x - y) := by
        funext y
        have hdecomp : problem y = linearPart y + problem 0 := by
          simpa using congrFun problem.operator.decomp y
        simpa [linearPart, bilinearPart] using
          congrArg (fun φ : Dual ℝ E ↦ φ (x - y)) hdecomp
      rw [hrepr]
      exact ContinuousOn.upperSemicontinuousOn (hbilinear.add hconstant).continuousOn
    have hfx' :
        ∀ x ∈ problem.feasibleSet,
          QuasiconcaveOn ℝ problem.feasibleSet (fun y : E ↦ problem y (x - y)) := by
      intro x hx
      -- Concavity of the source payoff is the quasiconcavity input for Sion.
      exact (problem.payoff_concaveOn x).quasiconcaveOn
    obtain ⟨w0, hw0, v0, hv0, hsaddle⟩ :=
      Sion.exists_isSaddlePointOn
        hfeas_nonempty
        problem.feasibleSet_convex
        hcompact
        hfy
        hfy'
        problem.feasibleSet_convex
        hfeas_nonempty
        hcompact
        hfx
        hfx'
    have hw0_nonpos : problem.gapFunction ⟨w0, hw0⟩ ≤ 0 := by
      -- The saddle point gives a feasible `v0` maximizing the payoff at `w0`, and comparing with
      -- the diagonal value at `(v0, v0)` forces that maximum to be nonpositive.
      rw [problem.gapFunction_def]
      have hmax : ∀ v ∈ problem.feasibleSet, problem v (w0 - v) ≤ problem v0 (w0 - v0) := by
        intro v hv
        exact hsaddle w0 hw0 v hv
      have hdiag : problem v0 (w0 - v0) ≤ 0 := by
        simpa using hsaddle v0 hv0 v0 hv0
      refine csSup_le ?_ ?_
      · exact ⟨_, Set.mem_range_self ⟨w0, hw0⟩⟩
      · rintro y ⟨v, rfl⟩
        exact (hmax v v.property).trans hdiag
    have hbelow : BddBelow (Set.range fun w : problem.feasibleSet ↦ problem.gapFunction w) := by
      refine ⟨0, ?_⟩
      rintro y ⟨w, rfl⟩
      exact problem.gapFunction_nonneg w
    refine le_antisymm ?_ ?_
    · exact (ciInf_le hbelow ⟨w0, hw0⟩).trans hw0_nonpos
    · exact le_ciInf fun w ↦ problem.gapFunction_nonneg w
  · letI : IsEmpty problem.feasibleSet := not_nonempty_iff.mp hne
    -- On the empty feasible subtype, indexed infima over `ℝ` reduce to `0`.
    simp

/-- Helper for Lemma 6.5: on the Chapter 6 owner, a feasible point solves the affine variational
inequality problem exactly when it minimizes the canonical gap function on the feasible subtype. -/
theorem isSolution_iff_isMinOn_gapFunction
    [FiniteDimensional ℝ E]
    (problem : AffineVariationalInequalityProblem E) (wStar : problem.feasibleSet) :
    problem.IsSolution wStar ↔ IsMinOn problem.gapFunction Set.univ wStar := by
  constructor
  · intro hsol
    -- A zero gap at `wStar` and nonnegativity everywhere else give the minimizing property.
    refine isMinOn_univ_iff.mpr ?_
    intro w
    rw [problem.gapFunction_eq_zero_of_isSolution wStar hsol]
    exact problem.gapFunction_nonneg w
  · intro hmin
    -- The reverse implication factors through the zero-gap characterization.
    have hzero : problem.gapFunction wStar = 0 := by
      letI : Nonempty problem.feasibleSet := ⟨wStar⟩
      rw [← problem.iInf_gapFunction_eq_zero]
      have hbelow : BddBelow (Set.range fun w : problem.feasibleSet ↦ problem.gapFunction w) := by
        refine ⟨0, ?_⟩
        rintro y ⟨w, rfl⟩
        exact problem.gapFunction_nonneg w
      have hmin' : ∀ w : problem.feasibleSet, problem.gapFunction wStar ≤ problem.gapFunction w :=
        isMinOn_univ_iff.mp hmin
      exact le_antisymm
        (le_ciInf hmin')
        (show
            (⨅ w : problem.feasibleSet, problem.gapFunction w) ≤
              problem.gapFunction wStar from
          ciInf_le hbelow wStar)
    exact (problem.isSolution_iff_gapFunction_eq_zero wStar).2
      hzero

/-- Helper for Lemma 6.5: once the infimum of the canonical gap function is known to be `0`, every
whole-set minimizer has zero gap. -/
lemma gapFunction_eq_zero_of_isMinOn_aux
    [FiniteDimensional ℝ E]
    (problem : AffineVariationalInequalityProblem E) (wStar : problem.feasibleSet)
    (hmin : IsMinOn problem.gapFunction Set.univ wStar) :
    problem.gapFunction wStar = 0 := by
  -- Compare the minimizing value with the global infimum, which the previous helper identifies.
  letI : Nonempty problem.feasibleSet := ⟨wStar⟩
  rw [← problem.iInf_gapFunction_eq_zero]
  have hbelow : BddBelow (Set.range fun w : problem.feasibleSet ↦ problem.gapFunction w) := by
    refine ⟨0, ?_⟩
    rintro y ⟨w, rfl⟩
    exact problem.gapFunction_nonneg w
  have hmin' : ∀ w : problem.feasibleSet, problem.gapFunction wStar ≤ problem.gapFunction w := by
    exact isMinOn_univ_iff.mp hmin
  exact le_antisymm
    (le_ciInf hmin')
    (show
        (⨅ w : problem.feasibleSet, problem.gapFunction w) ≤ problem.gapFunction wStar from
      ciInf_le hbelow wStar)

/-- Every minimizer of the canonical gap function has gap value `0`. -/
theorem gapFunction_eq_zero_of_isMinOn
    [FiniteDimensional ℝ E]
    (problem : AffineVariationalInequalityProblem E) (wStar : problem.feasibleSet)
    (hmin : IsMinOn problem.gapFunction Set.univ wStar) :
    problem.gapFunction wStar = 0 := by
  -- This theorem is the public corollary of the infimum-zero helper.
  exact problem.gapFunction_eq_zero_of_isMinOn_aux wStar hmin

end AffineVariationalInequalityProblem

/-- Helper for Lemma 6.5: the source-facing attainment hypothesis `hψmax` identifies the displayed
supremum with the value of the payoff `v ↦ ⟪B(v), w - v⟫` at a feasible maximizer. -/
theorem explicitGapFunction_eq_maxValue
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (w : Q) :
    ∃ v : Q,
      sSup
          (Set.range fun u : Q ↦
            inner ℝ (B (u : E)) ((w : E) - (u : E))) =
        inner ℝ (B (v : E)) ((w : E) - (v : E)) := by
  -- Unpack the maximizer supplied by `hψmax` and rewrite the displayed supremum through it.
  rcases hψmax w with ⟨v, hv⟩
  exact ⟨v, hv.csSup_eq⟩

/-- Helper for Lemma 6.5: rewriting the explicit payoff at `v` against the base point `w`
isolates the monotone diagonal term `⟪B (w - v), w - v⟫`. -/
lemma explicitPayoff_eq_basepoint_sub_diagonal
    [InnerProductSpace ℝ E]
    (B : E →ₗ[ℝ] E) (w v : E) :
    inner ℝ (B v) (w - v) =
      inner ℝ (B w) (w - v) - inner ℝ (B (w - v)) (w - v) := by
  -- Evaluate `B (w - v)` on the displacement `w - v` and expand the first argument linearly.
  have happly :
      inner ℝ (B (w - v)) (w - v) =
        inner ℝ (B w) (w - v) - inner ℝ (B v) (w - v) := by
    simpa [inner_sub_left] using
      congrArg (fun z : E ↦ inner ℝ z (w - v)) (B.map_sub w v)
  linarith

/-- Helper for Lemma 6.5: monotonicity of `B` bounds every explicit payoff by the basepoint
payoff at the same displacement. -/
lemma explicitPayoff_le_basepoint
    [InnerProductSpace ℝ E]
    (B : E →ₗ[ℝ] E) (hBmono : ∀ h : E, 0 ≤ inner ℝ (B h) h) (w v : E) :
    inner ℝ (B v) (w - v) ≤ inner ℝ (B w) (w - v) := by
  -- The diagonal term from the previous rewrite is nonnegative by the monotonicity hypothesis.
  have hdiag : 0 ≤ inner ℝ (B (w - v)) (w - v) := hBmono (w - v)
  have hrewrite := explicitPayoff_eq_basepoint_sub_diagonal B w v
  linarith

/-- Helper for Lemma 6.5: the pointwise maximizer hypothesis `hψmax` bounds the explicit payoff
range above, so the displayed supremum is a genuine real number. -/
lemma explicitGapFunction_range_bddAbove
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (w : Q) :
    BddAbove
      (Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((w : E) - (v : E))) := by
  -- The maximizing comparison point produced by `hψmax` is an upper bound for the whole range.
  rcases hψmax w with ⟨v, hv⟩
  exact ⟨_, fun y hy ↦ hv.2 hy⟩

/-- Helper for Lemma 6.5: the explicit gap is always nonnegative because the base point itself
contributes the value `0` to the displayed supremum. -/
lemma explicitGapFunction_nonneg
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (w : Q) :
    0 ≤
      sSup
        (Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((w : E) - (v : E))) := by
  -- Insert the feasible point `w` itself into the supremum formula.
  let payoffSet : Set ℝ :=
    Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((w : E) - (v : E))
  have hbdd : BddAbove payoffSet := by
    simpa [payoffSet] using explicitGapFunction_range_bddAbove Q B hψmax w
  have hle : inner ℝ (B (w : E)) ((w : E) - (w : E)) ≤ sSup payoffSet := by
    exact le_csSup hbdd (Set.mem_range_self w)
  simpa [payoffSet] using hle

/-- Helper for Lemma 6.5: replacing the base point by a feasible line-map point makes the explicit
gap at most the corresponding convex combination of the endpoint gap values. -/
lemma explicitGapFunction_le_combo_of_eq_lineMap
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (w u z : Q) {t : ℝ}
    (hz : (z : E) = AffineMap.lineMap (w : E) (u : E) t)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    sSup
        (Set.range fun v : Q ↦
          inner ℝ (B (v : E)) ((z : E) - (v : E))) ≤
      (1 - t) *
          sSup
            (Set.range fun v : Q ↦
              inner ℝ (B (v : E)) ((w : E) - (v : E))) +
        t *
          sSup
            (Set.range fun v : Q ↦
              inner ℝ (B (v : E)) ((u : E) - (v : E))) := by
  let payoffSetW : Set ℝ :=
    Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((w : E) - (v : E))
  let payoffSetU : Set ℝ :=
    Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((u : E) - (v : E))
  let payoffSetZ : Set ℝ :=
    Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((z : E) - (v : E))
  have hbddW : BddAbove payoffSetW := by
    simpa [payoffSetW] using explicitGapFunction_range_bddAbove Q B hψmax w
  have hbddU : BddAbove payoffSetU := by
    simpa [payoffSetU] using explicitGapFunction_range_bddAbove Q B hψmax u
  have hnonempty : payoffSetZ.Nonempty := ⟨_, Set.mem_range_self w⟩
  have h_one_sub_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  -- Control every comparison payoff at `z` by the endpoint suprema and then pass to `sSup`.
  refine csSup_le hnonempty ?_
  rintro y ⟨v, rfl⟩
  have hw_le : inner ℝ (B (v : E)) ((w : E) - (v : E)) ≤ sSup payoffSetW := by
    exact le_csSup hbddW ⟨v, rfl⟩
  have hu_le : inner ℝ (B (v : E)) ((u : E) - (v : E)) ≤ sSup payoffSetU := by
    exact le_csSup hbddU ⟨v, rfl⟩
  have hsplit :
      inner ℝ (B (v : E)) ((z : E) - (v : E)) =
        (1 - t) * inner ℝ (B (v : E)) ((w : E) - (v : E)) +
          t * inner ℝ (B (v : E)) ((u : E) - (v : E)) := by
    rw [hz, AffineMap.lineMap_apply_module]
    have hvec :
        (1 - t) • ((w : E) - (v : E)) + t • ((u : E) - (v : E)) =
          ((1 - t) • (w : E) + t • (u : E)) - (v : E) := by
      calc
        (1 - t) • ((w : E) - (v : E)) + t • ((u : E) - (v : E))
            = ((1 - t) • (w : E) + t • (u : E)) - ((1 - t) • (v : E) + t • (v : E)) := by
                rw [smul_sub, smul_sub]
                abel
        _ = ((1 - t) • (w : E) + t • (u : E)) - (v : E) := by
              congr 1
              calc
                (1 - t) • (v : E) + t • (v : E) = ((1 - t) + t) • (v : E) := by
                  rw [add_smul]
                _ = (1 : ℝ) • (v : E) := by ring_nf
                _ = v := by simp
    rw [← hvec, inner_add_right]
    let L : E →ₗ[ℝ] ℝ := (innerₗ E) (B (v : E))
    change L ((1 - t) • ((w : E) - (v : E))) + L (t • ((u : E) - (v : E))) =
      (1 - t) * L ((w : E) - (v : E)) + t * L ((u : E) - (v : E))
    rw [LinearMap.map_smul, LinearMap.map_smul]
    ring
  change inner ℝ (B (v : E)) ((z : E) - (v : E)) ≤
      (1 - t) * sSup payoffSetW + t * sSup payoffSetU
  rw [hsplit]
  have hleft :
      (1 - t) * inner ℝ (B (v : E)) ((w : E) - (v : E)) ≤
        (1 - t) * sSup payoffSetW := by
    exact mul_le_mul_of_nonneg_left hw_le h_one_sub_nonneg
  have hright :
      t * inner ℝ (B (v : E)) ((u : E) - (v : E)) ≤
        t * sSup payoffSetU := by
    exact mul_le_mul_of_nonneg_left hu_le ht.1
  exact add_le_add hleft hright

/-- Helper for Lemma 6.5: the explicit gap surface is convex on `Q`, because every feasible
segment value is controlled by the corresponding convex combination of the endpoint gap values. -/
lemma explicitGapFunction_convexOn
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E)))) :
    ConvexOn ℝ Q
      (fun w : E ↦
        sSup
          (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) := by
  rw [convexOn_iff_forall_pos]
  constructor
  · exact hQconv
  · intro x hx y hy a b ha hb hab
    let xSub : Q := ⟨x, hx⟩
    let ySub : Q := ⟨y, hy⟩
    let z : Q :=
      ⟨AffineMap.lineMap x y b, by
        -- The feasible set stays closed under the segment from `x` to `y`.
        simpa [AffineMap.lineMap_apply_module] using
          hQconv.lineMap_mem hx hy ⟨le_of_lt hb, by linarith⟩⟩
    have hz : (z : E) = AffineMap.lineMap x y b := rfl
    have hcombo :=
      explicitGapFunction_le_combo_of_eq_lineMap Q B hψmax xSub ySub z hz
        ⟨le_of_lt hb, by linarith⟩
    have hab' : a = 1 - b := by linarith
    -- Rewrite the line-map parameterization back to the `a • x + b • y` convex-combination form.
    simpa [xSub, ySub, z, AffineMap.lineMap_apply_module, hab'] using hcombo

/-- Helper for Lemma 6.5: if `v` is active in the explicit supremum at `wStar`, then the affine
slice with slope `B v` is a constrained subgradient of the explicit gap surface at `wStar`. -/
lemma activeExplicitGradient_mem_subdifferentialWithin
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    {wStar v : Q}
    (hv :
      IsGreatest
        (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
        (inner ℝ (B (v : E)) ((wStar : E) - (v : E)))) :
    B (v : E) ∈
      subdifferentialWithin Q
        ((fun w : E ↦
          sSup
            (Set.range fun u : Q ↦ inner ℝ (B (u : E)) (w - (u : E)))) : E → ℝ)
        (wStar : E) := by
  rw [mem_subdifferentialWithin_iff]
  refine ⟨wStar.property, ?_⟩
  intro y hy
  let ySub : Q := ⟨y, hy⟩
  have hy_le :
      inner ℝ (B (v : E)) (y - (v : E)) ≤
        sSup
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) (y - (u : E))) := by
    exact le_csSup (explicitGapFunction_range_bddAbove Q B hψmax ySub) ⟨v, rfl⟩
  have hv_eq :
      sSup
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E))) =
        inner ℝ (B (v : E)) ((wStar : E) - (v : E)) :=
    hv.csSup_eq
  have hsplit :
      inner ℝ (B (v : E)) (y - (v : E)) =
        inner ℝ (B (v : E)) ((wStar : E) - (v : E)) +
          inner ℝ (B (v : E)) (y - (wStar : E)) := by
    have hdecomp :
        y - (v : E) = ((wStar : E) - (v : E)) + (y - (wStar : E)) := by
      abel
    rw [hdecomp, inner_add_right]
  -- Compare the active affine slice with the explicit supremum at `y`, then rewrite the
  -- base-point slice value through activity at `wStar`.
  calc
    sSup
        (Set.range fun u : Q ↦ inner ℝ (B (u : E)) (y - (u : E)))
        ≥ inner ℝ (B (v : E)) (y - (v : E)) := hy_le
    _ = inner ℝ (B (v : E)) ((wStar : E) - (v : E)) +
          inner ℝ (B (v : E)) (y - (wStar : E)) := hsplit
    _ =
        sSup
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E))) +
          inner ℝ (B (v : E)) (y - (wStar : E)) := by
            rw [hv_eq]

/-- Helper for Lemma 6.5: a maximizer at `w` still gives a concrete lower bound for the explicit
gap at any feasible point on the segment from `w` to that maximizer. -/
lemma explicitGapFunction_lineMap_lowerBound_of_isGreatest
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (w v z : Q) {t : ℝ}
    (hv :
      IsGreatest
        (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
        (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (hz : (z : E) = AffineMap.lineMap (w : E) (v : E) t) :
    (1 - t) * inner ℝ (B (v : E)) ((w : E) - (v : E)) ≤
      sSup
        (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((z : E) - (u : E))) := by
  let payoffSetZ : Set ℝ :=
    Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((z : E) - (u : E))
  have hbddZ : BddAbove payoffSetZ := by
    simpa [payoffSetZ] using explicitGapFunction_range_bddAbove Q B hψmax z
  have hle :
      inner ℝ (B (v : E)) ((z : E) - (v : E)) ≤ sSup payoffSetZ := by
    exact le_csSup hbddZ ⟨v, rfl⟩
  have hvalue :
      inner ℝ (B (v : E)) ((z : E) - (v : E)) =
        (1 - t) * inner ℝ (B (v : E)) ((w : E) - (v : E)) := by
    rw [hz]
    have hvsub :
        AffineMap.lineMap (w : E) (v : E) t - (v : E) =
          (1 - t) • ((w : E) - (v : E)) := by
      simpa using AffineMap.lineMap_vsub_right (w : E) (v : E) t
    rw [hvsub]
    let L : E →ₗ[ℝ] ℝ := (innerₗ E) (B (v : E))
    change L ((1 - t) • ((w : E) - (v : E))) = (1 - t) * L ((w : E) - (v : E))
    rw [LinearMap.map_smul]
    ring
  rw [← hvalue]
  exact hle

/-- Helper for Lemma 6.5: every source-facing solution has explicit gap value `0`. -/
lemma explicitGapFunction_eq_zero_of_isSolutionAux
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hBmono : ∀ h : E, 0 ≤ inner ℝ (B h) h)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hsol : ∀ v ∈ Q, 0 ≤ inner ℝ (B (wStar : E)) (v - (wStar : E))) :
    sSup
      (Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((wStar : E) - (v : E))) = 0 := by
  apply le_antisymm
  · let payoffSet : Set ℝ :=
      Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((wStar : E) - (v : E))
    -- Every explicit payoff is bounded above by the reversed VI value at `wStar`.
    change sSup payoffSet ≤ (0 : ℝ)
    have hnonempty : payoffSet.Nonempty := ⟨_, Set.mem_range_self wStar⟩
    refine csSup_le hnonempty ?_
    rintro y ⟨v, rfl⟩
    have hbase_nonpos : inner ℝ (B (wStar : E)) ((wStar : E) - (v : E)) ≤ 0 := by
      have hvi : 0 ≤ inner ℝ (B (wStar : E)) ((v : E) - (wStar : E)) := hsol v v.property
      have hneg :
          inner ℝ (B (wStar : E)) ((wStar : E) - (v : E)) =
            -inner ℝ (B (wStar : E)) ((v : E) - (wStar : E)) := by
        rw [show ((wStar : E) - (v : E)) = -((v : E) - (wStar : E)) by abel, inner_neg_right]
      rw [hneg]
      exact neg_nonpos.mpr hvi
    exact (explicitPayoff_le_basepoint B hBmono (wStar : E) (v : E)).trans hbase_nonpos
  · exact explicitGapFunction_nonneg Q B hψmax wStar

/-- Helper for Lemma 6.5: evaluating `B` on a convex combination in its first argument
interpolates the resulting explicit payoff affinely. -/
lemma explicitPayoff_first_arg_combo
    [InnerProductSpace ℝ E]
    (B : E →ₗ[ℝ] E) (w v : E) (t : ℝ) (h : E) :
    inner ℝ (B ((1 - t) • w + t • v)) h =
      (1 - t) * inner ℝ (B w) h + t * inner ℝ (B v) h := by
  -- Expand the first argument through linearity of `B` and bilinearity of the inner product.
  rw [real_inner_comm, real_inner_comm h (B w), real_inner_comm h (B v)]
  let L : E →ₗ[ℝ] ℝ := (innerₗ E) h
  change L (B ((1 - t) • w + t • v)) = (1 - t) * L (B w) + t * L (B v)
  rw [map_add, map_smul, map_smul, LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]
  simp [L, innerₗ_apply_apply]

/-- Helper for Lemma 6.5: if the explicit variational inequality fails at `w`, then a nearby
feasible point contributes a strictly positive explicit payoff. -/
lemma exists_positive_explicitPayoff_of_not_isSolution
    [InnerProductSpace ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (w : Q)
    (hnot : ¬ ∀ v ∈ Q, 0 ≤ inner ℝ (B (w : E)) (v - (w : E))) :
    ∃ u : Q, 0 < inner ℝ (B (u : E)) ((w : E) - (u : E)) := by
  -- Extract a feasible comparison point where the explicit variational inequality is violated.
  classical
  push Not at hnot
  rcases hnot with ⟨u, hu_mem, hu_neg⟩
  let uSub : Q := ⟨u, hu_mem⟩
  let a : ℝ := inner ℝ (B (w : E)) ((w : E) - u)
  let b : ℝ := inner ℝ (B u) ((w : E) - u)
  have ha_pos : 0 < a := by
    -- Reversing the violated inequality turns the residual at `u` into a positive quantity.
    dsimp [a]
    have hneg :
        inner ℝ (B (w : E)) ((w : E) - u) =
          -inner ℝ (B (w : E)) (u - (w : E)) := by
      rw [show ((w : E) - u) = -(u - (w : E)) by abel, inner_neg_right]
    rw [hneg]
    exact neg_pos.mpr hu_neg
  let c : ℝ := a + |b|
  have hc_pos : 0 < c := by
    -- The denominator controlling the interpolation scale stays positive because `a > 0`.
    dsimp [c]
    exact add_pos_of_pos_of_nonneg ha_pos (abs_nonneg b)
  let τ : ℝ := a / (2 * c)
  have hτ_pos : 0 < τ := by
    -- Choose a small positive interpolation parameter that keeps the later affine estimate strict.
    dsimp [τ]
    positivity
  have hτ_mem : τ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_of_lt hτ_pos
    · have hupper : a ≤ 2 * c := by
        dsimp [c]
        nlinarith [ha_pos, abs_nonneg b]
      have hc2_pos : 0 < 2 * c := by
        positivity
      exact (div_le_one hc2_pos).2 hupper
  let z : Q :=
    ⟨AffineMap.lineMap (w : E) u τ, by
      simpa [AffineMap.lineMap_apply_module] using hQconv.lineMap_mem w.property hu_mem hτ_mem⟩
  have hz_diff : (w : E) - (z : E) = τ • ((w : E) - u) := by
    -- Moving from `w` toward `u` scales the displacement `w - u` by the chosen parameter `τ`.
    simpa [z] using AffineMap.left_vsub_lineMap (w : E) u τ
  have hz_scale :
      inner ℝ (B (z : E)) ((w : E) - (z : E)) =
        τ * inner ℝ (B (z : E)) ((w : E) - u) := by
    -- The explicit payoff is linear in its second argument.
    rw [hz_diff]
    let L : E →ₗ[ℝ] ℝ := (innerₗ E) (B (z : E))
    change L (τ • ((w : E) - u)) = τ * L ((w : E) - u)
    rw [LinearMap.map_smul]
    simpa [smul_eq_mul]
  have hz_combo :
      inner ℝ (B (z : E)) ((w : E) - u) = (1 - τ) * a + τ * b := by
    -- Interpolate the first argument affinely while keeping the displacement fixed.
    simpa [z, uSub, a, b, AffineMap.lineMap_apply_module] using
      explicitPayoff_first_arg_combo B (w : E) u τ ((w : E) - u)
  have hmix_pos : 0 < (1 - τ) * a + τ * b := by
    -- The negative `b` contribution is too small to cancel the positive term coming from `a`.
    have hb_lower : -|b| ≤ b := neg_abs_le b
    have hlower :
        a - τ * c ≤ (1 - τ) * a + τ * b := by
      dsimp [c]
      nlinarith
    have hτc : τ * c = a / 2 := by
      have hc_ne : c ≠ 0 := ne_of_gt hc_pos
      dsimp [τ]
      field_simp [hc_ne]
    have hhalf_pos : 0 < a / 2 := by positivity
    have hhalf_le : a / 2 ≤ (1 - τ) * a + τ * b := by
      nlinarith [hlower, hτc]
    exact lt_of_lt_of_le hhalf_pos hhalf_le
  refine ⟨z, ?_⟩
  -- The scaled affine interpolation now yields a strictly positive explicit payoff.
  rw [hz_scale, hz_combo]
  exact mul_pos hτ_pos hmix_pos

/-- Helper for Lemma 6.5: failure of the explicit variational inequality forces the displayed gap
value to be strictly positive. -/
lemma explicitGapFunction_pos_of_not_isSolution
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (w : Q)
    (hnot : ¬ ∀ v ∈ Q, 0 ≤ inner ℝ (B (w : E)) (v - (w : E))) :
    0 <
      sSup
        (Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((w : E) - (v : E))) := by
  rcases exists_positive_explicitPayoff_of_not_isSolution Q hQconv B w hnot with
    ⟨u, hu_pos⟩
  have hu_le :
      inner ℝ (B (u : E)) ((w : E) - (u : E)) ≤
        sSup (Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((w : E) - (v : E))) := by
    -- Compare the positive feasible payoff with the defining supremum of the explicit gap.
    exact le_csSup (explicitGapFunction_range_bddAbove Q B hψmax w) ⟨u, rfl⟩
  exact lt_of_lt_of_le hu_pos hu_le

/-- Helper for Lemma 6.5: a subtype minimizer of the explicit gap surface is the corresponding
ambient minimizer on `Q`. -/
lemma isMinOn_explicitGapAmbient_of_subtype
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E) (wStar : Q)
    (hmin : IsMinOn
      (fun w : Q ↦
        sSup
          (Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((w : E) - (v : E))))
      Set.univ
      wStar) :
    IsMinOn
      (fun w : E ↦
        sSup
          (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E))))
      Q
      (wStar : E) := by
  refine isMinOn_iff.mpr ?_
  intro y hy
  -- Evaluate the subtype minimizer inequality at the feasible ambient comparison point `y`.
  exact (isMinOn_univ_iff.mp hmin) ⟨y, hy⟩

/-- Helper for Lemma 6.5: a constrained minimizer yields the zero relative subgradient on the
feasible set. -/
lemma zero_mem_subdifferentialWithin_of_isMinOn
    [InnerProductSpace ℝ E]
    {Q : Set E} {f : E → ℝ} {xStar : E}
    (hxStar : xStar ∈ Q) (hmin : IsMinOn f Q xStar) :
    (0 : E) ∈ subdifferentialWithin Q f xStar := by
  rw [mem_subdifferentialWithin_iff]
  refine ⟨hxStar, ?_⟩
  intro y hy
  -- The zero vector records exactly the minimizing inequality `f xStar ≤ f y`.
  simpa using (isMinOn_iff.mp hmin) y hy

/-- Helper for Lemma 6.5: a zero relative subgradient already encodes constrained minimality. -/
lemma isMinOn_of_zero_mem_subdifferentialWithin
    [InnerProductSpace ℝ E]
    {Q : Set E} {f : E → ℝ} {xStar : E}
    (hzero : (0 : E) ∈ subdifferentialWithin Q f xStar) :
    IsMinOn f Q xStar := by
  rcases (mem_subdifferentialWithin_iff.mp hzero) with ⟨hxStar, hminorant⟩
  refine isMinOn_iff.mpr ?_
  intro y hy
  -- Evaluate the zero-slope support inequality at each feasible comparison point.
  simpa using hminorant hy

/-- Helper for Lemma 6.5: every explicit slice `x ↦ ⟪B(v), x - v⟫` has the constant gradient
`B(v)` on `Q`. -/
lemma explicitSliceGradient_mem_subdifferentialWithin
    [InnerProductSpace ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E) (wStar v : Q) :
    B (v : E) ∈
      subdifferentialWithin Q
        ((fun x : E ↦ inner ℝ (B (v : E)) (x - (v : E))) : E → ℝ)
        (wStar : E) := by
  rw [mem_subdifferentialWithin_iff]
  refine ⟨wStar.property, ?_⟩
  intro y hy
  have hsplit :
      inner ℝ (B (v : E)) (y - (v : E)) =
        inner ℝ (B (v : E)) ((wStar : E) - (v : E)) +
          inner ℝ (B (v : E)) (y - (wStar : E)) := by
    -- Split the target displacement through the base point `wStar`.
    have hdecomp :
        y - (v : E) = ((wStar : E) - (v : E)) + (y - (wStar : E)) := by
      abel
    rw [hdecomp, inner_add_right]
  -- The affine slice satisfies the subgradient inequality with equality.
  linarith

/-- Helper for Lemma 6.5: on feasible points, the real explicit gap coincides with the Chapter 3
`WithTop ℝ` pointwise-supremum owner over the ambient feasible set `Q`. -/
lemma explicitGapFunction_coe_eq_pointwiseSupremumOn
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    {x : E} (hx : x ∈ Q) :
    ((sSup (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (x - (v : E))) : ℝ) : WithTop ℝ) =
      pointwiseSupremumOn Q
        (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ))
        x := by
  let xSub : Q := ⟨x, hx⟩
  rcases hψmax xSub with ⟨v, hv⟩
  let payoffSetTop : Set (WithTop ℝ) :=
    (fun u : E ↦ (inner ℝ (B u) (x - u) : WithTop ℝ)) '' Q
  have hmemTop :
      ((inner ℝ (B (v : E)) (x - (v : E)) : ℝ) : WithTop ℝ) ∈ payoffSetTop := by
    exact ⟨v, v.property, rfl⟩
  have hnonemptyTop : payoffSetTop.Nonempty := ⟨_, hmemTop⟩
  have htop_eq :
      sSup payoffSetTop =
        ((inner ℝ (B (v : E)) (x - (v : E)) : ℝ) : WithTop ℝ) := by
    apply le_antisymm
    · refine csSup_le hnonemptyTop ?_
      rintro y ⟨u, hu, rfl⟩
      have hu_le :
          inner ℝ (B u) (x - u) ≤ inner ℝ (B (v : E)) (x - (v : E)) := by
        simpa [xSub] using hv.2 ⟨(⟨u, hu⟩ : Q), rfl⟩
      change
        (((inner ℝ (B u) (x - u) : ℝ) : WithTop ℝ) ≤
          ((inner ℝ (B (v : E)) (x - (v : E)) : ℝ) : WithTop ℝ))
      exact_mod_cast hu_le
    · exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ hmemTop
  -- Rewrite both suprema through the same attained maximizing value.
  calc
    ((sSup (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (x - (v : E))) : ℝ) : WithTop ℝ)
        = ((inner ℝ (B (v : E)) (x - (v : E)) : ℝ) : WithTop ℝ) := by
            exact congrArg (fun r : ℝ ↦ (r : WithTop ℝ)) hv.csSup_eq
    _ = sSup payoffSetTop := htop_eq.symm
    _ = pointwiseSupremumOn Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ))
          x := by
            rw [pointwiseSupremumOn_apply]

/-- Helper for Lemma 6.5: every feasible point lies in the effective domain of the Chapter 3
pointwise-supremum owner for the explicit gap kernel. -/
lemma mem_explicitPointwiseSupremumOnEffectiveDomain
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    {x : E} (hx : x ∈ Q) :
    x ∈ pointwiseSupremumOnEffectiveDomain Q Q
      (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)) := by
  -- On feasible points the explicit real-valued gap is finite, so the `WithTop` owner is finite
  -- there as well.
  refine (mem_pointwiseSupremumOnEffectiveDomain_iff_lt_top).2 ?_
  refine ⟨hx, ?_⟩
  rw [← explicitGapFunction_coe_eq_pointwiseSupremumOn Q B hψmax hx]
  exact WithTop.coe_lt_top _

/-- Helper for Lemma 6.5: the faithful owner
`pointwiseSupremumOnEffectiveDomain Q Q (fun x' u ↦ ⟪B u, x' - u⟫)` coincides with the feasible
set `Q` once the explicit payoff maximum is attained at every feasible base point. -/
lemma explicitPointwiseSupremumOnEffectiveDomain_eq
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E)))) :
    pointwiseSupremumOnEffectiveDomain Q Q
        (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)) =
      Q := by
  ext x
  constructor
  · intro hx
    -- The owner effective domain is defined by feasible membership plus finiteness.
    exact (mem_pointwiseSupremumOnEffectiveDomain_iff.mp hx).1
  · intro hx
    -- The explicit-gap finiteness bridge upgrades every feasible point back to the owner domain.
    exact mem_explicitPointwiseSupremumOnEffectiveDomain Q B hψmax hx

/-- Helper for Lemma 6.5: on feasible points, the finite real part of the Chapter 3 owner agrees
with the real explicit gap surface. -/
lemma withTopRealPart_explicitPointwiseSupremumOn_eq
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    {x : E} (hx : x ∈ Q) :
    withTopRealPart
        (pointwiseSupremumOn Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        x =
      sSup (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (x - (v : E))) := by
  let Φ : E → E → WithTop ℝ :=
    fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)
  have hxEff :
      x ∈ pointwiseSupremumOnEffectiveDomain Q Q Φ :=
    mem_explicitPointwiseSupremumOnEffectiveDomain Q B hψmax hx
  have hxDom :
      x ∈ dom (pointwiseSupremumOn Q Φ) := by
    -- Feasible points are exactly the finite-value points for this owner surface.
    exact (mem_pointwiseSupremumOnEffectiveDomain_iff.mp hxEff).2
  -- The faithful owner bridge now identifies the finite real part with the real explicit gap.
  apply WithTop.coe_injective
  rw [coe_withTopRealPart hxDom, ← explicitGapFunction_coe_eq_pointwiseSupremumOn Q B hψmax hx]

/-- Helper for Lemma 6.5: the faithful `WithTop ℝ` owner inherits the same convex feasible
surface as the real explicit gap once both are identified on `Q`. -/
lemma explicitPointwiseSupremumOn_convexOn
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E)))) :
    ConvexOn ℝ Q
      (withTopRealPart
        (pointwiseSupremumOn Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))) := by
  let f : E → ℝ :=
    fun w : E ↦
      sSup
        (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))
  have hfConv : ConvexOn ℝ Q f :=
    explicitGapFunction_convexOn Q hQconv B hψmax
  refine ⟨hQconv, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a • x + b • y ∈ Q := hfConv.1 hx hy ha hb hab
  -- Rewrite the owner finite real part at the two endpoints and the convex combination point.
  have hxEq :
      withTopRealPart
          (pointwiseSupremumOn Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          x =
        f x := by
    simpa [f] using withTopRealPart_explicitPointwiseSupremumOn_eq Q B hψmax hx
  have hyEq :
      withTopRealPart
          (pointwiseSupremumOn Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          y =
        f y := by
    simpa [f] using withTopRealPart_explicitPointwiseSupremumOn_eq Q B hψmax hy
  have hxyEq :
      withTopRealPart
          (pointwiseSupremumOn Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (a • x + b • y) =
        f (a • x + b • y) := by
    simpa [f] using withTopRealPart_explicitPointwiseSupremumOn_eq Q B hψmax hxy
  -- The remaining inequality is the already-proved convexity of the real explicit gap.
  rw [hxyEq, hxEq, hyEq]
  exact hfConv.2 hx hy ha hb hab

/-- Helper for Lemma 6.5: a constrained subgradient of the real explicit gap on `Q` transports to
the Chapter 3 `WithTop ℝ` pointwise-supremum owner on its effective domain. -/
lemma
    mem_constrainedSubdifferential_explicitPointwiseSupremumOn_of_mem_subdifferentialWithin
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    {wStar : Q} {g : E}
    (hg :
      g ∈ subdifferentialWithin Q
        ((fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ)
        (wStar : E)) :
    g ∈
      constrainedSubdifferential
        (pointwiseSupremumOnEffectiveDomain Q Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        (pointwiseSupremumOn Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        (wStar : E) := by
  let f : E → ℝ :=
    fun w : E ↦
      sSup
        (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))
  let Φ : E → E → WithTop ℝ :=
    fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)
  have hwStarEff :
      (wStar : E) ∈ pointwiseSupremumOnEffectiveDomain Q Q Φ :=
    mem_explicitPointwiseSupremumOnEffectiveDomain Q B hψmax wStar.property
  have hwStarDom :
      (wStar : E) ∈ dom (pointwiseSupremumOn Q Φ) :=
    (mem_pointwiseSupremumOnEffectiveDomain_iff.mp hwStarEff).2
  rcases (mem_subdifferentialWithin_iff.mp hg) with ⟨_, hg_minorant⟩
  rw [mem_constrainedSubdifferential_iff]
  refine ⟨hwStarEff, hwStarDom, ?_⟩
  intro y hyEff
  rcases (mem_pointwiseSupremumOnEffectiveDomain_iff.mp hyEff) with ⟨hyQ, hyDom⟩
  have hreal :
      f y ≥ f (wStar : E) + inner ℝ g (y - (wStar : E)) := hg_minorant hyQ
  -- Rewrite the owner values at `y` and `wStar` back to the real explicit gap on `Q`.
  rw [← explicitGapFunction_coe_eq_pointwiseSupremumOn Q B hψmax hyQ,
    ← explicitGapFunction_coe_eq_pointwiseSupremumOn Q B hψmax wStar.property]
  have hwithTop :
      (((f y : ℝ) : WithTop ℝ) ≥
        (((f (wStar : E) + inner ℝ g (y - (wStar : E))) : ℝ) : WithTop ℝ)) := by
    exact_mod_cast hreal
  simpa [WithTop.coe_add] using hwithTop

/-- Helper for Lemma 6.5: activity for the parameter subtype `Q` is the same as activity for the
ambient parameter set `Q ⊆ E` on the explicit kernel. -/
lemma ambientActive_of_subtypeActive
    [InnerProductSpace ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    {wStar v : Q}
    (hv :
      v ∈ activePointwiseSupremumOnIndices (Set.univ : Set Q)
        (fun x u ↦ (inner ℝ (B (u : E)) (x - (u : E)) : WithTop ℝ))
        (wStar : E)) :
    (v : E) ∈ activePointwiseSupremumOnIndices Q
      (fun x u ↦ (inner ℝ (B u) (x - u) : WithTop ℝ))
      (wStar : E) := by
  rcases (mem_activePointwiseSupremumOnIndices_iff.mp hv) with ⟨_, hv_eq⟩
  refine (mem_activePointwiseSupremumOnIndices_iff.mpr ?_)
  refine ⟨v.property, ?_⟩
  have himage :
      Set.range
          (fun y : Q ↦ (inner ℝ (B (y : E)) ((wStar : E) - (y : E)) : WithTop ℝ)) =
        (fun y : E ↦ (inner ℝ (B y) ((wStar : E) - y) : WithTop ℝ)) '' Q := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.property, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(⟨u, hu⟩ : Q), rfl⟩
  -- The subtype and ambient explicit kernels define the same `WithTop ℝ` supremum surface.
  change
    (inner ℝ (B (v : E)) ((wStar : E) - (v : E)) : WithTop ℝ) =
      pointwiseSupremumOn Q
        (fun x u ↦ (inner ℝ (B u) (x - u) : WithTop ℝ))
        (wStar : E)
  rw [pointwiseSupremumOn_apply] at hv_eq ⊢
  simpa [Set.image_univ, himage] using hv_eq

/-- Helper for Lemma 6.5: a simplex-weighted family of feasible comparison points whose explicit
slopes sum to zero yields a feasible barycenter that dominates the weighted explicit slices. -/
lemma explicitKernel_barycenter_domination_of_zeroRepresentation
    [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hBmono : ∀ h : E, 0 ≤ inner ℝ (B h) h)
    (weights : StdSimplex ℝ ι) (v : ι → Q)
    (hzero : (0 : E) = ∑ i, weights.weights i • B (v i : E)) :
    ∃ uBar ∈ Q,
      ∀ x ∈ Q,
        (∑ i, weights.weights i * inner ℝ (B (v i : E)) (x - (v i : E))) ≤
          inner ℝ (B uBar) (x - uBar) := by
  let uBar : E := Finset.univ.centerMass weights.weights (fun i ↦ (v i : E))
  have hweights_total : ∑ i, weights.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using weights.total
  have huBar_mem : uBar ∈ Q := by
    -- The barycenter stays feasible because the simplex weights form a convex combination.
    refine hQconv.centerMass_mem ?_ ?_ ?_
    · intro i hi
      exact weights.nonneg i
    · simpa [hweights_total] using (show (0 : ℝ) < 1 by norm_num)
    · intro i hi
      exact (v i).property
  have huBar_eq :
      uBar = ∑ i, weights.weights i • (v i : E) := by
    simpa [uBar] using
      (Finset.univ.centerMass_eq_of_sum_1 (w := weights.weights) (z := fun i ↦ (v i : E))
        hweights_total)
  have hsum_zero : ∑ i, weights.weights i • B (v i : E) = 0 := by
    simpa using hzero.symm
  have hBuBar_zero : B uBar = 0 := by
    -- The barycenter slope vanishes because `B` is linear and the weighted slopes sum to zero.
    calc
      B uBar = B (∑ i, weights.weights i • (v i : E)) := by rw [huBar_eq]
      _ = ∑ i, weights.weights i • B (v i : E) := by
            simp [map_sum]
      _ = 0 := hsum_zero
  refine ⟨uBar, huBar_mem, ?_⟩
  intro x hx
  have hdiag_nonneg :
      0 ≤ ∑ i, weights.weights i * inner ℝ (B (v i : E)) (v i : E) := by
    -- Each diagonal term is nonnegative by monotonicity of `B`.
    refine Finset.sum_nonneg ?_
    intro i hi
    exact mul_nonneg (weights.nonneg i) (hBmono (v i : E))
  have hsum_inner_x :
      ∑ i, weights.weights i * inner ℝ (B (v i : E)) x =
        inner ℝ (∑ i, weights.weights i • B (v i : E)) x := by
    calc
      ∑ i, weights.weights i * inner ℝ (B (v i : E)) x
          = ∑ i, inner ℝ (weights.weights i • B (v i : E)) x := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa [smul_eq_mul] using
                (inner_smul_left_eq_smul (x := B (v i : E)) (y := x) (r := weights.weights i)).symm
      _ = inner ℝ (∑ i, weights.weights i • B (v i : E)) x := by
            rw [sum_inner]
  have hweighted_rewrite :
      (∑ i, weights.weights i * inner ℝ (B (v i : E)) (x - (v i : E))) =
        inner ℝ (∑ i, weights.weights i • B (v i : E)) x -
          ∑ i, weights.weights i * inner ℝ (B (v i : E)) (v i : E) := by
    -- Expand the displacement `x - vᵢ` and collect the weighted `x` and diagonal terms.
    calc
      (∑ i, weights.weights i * inner ℝ (B (v i : E)) (x - (v i : E)))
          = ∑ i,
              (weights.weights i * inner ℝ (B (v i : E)) x -
                weights.weights i * inner ℝ (B (v i : E)) (v i : E)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [inner_sub_right, mul_sub]
      _ =
          (∑ i, weights.weights i * inner ℝ (B (v i : E)) x) -
            ∑ i, weights.weights i * inner ℝ (B (v i : E)) (v i : E) := by
              rw [Finset.sum_sub_distrib]
      _ = inner ℝ (∑ i, weights.weights i • B (v i : E)) x -
            ∑ i, weights.weights i * inner ℝ (B (v i : E)) (v i : E) := by
              rw [hsum_inner_x]
  have hweighted_nonpos :
      (∑ i, weights.weights i * inner ℝ (B (v i : E)) (x - (v i : E))) ≤ 0 := by
    rw [hweighted_rewrite, hsum_zero]
    simpa using neg_nonpos.mpr hdiag_nonneg
  -- The barycenter slice is identically zero because its slope vanishes.
  simpa [hBuBar_zero] using hweighted_nonpos

/-- Helper for Lemma 6.5: a subtype minimizer of the explicit gap packages the ambient
minimizer bridge, the faithful `WithTop ℝ` pointwise-supremum identification on `Q`, and the
resulting zero constrained subgradient at the minimizer. -/
lemma explicitGapZeroSubgradientData
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hmin : IsMinOn
      (fun w : Q ↦
        sSup
          (Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((w : E) - (v : E))))
      Set.univ
      wStar) :
    let f : E → ℝ :=
      fun w : E ↦
        sSup
          (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))
    IsMinOn f Q (wStar : E) ∧
      (∀ ⦃x : E⦄, x ∈ Q →
        (f x : WithTop ℝ) =
          pointwiseSupremumOn Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ))
            x) ∧
      (0 : E) ∈ subdifferentialWithin Q f (wStar : E) := by
  let f : E → ℝ :=
    fun w : E ↦
      sSup
        (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))
  refine ⟨?_, ?_, ?_⟩
  · -- Move the subtype minimizer back to the ambient feasible set `Q`.
    simpa [f] using isMinOn_explicitGapAmbient_of_subtype Q B wStar hmin
  · intro x hx
    -- The real explicit gap agrees with the Chapter 3 `WithTop ℝ` upper-envelope owner on `Q`.
    simpa [f] using explicitGapFunction_coe_eq_pointwiseSupremumOn Q B hψmax hx
  · -- The ambient minimizer certificate yields the zero constrained subgradient.
    have hminAmbient : IsMinOn f Q (wStar : E) := by
      simpa [f] using isMinOn_explicitGapAmbient_of_subtype Q B wStar hmin
    exact zero_mem_subdifferentialWithin_of_isMinOn wStar.property hminAmbient

/-- Helper for Lemma 6.5: a normal-cone point in the convex hull of active explicit slopes can be
packaged as a simplex-weighted active family. -/
lemma activeSlopeRepresentation_of_mem_convexHull_and_nonnegPairing
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E) (wStar : Q) {gBar : E}
    (hconv :
      gBar ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)})
    (hpair : ∀ x ∈ Q, 0 ≤ inner ℝ gBar (x - (wStar : E))) :
    ∃ (ι : Type) (_ : Fintype ι) (weights : StdSimplex ℝ ι) (v : ι → Q),
      (∀ i : ι,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
          (inner ℝ (B (v i : E)) ((wStar : E) - (v i : E)))) ∧
      (∀ x ∈ Q,
        0 ≤ inner ℝ (∑ i, weights.weights i • B (v i : E)) (x - (wStar : E))) := by
  classical
  rcases (mem_convexHull_iff_exists_fintype.mp hconv) with
    ⟨κ, _, w, z, hw₀, hw₁, hz, hzsum⟩
  have hz' :
      ∀ i : κ,
        ∃ v : Q,
          IsGreatest
            (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
            (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
          z i = B (v : E) := by
    intro i
    exact hz i
  choose v hvActive hzEq using hz'
  let weights : StdSimplex ℝ κ :=
    { weights := Finsupp.equivFunOnFinite.symm w
      nonneg := by
        intro i
        simpa using hw₀ i
      total := by
        simpa [Finsupp.equivFunOnFinite_symm_sum] using hw₁ }
  refine ⟨κ, inferInstance, weights, v, ?_, ?_⟩
  · exact hvActive
  intro x hx
  have hsumB : ∑ i, weights.weights i • B (v i : E) = gBar := by
    change ∑ i, w i • B (v i : E) = gBar
    calc
      ∑ i, w i • B (v i : E) = ∑ i, w i • z i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [(hzEq i).symm]
      _ = gBar := hzsum
  -- Rewrite the averaged slope back to the chosen normal-cone witness `gBar`.
  simpa [hsumB] using hpair x hx

/-- Helper for Lemma 6.5: the active explicit slope set at `wStar` is nonempty because the
displayed supremum is attained there. -/
lemma activeSlopeSet_nonempty
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q) :
    ({g | ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
          (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
        g = B (v : E)} : Set E).Nonempty := by
  -- The attainment hypothesis at `wStar` directly supplies one active slope.
  rcases hψmax wStar with ⟨v, hv⟩
  exact ⟨B (v : E), v, hv, rfl⟩

/-- Helper for Lemma 6.5: every real-valued constrained subdifferential is convex in the
subgradient variable. -/
lemma convex_subdifferentialWithin
    [InnerProductSpace ℝ E]
    {Q : Set E} {f : E → ℝ} {x : E} :
    Convex ℝ (subdifferentialWithin Q f x) := by
  rw [convex_iff_add_mem]
  intro g₁ hg₁ g₂ hg₂ a b ha hb hab
  rcases (mem_subdifferentialWithin_iff.mp hg₁) with ⟨hxQ, hg₁'⟩
  rcases (mem_subdifferentialWithin_iff.mp hg₂) with ⟨_, hg₂'⟩
  rw [mem_subdifferentialWithin_iff]
  refine ⟨hxQ, ?_⟩
  intro y hyQ
  have hg₁_real : f x + inner ℝ g₁ (y - x) ≤ f y := hg₁' hyQ
  have hg₂_real : f x + inner ℝ g₂ (y - x) ≤ f y := hg₂' hyQ
  have hcombo :
      a * (f x + inner ℝ g₁ (y - x)) +
        b * (f x + inner ℝ g₂ (y - x)) ≤
          f y := by
    have ha' := mul_le_mul_of_nonneg_left hg₁_real ha
    have hb' := mul_le_mul_of_nonneg_left hg₂_real hb
    calc
      a * (f x + inner ℝ g₁ (y - x)) +
          b * (f x + inner ℝ g₂ (y - x))
          ≤ a * f y + b * f y := add_le_add ha' hb'
      _ = f y := by
            rw [← add_mul, hab, one_mul]
  have htarget :
      f x + inner ℝ (a • g₁ + b • g₂) (y - x) ≤ f y := by
    have hsmul₁ :
        inner ℝ (a • g₁) (y - x) = a * inner ℝ g₁ (y - x) := by
      simpa using (inner_smul_left_eq_smul (x := g₁) (y := y - x) (r := a))
    have hsmul₂ :
        inner ℝ (b • g₂) (y - x) = b * inner ℝ g₂ (y - x) := by
      simpa using (inner_smul_left_eq_smul (x := g₂) (y := y - x) (r := b))
    calc
      f x + inner ℝ (a • g₁ + b • g₂) (y - x)
          = a * (f x + inner ℝ g₁ (y - x)) +
              b * (f x + inner ℝ g₂ (y - x)) := by
                rw [inner_add_left, hsmul₁, hsmul₂]
                calc
                  f x + (a * inner ℝ g₁ (y - x) + b * inner ℝ g₂ (y - x))
                      = (a * f x + b * f x) +
                          (a * inner ℝ g₁ (y - x) + b * inner ℝ g₂ (y - x)) := by
                            rw [← add_mul, hab, one_mul]
                  _ = a * (f x + inner ℝ g₁ (y - x)) +
                        b * (f x + inner ℝ g₂ (y - x)) := by
                          ring
      _ ≤ f y := hcombo
  exact htarget

/-- Helper for Lemma 6.5: every convex combination of active explicit slopes is already a
constrained subgradient of the explicit gap at `wStar`. -/
lemma convexHull_activeSlopes_subset_subdifferentialWithin
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q) :
    convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} ⊆
      subdifferentialWithin Q
        ((fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ)
        (wStar : E) := by
  -- Each active slope is already a relative subgradient, and the target subdifferential is
  -- convex, so `convexHull_min` upgrades the pointwise inclusion to the whole convex hull.
  refine convexHull_min ?_
    (convex_subdifferentialWithin
      (Q := Q)
      (f := (fun w : E ↦
        sSup (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))))
      (x := (wStar : E)))
  intro g hg
  rcases hg with ⟨v, hv, rfl⟩
  -- The singleton active-slice certificate is the source-faithful base case for the hull.
  simpa using activeExplicitGradient_mem_subdifferentialWithin Q B hψmax hv

/-- Helper for Lemma 6.5: every constrained subdifferential of a `WithTop ℝ`-valued owner is
convex in the slope variable. -/
lemma constrainedSubdifferential_convex
    [InnerProductSpace ℝ E]
    {Q : Set E} {f : E → WithTop ℝ} {x : E} :
    Convex ℝ (constrainedSubdifferential Q f x) := by
  rw [convex_iff_add_mem]
  intro g₁ hg₁ g₂ hg₂ a b ha hb hab
  rcases (mem_constrainedSubdifferential_iff.mp hg₁) with ⟨hxQ, hxdom, hg₁'⟩
  rcases (mem_constrainedSubdifferential_iff.mp hg₂) with ⟨_, _, hg₂'⟩
  rw [mem_constrainedSubdifferential_iff]
  refine ⟨hxQ, hxdom, ?_⟩
  intro y hyQ
  by_cases hyf : y ∈ dom f
  · have hg₁_withTop :
        (((withTopRealPart f x + inner ℝ g₁ (y - x) : ℝ) : WithTop ℝ) ≤ f y) := by
      rw [WithTop.coe_add, coe_withTopRealPart hxdom]
      exact hg₁' hyQ
    have hg₂_withTop :
        (((withTopRealPart f x + inner ℝ g₂ (y - x) : ℝ) : WithTop ℝ) ≤ f y) := by
      rw [WithTop.coe_add, coe_withTopRealPart hxdom]
      exact hg₂' hyQ
    have hg₁_real :
        withTopRealPart f x + inner ℝ g₁ (y - x) ≤ withTopRealPart f y :=
      (le_withTopRealPart_iff hyf).mpr hg₁_withTop
    have hg₂_real :
        withTopRealPart f x + inner ℝ g₂ (y - x) ≤ withTopRealPart f y :=
      (le_withTopRealPart_iff hyf).mpr hg₂_withTop
    have hcombo :
        a * (withTopRealPart f x + inner ℝ g₁ (y - x)) +
          b * (withTopRealPart f x + inner ℝ g₂ (y - x)) ≤
            withTopRealPart f y := by
      have ha' := mul_le_mul_of_nonneg_left hg₁_real ha
      have hb' := mul_le_mul_of_nonneg_left hg₂_real hb
      calc
        a * (withTopRealPart f x + inner ℝ g₁ (y - x)) +
            b * (withTopRealPart f x + inner ℝ g₂ (y - x))
            ≤ a * withTopRealPart f y + b * withTopRealPart f y := add_le_add ha' hb'
        _ = withTopRealPart f y := by
              rw [← add_mul, hab, one_mul]
    have htarget_real :
        withTopRealPart f x + inner ℝ (a • g₁ + b • g₂) (y - x) ≤
          withTopRealPart f y := by
      have hsmul₁ :
          inner ℝ (a • g₁) (y - x) = a * inner ℝ g₁ (y - x) := by
        simpa using (inner_smul_left_eq_smul (x := g₁) (y := y - x) (r := a))
      have hsmul₂ :
          inner ℝ (b • g₂) (y - x) = b * inner ℝ g₂ (y - x) := by
        simpa using (inner_smul_left_eq_smul (x := g₂) (y := y - x) (r := b))
      calc
        withTopRealPart f x + inner ℝ (a • g₁ + b • g₂) (y - x)
            = a * (withTopRealPart f x + inner ℝ g₁ (y - x)) +
                b * (withTopRealPart f x + inner ℝ g₂ (y - x)) := by
                  rw [inner_add_left, hsmul₁, hsmul₂]
                  calc
                    withTopRealPart f x +
                        (a * inner ℝ g₁ (y - x) + b * inner ℝ g₂ (y - x))
                        =
                          (a * withTopRealPart f x + b * withTopRealPart f x) +
                            (a * inner ℝ g₁ (y - x) + b * inner ℝ g₂ (y - x)) := by
                              rw [← add_mul, hab, one_mul]
                    _ = a * (withTopRealPart f x + inner ℝ g₁ (y - x)) +
                          b * (withTopRealPart f x + inner ℝ g₂ (y - x)) := by
                            ring
        _ ≤ withTopRealPart f y := hcombo
    have htarget_withTop :
        (((withTopRealPart f x + inner ℝ (a • g₁ + b • g₂) (y - x) : ℝ) : WithTop ℝ) ≤ f y) :=
      (le_withTopRealPart_iff hyf).mp htarget_real
    rw [ge_iff_le]
    rw [show f x = ((withTopRealPart f x : ℝ) : WithTop ℝ) by
      exact (coe_withTopRealPart hxdom).symm]
    simpa [WithTop.coe_add] using htarget_withTop
  · have htop : f y = ⊤ := by
      rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top] at hyf
      exact not_ne_iff.mp hyf
    simp [htop]

lemma activeExplicitGradient_mem_subdifferential_pointwiseSupremumOn
    [InnerProductSpace ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    {wStar v : Q}
    (hv :
      IsGreatest
        (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
        (inner ℝ (B (v : E)) ((wStar : E) - (v : E)))) :
    B (v : E) ∈
      subdifferential
        (pointwiseSupremumOn Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        (wStar : E) := by
  let Φ : E → E → WithTop ℝ := fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)
  let payoffSet : E → Set (WithTop ℝ) :=
    fun x ↦ (fun u : E ↦ (inner ℝ (B u) (x - u) : WithTop ℝ)) '' Q
  have hwStar_mem :
      ((inner ℝ (B (v : E)) ((wStar : E) - (v : E)) : ℝ) : WithTop ℝ) ∈
        payoffSet (wStar : E) := by
    exact ⟨(v : E), v.property, rfl⟩
  have hwStar_nonempty : (payoffSet (wStar : E)).Nonempty := ⟨_, hwStar_mem⟩
  have hwStar_eq :
      pointwiseSupremumOn Q Φ (wStar : E) =
        ((inner ℝ (B (v : E)) ((wStar : E) - (v : E)) : ℝ) : WithTop ℝ) := by
    rw [pointwiseSupremumOn_apply]
    apply le_antisymm
    · refine csSup_le hwStar_nonempty ?_
      rintro y ⟨u, hu, rfl⟩
      -- Activity at `wStar` identifies the owner value with the active slice value.
      change
        (((inner ℝ (B u) ((wStar : E) - u) : ℝ) : WithTop ℝ) ≤
          ((inner ℝ (B (v : E)) ((wStar : E) - (v : E)) : ℝ) : WithTop ℝ))
      exact_mod_cast hv.2 ⟨⟨u, hu⟩, rfl⟩
    · exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ hwStar_mem
  have hwStar_dom :
      (wStar : E) ∈ dom (pointwiseSupremumOn Q Φ) := by
    rw [mem_withTopEffectiveDomain_iff, hwStar_eq]
    exact WithTop.coe_lt_top _
  rw [mem_subdifferential_iff]
  refine ⟨hwStar_dom, ?_⟩
  intro y hy
  have hy_mem :
      ((inner ℝ (B (v : E)) (y - (v : E)) : ℝ) : WithTop ℝ) ∈ payoffSet y := by
    exact ⟨(v : E), v.property, rfl⟩
  have hy_slice_le :
      ((inner ℝ (B (v : E)) (y - (v : E)) : ℝ) : WithTop ℝ) ≤
        pointwiseSupremumOn Q Φ y := by
    rw [pointwiseSupremumOn_apply]
    exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ hy_mem
  have hsplit :
      inner ℝ (B (v : E)) (y - (v : E)) =
        inner ℝ (B (v : E)) ((wStar : E) - (v : E)) +
          inner ℝ (B (v : E)) (y - (wStar : E)) := by
    -- Split the affine slice through the base point `wStar`.
    have hdecomp :
        y - (v : E) = ((wStar : E) - (v : E)) + (y - (wStar : E)) := by
      abel
    rw [hdecomp, inner_add_right]
  have hsplit_top :
      ((inner ℝ (B (v : E)) (y - (v : E)) : ℝ) : WithTop ℝ) =
        ((inner ℝ (B (v : E)) ((wStar : E) - (v : E)) : ℝ) : WithTop ℝ) +
          ((inner ℝ (B (v : E)) (y - (wStar : E)) : ℝ) : WithTop ℝ) := by
    exact_mod_cast hsplit
  -- The active slice supports the whole owner because the supremum dominates that slice
  -- everywhere, while activity identifies the base-point value exactly.
  calc
    pointwiseSupremumOn Q Φ y
        ≥ ((inner ℝ (B (v : E)) (y - (v : E)) : ℝ) : WithTop ℝ) := hy_slice_le
    _ =
        ((inner ℝ (B (v : E)) ((wStar : E) - (v : E)) : ℝ) : WithTop ℝ) +
          ((inner ℝ (B (v : E)) (y - (wStar : E)) : ℝ) : WithTop ℝ) := by
            simpa [WithTop.coe_add] using hsplit_top
    _ =
        pointwiseSupremumOn Q Φ (wStar : E) +
          ((inner ℝ (B (v : E)) (y - (wStar : E)) : ℝ) : WithTop ℝ) := by
            rw [hwStar_eq]

/-- Helper for Lemma 6.5: every ambient owner subdifferential is convex in the subgradient
variable because its defining affine support inequalities are preserved by convex interpolation. -/
lemma convex_subdifferential
    [InnerProductSpace ℝ E]
    {f : E → WithTop ℝ} {x : E} :
    Convex ℝ (subdifferential f x) := by
  intro g₁ hg₁ g₂ hg₂ a b ha hb hab
  rcases (mem_subdifferential_iff.mp hg₁) with ⟨hx, h₁⟩
  rcases (mem_subdifferential_iff.mp hg₂) with ⟨_, h₂⟩
  rw [mem_subdifferential_iff]
  refine ⟨hx, ?_⟩
  intro y hy
  have h₁_real :
      withTopRealPart f y ≥ withTopRealPart f x + inner ℝ g₁ (y - x) := by
    have h₁' := h₁ hy
    rw [← coe_withTopRealPart hy, ← coe_withTopRealPart hx] at h₁'
    exact_mod_cast h₁'
  have h₂_real :
      withTopRealPart f y ≥ withTopRealPart f x + inner ℝ g₂ (y - x) := by
    have h₂' := h₂ hy
    rw [← coe_withTopRealPart hy, ← coe_withTopRealPart hx] at h₂'
    exact_mod_cast h₂'
  have hcombo :
      a * (withTopRealPart f x + inner ℝ g₁ (y - x)) +
        b * (withTopRealPart f x + inner ℝ g₂ (y - x)) ≤
          withTopRealPart f y := by
    have ha' := mul_le_mul_of_nonneg_left h₁_real ha
    have hb' := mul_le_mul_of_nonneg_left h₂_real hb
    calc
      a * (withTopRealPart f x + inner ℝ g₁ (y - x)) +
          b * (withTopRealPart f x + inner ℝ g₂ (y - x))
          ≤ a * withTopRealPart f y + b * withTopRealPart f y := add_le_add ha' hb'
      _ = withTopRealPart f y := by
            rw [← add_mul, hab, one_mul]
  have htarget_real :
      withTopRealPart f y ≥
        withTopRealPart f x + inner ℝ (a • g₁ + b • g₂) (y - x) := by
    have hsmul₁ :
        inner ℝ (a • g₁) (y - x) = a * inner ℝ g₁ (y - x) := by
      simpa using (inner_smul_left_eq_smul (x := g₁) (y := y - x) (r := a))
    have hsmul₂ :
        inner ℝ (b • g₂) (y - x) = b * inner ℝ g₂ (y - x) := by
      simpa using (inner_smul_left_eq_smul (x := g₂) (y := y - x) (r := b))
    calc
      withTopRealPart f y ≥
          a * (withTopRealPart f x + inner ℝ g₁ (y - x)) +
            b * (withTopRealPart f x + inner ℝ g₂ (y - x)) := hcombo
      _ = withTopRealPart f x + inner ℝ (a • g₁ + b • g₂) (y - x) := by
            calc
              a * (withTopRealPart f x + inner ℝ g₁ (y - x)) +
                  b * (withTopRealPart f x + inner ℝ g₂ (y - x))
                  =
                    (a + b) * withTopRealPart f x +
                      (a * inner ℝ g₁ (y - x) + b * inner ℝ g₂ (y - x)) := by
                        ring
              _ = withTopRealPart f x +
                    (a * inner ℝ g₁ (y - x) + b * inner ℝ g₂ (y - x)) := by
                      rw [hab]
                      ring
              _ = withTopRealPart f x + inner ℝ (a • g₁ + b • g₂) (y - x) := by
                    rw [inner_add_left, hsmul₁, hsmul₂]
  -- Convert the convex-combination support inequality back to the owner-valued statement.
  rw [← coe_withTopRealPart hy, ← coe_withTopRealPart hx]
  exact_mod_cast htarget_real

/-- Helper for Lemma 6.5: every explicit affine slice `x ↦ ⟪B v, x - v⟫` has ambient
subdifferential equal to the singleton slope `{B v}`. -/
lemma subdifferential_explicitAffineSlice_eq_singleton
    [InnerProductSpace ℝ E]
    (B : E →ₗ[ℝ] E) (v x : E) :
    ∂ (fun y : E ↦ (inner ℝ (B v) (y - v) : WithTop ℝ))(x) = {B v} := by
  ext g
  rw [Set.mem_singleton_iff, mem_subdifferential_coe_real_iff]
  constructor
  · intro hg
    -- Test the subgradient inequality in the affine-slice direction `g - B v`.
    have hz := hg (x + (g - B v))
    have hineq : inner ℝ g (g - B v) ≤ inner ℝ (B v) (g - B v) := by
      have hrewrite :
          inner ℝ (B v) ((x + (g - B v)) - v) =
            inner ℝ (B v) (x - v) + inner ℝ (B v) (g - B v) := by
        have hdecomp : (x + (g - B v)) - v = (x - v) + (g - B v) := by
          abel_nf
        rw [hdecomp, inner_add_right]
      have hsub : x + (g - B v) - x = g - B v := by
        abel_nf
      rw [hrewrite, hsub] at hz
      linarith
    have hnonpos : ‖g - B v‖ ^ (2 : ℕ) ≤ 0 := by
      have hpair : inner ℝ (g - B v) (g - B v) ≤ 0 := by
        calc
          inner ℝ (g - B v) (g - B v) = inner ℝ g (g - B v) - inner ℝ (B v) (g - B v) := by
            rw [inner_sub_left]
          _ ≤ 0 := sub_nonpos.mpr hineq
      simpa [real_inner_self_eq_norm_sq] using hpair
    have hzeroNorm : ‖g - B v‖ = 0 := by
      nlinarith [sq_nonneg ‖g - B v‖, hnonpos]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzeroNorm)
  · intro hg
    subst hg
    -- The displayed slope supports its own affine slice with equality at every point.
    intro y
    have hy : y = x + (y - x) := by
      abel_nf
    have hrewrite :
        inner ℝ (B v) ((x + (y - x)) - v) =
          inner ℝ (B v) (x - v) + inner ℝ (B v) (y - x) := by
      have hdecomp : (x + (y - x)) - v = (x - v) + (y - x) := by
        abel_nf
      rw [hdecomp, inner_add_right]
    have hsub : x + (y - x) - x = y - x := by
      abel_nf
    rw [hy, hrewrite, hsub]

/-- Helper for Lemma 6.5: the abstract active-slice generator used by Chapter 3 reduces to the
explicit active-slope set `{B v | v is active at wStar}`. -/
lemma activeExplicitSliceSubgradientSet_eq_activeSlopeSet
    [InnerProductSpace ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E) (wStar : Q) :
    {g | ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
          (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
        g ∈
          subdifferential
            (fun y : E ↦ (inner ℝ (B (v : E)) (y - (v : E)) : WithTop ℝ))
            (wStar : E)} =
      {g | ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
          (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
        g = B (v : E)} := by
  ext g
  constructor
  · rintro ⟨v, hv, hg⟩
    rw [subdifferential_explicitAffineSlice_eq_singleton B (v : E) (wStar : E)] at hg
    exact ⟨v, hv, Set.mem_singleton_iff.mp hg⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v, hv, ?_⟩
    rw [subdifferential_explicitAffineSlice_eq_singleton B (v : E) (wStar : E)]
    simp

/-- Helper for Lemma 6.5: every convex combination of active explicit slopes is already an
ambient subgradient of the Chapter 3 pointwise-supremum owner at `wStar`. -/
lemma convexHull_activeSlopes_subset_subdifferential_pointwiseSupremumOn
    [InnerProductSpace ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (wStar : Q) :
    convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} ⊆
      subdifferential
        (pointwiseSupremumOn Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        (wStar : E) := by
  -- Route correction: the active ambient membership lemma is now restored, so convexity of the
  -- owner subdifferential upgrades the pointwise inclusion to the full active hull.
  refine convexHull_min ?_
    (convex_subdifferential
      (f := pointwiseSupremumOn Q
        (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
      (x := (wStar : E)))
  intro g hg
  rcases hg with ⟨v, hv, rfl⟩
  -- A single active slope is already an ambient owner subgradient at `wStar`.
  simpa using activeExplicitGradient_mem_subdifferential_pointwiseSupremumOn Q B hv

/-- Helper for Lemma 6.5: each single active explicit slope already belongs to the owner-level
constrained subdifferential of the Chapter 3 pointwise-supremum surface. -/
lemma activeExplicitGradient_mem_constrainedSubdifferential_explicitPointwiseSupremumOn
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    {wStar v : Q}
    (hv :
      IsGreatest
        (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
        (inner ℝ (B (v : E)) ((wStar : E) - (v : E)))) :
    B (v : E) ∈
      constrainedSubdifferential
        (pointwiseSupremumOnEffectiveDomain Q Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        (pointwiseSupremumOn Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        (wStar : E) := by
  let f : E → ℝ :=
    fun w : E ↦
      sSup
        (Set.range fun u : Q ↦ inner ℝ (B (u : E)) (w - (u : E)))
  -- First record the active slope as a real-valued constrained subgradient of the explicit gap.
  have hvSub :
      B (v : E) ∈ subdifferentialWithin Q f (wStar : E) := by
    simpa [f] using activeExplicitGradient_mem_subdifferentialWithin Q B hψmax hv
  -- Then transport that real-valued subgradient to the faithful Chapter 3 owner.
  simpa [f] using
    mem_constrainedSubdifferential_explicitPointwiseSupremumOn_of_mem_subdifferentialWithin
      Q B hψmax (wStar := wStar) (g := B (v : E)) hvSub

/-- Helper for Lemma 6.5: after transporting the real explicit gap to the Chapter 3
`pointwiseSupremumOn` owner, every convex combination of active explicit slopes is still an
owner-level constrained subgradient at `wStar`. -/
lemma convexHull_activeSlopes_subset_constrainedSubdifferential_explicitPointwiseSupremumOn
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q) :
    convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} ⊆
      constrainedSubdifferential
        (pointwiseSupremumOnEffectiveDomain Q Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        (pointwiseSupremumOn Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        (wStar : E) := by
  -- Route correction: this wrapper stays entirely on the constrained owner surface. Each active
  -- slope already lies in the owner-level constrained subdifferential, and that target is convex.
  refine convexHull_min ?_
    (constrainedSubdifferential_convex
      (Q := pointwiseSupremumOnEffectiveDomain Q Q
        (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
      (f := pointwiseSupremumOn Q
        (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
      (x := (wStar : E)))
  intro g hg
  rcases hg with ⟨v, hv, rfl⟩
  -- The base active slope transport was proved above, so the hull follows by convexity.
  simpa using
    activeExplicitGradient_mem_constrainedSubdifferential_explicitPointwiseSupremumOn
      Q B hψmax hv

/-- Helper for Lemma 6.5: a minimizer of the explicit gap gives the zero owner-level constrained
subgradient for the corresponding Chapter 3 pointwise-supremum surface. -/
lemma zero_mem_constrainedSubdifferential_explicitPointwiseSupremumOn_of_isMinOn
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hmin : IsMinOn
      (fun w : Q ↦
        sSup
          (Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((w : E) - (v : E))))
      Set.univ
      wStar) :
    (0 : E) ∈
      constrainedSubdifferential
        (pointwiseSupremumOnEffectiveDomain Q Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        (pointwiseSupremumOn Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        (wStar : E) := by
  have hzeroSub :
      (0 : E) ∈ subdifferentialWithin Q
        ((fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ)
        (wStar : E) := by
    -- The explicit minimizer already supplies the zero real-valued constrained subgradient.
    exact (explicitGapZeroSubgradientData Q B hψmax wStar hmin).2.2
  -- Move the zero subgradient to the faithful Chapter 3 owner.
  simpa using
    mem_constrainedSubdifferential_explicitPointwiseSupremumOn_of_mem_subdifferentialWithin
      Q B hψmax (wStar := wStar) (g := (0 : E)) hzeroSub

/-- Helper for Lemma 6.5: if a convex combination of active slopes is corrected by a normal-cone
remainder, then the resulting difference is still an owner-level constrained subgradient of the
explicit pointwise-supremum surface at `wStar`. -/
lemma activeHullSubNormalCone_mem_constrainedSubdifferential_explicitPointwiseSupremumOn
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q) {gBar n : E}
    (hgBarHull :
      gBar ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)})
    (hn : n ∈ N[Q] (wStar : E)) :
    gBar - n ∈
      constrainedSubdifferential
        (pointwiseSupremumOnEffectiveDomain Q Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        (pointwiseSupremumOn Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        (wStar : E) := by
  have hgBarOwner :
      gBar ∈
        constrainedSubdifferential
          (pointwiseSupremumOnEffectiveDomain Q Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (pointwiseSupremumOn Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (wStar : E) :=
    convexHull_activeSlopes_subset_constrainedSubdifferential_explicitPointwiseSupremumOn
      Q B hψmax wStar hgBarHull
  rcases (mem_constrainedSubdifferential_iff.mp hgBarOwner) with
    ⟨hwStarEff, hwStarDom, hgBarMinorant⟩
  rw [mem_constrainedSubdifferential_iff]
  refine ⟨hwStarEff, hwStarDom, ?_⟩
  intro y hyEff
  rcases (mem_pointwiseSupremumOnEffectiveDomain_iff.mp hyEff) with ⟨hyQ, _⟩
  have hn_pair : 0 ≤ inner ℝ n (y - (wStar : E)) :=
    mem_normalCone_iff.mp hn y hyQ
  have hshift_real :
      inner ℝ (gBar - n) (y - (wStar : E)) ≤ inner ℝ gBar (y - (wStar : E)) := by
    -- The normal-cone correction can only decrease the affine lower support on feasible points.
    rw [inner_sub_left]
    linarith
  have hshift :
      pointwiseSupremumOn Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ))
          (wStar : E) +
        ((inner ℝ (gBar - n) (y - (wStar : E)) : ℝ) : WithTop ℝ) ≤
      pointwiseSupremumOn Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ))
          (wStar : E) +
        ((inner ℝ gBar (y - (wStar : E)) : ℝ) : WithTop ℝ) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right (by exact_mod_cast hshift_real)
        (pointwiseSupremumOn Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ))
          (wStar : E))
  -- Combine the owner-level active-hull support inequality with the normal-cone decrease.
  exact le_trans hshift (hgBarMinorant hyEff)

/-- Helper for Lemma 6.5: a zero owner-level constrained subgradient already implies that
`wStar` minimizes the real explicit gap on `Q`. -/
lemma isMinOn_explicitGapAmbient_of_zero_mem_constrainedSubdifferential_explicitPointwiseSupremumOn
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hzeroOwner :
      (0 : E) ∈
        constrainedSubdifferential
          (pointwiseSupremumOnEffectiveDomain Q Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (pointwiseSupremumOn Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (wStar : E)) :
    IsMinOn
      (fun w : E ↦
        sSup
          (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E))))
      Q
      (wStar : E) := by
  let f : E → ℝ :=
    fun w : E ↦
      sSup
        (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))
  rcases (mem_constrainedSubdifferential_iff.mp hzeroOwner) with ⟨_, _, hminorant⟩
  refine isMinOn_iff.mpr ?_
  intro y hyQ
  have hyEff :
      y ∈ pointwiseSupremumOnEffectiveDomain Q Q
        (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)) :=
    mem_explicitPointwiseSupremumOnEffectiveDomain Q B hψmax hyQ
  have howner := hminorant hyEff
  -- Rewrite the owner-level inequality back to the real explicit gap on feasible points.
  rw [← explicitGapFunction_coe_eq_pointwiseSupremumOn Q B hψmax hyQ,
    ← explicitGapFunction_coe_eq_pointwiseSupremumOn Q B hψmax wStar.property] at howner
  simpa [f] using howner

/-- Helper for Lemma 6.5: the same zero owner-level constrained subgradient yields the zero
relative subgradient of the real explicit gap at `wStar`. -/
lemma zero_mem_subdifferentialWithin_of_zero_mem_constrainedSubdifferential_explicitPointwiseSupremumOn
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hzeroOwner :
      (0 : E) ∈
        constrainedSubdifferential
          (pointwiseSupremumOnEffectiveDomain Q Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (pointwiseSupremumOn Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (wStar : E)) :
    (0 : E) ∈
      subdifferentialWithin Q
        ((fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ)
        (wStar : E) := by
  let f : E → ℝ :=
    fun w : E ↦
      sSup
        (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))
  have hmin :
      IsMinOn f Q (wStar : E) :=
    isMinOn_explicitGapAmbient_of_zero_mem_constrainedSubdifferential_explicitPointwiseSupremumOn
      Q B hψmax wStar hzeroOwner
  -- Once the owner certificate is read back as a real-valued minimizer, the zero relative
  -- subgradient is immediate.
  simpa [f] using zero_mem_subdifferentialWithin_of_isMinOn wStar.property hmin

/-- Helper for Lemma 6.5: a zero relative subgradient of the explicit gap already places `wStar`
in the canonical constrained argmin owner for that same real surface. -/
lemma mem_constrainedArgmin_explicitGap_of_zero_mem_subdifferentialWithin
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (wStar : Q)
    (hzeroSub :
      (0 : E) ∈ subdifferentialWithin Q
        ((fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ)
        (wStar : E)) :
    (wStar : E) ∈ argmin[Q]
      ((fun w : E ↦
        sSup
          (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ) := by
  -- Read the zero relative subgradient back through the canonical minimizer owner.
  refine mem_constrainedArgmin_iff.mpr ?_
  refine ⟨wStar.property, ?_⟩
  -- The ambient minimizer statement is exactly the owner data required by `argmin[Q]`.
  simpa using isMinOn_of_zero_mem_subdifferentialWithin hzeroSub

/-- Helper for Lemma 6.5: lifting a real-valued convex function on all of `E` to `WithTop ℝ`
preserves convexity on the effective-domain owner. -/
lemma convexOn_withTopLift_of_convexOnUniv
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ (dom (fun z : E ↦ (f z : WithTop ℝ)))
      (withTopRealPart (fun z : E ↦ (f z : WithTop ℝ))) := by
  -- The lifted objective is finite everywhere, so its `withTopRealPart` is just `f`.
  simpa [withTopEffectiveDomain, withTopRealPart] using hf

/-- Helper for Lemma 6.5: the `WithTop` lift of a real-valued objective has full interior domain,
so every feasible point is an interior-domain point for the owner API. -/
lemma subset_interior_dom_withTopLift
    {Q : Set E} {f : E → ℝ} :
    Q ⊆ interior (dom (fun z : E ↦ (f z : WithTop ℝ))) := by
  -- The coercion of a real-valued objective to `WithTop ℝ` is finite at every point.
  intro x hx
  simp [withTopEffectiveDomain]

/-- Helper for Lemma 6.5: a real-valued relative subgradient is definitionally a constrained
subgradient of the canonical `WithTop` lift. -/
lemma mem_constrainedSubdifferential_withTopLift_of_mem_subdifferentialWithin
    [InnerProductSpace ℝ E]
    {Q : Set E} {f : E → ℝ} {x g : E}
    (hg : g ∈ subdifferentialWithin Q f x) :
    g ∈ ∂[Q] (fun z : E ↦ (f z : WithTop ℝ))(x) := by
  -- This is exactly the bridge definition of `subdifferentialWithin`.
  simpa [subdifferentialWithin] using hg

/-- Helper for Lemma 6.5: restricting a globally convex real-valued function to `Q` and then
lifting it to `WithTop ℝ` preserves the convex owner inequality on `Q`. -/
lemma convexOn_withTopLift_on_set_of_convexOnUniv
    {Q : Set E} (hQconv : Convex ℝ Q) {f : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Q (withTopRealPart (fun z : E ↦ (f z : WithTop ℝ))) := by
  refine ⟨hQconv, ?_⟩
  intro x hx y hy a b ha hb hab
  -- The whole-space convexity inequality specializes directly to the feasible set `Q`.
  simpa [withTopRealPart] using hf.2 (by simp) (by simp) ha hb hab

/-- Helper for Lemma 6.5: if the real explicit gap is globally convex on `E`, then a zero
relative subgradient at `wStar` produces an ambient subgradient lying in the normal cone of
`Q` at `wStar`. -/
lemma exists_subgradient_mem_normalCone_of_zero_mem_subdifferentialWithin_explicitGapGlobalConvex
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E) (wStar : Q)
    (hfConvUniv :
      ConvexOn ℝ Set.univ
        ((fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ))
    (hzeroSub :
      (0 : E) ∈ subdifferentialWithin Q
        ((fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ)
        (wStar : E)) :
    ∃ gStar : E,
      gStar ∈
        subdifferential
          (fun w : E ↦
            (((sSup
              (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : ℝ) :
              WithTop ℝ))
          (wStar : E) ∧
        gStar ∈ N[Q] (wStar : E) := by
  let f : E → ℝ :=
    fun w : E ↦
      sSup
        (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))
  let fTop : E → WithTop ℝ := fun z : E ↦ (f z : WithTop ℝ)
  have hfTopConv :
      ConvexOn ℝ (dom fTop) (withTopRealPart fTop) :=
    convexOn_withTopLift_of_convexOnUniv hfConvUniv
  have hfTopConvQ :
      ConvexOn ℝ Q (withTopRealPart fTop) :=
    convexOn_withTopLift_on_set_of_convexOnUniv hQconv hfConvUniv
  have hQ_subset_interior : Q ⊆ interior (dom fTop) :=
    subset_interior_dom_withTopLift
  have hzeroTop :
      (0 : E) ∈ constrainedSubdifferential Q fTop (wStar : E) :=
    mem_constrainedSubdifferential_withTopLift_of_mem_subdifferentialWithin hzeroSub
  -- Repackage the real-valued zero relative subgradient as an owner-level constrained
  -- subgradient, then extract the ambient subgradient/normal-cone pair from Chapter 3.
  rcases existsSubgradientWithNormalConeRemainderOfMemConstrainedSubdifferential
      hfTopConv hfTopConvQ hQ_subset_interior wStar.property hzeroTop with
    ⟨gStar, hgStarSub, hgStarNormal⟩
  refine ⟨gStar, ?_, ?_⟩
  · simpa [f, fTop] using hgStarSub
  · simpa using hgStarNormal

/-- Helper for Lemma 6.5: once a globally convex explicit-gap subgradient is known to land in the
active explicit hull, the zero relative subgradient already yields the required hull/normal-cone
witness. -/
lemma exists_activeHullNormalWitness_of_zero_mem_subdifferentialWithin_explicitGapGlobalConvex
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E) (wStar : Q)
    (hfConvUniv :
      ConvexOn ℝ Set.univ
        ((fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ))
    (hsub :
      subdifferential
          (fun w : E ↦
            (((sSup
              (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : ℝ) :
              WithTop ℝ))
          (wStar : E) ⊆
        convexHull ℝ
          {g | ∃ v : Q,
              IsGreatest
                (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
                (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
              g = B (v : E)})
    (hzeroSub :
      (0 : E) ∈ subdifferentialWithin Q
        ((fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ)
        (wStar : E)) :
    ∃ gBar : E,
      gBar ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} ∧
        gBar ∈ N[Q] (wStar : E) := by
  rcases
      exists_subgradient_mem_normalCone_of_zero_mem_subdifferentialWithin_explicitGapGlobalConvex
        Q hQconv B wStar hfConvUniv hzeroSub with
    ⟨gStar, hgStarSub, hgStarNormal⟩
  -- Push the ambient subgradient into the active explicit hull through the assumed reverse
  -- inclusion, then keep the same normal-cone certificate.
  exact ⟨gStar, hsub hgStarSub, hgStarNormal⟩

/-- Helper for Lemma 6.5: once an owner-level ambient subgradient at `wStar` is known to lie in
the active explicit hull, any simultaneous normal-cone certificate already gives the required
active-hull/normal-cone witness. -/
lemma exists_activeHullNormalWitness_of_exists_ownerSubgradientNormalWitness
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (Q : Set E) (B : E →ₗ[ℝ] E) (wStar : Q)
    (howner :
      ∃ gBar : E,
        gBar ∈
          subdifferential
            (pointwiseSupremumOn Q
              (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
            (wStar : E) ∧
          gBar ∈ N[Q] (wStar : E))
    (hsub :
      subdifferential
          (pointwiseSupremumOn Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (wStar : E) ⊆
        convexHull ℝ
          {g | ∃ v : Q,
              IsGreatest
                (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
                (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
              g = B (v : E)}) :
    ∃ gBar : E,
      gBar ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} ∧
        gBar ∈ N[Q] (wStar : E) := by
  rcases howner with ⟨gBar, hgBarSub, hgBarNormal⟩
  -- Push the owner-level subgradient witness through the reverse active-hull inclusion.
  exact ⟨gBar, hsub hgBarSub, hgBarNormal⟩

/-- Helper for Lemma 6.5: an ambient minimizer of the explicit gap on `Q` restricts to the
canonical minimizer statement on the feasible subtype. -/
lemma isMinOn_explicitGapSubtype_of_isMinOnAmbient
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E) (wStar : Q)
    (hminAmbient :
      IsMinOn
        (fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E))))
        Q
        (wStar : E)) :
    IsMinOn
      (fun w : Q ↦
        sSup
          (Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((w : E) - (v : E))))
      Set.univ
      wStar := by
  refine isMinOn_iff.mpr ?_
  intro y hy
  -- Restrict the ambient feasible minimizer inequality to feasible subtype points.
  exact hminAmbient y.property

/-- Helper for Lemma 6.5: an ambient minimizer of the explicit gap on `Q` already yields the
zero constrained subgradient for the faithful Chapter 3 owner surface. -/
lemma zero_mem_constrainedSubdifferential_explicitPointwiseSupremumOn_of_isMinOnAmbient
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hminAmbient :
      IsMinOn
        (fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E))))
        Q
        (wStar : E)) :
    (0 : E) ∈
      constrainedSubdifferential
        (pointwiseSupremumOnEffectiveDomain Q Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        (pointwiseSupremumOn Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        (wStar : E) := by
  have hminSubtype :
      IsMinOn
        (fun w : Q ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((w : E) - (v : E))))
        Set.univ
        wStar :=
    isMinOn_explicitGapSubtype_of_isMinOnAmbient Q B wStar hminAmbient
  -- Reuse the existing subtype-to-owner transport once the minimizer lives on `Q`.
  exact
    zero_mem_constrainedSubdifferential_explicitPointwiseSupremumOn_of_isMinOn
      Q B hψmax wStar hminSubtype

/-- Helper for Lemma 6.5: for a single affine explicit-gap slice, the owner-level constrained
subgradient condition is equivalent to the slice gradient minus the candidate slope lying in the
normal cone of `Q` at `wStar`. -/
lemma mem_constrainedSubdifferential_explicitAffineSlice_iff_gradient_remainder_mem_normalCone
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    {wStar v : Q} {g : E} :
    g ∈
      constrainedSubdifferential
        (pointwiseSupremumOnEffectiveDomain Q Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        (fun x' ↦ (inner ℝ (B (v : E)) (x' - (v : E)) : WithTop ℝ))
        (wStar : E) ↔
      B (v : E) - g ∈ N[Q] (wStar : E) := by
  constructor
  · intro hg
    rcases (mem_constrainedSubdifferential_iff.mp hg) with ⟨_, _, hminorant⟩
    rw [mem_normalCone_iff]
    intro y hyQ
    have hyEff :
        y ∈ pointwiseSupremumOnEffectiveDomain Q Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)) :=
      mem_explicitPointwiseSupremumOnEffectiveDomain Q B hψmax hyQ
    have hminorantWithTop := hminorant hyEff
    -- Rewrite the owner inequality for the affine slice as a real-valued slope comparison.
    have hminorantReal :
        inner ℝ (B (v : E)) ((wStar : E) - (v : E)) +
            inner ℝ g (y - (wStar : E)) ≤
          inner ℝ (B (v : E)) (y - (v : E)) := by
      exact_mod_cast hminorantWithTop
    have hsplit :
        inner ℝ (B (v : E)) (y - (v : E)) =
          inner ℝ (B (v : E)) (y - (wStar : E)) +
            inner ℝ (B (v : E)) ((wStar : E) - (v : E)) := by
      have hdecomp :
          y - (v : E) = (y - (wStar : E)) + ((wStar : E) - (v : E)) := by
        abel
      calc
        inner ℝ (B (v : E)) (y - (v : E))
            = inner ℝ (B (v : E)) ((y - (wStar : E)) + ((wStar : E) - (v : E))) := by
                rw [hdecomp]
        _ = inner ℝ (B (v : E)) (y - (wStar : E)) +
              inner ℝ (B (v : E)) ((wStar : E) - (v : E)) := by
                rw [inner_add_right]
    have hgrad :
        inner ℝ g (y - (wStar : E)) ≤
          inner ℝ (B (v : E)) (y - (wStar : E)) := by
      linarith [hminorantReal, hsplit]
    -- The affine-slice subgradient inequality is exactly the normal-cone pairing for the
    -- remainder `B v - g`.
    rw [inner_sub_left]
    linarith
  · intro hnormal
    rw [mem_constrainedSubdifferential_iff]
    have hwStarEff :
        (wStar : E) ∈ pointwiseSupremumOnEffectiveDomain Q Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)) :=
      mem_explicitPointwiseSupremumOnEffectiveDomain Q B hψmax wStar.property
    refine ⟨hwStarEff, by simp, ?_⟩
    intro y hyEff
    rcases (mem_pointwiseSupremumOnEffectiveDomain_iff.mp hyEff) with ⟨hyQ, _⟩
    have hnormalPair :
        0 ≤ inner ℝ (B (v : E) - g) (y - (wStar : E)) :=
      mem_normalCone_iff.mp hnormal y hyQ
    -- Convert the normal-cone pairing back into the affine lower-support inequality.
    have hgrad :
        inner ℝ g (y - (wStar : E)) ≤
          inner ℝ (B (v : E)) (y - (wStar : E)) := by
      rw [inner_sub_left] at hnormalPair
      linarith
    have hsplit :
        inner ℝ (B (v : E)) (y - (v : E)) =
          inner ℝ (B (v : E)) (y - (wStar : E)) +
            inner ℝ (B (v : E)) ((wStar : E) - (v : E)) := by
      have hdecomp :
          y - (v : E) = (y - (wStar : E)) + ((wStar : E) - (v : E)) := by
        abel
      calc
        inner ℝ (B (v : E)) (y - (v : E))
            = inner ℝ (B (v : E)) ((y - (wStar : E)) + ((wStar : E) - (v : E))) := by
                rw [hdecomp]
        _ = inner ℝ (B (v : E)) (y - (wStar : E)) +
              inner ℝ (B (v : E)) ((wStar : E) - (v : E)) := by
                rw [inner_add_right]
    have htargetReal :
        inner ℝ (B (v : E)) ((wStar : E) - (v : E)) +
            inner ℝ g (y - (wStar : E)) ≤
          inner ℝ (B (v : E)) (y - (v : E)) := by
      linarith [hgrad, hsplit]
    have htargetWithTop :
        (((inner ℝ (B (v : E)) ((wStar : E) - (v : E)) +
            inner ℝ g (y - (wStar : E)) : ℝ) : WithTop ℝ) ≤
          ((inner ℝ (B (v : E)) (y - (v : E)) : ℝ) : WithTop ℝ)) := by
      exact_mod_cast htargetReal
    simpa [WithTop.coe_add] using htargetWithTop

/-- Helper for Lemma 6.5: membership in the constrained subdifferential of a single affine
explicit-gap slice can be written as the slice gradient minus a normal-cone vector. -/
lemma mem_constrainedSubdifferential_explicitAffineSlice_iff_exists_normalCone_remainder
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    {wStar v : Q} {g : E} :
    g ∈
      constrainedSubdifferential
        (pointwiseSupremumOnEffectiveDomain Q Q
          (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
        (fun x' ↦ (inner ℝ (B (v : E)) (x' - (v : E)) : WithTop ℝ))
        (wStar : E) ↔
      ∃ n ∈ N[Q] (wStar : E), g = B (v : E) - n := by
  constructor
  · intro hg
    refine ⟨B (v : E) - g, ?_, ?_⟩
    · exact
        (mem_constrainedSubdifferential_explicitAffineSlice_iff_gradient_remainder_mem_normalCone
          Q B hψmax).mp hg
    · abel
  · rintro ⟨n, hn, rfl⟩
    -- Repackage the same affine-slice certificate using the explicit normal-cone remainder.
    have hnormal :
        B (v : E) - (B (v : E) - n) ∈ N[Q] (wStar : E) := by
      simpa using hn
    exact
      (mem_constrainedSubdifferential_explicitAffineSlice_iff_gradient_remainder_mem_normalCone
        Q B hψmax).mpr hnormal

/-- Helper for Lemma 6.5: a zero owner-level constrained subgradient of the explicit
pointwise-supremum surface already places `wStar` in the constrained `argmin` of the real explicit
gap. -/
lemma mem_constrainedArgmin_explicitGap_of_zeroOwnerSubgradient
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hzeroOwner :
      (0 : E) ∈
        constrainedSubdifferential
          (pointwiseSupremumOnEffectiveDomain Q Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (pointwiseSupremumOn Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (wStar : E)) :
    (wStar : E) ∈ argmin[Q]
      ((fun w : E ↦
        sSup
          (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ) := by
  let f : E → ℝ :=
    fun w : E ↦
      sSup
        (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))
  have hzeroSub :
      (0 : E) ∈ subdifferentialWithin Q f (wStar : E) :=
    zero_mem_subdifferentialWithin_of_zero_mem_constrainedSubdifferential_explicitPointwiseSupremumOn
      Q B hψmax wStar hzeroOwner
  -- Read the faithful owner certificate back through the real-valued `argmin` bridge.
  simpa [f] using
    mem_constrainedArgmin_explicitGap_of_zero_mem_subdifferentialWithin
      Q B wStar hzeroSub

/-- Helper for Lemma 6.5: a constrained `argmin` of the real explicit gap already determines the
ambient minimizer, the subtype minimizer, and both zero-subgradient normal forms used by the
remaining geometric bridge. -/
lemma explicitGapArgminZeroSubgradientData
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hwStarArgmin :
      (wStar : E) ∈ argmin[Q]
        ((fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ)) :
    let f : E → ℝ :=
      fun w : E ↦
        sSup
          (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))
    IsMinOn f Q (wStar : E) ∧
      IsMinOn
        (fun w : Q ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((w : E) - (v : E))))
        Set.univ
        wStar ∧
      (0 : E) ∈
        constrainedSubdifferential
          (pointwiseSupremumOnEffectiveDomain Q Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (pointwiseSupremumOn Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (wStar : E) ∧
      (0 : E) ∈ subdifferentialWithin Q f (wStar : E) := by
  let f : E → ℝ :=
    fun w : E ↦
      sSup
        (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))
  rcases (mem_constrainedArgmin_iff.mp hwStarArgmin) with ⟨_, hminAmbient⟩
  have hminSubtype :
      IsMinOn
        (fun w : Q ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((w : E) - (v : E))))
        Set.univ
        wStar := by
    -- Restrict the ambient minimizer back to the feasible subtype.
    simpa [f] using isMinOn_explicitGapSubtype_of_isMinOnAmbient Q B wStar hminAmbient
  have hzeroOwner :
      (0 : E) ∈
        constrainedSubdifferential
          (pointwiseSupremumOnEffectiveDomain Q Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (pointwiseSupremumOn Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (wStar : E) := by
    -- The subtype minimizer feeds directly into the owner-level zero-subgradient bridge.
    exact
      zero_mem_constrainedSubdifferential_explicitPointwiseSupremumOn_of_isMinOn
        Q B hψmax wStar hminSubtype
  have hzeroSub :
      (0 : E) ∈ subdifferentialWithin Q f (wStar : E) := by
    -- The ambient minimizer already yields the zero relative subgradient of the real surface.
    exact zero_mem_subdifferentialWithin_of_isMinOn wStar.property hminAmbient
  exact ⟨hminAmbient, hminSubtype, hzeroOwner, hzeroSub⟩

/-- Helper for Lemma 6.5: if every feasible displacement admits some point of a compact convex
set `C` with nonnegative pairing, then one point of `C` works for all feasible displacements. -/
lemma exists_common_nonnegative_pairing_of_pointwise_nonnegative_pairing
    [InnerProductSpace ℝ E]
    (Q C : Set E) (hQnonempty : Q.Nonempty) (hQconv : Convex ℝ Q) (hQcompact : IsCompact Q)
    (wStar : E) (hwStar : wStar ∈ Q)
    (hCnonempty : C.Nonempty) (hCconv : Convex ℝ C) (hCcompact : IsCompact C)
    (hpointwise : ∀ x ∈ Q, ∃ g ∈ C, 0 ≤ inner ℝ g (x - wStar)) :
    ∃ gBar : E, gBar ∈ C ∧ ∀ x ∈ Q, 0 ≤ inner ℝ gBar (x - wStar) := by
  let Ψ : E → E → ℝ := fun x g ↦ inner ℝ g (x - wStar)
  have hΨ_cont : ContinuousOn (fun z : E × E ↦ Ψ z.1 z.2) (Set.prod Q C) := by
    -- The bilinear pairing is continuous on `Q × C`.
    simpa [Ψ] using
      ((continuous_snd).inner (continuous_fst.sub continuous_const)).continuousOn
  have hΨ_convex : ∀ g ∈ C, ConvexOn ℝ Q (fun x : E ↦ Ψ x g) := by
    intro g hg
    refine ⟨hQconv, ?_⟩
    intro x hx y hy a b ha hb hab
    -- For fixed `g`, the pairing is affine in the primal variable.
    have haffine :
        Ψ (a • x + b • y) g = a * Ψ x g + b * Ψ y g := by
      dsimp [Ψ]
      have hdecomp :
          a • x + b • y - wStar = a • (x - wStar) + b • (y - wStar) := by
        calc
          a • x + b • y - wStar = a • x + b • y - (a + b) • wStar := by
            rw [hab, one_smul]
          _ = a • (x - wStar) + b • (y - wStar) := by
            abel
      rw [hdecomp, inner_add_right, inner_smul_right, inner_smul_right]
      ring
    exact le_of_eq haffine
  have hΨ_concave : ∀ x ∈ Q, ConcaveOn ℝ C (fun g : E ↦ Ψ x g) := by
    intro x hx
    refine ⟨hCconv, ?_⟩
    intro g₁ hg₁ g₂ hg₂ a b ha hb hab
    -- For fixed `x`, the pairing is affine in the dual variable.
    have haffine :
        Ψ x (a • g₁ + b • g₂) = a * Ψ x g₁ + b * Ψ x g₂ := by
      dsimp [Ψ]
      rw [inner_add_left, inner_smul_left, inner_smul_left]
      ring
    exact le_of_eq haffine.symm
  obtain ⟨x0, hx0, gBar, hgBar, hsaddle⟩ :=
    Sion.exists_isSaddlePointOn
      hQnonempty hQconv hQcompact
      (fun g hg ↦ (hΨ_cont.comp
        (show ContinuousOn (fun x : E ↦ (x, g)) Q from continuousOn_id.prodMk continuousOn_const)
        (show Set.MapsTo (fun x : E ↦ (x, g)) Q (Set.prod Q C) from fun x hx ↦ ⟨hx, hg⟩))
          .lowerSemicontinuousOn)
      (fun g hg ↦ (hΨ_convex g hg).quasiconvexOn)
      hCconv hCnonempty hCcompact
      (fun x hx ↦ (hΨ_cont.comp
        (show ContinuousOn (fun g : E ↦ (x, g)) C from continuousOn_const.prodMk continuousOn_id)
        (show Set.MapsTo (fun g : E ↦ (x, g)) C (Set.prod Q C) from fun g hg ↦ ⟨hx, hg⟩))
          .upperSemicontinuousOn)
      (fun x hx ↦ (hΨ_concave x hx).quasiconcaveOn)
  rcases hpointwise x0 hx0 with ⟨g0, hg0, hg0_nonneg⟩
  have hx0_nonneg : 0 ≤ Ψ x0 gBar := by
    -- At the saddle-point primal coordinate, `gBar` is a maximizing dual certificate.
    exact le_trans hg0_nonneg (hsaddle x0 hx0 g0 hg0)
  have hx0_nonpos : Ψ x0 gBar ≤ 0 := by
    -- Testing the saddle inequality at `wStar` forces the same value to be nonpositive.
    simpa [Ψ] using hsaddle (wStar : E) hwStar gBar hgBar
  have hx0_zero : Ψ x0 gBar = 0 := by
    linarith
  refine ⟨gBar, hgBar, ?_⟩
  intro x hx
  -- The saddle inequality now propagates the zero pairing at `x0` to every feasible point.
  have hmono : Ψ x0 gBar ≤ Ψ x gBar := hsaddle x hx gBar hgBar
  simpa [Ψ, hx0_zero] using hmono

/-- Helper for Lemma 6.5: a finite nonnegative weighted sum of normal-cone vectors remains in the
same normal cone. -/
lemma normalCone_weightedSum_mem
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} [Fintype ι]
    (Q : Set E) (wStar : Q) (weights : ι → ℝ)
    (hweights_nonneg : ∀ i : ι, 0 ≤ weights i) {n : ι → E}
    (hn : ∀ i : ι, n i ∈ N[Q] (wStar : E)) :
    ∑ i, weights i • n i ∈ N[Q] (wStar : E) := by
  rw [mem_normalCone_iff]
  intro y hyQ
  -- Sum the nonnegative normal-cone pairings term by term.
  have hterm :
      ∀ i : ι, 0 ≤ inner ℝ (weights i • n i) (y - (wStar : E)) := by
    intro i
    have hi : 0 ≤ inner ℝ (n i) (y - (wStar : E)) :=
      mem_normalCone_iff.mp (hn i) y hyQ
    rw [inner_smul_left]
    exact mul_nonneg (hweights_nonneg i) hi
  rw [inner_sum]
  exact Finset.sum_nonneg fun i _ ↦ hterm i

/-- Helper for Lemma 6.5: the remaining owner-level geometric step is to place the zero
constrained subgradient in the convex hull of the active affine-slice constrained
subdifferentials. -/
lemma zeroOwner_mem_convexHull_activeExplicitSliceConstrainedSubgradients
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hzeroOwner :
      (0 : E) ∈
        constrainedSubdifferential
          (pointwiseSupremumOnEffectiveDomain Q Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (pointwiseSupremumOn Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (wStar : E)) :
    (0 : E) ∈ convexHull ℝ
      {g | ∃ v : Q,
          IsGreatest
            (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
            (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
          g ∈
            constrainedSubdifferential
              (pointwiseSupremumOnEffectiveDomain Q Q
                (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
              (fun x' ↦ (inner ℝ (B (v : E)) (x' - (v : E)) : WithTop ℝ))
              (wStar : E)} := by
  -- Route correction: this is now the only remaining geometric frontier. Once the owner-level
  -- zero certificate is represented on the active constrained-slice surface, the averaging step
  -- below turns it into an active-hull point in the normal cone.
  -- TODO: prove the zero-only reverse inclusion from the owner constrained subdifferential of the
  -- explicit pointwise supremum at `wStar` to the convex hull of active affine-slice constrained
  -- subgradients, then feed that convex representation to the averaging lemma below.
  sorry

/-- Helper for Lemma 6.5: once the zero owner-level certificate is written as a finite convex
combination of active affine-slice constrained subgradients, averaging the slice remainders gives
an active-slope point in the normal cone. -/
lemma activeHullNormalWitness_of_zeroConvexCombination_activeExplicitSliceSubgradients
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hconv :
      (0 : E) ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g ∈
              constrainedSubdifferential
                (pointwiseSupremumOnEffectiveDomain Q Q
                  (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
                (fun x' ↦ (inner ℝ (B (v : E)) (x' - (v : E)) : WithTop ℝ))
                (wStar : E)}) :
    ∃ gBar : E,
      gBar ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} ∧
        gBar ∈ N[Q] (wStar : E) := by
  classical
  rcases (mem_convexHull_iff_exists_fintype.mp hconv) with
    ⟨κ, _, w, z, hw₀, hw₁, hz, hzsum⟩
  have hz' :
      ∀ i : κ,
        ∃ v : Q,
          IsGreatest
            (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
            (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
          z i ∈
            constrainedSubdifferential
              (pointwiseSupremumOnEffectiveDomain Q Q
                (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
              (fun x' ↦ (inner ℝ (B (v : E)) (x' - (v : E)) : WithTop ℝ))
              (wStar : E) := by
    intro i
    exact hz i
  choose v hvActive hzSub using hz'
  have hzRemainder :
      ∀ i : κ, ∃ n ∈ N[Q] (wStar : E), z i = B (v i : E) - n := by
    intro i
    exact
      (mem_constrainedSubdifferential_explicitAffineSlice_iff_exists_normalCone_remainder
        Q B hψmax (wStar := wStar) (v := v i) (g := z i)).mp (hzSub i)
  choose n hnNormal hzEq using hzRemainder
  have hnBar :
      ∑ i, w i • n i ∈ N[Q] (wStar : E) :=
    normalCone_weightedSum_mem Q wStar w hw₀ hnNormal
  have hsumSlopeEqNormal :
      ∑ i, w i • B (v i : E) = ∑ i, w i • n i := by
    -- Rewrite the zero convex combination of slice subgradients as the equality of the averaged
    -- active slopes and the averaged normal-cone remainders.
    calc
      ∑ i, w i • B (v i : E)
          = ∑ i, (w i • z i + w i • n i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hB : B (v i : E) = z i + n i := by
                rw [hzEq i]
                abel
              rw [hB, smul_add]
      _ = ∑ i, w i • z i + ∑ i, w i • n i := by
            rw [Finset.sum_add_distrib]
      _ = ∑ i, w i • n i := by
            rw [hzsum, zero_add]
  have hconvSlope :
      ∑ i, w i • B (v i : E) ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} := by
    -- Keep the same convex weights and replace each slice subgradient by its active slope.
    refine mem_convexHull_iff_exists_fintype.mpr ?_
    refine ⟨κ, inferInstance, w, fun i ↦ B (v i : E), hw₀, hw₁, ?_, rfl⟩
    intro i
    exact ⟨v i, hvActive i, rfl⟩
  refine ⟨∑ i, w i • B (v i : E), hconvSlope, ?_⟩
  -- The weighted normal-cone remainder equals the averaged active slope.
  rw [hsumSlopeEqNormal]
  exact hnBar

/-- Helper for Lemma 6.5: on the normalized `argmin` surface, it is enough to produce one convex
combination of active explicit slopes whose pairing is nonnegative on every feasible displacement.
The normal-cone witness is then recovered by `mem_normalCone_iff`. -/
lemma activeHullNormalWitness_of_mem_constrainedArgmin_explicitGap
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hwStarArgmin :
      (wStar : E) ∈ argmin[Q]
        ((fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ)) :
    ∃ gBar : E,
      gBar ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} ∧
        gBar ∈ N[Q] (wStar : E) := by
  obtain ⟨_, _, hzeroOwner, _⟩ :=
    explicitGapArgminZeroSubgradientData Q B hψmax wStar hwStarArgmin
  have hzeroSlices :
      (0 : E) ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g ∈
              constrainedSubdifferential
                (pointwiseSupremumOnEffectiveDomain Q Q
                  (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
                (fun x' ↦ (inner ℝ (B (v : E)) (x' - (v : E)) : WithTop ℝ))
                (wStar : E)} :=
    zeroOwner_mem_convexHull_activeExplicitSliceConstrainedSubgradients
      Q B hψmax wStar hzeroOwner
  -- Route correction: the normalized minimizer data is now consumed only through the zero-owner
  -- slice-hull bridge and the proved finite averaging lemma below.
  exact
    activeHullNormalWitness_of_zeroConvexCombination_activeExplicitSliceSubgradients
      Q B hψmax wStar hzeroSlices

/-- Helper for Lemma 6.5: on the normalized `argmin` surface, it is enough to produce one convex
combination of active explicit slopes whose pairing is nonnegative on every feasible displacement.
The normal-cone witness is then recovered by `mem_normalCone_iff`. -/
lemma exists_activeSlopeBar_mem_convexHull_and_nonnegPairing_of_mem_constrainedArgmin_explicitGap
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hwStarArgmin :
      (wStar : E) ∈ argmin[Q]
        ((fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ)) :
    ∃ gBar : E,
      gBar ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} ∧
        (∀ x ∈ Q, 0 ≤ inner ℝ gBar (x - (wStar : E))) := by
  rcases
      activeHullNormalWitness_of_mem_constrainedArgmin_explicitGap
        Q hQconv B hψmax wStar hwStarArgmin with
    ⟨gBar, hgBarHull, hgBarNormal⟩
  -- Read the normal-cone witness back as the textbook pairing inequality on `Q`.
  exact ⟨gBar, hgBarHull, mem_normalCone_iff.mp hgBarNormal⟩

/-- Helper for Lemma 6.5: the remaining reverse-inclusion step should convert the zero owner-level
constrained subgradient of the explicit `pointwiseSupremumOn` surface at `wStar` into a point of
the active explicit-slope convex hull that also lies in `N[Q] (wStar : E)`. -/
lemma activeHullNormalWitness_of_zeroOwnerSubgradient
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hzeroOwner :
      (0 : E) ∈
        constrainedSubdifferential
          (pointwiseSupremumOnEffectiveDomain Q Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (pointwiseSupremumOn Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (wStar : E)) :
    ∃ gBar : E,
      gBar ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} ∧
        gBar ∈ N[Q] (wStar : E) := by
  have hwStarArgmin :
      (wStar : E) ∈ argmin[Q]
        ((fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ) :=
    mem_constrainedArgmin_explicitGap_of_zeroOwnerSubgradient
      Q B hψmax wStar hzeroOwner
  -- Route correction: the owner-level wrapper now only forwards the normalized `argmin` data to
  -- the dedicated active-hull normal-witness bridge.
  exact
    activeHullNormalWitness_of_mem_constrainedArgmin_explicitGap
      Q hQconv B hψmax wStar hwStarArgmin

/-- Helper for Lemma 6.5: an ambient minimizer of the explicit gap on `Q` should already expose a
point of the active explicit-slope convex hull that lies in the normal cone of `Q` at `wStar`. -/
lemma activeHullNormalWitness_of_isMinOn_explicitGapAmbient
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hminAmbient :
      IsMinOn
        (fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E))))
        Q
        (wStar : E)) :
    ∃ gBar : E,
      gBar ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} ∧
        gBar ∈ N[Q] (wStar : E) := by
  have hwStarArgmin :
      (wStar : E) ∈ argmin[Q]
        ((fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ) :=
    mem_constrainedArgmin_iff.mpr ⟨wStar.property, hminAmbient⟩
  -- Route correction: the ambient minimizer is now pushed directly to the constrained-argmin
  -- surface, so the only remaining blocker sits in the geometric `argmin -> active hull ∩ normal`
  -- step below instead of in a stale owner-level zero-subgradient detour.
  exact
    activeHullNormalWitness_of_mem_constrainedArgmin_explicitGap
      Q hQconv B hψmax wStar hwStarArgmin

/-- Helper for Lemma 6.5: a zero owner-level constrained subgradient of the explicit
pointwise-supremum surface should already produce an active-slope convex-hull point in the normal
cone at `wStar`. -/
lemma activeHullNormalWitness_of_zero_mem_constrainedSubdifferential_explicitPointwiseSupremumOn
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hzeroOwner :
      (0 : E) ∈
        constrainedSubdifferential
          (pointwiseSupremumOnEffectiveDomain Q Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (pointwiseSupremumOn Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (wStar : E)) :
    ∃ gBar : E,
      gBar ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} ∧
        gBar ∈ N[Q] (wStar : E) := by
  have hminAmbient :
      IsMinOn
        (fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E))))
        Q
        (wStar : E) :=
    isMinOn_explicitGapAmbient_of_zero_mem_constrainedSubdifferential_explicitPointwiseSupremumOn
      Q B hψmax wStar hzeroOwner
  -- The zero owner-level certificate now only serves as an adapter into the direct minimizer
  -- witness theorem.
  exact
    activeHullNormalWitness_of_isMinOn_explicitGapAmbient
      Q hQconv B hψmax wStar hminAmbient

/-- Helper for Lemma 6.5: the remaining converse bridge specializes the zero owner-level
constrained subgradient at a minimizer to an active-hull point in the normal cone. -/
lemma zeroSubdifferentialWithin_explicitGap_has_activeHullNormalWitness
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hzeroSub :
      (0 : E) ∈ subdifferentialWithin Q
        ((fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ)
        (wStar : E)) :
    ∃ gBar : E,
      gBar ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} ∧
        gBar ∈ N[Q] (wStar : E) := by
  have hwStarArgmin :
      (wStar : E) ∈ argmin[Q]
        ((fun w : E ↦
          sSup
            (Set.range fun v : Q ↦ inner ℝ (B (v : E)) (w - (v : E)))) : E → ℝ) :=
    mem_constrainedArgmin_explicitGap_of_zero_mem_subdifferentialWithin
      Q B wStar hzeroSub
  -- The zero-subgradient-to-argmin transport is complete, so only the source-faithful geometric
  -- argmin step remains.
  exact
    activeHullNormalWitness_of_mem_constrainedArgmin_explicitGap
      Q hQconv B hψmax wStar hwStarArgmin

/-- Helper for Lemma 6.5: the remaining converse bridge specializes the zero owner-level
constrained subgradient at a minimizer to an active-hull point in the normal cone. -/
lemma zeroOwnerConstrainedSubgradient_has_activeHullNormalWitness
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hzeroOwner :
      (0 : E) ∈
        constrainedSubdifferential
          (pointwiseSupremumOnEffectiveDomain Q Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (pointwiseSupremumOn Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (wStar : E)) :
    ∃ gBar : E,
      gBar ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} ∧
        gBar ∈ N[Q] (wStar : E) := by
  -- The owner-level geometric converse is now isolated in its dedicated helper.
  exact
    activeHullNormalWitness_of_zero_mem_constrainedSubdifferential_explicitPointwiseSupremumOn
      Q hQconv B hψmax wStar hzeroOwner

/-- Helper for Lemma 6.5: a minimizer of the explicit gap surface should produce a convex-hull
active-slope witness whose pairing is nonnegative on every feasible displacement. -/
lemma exists_activeSlopeBar_mem_convexHull_and_nonnegPairing_of_mem_normalCone
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (B : E →ₗ[ℝ] E) (wStar : Q) :
    (∃ gBar : E,
      gBar ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} ∧
        gBar ∈ N[Q] (wStar : E)) →
    ∃ gBar : E,
      gBar ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} ∧
        (∀ x ∈ Q, 0 ≤ inner ℝ gBar (x - (wStar : E))) := by
  intro hnormal
  rcases hnormal with ⟨gBar, hgBarHull, hgBarNormal⟩
  -- Read the normal-cone witness back as the textbook pairing inequality on `Q`.
  exact ⟨gBar, hgBarHull, mem_normalCone_iff.mp hgBarNormal⟩

/-- Helper for Lemma 6.5: a minimizer of the explicit gap surface should produce a convex-hull
active-slope witness whose pairing is nonnegative on every feasible displacement. -/
lemma exists_activeSlopeBar_mem_convexHull_and_nonnegPairing_of_isMinOn
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hmin : IsMinOn
      (fun w : Q ↦
        sSup
          (Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((w : E) - (v : E))))
      Set.univ
      wStar) :
    ∃ gBar : E,
      gBar ∈ convexHull ℝ
        {g | ∃ v : Q,
            IsGreatest
              (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
              (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
            g = B (v : E)} ∧
        (∀ x ∈ Q, 0 ≤ inner ℝ gBar (x - (wStar : E))) := by
  have hzeroOwner :
      (0 : E) ∈
        constrainedSubdifferential
          (pointwiseSupremumOnEffectiveDomain Q Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (pointwiseSupremumOn Q
            (fun x' u ↦ (inner ℝ (B u) (x' - u) : WithTop ℝ)))
          (wStar : E) :=
    zero_mem_constrainedSubdifferential_explicitPointwiseSupremumOn_of_isMinOn
      Q B hψmax wStar hmin
  -- Route correction: the stale `hzeroOwner` transport branch is removed here. The remaining
  -- blocker is now isolated in the dedicated zero-owner converse helper above.
  have hHullNormal :
      ∃ gBar : E,
        gBar ∈ convexHull ℝ
          {g | ∃ v : Q,
              IsGreatest
                (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
                (inner ℝ (B (v : E)) ((wStar : E) - (v : E))) ∧
              g = B (v : E)} ∧
          gBar ∈ N[Q] (wStar : E) :=
    zeroOwnerConstrainedSubgradient_has_activeHullNormalWitness
      Q hQconv B hψmax wStar hzeroOwner
  exact
    exists_activeSlopeBar_mem_convexHull_and_nonnegPairing_of_mem_normalCone
      Q B wStar hHullNormal

/-- Helper for Lemma 6.5: the remaining missing premise is a finite active family whose averaged
explicit slope has the minimizer's normal-cone pairing on `Q`. -/
lemma exists_activeSlopeRepresentation_nonnegPairing_of_isMinOn
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hmin : IsMinOn
      (fun w : Q ↦
        sSup
          (Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((w : E) - (v : E))))
      Set.univ
      wStar) :
    ∃ (ι : Type) (_ : Fintype ι) (weights : StdSimplex ℝ ι) (v : ι → Q),
      (∀ i : ι,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
          (inner ℝ (B (v i : E)) ((wStar : E) - (v i : E)))) ∧
      (∀ x ∈ Q,
        0 ≤ inner ℝ (∑ i, weights.weights i • B (v i : E)) (x - (wStar : E))) := by
  -- Route correction: the closing step now packages the convex-hull witness produced directly
  -- from minimizer optimality, instead of reopening the old owner-level transport branch.
  have hHullNormal :=
    exists_activeSlopeBar_mem_convexHull_and_nonnegPairing_of_isMinOn
      Q hQconv B hψmax wStar hmin
  rcases hHullNormal with ⟨gBar, hgBarHull, hgBarPair⟩
  exact
    activeSlopeRepresentation_of_mem_convexHull_and_nonnegPairing
      Q B wStar hgBarHull hgBarPair

/-- Helper for Lemma 6.5: the simplex-weighted displacements from the center of mass cancel. -/
lemma centerMass_weighted_displacements_eq_zero
    {ι : Type*} [Fintype ι]
    (weights : StdSimplex ℝ ι) {Q : Set E} (v : ι → Q) :
    let uBar : E := Finset.univ.centerMass weights.weights (fun i ↦ (v i : E))
    ∑ i, weights.weights i • (uBar - (v i : E)) = 0 := by
  let uBar : E := Finset.univ.centerMass weights.weights (fun i ↦ (v i : E))
  have hweights_total : ∑ i, weights.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using weights.total
  have huBar_eq :
      uBar = ∑ i, weights.weights i • (v i : E) := by
    -- Rewrite the barycenter as the corresponding weighted finite sum.
    simpa [uBar] using
      (Finset.univ.centerMass_eq_of_sum_1 (w := weights.weights) (z := fun i ↦ (v i : E))
        hweights_total)
  -- The weighted displacements from the barycenter cancel by the defining center-mass identity.
  calc
    ∑ i, weights.weights i • (uBar - (v i : E))
        = ∑ i, (weights.weights i • uBar - weights.weights i • (v i : E)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [smul_sub]
    _ = (∑ i, weights.weights i • uBar) - ∑ i, weights.weights i • (v i : E) := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ i, weights.weights i) • uBar - ∑ i, weights.weights i • (v i : E) := by
          rw [Finset.sum_smul]
    _ = uBar - ∑ i, weights.weights i • (v i : E) := by
          rw [hweights_total, one_smul]
    _ = 0 := by rw [huBar_eq, sub_self]

/-- Helper for Lemma 6.5: pairing a fixed vector with the simplex-weighted barycenter
displacements is the corresponding weighted scalar sum. -/
lemma weighted_barycenter_pairing_eq_sum
    [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι]
    (weights : StdSimplex ℝ ι) {Q : Set E} (v : ι → Q) (g : E) :
    let uBar : E := Finset.univ.centerMass weights.weights (fun i ↦ (v i : E))
    inner ℝ g (∑ i, weights.weights i • (uBar - (v i : E))) =
      ∑ i, weights.weights i * inner ℝ g (uBar - (v i : E)) := by
  let uBar : E := Finset.univ.centerMass weights.weights (fun i ↦ (v i : E))
  -- Expand the pairing against the finite weighted displacement sum term by term.
  calc
    inner ℝ g (∑ i, weights.weights i • (uBar - (v i : E)))
        = ∑ i, inner ℝ g (weights.weights i • (uBar - (v i : E))) := by
            rw [inner_sum]
    _ = ∑ i, weights.weights i * inner ℝ g (uBar - (v i : E)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          change inner ℝ g (weights.weights i • (uBar - (v i : E))) =
            weights.weights i * inner ℝ g (uBar - (v i : E))
          simpa [smul_eq_mul] using
            (inner_smul_right_eq_smul g (uBar - (v i : E)) (weights.weights i))

/-- Helper for Lemma 6.5: at the barycenter of a simplex-weighted active family, the weighted
explicit self-payoff is nonpositive because each term is bounded by the barycenter slice and the
weighted barycenter displacement sums to `0`. -/
lemma weightedActivePayoff_nonpos
    [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι]
    (B : E →ₗ[ℝ] E) (hBmono : ∀ h : E, 0 ≤ inner ℝ (B h) h)
    (weights : StdSimplex ℝ ι) {Q : Set E} (v : ι → Q) :
    let uBar : E := Finset.univ.centerMass weights.weights (fun i ↦ (v i : E))
    ∑ i, weights.weights i * inner ℝ (B (v i : E)) (uBar - (v i : E)) ≤ 0 := by
  let uBar : E := Finset.univ.centerMass weights.weights (fun i ↦ (v i : E))
  have hcompare :
      ∀ i : ι,
        inner ℝ (B (v i : E)) (uBar - (v i : E)) ≤
          inner ℝ (B uBar) (uBar - (v i : E)) := by
    intro i
    -- Monotonicity on the displacement `vᵢ - uBar` compares each active slice to the barycenter.
    have hmono_i :
        0 ≤ inner ℝ (B ((v i : E) - uBar)) ((v i : E) - uBar) := hBmono ((v i : E) - uBar)
    have hmono_expanded :
        0 ≤
          inner ℝ (B (v i : E)) ((v i : E) - uBar) -
            inner ℝ (B uBar) ((v i : E) - uBar) := by
      simpa [map_sub, inner_sub_left] using hmono_i
    have hforward :
        inner ℝ (B uBar) ((v i : E) - uBar) ≤
          inner ℝ (B (v i : E)) ((v i : E) - uBar) := by
      linarith
    have hneg_vi :
        inner ℝ (B (v i : E)) (uBar - (v i : E)) =
          -inner ℝ (B (v i : E)) ((v i : E) - uBar) := by
      rw [show uBar - (v i : E) = -((v i : E) - uBar) by abel, inner_neg_right]
    have hneg_uBar :
        inner ℝ (B uBar) (uBar - (v i : E)) =
          -inner ℝ (B uBar) ((v i : E) - uBar) := by
      rw [show uBar - (v i : E) = -((v i : E) - uBar) by abel, inner_neg_right]
    rw [hneg_vi, hneg_uBar]
    exact neg_le_neg hforward
  have hweighted_compare :
      ∀ i : ι,
        weights.weights i * inner ℝ (B (v i : E)) (uBar - (v i : E)) ≤
          weights.weights i * inner ℝ (B uBar) (uBar - (v i : E)) := by
    intro i
    exact mul_le_mul_of_nonneg_left (hcompare i) (weights.nonneg i)
  have hsum_compare :
      ∑ i, weights.weights i * inner ℝ (B (v i : E)) (uBar - (v i : E)) ≤
        ∑ i, weights.weights i * inner ℝ (B uBar) (uBar - (v i : E)) := by
    -- Summing the weighted pointwise comparisons preserves the inequality.
    exact Finset.sum_le_sum fun i hi ↦ hweighted_compare i
  have hdisp_zero :
      ∑ i, weights.weights i • (uBar - (v i : E)) = 0 := by
    -- The weighted barycenter displacements cancel exactly.
    simpa [uBar] using centerMass_weighted_displacements_eq_zero weights v
  have hsum_barycenter :
      ∑ i, weights.weights i * inner ℝ (B uBar) (uBar - (v i : E)) = 0 := by
    -- Factor the common barycenter slope through the cancelled displacement sum.
    calc
      ∑ i, weights.weights i * inner ℝ (B uBar) (uBar - (v i : E))
          = inner ℝ (B uBar) (∑ i, weights.weights i • (uBar - (v i : E))) := by
              symm
              simpa [uBar] using weighted_barycenter_pairing_eq_sum weights v (B uBar)
      _ = 0 := by simpa [hdisp_zero]
  exact hsum_compare.trans_eq hsum_barycenter

/-- Helper for Lemma 6.5: an active finite family whose averaged slope has the minimizer's
nonnegative pairing on `Q` forces the explicit gap at `wStar` to be nonpositive. -/
lemma explicitGapFunction_nonpos_of_activeSlopeRepresentation_nonnegPairing
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hBmono : ∀ h : E, 0 ≤ inner ℝ (B h) h)
    (wStar : Q) (weights : StdSimplex ℝ ι) (v : ι → Q)
    (hvActive :
      ∀ i : ι,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E)))
          (inner ℝ (B (v i : E)) ((wStar : E) - (v i : E))))
    (hpair :
      ∀ x ∈ Q,
        0 ≤ inner ℝ (∑ i, weights.weights i • B (v i : E)) (x - (wStar : E))) :
    sSup
      (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E))) ≤ 0 := by
  let payoffSet : Set ℝ :=
    Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((wStar : E) - (u : E))
  let uBar : E := Finset.univ.centerMass weights.weights (fun i ↦ (v i : E))
  let gBar : E := ∑ i, weights.weights i • B (v i : E)
  have hweights_total : ∑ i, weights.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using weights.total
  have huBar_mem : uBar ∈ Q := by
    -- The barycenter stays feasible because the simplex weights form a convex combination.
    refine hQconv.centerMass_mem ?_ ?_ ?_
    · intro i hi
      exact weights.nonneg i
    · simpa [hweights_total] using (show (0 : ℝ) < 1 by norm_num)
    · intro i hi
      exact (v i).property
  have hweighted_nonpos :
      ∑ i, weights.weights i * inner ℝ (B (v i : E)) (uBar - (v i : E)) ≤ 0 := by
    simpa [uBar] using weightedActivePayoff_nonpos B hBmono weights v
  have hpair_uBar :
      0 ≤ inner ℝ gBar (uBar - (wStar : E)) := hpair uBar huBar_mem
  have hpair_nonpos : inner ℝ gBar ((wStar : E) - uBar) ≤ 0 := by
    -- Reverse the pairing direction to compare with the decomposition of the active payoffs.
    have hneg :
        inner ℝ gBar ((wStar : E) - uBar) = -inner ℝ gBar (uBar - (wStar : E)) := by
      rw [show ((wStar : E) - uBar) = -(uBar - (wStar : E)) by abel, inner_neg_right]
    rw [hneg]
    exact neg_nonpos.mpr hpair_uBar
  have hactive_sum :
      ∑ i, weights.weights i * inner ℝ (B (v i : E)) ((wStar : E) - (v i : E)) =
        sSup payoffSet := by
    -- Every active point realizes the same explicit gap value at `wStar`.
    calc
      ∑ i, weights.weights i * inner ℝ (B (v i : E)) ((wStar : E) - (v i : E))
          = ∑ i, weights.weights i * sSup payoffSet := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [(hvActive i).csSup_eq]
      _ = (∑ i, weights.weights i) * sSup payoffSet := by
            rw [Finset.sum_mul]
      _ = sSup payoffSet := by rw [hweights_total, one_mul]
  have hsplit :
      ∑ i, weights.weights i * inner ℝ (B (v i : E)) ((wStar : E) - (v i : E)) =
        ∑ i, weights.weights i * inner ℝ (B (v i : E)) (uBar - (v i : E)) +
          ∑ i, weights.weights i * inner ℝ (B (v i : E)) ((wStar : E) - uBar) := by
    -- Split the active payoff through the feasible barycenter `uBar`.
    calc
      ∑ i, weights.weights i * inner ℝ (B (v i : E)) ((wStar : E) - (v i : E))
          = ∑ i,
              (weights.weights i * inner ℝ (B (v i : E)) (uBar - (v i : E)) +
                weights.weights i * inner ℝ (B (v i : E)) ((wStar : E) - uBar)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                have hdecomp :
                    (wStar : E) - (v i : E) = (uBar - (v i : E)) + ((wStar : E) - uBar) := by
                  abel
                rw [hdecomp, inner_add_right, mul_add]
      _ =
          ∑ i, weights.weights i * inner ℝ (B (v i : E)) (uBar - (v i : E)) +
            ∑ i, weights.weights i * inner ℝ (B (v i : E)) ((wStar : E) - uBar) := by
              rw [Finset.sum_add_distrib]
  have hgradient_sum :
      ∑ i, weights.weights i * inner ℝ (B (v i : E)) ((wStar : E) - uBar) =
        inner ℝ gBar ((wStar : E) - uBar) := by
    -- The common displacement factors the weighted slopes into the averaged slope `gBar`.
    calc
      ∑ i, weights.weights i * inner ℝ (B (v i : E)) ((wStar : E) - uBar)
          = ∑ i, inner ℝ (weights.weights i • B (v i : E)) ((wStar : E) - uBar) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa [smul_eq_mul] using
                (inner_smul_left_eq_smul
                  (x := B (v i : E))
                  (y := (wStar : E) - uBar)
                  (r := weights.weights i)).symm
      _ = inner ℝ (∑ i, weights.weights i • B (v i : E)) ((wStar : E) - uBar) := by
            rw [sum_inner]
      _ = inner ℝ gBar ((wStar : E) - uBar) := by rfl
  have hgap_nonpos :
      sSup payoffSet ≤ 0 := by
    -- Combine the barycenter self-payoff bound with the nonpositive pairing of the averaged slope.
    rw [← hactive_sum, hsplit, hgradient_sum]
    linarith
  simpa [payoffSet] using hgap_nonpos

/-- Helper for Lemma 6.5: once the explicit minimization statement is known, the remaining task is
to show that every whole-set minimizer has explicit gap value `0`. -/
lemma explicitGapFunction_eq_zero_of_isMinOn_aux
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hBmono : ∀ h : E, 0 ≤ inner ℝ (B h) h)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hmin : IsMinOn
      (fun w : Q ↦
        sSup
          (Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((w : E) - (v : E))))
      Set.univ
      wStar) :
    sSup
      (Set.range fun v : Q ↦ inner ℝ (B (v : E)) ((wStar : E) - (v : E))) = 0 := by
  -- Route correction: the reverse implication now closes directly from an active finite family
  -- whose averaged slope has the minimizer's nonnegative pairing on `Q`.
  obtain ⟨κ, hκ, weights, v, hvActive, hpair⟩ :=
    exists_activeSlopeRepresentation_nonnegPairing_of_isMinOn Q hQconv B hψmax wStar hmin
  apply le_antisymm
  · exact
      @explicitGapFunction_nonpos_of_activeSlopeRepresentation_nonnegPairing
        E _ _ _ _ κ hκ Q hQconv B hBmono wStar weights v hvActive hpair
  · exact explicitGapFunction_nonneg Q B hψmax wStar

/-- Lemma 6.5: for a convex set `Q ⊆ E` and a monotone linear operator `B : E →ₗ[ℝ] E`, the
explicit gap bridge
`ψ(w) = sup_{v ∈ Q} ⟪B(v), w - v⟫`
is minimized exactly at the feasible solutions of the source variational inequality. The
additional hypothesis `hψmax` records that this supremum is attained for each feasible `w`, so the
`sSup` surface faithfully bridges the source `max` notation. -/
theorem isSolution_iff_isMinOn_explicitGapFunction
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hBmono : ∀ h : E, 0 ≤ inner ℝ (B h) h)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q) :
    (∀ v ∈ Q, 0 ≤ inner ℝ (B (wStar : E)) (v - (wStar : E))) ↔
      IsMinOn
        (fun w : Q ↦
          sSup
            (Set.range fun v : Q ↦
              inner ℝ (B (v : E)) ((w : E) - (v : E))))
        Set.univ
        wStar := by
  constructor
  · intro hsol
    -- A solution has zero explicit gap, while every feasible point has nonnegative explicit gap.
    refine isMinOn_univ_iff.mpr ?_
    intro w
    rw [explicitGapFunction_eq_zero_of_isSolutionAux Q B hBmono hψmax wStar hsol]
    exact explicitGapFunction_nonneg Q B hψmax w
  · intro hmin
    -- Route correction: the owner proof cannot be reused directly here because the explicit
    -- theorem assumes only convexity plus pointwise attainment, not the owner's compactness data.
    have hzero :
        sSup
            (Set.range fun v : Q ↦
              inner ℝ (B (v : E)) ((wStar : E) - (v : E))) = 0 := by
      -- Reduce the reverse implication to the pending zero-gap lemma for whole-set minimizers.
      exact explicitGapFunction_eq_zero_of_isMinOn_aux Q hQconv B hBmono hψmax wStar hmin
    by_contra hnot
    have hpos :
        0 <
          sSup
            (Set.range fun v : Q ↦
              inner ℝ (B (v : E)) ((wStar : E) - (v : E))) := by
      -- Failure of the variational inequality gives a strictly positive explicit gap at `wStar`.
      exact explicitGapFunction_pos_of_not_isSolution Q hQconv B hψmax wStar hnot
    linarith

/-- Source-facing corollary to Lemma 6.5: under the textbook convexity hypothesis, any feasible
point satisfying the explicit variational inequality has explicit gap value `0` for the supremum
bridge `ψ(w) = sup_{v ∈ Q} ⟪B(v), w - v⟫`, with `hψmax` recording that the displayed supremum is a
genuine maximum. -/
theorem explicitGapFunction_eq_zero_of_isSolution
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (_hQconv : Convex ℝ Q) (B : E →ₗ[ℝ] E)
    (hBmono : ∀ h : E, 0 ≤ inner ℝ (B h) h)
    (hψmax :
      ∀ w : Q, ∃ v : Q,
        IsGreatest
          (Set.range fun u : Q ↦ inner ℝ (B (u : E)) ((w : E) - (u : E)))
          (inner ℝ (B (v : E)) ((w : E) - (v : E))))
    (wStar : Q)
    (hsol : ∀ v ∈ Q, 0 ≤ inner ℝ (B (wStar : E)) (v - (wStar : E))) :
    sSup
      (Set.range fun v : Q ↦
        inner ℝ (B (v : E)) ((wStar : E) - (v : E))) = 0 := by
  -- This is the source-facing zero-gap theorem proved directly on the explicit payoff surface.
  exact explicitGapFunction_eq_zero_of_isSolutionAux Q B hBmono hψmax wStar hsol

end
