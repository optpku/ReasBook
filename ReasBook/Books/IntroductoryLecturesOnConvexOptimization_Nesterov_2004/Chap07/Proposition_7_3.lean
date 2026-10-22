/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Example_2_1_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_22
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.LinearEqualityFeasibleSet
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_34

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators SupportFunction NormalCone WithTopConvexAnalysis

variable {m n : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "Eₙ₋₁" => EuclideanSpace ℝ (Fin (n - 1))

/- Proposition 7.3 lies in the chapter's homogeneous linear-programming / support-envelope
duality domain.

Sampled owner-style declarations:
* `supportFunction` and `supportFunction_apply` in `Chap03/Definition_3_9`, the chapter owner for
  suprema of linear functionals over sets;
* `linearEqualityFeasibleSet` and `mem_linearEqualityFeasibleSet_iff` in
  `Chap03/LinearEqualityFeasibleSet`, the chapter owner for feasible regions cut out by
  `u ∈ Q` and a linear equality `A u = b`;
* `zeroOneBox` in `Chap01/Definition_1_3_1`, the project's explicit-dimension box-owner pattern;
* `linearOptimizationProblemWithNonnegativityConstraints` in `Chap05/Definition_5_4_3_1`, a
  nearby project file that specializes equality-feasible-set owners to linear programs.

Best owner abstraction:
* source-facing: the Chapter 7 homogeneous linear-programming value `f*` and dual profile `φ₁`;
* core/canonical: the Chapter 3 support-function owner applied to `coordinatewiseUnitBox m`,
  together with the Chapter 3 equality-feasible-set owner
  `linearEqualityFeasibleSet (coordinatewiseUnitBox m) hatA.transpose.toEuclideanLin 0`;
* bridge/view: the coordinatewise box-membership lemma and the explicit sum-of-absolute-values
  formula for `φ₁`.

Primitive data:
* the source-facing box `coordinatewiseUnitBox m`;
* the matrix `hatA` and vector `c`.

Derived API:
* the feasible set and optimal value of the homogeneous linear program;
* the support-function/supremum expansion of `φ₁`;
* the explicit `∑ |(hatA.mulVec y)ᵢ + cᵢ|` formula and the least-value theorem.

This refinement keeps the Chapter 7 source-facing owners, but gives the box its explicit dimension
parameter and presents the feasible region as a thin specialization of the canonical
`linearEqualityFeasibleSet` owner instead of rebuilding the conjunction by hand.
-/

/-- The coordinatewise box `[-1, 1]^m` in `ℝ^m`. -/
abbrev coordinatewiseUnitBox (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {u | ∀ i, |u i| ≤ 1}

/-- Membership in `coordinatewiseUnitBox` means satisfying `|uᵢ| ≤ 1` in every coordinate. -/
@[simp]
theorem mem_coordinatewiseUnitBox_iff {u : Eₘ} :
    u ∈ coordinatewiseUnitBox m ↔ ∀ i, |u i| ≤ 1 :=
  Iff.rfl

/-- Helper for Proposition 7.3: the linear functional `u ↦ ⟪v, u⟫` attains its maximum on the
coordinatewise unit box at the coordinatewise sign vector, with value `∑ᵢ |vᵢ|`. -/
theorem isGreatest_inner_image_coordinatewiseUnitBox (v : Eₘ) :
    IsGreatest ((fun u : Eₘ ↦ inner ℝ v u) '' coordinatewiseUnitBox m)
      (∑ i : Fin m, |v i|) := by
  let uSign : Eₘ := WithLp.toLp 2 fun i ↦ (SignType.sign (v i) : ℝ)
  have huSign : uSign ∈ coordinatewiseUnitBox m := by
    -- The sign vector stays inside the box because every coordinate has absolute value at most `1`.
    intro i
    rcases lt_trichotomy (v i) 0 with hneg | hzero | hpos
    · simpa [uSign, hneg] using (show |(-1 : ℝ)| ≤ 1 by norm_num)
    · simpa [uSign, hzero] using (show |(0 : ℝ)| ≤ 1 by norm_num)
    · simpa [uSign, hpos] using (show |(1 : ℝ)| ≤ 1 by norm_num)
  refine ⟨?_, ?_⟩
  · -- The sign vector realizes the claimed value.
    refine ⟨uSign, huSign, ?_⟩
    change inner ℝ v uSign = ∑ i : Fin m, |v i|
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    calc
      inner ℝ (v i) (uSign i) = v i * (SignType.sign (v i) : ℝ) := by
        have huSign_i : uSign i = (SignType.sign (v i) : ℝ) := by
          simp [uSign]
        rw [huSign_i]
        exact RCLike.inner_apply' (v i) ((SignType.sign (v i) : ℝ))
      _ = |v i| := self_mul_sign (v i)
  · intro z hz
    rcases hz with ⟨u, hu, rfl⟩
    change inner ℝ v u ≤ ∑ i : Fin m, |v i|
    rw [PiLp.inner_apply]
    have hinner :
        ∑ i : Fin m, inner ℝ (v i) (u i) =
          ∑ i : Fin m, v i * u i := by
      refine Finset.sum_congr rfl ?_
      intro i _
      simpa using (RCLike.inner_apply' (v i) (u i))
    rw [hinner]
    calc
      ∑ i : Fin m, v i * u i ≤ ∑ i : Fin m, |v i * u i| := by
        refine Finset.sum_le_sum ?_
        intro i _
        exact le_abs_self (v i * u i)
      _ = ∑ i : Fin m, |v i| * |u i| := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [abs_mul]
      _ ≤ ∑ i : Fin m, |v i| * 1 := by
        refine Finset.sum_le_sum ?_
        intro i _
        exact mul_le_mul_of_nonneg_left (hu i) (abs_nonneg (v i))
      _ = ∑ i : Fin m, |v i| := by
        simp

/-- The function `φ₁(y)` is the Chapter 3 support function of the coordinatewise box `[-1, 1]^m`,
evaluated at the affine coefficient vector `\hat A y + c`. -/
def homogeneousLinearProgrammingPhi1
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) : Eₙ₋₁ → ℝ :=
  fun y ↦ (ξ[coordinatewiseUnitBox m] (hatA.toEuclideanLin y + c)).toReal

/-- Evaluating `homogeneousLinearProgrammingPhi1 hatA c` at `y` recovers its defining supremum
of the linear functional `u ↦ ⟪\hat A y + c, u⟫` over `coordinatewiseUnitBox`. -/
-- Proof sketch: expand the Chapter 3 support-function owner by `supportFunction_apply`.
theorem homogeneousLinearProgrammingPhi1_eq_sSup
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) (y : Eₙ₋₁) :
    homogeneousLinearProgrammingPhi1 hatA c y =
      sSup
        ((fun u : Eₘ ↦ inner ℝ (hatA.toEuclideanLin y + c) u) '' coordinatewiseUnitBox m) := by
  let v : Eₘ := hatA.toEuclideanLin y + c
  have hgreatest :
      IsGreatest ((fun u : Eₘ ↦ inner ℝ v u) '' coordinatewiseUnitBox m)
        (∑ i : Fin m, |v i|) :=
    isGreatest_inner_image_coordinatewiseUnitBox (m := m) v
  have hgreatestEReal :
      IsGreatest
        ((fun u : Eₘ ↦ ((inner ℝ v u : ℝ) : EReal)) '' coordinatewiseUnitBox m)
        ((∑ i : Fin m, |v i| : ℝ) : EReal) := by
    -- The same maximizer statement transfers to the `EReal` image used by `supportFunction`.
    simpa only [Set.image_image] using
      (EReal.coe_strictMono.map_isGreatest).2 hgreatest
  -- Route correction: compute both sides by the same attained maximum value instead of trying to
  -- rewrite `EReal.toReal` of a bare supremum directly.
  calc
    homogeneousLinearProgrammingPhi1 hatA c y
        = ∑ i : Fin m, |v i| := by
            -- Expand the support function and use the attained `EReal` maximum.
            rw [homogeneousLinearProgrammingPhi1, supportFunction_apply]
            have hcsSup :
                sSup ((fun g : Eₘ ↦ ((inner ℝ g v : ℝ) : EReal)) '' coordinatewiseUnitBox m) =
                  ((∑ i : Fin m, |v i| : ℝ) : EReal) := by
              simpa [real_inner_comm] using hgreatestEReal.csSup_eq
            rw [hcsSup]
            simp [v]
    _ = sSup ((fun u : Eₘ ↦ inner ℝ v u) '' coordinatewiseUnitBox m) := by
          symm
          exact hgreatest.csSup_eq
    _ = sSup
          ((fun u : Eₘ ↦ inner ℝ (hatA.toEuclideanLin y + c) u) '' coordinatewiseUnitBox m) := by
          simp [v]

/-- The box-constrained feasible set of the dual linear program
`max {⟪c, u⟫ : \hat Aᵀ u = 0, |uᵢ| ≤ 1}`. -/
abbrev homogeneousLinearProgrammingFeasibleSet
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) : Set Eₘ :=
  linearEqualityFeasibleSet (coordinatewiseUnitBox m) hatA.transpose.toEuclideanLin 0

/-- Membership in `homogeneousLinearProgrammingFeasibleSet hatA` means satisfying the linear
constraint `\hat Aᵀ u = 0` together with the coordinatewise bounds `|uᵢ| ≤ 1`. -/
@[simp]
theorem mem_homogeneousLinearProgrammingFeasibleSet_iff
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (u : Eₘ) :
    u ∈ homogeneousLinearProgrammingFeasibleSet hatA ↔
      hatA.transpose.mulVec u = 0 ∧ u ∈ coordinatewiseUnitBox m := by
  change
    u ∈ linearEqualityFeasibleSet (coordinatewiseUnitBox m) hatA.transpose.toEuclideanLin
      (0 : Eₙ₋₁) ↔
      hatA.transpose.mulVec u = 0 ∧ u ∈ coordinatewiseUnitBox m
  rw [mem_linearEqualityFeasibleSet_iff]
  constructor
  · rintro ⟨hu, hA⟩
    refine ⟨?_, hu⟩
    ext i
    have hi : (hatA.transpose.toEuclideanLin u) i = 0 := by
      simpa using congrArg (fun v : Eₙ₋₁ ↦ v i) hA
    simpa using hi
  · rintro ⟨hA, hu⟩
    refine ⟨hu, ?_⟩
    ext i
    have hi : (hatA.transpose.mulVec u) i = 0 := by
      simpa using congrArg (fun v ↦ v i) hA
    simpa using hi

/-- The optimal value `f*` of the box-constrained dual linear program
`max {⟪c, u⟫ : \hat Aᵀ u = 0, |uᵢ| ≤ 1}`. -/
def homogeneousLinearProgrammingOptimalValue
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) : ℝ :=
  sSup ((fun u : Eₘ ↦ inner ℝ c u) '' homogeneousLinearProgrammingFeasibleSet hatA)

/-- Expanding `homogeneousLinearProgrammingOptimalValue hatA c` gives the defining supremum of
the linear functional `u ↦ ⟪c, u⟫` over the feasible set. -/
-- Proof sketch: unfold `homogeneousLinearProgrammingOptimalValue`.
theorem homogeneousLinearProgrammingOptimalValue_eq_sSup
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) :
    homogeneousLinearProgrammingOptimalValue hatA c =
      sSup ((fun u : Eₘ ↦ inner ℝ c u) '' homogeneousLinearProgrammingFeasibleSet hatA) := by
  -- This is exactly the defining supremum stored by `homogeneousLinearProgrammingOptimalValue`.
  rfl

/-- Helper for Proposition 7.3: the subdifferential of a linear inner-product functional is the
singleton containing its coefficient vector. -/
lemma subdifferential_inner_eq_singleton_local (v x : Eₘ) :
    ∂ (fun y : Eₘ ↦ ((inner ℝ v y : ℝ) : WithTop ℝ))(x) = ({v} : Set Eₘ) := by
  ext g
  rw [Set.mem_singleton_iff, mem_subdifferential_coe_real_iff]
  constructor
  · intro hg
    -- Test the subgradient inequality in the direction `g - v` to force the norm gap to vanish.
    have hz := hg (x + (g - v))
    have hineq : inner ℝ g (g - v) ≤ inner ℝ v (g - v) := by
      have hrewrite :
          inner ℝ v (x + (g - v)) = inner ℝ v x + inner ℝ v (g - v) := by
        rw [inner_add_right]
      have hsub : x + (g - v) - x = g - v := by
        abel_nf
      rw [hrewrite, hsub] at hz
      linarith
    have hnonpos : ‖g - v‖ ^ (2 : ℕ) ≤ 0 := by
      have hpair : inner ℝ (g - v) (g - v) ≤ 0 := by
        calc
          inner ℝ (g - v) (g - v) = inner ℝ g (g - v) - inner ℝ v (g - v) := by
            rw [inner_sub_left]
          _ ≤ 0 := sub_nonpos.mpr hineq
      simpa [real_inner_self_eq_norm_sq] using hpair
    have hzeroNorm : ‖g - v‖ = 0 := by
      nlinarith [sq_nonneg ‖g - v‖, hnonpos]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzeroNorm)
  · intro hg
    subst hg
    -- The true coefficient vector realizes the subgradient inequality with equality.
    intro y
    have hy : y = x + (y - x) := by
      abel_nf
    have hsub : x + (y - x) - x = y - x := by
      abel_nf
    rw [hy, inner_add_right, hsub]

/-- The auxiliary function `φ₁` is the sum of the coordinatewise absolute values
`|(\hat A y + c)ᵢ|`. -/
-- Proof sketch: expand the support-function form of `φ₁`, observe that the maximization over
-- `coordinatewiseUnitBox m` decouples by coordinates, and maximize each scalar term
-- `(\hat A y + c)ᵢ uᵢ` over `|uᵢ| ≤ 1`.
theorem homogeneousLinearProgrammingPhi1_eq_sum_abs
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) (y : Eₙ₋₁) :
    homogeneousLinearProgrammingPhi1 hatA c y =
      ∑ i : Fin m, |(hatA.toEuclideanLin y + c) i| := by
  -- Replace `φ₁` by the attained support-function supremum and evaluate that maximum explicitly.
  rw [homogeneousLinearProgrammingPhi1_eq_sSup]
  exact (isGreatest_inner_image_coordinatewiseUnitBox
    (m := m) (hatA.toEuclideanLin y + c)).csSup_eq

/-- Helper for Proposition 7.3: every feasible dual point gives a weak-duality lower bound on the
support-function objective `φ₁(y)`. -/
theorem le_homogeneousLinearProgrammingPhi1_of_feasible
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) {u : Eₘ}
    (hu : u ∈ homogeneousLinearProgrammingFeasibleSet hatA) (y : Eₙ₋₁) :
    inner ℝ c u ≤ homogeneousLinearProgrammingPhi1 hatA c y := by
  rcases (mem_homogeneousLinearProgrammingFeasibleSet_iff hatA u).mp hu with ⟨hAu, huBox⟩
  have hAuLin : hatA.transpose.toEuclideanLin u = 0 := by
    -- Rewrite the matrix equality constraint into the linear-map form needed for the adjoint step.
    ext i
    have hi : (hatA.transpose.mulVec u) i = 0 := by
      simpa using congrArg (fun w ↦ w i) hAu
    simpa using hi
  have hAy_zero : inner ℝ (hatA.toEuclideanLin y) u = 0 := by
    have hadj : hatA.toEuclideanLin.adjoint = hatA.transpose.toEuclideanLin := by
      simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint hatA).symm
    calc
      inner ℝ (hatA.toEuclideanLin y) u = inner ℝ y (hatA.toEuclideanLin.adjoint u) := by
        simpa using (LinearMap.adjoint_inner_right (hatA.toEuclideanLin) y u).symm
      _ = inner ℝ y (hatA.transpose.toEuclideanLin u) := by
        rw [hadj]
      _ = 0 := by simp [hAuLin]
  have hmem :
      inner ℝ (hatA.toEuclideanLin y + c) u ∈
        ((fun w : Eₘ ↦ inner ℝ (hatA.toEuclideanLin y + c) w) '' coordinatewiseUnitBox m) :=
    ⟨u, huBox, rfl⟩
  have himage_le :
      inner ℝ (hatA.toEuclideanLin y + c) u ≤
        ∑ i : Fin m, |(hatA.toEuclideanLin y + c) i| :=
    (isGreatest_inner_image_coordinatewiseUnitBox
      (m := m) (hatA.toEuclideanLin y + c)).2 hmem
  -- The equality constraint kills the `⟪\hat A y, u⟫` term, leaving only `⟪c, u⟫`.
  calc
    inner ℝ c u = inner ℝ (hatA.toEuclideanLin y + c) u := by
      rw [inner_add_left, hAy_zero, zero_add]
    _ ≤ ∑ i : Fin m, |(hatA.toEuclideanLin y + c) i| := himage_le
    _ = homogeneousLinearProgrammingPhi1 hatA c y := by
      symm
      exact homogeneousLinearProgrammingPhi1_eq_sum_abs hatA c y

/-- Helper for Proposition 7.3: the dual optimal value is bounded above by every value of `φ₁`. -/
theorem homogeneousLinearProgrammingOptimalValue_le_phi1
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) (y : Eₙ₋₁) :
    homogeneousLinearProgrammingOptimalValue hatA c ≤ homogeneousLinearProgrammingPhi1 hatA c y := by
  rw [homogeneousLinearProgrammingOptimalValue_eq_sSup]
  have hzero_feasible : (0 : Eₘ) ∈ homogeneousLinearProgrammingFeasibleSet hatA := by
    rw [mem_homogeneousLinearProgrammingFeasibleSet_iff]
    constructor
    · simp
    · simp [mem_coordinatewiseUnitBox_iff]
  have himage_nonempty :
      (((fun u : Eₘ ↦ inner ℝ c u) '' homogeneousLinearProgrammingFeasibleSet hatA) : Set ℝ).Nonempty :=
    ⟨0, ⟨0, hzero_feasible, by simp⟩⟩
  -- Apply weak duality pointwise to every feasible image value.
  refine show
      sSup ((fun u : Eₘ ↦ inner ℝ c u) '' homogeneousLinearProgrammingFeasibleSet hatA) ≤
        homogeneousLinearProgrammingPhi1 hatA c y from
      csSup_le himage_nonempty ?_
  rintro z ⟨u, hu, rfl⟩
  exact le_homogeneousLinearProgrammingPhi1_of_feasible hatA c hu y

/-- Helper for Proposition 7.3: the coordinatewise unit box is closed. -/
lemma isClosed_coordinatewiseUnitBox : IsClosed (coordinatewiseUnitBox m : Set Eₘ) := by
  -- The box is the finite intersection of the closed coordinate slabs `|u i| ≤ 1`.
  classical
  have hset :
      (coordinatewiseUnitBox m : Set Eₘ) = ⋂ i : Fin m, {u : Eₘ | |u i| ≤ 1} := by
    ext u
    simp [coordinatewiseUnitBox]
  rw [hset]
  exact isClosed_iInter fun i : Fin m =>
    isClosed_le
      (continuous_abs.comp (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i))
      continuous_const

/-- Helper for Proposition 7.3: convex combinations preserve the coordinatewise unit box. -/
lemma convex_coordinatewiseUnitBox : Convex ℝ (coordinatewiseUnitBox m : Set Eₘ) := by
  intro x hx y hy a b ha hb hab
  intro i
  -- Bound each coordinate of the convex combination by the convex combination of the bounds.
  calc
    |(a • x + b • y) i| = |a * x i + b * y i| := by
      simp [smul_eq_mul]
    _ ≤ |a * x i| + |b * y i| := abs_add_le _ _
    _ = a * |x i| + b * |y i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := by
      have hax : a * |x i| ≤ a * 1 := mul_le_mul_of_nonneg_left (hx i) ha
      have hby : b * |y i| ≤ b * 1 := mul_le_mul_of_nonneg_left (hy i) hb
      linarith
    _ = 1 := by linarith

/-- Helper for Proposition 7.3: every point of the coordinatewise unit box has norm at most `m`,
so the box lies in the closed ball of radius `m` about the origin. -/
lemma coordinatewiseUnitBox_subset_closedBall :
    coordinatewiseUnitBox m ⊆ Metric.closedBall (0 : Eₘ) m := by
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  -- Bound the squared norm by summing the coordinatewise bounds `|u i| ≤ 1`.
  have hsum_le : ∑ i : Fin m, ‖u i‖ ^ 2 ≤ ∑ i : Fin m, (1 : ℝ) ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro i _
    have hui : ‖u i‖ ≤ 1 := by
      simpa [Real.norm_eq_abs] using hu i
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg _)] using hui)
  have hsqrt_le :
      Real.sqrt (∑ i : Fin m, ‖u i‖ ^ 2) ≤
        Real.sqrt (∑ i : Fin m, (1 : ℝ) ^ 2) :=
    Real.sqrt_le_sqrt hsum_le
  have hsqrt_le' : Real.sqrt (∑ i : Fin m, ‖u i‖ ^ 2) ≤ Real.sqrt m := by
    simpa using hsqrt_le
  cases m with
  | zero =>
      simpa using hsqrt_le'
  | succ k =>
      have hk_nonneg : (0 : ℝ) ≤ (Nat.succ k : ℝ) := by
        positivity
      have hk_one : (1 : ℝ) ≤ (Nat.succ k : ℝ) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
      have hsqrt_bound : Real.sqrt (Nat.succ k : ℝ) ≤ (Nat.succ k : ℝ) := by
        nlinarith [Real.sq_sqrt hk_nonneg, hk_one]
      exact hsqrt_le'.trans hsqrt_bound

/-- Helper for Proposition 7.3: the open Euclidean unit ball around the origin sits inside the
coordinatewise unit box. -/
lemma metricBall_subset_coordinatewiseUnitBox :
    Metric.ball (0 : Eₘ) 1 ⊆ coordinatewiseUnitBox m := by
  intro u huBall i
  have hcoord : |u i| ≤ ‖u‖ := by
    -- Read the `i`-th coordinate as an inner product with the standard basis vector.
    calc
      |u i| = |inner ℝ u (EuclideanSpace.basisFun (Fin m) ℝ i)| := by
        rw [EuclideanSpace.inner_basisFun_real]
      _ ≤ ‖u‖ * ‖EuclideanSpace.basisFun (Fin m) ℝ i‖ := abs_real_inner_le_norm _ _
      _ = ‖u‖ := by
        simp
  have hunorm : ‖u‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using huBall
  exact hcoord.trans hunorm.le

/-- Helper for Proposition 7.3: the linear objective `u ↦ ⟪c, u⟫` attains its maximum on the
feasible box slice. -/
lemma homogeneousLinearProgramming_feasible_linear_objective_attains_max
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) :
    ∃ uStar ∈ homogeneousLinearProgrammingFeasibleSet hatA,
      ∀ u ∈ homogeneousLinearProgrammingFeasibleSet hatA, inner ℝ c u ≤ inner ℝ c uStar := by
  have hfeas_closed : IsClosed (homogeneousLinearProgrammingFeasibleSet hatA : Set Eₘ) := by
    have hEq_closed : IsClosed {u : Eₘ | hatA.transpose.toEuclideanLin u = (0 : Eₙ₋₁)} := by
      -- The equality slice is the preimage of the closed singleton `{0}` under a continuous map.
      simpa [Set.preimage] using
        IsClosed.preimage
          (LinearMap.continuous_of_finiteDimensional hatA.transpose.toEuclideanLin)
          isClosed_singleton
    simpa [homogeneousLinearProgrammingFeasibleSet, linearEqualityFeasibleSet] using
      (isClosed_coordinatewiseUnitBox (m := m)).inter hEq_closed
  have hfeas_subset :
      homogeneousLinearProgrammingFeasibleSet hatA ⊆ Metric.closedBall (0 : Eₘ) m := by
    intro u hu
    exact coordinatewiseUnitBox_subset_closedBall (m := m)
      ((mem_homogeneousLinearProgrammingFeasibleSet_iff hatA u).mp hu).2
  have hcompact : IsCompact (homogeneousLinearProgrammingFeasibleSet hatA : Set Eₘ) := by
    -- A closed subset of a compact closed ball is compact.
    exact (isCompact_closedBall (0 : Eₘ) m).of_isClosed_subset hfeas_closed hfeas_subset
  have hzero_feasible : (0 : Eₘ) ∈ homogeneousLinearProgrammingFeasibleSet hatA := by
    rw [mem_homogeneousLinearProgrammingFeasibleSet_iff]
    constructor
    · simp
    · simp [mem_coordinatewiseUnitBox_iff]
  have hcont : ContinuousOn (fun u : Eₘ ↦ inner ℝ c u)
      (homogeneousLinearProgrammingFeasibleSet hatA) := by
    simpa using (continuous_const.inner continuous_id).continuousOn
  -- Compactness gives an attained maximizer of the linear functional on the feasible set.
  obtain ⟨uStar, huStar, huMax⟩ :=
    hcompact.exists_isMaxOn ⟨0, hzero_feasible⟩ hcont
  exact ⟨uStar, huStar, huMax⟩

/-- Helper for Proposition 7.3: a maximizing feasible point realizes the supremal optimal value. -/
lemma homogeneousLinearProgrammingOptimalValue_eq_inner_of_maximizer
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) {uStar : Eₘ}
    (hu : uStar ∈ homogeneousLinearProgrammingFeasibleSet hatA)
    (huMax : ∀ u ∈ homogeneousLinearProgrammingFeasibleSet hatA,
      inner ℝ c u ≤ inner ℝ c uStar) :
    homogeneousLinearProgrammingOptimalValue hatA c = inner ℝ c uStar := by
  have hgreatest :
      IsGreatest
        ((fun u : Eₘ ↦ inner ℝ c u) '' homogeneousLinearProgrammingFeasibleSet hatA)
        (inner ℝ c uStar) := by
    refine ⟨?_, ?_⟩
    · exact ⟨uStar, hu, rfl⟩
    · rintro z ⟨u, huFeas, rfl⟩
      exact huMax u huFeas
  -- Replace the optimal value by the defining supremum and evaluate the attained maximum.
  rw [homogeneousLinearProgrammingOptimalValue_eq_sSup]
  exact hgreatest.csSup_eq

/-- Helper for Proposition 7.3: a negative normal-cone certificate on the coordinatewise unit box
forces the corresponding inner product to equal the box support value `∑ i |v i|`. -/
lemma inner_eq_sum_abs_of_neg_mem_normalCone_coordinatewiseUnitBox
    {u v : Eₘ} (hu : u ∈ coordinatewiseUnitBox m)
    (hn : -v ∈ N[coordinatewiseUnitBox m] u) :
    inner ℝ v u = ∑ i : Fin m, |v i| := by
  have hu_image :
      inner ℝ v u ∈ ((fun x : Eₘ ↦ inner ℝ v x) '' coordinatewiseUnitBox m) :=
    ⟨u, hu, rfl⟩
  have hmaxOn : ∀ x ∈ coordinatewiseUnitBox m, inner ℝ v x ≤ inner ℝ v u := by
    intro x hx
    have hpair : inner ℝ v (u - x) ≥ 0 := (neg_mem_normalCone_iff.mp hn) x hx
    have hrewrite : inner ℝ v (u - x) = inner ℝ v u - inner ℝ v x := by
      rw [inner_sub_right]
    linarith [hrewrite]
  have hsupport_le : ∑ i : Fin m, |v i| ≤ inner ℝ v u := by
    rcases (isGreatest_inner_image_coordinatewiseUnitBox (m := m) v).1 with ⟨xMax, hxMax, hxEq⟩
    have hxle : inner ℝ v xMax ≤ inner ℝ v u := hmaxOn xMax hxMax
    simpa [hxEq] using hxle
  -- Compare the normal-cone maximizer `u` with the already computed greatest support value.
  exact le_antisymm
    ((isGreatest_inner_image_coordinatewiseUnitBox (m := m) v).2 hu_image)
    hsupport_le

/-- Proposition 7.3: the box-constrained dual optimal value
`max {⟪c, u⟫ : \hat Aᵀ u = 0, |uᵢ| ≤ 1}` is the minimum value attained by the function
`y ↦ homogeneousLinearProgrammingPhi1 hatA c y`. -/
-- Proof sketch: use linear-programming duality for the primal problem
-- `max {⟪c, u⟫ : \hat Aᵀ u = 0, |uᵢ| ≤ 1}`. The Lagrangian introduces a free multiplier `y` for
-- `\hat Aᵀ u = 0` and nonnegative multipliers for the box constraints, and eliminating the latter
-- yields the dual objective `homogeneousLinearProgrammingPhi1 hatA c y`. Strong duality then
-- identifies the primal optimal value with the least element of the value set of `φ₁`.
theorem homogeneousLinearProgrammingOptimalValue_isLeast_phi1_values
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) :
    IsLeast (Set.range (homogeneousLinearProgrammingPhi1 hatA c))
      (homogeneousLinearProgrammingOptimalValue hatA c) := by
  let f : Eₘ → WithTop ℝ := fun u ↦ ((-inner ℝ c u : ℝ) : WithTop ℝ)
  obtain ⟨uStar, huStar, huMax⟩ :=
    homogeneousLinearProgramming_feasible_linear_objective_attains_max (hatA := hatA) c
  have hopt :
      homogeneousLinearProgrammingOptimalValue hatA c = inner ℝ c uStar :=
    homogeneousLinearProgrammingOptimalValue_eq_inner_of_maximizer
      (hatA := hatA) c huStar huMax
  have huBox : uStar ∈ coordinatewiseUnitBox m := by
    exact ((mem_homogeneousLinearProgrammingFeasibleSet_iff hatA uStar).mp huStar).2
  have hQ_closed : IsClosed (coordinatewiseUnitBox m : Set Eₘ) :=
    isClosed_coordinatewiseUnitBox (m := m)
  have hQ_convex : Convex ℝ (coordinatewiseUnitBox m : Set Eₘ) :=
    convex_coordinatewiseUnitBox (m := m)
  have hQ_bounded : Bornology.IsBounded (coordinatewiseUnitBox m : Set Eₘ) := by
    exact Bornology.IsBounded.subset Metric.isBounded_closedBall
      (coordinatewiseUnitBox_subset_closedBall (m := m))
  have hdom_univ : withTopEffectiveDomain f = Set.univ := by
    ext x
    simpa [withTopEffectiveDomain, f] using (WithTop.coe_lt_top (-inner ℝ c x))
  have hf : ConvexOn ℝ (withTopEffectiveDomain f) (withTopRealPart f) := by
    -- Route correction: treat the objective as the affine functional `u ↦ ⟪-c, u⟫`.
    rw [hdom_univ]
    simpa [f, withTopRealPart, Function.comp] using
      convexOn_const_add_inner_univ (n := m) 0 (-c)
  have hQ_subset_interior : coordinatewiseUnitBox m ⊆ interior (withTopEffectiveDomain f) := by
    rw [hdom_univ]
    simpa using (Set.subset_univ (coordinatewiseUnitBox m))
  have hlevel_bounded :
      ∀ α : ℝ, Bornology.IsBounded (constrainedSublevelSet (coordinatewiseUnitBox m) f α) := by
    intro α
    refine Bornology.IsBounded.subset hQ_bounded ?_
    intro x hx
    exact (mem_constrainedSublevelSet_iff.mp hx).1
  have hmin :
      IsMinOn (withTopRealPart f)
        (linearEqualityFeasibleSet (coordinatewiseUnitBox m) hatA.transpose.toEuclideanLin 0) uStar := by
    intro u hu
    -- Minimizing `u ↦ -⟪c, u⟫` is the same as maximizing `u ↦ ⟪c, u⟫`.
    simpa [f, withTopRealPart, Function.comp] using neg_le_neg (huMax u hu)
  have hkkt :=
    (isMinOn_linearEqualityFeasibleSet_iff_exists_subgradient_multiplier_with_bound
      (Q := coordinatewiseUnitBox m) (f := f)
      hQ_closed hQ_convex hf hQ_subset_interior hlevel_bounded
      (A := hatA.transpose.toEuclideanLin) (b := (0 : Eₙ₋₁))
      (xBar := (0 : Eₘ)) (ε := (1 : ℝ))
      (by simp) (by norm_num)
      (metricBall_subset_coordinatewiseUnitBox (m := m))
      (xStar := uStar)).mp hmin
  rcases hkkt with ⟨huStar', yStar, gStar, hgStar, hgNormal, _⟩
  have hgStar_mem : gStar ∈ ∂ f(uStar) := by
    simpa [mem_subdifferential_iff] using hgStar
  have hgEq : gStar = -c := by
    -- The subdifferential of the affine objective is the singleton containing its coefficient.
    have hsingleton : ∂ f(uStar) = ({-c} : Set Eₘ) := by
      simpa [f] using subdifferential_inner_eq_singleton_local (-c) uStar
    have hgSingleton : gStar ∈ ({-c} : Set Eₘ) := by
      simpa [hsingleton] using hgStar_mem
    simpa using hgSingleton
  have hadj_transpose :
      hatA.transpose.toEuclideanLin.adjoint = hatA.toEuclideanLin := by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint hatA.transpose).symm
  have hnormal :
      -(hatA.toEuclideanLin yStar + c) ∈ N[coordinatewiseUnitBox m] uStar := by
    -- Rewrite the KKT stationarity certificate into the box-normal-cone form used by the support
    -- maximizer bridge.
    simpa [hgEq, hadj_transpose, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hgNormal
  have hsum_value :
      inner ℝ (hatA.toEuclideanLin yStar + c) uStar =
        ∑ i : Fin m, |(hatA.toEuclideanLin yStar + c) i| :=
    inner_eq_sum_abs_of_neg_mem_normalCone_coordinatewiseUnitBox
      (m := m) huBox hnormal
  have hAuLin : hatA.transpose.toEuclideanLin uStar = 0 := by
    rcases (mem_homogeneousLinearProgrammingFeasibleSet_iff hatA uStar).mp huStar' with ⟨hAu, _⟩
    ext i
    have hi : (hatA.transpose.mulVec uStar) i = 0 := by
      simpa using congrArg (fun v ↦ v i) hAu
    simpa using hi
  have hAy_zero : inner ℝ (hatA.toEuclideanLin yStar) uStar = 0 := by
    have hadj : hatA.toEuclideanLin.adjoint = hatA.transpose.toEuclideanLin := by
      simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint hatA).symm
    -- Feasibility cancels the multiplier term through the adjoint identity.
    calc
      inner ℝ (hatA.toEuclideanLin yStar) uStar =
          inner ℝ yStar (hatA.toEuclideanLin.adjoint uStar) := by
            simpa using (LinearMap.adjoint_inner_right (hatA.toEuclideanLin) yStar uStar).symm
      _ = inner ℝ yStar (hatA.transpose.toEuclideanLin uStar) := by
        rw [hadj]
      _ = 0 := by
        simp [hAuLin]
  have hphi :
      homogeneousLinearProgrammingPhi1 hatA c yStar = inner ℝ c uStar := by
    -- Convert the box support value back to `φ₁(yStar)` and then remove the vanished multiplier
    -- term.
    calc
      homogeneousLinearProgrammingPhi1 hatA c yStar =
          ∑ i : Fin m, |(hatA.toEuclideanLin yStar + c) i| := by
            exact homogeneousLinearProgrammingPhi1_eq_sum_abs hatA c yStar
      _ = inner ℝ (hatA.toEuclideanLin yStar + c) uStar := by
        symm
        exact hsum_value
      _ = inner ℝ c uStar := by
        rw [inner_add_left, hAy_zero, zero_add]
  refine ⟨?_, ?_⟩
  · refine ⟨yStar, ?_⟩
    calc
      homogeneousLinearProgrammingPhi1 hatA c yStar = inner ℝ c uStar := hphi
      _ = homogeneousLinearProgrammingOptimalValue hatA c := hopt.symm
  · rintro z ⟨y, rfl⟩
    exact homogeneousLinearProgrammingOptimalValue_le_phi1 hatA c y

end
