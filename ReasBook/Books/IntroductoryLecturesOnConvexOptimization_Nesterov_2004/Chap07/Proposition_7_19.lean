/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_23
import Mathlib.Order.ConditionallyCompleteLattice.Finset

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SupportFunction

universe u v

variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 7.19 lies in Chapter 7's finite-range support-function / log-sum-exp smoothing
domain.

Sampled owner-style declarations:
- `ξ[Q]` and `supportFunction_apply` in `Chap03/Definition_3_9`, the chapter owner for support
  functions;
- `supportFunction_range_toReal_eq_sSup_inner` in `Chap07/Lemma_7_1`, the nearby finite-range
  evaluation theorem for `ξ[Set.range a]`;
- the Chapter 6 owner `η` and `eta_apply` in `Chap06/Proposition_6_23`, which provide the
  positive-parameter log-sum-exp surface used here;
- `HasDiagonalOrthantSupportBounds` in `Chap07/Proposition_7_21`, the direct downstream support-
  function surface for the same finite family `a`.

Best owner abstraction:
- source-facing: Proposition 7.19's smoothing bound for the support function of `Set.range a`;
- core/canonical: `ξ[Set.range a]` and `smoothMaxInnerApproximation a μ`;
- bridge/view: the finite-max evaluation
  `maxTypeObjective (fun i y ↦ inner ℝ (a i) y) x = (ξ[Set.range a] x).toReal`.

Primitive data:
- the finite nonempty index type `ι`;
- the vectors `a : ι → E`;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`.

Derived API:
- the canonical support-function owner `(ξ[Set.range a] x).toReal`;
- the canonical smoothing owner `smoothMaxInnerApproximation a μ`;
- the additive error term `(μ : ℝ) * Real.log (Fintype.card ι)`.

This refinement keeps Proposition 7.19 on the intrinsic Chapter 3 support-function owner instead
of the lower-level finite-max owner. The finite maximum remains only a bridge/view to this support
function surface, matching the surrounding Chapter 7 API in `Lemma_7_1` and `Proposition_7_21`.
-/

/-- Helper for Proposition 7.19: the file-local smoothing surface `x ↦ μ log (∑ i exp (⟪aᵢ, x⟫ / μ))`
implemented directly from the Chapter 6 owner `η`. -/
private def smoothMaxInnerApproximationLocal
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) : E → ℝ :=
  fun x ↦ η μ (WithLp.toLp 2 fun i ↦ inner ℝ (a i) x)

local notation "smoothMaxInnerApproximation" => smoothMaxInnerApproximationLocal

/-- Helper for Proposition 7.19: evaluating the local smoothing surface gives the textbook
log-sum-exp formula. -/
private theorem smoothMaxInnerApproximationLocal_apply
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    smoothMaxInnerApproximation a μ x =
      (μ : ℝ) * Real.log (∑ i : ι, Real.exp (inner ℝ (a i) x / (μ : ℝ))) := by
  -- Evaluate the Chapter 6 owner `η` on the score vector `i ↦ ⟪aᵢ, x⟫`.
  simpa [smoothMaxInnerApproximationLocal] using
    (eta_apply μ (WithLp.toLp 2 fun i ↦ inner ℝ (a i) x))

/-- Helper for Proposition 7.19: the support function of a finite range is the attained maximum
of the corresponding inner products. -/
lemma supportFunction_range_toReal_eq_sup_inner
    (a : ι → E) (x : E) :
    (ξ[Set.range a] x).toReal =
      Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦ inner ℝ (a i) x) := by
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦ inner ℝ (a i) x)
  have hupper : ξ[Set.range a] x ≤ (M : EReal) := by
    -- Every inner product from the finite family is bounded by the attained maximum `M`.
    rw [supportFunction_apply]
    refine sSup_le ?_
    rintro _ ⟨y, ⟨i, rfl⟩, rfl⟩
    exact show (((inner ℝ (a i) x : ℝ) : EReal) ≤ (M : EReal)) by
      exact_mod_cast
        (Finset.le_sup' (f := fun j : ι ↦ inner ℝ (a j) x) (Finset.mem_univ i))
  have hlower : (M : EReal) ≤ ξ[Set.range a] x := by
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j : ι ↦ inner ℝ (a j) x)
    rw [supportFunction_apply]
    have hi_mem :
        (((inner ℝ (a i) x : ℝ) : EReal)) ≤
          sSup ((fun g : E ↦ ((inner ℝ g x : ℝ) : EReal)) '' Set.range a) :=
      le_sSup ⟨a i, Set.mem_range_self i, rfl⟩
    have hM : (M : EReal) = (((inner ℝ (a i) x : ℝ) : EReal)) := by
      exact_mod_cast hi
    calc
      (M : EReal) = (((inner ℝ (a i) x : ℝ) : EReal)) := hM
      _ ≤ sSup ((fun g : E ↦ ((inner ℝ g x : ℝ) : EReal)) '' Set.range a) := hi_mem
  have hξ : ξ[Set.range a] x = (M : EReal) := le_antisymm hupper hlower
  -- Passing to `toReal` recovers the finite attained maximum.
  simpa [M] using congrArg EReal.toReal hξ

/-- Helper for Proposition 7.19: after reindexing the finite family along an equivalence
`e : ι ≃ Fin n`, the support function of `Set.range a` is the Chapter 6 maximal coordinate of the
same score vector. -/
lemma supportFunction_range_toReal_eq_coordinateMaximum_scores
    {n : ℕ} [NeZero n] (e : ι ≃ Fin n) (a : ι → E) (x : E) :
    (ξ[Set.range a] x).toReal =
      coordinateMaximum (WithLp.toLp 2 fun j : Fin n ↦ inner ℝ (a (e.symm j)) x) := by
  have hfamily_range :
      Set.range (fun j : Fin n ↦ a (e.symm j)) = Set.range a := by
    -- Reindexing along `e` preserves the finite family.
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact Set.mem_range_self _
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp⟩
  have hsupport :
      (ξ[Set.range a] x).toReal =
        sSup (Set.range fun j : Fin n ↦ inner ℝ (a (e.symm j)) x) := by
    have hscore_range :
        Set.range (fun j : Fin n ↦ inner ℝ (a (e.symm j)) x) =
          Set.range (fun i : ι ↦ inner ℝ (a i) x) := by
      -- Reindexing also preserves the finite set of scores.
      ext t
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e.symm j, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e i, by simp⟩
    have hsSup :
        (ξ[Set.range a] x).toReal =
          sSup (Set.range fun i : ι ↦ inner ℝ (a i) x) := by
      -- Convert the already-proved finite maximum formula to the corresponding `sSup` statement.
      calc
        (ξ[Set.range a] x).toReal =
            Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦ inner ℝ (a i) x) :=
          supportFunction_range_toReal_eq_sup_inner a x
        _ = sSup (Set.range fun i : ι ↦ inner ℝ (a i) x) := by
          simpa using
            (Finset.sup'_eq_csSup_image Finset.univ Finset.univ_nonempty
              (fun i : ι ↦ inner ℝ (a i) x))
    exact hsSup.trans <| by simp [hscore_range]
  have hcoordinate :
      coordinateMaximum (WithLp.toLp 2 fun j : Fin n ↦ inner ℝ (a (e.symm j)) x) =
        sSup (Set.range fun j : Fin n ↦ inner ℝ (a (e.symm j)) x) := by
    -- `coordinateMaximum` is the finite supremum of this same score vector.
    simpa [coordinateMaximum_def] using
      (Finset.sup'_eq_csSup_image Finset.univ Finset.univ_nonempty
        (fun j : Fin n ↦ inner ℝ (a (e.symm j)) x))
  exact hsupport.trans hcoordinate.symm

/-- Helper for Proposition 7.19: reindexing the finite family of inner-product scores along
`e : ι ≃ Fin n` turns the local smoothing surface into the Chapter 6 owner `η` on that same
reindexed score vector. -/
lemma smoothMaxInnerApproximation_eq_eta_reindexed_scores
    {n : ℕ} (e : ι ≃ Fin n) (a : ι → E) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    smoothMaxInnerApproximation a μ x =
      η μ (WithLp.toLp 2 fun j : Fin n ↦ inner ℝ (a (e.symm j)) x) := by
  have hsum :
      ∑ i : ι, Real.exp (inner ℝ (a i) x / (μ : ℝ)) =
        ∑ j : Fin n, Real.exp (inner ℝ (a (e.symm j)) x / (μ : ℝ)) := by
    -- Transport the finite exponential sum across the equivalence `e`.
    exact Fintype.sum_equiv e
      (fun i : ι ↦ Real.exp (inner ℝ (a i) x / (μ : ℝ)))
      (fun j : Fin n ↦ Real.exp (inner ℝ (a (e.symm j)) x / (μ : ℝ)))
      (fun i ↦ by simp)
  -- Once the sum is reindexed, both sides are the same `μ log` expression.
  rw [smoothMaxInnerApproximationLocal_apply, eta_apply]
  simpa using congrArg (fun t : ℝ ↦ (μ : ℝ) * Real.log t) hsum

/-- Helper for Proposition 7.19: the centered remainder in the Chapter 6 stable log-sum-exp
decomposition is nonnegative and bounded above by `μ log n`. -/
lemma eta_centeredByCoordinateMaximum_bounds
    {n : ℕ} [NeZero n] (μ : {μ : ℝ // 0 < μ}) (u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ η μ (centeredByCoordinateMaximum u) ∧
      η μ (centeredByCoordinateMaximum u) ≤ (μ : ℝ) * Real.log (n : ℝ) := by
  obtain ⟨jmax, -, hjmax⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j : Fin n ↦ u j)
  have hmu_nonneg : 0 ≤ (μ : ℝ) := le_of_lt μ.property
  have hzero : centeredByCoordinateMaximum u jmax = 0 := by
    -- At a maximizing coordinate, centering subtracts the coordinate from itself.
    rw [centeredByCoordinateMaximum_apply, coordinateMaximum_def, hjmax]
    simp
  have hcentered_nonpos (j : Fin n) : centeredByCoordinateMaximum u j ≤ 0 := by
    -- Every centered coordinate is the original coordinate minus an upper bound for that
    -- coordinate.
    rw [centeredByCoordinateMaximum_apply]
    exact sub_nonpos.mpr <|
      by simpa [coordinateMaximum_def] using
        (Finset.le_sup' (f := fun k : Fin n ↦ u k) (Finset.mem_univ j))
  have hsum_ge_one :
      1 ≤ ∑ j : Fin n, Real.exp (centeredByCoordinateMaximum u j / (μ : ℝ)) := by
    have hsingle :
        Real.exp (centeredByCoordinateMaximum u jmax / (μ : ℝ)) ≤
          ∑ j : Fin n, Real.exp (centeredByCoordinateMaximum u j / (μ : ℝ)) := by
      -- The maximizing coordinate contributes one full `exp 0 = 1` term to the sum.
      simpa using
        (Finset.single_le_sum
          (f := fun j : Fin n ↦ Real.exp (centeredByCoordinateMaximum u j / (μ : ℝ)))
          (fun j _ ↦ Real.exp_nonneg _)
          (Finset.mem_univ jmax))
    calc
      1 = Real.exp (centeredByCoordinateMaximum u jmax / (μ : ℝ)) := by
        rw [hzero]
        simp
      _ ≤ ∑ j : Fin n, Real.exp (centeredByCoordinateMaximum u j / (μ : ℝ)) := hsingle
  have hsum_le_card :
      ∑ j : Fin n, Real.exp (centeredByCoordinateMaximum u j / (μ : ℝ)) ≤ (n : ℝ) := by
    -- Each centered exponent is at most `exp 0 = 1`, so the whole sum is bounded by the number
    -- of coordinates.
    calc
      ∑ j : Fin n, Real.exp (centeredByCoordinateMaximum u j / (μ : ℝ)) ≤
          ∑ j : Fin n, (1 : ℝ) := by
        exact Finset.sum_le_sum fun j _ ↦ by
          have hdiv_nonpos :
              centeredByCoordinateMaximum u j / (μ : ℝ) ≤ 0 := by
            rw [div_eq_mul_inv]
            exact mul_nonpos_of_nonpos_of_nonneg (hcentered_nonpos j)
              (inv_nonneg.mpr hmu_nonneg)
          have hexp_le :
              Real.exp (centeredByCoordinateMaximum u j / (μ : ℝ)) ≤ Real.exp 0 := by
            exact Real.exp_le_exp.mpr hdiv_nonpos
          simpa using hexp_le
      _ = (n : ℝ) := by simp
  have hlower : 0 ≤ η μ (centeredByCoordinateMaximum u) := by
    -- A sum at least `1` has nonnegative logarithm, and `μ` is positive.
    rw [eta_apply]
    exact mul_nonneg hmu_nonneg (Real.log_nonneg hsum_ge_one)
  have hupper : η μ (centeredByCoordinateMaximum u) ≤ (μ : ℝ) * Real.log (n : ℝ) := by
    -- Monotonicity of `log` transfers the cardinality bound to the centered remainder.
    rw [eta_apply]
    have hsum_pos :
        0 < ∑ j : Fin n, Real.exp (centeredByCoordinateMaximum u j / (μ : ℝ)) := by
      positivity
    have hlog_le :
        Real.log (∑ j : Fin n, Real.exp (centeredByCoordinateMaximum u j / (μ : ℝ))) ≤
          Real.log (n : ℝ) := by
      exact Real.log_le_log hsum_pos hsum_le_card
    exact mul_le_mul_of_nonneg_left hlog_le hmu_nonneg
  exact ⟨hlower, hupper⟩

/-- Proposition 7.19: for a finite nonempty family `aᵢ` in a real inner product space, the
log-sum-exp smoothing of the support function of `Set.range a` lies between
`(ξ[Set.range a] x).toReal` and the same quantity plus `μ log (Fintype.card ι)` at every point
`x`, for every positive smoothing parameter `μ`. -/
-- Proof sketch: let `M = (ξ[Set.range a] x).toReal`, equivalently
-- `M = max_i ⟪aᵢ, x⟫`. Every summand `exp (⟪aᵢ, x⟫ / μ)` is at most `exp (M / μ)`, so the whole
-- sum is at most `Fintype.card ι * exp (M / μ)`, which gives the upper bound after applying
-- `μ * log`. Since the finite maximum is attained, one summand is exactly `exp (M / μ)`, so the
-- sum is at least that term, yielding the lower bound.
theorem supportFunction_range_toReal_smoothing_bounds
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    (ξ[Set.range a] x).toReal ≤ smoothMaxInnerApproximation a μ x ∧
      smoothMaxInnerApproximation a μ x ≤
        (ξ[Set.range a] x).toReal +
          (μ : ℝ) * Real.log (Fintype.card ι) := by
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  letI : NeZero n := ⟨by simpa [n] using (Fintype.card_ne_zero : Fintype.card ι ≠ 0)⟩
  let u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun j ↦ inner ℝ (a (e.symm j)) x
  have hsupport :
      (ξ[Set.range a] x).toReal = coordinateMaximum u := by
    -- Rewrite the support function and the Chapter 6 max-shift API on the same score vector.
    simpa [u] using
      (supportFunction_range_toReal_eq_coordinateMaximum_scores (e := e) a x)
  have hsmooth : smoothMaxInnerApproximation a μ x = η μ u := by
    -- The smoothing term is the same `η` owner on that reindexed score vector.
    simpa [u] using
      (smoothMaxInnerApproximation_eq_eta_reindexed_scores (e := e) a μ x)
  have hcentered :
      0 ≤ η μ (centeredByCoordinateMaximum u) ∧
        η μ (centeredByCoordinateMaximum u) ≤ (μ : ℝ) * Real.log (n : ℝ) :=
    eta_centeredByCoordinateMaximum_bounds μ u
  have hshift :
      η μ u = coordinateMaximum u + η μ (centeredByCoordinateMaximum u) :=
    eta_eq_coordinateMaximum_add_eta_centered μ u
  constructor
  · -- Route correction: instead of the raw `exp`-sandwich, use the stable max-shift identity and
    -- the nonnegativity of the centered remainder.
    rw [hsupport, hsmooth, hshift]
    exact le_add_of_nonneg_right hcentered.1
  · -- The upper bound is the same stable decomposition plus the cardinality bound on the centered
    -- remainder.
    rw [hsupport, hsmooth, hshift]
    simpa [n] using add_le_add_left hcentered.2 (coordinateMaximum u)

end
