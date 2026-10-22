/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.HausdorffDistance

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 3.12 is `source-facing`: it identifies the gradient of the half squared distance to
a nonempty closed convex set. The canonical `core/canonical` owner results in this domain are the
mathlib Hilbert projection theorems `exists_norm_eq_iInf_of_complete_convex` and
`norm_eq_iInf_iff_real_inner_le_zero`, together with the metric owner formula
`Metric.infDist_eq_iInf`. The only primitive data here are the set `C` together with its
nonempty/closed/convex hypotheses; the chosen metric projection and its basic properties are
derived `bridge/view` API built from those owner theorems. -/

/-- The metric projection onto a nonempty closed convex subset of a complete real inner product
space, valued in the set itself. -/
noncomputable def metricProjection [CompleteSpace E] (C : Set E) (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) : E → C :=
  fun x ↦
    let hp :=
      exists_norm_eq_iInf_of_complete_convex hC_nonempty hC_closed.isComplete hC_convex x
    ⟨Classical.choose hp, (Classical.choose_spec hp).1⟩

/-- The complete-subset bridge for the metric projection: when the minimizing set is known
complete and convex, one can choose its Hilbert projection without assuming the ambient space is
complete. Under `[CompleteSpace E]` and `IsClosed C`, compare `metricProjection`. -/
noncomputable def metricProjectionOfComplete (C : Set E) (hC_nonempty : C.Nonempty)
    (hC_complete : IsComplete C) (hC_convex : Convex ℝ C) : E → C :=
  fun x ↦
    let hp := exists_norm_eq_iInf_of_complete_convex hC_nonempty hC_complete hC_convex x
    ⟨Classical.choose hp, (Classical.choose_spec hp).1⟩

section ProjectionData

variable [CompleteSpace E]

/-- The ambient-space point projection `x ↦ P_C(x)` associated to the metric projection onto a
nonempty closed convex set. This is the canonical chapter-level point-valued bridge from
`metricProjection`. -/
noncomputable abbrev projectionPoint (C : Set E) (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) : E → E :=
  fun x ↦ (metricProjection C hC_nonempty hC_closed hC_convex x : E)

syntax:max "Pp[" term ", " term ", " term ", " term "]" : term

macro_rules
  | `(Pp[$C, $hC_nonempty, $hC_closed, $hC_convex]) =>
      `(projectionPoint $C $hC_nonempty $hC_closed $hC_convex)

end ProjectionData

section ProjectionOfComplete

variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_complete : IsComplete C)
    (hC_convex : Convex ℝ C)

local notation "P" => metricProjectionOfComplete C hC_nonempty hC_complete hC_convex

/-- The complete-subset metric projection realizes the minimum distance to the set. -/
theorem norm_sub_metricProjectionOfComplete_eq_iInf (x : E) :
    ‖x - (P x : E)‖ = ⨅ w : C, ‖x - w‖ := by
  -- Unfold the chosen minimizer and read off the minimizing equality from mathlib's existence
  -- theorem.
  simpa [metricProjectionOfComplete] using
    (Classical.choose_spec
      (exists_norm_eq_iInf_of_complete_convex hC_nonempty hC_complete hC_convex x)).2

/-- The complete-subset metric projection satisfies the Hilbert-space variational inequality. -/
theorem inner_sub_metricProjectionOfComplete_le_zero (x w : E) (hw : w ∈ C) :
    inner ℝ (x - (P x : E)) (w - (P x : E)) ≤ 0 := by
  -- Convert the minimizing property into the standard real-inner-product optimality condition.
  exact
    (norm_eq_iInf_iff_real_inner_le_zero hC_convex (P x).property).mp
      (norm_sub_metricProjectionOfComplete_eq_iInf C hC_nonempty hC_complete hC_convex x)
      w hw

/-- The distance from `x` to a nonempty complete convex set is realized by the complete-subset
metric projection. -/
theorem infDist_eq_dist_metricProjectionOfComplete (x : E) :
    infDist x C = dist x (P x) := by
  -- Rewrite the infimum formula for `infDist` using the minimizing point selected above.
  rw [Metric.infDist_eq_iInf, dist_eq_norm]
  simpa [dist_eq_norm] using
    (norm_sub_metricProjectionOfComplete_eq_iInf C hC_nonempty hC_complete hC_convex x).symm

/-- On a nonempty closed convex set in a complete ambient space, the closed-set owner
`metricProjection` agrees with the complete-subset bridge `metricProjectionOfComplete`. -/
theorem metricProjection_eq_metricProjectionOfComplete [CompleteSpace E]
    (hC_closed : IsClosed C) (x : E) :
    metricProjection C hC_nonempty hC_closed hC_convex x =
      metricProjectionOfComplete C hC_nonempty hC_complete hC_convex x := by
  let p : C := metricProjection C hC_nonempty hC_closed hC_convex x
  let q : C := metricProjectionOfComplete C hC_nonempty hC_complete hC_convex x
  have hp_eq_iInf : ‖x - (p : E)‖ = ⨅ w : C, ‖x - w‖ := by
    -- The closed-set projection is defined from the same minimizing existence theorem.
    simpa [metricProjection, p] using
      (Classical.choose_spec
        (exists_norm_eq_iInf_of_complete_convex hC_nonempty hC_closed.isComplete hC_convex x)).2
  have hp_nonneg : 0 ≤ inner ℝ (x - (p : E)) ((p : E) - (q : E)) := by
    have hp_le :
        inner ℝ (x - (p : E)) ((q : E) - (p : E)) ≤ 0 :=
      (norm_eq_iInf_iff_real_inner_le_zero hC_convex p.property).mp hp_eq_iInf (q : E) q.property
    have hqp : ((q : E) - (p : E)) = -((p : E) - (q : E)) := by
      abel_nf
    rw [hqp, inner_neg_right] at hp_le
    linarith
  have hq_le : inner ℝ (x - (q : E)) ((p : E) - (q : E)) ≤ 0 := by
    simpa [q] using
      inner_sub_metricProjectionOfComplete_le_zero
        C hC_nonempty hC_complete hC_convex x (p : E) p.property
  have hsq : ‖(p : E) - (q : E)‖ ^ (2 : ℕ) ≤ 0 := by
    -- Compare the two optimality inequalities to force the residual between the projections to
    -- vanish.
    have hq_expanded :
        inner ℝ (x - (p : E)) ((p : E) - (q : E)) + ‖(p : E) - (q : E)‖ ^ (2 : ℕ) ≤ 0 := by
      have hxq : x - (q : E) = (x - (p : E)) + ((p : E) - (q : E)) := by
        abel
      rw [hxq, inner_add_left, real_inner_self_eq_norm_sq] at hq_le
      exact hq_le
    nlinarith
  have hpq : (p : E) = (q : E) := by
    have hnorm : ‖(p : E) - (q : E)‖ = 0 := by
      nlinarith [hsq, norm_nonneg ((p : E) - (q : E))]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  -- Equality in the ambient space gives equality in the subtype.
  exact Subtype.ext hpq

/-- The point-valued closed-set projection agrees with the complete-subset bridge after coercing to
the ambient space. -/
theorem projectionPoint_eq_metricProjectionOfComplete [CompleteSpace E]
    (hC_closed : IsClosed C) (x : E) :
    Pp[C, hC_nonempty, hC_closed, hC_convex] x =
      (metricProjectionOfComplete C hC_nonempty hC_complete hC_convex x : E) := by
  simpa [projectionPoint] using
    congrArg (fun z : C ↦ (z : E))
      (metricProjection_eq_metricProjectionOfComplete
        C hC_nonempty hC_complete hC_convex hC_closed x)

end ProjectionOfComplete

section Projection

variable [CompleteSpace E]
variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C)

local notation "P" => projectionPoint C hC_nonempty hC_closed hC_convex

-- Proof sketch: unfold `metricProjection` as the chosen witness from
-- `exists_norm_eq_iInf_of_complete_convex`; the chosen point satisfies the defining minimization
-- property.
/-- The metric projection realizes the minimum distance to the set. -/
theorem norm_sub_metricProjection_eq_iInf (x : E) :
    ‖x - P x‖ = ⨅ w : C, ‖x - w‖ := by
  -- Rewrite the closed-set projection through the complete-subset bridge.
  rw [projectionPoint_eq_metricProjectionOfComplete
      C hC_nonempty hC_closed.isComplete hC_convex hC_closed x]
  exact norm_sub_metricProjectionOfComplete_eq_iInf
    C hC_nonempty hC_closed.isComplete hC_convex x

-- Proof sketch: combine the minimizing property of `P_C x` from
-- `norm_sub_metricProjection_eq_iInf` with mathlib's Hilbert-space characterization
-- `norm_eq_iInf_iff_real_inner_le_zero`.
/-- The metric projection satisfies the Hilbert-space variational inequality. -/
theorem inner_sub_metricProjection_le_zero (x w : E) (hw : w ∈ C) :
    inner ℝ (x - P x) (w - P x) ≤ 0 := by
  -- The closed-set projection inherits the complete-subset optimality inequality by rewriting.
  rw [projectionPoint_eq_metricProjectionOfComplete
      C hC_nonempty hC_closed.isComplete hC_convex hC_closed x]
  exact inner_sub_metricProjectionOfComplete_le_zero
    C hC_nonempty hC_closed.isComplete hC_convex x w hw

-- Proof sketch: rewrite `Metric.infDist` as the infimum of `dist x y` over `y ∈ C`, then apply
-- `norm_sub_metricProjection_eq_iInf` and `dist_eq_norm`.
/-- The distance from `x` to a nonempty closed convex set is realized by the metric projection. -/
theorem infDist_eq_dist_metricProjection (x : E) :
    infDist x C = dist x (P x) := by
  -- The closed-set distance formula is the complete-subset formula after rewriting the chosen
  -- point.
  rw [projectionPoint_eq_metricProjectionOfComplete
      C hC_nonempty hC_closed.isComplete hC_convex hC_closed x]
  exact infDist_eq_dist_metricProjectionOfComplete
    C hC_nonempty hC_closed.isComplete hC_convex x

-- Proof sketch: let `p = metricProjection C hC_nonempty hC_closed hC_convex x`. Use the
-- minimizing property of `p` together with convexity of `C` to get the first-order optimality
-- condition from `norm_eq_iInf_iff_real_inner_le_zero`. Rewrite
-- `y ↦ (Metric.infDist y C)^2 / 2` near `x` through the projection inequality, compare it with the
-- affine approximation `d ↦ ⟪x - p, d⟫ + (Metric.infDist x C)^2 / 2`, and conclude via
-- `hasGradientAt_iff_isLittleO`.
section Gradient

variable [FiniteDimensional ℝ E]

/-- Helper for Proposition 3.12: the first-order remainder of
`y ↦ (Metric.infDist y C)^2 / 2` at `x` is bounded above and below by quadratic terms in the
increment. -/
theorem halfSqInfDistRemainderBound (x h : E) :
    let p := P x
    let r := (infDist (x + h) C) ^ (2 : ℕ) / 2 - (infDist x C) ^ (2 : ℕ) / 2 -
      inner ℝ (x - p) h
    0 ≤ r ∧ r ≤ ‖h‖ ^ (2 : ℕ) / 2 := by
  let p := P x
  let p' := P (x + h)
  let a : E := x - p
  let d : E := p' - p
  let r : ℝ := (infDist (x + h) C) ^ (2 : ℕ) / 2 - (infDist x C) ^ (2 : ℕ) / 2 -
    inner ℝ (x - p) h
  have hp : p ∈ C := by
    simpa [p, projectionPoint] using
      (metricProjection C hC_nonempty hC_closed hC_convex x).property
  have hp' : p' ∈ C := by
    simpa [p', projectionPoint] using
      (metricProjection C hC_nonempty hC_closed hC_convex (x + h)).property
  have hA : inner ℝ a d ≤ 0 := by
    -- The optimality condition at `x` controls the projection displacement `d`.
    simpa [a, d, p] using
      inner_sub_metricProjection_le_zero C hC_nonempty hC_closed hC_convex x p' hp'
  have hB : ‖d‖ ^ (2 : ℕ) ≤ inner ℝ (a + h) d := by
    -- The optimality condition at `x + h` gives the complementary inequality.
    have hvar :
        inner ℝ ((x + h) - p') (p - p') ≤ 0 := by
      simpa [p] using
        inner_sub_metricProjection_le_zero C hC_nonempty hC_closed hC_convex (x + h) p hp
    have hnonneg : 0 ≤ inner ℝ (a + h - d) d := by
      have hx : (x + h) - p' = a + h - d := by
        dsimp [a, d]
        abel_nf
      have hpq : p - p' = -d := by
        dsimp [d]
        abel_nf
      rw [hx, hpq, inner_neg_right] at hvar
      linarith
    have hexpanded : 0 ≤ inner ℝ (a + h) d - ‖d‖ ^ (2 : ℕ) := by
      simpa [inner_sub_left, inner_add_left, real_inner_self_eq_norm_sq] using hnonneg
    nlinarith
  have hInfx : infDist x C = ‖a‖ := by
    simpa [a, p, dist_eq_norm] using
      infDist_eq_dist_metricProjection C hC_nonempty hC_closed hC_convex x
  have hInfxh : infDist (x + h) C = ‖a + h - d‖ := by
    rw [infDist_eq_dist_metricProjection C hC_nonempty hC_closed hC_convex (x + h), dist_eq_norm]
    have hx : (x + h) - p' = a + h - d := by
      dsimp [a, d]
      abel_nf
    rw [hx]
  have hrLower : r = -inner ℝ a d + ‖h - d‖ ^ (2 : ℕ) / 2 := by
    -- Normalize the remainder to expose the coercive square term.
    dsimp [r]
    simp [a]
    rw [hInfxh, hInfx]
    have hadd : a + h - d = a + (h - d) := by
      abel_nf
    rw [hadd]
    have hsq :
        ‖a + (h - d)‖ ^ (2 : ℕ) =
          ‖a‖ ^ (2 : ℕ) + 2 * inner ℝ a h - 2 * inner ℝ a d + ‖h - d‖ ^ (2 : ℕ) := by
      calc
        ‖a + (h - d)‖ ^ (2 : ℕ) =
            ‖a‖ ^ (2 : ℕ) + 2 * inner ℝ a (h - d) + ‖h - d‖ ^ (2 : ℕ) := by
              simpa [pow_two, two_mul] using norm_add_sq_real a (h - d)
        _ = ‖a‖ ^ (2 : ℕ) + 2 * inner ℝ a h - 2 * inner ℝ a d + ‖h - d‖ ^ (2 : ℕ) := by
              rw [inner_sub_right]
              ring
    nlinarith
  have hrUpper : r = ‖h‖ ^ (2 : ℕ) / 2 - inner ℝ (a + h) d + ‖d‖ ^ (2 : ℕ) / 2 := by
    -- A second normalization isolates the term controlled by the second variational inequality.
    dsimp [r]
    simp [a]
    rw [hInfxh, hInfx]
    have hsq₁ :
        ‖a + h - d‖ ^ (2 : ℕ) =
          ‖a + h‖ ^ (2 : ℕ) - 2 * inner ℝ (a + h) d + ‖d‖ ^ (2 : ℕ) := by
      simpa [pow_two] using norm_sub_sq_real (a + h) d
    have hsq₂ :
        ‖a + h‖ ^ (2 : ℕ) =
          ‖a‖ ^ (2 : ℕ) + 2 * inner ℝ a h + ‖h‖ ^ (2 : ℕ) := by
      simpa [pow_two, two_mul] using norm_add_sq_real a h
    nlinarith
  -- The two normal forms turn the variational inequalities into the quadratic remainder bound.
  have hlower : 0 ≤ r := by
    nlinarith [hrLower, hA, sq_nonneg ‖h - d‖]
  have hupper : r ≤ ‖h‖ ^ (2 : ℕ) / 2 := by
    nlinarith [hrUpper, hB, sq_nonneg ‖d‖]
  simpa [p, r] using And.intro hlower hupper

/-- Proposition 3.12: for a nonempty closed convex set `C` in a Euclidean space, the function
`x ↦ (Metric.infDist x C)^2 / 2` has gradient `x - P_C(x)` at `x`, where `P_C` is the metric
projection onto `C`. -/
theorem hasGradientAt_half_sq_infDist (x : E) :
    HasGradientAt (fun y ↦ (infDist y C) ^ 2 / 2) (x - P x) x := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  let r : E → ℝ := fun h ↦
    (infDist (x + h) C) ^ (2 : ℕ) / 2 - (infDist x C) ^ (2 : ℕ) / 2 - inner ℝ (x - P x) h
  have hr_abs : ∀ h, |r h| ≤ ‖h‖ ^ (2 : ℕ) / 2 := by
    intro h
    have hrem := halfSqInfDistRemainderBound C hC_nonempty hC_closed hC_convex x h
    have hr_nonneg : 0 ≤ r h := by
      simpa [r] using hrem.1
    rw [abs_of_nonneg hr_nonneg]
    simpa [r] using hrem.2
  have hbig : r =O[nhds (0 : E)] fun h ↦ ‖h‖ ^ (2 : ℕ) := by
    -- The remainder is uniformly bounded by a quadratic norm term.
    refine Asymptotics.IsBigO.of_bound (1 / 2 : ℝ) (Filter.Eventually.of_forall ?_)
    intro h
    simpa [r, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg h) _), div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using hr_abs h
  have hsmallPow : (fun h : E ↦ ‖h‖ ^ (2 : ℕ)) =o[nhds (0 : E)] fun h ↦ h := by
    simpa using (Asymptotics.isLittleO_norm_pow_id (E' := E) (n := 2) (by norm_num))
  -- Compose the quadratic bound with the standard `‖h‖² = o(‖h‖)` fact.
  simpa [r] using (hbig.trans_isLittleO hsmallPow)

-- Proof sketch: apply `HasGradientAt.gradient` to `hasGradientAt_half_sq_infDist`.
/-- The totalized gradient of `x ↦ (Metric.infDist x C)^2 / 2` agrees with `x - P_C(x)` at points
where Proposition 3.12 provides differentiability. -/
theorem gradient_half_sq_infDist_eq_sub_metricProjection (x : E) :
    gradient (fun y ↦ (infDist y C) ^ 2 / 2) x = x - P x := by
  -- Once the gradient witness is known, the totalized gradient agrees with it.
  exact (hasGradientAt_half_sq_infDist C hC_nonempty hC_closed hC_convex x).gradient

end Gradient

end Projection

section PointProjectionFacts

variable [CompleteSpace E]
variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C)

local notation "P" => projectionPoint C hC_nonempty hC_closed hC_convex

-- Proof sketch: `projectionPoint` is the ambient-space coercion of `metricProjection`, whose
-- values lie in `C` by construction.
/-- The point projection onto a nonempty closed convex set belongs to that set. -/
theorem projectionPoint_mem (x : E) :
    Pp[C, hC_nonempty, hC_closed, hC_convex] x ∈ C := by
  -- `projectionPoint` is just the ambient coercion of the subtype-valued metric projection.
  simpa [projectionPoint] using
    (metricProjection C hC_nonempty hC_closed hC_convex x).property

-- Proof sketch: apply `inner_sub_metricProjection_le_zero` at the feasible point `y` and the test
-- point `w = y`; the resulting inequality is `‖y - P_C(y)‖² ≤ 0`, so the residual must vanish.
/-- Points of a nonempty closed convex set are fixed by its point projection. -/
theorem projectionPoint_eq_self_of_mem {y : E} (hy : y ∈ C) :
    Pp[C, hC_nonempty, hC_closed, hC_convex] y = y := by
  have hsq : ‖y - P y‖ ^ (2 : ℕ) ≤ 0 := by
    -- The variational inequality at a feasible point collapses to the squared residual.
    simpa [real_inner_self_eq_norm_sq] using
      inner_sub_metricProjection_le_zero C hC_nonempty hC_closed hC_convex y y hy
  have hnorm : ‖y - P y‖ = 0 := by
    nlinarith [hsq, norm_nonneg (y - P y)]
  have hsub : y - P y = 0 := norm_eq_zero.mp hnorm
  exact (sub_eq_zero.mp hsub).symm

/-- As a subtype-valued owner statement, the metric projection fixes feasible points exactly. -/
theorem metricProjection_eq_self_of_mem {y : E} (hy : y ∈ C) :
    metricProjection C hC_nonempty hC_closed hC_convex y = ⟨y, hy⟩ := by
  apply Subtype.ext
  simpa [projectionPoint] using
    projectionPoint_eq_self_of_mem C hC_nonempty hC_closed hC_convex hy

-- Proof sketch: the norm-minimizing property of `metricProjection` immediately yields the
-- pointwise comparison `‖P_C(x) - x‖ ≤ ‖y - x‖` for every `y ∈ C`; monotonicity of squaring on
-- nonnegative reals then gives the half squared-distance minimizer formulation.
/-- The point projection onto a nonempty closed convex set minimizes the half squared-distance
objective over that set. -/
theorem projectionPoint_isMinOn (x : E) :
    IsMinOn (fun y ↦ ‖y - x‖ ^ (2 : ℕ) / 2) C
      (Pp[C, hC_nonempty, hC_closed, hC_convex] x) := by
  rw [isMinOn_iff]
  intro y hy
  -- Compare the chosen projection distance with the distance to an arbitrary feasible point.
  have hdist : dist x (P x) ≤ dist x y := by
    rw [← infDist_eq_dist_metricProjection C hC_nonempty hC_closed hC_convex x]
    exact Metric.infDist_le_dist_of_mem hy
  have hnorm : ‖P x - x‖ ≤ ‖y - x‖ := by
    simpa [dist_eq_norm, dist_comm, norm_sub_rev] using hdist
  have hsq : ‖P x - x‖ ^ (2 : ℕ) ≤ ‖y - x‖ ^ (2 : ℕ) := by
    nlinarith [hnorm, norm_nonneg (P x - x), norm_nonneg (y - x)]
  nlinarith [hsq]

-- Proof sketch: the owner minimizer theorem gives one minimizing point, so any other feasible
-- minimizer has the same half squared-distance value. Since norms are nonnegative, equal squared
-- distances imply equal distances; uniqueness of the metric projection then identifies the point.
/-- Any feasible minimizer of the half squared-distance objective over a nonempty closed convex set
is the point projection onto that set. -/
theorem eq_projectionPoint_of_mem_isMinOn (x : E) {y : E} (hy : y ∈ C)
    (hmin : IsMinOn (fun z ↦ ‖z - x‖ ^ (2 : ℕ) / 2) C y) :
    y = Pp[C, hC_nonempty, hC_closed, hC_convex] x := by
  rw [isMinOn_iff] at hmin
  have hp : P x ∈ C := projectionPoint_mem C hC_nonempty hC_closed hC_convex x
  have hy_le : ‖y - x‖ ^ (2 : ℕ) / 2 ≤ ‖P x - x‖ ^ (2 : ℕ) / 2 := hmin (P x) hp
  have hp_le : ‖P x - x‖ ^ (2 : ℕ) / 2 ≤ ‖y - x‖ ^ (2 : ℕ) / 2 :=
    (isMinOn_iff.mp <|
      projectionPoint_isMinOn C hC_nonempty hC_closed hC_convex x) y hy
  have hnorm_eq : ‖x - y‖ = ‖x - P x‖ := by
    have hsq_eq : ‖y - x‖ ^ (2 : ℕ) = ‖P x - x‖ ^ (2 : ℕ) := by
      nlinarith [hy_le, hp_le]
    have hnorm_eq' : ‖y - x‖ = ‖P x - x‖ := by
      nlinarith [hsq_eq, norm_nonneg (y - x), norm_nonneg (P x - x)]
    simpa [norm_sub_rev] using hnorm_eq'
  have hy_eq_iInf : ‖x - y‖ = ⨅ w : C, ‖x - w‖ := by
    calc
      ‖x - y‖ = ‖x - P x‖ := hnorm_eq
      _ = ⨅ w : C, ‖x - w‖ := norm_sub_metricProjection_eq_iInf C hC_nonempty hC_closed hC_convex x
  have hy_nonneg : 0 ≤ inner ℝ (x - y) (y - P x) := by
    have hy_opt :
        inner ℝ (x - y) (P x - y) ≤ 0 :=
      (norm_eq_iInf_iff_real_inner_le_zero hC_convex hy).mp hy_eq_iInf (P x) hp
    have hpy : P x - y = -(y - P x) := by
      abel_nf
    rw [hpy, inner_neg_right] at hy_opt
    linarith
  have hp_opt : inner ℝ (x - P x) (y - P x) ≤ 0 := by
    simpa using inner_sub_metricProjection_le_zero C hC_nonempty hC_closed hC_convex x y hy
  have hsq : ‖y - P x‖ ^ (2 : ℕ) ≤ 0 := by
    -- The two optimality conditions force the residual `y - P_C(x)` to vanish.
    have hp_expanded :
        inner ℝ (x - y) (y - P x) + ‖y - P x‖ ^ (2 : ℕ) ≤ 0 := by
      have hxy : x - P x = (x - y) + (y - P x) := by
        abel
      rw [hxy, inner_add_left, real_inner_self_eq_norm_sq] at hp_opt
      exact hp_opt
    nlinarith
  have hnorm : ‖y - P x‖ = 0 := by
    nlinarith [hsq, norm_nonneg (y - P x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end PointProjectionFacts

end
