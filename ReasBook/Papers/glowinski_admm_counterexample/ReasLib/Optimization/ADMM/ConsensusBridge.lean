module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UniformConvergence
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycleTrajectory
public import Mathlib.Analysis.Convex.Caratheodory

@[expose] public section

open Filter

namespace ConsensusADMM

namespace CoordinateBridge

variable {d : ℕ}

/-- A Euclidean consensus problem represented in the coordinate convention used
by the general two-block convergence theorem. -/
noncomputable def problem (f g : EuclideanSpace ℝ (Fin d) → EReal) :
    ADMM.Problem d d d where
  f x := f (WithLp.toLp 2 x)
  g y := g (WithLp.toLp 2 y)
  A := 1
  B := -1
  b := 0

lemma inner_eq_dot (x y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ x y = dotProduct x.ofLp y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  exact dotProduct_comm _ _

lemma firstObjective (f g : EuclideanSpace ℝ (Fin d) → EReal)
    (v y x : EuclideanSpace ℝ (Fin d)) :
    (problem f g).firstBlockObjective 1 v.ofLp y.ofLp x.ofLp =
      f x + ((inner ℝ v (x - y) + ‖x - y‖ ^ 2 / 2 : ℝ) : EReal) := by
  simp only [ADMM.Problem.firstBlockObjective, problem, Matrix.one_mulVec,
    Matrix.neg_mulVec, sub_zero, ← sub_eq_add_neg, ← WithLp.ofLp_sub,
    WithLp.toLp_ofLp, ← inner_eq_dot, real_inner_self_eq_norm_sq]
  rw [EReal.coe_add, ← add_assoc]
  congr 2
  ring

lemma secondObjective (f g : EuclideanSpace ℝ (Fin d) → EReal)
    (v x y : EuclideanSpace ℝ (Fin d)) :
    (problem f g).secondBlockObjective 1 v.ofLp x.ofLp y.ofLp =
      g y + ((inner ℝ v (x - y) + ‖x - y‖ ^ 2 / 2 : ℝ) : EReal) := by
  simp only [ADMM.Problem.secondBlockObjective, problem, Matrix.one_mulVec,
    Matrix.neg_mulVec, sub_zero, ← sub_eq_add_neg, ← WithLp.ofLp_sub,
    WithLp.toLp_ofLp, ← inner_eq_dot, real_inner_self_eq_norm_sq]
  rw [EReal.coe_add, ← add_assoc]
  congr 2
  ring

/-- Coordinate transport preserves both finite block minima and the multiplier
recurrence. The objectives are allowed to take positive infinity. -/
noncomputable def trajectory {γ : ℝ}
    {f g : EuclideanSpace ℝ (Fin d) → EReal}
    {x y v : ℕ → EuclideanSpace ℝ (Fin d)}
    (hf : ∀ z, f z ≠ ⊥) (hg : ∀ z, g z ≠ ⊥)
    (hz : IsTrajectory γ f g x y v) : ADMM.Trajectory (problem f g) 1 γ where
  x k := (x k).ofLp
  y k := (y k).ofLp
  multiplier k := (v k).ofLp
  firstMinimizes k := by
    refine ⟨(f (x (k + 1))).toReal + inner ℝ (v k) (x (k + 1) - y k) +
      ‖x (k + 1) - y k‖ ^ 2 / 2, ?_, ?_⟩
    · simp only [firstObjective, EReal.coe_add,
        EReal.coe_toReal (hz k).2.2.1 (hf _), add_assoc]
    · intro z
      rw [firstObjective]
      rw [← WithLp.ofLp_toLp 2 z, firstObjective]
      exact (hz k).1 _
  secondMinimizes k := by
    refine ⟨(g (y (k + 1))).toReal + inner ℝ (v k) (x (k + 1) - y (k + 1)) +
      ‖x (k + 1) - y (k + 1)‖ ^ 2 / 2, ?_, ?_⟩
    · simp only [secondObjective, EReal.coe_add,
        EReal.coe_toReal (hz k).2.2.2.1 (hg _), add_assoc]
    · intro z
      rw [secondObjective]
      rw [← WithLp.ofLp_toLp 2 z, secondObjective]
      exact (hz k).2.1 _
  multiplierStep k := by
    have h := congrArg WithLp.ofLp (hz k).2.2.2.2
    simpa [problem, Matrix.neg_mulVec, sub_eq_add_neg] using h

/-- A closed convex set containing zero has a closed proper convex indicator
after changing from Euclidean vectors to coordinate functions. -/
lemma indicator_closedProperConvex {X : Set (EuclideanSpace ℝ (Fin d))}
    (hclosed : IsClosed X) (hconvex : Convex ℝ X) (hzero : 0 ∈ X) :
    ADMM.IsClosedProperConvex (fun x : Fin d → ℝ ↦ extendedIndicator X (WithLp.toLp 2 x)) := by
  have hepi : {p : (Fin d → ℝ) × ℝ |
      extendedIndicator X (WithLp.toLp 2 p.1) ≤ (p.2 : EReal)} =
      {p | WithLp.toLp 2 p.1 ∈ X ∧ 0 ≤ p.2} := by
    ext p
    by_cases hp : WithLp.toLp 2 p.1 ∈ X
    · simp [extendedIndicator_of_mem hp, hp]
    · simp [extendedIndicator_of_not_mem hp, hp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hepi]
    intro a ha b hb s t hs ht hst
    constructor
    · exact hconvex ha.1 hb.1 hs ht hst
    · change 0 ≤ s * a.2 + t * b.2
      exact add_nonneg (mul_nonneg hs ha.2) (mul_nonneg ht hb.2)
  · rw [hepi]
    exact (hclosed.preimage ((PiLp.continuous_toLp 2 _).comp continuous_fst)).inter
      (isClosed_le continuous_const continuous_snd)
  · intro x
    by_cases hx : WithLp.toLp 2 x ∈ X
    · simp [extendedIndicator_of_mem hx]
    · simp [extendedIndicator_of_not_mem hx]
  · refine ⟨0, ?_⟩
    simp [extendedIndicator_of_mem hzero]

lemma indicator_kkt {X Y : Set (EuclideanSpace ℝ (Fin d))}
    (hX : 0 ∈ X) (hY : 0 ∈ Y) :
    (problem (extendedIndicator X) (extendedIndicator Y)).IsKKT 0 0 0 := by
  have stationary (Z : Set (EuclideanSpace ℝ (Fin d))) (hZ : 0 ∈ Z) :
      ADMM.IsSubgradientAt (fun x : Fin d → ℝ ↦ extendedIndicator Z (WithLp.toLp 2 x)) 0 0 := by
    refine ⟨0, ?_, ?_⟩
    · simpa using extendedIndicator_of_mem hZ
    · intro z
      by_cases hz : WithLp.toLp 2 z ∈ Z
      · simp [extendedIndicator_of_mem hZ, extendedIndicator_of_mem hz]
      · simp [extendedIndicator_of_mem hZ, extendedIndicator_of_not_mem hz]
  constructor
  · simpa [problem] using stationary X hX
  · simpa [problem] using stationary Y hY
  · simp [problem]

end CoordinateBridge

/-- A nonconstant Euclidean projection cycle contradicts the residual conclusion
of uniform convergence, using the consensus matrices `I` and `-I`. -/
theorem IsProjectionCycle.not_uniformConvergenceAt {N d : ℕ}
    (γ : ℝ) (η ν : ZMod N → EuclideanSpace ℝ (Fin d))
    (hN : 2 ≤ N) (hγ : 0 < γ) (hcycle : IsProjectionCycle γ η ν)
    (hnonzero : ∃ i, ProjectionCycle.residual γ ν i ≠ 0) :
    ¬ ADMM.UniformConvergenceAt γ := by
  classical
  letI : NeZero N := ⟨by omega⟩
  let X := ProjectionCycle.xSet γ η ν
  let Y := ProjectionCycle.ySet η
  have hX0 : 0 ∈ X := subset_convexHull ℝ _ (Set.mem_insert 0 _)
  have hY0 : 0 ∈ Y := subset_convexHull ℝ _ (Set.mem_insert 0 _)
  have hXC : IsClosed X :=
    ((Set.finite_range (ProjectionCycle.xVertex γ η ν)).insert 0).isCompact_convexHull ℝ |>.isClosed
  have hYC : IsClosed Y :=
    ((Set.finite_range η).insert 0).isCompact_convexHull ℝ |>.isClosed
  have hf := CoordinateBridge.indicator_closedProperConvex hXC (convex_convexHull ℝ _) hX0
  have hg := CoordinateBridge.indicator_closedProperConvex hYC (convex_convexHull ℝ _) hY0
  have hfbot (z) : extendedIndicator X z ≠ ⊥ := by
    simpa using hf.ne_bot z.ofLp
  have hgbot (z) : extendedIndicator Y z ≠ ⊥ := by
    simpa using hg.ne_bot z.ofLp
  let z := CoordinateBridge.trajectory hfbot hgbot (hcycle.isTrajectory γ η ν hN hγ)
  intro uniform
  have hconv := (uniform d d d (CoordinateBridge.problem (extendedIndicator X)
    (extendedIndicator Y)) hf hg ⟨0, 0, 0, CoordinateBridge.indicator_kkt hX0 hY0⟩
    1 zero_lt_one z).1.1
  have hpost := hconv.comp (tendsto_add_atTop_nat 1)
  have hEuclidean := (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).tendsto 0 |>.comp hpost
  apply hcycle.residual_not_tendsto γ η ν hN hγ hnonzero
  have heq : ProjectionCycle.primalResidual γ η ν =
      WithLp.toLp 2 ∘ z.primalResidual ∘ (fun k : ℕ ↦ k + 1) := by
    funext k
    simp [Function.comp_def, ADMM.Trajectory.primalResidual, z,
      CoordinateBridge.trajectory, CoordinateBridge.problem, Matrix.neg_mulVec,
      ProjectionCycle.primalResidual_apply, ProjectionCycle.xSequence_succ,
      ProjectionCycle.ySequence_succ, ProjectionCycle.xVertex_apply, ← sub_eq_add_neg]
  rw [heq]
  exact hEuclidean

end ConsensusADMM
