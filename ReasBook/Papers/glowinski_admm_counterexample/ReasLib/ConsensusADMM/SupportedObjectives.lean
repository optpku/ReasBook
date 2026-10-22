/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycleTrajectory
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.StrictProjectionCycle
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Optimality
public import glowinski_admm_counterexample.ReasLib.Convex.ExtendedReal
public import glowinski_admm_counterexample.ReasLib.Convex.Polyhedral
public import glowinski_admm_counterexample.ReasLib.Convex.PiecewiseQuadratic
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Mul

@[expose] public section

namespace ConsensusADMM

/-- A real supporting plane at a point certifies that the corresponding unit
quadratic ADMM subproblem is uniquely minimized there. -/
lemma ofRealAugmented_uniqueMinimizer
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (p center dual : E)
    (supports : ∀ z, f p + inner ℝ (center - dual - p) (z - p) ≤ f z) :
    (∀ z,
      ofReal f p +
          ((inner ℝ dual (p - center) + ‖p - center‖ ^ 2 / 2 : ℝ) : EReal) ≤
        ofReal f z +
          ((inner ℝ dual (z - center) + ‖z - center‖ ^ 2 / 2 : ℝ) : EReal)) ∧
      (∀ z,
        ofReal f z +
            ((inner ℝ dual (z - center) + ‖z - center‖ ^ 2 / 2 : ℝ) : EReal) ≤
          ofReal f p +
            ((inner ℝ dual (p - center) + ‖p - center‖ ^ 2 / 2 : ℝ) : EReal) →
        z = p) ∧
      ofReal f p ≠ ⊤ := by
  -- Completing the square separates the supplied support gap from the
  -- nonnegative squared distance to the candidate point.
  have objective_gap (z : E) :
      f z + inner ℝ dual (z - center) + ‖z - center‖ ^ 2 / 2 =
        f p + inner ℝ dual (p - center) + ‖p - center‖ ^ 2 / 2 +
          (f z - f p - inner ℝ (center - dual - p) (z - p)) +
          ‖z - p‖ ^ 2 / 2 := by
    have displacement : z - center = (p - center) + (z - p) := by
      abel
    rw [displacement, norm_add_sq_real]
    simp only [inner_add_right, inner_sub_left, inner_sub_right]
    ring
  have support_gap_nonneg (z : E) :
      0 ≤ f z - f p - inner ℝ (center - dual - p) (z - p) := by
    linarith [supports z]
  constructor
  · intro z
    simp only [ofReal_apply, ← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith [objective_gap z, support_gap_nonneg z, sq_nonneg ‖z - p‖]
  constructor
  · intro z objective_le
    have real_objective_le :
        f z + inner ℝ dual (z - center) + ‖z - center‖ ^ 2 / 2 ≤
          f p + inner ℝ dual (p - center) + ‖p - center‖ ^ 2 / 2 := by
      simpa only [ofReal_apply, ← EReal.coe_add, EReal.coe_le_coe_iff,
        add_assoc] using objective_le
    have distance_zero : ‖z - p‖ = 0 := by
      rw [objective_gap z] at real_objective_le
      nlinarith [support_gap_nonneg z, sq_nonneg ‖z - p‖, norm_nonneg (z - p)]
    exact sub_eq_zero.mp (norm_eq_zero.mp distance_zero)
  · rw [ofReal_apply]
    exact EReal.coe_ne_top _

/-- A common orthogonal phase shift makes the paired inner product of two
advanced cyclic families independent of the phase. -/
lemma cyclicInner_eq_zeroPhase
    {N : ℕ} [NeZero N] {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p n : ZMod N → E) (U : E ≃ₗᵢ[ℝ] E)
    (advance : ∀ i, U (p i) = p (i + 1) ∧ U (n i) = n (i + 1))
    (i : ZMod N) :
    inner ℝ (n i) (p i) = inner ℝ (n 0) (p 0) := by
  -- Isometry invariance identifies the paired inner product at consecutive
  -- phases, after which a natural representative reaches every `ZMod` phase.
  have next_eq (j : ZMod N) :
      inner ℝ (n (j + 1)) (p (j + 1)) = inner ℝ (n j) (p j) := by
    rw [← (advance j).2, ← (advance j).1,
      LinearIsometryEquiv.inner_map_map]
  rw [← ZMod.natCast_zmod_val i]
  induction i.val with
  | zero => simp only [Nat.cast_zero]
  | succ k induction_hypothesis =>
      simpa only [Nat.cast_succ, Nat.cast_one] using
        (next_eq (k : ZMod N)).trans induction_hypothesis

/-- Strict cyclic supports with an orthogonal phase shift have one positive
self-product, and each phase form is strictly active at its own vertex. -/
lemma cyclicSupport_activeForm
    {N : ℕ} [NeZero N] {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p n : ZMod N → E)
    (supports : ProjectionCycle.StrictNonselfSupports p n)
    (symmetry : ProjectionCycle.HasOrthogonalCyclicSymmetry p n) :
    ∃ α : ℝ, 0 < α ∧
      (∀ i, inner ℝ (n i) (p i) = α) ∧
      ∀ i j, j ≠ i → inner ℝ (n j) (p i) < α := by
  -- Choose the zero-phase value and use cyclic invariance for every self term.
  obtain ⟨U, advance⟩ := symmetry
  let α := inner ℝ (n 0) (p 0)
  have alpha_pos : 0 < α := (supports 0).1
  have self_eq (i : ZMod N) : inner ℝ (n i) (p i) = α := by
    exact cyclicInner_eq_zeroPhase p n U advance i
  refine ⟨α, alpha_pos, self_eq, ?_⟩
  -- The strict support inequality for normal `n j`, rewritten with the common
  -- self-product, says precisely that its value at `p i` is smaller.
  intro i j hji
  have strict_support := (supports j).2 i hji.symm
  rw [inner_sub_right, self_eq j] at strict_support
  linarith

/-- Orthogonal symmetry of projection-cycle data advances the two derived
vertex-normal support families as well. -/
lemma projectionCycleSupportFamilies_hasOrthogonalCyclicSymmetry
    {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (gamma : ℝ) (eta nu : ZMod N → E)
    (symmetry : ProjectionCycle.HasOrthogonalCyclicSymmetry eta nu) :
    ProjectionCycle.HasOrthogonalCyclicSymmetry
        (ProjectionCycle.xVertex gamma eta nu)
        (ProjectionCycle.firstNormal gamma eta nu) ∧
      ProjectionCycle.HasOrthogonalCyclicSymmetry eta
        (ProjectionCycle.secondNormal gamma nu) := by
  obtain ⟨U, advance⟩ := symmetry
  -- Linearity transports the residual recurrence through the phase isometry.
  have residual_advance (i : ZMod N) :
      U (ProjectionCycle.residual gamma nu i) =
        ProjectionCycle.residual gamma nu (i + 1) := by
    rw [ProjectionCycle.residual_apply, ProjectionCycle.residual_apply,
      LinearIsometryEquiv.map_smul, LinearIsometryEquiv.map_sub,
      (advance i).2, (advance (i - 1)).2]
    simp only [sub_add_cancel, add_sub_cancel_right]
  have vertex_advance (i : ZMod N) :
      U (ProjectionCycle.xVertex gamma eta nu i) =
        ProjectionCycle.xVertex gamma eta nu (i + 1) := by
    rw [ProjectionCycle.xVertex_apply, ProjectionCycle.xVertex_apply,
      LinearIsometryEquiv.map_add, (advance i).1, residual_advance]
  have firstNormal_advance (i : ZMod N) :
      U (ProjectionCycle.firstNormal gamma eta nu i) =
        ProjectionCycle.firstNormal gamma eta nu (i + 1) := by
    rw [ProjectionCycle.firstNormal_apply, ProjectionCycle.firstNormal_apply,
      LinearIsometryEquiv.map_sub, LinearIsometryEquiv.map_sub,
      (advance (i - 1)).1, (advance (i - 1)).2, vertex_advance]
    simp only [sub_add_cancel, add_sub_cancel_right]
  have secondNormal_advance (i : ZMod N) :
      U (ProjectionCycle.secondNormal gamma nu i) =
        ProjectionCycle.secondNormal gamma nu (i + 1) := by
    rw [ProjectionCycle.secondNormal_apply, ProjectionCycle.secondNormal_apply,
      LinearIsometryEquiv.map_add, (advance (i - 1)).2, residual_advance]
    simp only [sub_add_cancel, add_sub_cancel_right]
  -- Package the same isometry with its two derived phase-advance laws.
  exact ⟨⟨U, fun i ↦ ⟨vertex_advance i, firstNormal_advance i⟩⟩,
    ⟨U, fun i ↦ ⟨(advance i).1, secondNormal_advance i⟩⟩⟩

/-- Supporting planes for the two projection-cycle normal families give the
corresponding real-valued consensus ADMM trajectory and unique block updates. -/
lemma ofRealSupportedCycle_updates
    {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (gamma : ℝ) (eta nu : ZMod N → E) (f g : E → ℝ)
    (gamma_pos : 0 < gamma)
    (first_supports : ∀ i z,
      f (ProjectionCycle.xVertex gamma eta nu i) +
          inner ℝ (ProjectionCycle.firstNormal gamma eta nu i)
            (z - ProjectionCycle.xVertex gamma eta nu i) ≤ f z)
    (second_supports : ∀ i z,
      g (eta i) + inner ℝ (ProjectionCycle.secondNormal gamma nu i) (z - eta i) ≤ g z) :
    IsTrajectory gamma (ofReal f) (ofReal g)
        (ProjectionCycle.xSequence gamma eta nu) (ProjectionCycle.ySequence eta)
        (ProjectionCycle.dualSequence nu) ∧
      HasUniqueUpdates (ofReal f) (ofReal g)
        (ProjectionCycle.xSequence gamma eta nu) (ProjectionCycle.ySequence eta)
        (ProjectionCycle.dualSequence nu) := by
  -- The first support normal is already in the orientation required by the
  -- generic real augmented-minimizer certificate.
  have first_gradient_support (i : ZMod N) : ∀ z,
      f (ProjectionCycle.xVertex gamma eta nu i) +
          inner ℝ (eta (i - 1) - nu (i - 1) -
            ProjectionCycle.xVertex gamma eta nu i)
            (z - ProjectionCycle.xVertex gamma eta nu i) ≤ f z := by
    intro z
    simpa only [ProjectionCycle.firstNormal_apply] using first_supports i z
  have first_update (i : ZMod N) := ofRealAugmented_uniqueMinimizer f
    (ProjectionCycle.xVertex gamma eta nu i) (eta (i - 1)) (nu (i - 1))
    (first_gradient_support i)
  -- Negating the multiplier puts the second support normal into the same
  -- generic orientation.
  have second_normal_as_gradient (i : ZMod N) :
      ProjectionCycle.xVertex gamma eta nu i - (-nu (i - 1)) - eta i =
        ProjectionCycle.secondNormal gamma nu i := by
    rw [ProjectionCycle.xVertex_apply, ProjectionCycle.secondNormal_apply]
    abel
  have second_gradient_support (i : ZMod N) : ∀ z,
      g (eta i) + inner ℝ
          (ProjectionCycle.xVertex gamma eta nu i - (-nu (i - 1)) - eta i)
          (z - eta i) ≤ g z := by
    intro z
    rw [second_normal_as_gradient i]
    exact second_supports i z
  have second_update (i : ZMod N) := ofRealAugmented_uniqueMinimizer g
    (eta i) (ProjectionCycle.xVertex gamma eta nu i) (-nu (i - 1))
    (second_gradient_support i)
  have second_objective (i : ZMod N) (z : E) :
      inner ℝ (-nu (i - 1)) (z - ProjectionCycle.xVertex gamma eta nu i) +
          ‖z - ProjectionCycle.xVertex gamma eta nu i‖ ^ 2 / 2 =
        inner ℝ (nu (i - 1)) (ProjectionCycle.xVertex gamma eta nu i - z) +
          ‖ProjectionCycle.xVertex gamma eta nu i - z‖ ^ 2 / 2 := by
    have reverse_displacement :
        z - ProjectionCycle.xVertex gamma eta nu i =
          -(ProjectionCycle.xVertex gamma eta nu i - z) := by
      abel
    rw [reverse_displacement, inner_neg_left, inner_neg_right, norm_neg, neg_neg]
  constructor
  · rw [trajectory_iff]
    intro k
    -- Normalize every stored sequence to phase `k` and apply the two phasewise
    -- augmented-minimizer certificates.
    rw [ProjectionCycle.xSequence_succ, ProjectionCycle.ySequence_succ,
      ProjectionCycle.ySequence_apply, ProjectionCycle.dualSequence_succ,
      ProjectionCycle.dualSequence_apply]
    refine ⟨(first_update (k : ZMod N)).1, ?_,
      (first_update (k : ZMod N)).2.2, (second_update (k : ZMod N)).2.2, ?_⟩
    · intro z
      have update := (second_update (k : ZMod N)).1 z
      rw [second_objective (k : ZMod N) (eta (k : ZMod N)),
        second_objective (k : ZMod N) z] at update
      exact update
    · rw [ProjectionCycle.xVertex_apply, add_sub_cancel_left,
        ProjectionCycle.residual_apply, smul_smul]
      simp [gamma_pos.ne']
  · rw [uniqueUpdates_iff]
    intro k
    -- The second uniqueness implication is transported through the same
    -- displacement-reversal identity.
    rw [ProjectionCycle.xSequence_succ, ProjectionCycle.ySequence_succ,
      ProjectionCycle.ySequence_apply, ProjectionCycle.dualSequence_apply]
    refine ⟨(first_update (k : ZMod N)).2.1, ?_⟩
    intro z objective_le
    apply (second_update (k : ZMod N)).2.1 z
    rw [second_objective (k : ZMod N) z,
      second_objective (k : ZMod N) (eta (k : ZMod N))]
    exact objective_le

/-- Nonnegative real objectives that vanish at the origin have the origin as
a zero-valued KKT point and a primal minimizer after lifting to `EReal`. -/
lemma ofRealOriginOptimality
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : E → ℝ) (f_zero : f 0 = 0) (g_zero : g 0 = 0)
    (f_nonneg : ∀ z, 0 ≤ f z) (g_nonneg : ∀ z, 0 ≤ g z) :
    IsKKT (ofReal f) (ofReal g) 0 0 0 ∧
      ofReal f 0 + ofReal g 0 = 0 ∧
      IsPrimalMinimizer (ofReal f) (ofReal g) 0 := by
  -- At zero multiplier, the KKT inequalities reduce to the two supplied
  -- nonnegativity inequalities.
  have kkt : IsKKT (ofReal f) (ofReal g) 0 0 0 := by
    rw [kkt_iff]
    refine ⟨rfl, ?_, ?_⟩
    · intro z
      simp only [ofReal_apply, f_zero, neg_zero, inner_zero_left, EReal.coe_zero, zero_add]
      exact EReal.coe_nonneg.mpr (f_nonneg z)
    · intro z
      simp only [ofReal_apply, g_zero, inner_zero_left, EReal.coe_zero, zero_add]
      exact EReal.coe_nonneg.mpr (g_nonneg z)
  -- Both lifted objectives retain their zero value at the origin.
  have value : ofReal f 0 + ofReal g 0 = 0 := by
    simp only [ofReal_apply, f_zero, g_zero, EReal.coe_zero, add_zero]
  -- The sum of the two nonnegative objectives cannot improve on zero.
  have primal : IsPrimalMinimizer (ofReal f) (ofReal g) 0 := by
    rw [primalMinimizer_iff]
    intro z
    simpa only [ofReal_apply, f_zero, g_zero, EReal.coe_zero, zero_add,
      ← EReal.coe_add, ← EReal.coe_zero, EReal.coe_le_coe_iff] using
        add_nonneg (f_nonneg z) (g_nonneg z)
  exact ⟨kkt, value, primal⟩

/-- A finite family of active linear forms with a common positive self-product
defines a nonnegative closed convex piecewise-quadratic max-square objective. -/
lemma maxSquareObjective_spec
    {N : ℕ} [NeZero N] {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p n : ZMod N → E) (α : ℝ) (alpha_pos : 0 < α)
    (self_eq : ∀ i, inner ℝ (n i) (p i) = α)
    (active : ∀ i j, j ≠ i → inner ℝ (n j) (p i) < α) :
    ∃ f : E → ℝ,
      IsFiniteClosedConvexPiecewiseQuadratic f ∧
        f 0 = 0 ∧ (∀ z, 0 ≤ f z) ∧
        ∀ (t : ℝ), 0 ≤ t → ∀ i,
          f (t • p i) = t ^ 2 * α / 2 ∧
            ∀ z, f (t • p i) + inner ℝ (t • n i) (z - t • p i) ≤ f z := by
  classical
  -- Adjoin the zero form so the finite maximum is globally nonnegative.
  let a : Option (ZMod N) → E
    | none => 0
    | some i => n i
  have indices_nonempty : (Finset.univ : Finset (Option (ZMod N))).Nonempty :=
    ⟨none, Finset.mem_univ none⟩
  let h : E → ℝ := fun z ↦
    Finset.univ.sup' indices_nonempty (fun i ↦ inner ℝ (a i) z)
  let f : E → ℝ := fun z ↦ h z ^ 2 / (2 * α)
  have two_pos : (0 : ℝ) < 2 := by
    norm_num
  have denominator_pos : 0 < 2 * α := mul_pos two_pos alpha_pos
  have h_nonneg (z : E) : 0 ≤ h z := by
    -- The zero form is one of the competitors in the finite maximum.
    have zero_le := Finset.le_sup'
      (fun i : Option (ZMod N) ↦ inner ℝ (a i) z) (Finset.mem_univ none)
    simpa only [h, a, inner_zero_left] using zero_le
  have h_convex : ConvexOn ℝ Set.univ h := by
    -- Each linear form lies below the corresponding convex combination of the
    -- two finite maxima, so their maximum is convex.
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ c d hc hd _
    apply Finset.sup'_le
    intro i hi
    have x_le : inner ℝ (a i) x ≤ h x := by
      exact Finset.le_sup' (fun j : Option (ZMod N) ↦ inner ℝ (a j) x) hi
    have y_le : inner ℝ (a i) y ≤ h y := by
      exact Finset.le_sup' (fun j : Option (ZMod N) ↦ inner ℝ (a j) y) hi
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    exact add_le_add (mul_le_mul_of_nonneg_left x_le hc)
      (mul_le_mul_of_nonneg_left y_le hd)
  have h_continuous : Continuous h := by
    -- Finite maxima of continuous linear forms are continuous.
    dsimp only [h]
    exact Continuous.finset_sup'_apply indices_nonempty
      (fun _ _ ↦ continuous_const.inner continuous_id)
  have f_convex : ConvexOn ℝ Set.univ f := by
    -- Squaring preserves convexity on a nonnegative convex function, and the
    -- remaining scalar is positive.
    have square_convex := h_convex.pow (fun z _ ↦ h_nonneg z) 2
    have scaled_convex := ConvexOn.smul (inv_nonneg.mpr denominator_pos.le) square_convex
    simpa only [f, Pi.smul_apply, Pi.pow_apply, div_eq_mul_inv, smul_eq_mul, mul_comm] using scaled_convex
  have f_continuous : Continuous f := by
    -- The max-square formula is a quotient by one nonzero constant.
    simpa only [f, Pi.pow_apply] using (h_continuous.pow 2).div_const (2 * α)
  have f_closed_epigraph : IsClosed {q : E × ℝ | f q.1 ≤ q.2} := by
    -- Continuity gives the closed epigraph required by the project predicate.
    simpa only [Set.mem_univ, true_and] using
      (isClosed_univ.epigraph f_continuous.continuousOn)
  have h_zero : h 0 = 0 := by
    -- Every linear form vanishes at the origin.
    dsimp only [h]
    apply Finset.sup'_eq_of_forall
    intro i _
    simp only [inner_zero_right]
  have f_zero : f 0 = 0 := by
    change h 0 ^ 2 / (2 * α) = 0
    rw [h_zero]
    norm_num
  have f_nonneg (z : E) : 0 ≤ f z := by
    exact div_nonneg (sq_nonneg (h z)) denominator_pos.le
  -- Reindex the active cells by `Fin` to match the piecewise-quadratic API.
  let e := Fintype.equivFin (Option (ZMod N))
  let cells : Fin (Fintype.card (Option (ZMod N))) → Set E := fun i ↦
    {z | ∀ j, inner ℝ (a (e.symm j)) z ≤ inner ℝ (a (e.symm i)) z}
  let q : Fin (Fintype.card (Option (ZMod N))) → E →L[ℝ] E := fun i ↦
    α⁻¹ • InnerProductSpace.rankOne ℝ (a (e.symm i)) (a (e.symm i))
  let l : Fin (Fintype.card (Option (ZMod N))) → E := fun _ ↦ 0
  let c : Fin (Fintype.card (Option (ZMod N))) → ℝ := fun _ ↦ 0
  have cells_polyhedral (i : Fin (Fintype.card (Option (ZMod N)))) :
      IsPolyhedralSet (cells i) := by
    -- A cell is the finite intersection saying that its chosen form dominates
    -- every competing form.
    rw [polyhedralSet_iff]
    refine ⟨Fintype.card (Option (ZMod N)),
      fun j ↦ a (e.symm j) - a (e.symm i), fun _ ↦ 0, ?_⟩
    ext z
    simp only [cells, Set.mem_setOf_eq, inner_sub_left, sub_nonpos]
  have cells_cover (z : E) : ∃ i, z ∈ cells i := by
    -- Choose a form attaining the finite maximum and use its maximizing
    -- inequality as the cell-membership certificate.
    obtain ⟨r, _, maximum_eq⟩ := Finset.exists_mem_eq_sup'
      (s := Finset.univ) indices_nonempty (fun i ↦ inner ℝ (a i) z)
    refine ⟨e r, ?_⟩
    dsimp only [cells, Set.mem_setOf_eq]
    intro j
    have competitor_le := Finset.le_sup'
      (fun i : Option (ZMod N) ↦ inner ℝ (a i) z)
      (Finset.mem_univ (e.symm j))
    rw [maximum_eq] at competitor_le
    simpa only [Equiv.symm_apply_apply] using competitor_le
  have h_eq_on_cell (i : Fin (Fintype.card (Option (ZMod N))))
      (z : E) (hz : z ∈ cells i) :
      h z = inner ℝ (a (e.symm i)) z := by
    -- Cell membership supplies the upper bound, while the active form itself
    -- supplies the reverse finite-maximum bound.
    apply le_antisymm
    · dsimp only [h]
      dsimp only [cells, Set.mem_setOf_eq] at hz
      apply Finset.sup'_le
      intro r _
      simpa only [Equiv.symm_apply_apply] using hz (e r)
    · dsimp only [h]
      exact Finset.le_sup'
        (fun r : Option (ZMod N) ↦ inner ℝ (a r) z)
        (Finset.mem_univ (e.symm i))
  have quadratic_formula (i : Fin (Fintype.card (Option (ZMod N))))
      (z : E) (hz : z ∈ cells i) :
      f z = inner ℝ (q i z) z / 2 + inner ℝ (l i) z + c i := by
    -- On one active cell the finite maximum is one linear form, whose square
    -- is represented by the corresponding scaled rank-one quadratic map.
    change h z ^ 2 / (2 * α) = _
    rw [h_eq_on_cell i z hz]
    simp only [q, l, c, ContinuousLinearMap.smul_apply,
      InnerProductSpace.rankOne_apply, real_inner_smul_left, inner_smul_right,
      inner_zero_left, zero_add, add_zero]
    field_simp [alpha_pos.ne'] <;> ring
  have piecewise : IsFiniteClosedConvexPiecewiseQuadratic f := by
    -- Assemble the convexity, closedness, finite cover, and cell formulas.
    rw [finiteClosedConvexPiecewiseQuadratic_iff]
    exact ⟨f_convex, f_closed_epigraph,
      Fintype.card (Option (ZMod N)), cells, q, l, c, cells_cover,
      fun i ↦ ⟨cells_polyhedral i, quadratic_formula i⟩⟩
  refine ⟨f, piecewise, f_zero, f_nonneg, ?_⟩
  intro t ht i
  have h_ray : h (t • p i) = t * α := by
    -- At a nonnegative point of the `i`th ray, its own form has value `t * α`
    -- and every other form is no larger.
    apply le_antisymm
    · dsimp only [h]
      apply Finset.sup'_le
      intro r _
      cases r with
      | none =>
          simp only [a, inner_zero_left]
          exact mul_nonneg ht alpha_pos.le
      | some j =>
          rw [inner_smul_right]
          by_cases hji : j = i
          · subst j
            rw [self_eq]
          · exact mul_le_mul_of_nonneg_left (active i j hji).le ht
    · have selected_le := Finset.le_sup'
        (fun r : Option (ZMod N) ↦ inner ℝ (a r) (t • p i))
        (Finset.mem_univ (some i))
      simpa only [h, a, inner_smul_right, self_eq i] using selected_le
  have ray_value : f (t • p i) = t ^ 2 * α / 2 := by
    -- Substitute the active value and cancel the positive common self-product.
    change h (t • p i) ^ 2 / (2 * α) = _
    rw [h_ray]
    field_simp [alpha_pos.ne'] <;> ring
  refine ⟨ray_value, ?_⟩
  intro z
  have selected_le : inner ℝ (n i) z ≤ h z := by
    have form_le := Finset.le_sup'
      (fun r : Option (ZMod N) ↦ inner ℝ (a r) z)
      (Finset.mem_univ (some i))
    simpa only [h, a] using form_le
  have scaled_selected_le : t * inner ℝ (n i) z ≤ t * h z :=
    mul_le_mul_of_nonneg_left selected_le ht
  have square_nonneg : 0 ≤ (h z - t * α) ^ 2 := sq_nonneg _
  -- The scalar inequality is the supporting-line inequality for the square on
  -- the nonnegative half-line, after multiplying by the positive denominator.
  rw [ray_value]
  simp only [inner_sub_right, real_inner_smul_left, inner_smul_right, self_eq i]
  change t ^ 2 * α / 2 + (t * inner ℝ (n i) z - t * (t * α)) ≤ h z ^ 2 / (2 * α)
  apply (le_div_iff₀ denominator_pos).2
  nlinarith

end ConsensusADMM
