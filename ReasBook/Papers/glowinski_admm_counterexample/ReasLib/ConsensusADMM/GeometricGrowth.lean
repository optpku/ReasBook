/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.SupportedObjectives
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

open Filter

namespace ConsensusADMM.GeometricGrowth

universe u
variable {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The phase residual for a trajectory expanding by the factor `κ` per step. -/
noncomputable def residual (γ κ : ℝ) (ν : ZMod N → E) (i : ZMod N) : E :=
  γ⁻¹ • (ν i - κ⁻¹ • ν (i - 1))

noncomputable def vertex (γ κ : ℝ) (η ν : ZMod N → E) (i : ZMod N) : E :=
  η i + residual γ κ ν i

noncomputable def firstNormal (γ κ : ℝ) (η ν : ZMod N → E) (i : ZMod N) : E :=
  κ⁻¹ • (η (i - 1) - ν (i - 1)) - vertex γ κ η ν i

noncomputable def secondNormal (γ κ : ℝ) (ν : ZMod N → E) (i : ZMod N) : E :=
  κ⁻¹ • ν (i - 1) + residual γ κ ν i

lemma at_one (γ : ℝ) (η ν : ZMod N → E) :
    residual γ 1 ν = ProjectionCycle.residual γ ν ∧
    vertex γ 1 η ν = ProjectionCycle.xVertex γ η ν ∧
    firstNormal γ 1 η ν = ProjectionCycle.firstNormal γ η ν ∧
    secondNormal γ 1 ν = ProjectionCycle.secondNormal γ ν := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;>
    simp [residual, vertex, firstNormal, secondNormal, ProjectionCycle.residual,
    ProjectionCycle.xVertex, ProjectionCycle.firstNormal, ProjectionCycle.secondNormal]

/-- Finite strict support tables persist under continuous perturbations. -/
lemma supports_eventually [NeZero N] {p n : ℝ → ZMod N → E} {t : ℝ}
    (hp : ∀ i, ContinuousAt (fun s ↦ p s i) t)
    (hn : ∀ i, ContinuousAt (fun s ↦ n s i) t)
    (h : ProjectionCycle.StrictNonselfSupports (p t) (n t)) :
    ∀ᶠ s in nhds t, ProjectionCycle.StrictNonselfSupports (p s) (n s) := by
  apply Filter.eventually_all.mpr
  intro i
  have horigin := ((hn i).inner (hp i)).eventually (lt_mem_nhds (h i).1)
  have hpairs : ∀ᶠ s in nhds t, ∀ j, j ≠ i →
      0 < inner ℝ (n s i) (p s i - p s j) := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall fun _ hj ↦ (hj hji).elim
    · exact (((hn i).inner ((hp i).sub (hp j))).eventually
        (lt_mem_nhds ((h i).2 j hji))).mono fun _ hs _ ↦ hs
  exact horigin.and hpairs

/-- Choose a genuine expansion factor while retaining both strict support tables
and a nonzero residual. This is the continuity step in the growth construction. -/
lemma expanding_data [NeZero N] (γ : ℝ) (η ν : ZMod N → E)
    (hstrict : IsStrictProjectionCycle γ η ν)
    (hnonzero : ∃ i, ProjectionCycle.residual γ ν i ≠ 0) :
    ∃ κ : ℝ, 1 < κ ∧
      ProjectionCycle.StrictNonselfSupports (vertex γ κ η ν) (firstNormal γ κ η ν) ∧
      ProjectionCycle.StrictNonselfSupports η (secondNormal γ κ ν) ∧
      ∃ i, residual γ κ ν i ≠ 0 := by
  have hr (i : ZMod N) : ContinuousAt (fun κ : ℝ ↦ residual γ κ ν i) 1 :=
    continuousAt_const.smul
      (continuousAt_const.sub ((continuousAt_id.inv₀ one_ne_zero).smul continuousAt_const))
  have hx (i : ZMod N) : ContinuousAt (fun κ : ℝ ↦ vertex γ κ η ν i) 1 :=
    continuousAt_const.add (hr i)
  have ha (i : ZMod N) : ContinuousAt (fun κ : ℝ ↦ firstNormal γ κ η ν i) 1 :=
    ((continuousAt_id.inv₀ one_ne_zero).smul continuousAt_const).sub (hx i)
  have hc (i : ZMod N) : ContinuousAt (fun κ : ℝ ↦ secondNormal γ κ ν i) 1 :=
    ((continuousAt_id.inv₀ one_ne_zero).smul continuousAt_const).add (hr i)
  obtain ⟨i, hi⟩ := hnonzero
  have hfirst := supports_eventually hx ha (by simpa only [(at_one γ η ν).2.1,
    (at_one γ η ν).2.2.1] using hstrict.1)
  have hsecond := supports_eventually (p := fun _ ↦ η) (fun _ ↦ continuousAt_const) hc
    (by simpa only [(at_one γ η ν).2.2.2] using hstrict.2)
  have hne : ∀ᶠ κ in nhds (1 : ℝ), residual γ κ ν i ≠ 0 :=
    (hr i).eventually_ne (by simpa only [(at_one γ η ν).1] using hi)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hfirst.and (hsecond.and hne))
  have hdist : dist (1 + ε / 2) (1 : ℝ) < ε := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]
    linarith
  obtain ⟨hfirst', hsecond', hne'⟩ := hball hdist
  exact ⟨1 + ε / 2, by linarith, hfirst', hsecond', i, hne'⟩

/-- The same orthogonal phase shift preserves the perturbed residuals and both
vertex-normal families. -/
lemma symmetry (γ κ : ℝ) (η ν : ZMod N → E)
    (hsym : ProjectionCycle.HasOrthogonalCyclicSymmetry η ν) :
    ProjectionCycle.HasOrthogonalCyclicSymmetry (vertex γ κ η ν) (firstNormal γ κ η ν) ∧
    ProjectionCycle.HasOrthogonalCyclicSymmetry η (secondNormal γ κ ν) ∧
    ProjectionCycle.HasOrthogonalCyclicSymmetry (residual γ κ ν) (residual γ κ ν) := by
  obtain ⟨U, hU⟩ := hsym
  have hr (i : ZMod N) : U (residual γ κ ν i) = residual γ κ ν (i + 1) := by
    simp only [residual, map_smul, map_sub, (hU i).2, (hU (i - 1)).2,
      sub_add_cancel, add_sub_cancel_right]
  have hx (i : ZMod N) : U (vertex γ κ η ν i) = vertex γ κ η ν (i + 1) := by
    simp only [vertex, map_add, (hU i).1, hr]
  have ha (i : ZMod N) : U (firstNormal γ κ η ν i) = firstNormal γ κ η ν (i + 1) := by
    simp only [firstNormal, map_sub, map_smul, (hU (i - 1)).1, (hU (i - 1)).2,
      hx, sub_add_cancel, add_sub_cancel_right]
  have hc (i : ZMod N) : U (secondNormal γ κ ν i) = secondNormal γ κ ν (i + 1) := by
    simp only [secondNormal, map_add, map_smul, (hU (i - 1)).2,
      hr, sub_add_cancel, add_sub_cancel_right]
  exact ⟨⟨U, fun i ↦ ⟨hx i, ha i⟩⟩, ⟨U, fun i ↦ ⟨(hU i).1, hc i⟩⟩,
    ⟨U, fun i ↦ ⟨hr i, hr i⟩⟩⟩

/-- The initial phase is scaled by `κ⁻¹`; each successor has the paper's form
`κ^k • p[k]`. -/
noncomputable def sequence (κ : ℝ) (p : ZMod N → E) (k : ℕ) : E :=
  κ ^ k • (κ⁻¹ • p ((k : ZMod N) - 1))

lemma sequence_succ {κ : ℝ} (hκ : κ ≠ 0) (p : ZMod N → E) (k : ℕ) :
    sequence κ p (k + 1) = κ ^ k • p (k : ZMod N) := by
  simp [sequence, pow_succ, smul_smul, mul_assoc, hκ]

/-- Supporting planes along positive rays certify every expanding ADMM step,
including the return from the last phase to phase zero. -/
lemma supported_updates (γ κ : ℝ) (η ν : ZMod N → E) (f g : E → ℝ)
    (hγ : 0 < γ) (hκ : 0 < κ)
    (hf : ∀ t : ℝ, 0 ≤ t → ∀ i z,
      f (t • vertex γ κ η ν i) + inner ℝ (t • firstNormal γ κ η ν i)
        (z - t • vertex γ κ η ν i) ≤ f z)
    (hg : ∀ t : ℝ, 0 ≤ t → ∀ i z,
      g (t • η i) + inner ℝ (t • secondNormal γ κ ν i) (z - t • η i) ≤ g z) :
    IsTrajectory γ (ofReal f) (ofReal g)
      (sequence κ (vertex γ κ η ν)) (sequence κ η) (sequence κ ν) ∧
    HasUniqueUpdates (ofReal f) (ofReal g)
      (sequence κ (vertex γ κ η ν)) (sequence κ η) (sequence κ ν) := by
  have hfirstNormal (k : ℕ) :
      sequence κ η k - sequence κ ν k - κ ^ k • vertex γ κ η ν (k : ZMod N) =
        κ ^ k • firstNormal γ κ η ν (k : ZMod N) := by
    simp only [sequence, firstNormal, smul_sub]
  have hsecondNormal (k : ℕ) :
      κ ^ k • vertex γ κ η ν (k : ZMod N) - (-sequence κ ν k) - κ ^ k • η (k : ZMod N) =
        κ ^ k • secondNormal γ κ ν (k : ZMod N) := by
    simp only [sequence, vertex, secondNormal, smul_add]
    abel
  have first_support (k : ℕ) (z : E) :
      f (κ ^ k • vertex γ κ η ν (k : ZMod N)) +
        inner ℝ (sequence κ η k - sequence κ ν k - κ ^ k • vertex γ κ η ν (k : ZMod N))
          (z - κ ^ k • vertex γ κ η ν (k : ZMod N)) ≤ f z := by
    rw [hfirstNormal]
    exact hf _ (pow_nonneg hκ.le _) _ _
  have second_support (k : ℕ) (z : E) :
      g (κ ^ k • η (k : ZMod N)) +
        inner ℝ (κ ^ k • vertex γ κ η ν (k : ZMod N) - (-sequence κ ν k) - κ ^ k • η (k : ZMod N))
          (z - κ ^ k • η (k : ZMod N)) ≤ g z := by
    rw [hsecondNormal]
    exact hg _ (pow_nonneg hκ.le _) _ _
  have first_update (k : ℕ) := ofRealAugmented_uniqueMinimizer f
    (κ ^ k • vertex γ κ η ν (k : ZMod N)) (sequence κ η k) (sequence κ ν k)
    (first_support k)
  have second_update (k : ℕ) := ofRealAugmented_uniqueMinimizer g
    (κ ^ k • η (k : ZMod N)) (κ ^ k • vertex γ κ η ν (k : ZMod N)) (-sequence κ ν k)
    (second_support k)
  have second_objective (k : ℕ) (z : E) :
      inner ℝ (-sequence κ ν k) (z - κ ^ k • vertex γ κ η ν (k : ZMod N)) +
        ‖z - κ ^ k • vertex γ κ η ν (k : ZMod N)‖ ^ 2 / 2 =
      inner ℝ (sequence κ ν k) (κ ^ k • vertex γ κ η ν (k : ZMod N) - z) +
        ‖κ ^ k • vertex γ κ η ν (k : ZMod N) - z‖ ^ 2 / 2 := by
    rw [← neg_sub (κ ^ k • vertex γ κ η ν (k : ZMod N)) z,
      inner_neg_left, inner_neg_right, norm_neg, neg_neg]
  constructor
  · intro k
    simp only [sequence_succ hκ.ne']
    refine ⟨(first_update k).1, ?_, (first_update k).2.2, (second_update k).2.2, ?_⟩
    · intro z
      have h := (second_update k).1 z
      rw [second_objective, second_objective] at h
      exact h
    · rw [vertex, smul_add, add_sub_cancel_left]
      rw [smul_comm γ (κ ^ k)]
      simp only [residual, smul_smul, mul_assoc, mul_inv_cancel₀ hγ.ne', mul_one]
      simp only [sequence, smul_sub, add_sub_cancel]
  · intro k
    simp only [sequence_succ hκ.ne']
    refine ⟨(first_update k).2.1, ?_⟩
    intro z h
    apply (second_update k).2.1 z
    rw [second_objective, second_objective]
    exact h

/-- A symmetric strict projection cycle yields fixed piecewise-quadratic
objectives with geometrically growing residuals and objective values. -/
theorem counterexample [NeZero N] (γ : ℝ) (η ν : ZMod N → E)
    (hγ : 0 < γ) (hstrict : IsStrictProjectionCycle γ η ν)
    (hnonzero : ∃ i, ProjectionCycle.residual γ ν i ≠ 0)
    (hsym : ProjectionCycle.HasOrthogonalCyclicSymmetry η ν) :
    ∃ f g : E → ℝ, ∃ x y dual : ℕ → E, ∃ c_r c_f κ : ℝ,
      IsFiniteClosedConvexPiecewiseQuadratic f ∧
      IsFiniteClosedConvexPiecewiseQuadratic g ∧
      IsTrajectory γ (ofReal f) (ofReal g) x y dual ∧
      HasUniqueUpdates (ofReal f) (ofReal g) x y dual ∧
      0 < c_r ∧ 0 < c_f ∧ 1 < κ ∧
      (∀ k, ‖x (k + 1) - y (k + 1)‖ = c_r * κ ^ k) ∧
      (∀ k, f (x (k + 1)) + g (y (k + 1)) = c_f * κ ^ (2 * k)) ∧
      IsKKT (ofReal f) (ofReal g) 0 0 0 ∧
      ofReal f 0 + ofReal g 0 = 0 ∧ IsPrimalMinimizer (ofReal f) (ofReal g) 0 := by
  obtain ⟨κ, hκ, hfirst, hsecond, i, hi⟩ := expanding_data γ η ν hstrict hnonzero
  have hκpos : 0 < κ := zero_lt_one.trans hκ
  obtain ⟨hsymX, hsymY, U, hU⟩ := symmetry γ κ η ν hsym
  have hnorm (j : ZMod N) : ‖residual γ κ ν j‖ = ‖residual γ κ ν 0‖ := by
    have h := cyclicInner_eq_zeroPhase (residual γ κ ν) (residual γ κ ν) U hU j
    simp only [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (residual γ κ ν j), norm_nonneg (residual γ κ ν 0)]
  have hrpos : 0 < ‖residual γ κ ν 0‖ := by
    rw [← hnorm i]
    exact norm_pos_iff.mpr hi
  obtain ⟨αX, hαX, hselfX, hactiveX⟩ := cyclicSupport_activeForm
    (vertex γ κ η ν) (firstNormal γ κ η ν) hfirst hsymX
  obtain ⟨αY, hαY, hselfY, hactiveY⟩ := cyclicSupport_activeForm
    η (secondNormal γ κ ν) hsecond hsymY
  obtain ⟨f, hfpw, hf0, hfpos, hfray⟩ := maxSquareObjective_spec
    (vertex γ κ η ν) (firstNormal γ κ η ν) αX hαX hselfX hactiveX
  obtain ⟨g, hgpw, hg0, hgpos, hgray⟩ := maxSquareObjective_spec
    η (secondNormal γ κ ν) αY hαY hselfY hactiveY
  obtain ⟨htrajectory, hunique⟩ := supported_updates γ κ η ν f g hγ hκpos
    (fun t ht i ↦ (hfray t ht i).2) (fun t ht i ↦ (hgray t ht i).2)
  obtain ⟨hkkt, hvalue, hprimal⟩ := ofRealOriginOptimality f g hf0 hg0 hfpos hgpos
  refine ⟨f, g, sequence κ (vertex γ κ η ν), sequence κ η, sequence κ ν,
    ‖residual γ κ ν 0‖, αX / 2 + αY / 2, κ,
    hfpw, hgpw, htrajectory, hunique, hrpos, by positivity, hκ, ?_, ?_,
    hkkt, hvalue, hprimal⟩
  · intro k
    rw [sequence_succ hκpos.ne', sequence_succ hκpos.ne', ← smul_sub,
      vertex, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hκpos.le _), hnorm]
    exact mul_comm _ _
  · intro k
    rw [sequence_succ hκpos.ne', sequence_succ hκpos.ne',
      (hfray _ (pow_nonneg hκpos.le _) _).1, (hgray _ (pow_nonneg hκpos.le _) _).1]
    rw [Nat.mul_comm 2 k, pow_mul]
    ring

end ConsensusADMM.GeometricGrowth
