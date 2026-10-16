module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.SupportedObjectives
public import glowinski_admm_counterexample.ReasLib.Convex.SmoothInterpolation

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM.SmoothCycle

variable {N : ℕ} [NeZero N] {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Smooth interpolation of a strict cyclic support family.  Adjoining the
origin keeps the global minimum at zero while all phases receive one value. -/
theorem interpolate (p n : ZMod N → E)
    (supports : ProjectionCycle.StrictNonselfSupports p n)
    (symmetry : ProjectionCycle.HasOrthogonalCyclicSymmetry p n) :
    ∃ f : E → ℝ, ∃ μ α : ℝ, ∃ L : NNReal,
      0 < μ ∧ 0 < α ∧ StrongConvexOn Set.univ μ f ∧ ContDiff ℝ 1 f ∧
      LipschitzWith L (fderiv ℝ f) ∧ f 0 = 0 ∧
      (∀ x, μ/2 * ‖x‖^2 ≤ f x) ∧
      (∀ i, f (p i) = α) ∧
      (∀ i x, f (p i) + inner ℝ (n i) (x-p i) ≤ f x) := by
  classical
  obtain ⟨a, ha, hself, hactive⟩ := cyclicSupport_activeForm p n supports symmetry
  let z : Option (ZMod N) → E := Option.elim' 0 p
  let q : Option (ZMod N) → E := Option.elim' 0 n
  let φ : Option (ZMod N) → ℝ := Option.elim' 0 (fun _ ↦ a/2)
  have hstrict (i j : Option (ZMod N)) (hij : i ≠ j) :
      0 < φ i - φ j - inner ℝ (q j) (z i-z j) := by
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j =>
        simp only [φ, q, z, Option.elim', zero_sub, inner_neg_right, hself]
        linarith
    | some i =>
      cases j with
      | none =>
        simp only [φ, q, z, Option.elim', sub_zero, inner_zero_left]
        linarith
      | some j =>
        have hji : i ≠ j := fun h ↦ hij (congrArg some h)
        have hs := (supports j).2 i hji
        simp only [φ, q, z, Option.elim', sub_self, zero_sub]
        simp only [inner_sub_right] at hs ⊢
        linarith
  obtain ⟨f, μ, L, hf⟩ := SmoothInterpolation.exists_strongInterpolation z q φ none
    rfl rfl rfl hstrict
  refine ⟨f, μ, a/2, L, hf.positive, by positivity, hf.stronglyConvex,
    hf.contDiff, hf.lipschitz, hf.zero, hf.lower, ?_, ?_⟩
  · intro i
    exact hf.values (some i)
  · intro i x
    exact hf.supports (some i) x

/-- Strict cyclic projection data admit smooth strongly convex objectives with
Lipschitz derivatives, a positive constant objective along their ADMM orbit,
and a unique feasible primal minimizer at zero. -/
theorem counterexample (γ : ℝ) (η ν : ZMod N → E) (hγ : 0 < γ)
    (hstrict : IsStrictProjectionCycle γ η ν)
    (hsym : ProjectionCycle.HasOrthogonalCyclicSymmetry η ν) :
    ∃ f g : E → ℝ, ∃ μf μg : ℝ, ∃ Lf Lg : NNReal,
      ∃ x y dual : ℕ → E, ∃ c_f : ℝ,
        0 < μf ∧ 0 < μg ∧
        StrongConvexOn Set.univ μf f ∧ StrongConvexOn Set.univ μg g ∧
        ContDiff ℝ 1 f ∧ ContDiff ℝ 1 g ∧
        LipschitzWith Lf (fderiv ℝ f) ∧ LipschitzWith Lg (fderiv ℝ g) ∧
        IsTrajectory γ (ofReal f) (ofReal g) x y dual ∧
        HasUniqueUpdates (ofReal f) (ofReal g) x y dual ∧
        Function.Periodic (fun k ↦ (x (k+1), y (k+1), dual (k+1))) N ∧
        0 < c_f ∧ (∀ k, f (x (k+1)) + g (y (k+1)) = c_f) ∧
        IsKKT (ofReal f) (ofReal g) 0 0 0 ∧
        ofReal f 0 + ofReal g 0 = 0 ∧
        IsPrimalMinimizer (ofReal f) (ofReal g) 0 ∧
        ∀ z, IsPrimalMinimizer (ofReal f) (ofReal g) z → z = 0 := by
  obtain ⟨hsymX, hsymY⟩ := projectionCycleSupportFamilies_hasOrthogonalCyclicSymmetry
    γ η ν hsym
  obtain ⟨f, μf, αf, Lf, hμf, hαf, hcf, hdf, hlf, hf0, hf_lower, hf_value, hf_support⟩ :=
    interpolate (ProjectionCycle.xVertex γ η ν) (ProjectionCycle.firstNormal γ η ν)
      hstrict.1 hsymX
  obtain ⟨g, μg, αg, Lg, hμg, hαg, hcg, hdg, hlg, hg0, hg_lower, hg_value, hg_support⟩ :=
    interpolate η (ProjectionCycle.secondNormal γ ν) hstrict.2 hsymY
  obtain ⟨trajectory, updates⟩ := ofRealSupportedCycle_updates γ η ν f g hγ
    hf_support hg_support
  have periodic : Function.Periodic
      (fun k ↦ (ProjectionCycle.xSequence γ η ν (k+1),
        ProjectionCycle.ySequence η (k+1), ProjectionCycle.dualSequence ν (k+1))) N := by
    intro k
    have phase : ((k+N : ℕ) : ZMod N) = (k : ZMod N) := by simp
    simp only [ProjectionCycle.xSequence_succ, ProjectionCycle.ySequence_succ,
      ProjectionCycle.dualSequence_succ, phase]
  have value (k : ℕ) : f (ProjectionCycle.xSequence γ η ν (k+1)) +
      g (ProjectionCycle.ySequence η (k+1)) = αf + αg := by
    simp only [ProjectionCycle.xSequence_succ, ProjectionCycle.ySequence_succ,
      hf_value, hg_value]
  have hf_nonneg (z : E) : 0 ≤ f z :=
    (mul_nonneg (by positivity : 0 ≤ μf/2) (sq_nonneg _)).trans (hf_lower z)
  have hg_nonneg (z : E) : 0 ≤ g z :=
    (mul_nonneg (by positivity : 0 ≤ μg/2) (sq_nonneg _)).trans (hg_lower z)
  obtain ⟨kkt, zero_value, primal⟩ := ofRealOriginOptimality f g hf0 hg0 hf_nonneg hg_nonneg
  refine ⟨f, g, μf, μg, Lf, Lg, ProjectionCycle.xSequence γ η ν,
    ProjectionCycle.ySequence η, ProjectionCycle.dualSequence ν, αf+αg,
    hμf, hμg, hcf, hcg, hdf, hdg, hlf, hlg, trajectory, updates, periodic,
    add_pos hαf hαg, value, kkt, zero_value, primal, ?_⟩
  intro z hz
  have hmin := hz 0
  have hsum : f z + g z ≤ 0 := by
    simpa only [ofReal_apply, hf0, hg0, EReal.coe_zero, add_zero,
      ← EReal.coe_add, ← EReal.coe_zero, EReal.coe_le_coe_iff] using hmin
  have hn : ‖z‖^2 = 0 := by
    nlinarith [hf_lower z, hg_nonneg z, sq_nonneg ‖z‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

end ConsensusADMM.SmoothCycle
