module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.StrictProjectionCycle
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UniformConvergence
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycleTrajectory
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ConsensusBridge
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Strictification.Support
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Strictification.Compression
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Strictification.Auxiliary
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Strictification.Perturbation

@[expose] public section

namespace ConsensusADMM.IsProjectionCycle

open ConsensusADMM ProjectionCycle

universe u

variable {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nontrivial projection cycle with one strict block can be strictified in dimension
at most `2 * N`, while preserving orthogonal cyclic symmetry. -/
theorem strictifyOneBlock (γ : ℝ) (η ν : ZMod N → E) (hN : 2 ≤ N)
    (hγ : 0 < γ) (hγtwo : γ < 2) (hcycle : ConsensusADMM.IsProjectionCycle γ η ν)
    (hnonzero : ∃ i, residual γ ν i ≠ 0) (hstrict : HasStrictBlock γ η ν) :
    ∃ d : ℕ, d ≤ 2 * N ∧
      ∃ eta' nu' : ZMod N → EuclideanSpace ℝ (Fin d),
        IsStrictProjectionCycle γ eta' nu' ∧
          (∃ i, residual γ nu' i ≠ 0) ∧
          (HasOrthogonalCyclicSymmetry η ν → HasOrthogonalCyclicSymmetry eta' nu') := by
  classical
  letI : NeZero N := ⟨by omega⟩
  -- A sufficiently small positive scale preserves the original strict block.
  have positive_scale {P : ℝ → Prop} (h : ∀ᶠ ε in nhds (0 : ℝ), P ε) :
      ∃ ε : ℝ, ε ≠ 0 ∧ P ε := by
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp h
    refine ⟨δ / 2, ne_of_gt (by positivity), hball ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  -- The two auxiliary constructions fill the weak block. Their other supports
  -- are arbitrary, which is harmless after the common scale is made small.
  obtain ⟨η₁, ν₁, hsym₁, ε, hε, hpaired⟩ :
      ∃ η₁ ν₁ : ZMod N → EuclideanSpace ℝ (ZMod N),
        HasOrthogonalCyclicSymmetry η₁ ν₁ ∧ ∃ ε : ℝ, ε ≠ 0 ∧
          IsStrictProjectionCycle γ
            (fun i ↦ scaledPair ε (η i) (η₁ i))
            (fun i ↦ scaledPair ε (ν i) (ν₁ i)) := by
    rcases hstrict with hfirst | hsecond
    · let η₁ := auxiliarySecondEta (N := N) γ
      let ν₁ := auxiliaryNu (N := N) γ
      have hpreserve := strictSupports_scaledPair_eventually
        (xVertex γ η₁ ν₁) (firstNormal γ η₁ ν₁) hfirst
      obtain ⟨ε, hε, hεstrict⟩ := positive_scale hpreserve
      refine ⟨η₁, ν₁, auxiliary_second_symmetry γ, ε, hε, ?_⟩
      have hx := funext fun i ↦ (cycleVectors_scaledPair γ ε η ν η₁ ν₁ i).2.1
      have ha := funext fun i ↦ (cycleVectors_scaledPair γ ε η ν η₁ ν₁ i).2.2.1
      have hc := funext fun i ↦ (cycleVectors_scaledPair γ ε η ν η₁ ν₁ i).2.2.2
      constructor
      · rw [hx, ha]
        exact hεstrict
      · rw [hc]
        exact strictSupports_scaledPair hcycle.2 (auxiliary_second_strict hγ hγtwo) hε
    · let η₁ := auxiliaryFirstEta (N := N) γ
      let ν₁ := auxiliaryNu (N := N) γ
      have hpreserve := strictSupports_scaledPair_eventually η₁ (secondNormal γ ν₁) hsecond
      obtain ⟨ε, hε, hεstrict⟩ := positive_scale hpreserve
      refine ⟨η₁, ν₁, auxiliary_first_symmetry γ, ε, hε, ?_⟩
      have hx := funext fun i ↦ (cycleVectors_scaledPair γ ε η ν η₁ ν₁ i).2.1
      have ha := funext fun i ↦ (cycleVectors_scaledPair γ ε η ν η₁ ν₁ i).2.2.1
      have hc := funext fun i ↦ (cycleVectors_scaledPair γ ε η ν η₁ ν₁ i).2.2.2
      constructor
      · rw [hx, ha]
        exact strictSupports_scaledPair hcycle.1 (auxiliary_first_strict hγ) hε
      · rw [hc]
        exact hεstrict
  -- Restrict the paired data to their joint span and choose orthonormal
  -- coordinates. This also transports a phase map whenever one was supplied.
  obtain ⟨d, hd, η', ν', hstrict', hnonzero', hsym'⟩ :=
    strictCycle_compress γ (fun i ↦ scaledPair ε (η i) (η₁ i))
      (fun i ↦ scaledPair ε (ν i) (ν₁ i)) hpaired
      (residual_scaledPair_nonzero γ ε ν ν₁ hnonzero)
  exact ⟨d, hd, η', ν', hstrict', hnonzero',
    fun hsym ↦ hsym' (symmetry_scaledPair ε hsym hsym₁)⟩

/-- A nontrivial projection cycle with one strict block lies strictly above the
uniform-convergence endpoint. -/
theorem uniformConvergenceEndpoint_lt (γ : ℝ) (η ν : ZMod N → E) (hN : 2 ≤ N)
    (hγ : 0 < γ) (hγtwo : γ < 2) (hcycle : ConsensusADMM.IsProjectionCycle γ η ν)
    (hnonzero : ∃ i, residual γ ν i ≠ 0) (hstrict : HasStrictBlock γ η ν) :
    ADMM.uniformConvergenceEndpoint < γ := by
  classical
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨d, _, η', ν', hstrict', hnonzero', _⟩ :=
    strictifyOneBlock γ η ν hN hγ hγtwo hcycle hnonzero hstrict
  obtain ⟨t, htpos, htγ, htstrict, htnonzero⟩ :=
    strictCycle_exists_smaller hγ hstrict' hnonzero'
  have hfail := not_uniformConvergenceAt t η' ν' hN htpos
    htstrict.isProjectionCycle htnonzero
  have hbound : ADMM.uniformConvergenceEndpoint ≤ t := by
    rw [ADMM.uniformConvergenceEndpoint_def]
    let S := {c : ℝ | 0 < c ∧ ∀ s, 0 < s → s < c → ADMM.UniformConvergenceAt s}
    change sSup S ≤ t
    by_cases hS : S.Nonempty
    · apply csSup_le hS
      intro c hc
      by_contra hct
      exact hfail (hc.2 t htpos (lt_of_not_ge hct))
    · rw [Set.not_nonempty_iff_eq_empty.mp hS, Real.sSup_empty]
      exact htpos.le
  exact hbound.trans_lt htγ

end ConsensusADMM.IsProjectionCycle
