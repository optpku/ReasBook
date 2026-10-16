module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.StrictProjectionCycle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

open scoped RealInnerProductSpace
open Filter

namespace ConsensusADMM.ProjectionCycle

universe u
variable {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every support inequality is continuous in the positive relaxation factor. -/
theorem strictCycle_eventually {η ν : ZMod N → E} {γ : ℝ} [NeZero N]
    (hγ : γ ≠ 0) (hstrict : IsStrictProjectionCycle γ η ν) :
    ∀ᶠ t in nhds γ, IsStrictProjectionCycle t η ν := by
  have hr (i : ZMod N) : ContinuousAt (fun t : ℝ ↦ residual t ν i) γ :=
    (continuousAt_id.inv₀ hγ).smul continuousAt_const
  have hx (i : ZMod N) : ContinuousAt (fun t : ℝ ↦ xVertex t η ν i) γ :=
    continuousAt_const.add (hr i)
  have ha (i : ZMod N) : ContinuousAt (fun t : ℝ ↦ firstNormal t η ν i) γ :=
    continuousAt_const.sub (hx i)
  have hc (i : ZMod N) : ContinuousAt (fun t : ℝ ↦ secondNormal t ν i) γ :=
    continuousAt_const.add (hr i)
  have hfirst : ∀ᶠ t in nhds γ,
      StrictNonselfSupports (xVertex t η ν) (firstNormal t η ν) := by
    apply (Filter.eventually_all).mpr
    intro i
    have hzero := ((ha i).inner (hx i)).eventually (lt_mem_nhds (hstrict.1 i).1)
    have hpairs : ∀ᶠ t in nhds γ, ∀ j, j ≠ i →
        0 < inner ℝ (firstNormal t η ν i) (xVertex t η ν i - xVertex t η ν j) := by
      apply (Filter.eventually_all).mpr
      intro j
      by_cases hji : j = i
      · exact Filter.Eventually.of_forall fun _ hj ↦ (hj hji).elim
      · exact (((ha i).inner ((hx i).sub (hx j))).eventually
          (lt_mem_nhds ((hstrict.1 i).2 j hji))).mono fun _ h _ ↦ h
    exact hzero.and hpairs
  have hsecond : ∀ᶠ t in nhds γ, StrictNonselfSupports η (secondNormal t ν) := by
    apply (Filter.eventually_all).mpr
    intro i
    have hzero := ((hc i).inner continuousAt_const).eventually
      (lt_mem_nhds (hstrict.2 i).1)
    have hpairs : ∀ᶠ t in nhds γ, ∀ j, j ≠ i →
        0 < inner ℝ (secondNormal t ν i) (η i - η j) := by
      apply (Filter.eventually_all).mpr
      intro j
      by_cases hji : j = i
      · exact Filter.Eventually.of_forall fun _ hj ↦ (hj hji).elim
      · exact (((hc i).inner continuousAt_const).eventually
          (lt_mem_nhds ((hstrict.2 i).2 j hji))).mono fun _ h _ ↦ h
    exact hzero.and hpairs
  exact hfirst.and hsecond

/-- Strict cycles persist at a smaller positive factor; their nonzero residual
survives because the multiplier difference is unchanged. -/
theorem strictCycle_exists_smaller {η ν : ZMod N → E} {γ : ℝ} [NeZero N]
    (hγ : 0 < γ) (hstrict : IsStrictProjectionCycle γ η ν)
    (hnonzero : ∃ i, residual γ ν i ≠ 0) :
    ∃ t, 0 < t ∧ t < γ ∧ IsStrictProjectionCycle t η ν ∧
      ∃ i, residual t ν i ≠ 0 := by
  have hevent := (strictCycle_eventually hγ.ne' hstrict).and (lt_mem_nhds hγ)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let t := γ - min ε γ / 2
  have hm : 0 < min ε γ := lt_min hε hγ
  have htpos : 0 < t := by dsimp [t]; nlinarith [min_le_right ε γ]
  have htlt : t < γ := by dsimp [t]; linarith
  have hdist : dist t γ < ε := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr htlt)]
    dsimp [t]
    nlinarith [min_le_left ε γ]
  refine ⟨t, htpos, htlt, (hball hdist).1, ?_⟩
  obtain ⟨i, hi⟩ := hnonzero
  refine ⟨i, ?_⟩
  intro hz
  have hd : ν i - ν (i - 1) = 0 :=
    (smul_eq_zero.mp hz).resolve_left (inv_ne_zero htpos.ne')
  exact hi (by simp [residual, hd])

/-- A finite collection of positive margins remains positive under sufficiently
small common additive perturbations, regardless of the perturbation signs. -/
theorem finite_positive_perturbation {ι : Type*} [Finite ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, 0 < a i + ε * b i := by
  have hevent : ∀ᶠ ε in nhds (0 : ℝ), ∀ i, 0 < a i + ε * b i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).eventually
      (by simpa using lt_mem_nhds (ha i))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨δ / 2, by positivity, hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  linarith

end ConsensusADMM.ProjectionCycle
