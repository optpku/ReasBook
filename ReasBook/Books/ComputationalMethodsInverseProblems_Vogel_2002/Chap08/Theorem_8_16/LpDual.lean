/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.LpDual.ConverseHolder
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.DualPairBidual

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace VariationalRegularization.LpDual

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  (p q : ENNReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Every bounded linear functional on finite `Lp`, for `1 < p < ∞`, is
integration against a function in its conjugate space. -/
theorem pairing_surjective (hp : p ≠ ∞) (hq : q ≠ ∞)
    (hpq : p.toReal.HolderConjugate q.toReal) :
    Function.Surjective ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p) := by
  intro ℓ
  obtain ⟨g, hgm, hg, hrep⟩ := exists_integrable_density μ p hp ℓ
  have hgq : MemLp g q μ := density_memLp_conjugate μ p q hp hq hpq ℓ hgm hg hrep
  let J : StrongDual ℝ (Lp ℝ p μ) :=
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p (hgq.toLp g)
  refine ⟨hgq.toLp g, ?_⟩
  have hsimple : ∀ f : SimpleFunc α ℝ,
      J ((f.memLp_of_isFiniteMeasure p μ).toLp f) =
        ℓ ((f.memLp_of_isFiniteMeasure p μ).toLp f) := by
    intro f
    rw [functional_eq_integral_simple μ p ℓ hg hrep f]
    change (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p (hgq.toLp g)
      ((f.memLp_of_isFiniteMeasure p μ).toLp f) = _
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hgq.coeFn_toLp, (f.memLp_of_isFiniteMeasure p μ).coeFn_toLp]
      with x hx hy
    simpa only [ContinuousLinearMap.mul_apply', hx, hy] using mul_comm (g x) (f x)
  apply ContinuousLinearMap.ext
  intro f
  refine (Lp.simpleFunc.denseRange (E := ℝ) (μ := μ) hp).induction_on
    (p := fun f ↦ J f = ℓ f) f (isClosed_eq J.continuous ℓ.continuous) ?_
  intro s
  let t := Lp.simpleFunc.toSimpleFunc s
  have hs : ((t.memLp_of_isFiniteMeasure p μ).toLp t : Lp ℝ p μ) =
      (s : Lp ℝ p μ) := by
    have h := congrArg (fun t : Lp.simpleFunc ℝ p μ ↦ (t : Lp ℝ p μ))
      (Lp.simpleFunc.toLp_toSimpleFunc s)
    simpa only [Lp.simpleFunc.toLp_eq_toLp] using h
  rw [← hs]
  exact hsimple t

/-- Two applications of finite-measure `Lp` duality fill the bidual. -/
theorem inclusionInDoubleDualWeak_range_isClosed (hp : p ≠ ∞) (hq : q ≠ ∞)
    (hpq : p.toReal.HolderConjugate q.toReal) :
    IsClosed (Set.range (NormedSpace.inclusionInDoubleDualWeak ℝ (Lp ℝ p μ))) := by
  apply BVCompactness.lp_inclusionInDoubleDualWeak_range_isClosed_of_pairingSurjective μ p q
  · exact pairing_surjective μ q p hq hp hpq.symm
  · exact pairing_surjective μ p q hp hq hpq

end VariationalRegularization.LpDual
