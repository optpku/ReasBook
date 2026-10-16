module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.GraphLimits
public import Mathlib.Topology.Algebra.Module.Basic

@[expose] public section

open Filter

namespace ADMM.ConvergenceProof

/-- A convergent reduced ADMM trajectory satisfies feasibility and both
stationarity conditions at its limit. The proof uses the multiplier recurrence
and closed subgradient graphs, so no continuity claim about extended-real
objectives is needed. -/
theorem reduced_limit_stationary {m : ℕ} {f g : (Fin m → ℝ) → EReal}
    (hf : IsClosedProperConvex f) (hg : IsClosedProperConvex g)
    {q v u : ℕ → Fin m → ℝ} {qBar vBar uBar : Fin m → ℝ}
    {γ : ℝ} (hγ : γ ≠ 0)
    (hrec : ∀ k, u (k + 1) = u k + γ • (q (k + 1) + v (k + 1)))
    (hfirst : ∀ k, IsSubgradientAt f (-v k - u k - q (k + 1)) (q (k + 1)))
    (hsecond : ∀ k, IsSubgradientAt g (-q (k + 1) - u k - v (k + 1)) (v (k + 1)))
    (hq : Tendsto q atTop (nhds qBar)) (hv : Tendsto v atTop (nhds vBar))
    (hu : Tendsto u atTop (nhds uBar)) :
    qBar + vBar = 0 ∧ IsSubgradientAt f (-uBar) qBar ∧
      IsSubgradientAt g (-uBar) vBar := by
  have hqs : Tendsto (fun k ↦ q (k + 1)) atTop (nhds qBar) :=
    hq.comp (tendsto_add_atTop_nat 1)
  have hvs : Tendsto (fun k ↦ v (k + 1)) atTop (nhds vBar) :=
    hv.comp (tendsto_add_atTop_nat 1)
  have hus : Tendsto (fun k ↦ u (k + 1)) atTop (nhds uBar) :=
    hu.comp (tendsto_add_atTop_nat 1)
  have hrecLimit : Tendsto (fun k ↦ u (k + 1)) atTop
      (nhds (uBar + γ • (qBar + vBar))) := by
    exact (hu.add ((hqs.add hvs).const_smul γ)).congr
      (fun k ↦ (hrec k).symm)
  have hzero : γ • (qBar + vBar) = 0 := by
    have heq := tendsto_nhds_unique hrecLimit hus
    exact add_left_cancel (show uBar + γ • (qBar + vBar) = uBar + 0 by simpa using heq)
  have hfeas : qBar + vBar = 0 := (smul_eq_zero.mp hzero).resolve_left hγ
  have hnormFirst : -vBar - uBar - qBar = -uBar := by
    have hvBar : vBar = -qBar := eq_neg_of_add_eq_zero_right hfeas
    rw [hvBar]
    module
  have hnormSecond : -qBar - uBar - vBar = -uBar := by
    have hvBar : vBar = -qBar := eq_neg_of_add_eq_zero_right hfeas
    rw [hvBar]
    module
  refine ⟨hfeas, ?_, ?_⟩
  · have h := subgradient_of_tendsto hf hfirst hqs ((hv.neg.sub hu).sub hqs)
    rwa [hnormFirst] at h
  · have h := subgradient_of_tendsto hg hsecond hvs ((hqs.neg.sub hu).sub hvs)
    rwa [hnormSecond] at h

/-- Along a convergent reduced orbit, the individual objective values converge
at the generated points, including when the limit is a domain boundary. -/
theorem reduced_objectives_tendsto {m : ℕ} {f g : (Fin m → ℝ) → EReal}
    (hf : IsClosedProperConvex f) (hg : IsClosedProperConvex g)
    {q v u : ℕ → Fin m → ℝ} {qBar vBar uBar : Fin m → ℝ}
    (hfirst : ∀ k, IsSubgradientAt f (-v k - u k - q (k + 1)) (q (k + 1)))
    (hsecond : ∀ k, IsSubgradientAt g (-q (k + 1) - u k - v (k + 1)) (v (k + 1)))
    (hq : Tendsto q atTop (nhds qBar)) (hv : Tendsto v atTop (nhds vBar))
    (hu : Tendsto u atTop (nhds uBar)) :
    Tendsto (fun k ↦ f (q k)) atTop (nhds (f qBar)) ∧
      Tendsto (fun k ↦ g (v k)) atTop (nhds (g vBar)) := by
  have hqs : Tendsto (fun k ↦ q (k + 1)) atTop (nhds qBar) :=
    hq.comp (tendsto_add_atTop_nat 1)
  have hvs : Tendsto (fun k ↦ v (k + 1)) atTop (nhds vBar) :=
    hv.comp (tendsto_add_atTop_nat 1)
  have hfirstLimit := subgradient_of_tendsto hf hfirst hqs ((hv.neg.sub hu).sub hqs)
  have hsecondLimit := subgradient_of_tendsto hg hsecond hvs ((hqs.neg.sub hu).sub hvs)
  constructor
  · apply (tendsto_add_atTop_iff_nat 1).1
    exact subgradient_ereal_value_tendsto hfirst hfirstLimit hqs ((hv.neg.sub hu).sub hqs)
  · apply (tendsto_add_atTop_iff_nat 1).1
    exact subgradient_ereal_value_tendsto hsecond hsecondLimit hvs ((hqs.neg.sub hu).sub hvs)

end ADMM.ConvergenceProof
