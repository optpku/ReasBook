/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.OrbitEnergy
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.GraphLimits
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

open Filter

namespace ADMM.ConvergenceProof

/-- The supremum norm squared is bounded by the coordinate square, also in
zero-dimensional spaces. -/
theorem norm_sq_le_coordinateSquare {m : ℕ} (x : Fin m → ℝ) :
    ‖x‖ ^ 2 ≤ coordinateSquare x := by
  classical
  cases isEmpty_or_nonempty (Fin m) with
  | inl hempty =>
    have hx : x = 0 := Subsingleton.elim x 0
    simp [hx, coordinateSquare]
  | inr _ =>
    obtain ⟨i, hi⟩ := (IsGreatest.pi_norm x).1
    have hterm : x i * x i ≤ coordinateSquare x := by
      unfold coordinateSquare dotProduct
      exact Finset.single_le_sum (fun j _ ↦ mul_self_nonneg (x j)) (Finset.mem_univ i)
    calc
      ‖x‖ ^ 2 = ‖x i‖ ^ 2 := (congrArg (fun r : ℝ ↦ r ^ 2) hi).symm
      _ = x i * x i := by rw [Real.norm_eq_abs, sq_abs, pow_two]
      _ ≤ coordinateSquare x := hterm

/-- Vanishing coordinate squares imply vector convergence to zero. -/
theorem tendsto_zero_of_coordinateSquare {m : ℕ} {x : ℕ → Fin m → ℝ}
    (h : Tendsto (fun k ↦ coordinateSquare (x k)) atTop (nhds 0)) :
    Tendsto x atTop (nhds 0) := by
  apply tendsto_zero_of_norm_sq
  exact squeeze_zero (fun k ↦ sq_nonneg _) (fun k ↦ norm_sq_le_coordinateSquare _) h

/-- The coordinate square is continuous along convergent finite vectors. -/
theorem coordinateSquare_tendsto {m : ℕ} {x : ℕ → Fin m → ℝ} {xBar : Fin m → ℝ}
    (hx : Tendsto x atTop (nhds xBar)) :
    Tendsto (fun k ↦ coordinateSquare (x k)) atTop (nhds (coordinateSquare xBar)) :=
  tendsto_dotProduct hx hx

/-- A coordinate-square bound on the two reduced states provides a convergent
common subsequence. -/
theorem state_exists_subsequence {m : ℕ} (η w : ℕ → Fin m → ℝ)
    (hbound : ∃ C : ℝ, ∀ k, coordinateSquare (η k) + coordinateSquare (w k) ≤ C) :
    ∃ ηBar wBar, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (η ∘ σ) atTop (nhds ηBar) ∧ Tendsto (w ∘ σ) atTop (nhds wBar) := by
  obtain ⟨C, hC⟩ := hbound
  have hnorm (k : ℕ) : ‖(η k, w k)‖ ≤ Real.sqrt C := by
    rw [Prod.norm_mk, max_le_iff]
    constructor
    · apply Real.le_sqrt_of_sq_le
      linarith [norm_sq_le_coordinateSquare (η k), coordinateSquare_nonneg (w k), hC k]
    · apply Real.le_sqrt_of_sq_le
      linarith [norm_sq_le_coordinateSquare (w k), coordinateSquare_nonneg (η k), hC k]
  have hmem : ∀ k, (η k, w k) ∈ Metric.closedBall (0 : (Fin m → ℝ) × (Fin m → ℝ))
      (Real.sqrt C) := by
    intro k
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm k
  obtain ⟨p, hp, σ, hσ, hlim⟩ := (isCompact_closedBall
    (0 : (Fin m → ℝ) × (Fin m → ℝ)) (Real.sqrt C)).tendsto_subseq hmem
  refine ⟨p.1, p.2, σ, hσ, ?_, ?_⟩
  · exact continuous_fst.continuousAt.tendsto.comp hlim
  · exact continuous_snd.continuousAt.tendsto.comp hlim

end ADMM.ConvergenceProof
