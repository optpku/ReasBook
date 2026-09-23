/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Optimization.DFP.WolfeCounterexample.ParameterizedPlanar
public import ReasLib.Optimization.DFP.PlanarConvergence
public import ReasLib.Analysis.Calculus.Gradient.HessianHolder
public import ReasLib.Optimization.DFP.WolfeCounterexample.AutomaticMatrixIdentityLiminf
/-!
# Strong-Wolfe counterexamples with a Hölder Hessian

The same realization satisfies the Wolfe conditions, the exact uniform Hessian
bounds, nonconvergence, and global one-half Hölder continuity of its Hessian.
-/

public section

open Filter
open scoped Topology

namespace DFP

/-- Helper for thm:main: the planar strong-Wolfe construction has a globally
one-half Hölder Hessian, with all properties attached to the same objective. -/
theorem existsPlanarStrongWolfeCounterexampleHolder
    {c₁ c₂ : ℝ} (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    ∃ c : StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
      ∃ C > 0, ∀ x y,
        ‖hessian c.iteration.objective x - hessian c.iteration.objective y‖ ≤
          C * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  apply existsPlanarStrongWolfeCounterexampleWithProperty
    (fun f _ ↦ ∃ C > 0, ∀ x y,
      ‖hessian f x - hessian f y‖ ≤ C * ‖x - y‖ ^ (1 / 2 : ℝ))
    _ hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
  intro curve
  obtain ⟨η, hη, C, hC, hHolder⟩ := PlanarConvergence.realizedObjectiveHessianHolder curve
  refine ⟨η, hη, ?_⟩
  intro ε₀ hε₀
  dsimp only
  intro Clim hClim Glim hGlim hGlimLimit
  refine ⟨C, hC, ?_⟩
  simpa only [hessian_def, EuclideanPlane.hessian_def] using
    hHolder ε₀ hε₀ Clim hClim Glim hGlim hGlimLimit

/-- Helper for cor:identity-initialization: a continuous linear change of
coordinates preserves existence of a positive global one-half Hölder constant. -/
theorem existsHessianHolderPullback
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} (hf : ContDiff ℝ 2 f) (L : E ≃L[ℝ] F)
    (h : ∃ C > 0, ∀ x y, ‖hessian f x - hessian f y‖ ≤ C * ‖x - y‖ ^ (1 / 2 : ℝ)) :
    ∃ C > 0, ∀ x y,
      ‖hessian (f ∘ L) x - hessian (f ∘ L) y‖ ≤ C * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, h⟩ := h
  let D := ‖L.toContinuousLinearMap‖ ^ 2 * C * ‖L.toContinuousLinearMap‖ ^ (1 / 2 : ℝ)
  have hD : 0 ≤ D := by positivity
  have hDpos : 0 < D + 1 := by positivity
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  refine ⟨D + 1, hDpos, ?_⟩
  intro x y
  apply (hessianHolder_comp_continuousLinearEquiv hf L hC.le hhalf h x y).trans
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
    (Real.rpow_nonneg (norm_nonneg _) _)

/-- Helper for thm:main: in every dimension at least two, one classical strong-Wolfe
counterexample has the exact Hessian bounds and a globally one-half Hölder Hessian. -/
theorem existsStrongWolfeCounterexampleHolder_of_dimension_ge_two
    (n : ℕ) (hn : 2 ≤ n) {c₁ c₂ : ℝ}
    (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    ∃ c : StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂,
      ∃ C > 0, ∀ x y,
        ‖hessian c.iteration.objective x - hessian c.iteration.objective y‖ ≤
          C * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  classical
  obtain ⟨c, C, hC, hHolder⟩ := existsPlanarStrongWolfeCounterexampleHolder
    hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
  have hlower : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hupper : (1 : ℝ) ≤ 3 / 2 := by norm_num
  obtain ⟨d, hd, _⟩ := c.orthogonalSumWithObjective (κ := Fin (n - 2)) hlower hupper
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hDHolder : ∀ x y,
      ‖hessian d.iteration.objective x - hessian d.iteration.objective y‖ ≤
        C * ‖x - y‖ ^ (1 / 2 : ℝ) := by
    rw [hd, DFP.OrthogonalSum.objective_eq]
    exact EuclideanSpace.OrthogonalSum.Gradient.hessianHolder_objective
      c.objectiveContDiff hC.le hhalf hHolder
  have hdim : 2 + (n - 2) = n := by omega
  let e : Fin n ≃ Fin 2 ⊕ Fin (n - 2) :=
    (finCongr hdim.symm).trans finSumFinEquiv.symm
  let Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2 ⊕ Fin (n - 2)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  have hupperPos : (0 : ℝ) ≤ 3 / 2 := by norm_num
  obtain ⟨result, hresult, _⟩ := d.pullbackWithObjective Q hhalf hupperPos
  refine ⟨result, ?_⟩
  rw [hresult]
  exact existsHessianHolderPullback d.objectiveContDiff Q.toContinuousLinearEquiv
    ⟨C, hC, hDHolder⟩

/-- Corollary 2 (`cor:identity-initialization`): identity-initialized classical DFP fails to
converge in every dimension at least two even with a global one-half Hölder
Hessian and positive ordered uniform Hessian bounds. -/
theorem existsMatrixIdentityLiminfStrongWolfeHolder
    (n : ℕ) (hn : 2 ≤ n) {c₁ c₂ : ℝ}
    (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    ∃ m M : ℝ, ∃ c : WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate
      n m M c₁ c₂, ∃ C > 0, ∀ x y,
        ‖hessian c.iteration.objective x - hessian c.iteration.objective y‖ ≤
          C * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨c, hHolder⟩ := existsStrongWolfeCounterexampleHolder_of_dimension_ge_two n hn
    hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
  obtain ⟨L, a, b, q, ha, hb, hq, hfactor, hlower, hupper, hgradient⟩ :=
    WolfeCounterexample.factorAndBounds_of_initialPosDef c.initialInverseHessianPosDef
  have hc₁₂ : c₁ < c₂ := hc₁_lt_two_thirds.trans_le hc₂_ge_two_thirds
  obtain ⟨d, hd⟩ := WolfeCounterexample.matrixIdentityLiminfStrongWolfeWithObjective
    hn c L hfactor ha hb hq hc₁_pos hc₁₂ hc₂_lt_one hlower hupper hgradient
  refine ⟨(1 / 2 : ℝ) * a, (3 / 2 : ℝ) * b, d, ?_⟩
  rw [hd]
  exact existsHessianHolderPullback c.objectiveContDiff L hHolder

end DFP
