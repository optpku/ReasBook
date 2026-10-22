/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Theorem_6_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Corollary_12_31

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient InnerProductSpace Pointwise Set

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {K : Set H}
variable (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
variable (hK_convex : Convex ℝ K)

private theorem isChebyshev_K
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K) :
    IsChebyshev K :=
  isChebyshev_of_nonempty_isClosed_convex hK_nonempty hK_closed hK_convex

private theorem polarCone_nonempty : (Kᵒ⊖ : Set H).Nonempty := by
  rw [Set.polarCone_eq_innerDual_neg]
  simpa [Set.negativePolar] using Set.negativePolar_nonempty K

private theorem polarCone_isClosed : IsClosed (Kᵒ⊖ : Set H) := by
  rw [Set.polarCone_eq_innerDual_neg]
  simpa [Set.negativePolar] using Set.negativePolar_isClosed K

private theorem polarCone_convex : Convex ℝ (Kᵒ⊖ : Set H) := by
  rw [Set.polarCone_eq_innerDual_neg]
  simpa [Set.negativePolar] using Set.negativePolar_convex K

private theorem isChebyshev_polarCone
    (_ : K.Nonempty) (_ : IsClosed K) (_ : Convex ℝ K) :
    IsChebyshev (Kᵒ⊖ : Set H) :=
  isChebyshev_of_nonempty_isClosed_convex
    polarCone_nonempty polarCone_isClosed polarCone_convex

local notation "Pₖ" => projectionPoint K (isChebyshev_K hK_nonempty hK_closed hK_convex)
local notation "Pᵒ⊖" =>
  projectionPoint (Kᵒ⊖ : Set H) (isChebyshev_polarCone hK_nonempty hK_closed hK_convex)

/-- The residual of the projection onto the polar cone is the projection onto `K`. -/
theorem sub_projectionPoint_polarCone_eq_projectionPoint (hK_cone : IsCone K) (x : H) :
    x - Pᵒ⊖ x = Pₖ x := by
  let coneK : ConvexCone ℝ H := hK_convex.toCone K
  have htoCone : (coneK : Set H) = K := by
    ext y
    constructor
    · intro hy
      rcases hK_convex.mem_toCone.mp hy with ⟨c, hc, z, hz, rfl⟩
      rw [isCone_iff] at hK_cone
      exact hK_cone.symm ▸ Set.mem_smul.mpr ⟨c, hc, z, hz, rfl⟩
    · intro hy
      exact hK_convex.subset_toCone hy
  have hconeK_nonempty : (coneK : Set H).Nonempty := by
    simpa [htoCone] using hK_nonempty
  have hconeK_closed : IsClosed (coneK : Set H) := by
    simpa [htoCone] using hK_closed
  classical
  let hKp : ∃ C : ProperCone ℝ H, (C : ConvexCone ℝ H) = coneK :=
    CanLift.prf coneK ⟨hconeK_nonempty, hconeK_closed⟩
  let Kp : ProperCone ℝ H := Classical.choose hKp
  have hKp_set : (Kp : Set H) = K := by
    ext y
    change y ∈ ((Kp : ConvexCone ℝ H) : Set H) ↔ y ∈ K
    rw [Classical.choose_spec hKp, htoCone]
  have hpolar_eq : Set.negativePolar (Kp : Set H) = (Kᵒ⊖) := by
    simpa [Set.negativePolar, hKp_set] using (Set.polarCone_eq_innerDual_neg K).symm
  have hbest :
      IsBestApproximation x K
        (projectionPoint (Kp : Set H) (isChebyshev_of_properCone Kp) x) := by
    refine ⟨?_, ?_⟩
    · rw [← hKp_set]
      exact
        (projectionPoint_isBestApproximation
          (Kp : Set H) (isChebyshev_of_properCone Kp) x).1
    · rw [← hKp_set]
      exact
        (projectionPoint_isBestApproximation
          (Kp : Set H) (isChebyshev_of_properCone Kp) x).2
  have hproj_eq :
      projectionPoint (Kp : Set H) (isChebyshev_of_properCone Kp) x = Pₖ x := by
    exact
      eq_projectionPoint_of_isBestApproximation K
        (isChebyshev_K hK_nonempty hK_closed hK_convex)
        hbest
  have hpolar_best :
      IsBestApproximation x (Kᵒ⊖)
        (projectionPoint (Set.negativePolar (Kp : Set H)) (isChebyshev_negativePolar Kp) x) := by
    refine ⟨?_, ?_⟩
    · rw [← hpolar_eq]
      exact
        (projectionPoint_isBestApproximation
          (Set.negativePolar (Kp : Set H)) (isChebyshev_negativePolar Kp) x).1
    · rw [← hpolar_eq]
      exact
        (projectionPoint_isBestApproximation
          (Set.negativePolar (Kp : Set H)) (isChebyshev_negativePolar Kp) x).2
  have hpolar_proj_eq :
      projectionPoint
          (Set.negativePolar (Kp : Set H)) (isChebyshev_negativePolar Kp) x =
        Pᵒ⊖ x := by
    exact
      eq_projectionPoint_of_isBestApproximation
        (Kᵒ⊖)
        (isChebyshev_polarCone hK_nonempty hK_closed hK_convex)
        hpolar_best
  have hdecomp :
      x = Pₖ x + Pᵒ⊖ x := by
    calc
      x =
          projectionPoint (Kp : Set H) (isChebyshev_of_properCone Kp) x +
            projectionPoint (Set.negativePolar (Kp : Set H)) (isChebyshev_negativePolar Kp) x := by
        simpa using eq_projectionPoint_add_projectionPoint_negativePolar Kp x
      _ =
          Pₖ x + Pᵒ⊖ x := by
        rw [hproj_eq, hpolar_proj_eq]
  have hsub :
      x - Pᵒ⊖ x = (Pₖ x + Pᵒ⊖ x) - Pᵒ⊖ x := by
    exact
      congrArg (fun z : H ↦ z - Pᵒ⊖ x) hdecomp
  calc
    x - Pᵒ⊖ x = (Pₖ x + Pᵒ⊖ x) - Pᵒ⊖ x := hsub
    _ = Pₖ x := by
      abel

-- Proof sketch: use Moreau's decomposition `P_K = Id - P_{Kᵒ⊖}`, so
-- `(1 / 2) * ‖P_K x‖^2 = (1 / 2) * d(x, Kᵒ⊖)^2`;
-- then take gradients of the equal functions.
/-- Proposition 12.32 (1): for a nonempty closed convex cone `K` in a real Hilbert space, the
gradients of `q ∘ P_K` and `(1 / 2) d_{Kᵒ⊖}^2` agree. -/
theorem gradient_half_norm_sq_projectionPoint_eq_gradient_half_sq_infDist_polarCone
    (hK_cone : IsCone K)
    :
    ∇ (fun x : H ↦ (1 / 2 : ℝ) * ‖Pₖ x‖ ^ 2) =
      ∇ (fun x : H ↦ (1 / 2 : ℝ) * Metric.infDist x (Kᵒ⊖) ^ 2) := by
  have hfun :
      (fun x : H ↦ (1 / 2 : ℝ) * ‖Pₖ x‖ ^ 2) =
        fun x : H ↦ (1 / 2 : ℝ) * Metric.infDist x (Kᵒ⊖) ^ 2 := by
    funext x
    have hdist :
        Metric.infDist x (Kᵒ⊖) = ‖Pₖ x‖ := by
      calc
        Metric.infDist x (Kᵒ⊖) =
            dist x (Pᵒ⊖ x) := by
          symm
          simpa using
            (projectionPoint_isBestApproximation (Kᵒ⊖)
              (isChebyshev_polarCone hK_nonempty hK_closed hK_convex) x).2
        _ = ‖x - Pᵒ⊖ x‖ := by
          rw [dist_eq_norm]
        _ = ‖Pₖ x‖ := by
          rw [sub_projectionPoint_polarCone_eq_projectionPoint
            hK_nonempty hK_closed hK_convex hK_cone x]
    simp [hdist]
  exact congrArg ∇ hfun

-- Proof sketch: apply Corollary 12.31 to `C = Kᵒ⊖` and scale the resulting gradient by `1 / 2`;
-- then rewrite `x - P_{Kᵒ⊖} x` as `P_K`.
/-- Proposition 12.32 (2): for a nonempty closed convex cone `K` in a real Hilbert space, the
gradient of `(1 / 2) d_{Kᵒ⊖}^2` is the metric projection `P_K`. -/
theorem gradient_half_sq_infDist_polarCone_eq_projectionPoint
    (hK_cone : IsCone K)
    :
    ∇ (fun x : H ↦ (1 / 2 : ℝ) * Metric.infDist x (Kᵒ⊖) ^ 2) =
      Pₖ := by
  have h_half_two : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  apply gradient_eq
  intro x
  have hsq :
      HasGradientAt
        (fun y : H ↦ Metric.infDist y (Kᵒ⊖) ^ 2)
        ((2 : ℝ) • (x - Pᵒ⊖ x)) x :=
    sq_infDist_hasGradientAt_of_nonempty_isClosed_convex
      polarCone_nonempty polarCone_isClosed polarCone_convex x
  have hhalf :
      HasGradientAt
        (fun y : H ↦ (1 / 2 : ℝ) * Metric.infDist y (Kᵒ⊖) ^ 2)
        (x - Pᵒ⊖ x) x := by
    simpa [Pi.smul_apply, smul_eq_mul, smul_smul, h_half_two] using
      (hsq.hasFDerivAt.const_smul (1 / 2 : ℝ)).hasGradientAt
  have hsub : x - Pᵒ⊖ x = Pₖ x :=
    sub_projectionPoint_polarCone_eq_projectionPoint
      hK_nonempty hK_closed hK_convex hK_cone x
  simpa [hsub] using hhalf

end
