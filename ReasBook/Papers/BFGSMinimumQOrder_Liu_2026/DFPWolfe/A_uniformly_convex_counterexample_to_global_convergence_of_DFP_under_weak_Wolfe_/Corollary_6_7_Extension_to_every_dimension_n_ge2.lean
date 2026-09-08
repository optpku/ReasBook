module

public import ReasLib.Analysis.Calculus.Gradient.Hessian.EuclideanPlane
public import ReasLib.Optimization.DFP.OrthogonalSum
public import ReasLib.Optimization.DFP.OrthogonalSum.Hessian

public section

open Filter
open scoped Matrix Topology

variable (m : ℕ)

/- Corollary 6.7 (Extension to every dimension $n\ge2$) (1): embedding the planar
iterates and gradients with zero complementary component and adjoining an identity
matrix block transports the complete DFP orbit. -/
#check (DFP.IsOrbit.orthogonalSum :
  ∀ {f : EuclideanSpace ℝ (Fin 2) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin 2)} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ},
    DFP.IsOrbit f α x g H →
      DFP.IsOrbit (DFP.OrthogonalSum.objective f) α
        (fun k ↦ DFP.OrthogonalSum.embed (x k) :
          ℕ → EuclideanSpace ℝ (Fin 2 ⊕ Fin m))
        (fun k ↦ DFP.OrthogonalSum.embed (g k) :
          ℕ → EuclideanSpace ℝ (Fin 2 ⊕ Fin m))
        (fun k ↦ DFP.OrthogonalSum.matrix (H k) :
          ℕ → Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) ℝ))

/-- Corollary 6.7 (Extension to every dimension $n\ge2$) (2): adjoining the
quadratic complement `‖w‖ ^ 2 / 2` preserves the global Hessian bounds
`(1 / 2)I ≼ ∇²f ≼ (3 / 2)I`. -/
theorem orthogonalSumObjectiveHessianBounds
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (hf : ContDiff ℝ 2 f)
    (h_lower : ∀ z,
      (EuclideanPlane.hessianMatrix f z - (1 / 2 : ℝ) • 1).PosSemidef)
    (h_upper : ∀ z,
      ((3 / 2 : ℝ) • 1 - EuclideanPlane.hessianMatrix f z).PosSemidef)
    (p v : EuclideanSpace ℝ (Fin 2 ⊕ Fin m)) :
    let F : EuclideanSpace ℝ (Fin 2 ⊕ Fin m) → ℝ :=
      DFP.OrthogonalSum.objective f
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient F) p v) v ∧
      inner ℝ (fderiv ℝ (gradient F) p v) v ≤ (3 / 2 : ℝ) * ‖v‖ ^ 2 := by
  dsimp only
  have hfBounds : HasHessianBounds (1 / 2 : ℝ) (3 / 2 : ℝ) f :=
    (EuclideanPlane.hasHessianBounds_iff_hessianMatrix hf).2 fun z =>
      ⟨h_lower z, h_upper z⟩
  have hsum :=
    DFP.OrthogonalSum.hasHessianBounds_objective
      (κ := Fin m) hf hfBounds (by norm_num) (by norm_num)
  simpa only [hessian_def] using (hsum.at p).quadraticForm v

/- Corollary 6.7 (Extension to every dimension $n\ge2$) (3): weak Wolfe
satisfaction for every embedded step is exactly the original planar condition. -/
#check (LineSearch.IsWeakWolfe.orthogonalSum_iff :
  ∀ {c₁ c₂ : ℝ} {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {x s : EuclideanSpace ℝ (Fin 2)},
    LineSearch.IsWeakWolfe c₁ c₂ (DFP.OrthogonalSum.objective f)
        (DFP.OrthogonalSum.embed x : EuclideanSpace ℝ (Fin 2 ⊕ Fin m))
        (DFP.OrthogonalSum.embed s : EuclideanSpace ℝ (Fin 2 ⊕ Fin m)) ↔
      LineSearch.IsWeakWolfe c₁ c₂ f x s)

/- Corollary 6.7 (Extension to every dimension $n\ge2$) (4): adjoining an
identity block preserves and reflects positive definiteness. -/
#check (DFP.OrthogonalSum.matrix_posDef_iff :
  ∀ H : Matrix (Fin 2) (Fin 2) ℝ,
    (DFP.OrthogonalSum.matrix H :
      Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) ℝ).PosDef ↔ H.PosDef)

/-- Corollary 6.7 (Extension to every dimension $n\ge2$) (5): zero-component
embedding preserves the limiting gradient norm, hence also its positive limit. -/
theorem orthogonalSumGradientNormTendsto_iff
    (g : ℕ → EuclideanSpace ℝ (Fin 2)) (G : ℝ) :
    Tendsto
        (fun k ↦ ‖(DFP.OrthogonalSum.embed (g k) :
          EuclideanSpace ℝ (Fin 2 ⊕ Fin m))‖) atTop (𝓝 G) ↔
      Tendsto (fun k ↦ ‖g k‖) atTop (𝓝 G) := by
  simp only [DFP.OrthogonalSum.norm_embed]
