module

public import Book.Lemma_4_2_Hessian
public import ReasLib.Analysis.Convergence.QOrder
public import ReasLib.Optimization.BFGS.Scaling

public section

universe u

open scoped Pointwise

namespace BFGS.Scale

/-- Lemma 4.3 (2): the Hessian of the scaled objective at `z` equals the original
Hessian at the inverse-scaled point. -/
theorem hessian {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (B : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (α : ℕ → ℝ) (B₀ : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hF : ContDiff ℝ 2 F) (hRun : BFGS.IsTrajectory F B₀ x B α) (hc : 0 < c)
    (z : EuclideanSpace ℝ (Fin n)) :
    ConvexAnalysis.hessian (objective c F) z =
      ConvexAnalysis.hessian F (c⁻¹ • z) := by
  calc
    ConvexAnalysis.hessian (objective c F) z =
        (Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))).symm
          (fderiv ℝ (gradient (objective c F)) z) := by
      simpa using congrArg
        (Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))).symm
        (ConvexAnalysis.toEuclideanCLM_hessian (objective c F) z)
    _ = (Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))).symm
          (fderiv ℝ (gradient F) (c⁻¹ • z)) :=
      hessian_objective (ne_of_gt hc) hF z
    _ = ConvexAnalysis.hessian F (c⁻¹ • z) := by
      symm
      simpa using congrArg
        (Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))).symm
        (ConvexAnalysis.toEuclideanCLM_hessian F (c⁻¹ • z))

end BFGS.Scale

#check (BFGS.Scale.objective :
  ∀ {E : Type u} [SMul ℝ E], ℝ → (E → ℝ) → E → ℝ)

/- Lemma 4.3 (scaling invariance): positive spatial dilation and quadratic value
scaling preserve a selected exact-line-search BFGS trajectory with the same step
lengths and Hessian approximations. -/
#check (BFGS.IsTrajectory.scale :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    {F : EuclideanSpace ℝ ι → ℝ} {B₀ : Matrix ι ι ℝ}
    {x : ℕ → EuclideanSpace ℝ ι} {B : ℕ → Matrix ι ι ℝ} {α : ℕ → ℝ},
    BFGS.IsTrajectory F B₀ x B α →
      ∀ {c : ℝ}, c ≠ 0 →
        BFGS.IsTrajectory (BFGS.Scale.objective c F) B₀ (fun k ↦ c • x k) B α)

#check (BFGS.Scale.hessian :
  ∀ {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (B : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (α : ℕ → ℝ) (B₀ : Matrix (Fin n) (Fin n) ℝ) (c : ℝ),
    ContDiff ℝ 2 F → BFGS.IsTrajectory F B₀ x B α → 0 < c →
      ∀ z : EuclideanSpace ℝ (Fin n),
        ConvexAnalysis.hessian (BFGS.Scale.objective c F) z =
          ConvexAnalysis.hessian F (c⁻¹ • z))

#check (BFGS.Scale.tsupport_sub_quadratic :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {c : ℝ}, c ≠ 0 → ∀ F : E → ℝ,
      _root_.tsupport (BFGS.Scale.objective c F - standardQuadratic) =
        c • _root_.tsupport (F - standardQuadratic))

#check (QConvergence.hasOrderAtLeast_smul :
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : ℕ → E} {xStar : E} {p c : ℝ}, c ≠ 0 →
      (QConvergence.HasOrderAtLeast (fun k ↦ c • x k) (c • xStar) p ↔
        QConvergence.HasOrderAtLeast x xStar p))

#check (QConvergence.order_smul :
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : ℕ → E} {xStar : E} {c : ℝ}, c ≠ 0 →
      QConvergence.order (fun k ↦ c • x k) (c • xStar) =
        QConvergence.order x xStar)
