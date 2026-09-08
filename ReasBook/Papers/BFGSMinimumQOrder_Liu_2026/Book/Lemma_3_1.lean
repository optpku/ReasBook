module

public import Book.Notation_3_1_TangentRecurrence
public import ReasLib.Optimization.BFGS.PlanarGradient.Recurrence

public section

noncomputable section

universe u

namespace PlanarGradient

section OrientedPlane

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/- Lemma 3.1 (1): the parallel coefficient under the pre-step relation. -/
#check
  (PlanarGradient.parallelCoefficient_eq_of_preStep :
    ∀ (o : Orientation ℝ E (Fin 2)) (gPrev g : E) (δPrev : ℝ),
      gPrev ≠ 0 → g ≠ 0 → g ≠ gPrev →
      inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev) →
      parallelCoefficient gPrev g =
        δPrev * ‖g‖ * o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g) /
          ‖g - gPrev‖)

/- Lemma 3.1 (2): the tangent coefficient in terms of the oriented area form. -/
#check
  (PlanarGradient.tangentCoefficient_eq_areaForm :
    ∀ (o : Orientation ℝ E (Fin 2)) (gPrev g : E) (δPrev : ℝ),
      gPrev ≠ 0 → g ≠ 0 → g ≠ gPrev →
      inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev) →
      tangentCoefficient o gPrev g =
        ‖gPrev‖ * o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g) /
          ‖g - gPrev‖)

/- Lemma 3.1 (3): positive angular separation makes the tangent coefficient nonzero. -/
#check
  (PlanarGradient.tangentCoefficient_ne_zero :
    ∀ (o : Orientation ℝ E (Fin 2)) (gPrev g : E) (δPrev : ℝ),
      gPrev ≠ 0 → g ≠ 0 → g ≠ gPrev →
      inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev) →
      0 < angularSeparation o gPrev g → tangentCoefficient o gPrev g ≠ 0)

/- Lemma 3.1 (4): the absolute ratio of the parallel and tangent coefficients. -/
#check
  (PlanarGradient.abs_coefficientRatio :
    ∀ (o : Orientation ℝ E (Fin 2)) (gPrev g : E) (δPrev : ℝ),
      gPrev ≠ 0 → g ≠ 0 → g ≠ gPrev →
      inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev) →
      0 < angularSeparation o gPrev g →
      |parallelCoefficient gPrev g / tangentCoefficient o gPrev g| =
        |δPrev| * ‖g‖ / ‖gPrev‖)

/- Lemma 3.1 (5): every tangential choice at the next gradient satisfies the post-step
orthogonality relation. -/
#check
  (PlanarGradient.next_candidate_orthogonal :
    ∀ (o : Orientation ℝ E (Fin 2)) (gPrev g : E) (δPrev δ : ℝ) (ΔNext : E),
      gPrev ≠ 0 → g ≠ 0 → g ≠ gPrev →
      inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev) →
      scale o gPrev g δ ≠ 0 → inner ℝ (next o gPrev g δ) ΔNext = 0 →
      inner ℝ (next o gPrev g δ)
        ((next o gPrev g δ + ΔNext) - candidate o g δ) = 0)

/- Lemma 3.1 (6): the next gradient lies in the span of the gradient difference. -/
#check
  (PlanarGradient.next_mem_span :
    ∀ (o : Orientation ℝ E (Fin 2)) (gPrev g : E) (δPrev δ : ℝ),
      gPrev ≠ 0 → g ≠ 0 → g ≠ gPrev →
      inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev) →
      scale o gPrev g δ ≠ 0 →
      next o gPrev g δ ∈ Submodule.span ℝ {g - gPrev})

/- Lemma 3.1 (7): a nonzero recurrence scale produces a nonzero next gradient. -/
#check
  (PlanarGradient.next_ne_zero :
    ∀ (o : Orientation ℝ E (Fin 2)) (gPrev g : E) (δPrev δ : ℝ),
      gPrev ≠ 0 → g ≠ 0 → g ≠ gPrev →
      inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev) →
      scale o gPrev g δ ≠ 0 → next o gPrev g δ ≠ 0)

/- Lemma 3.1 (8): angular separation after the parameterized recurrence. -/
#check
  (PlanarGradient.angularSeparation_next :
    ∀ (o : Orientation ℝ E (Fin 2)) (gPrev g : E) (δPrev δ : ℝ),
      gPrev ≠ 0 → g ≠ 0 → g ≠ gPrev →
      inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev) →
      scale o gPrev g δ ≠ 0 →
      angularSeparation o g (next o gPrev g δ) =
        ‖gPrev‖ * angularSeparation o gPrev g / ‖g - gPrev‖)

/- Lemma 3.1 (9): the tangent coefficient equals the next angular separation in absolute
value. -/
#check
  (PlanarGradient.abs_tangentCoefficient_eq_next :
    ∀ (o : Orientation ℝ E (Fin 2)) (gPrev g : E) (δPrev δ : ℝ),
      gPrev ≠ 0 → g ≠ 0 → g ≠ gPrev →
      inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev) →
      scale o gPrev g δ ≠ 0 →
      |tangentCoefficient o gPrev g| = angularSeparation o g (next o gPrev g δ))

end OrientedPlane

end PlanarGradient
