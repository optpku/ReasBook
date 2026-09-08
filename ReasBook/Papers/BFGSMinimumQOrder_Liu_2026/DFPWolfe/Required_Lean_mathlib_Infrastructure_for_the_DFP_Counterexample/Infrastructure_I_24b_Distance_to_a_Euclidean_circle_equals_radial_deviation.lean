module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ReasLib.Topology.MetricSpace.Sphere

public section

universe u

/- Infrastructure I.24b (Distance to a Euclidean circle equals radial deviation) (1):
for positive radius, the distance to the affine image of the unit sphere is the absolute
radial deviation, including at the center. -/
#check (Metric.infDist_affinity_unitSphere :
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (x C : E) (R : ℝ), 0 < R →
      Metric.infDist x ((fun v : E ↦ C + R • v) '' Metric.sphere 0 1) =
        |‖x - C‖ - R|)

/- Infrastructure I.24b (Distance to a Euclidean circle equals radial deviation) (2):
the specialization to the Euclidean plane for the circle used as `Γ`. -/
#check (Metric.infDist_affinity_unitSphere (E := EuclideanSpace ℝ (Fin 2)) :
  ∀ (x C : EuclideanSpace ℝ (Fin 2)) (R : ℝ), 0 < R →
    Metric.infDist x
        ((fun v : EuclideanSpace ℝ (Fin 2) ↦ C + R • v) '' Metric.sphere 0 1) =
      |‖x - C‖ - R|)
