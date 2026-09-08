module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowGraph
public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

/-!
# Invariant slow curves

This module adds the state-map invariance law to a fifth-order slow graph.  The
chosen graph is explicit structure data because more than one local invariant
representative may be present in the same development.
-/

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- A fifth-order slow graph that is locally forward invariant under the
two-leg state map. -/
structure SlowCurve extends SlowGraph where
  /-- Near zero, applying the state map stays on the same chosen graph. -/
  isInvariant :
    (fun ε ↦ stateMap (ε, shape ε, high ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let nextScale := (stateMap (ε, shape ε, high ε)).1
        (nextScale, shape nextScale, high nextScale))

namespace SlowCurve

/-- Bundle two graph coordinates, their fifth-order asymptotics, and their
local invariance under the two-leg state map as an invariant slow curve. -/
def ofAsymptotics (shape high : ℝ → ℝ)
    (shapeRemainder :
      (fun ε : ℝ ↦
        shape ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (highRemainder :
      (fun ε : ℝ ↦ high ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (isInvariant :
      (fun ε ↦ stateMap (ε, shape ε, high ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let nextScale := (stateMap (ε, shape ε, high ε)).1
          (nextScale, shape nextScale, high nextScale))) : SlowCurve :=
  { shape := shape
    high := high
    shapeRemainder := shapeRemainder
    highRemainder := highRemainder
    isInvariant := isInvariant }

/-- An invariant slow curve bundled by `ofAsymptotics` retains its shape
coordinate. -/
@[simp]
theorem ofAsymptotics_shape (shape high : ℝ → ℝ)
    (shapeRemainder :
      (fun ε : ℝ ↦
        shape ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (highRemainder :
      (fun ε : ℝ ↦ high ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (isInvariant :
      (fun ε ↦ stateMap (ε, shape ε, high ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let nextScale := (stateMap (ε, shape ε, high ε)).1
          (nextScale, shape nextScale, high nextScale))) :
    (ofAsymptotics shape high shapeRemainder highRemainder isInvariant).shape = shape := by
  rfl

/-- An invariant slow curve bundled by `ofAsymptotics` retains its high
coordinate. -/
@[simp]
theorem ofAsymptotics_high (shape high : ℝ → ℝ)
    (shapeRemainder :
      (fun ε : ℝ ↦
        shape ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (highRemainder :
      (fun ε : ℝ ↦ high ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (isInvariant :
      (fun ε ↦ stateMap (ε, shape ε, high ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let nextScale := (stateMap (ε, shape ε, high ε)).1
          (nextScale, shape nextScale, high nextScale))) :
    (ofAsymptotics shape high shapeRemainder highRemainder isInvariant).high = high := by
  rfl

/-- Pathwise invariance of a slow graph is equivalent to the coordinate form
stored by an invariant slow curve. -/
private theorem coordinateInvariantOfPath (graph : SlowGraph)
    (hInvariant :
      (fun ε ↦ stateMap (graph.path ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let nextScale := (stateMap (graph.path ε)).1
          graph.path nextScale)) :
    (fun ε ↦ stateMap (ε, graph.shape ε, graph.high ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let nextScale := (stateMap (ε, graph.shape ε, graph.high ε)).1
        (nextScale, graph.shape nextScale, graph.high nextScale)) := by
  filter_upwards [hInvariant] with ε hε
  simpa only [SlowGraph.path_apply] using hε

/-- Attach a local state-map invariance law to an explicitly chosen slow
graph. -/
def ofInvariantGraph (graph : SlowGraph)
    (isInvariant :
      (fun ε ↦ stateMap (graph.path ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let nextScale := (stateMap (graph.path ε)).1
          graph.path nextScale)) : SlowCurve :=
  { toSlowGraph := graph
    isInvariant := coordinateInvariantOfPath graph isInvariant }

/-- The state-space path traced by an invariant slow curve. -/
def path (curve : SlowCurve) (ε : ℝ) : ℝ × ℝ × ℝ :=
  curve.toSlowGraph.path ε

/-- The invariant slow-curve path exposes its three coordinates. -/
theorem path_apply (curve : SlowCurve) (ε : ℝ) :
    curve.path ε = (ε, curve.shape ε, curve.high ε) := by
  rw [SlowCurve.path]
  exact SlowGraph.path_apply curve.toSlowGraph ε

/-- Applying the two-leg state map along an invariant slow curve eventually
agrees with reparametrization by the next scale. -/
theorem stateMap_path_eventuallyEq (curve : SlowCurve) :
    (fun ε ↦ stateMap (curve.path ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let nextScale := (stateMap (curve.path ε)).1
        curve.path nextScale) := by
  filter_upwards [curve.isInvariant] with ε hε
  simpa only [path_apply] using hε

end SlowCurve

end DFP.TwoLeg
