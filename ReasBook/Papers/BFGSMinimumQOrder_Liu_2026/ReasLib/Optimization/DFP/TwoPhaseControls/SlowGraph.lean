module

public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
public import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Fifth-order slow graphs

This module bundles a chosen pair of transverse graph coordinates together
with their fifth-order agreement with the canonical polynomial slow-graph jet.
The bundle is explicit data, rather than a typeclass, because different slow
graphs may be compared in the same context.
-/

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- A parameter graph whose shape and high coordinates agree through order four
with the canonical polynomial slow-graph jet. -/
structure SlowGraph where
  /-- The shape coordinate of the graph. -/
  shape : ℝ → ℝ
  /-- The high-eigenvalue coordinate of the graph. -/
  high : ℝ → ℝ
  /-- The shape-coordinate error is of fifth order at zero. -/
  shapeRemainder :
    (fun ε : ℝ ↦
      shape ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)
  /-- The high-coordinate error is of fifth order at zero. -/
  highRemainder :
    (fun ε : ℝ ↦ high ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)

namespace SlowGraph

/-- Bundle two coordinate functions and their prescribed fifth-order
asymptotics as a slow graph. -/
def ofAsymptotics (shape high : ℝ → ℝ)
    (shapeRemainder :
      (fun ε : ℝ ↦
        shape ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (highRemainder :
      (fun ε : ℝ ↦ high ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) : SlowGraph :=
  { shape := shape
    high := high
    shapeRemainder := shapeRemainder
    highRemainder := highRemainder }

/-- The slow graph bundled by `ofAsymptotics` retains its shape coordinate. -/
@[simp]
theorem ofAsymptotics_shape (shape high : ℝ → ℝ)
    (shapeRemainder :
      (fun ε : ℝ ↦
        shape ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (highRemainder :
      (fun ε : ℝ ↦ high ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (ofAsymptotics shape high shapeRemainder highRemainder).shape = shape := by
  rfl

/-- The slow graph bundled by `ofAsymptotics` retains its high coordinate. -/
@[simp]
theorem ofAsymptotics_high (shape high : ℝ → ℝ)
    (shapeRemainder :
      (fun ε : ℝ ↦
        shape ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (highRemainder :
      (fun ε : ℝ ↦ high ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (ofAsymptotics shape high shapeRemainder highRemainder).high = high := by
  rfl

/-- The state-space path traced by a slow graph. -/
def path (graph : SlowGraph) (ε : ℝ) : ℝ × ℝ × ℝ :=
  (ε, graph.shape ε, graph.high ε)

/-- The state-space path exposes the scale, shape, and high coordinates. -/
theorem path_apply (graph : SlowGraph) (ε : ℝ) :
    graph.path ε = (ε, graph.shape ε, graph.high ε) := by
  rfl

/-- Every fifth-order slow graph converges to the canceled base state. -/
theorem path_tendsto (graph : SlowGraph) :
    Tendsto graph.path (𝓝 0) (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
  let shapeJet : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let highJet : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hshapeRemainder :
      (fun ε ↦ graph.shape ε - shapeJet ε) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [shapeJet] using graph.shapeRemainder
  have hhighRemainder :
      (fun ε ↦ graph.high ε - highJet ε) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [highJet] using graph.highRemainder
  have hpowFive : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hshapeJet : Tendsto shapeJet (𝓝 0) (𝓝 2) := by
    have hcontinuous : ContinuousAt shapeJet 0 := by
      dsimp only [shapeJet]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [shapeJet]
  have hhighJet : Tendsto highJet (𝓝 0) (𝓝 1) := by
    have hcontinuous : ContinuousAt highJet 0 := by
      dsimp only [highJet]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [highJet]
  have hshape : Tendsto graph.shape (𝓝 0) (𝓝 2) := by
    simpa only [sub_add_cancel, zero_add] using
      (hshapeRemainder.trans_tendsto hpowFive).add hshapeJet
  have hhigh : Tendsto graph.high (𝓝 0) (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using
      (hhighRemainder.trans_tendsto hpowFive).add hhighJet
  have hpath : graph.path =
      (fun ε : ℝ ↦ (ε, graph.shape ε, graph.high ε)) := by
    funext ε
    exact path_apply graph ε
  rw [hpath]
  simpa only [id_eq, nhds_prod_eq] using
    tendsto_id.prodMk (hshape.prodMk hhigh)

/-- The state-space path of a slow graph differs from the canonical polynomial
jet by a fifth-order vector error. -/
theorem path_sub_jet_isBigO (graph : SlowGraph) :
    (fun ε : ℝ ↦ graph.path ε - slowGraphJetPath ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
  have hscale : (fun _ : ℝ ↦ (0 : ℝ)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) :=
    Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
  have hcoordinates :=
    hscale.prod_left (graph.shapeRemainder.prod_left graph.highRemainder)
  simpa [path_apply, slowGraphJetPath_apply] using hcoordinates

end SlowGraph

end DFP.TwoLeg
