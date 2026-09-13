/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SeedWitnesses
public import RockafellarSum_2026.ReasLib.Analysis.Convex.NormalCone.ClosedBall
public import RockafellarSum_2026.ReasLib.Analysis.Convex.NormalCone.Sum
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing.Origin
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing.Surjective

/-!
# The S3 seed counterexample
-/

public section
open scoped Pointwise

namespace Lorentz

/-- The source seed yields a maximal monotone operator whose sum with the
radius-twelve ball normal cone is not maximal, despite interior qualification. -/
theorem exists_seedCounterexample : ∃ M : SetValuedOperator C0Seq L1Seq,
    Maximal C0Seq.coordinateDualPairing.IsMonotone M.graph ∧
    Maximal C0Seq.coordinateDualPairing.IsMonotone
      (C0Seq.coordinateDualPairing.normalConeGraph (Metric.closedBall (0 : C0Seq) 12)) ∧
    (M.dom ∩ interior (Metric.closedBall (0 : C0Seq) 12)).Nonempty ∧
    ¬ Maximal C0Seq.coordinateDualPairing.IsMonotone
      (M + C0Seq.coordinateDualPairing.normalCone (Metric.closedBall (0 : C0Seq) 12)).graph := by
  obtain ⟨G, hG, ⟨z, hzG, hzneg⟩, ⟨y, hyG, hynorm⟩, hlocal⟩ := exists_S3_maximal_graph
  let M : SetValuedOperator C0Seq L1Seq := fun x ↦ {u | (x, u) ∈ G}
  have hgraph : M.graph = G := by
    ext w
    rcases w with ⟨x, u⟩
    rw [SetValuedOperator.mem_graph]
    rfl
  have hM : Maximal C0Seq.coordinateDualPairing.IsMonotone M.graph := by
    rw [hgraph]
    exact hG
  have hr : (0 : ℝ) < 12 := by norm_num
  have hzeroBall : (0 : C0Seq) ∈ Metric.closedBall (0 : C0Seq) 12 := by
    simp
  have hzeroInt : (0 : C0Seq) ∈ interior (Metric.closedBall (0 : C0Seq) 12) := by
    rw [interior_closedBall _ (ne_of_gt hr)]
    simp
  have hqual : (M.dom ∩ interior (Metric.closedBall (0 : C0Seq) 12)).Nonempty := by
    refine ⟨y.1, ?_, ?_⟩
    · rw [SetValuedOperator.mem_dom]
      exact ⟨y.2, hyG⟩
    · rw [interior_closedBall _ (ne_of_gt hr)]
      simpa only [Metric.mem_ball, dist_zero_right] using hynorm
  have hsumNonneg : ∀ x u, (x, u) ∈
      (M + C0Seq.coordinateDualPairing.normalCone (Metric.closedBall (0 : C0Seq) 12)).graph →
      0 ≤ C0Seq.coordinateDualPairing.quadratic (x, u) := by
    intro x u hxu
    apply C0Seq.coordinateDualPairing.quadratic_nonneg_of_mem_graph_add_normalCone M
      (Metric.closedBall (0 : C0Seq) 12) (Metric.ball (0 : C0Seq) 16) hzeroBall _ _ x u hxu
    · intro a ha
      simp only [Metric.mem_closedBall, Metric.mem_ball, dist_zero_right] at ha ⊢
      linarith
    · intro a b hab ha
      rw [← C0Seq.quadraticPairing_eq_coordinateQuadratic]
      rw [hgraph] at hab
      apply hlocal (a, b) hab
      simpa only [Metric.mem_ball, dist_zero_right] using ha
  have hpolar : (0, 0) ∈ C0Seq.coordinateDualPairing.monotonePolar
      (M + C0Seq.coordinateDualPairing.normalCone (Metric.closedBall (0 : C0Seq) 12)).graph := by
    rw [C0Seq.coordinateDualPairing.mem_monotonePolar]
    rintro ⟨x, u⟩ hxu
    have hn := hsumNonneg x u hxu
    simpa only [← Prod.zero_eq_mk, zero_sub, QuadraticMap.map_neg] using hn
  have hnot : (0, 0) ∉
      (M + C0Seq.coordinateDualPairing.normalCone (Metric.closedBall (0 : C0Seq) 12)).graph := by
    intro h
    rw [SetValuedOperator.mem_graph_add] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    rw [C0Seq.coordinateDualPairing.normalCone_eq_zero_of_mem_interior hzeroInt] at hb
    have hb0 : b = 0 := Set.mem_singleton_iff.mp hb
    subst b
    simp only [add_zero] at hab
    subst a
    exact C0Seq.zero_not_mem_of_quadraticPairing_neg hzG hzneg hG.1 ha
  refine ⟨M, hM, ?_, hqual, ?_⟩
  · exact C0Seq.coordinateDualPairing.maximalMonotone_normalConeGraph_closedBall
      C0Seq.coordinateDualPairing_surjective 12 hr
  · intro hmax
    have heq := (C0Seq.coordinateDualPairing.maximalMonotone_iff_polar_eq _ hmax.1).mp hmax
    rw [heq] at hpolar
    exact hnot hpolar

end Lorentz

namespace C0Seq

/-- Two maximally monotone operators on real `c₀` satisfy the interior-domain
constraint qualification but their pointwise sum is not maximally monotone. -/
theorem exists_maximalMonotone_sum_not_maximal :
    ∃ A B : SetValuedOperator C0Seq L1Seq,
      Maximal coordinateDualPairing.IsMonotone A.graph ∧
      Maximal coordinateDualPairing.IsMonotone B.graph ∧
      (A.dom ∩ interior B.dom).Nonempty ∧
      ¬ Maximal coordinateDualPairing.IsMonotone (A + B).graph := by
  obtain ⟨A, hA, hB, hdom, hsum⟩ := Lorentz.exists_seedCounterexample
  let B := coordinateDualPairing.normalCone (Metric.closedBall (0 : C0Seq) 12)
  have hgraph : B.graph = coordinateDualPairing.normalConeGraph
      (Metric.closedBall (0 : C0Seq) 12) := by
    ext z
    rcases z with ⟨x, u⟩
    rw [SetValuedOperator.mem_graph, coordinateDualPairing.mem_graph_normalCone]
    exact coordinateDualPairing.mem_normalCone _ x u
  have hBdom : B.dom = Metric.closedBall (0 : C0Seq) 12 := by
    ext x
    rw [SetValuedOperator.mem_dom]
    constructor
    · rintro ⟨u, hu⟩
      exact (coordinateDualPairing.mem_normalCone _ x u).mp hu |>.1
    · intro hx
      refine ⟨0, ?_⟩
      rw [coordinateDualPairing.mem_normalCone]
      refine ⟨hx, ?_⟩
      intro y hy
      simp
  refine ⟨A, B, hA, ?_, ?_, hsum⟩
  · rw [hgraph]
    exact hB
  · rw [hBdom]
    exact hdom

end C0Seq
