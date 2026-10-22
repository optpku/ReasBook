/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Proposition_20_37

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace SetValuedOperator Topology

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section GraphClosedness

variable [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 20.38 states mixed strong/weak sequential closedness of `gra A`.
- `core/canonical`: the owner is the graph `gra A` of a maximally monotone operator.
- `bridge/view`: the strong-weak and weak-strong clauses are the two coordinate views of the same
  graph-closure phenomenon, with the second obtained canonically from the inverse operator `A⁻¹`
  and the coordinate swap `Prod.swap`.

The refinement therefore exposes clauses `(1)` and `(2)` as sequential closedness of these graph
images, and uses Proposition 20.37 only as the proof engine for the decoded graph-point sequences.
-/

-- Proof sketch: decode a convergent sequence in the image of `gra A` under
-- `Prod.map id (toWeakSpace ℝ H)` back to graph points `(xₙ, uₙ)`. Strong convergence of the first
-- coordinate and weak convergence of the second give the boundedness needed for Proposition 20.37
-- (1), so the decoded limit pair remains in `gra A`; re-encoding puts the limit back in the
-- mixed-topology image.
/-- Proposition 20.38 (1): the graph of a maximally monotone operator is sequentially closed in
the mixed topology with strong convergence in the primal variable and weak convergence in the dual
variable, encoded as sequential closedness of its image in `H × WeakSpace ℝ H`. -/
theorem Maximal.graph_isSeqClosed_strongWeak
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    IsSeqClosed ((Prod.map id (toWeakSpace ℝ H)) '' gra A) := by
  intro pₙ p hpₙ hp
  have hgraph : ∀ n, ((pₙ n).1, (toWeakSpace ℝ H).symm (pₙ n).2) ∈ gra A := by
    intro n
    rcases hpₙ n with ⟨⟨xₙ, uₙ⟩, hxuₙ, hpₙ_eq⟩
    rw [← hpₙ_eq]
    simpa using hxuₙ
  have hx : Tendsto (fun n ↦ (pₙ n).1) atTop (𝓝 p.1) := by
    simpa using (continuous_fst.tendsto p).comp hp
  have hu :
      Tendsto (fun n ↦ toWeakSpace ℝ H ((toWeakSpace ℝ H).symm (pₙ n).2)) atTop
        (𝓝 (toWeakSpace ℝ H ((toWeakSpace ℝ H).symm p.2))) := by
    simpa using (continuous_snd.tendsto p).comp hp
  have hx_bounded : Bornology.IsBounded (Set.range fun n ↦ (pₙ n).1) :=
    Metric.isBounded_range_of_tendsto _ hx
  have hu_bounded : Bornology.IsBounded (Set.range fun n ↦ (toWeakSpace ℝ H).symm (pₙ n).2) :=
    bounded_range_of_tendsto_weakly hu
  have hbounded :
      Bornology.IsBounded (Set.range fun n ↦ ((pₙ n).1, (toWeakSpace ℝ H).symm (pₙ n).2)) := by
    refine (hx_bounded.prod hu_bounded).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨⟨n, rfl⟩, ⟨n, rfl⟩⟩
  have hmem :
      (p.1, (toWeakSpace ℝ H).symm p.2) ∈ gra A :=
    SetValuedOperator.Maximal.mem_graph_of_tendsto_of_tendsto_weakly hA hgraph hbounded hx hu
  refine ⟨(p.1, (toWeakSpace ℝ H).symm p.2), hmem, ?_⟩
  simp

-- Proof sketch: apply clause (1) to the inverse operator `A⁻¹`, whose graph swaps the coordinates
-- of `gra A`. Pull the resulting sequential closedness statement back along the continuous swap
-- map `Prod.swap : WeakSpace ℝ H × H → H × WeakSpace ℝ H`; the preimage is exactly the
-- weak-strong graph image of `A`.
/-- Proposition 20.38 (2): the graph of a maximally monotone operator is sequentially closed in
the mixed topology with weak convergence in the primal variable and strong convergence in the dual
variable, encoded as sequential closedness of its image in `WeakSpace ℝ H × H`. -/
theorem Maximal.graph_isSeqClosed_weakStrong
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    IsSeqClosed ((Prod.map (toWeakSpace ℝ H) id) '' gra A) := by
  have hseq_inverse : IsSeqClosed ((Prod.map id (toWeakSpace ℝ H)) '' gra A⁻¹) :=
    SetValuedOperator.Maximal.graph_isSeqClosed_strongWeak
      (SetValuedOperator.Maximal.inverse hA)
  have hswap_preimage :
      Prod.swap ⁻¹' ((Prod.map id (toWeakSpace ℝ H)) '' gra A⁻¹) =
        ((Prod.map (toWeakSpace ℝ H) id) '' gra A) := by
    ext p
    constructor
    · intro hp
      change Prod.swap p ∈ ((Prod.map id (toWeakSpace ℝ H)) '' gra A⁻¹) at hp
      rcases hp with ⟨⟨u, x⟩, hux, hEq⟩
      refine ⟨(x, u), ?_, ?_⟩
      · simpa using hux
      · simpa using congrArg Prod.swap hEq
    · rintro ⟨⟨x, u⟩, hxu, hEq⟩
      change Prod.swap p ∈ ((Prod.map id (toWeakSpace ℝ H)) '' gra A⁻¹)
      refine ⟨(u, x), ?_, ?_⟩
      · simpa using hxu
      · simpa using congrArg Prod.swap hEq
  simpa [hswap_preimage] using hseq_inverse.preimage continuous_swap.seqContinuous

-- Proof sketch: clause (1) makes the mixed-topology image of `gra A` sequentially closed.
-- Pull that property back along the continuous injective map `Prod.map id (toWeakSpace ℝ H)` from
-- the strong product space `H × H`; in the metric space `H × H`, sequential closedness is
-- equivalent to topological closedness.
/-- Proposition 20.38 (3): the graph of a maximally monotone operator is closed in the strong
product topology on `H × H`. -/
theorem Maximal.graph_isClosed
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    IsClosed (gra A) := by
  have hseq_image : IsSeqClosed ((Prod.map id (toWeakSpace ℝ H)) '' gra A) :=
    SetValuedOperator.Maximal.graph_isSeqClosed_strongWeak hA
  have hweak : Continuous (toWeakSpace ℝ H : H → WeakSpace ℝ H) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using (toWeakSpaceCLM ℝ H).continuous
  have hmap : Continuous (Prod.map id (toWeakSpace ℝ H) : H × H → H × WeakSpace ℝ H) :=
    continuous_id.prodMap hweak
  have hmap_injective :
      Function.Injective (Prod.map id (toWeakSpace ℝ H) : H × H → H × WeakSpace ℝ H) :=
    (Prod.map_injective).2 ⟨fun _ _ h ↦ h, (toWeakSpace ℝ H).injective⟩
  have hseq_graph : IsSeqClosed (gra A) := by
    simpa [Set.preimage_image_eq _ hmap_injective] using hseq_image.preimage hmap.seqContinuous
  exact hseq_graph.isClosed

end GraphClosedness

end SetValuedOperator
