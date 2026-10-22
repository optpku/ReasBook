/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Proposition_20_22

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace SetValuedOperator Topology

universe u v

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {B : Type v} [Nonempty B] [Preorder B] [IsDirectedOrder B]

/- Source/core/bridge triage:
- `source-facing`: Proposition 20.37 records mixed strong/weak net closedness as graph-point
  membership statements.
- `core/canonical`: the owner data are maximal monotonicity `Maximal IsMonotone A` and graph
  membership `(x, u) ∈ gra A`.
- `bridge/view`: clause `(2)` is the inverse-coordinate-swap view of clause `(1)`, so it should
  reuse the canonical inverse owner API rather than duplicate the same closure argument. -/

-- Proof sketch: test maximal monotonicity of `A` against an arbitrary graph point `(y, v)`. The
-- graph inequalities for `(x_b b, u_b b)` pass to the limit because `x_b` converges strongly, `u_b`
-- converges weakly, and the graph net is bounded. The resulting inequality for every `(y, v) ∈ gra
-- A` gives `(x, u) ∈ gra A` by the maximal-monotonicity criterion.
/-- Proposition 20.37 (1): if a bounded net of graph points of a maximally monotone operator
converges strongly in the primal variable and weakly in the dual variable, then its limit pair
still belongs to the graph. -/
theorem Maximal.mem_graph_of_tendsto_of_tendsto_weakly
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    {x_b u_b : B → H} {x u : H}
    (hgraph : ∀ b, (x_b b, u_b b) ∈ gra A)
    (hbounded : Bornology.IsBounded (Set.range fun b ↦ (x_b b, u_b b)))
    (hx_b : Tendsto x_b atTop (𝓝 x))
    (hu_b : Tendsto (fun b ↦ toWeakSpace ℝ H (u_b b)) atTop (𝓝 (toWeakSpace ℝ H u))) :
    (x, u) ∈ gra A := sorry

-- Proof sketch: apply part (1) to the inverse operator `A.inverse`, whose graph is obtained by
-- swapping the coordinates. Strong convergence of `u_b` and weak convergence of `x_b` translate
-- exactly into the hypotheses of part (1) for the inverse graph, giving `(u, x) ∈ gra A⁻¹` and
-- hence `(x, u) ∈ gra A`.
/-- Proposition 20.37 (2): if a bounded net of graph points of a maximally monotone operator
converges weakly in the primal variable and strongly in the dual variable, then its limit pair
still belongs to the graph. -/
theorem Maximal.mem_graph_of_tendsto_weakly_of_tendsto
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    {x_b u_b : B → H} {x u : H}
    (hgraph : ∀ b, (x_b b, u_b b) ∈ gra A)
    (hbounded : Bornology.IsBounded (Set.range fun b ↦ (x_b b, u_b b)))
    (hx_b : Tendsto (fun b ↦ toWeakSpace ℝ H (x_b b)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hu_b : Tendsto u_b atTop (𝓝 u)) :
    (x, u) ∈ gra A := by
  have hAinv : Maximal IsMonotone A⁻¹ := SetValuedOperator.Maximal.inverse hA
  have hu_range :
      Prod.snd '' Set.range (fun b ↦ (x_b b, u_b b)) = Set.range u_b := by
    ext u'
    constructor
    · rintro ⟨p, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨(x_b b, u_b b), ⟨b, rfl⟩, rfl⟩
  have hx_range :
      Prod.fst '' Set.range (fun b ↦ (x_b b, u_b b)) = Set.range x_b := by
    ext x'
    constructor
    · rintro ⟨p, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨(x_b b, u_b b), ⟨b, rfl⟩, rfl⟩
  have hu_bounded : Bornology.IsBounded (Set.range u_b) := by
    rw [← hu_range]
    exact hbounded.image_snd
  have hx_bounded : Bornology.IsBounded (Set.range x_b) := by
    rw [← hx_range]
    exact hbounded.image_fst
  have hbounded_inv : Bornology.IsBounded (Set.range fun b ↦ (u_b b, x_b b)) := by
    rw [← Bornology.isBounded_image_fst_and_snd]
    constructor
    · have hfst : Prod.fst '' Set.range (fun b ↦ (u_b b, x_b b)) = Set.range u_b := by
        ext u'
        constructor
        · rintro ⟨p, ⟨b, rfl⟩, rfl⟩
          exact ⟨b, rfl⟩
        · rintro ⟨b, rfl⟩
          exact ⟨(u_b b, x_b b), ⟨b, rfl⟩, rfl⟩
      rw [hfst]
      exact hu_bounded
    · have hsnd : Prod.snd '' Set.range (fun b ↦ (u_b b, x_b b)) = Set.range x_b := by
        ext x'
        constructor
        · rintro ⟨p, ⟨b, rfl⟩, rfl⟩
          exact ⟨b, rfl⟩
        · rintro ⟨b, rfl⟩
          exact ⟨(u_b b, x_b b), ⟨b, rfl⟩, rfl⟩
      rw [hsnd]
      exact hx_bounded
  have hgraph_inv : ∀ b, (u_b b, x_b b) ∈ gra A⁻¹ := by
    intro b
    simpa using hgraph b
  have hmem_inv : (u, x) ∈ gra A⁻¹ :=
    SetValuedOperator.Maximal.mem_graph_of_tendsto_of_tendsto_weakly
      hAinv hgraph_inv hbounded_inv hu_b hx_b
  simpa using hmem_inv

end SetValuedOperator
