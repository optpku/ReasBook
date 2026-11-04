/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib

namespace SimpleGraph

/-- Helper for Proposition 8.9: deleting vertices from a full-vertex subgraph and then forgetting
the ambient owner gives, up to graph isomorphism, the original graph induced on the complement. -/
theorem toSubgraph_deleteVerts_coe_isTree_iff
    {V : Type*}
    (G H : SimpleGraph V)
    (h : H ≤ G)
    (S : Set V) :
    ((G.toSubgraph H h).deleteVerts S).coe.IsTree ↔ (H.induce Sᶜ).IsTree := by
  let toComplement : ((G.toSubgraph H h).deleteVerts S).verts → {v : V // v ∈ Sᶜ} :=
    fun v ↦ ⟨v.1, v.2.2⟩
  let fromComplement : {v : V // v ∈ Sᶜ} → ((G.toSubgraph H h).deleteVerts S).verts :=
    fun v ↦ ⟨v.1, ⟨Set.mem_univ v.1, v.2⟩⟩
  have hleft : Function.LeftInverse fromComplement toComplement := by
    intro v
    -- Both maps preserve the ambient vertex and differ only in proof fields.
    apply Subtype.ext
    rfl
  have hright : Function.RightInverse fromComplement toComplement := by
    intro v
    -- The reverse composite likewise preserves the underlying complement vertex.
    apply Subtype.ext
    rfl
  have hadj : ∀ u v,
      (H.induce Sᶜ).Adj (toComplement u) (toComplement v) ↔
        ((G.toSubgraph H h).deleteVerts S).coe.Adj u v := by
    intro u v
    -- Both adjacency relations reduce to adjacency in `H`; the vertex restrictions are already
    -- carried by the two subtype domains.
    simp [SimpleGraph.toSubgraph, toComplement]
  let deletionIso : ((G.toSubgraph H h).deleteVerts S).coe ≃g H.induce Sᶜ :=
    { toFun := toComplement
      invFun := fromComplement
      left_inv := hleft
      right_inv := hright
      map_rel_iff' := fun {u v} ↦ hadj u v }
  -- Treehood is invariant under the explicit complement-subtype graph isomorphism.
  exact deletionIso.isTree_iff

end SimpleGraph
