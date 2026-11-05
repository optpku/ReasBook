module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Category.Profinite.Basic
import stacks_project.Chap05.Lemma_5_12_10
import stacks_project.Chap05.Lemma_5_22_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

/- Domain-style sampling for connected components of spectral spaces:
- primary domain: connected-component quotients and profinite topology
- inspected owner declarations:
  `PrespectralSpace.connectedComponent_eq_iInter_isClopen`,
  `ConnectedComponents.t2_of_connectedComponent_eq_iInter_isClopen`,
  `connectedComponents_exists_profinite`,
  `Profinite.of`
- best owner abstraction: the quotient owner `ConnectedComponents X`, with profiniteness expressed
  through the canonical bundled owner `Profinite`

Layer triage:
- `source-facing`: Lemma 5.23.9, asserting that the connected-components quotient of a spectral
  space is profinite
- `core/canonical`: `ConnectedComponents X` and the owner theorem
  `connectedComponents_exists_profinite`
- `bridge/view`: the spectral-space specialization obtained from
  `PrespectralSpace.connectedComponent_eq_iInter_isClopen`

Primitive data is only the ambient spectral-space structure. The clopen-neighborhood description of
connected components is derived from the canonical owner theorem in
`PrespectralSpace.connectedComponent_eq_iInter_isClopen`, and the bundled profinite space is then
the canonical `Profinite.of (ConnectedComponents X)`. A local alias for that bundled object would
therefore duplicate existing owner API rather than add source mathematics.
-/

-- Proof sketch: in a spectral space, connected components are intersections of the clopen
-- neighborhoods of their points by Lemma 5.12.10. Lemma 5.22.5 is then the exact owner theorem
-- turning that description into a profinite realization of `ConnectedComponents X`.
/-- Lemma 5.23.9: if `X` is a spectral space, then `π₀(X)` is profinite. The canonical Lean model
of `π₀(X)` is `ConnectedComponents X`; its bundled profinite realization is the owner object
`Profinite.of (ConnectedComponents X)`, so no separate local alias is needed here. -/
theorem connectedComponents_exists_profinite_of_spectralSpace :
    ∃ P : Profinite.{u}, Nonempty (ConnectedComponents X ≃ₜ P) := by
  -- Specialize Lemma 5.12.10 to identify each connected component with the intersection of the
  -- clopen neighborhoods of its point.
  -- Feed that structural description into Lemma 5.22.5, which is exactly the profinite existence
  -- criterion for connected components.
  exact
    connectedComponents_exists_profinite
      PrespectralSpace.connectedComponent_eq_iInter_isClopen

end
