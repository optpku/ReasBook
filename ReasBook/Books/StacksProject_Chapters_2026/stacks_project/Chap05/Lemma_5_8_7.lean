module

public import Mathlib.Topology.Sober
import Mathlib.Tactic.Recall
import Mathlib.Topology.LocallyClosed

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology

universe u

section

variable {X : Type u} [TopologicalSpace X] {Y : Set X}

/- Domain-style sampling for locally closed subspaces in sober topology:
- primary domain: separation and sobriety properties of subtype spaces
- sampled canonical declarations:
  `Subtype.t0Space`
  `IsLocallyClosed.isOpen_preimage_val_closure`
  `Topology.IsClosedEmbedding.quasiSober`
  `Topology.IsOpenEmbedding.quasiSober`

Layer triage:
- `source-facing`: Lemma 5.8.7, asserting that locally closed subspaces inherit Kolmogorov,
  quasi-sober, and sober structure
- `core/canonical`: `T0Space` and `QuasiSober`
- `bridge/view`: a locally closed subset as an open subspace of its closure

Primitive data are just the subset `Y` and the proof `hY : IsLocallyClosed Y`. The induced
`T0Space` and `QuasiSober` structures are derived from the owner abstractions above, so this file
should expose bridge theorems on `IsLocallyClosed`, not parallel wrapper APIs around subtype
spaces.
-/

/- Every subspace of a Kolmogorov space is Kolmogorov. This is the canonical
subtype instance `Subtype.t0Space`. -/
recall Subtype.t0Space

/-- Lemma 5.8.7 (1): a locally closed subspace of a quasi-sober space is quasi-sober. -/
-- Proof sketch: a locally closed subset is open in its closure. The closure subtype is
-- quasi-sober because it is a closed subspace of `X`, and the inclusion `Y ↪ closure Y`
-- is an open embedding, so `Y` is quasi-sober.
protected theorem IsLocallyClosed.quasiSober
    [QuasiSober X] (hY : IsLocallyClosed Y) : QuasiSober Y := by
  letI : QuasiSober (closure Y) := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  exact (IsOpenEmbedding.inclusion (subset_closure : Y ⊆ closure Y)
    hY.isOpen_preimage_val_closure).quasiSober

/-- Lemma 5.8.7 (2): a locally closed subspace of a sober space is sober, expressed in the
canonical owner form `T0Space ∧ QuasiSober`. -/
-- Proof sketch: sobriety is owned by the pair `T₀ +` quasi-sobriety. The subtype inherits
-- `T0Space` from `X`, and clause `(1)` supplies the quasi-sober part.
protected theorem IsLocallyClosed.sober
    [T0Space X] [QuasiSober X] (hY : IsLocallyClosed Y) : T0Space Y ∧ QuasiSober Y :=
  ⟨inferInstance, hY.quasiSober⟩

end
