/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_5_6

open scoped Monoid.Coprod
open FreeGroup

universe u v w

-- Declarations for this item are recorded in this dedicated item file.

-- Primary domain: one-relator groups and free-product decompositions.
-- Layer triage:
-- `source-facing`: a one-relator presentation on generators `x₁, …, xₙ`, together with the
-- hypothesis that the relator has minimal reduced length in its automorphism orbit and uses
-- exactly the first `k` generators.
-- `core/canonical`: `PresentedGroup` for one-relator presentations, `MulAut (FreeGroup (Fin n))`
-- for automorphisms of the ambient free group, `reducedWordSupport` for reduced-word support, and
-- `Monoid.Coprod` for the free-product decomposition.
-- `bridge/view`: the source phrase “`G₁ = (x₁, …, x_k; r)`” is encoded by the canonical relator
-- obtained from `r` by the owner map `FreeGroup.lift` that keeps the first `k` generators and
-- sends the remaining ambient generators to `1`.
-- Domain sampling:
-- 1. `PresentedGroup ({r} : Set (FreeGroup (Fin n)))` is the canonical one-relator owner object.
-- 2. `MulAut (FreeGroup (Fin n))` is the owner abstraction for `Aut(F)`.
-- 3. `reducedWordSupport` from Proposition `1-5-6` is the project's owner abstraction for the
--    basis letters occurring in the canonical reduced word of a free-group element.
-- 4. `Fin.castLE` and `Fin.castLEEmb` are the canonical initial-segment inclusions `Fin k ↪ Fin n`
--    used to embed the smaller relator support into the ambient free group.
-- 5. `Monoid.Coprod` with notation `G₁ ∗ G₂` is mathlib's owner abstraction for free products.
-- Primitive vs. derived:
-- the primitive data are the relator `r`, the cutoff `k`, and the two source hypotheses. The
-- smaller relator, the induced one-relator factor on the first `k` generators, and the free
-- factor are derived canonical presentation-level objects.

section

/-- A group is freely indecomposable when any free-product decomposition has a trivial factor. -/
class IsFreelyIndecomposable (G : Type u) [Group G] : Prop where
  of_mulEquiv_coprod {A : Type*} {B : Type*} [Group A] [Group B]
    (e : G ≃* A ∗ B) : Subsingleton A ∨ Subsingleton B

namespace IsFreelyIndecomposable

/-- Free indecomposability is invariant under multiplicative equivalence. -/
theorem of_mulEquiv {G : Type u} {G' : Type v} [Group G] [Group G'] (e : G ≃* G')
    (hG : IsFreelyIndecomposable G) :
    IsFreelyIndecomposable G' := by
  sorry

/-- Free indecomposability is preserved and reflected by multiplicative equivalence. -/
theorem iff_mulEquiv {G : Type u} {G' : Type v} [Group G] [Group G'] (e : G ≃* G') :
    IsFreelyIndecomposable G ↔ IsFreelyIndecomposable G' :=
  ⟨of_mulEquiv e, of_mulEquiv e.symm⟩

end IsFreelyIndecomposable

end

section

private def initialSegmentRelator
    {n : ℕ} (k : ℕ) (r : FreeGroup (Fin n)) :
    FreeGroup (Fin k) :=
  lift (fun i ↦ if hi : (i : ℕ) < k then of ⟨i, hi⟩ else 1) r

variable {n k : ℕ} (hk : k ≤ n) (r : FreeGroup (Fin n))

local notation "r₀" => initialSegmentRelator k r
local notation "G" => PresentedGroup (Set.singleton r)
local notation "G₁" => PresentedGroup (Set.singleton r₀)
local notation "G₂" => FreeGroup (Fin (n - k))

-- Proof sketch: use the minimal-length hypothesis together with the exact support condition to
-- isolate the first `k` generators as the unique support of the relator. Rewrite the original
-- one-relator presentation as the free product of the smaller one-relator presentation on those
-- generators and the free group on the remaining generators. Then apply Magnus's
-- freely-indecomposable theorem to the smaller factor.
/-- Proposition 2-5-12: if the relator `r` in the one-relator presentation
`(x₁, …, xₙ; r)` has minimal reduced-word length in its automorphism orbit and its reduced-word
support is exactly the first `k` generators, then the presented group splits as the free product
of the one-relator group on those `k` generators and a free group on the remaining generators,
and the smaller one-relator factor is freely indecomposable. -/
theorem one_relator_group_freeProduct_decomposition
    (hmin : ∀ α : MulAut (FreeGroup (Fin n)),
      r.toWord.length ≤ (α r).toWord.length)
    (hsupp : reducedWordSupport r = (Finset.univ : Finset (Fin k)).map (Fin.castLEEmb hk)) :
    ∃ e : G ≃* (G₁ ∗ G₂), IsFreelyIndecomposable G₁ := sorry

end
