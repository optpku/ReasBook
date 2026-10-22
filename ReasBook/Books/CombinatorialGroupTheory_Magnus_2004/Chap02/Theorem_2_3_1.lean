/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory groupHomology Rep

-- Primary domain: low-degree group homology attached to a free presentation.
-- Layer triage:
-- `source-facing`: a free presentation `π : F →* G` with `F` free, kernel `N = π.ker`, and the
-- Hopf-formula identification of the second integral homology with `(N ∩ [F, F]) / [F, N]`.
-- `core/canonical`: the bundled trivial representation `Rep.trivial ℤ G ℤ`, the low-degree owner
-- object `groupHomology.H2` together with its `≅`-valued comparison API such as
-- `groupHomology.H2Iso`, the commutator subgroup `_root_.commutator F`, and the subgroup
-- commutator `⁅(⊤ : Subgroup F), π.ker⁆`.
-- `bridge/view`: the source quotient is viewed as an object of `ModuleCat ℤ` via `Additive`; a
-- helper commutativity instance records that this quotient is abelian.
-- Domain sampling:
-- 1. `groupHomology.H2` and the comparison isomorphism pattern `groupHomology.H2Iso` are the
--    owner-side API for second group homology.
-- 2. `Rep.trivial ℤ G ℤ` is the canonical trivial integral `G`-representation.
-- 3. `_root_.commutator F` is the owner-side commutator subgroup `[F, F]`.
-- 4. `⁅(⊤ : Subgroup F), π.ker⁆` is the ambient-group realization of `[F, N]`.
-- 5. `Subgroup.subgroupOf` is the canonical way to form the denominator subgroup inside
--    `π.ker ⊓ commutator F`.
-- Primitive vs. derived:
-- the primitive source data are the free group `F`, the presentation map `π`, and the
-- surjectivity hypothesis. The quotient appearing in Hopf's formula is derived directly from
-- `π.ker` and the commutator constructions, so no wrapper around presentation data is introduced.
-- The later prose in the source item about free and amalgamated products is bibliographic
-- motivation rather than a separate atomic theorem statement, so only the explicit Hopf formula is
-- formalized here.

noncomputable section

variable {F G : Type} [Group F] [IsFreeGroup F] [Group G]

/-- The quotient `(ker π ∩ [F, F]) / [F, ker π]` appearing in Hopf's formula. -/
abbrev hopfFormulaQuotient (π : F →* G) :=
  ((π.ker ⊓ commutator F) : Subgroup F) ⧸
    (⁅(⊤ : Subgroup F), π.ker⁆).subgroupOf ((π.ker ⊓ commutator F) : Subgroup F)

-- Proof sketch: `⁅π.ker ⊓ commutator F, π.ker ⊓ commutator F⁆` is contained in
-- `⁅⊤, π.ker⁆` by monotonicity of subgroup commutators, so the quotient of
-- `π.ker ⊓ commutator F` by `⁅⊤, π.ker⁆.subgroupOf (π.ker ⊓ commutator F)` is commutative.
/-- The quotient appearing on the right-hand side of Hopf's formula is a commutative group. -/
instance (π : F →* G) : CommGroup (hopfFormulaQuotient π) := by
  let H : Subgroup F := π.ker ⊓ commutator F
  let K : Subgroup H := (⁅(⊤ : Subgroup F), π.ker⁆).subgroupOf H
  have hcomm : _root_.commutator H ≤ K := by
    intro x hx
    change ((x : H) : F) ∈ ⁅(⊤ : Subgroup F), π.ker⁆
    have hx' : ((x : H) : F) ∈ (_root_.commutator H).map H.subtype := ⟨x, hx, rfl⟩
    rw [Subgroup.map_subtype_commutator] at hx'
    exact (Subgroup.commutator_mono
      (by simp)
      (by simp [H])) hx'
  let hmulComm := Subgroup.Normal.quotient_commutative_iff_commutator_le.2 hcomm
  letI : CommGroup (H ⧸ K) := ⟨hmulComm.is_comm.comm⟩
  simpa [hopfFormulaQuotient, H, K]

/-- Theorem 2-3-1: for a surjection `π : F →* G` from a free group, Hopf's formula identifies the
second integral homology of `G` with the quotient `(ker π ∩ [F, F]) / [F, ker π]` by exhibiting an
isomorphism in `ModuleCat ℤ`. -/
-- Proof sketch: start from the presentation resolution attached to `π`, compute the second
-- homology of the trivial integral representation via that free resolution, and identify the
-- resulting cokernel with the quotient built from `π.ker`, the ambient commutator subgroup of
-- `F`, and the subgroup commutator `⁅⊤, π.ker⁆`.
theorem hopf_formula_second_homology_of_free_presentation
    (π : F →* G) (hπ : Function.Surjective π) :
    Nonempty (H2 (trivial ℤ G ℤ) ≅
      ModuleCat.of ℤ (Additive (hopfFormulaQuotient π))) := by
  sorry

end
