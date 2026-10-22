/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

universe u

noncomputable section

section

variable {G : Type u} [Group G]

/-- The augmentation ideal of the integral group ring of `G`. -/
private abbrev groupRingAugmentationIdeal (G : Type u) [Group G] :
    Ideal (MonoidAlgebra ℤ G) :=
  RingHom.ker (Bialgebra.counitAlgHom ℤ (MonoidAlgebra ℤ G))

/-- The augmentation ideal of the noncommutative free algebra on `m` generators. -/
private abbrev freeAlgebraAugmentationIdeal (m : ℕ) : Ideal (FreeAlgebra ℤ (Fin m)) :=
  RingHom.ker (FreeAlgebra.algebraMapInv : FreeAlgebra ℤ (Fin m) →ₐ[ℤ] ℤ)

/-- The truncated Magnus algebra on `m` generators modulo the `n`th augmentation-ideal power. -/
private abbrev truncatedFoxMagnusAlgebra (m n : ℕ) :=
  FreeAlgebra ℤ (Fin m) ⧸ freeAlgebraAugmentationIdeal m ^ n

private def dimensionSubgroupToUnits (G : Type u) [Group G] (n : ℕ) :
    G →* Units ((MonoidAlgebra ℤ G) ⧸ groupRingAugmentationIdeal G ^ n) :=
  ((Ideal.Quotient.mk (groupRingAugmentationIdeal G ^ n)).toMonoidHom.comp
    (MonoidAlgebra.of ℤ G)).toHomUnits

/-- The section-10 dimension subgroup `D_n(G)`, defined by the `n`-th power of the augmentation
ideal of the integral group ring of `G`, equivalently the kernel of the canonical quotient
representation into the units of `ℤ[G] / I^n`. -/
def dimensionSubgroup (G : Type u) [Group G] (n : ℕ) : Subgroup G :=
  (dimensionSubgroupToUnits G n).ker

/-- Membership in `D_n(G)` is the usual augmentation-ideal condition
`MonoidAlgebra.of ℤ G g - 1 ∈ I^n`. -/
@[simp] theorem mem_dimensionSubgroup_iff {n : ℕ} {g : G} :
    g ∈ dimensionSubgroup G n ↔
      MonoidAlgebra.of ℤ G g - 1 ∈ groupRingAugmentationIdeal G ^ n := by
  rw [dimensionSubgroup, MonoidHom.mem_ker, ← Units.val_inj]
  simp [dimensionSubgroupToUnits, Ideal.Quotient.mk_eq_one_iff_sub_mem]

/-- The section-10 Magnus/Fox filtration `L_n(G)`, realized as the intersection of the kernels of
all representations of `G` into the unit groups of the truncated noncommutative Magnus algebras
`ℤ⟨X₁, …, X_m⟩ / I^n`, where `I` is the augmentation ideal. -/
def foxMagnusSeries (G : Type u) [Group G] (n : ℕ) : Subgroup G :=
  ⨅ m : ℕ, ⨅ ρ : G →* Units (truncatedFoxMagnusAlgebra m n), ρ.ker

-- Layer triage:
-- `source-facing`: the textbook filtrations `G_n`, `L_n(G)`, and `D_n(G)`.
-- `core/canonical`: mathlib's owner lower central series `lowerCentralSeries G`, the augmentation
-- ideals of `MonoidAlgebra ℤ G` and `FreeAlgebra ℤ (Fin m)`, together with quotient rings by
-- powers of those ideals and their unit groups.
-- `bridge/view`: the textbook lower central term `G_n` starts with `G_1 = G`, whereas mathlib
-- uses `lowerCentralSeries G 0 = G`; the theorem below therefore uses the Lean index `n` to encode
-- the textbook index `n + 1`.
-- Domain sampling:
-- 1. `lowerCentralSeries G` is the canonical descending central series in mathlib.
-- 2. `foxMagnusHom` from Proposition `1-10-1` is the chapter's earlier Magnus owner on a chosen
--    free basis, so this file should only add the source-facing all-representations filtration and
--    not a second basis-packaged Magnus map.
-- 3. `foxTriangularRepresentation` from Definition `1-10-7` is the project owner for the Fox
--    representation viewpoint, confirming that the representation targets here are derived from the
--    augmentation owners rather than primitive public data.
-- 4. `Bialgebra.counitAlgHom` and `FreeAlgebra.algebraMapInv`, together with `RingHom.ker`, are
--    the canonical augmentation owners on the integral group ring and the noncommutative free
--    algebra.
-- Primitive vs. derived:
-- the primitive section-10 data are the augmentation filtrations on the integral group ring and on
-- the noncommutative free algebra; the truncated Magnus targets and the quotient-to-units map
-- defining `dimensionSubgroup G n` are derived quotient owners, and the subgroup
-- `foxMagnusSeries G n` is the derived intersection of the resulting representation kernels on `G`.

/- Proposition 1-10-3: after reindexing the lower central series to match the textbook convention
`G_1 = G`, every group satisfies
`G_{n + 1} ⊆ L_{n + 1}(G) ⊆ D_{n + 1}(G)`. In Lean this is
`lowerCentralSeries G n ≤ foxMagnusSeries G (n + 1)` and
`foxMagnusSeries G (n + 1) ≤ dimensionSubgroup G (n + 1)`.

The atomic inclusions are exposed first as the reusable public API, and the original chained
statement is then recovered as a bundled companion theorem. -/
-- Proof sketch: the first inclusion comes from the standard fact that, after quotienting the
-- target noncommutative Magnus algebra by the `(n + 1)`st augmentation power, every such reduced
-- representation factors through an `n`-step nilpotent quotient, so it kills the `(n + 1)`st
-- textbook lower-central term. For the second inclusion, apply the Magnus/Fox formula `(*)` to
-- compare the augmentation filtration on those truncated Magnus representations with powers of the
-- augmentation ideal in the integral group ring.
/-- Proposition 1-10-3, first inclusion: the `(n + 1)`st textbook lower-central term lies in the
Magnus/Fox filtration term `L_{n + 1}(G)`. -/
theorem lowerCentralSeries_le_foxMagnusSeries (n : ℕ) :
    lowerCentralSeries G n ≤ foxMagnusSeries G (n + 1) := sorry

/-- Proposition 1-10-3, second inclusion: the Magnus/Fox filtration term `L_{n + 1}(G)` lies in
the section-10 dimension subgroup `D_{n + 1}(G)`. -/
theorem foxMagnusSeries_le_dimensionSubgroup (n : ℕ) :
    foxMagnusSeries G (n + 1) ≤ dimensionSubgroup G (n + 1) := sorry

/-- Proposition 1-10-3 in its original chained form. -/
theorem lowerCentralSeries_le_foxMagnusSeries_le_dimensionSubgroup (n : ℕ) :
    lowerCentralSeries G n ≤ foxMagnusSeries G (n + 1) ∧
      foxMagnusSeries G (n + 1) ≤ dimensionSubgroup G (n + 1) :=
  ⟨lowerCentralSeries_le_foxMagnusSeries n, foxMagnusSeries_le_dimensionSubgroup n⟩

end
