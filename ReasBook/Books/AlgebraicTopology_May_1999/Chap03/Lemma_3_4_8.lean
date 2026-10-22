/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_7
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open QuotientGroup
open scoped Pointwise

namespace Subgroup

variable {G : Type u} [Group G]

/-- A coset `γK` is `H`-fixed in `G ⧸ K` exactly when `γ⁻¹ H γ ≤ K`. -/
-- Proof sketch: rewrite the fixed-coset condition as `(h * γ)K = γK` for every `h ∈ H`, then use
-- the quotient-group criterion for equality of left cosets to identify this with
-- `γ⁻¹ * h * γ ∈ K`.
theorem mem_fixedPoints_iff_conj_le (H K : Subgroup G) (γ : G) :
    ((γ : G ⧸ K) ∈ MulAction.fixedPoints H (G ⧸ K)) ↔
      MulAut.conj γ⁻¹ • H ≤ K := by
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro h
    rw [Subgroup.pointwise_smul_def]
    rintro _ ⟨h', hh', rfl⟩
    have hq : (((h'⁻¹ : G) * γ : G) : G ⧸ K) = (γ : G ⧸ K) := by
      simpa using h ⟨h'⁻¹, H.inv_mem hh'⟩
    simpa [MulAut.conj_apply, mul_assoc] using
      (show γ⁻¹ * h' * γ ∈ K by
        simpa [mul_assoc] using (QuotientGroup.eq.mp hq))
  · intro h h'
    rw [Subgroup.pointwise_smul_def] at h
    apply QuotientGroup.eq.mpr
    have hk : γ⁻¹ * ((h' : G)⁻¹) * γ ∈ K := by
      exact h ⟨(h' : G)⁻¹, H.inv_mem h'.2, by simp [mul_assoc]⟩
    simpa [mul_assoc] using hk

/-- Evaluation at the identity coset sends a morphism in the orbit category to its corresponding
`H`-fixed coset in `G ⧸ K`. -/
def orbitCategoryHomEvalOne (H K : O(G)) :
    (H ⟶ K) → MulAction.fixedPoints (H : Subgroup G) (G ⧸ K) :=
  fun α ↦ ⟨α.toFun ((1 : G) : G ⧸ H), quotient_mulActionHom_apply_one_mem_fixedPoints α⟩

/-- Helper for Lemma 3.4.8: an `H`-fixed coset has stabilizer containing `H`. -/
theorem fixed_points_le_stabilizer_quotient (H K : O(G))
    (x : MulAction.fixedPoints (H : Subgroup G) (G ⧸ K)) :
    (H : Subgroup G) ≤ MulAction.stabilizer G (x : G ⧸ K) := by
  -- Rewrite fixedness as a stabilizer condition for each element of `H`.
  intro h hh
  rw [MulAction.mem_stabilizer_iff]
  exact (MulAction.mem_fixedPoints.mp x.2) ⟨h, hh⟩

/-- Helper for Lemma 3.4.8: quotient maps induced by subgroup inclusions commute with the
ambient `G`-action on quotient sets. -/
theorem quotientMapOfLE_smul {H L : Subgroup G} (h : H ≤ L) (g : G) (q : G ⧸ H) :
    Subgroup.quotientMapOfLE h (g • q) = g • Subgroup.quotientMapOfLE h q := by
  -- Check the formula on representatives, where both sides are definitional.
  refine Quotient.inductionOn' q ?_
  intro a
  simp [Subgroup.quotientMapOfLE_apply_mk]

/-- Helper for Lemma 3.4.8: the orbit map attached to an `H`-fixed coset is `G`-equivariant. -/
theorem orbitCategoryHomOfFixedPoint_map_smul (H K : O(G))
    (x : MulAction.fixedPoints (H : Subgroup G) (G ⧸ K))
    (g : G) (q : G ⧸ H) :
    MulAction.ofQuotientStabilizer G (x : G ⧸ K)
      (Subgroup.quotientMapOfLE (fixed_points_le_stabilizer_quotient H K x) (g • q)) =
      g • MulAction.ofQuotientStabilizer G (x : G ⧸ K)
        (Subgroup.quotientMapOfLE (fixed_points_le_stabilizer_quotient H K x) q) := by
  -- Pass the action through the quotient map, then through the quotient-stabilizer map.
  rw [quotientMapOfLE_smul]
  simpa using
    (MulAction.ofQuotientStabilizer_smul G (x : G ⧸ K) g
      (Subgroup.quotientMapOfLE (fixed_points_le_stabilizer_quotient H K x) q))

/-- Helper for Lemma 3.4.8: an `H`-fixed coset determines the equivariant map `gH ↦ g • x`. -/
def orbitCategoryHomOfFixedPoint (H K : O(G)) :
    MulAction.fixedPoints (H : Subgroup G) (G ⧸ K) → (H ⟶ K) :=
  fun x ↦
    { toFun := fun q ↦
        MulAction.ofQuotientStabilizer G (x : G ⧸ K)
          (Subgroup.quotientMapOfLE (fixed_points_le_stabilizer_quotient H K x) q)
      map_smul' := orbitCategoryHomOfFixedPoint_map_smul H K x }

/-- Helper for Lemma 3.4.8: evaluating the orbit map built from a fixed coset recovers that
fixed coset. -/
theorem orbitCategoryHomEvalOne_orbitCategoryHomOfFixedPoint (H K : O(G))
    (x : MulAction.fixedPoints (H : Subgroup G) (G ⧸ K)) :
    orbitCategoryHomEvalOne H K (orbitCategoryHomOfFixedPoint H K x) = x := by
  -- Compare the underlying cosets at the identity representative.
  apply Subtype.ext
  simp [orbitCategoryHomEvalOne, orbitCategoryHomOfFixedPoint,
    Subgroup.quotientMapOfLE_apply_mk, MulAction.ofQuotientStabilizer_mk]

/-- Helper for Lemma 3.4.8: rebuilding a morphism from its value on the identity coset gives back
that morphism. -/
theorem orbitCategoryHomOfFixedPoint_orbitCategoryHomEvalOne (H K : O(G))
    (α : H ⟶ K) :
    orbitCategoryHomOfFixedPoint H K (orbitCategoryHomEvalOne H K α) = α := by
  -- Compare the two equivariant maps on quotient representatives.
  refine MulActionHom.ext ?_
  intro q
  refine Quotient.inductionOn' q ?_
  intro g
  calc
    (orbitCategoryHomOfFixedPoint H K (orbitCategoryHomEvalOne H K α)).toFun (g : G ⧸ H)
        = g • α.toFun ((1 : G) : G ⧸ H) := by
          simp [orbitCategoryHomOfFixedPoint, orbitCategoryHomEvalOne,
            Subgroup.quotientMapOfLE_apply_mk, MulAction.ofQuotientStabilizer_mk]
    -- Equivariance rewrites the original morphism on `gH` using its value on `1H`.
    _ = α.toFun (g • ((1 : G) : G ⧸ H)) := by
          exact (α.map_smul' g (((1 : G) : G ⧸ H))).symm
    _ = α.toFun (g : G ⧸ H) := by simp

/-- Evaluation at the identity coset gives a bijection from orbit-category morphisms to admissible
subconjugacy cosets, canonically realized as `H`-fixed cosets of `G ⧸ K`. -/
-- Proof sketch: injectivity is Lemma 3.4.6, which says an equivariant map is determined by the
-- image of the identity coset. Surjectivity sends an admissible coset `γK` to the unique map
-- `gH ↦ gγK`; the fixed-coset condition is exactly what makes this formula well defined.
theorem orbitCategoryHomEvalOne_bijective (H K : O(G)) :
    Function.Bijective (orbitCategoryHomEvalOne H K) := by
  constructor
  · intro α β hαβ
    -- Evaluation at `1H` determines the whole morphism, so compare both reconstructions.
    calc
      α = orbitCategoryHomOfFixedPoint H K (orbitCategoryHomEvalOne H K α) := by
        symm
        exact orbitCategoryHomOfFixedPoint_orbitCategoryHomEvalOne H K α
      _ = orbitCategoryHomOfFixedPoint H K (orbitCategoryHomEvalOne H K β) := by
        rw [hαβ]
      _ = β := orbitCategoryHomOfFixedPoint_orbitCategoryHomEvalOne H K β
  · intro x
    -- The canonical orbit map attached to `x` evaluates back to `x`.
    exact ⟨orbitCategoryHomOfFixedPoint H K x,
      orbitCategoryHomEvalOne_orbitCategoryHomOfFixedPoint H K x⟩

/-- Lemma 3.4.8: for subgroups `H, K ≤ G`, the morphisms in `O(G)` from `H` to `K` are exactly
the distinct subconjugacy relations `γ⁻¹ H γ ≤ K`, canonically encoded as `H`-fixed cosets
of `G ⧸ K`. -/
noncomputable def orbitCategoryHomEquivFixedPoints (H K : O(G)) :
    (H ⟶ K) ≃ MulAction.fixedPoints (H : Subgroup G) (G ⧸ K) :=
  Equiv.ofBijective (orbitCategoryHomEvalOne H K) (orbitCategoryHomEvalOne_bijective H K)

/-- Applying the equivalence of Lemma 3.4.8 is evaluation of an orbit-category morphism at the
identity coset. -/
-- Proof sketch: unfold `orbitCategoryHomEquivFixedPoints`; it was defined by applying
-- `Equiv.ofBijective` to `orbitCategoryHomEvalOne`.
theorem orbitCategoryHomEquivFixedPoints_apply (H K : O(G)) (α : H ⟶ K) :
    orbitCategoryHomEquivFixedPoints H K α = orbitCategoryHomEvalOne H K α := by
  -- The equivalence was defined with `orbitCategoryHomEvalOne` as its forward map.
  rfl

end Subgroup
