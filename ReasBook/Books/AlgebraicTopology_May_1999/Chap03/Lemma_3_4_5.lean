/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_4
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open CategoryTheory
open scoped Pointwise
open QuotientGroup
open Subgroup

variable {G : Type u} {S : Type v} [Group G] [MulAction G S]

/- We write the textbook notation `Aut_G(S)` as `Aut_ G S` in Lean. -/
notation "Aut_" G:arg S:arg => Aut (Action.ofMulAction G S)

/-- The concrete centralizer view of `Aut_G S` inside `Equiv.Perm S`. -/
abbrev gSetAut (G : Type u) (S : Type v) [Group G] [MulAction G S] : Subgroup (Equiv.Perm S) :=
  centralizer ((MulAction.toPermHom G S).range : Set (Equiv.Perm S))

private noncomputable def autToPerm (f : Aut_ G S) : Equiv.Perm S where
  toFun := f.hom.hom
  invFun := f.inv.hom
  left_inv x := by
    change (f.hom.hom ≫ f.inv.hom) x = x
    rw [Action.hom_inv_hom]
    rfl
  right_inv x := by
    change (f.inv.hom ≫ f.hom.hom) x = x
    rw [Action.inv_hom_hom]
    rfl

private noncomputable def autToGSetAut (f : Aut_ G S) : gSetAut G S :=
  ⟨autToPerm f, by
    intro τ hτ
    rcases hτ with ⟨g, rfl⟩
    ext x
    simpa [Action.ofMulAction_apply, autToPerm] using
      (congrArg (fun k ↦ k x) (f.hom.comm g)).symm⟩

private noncomputable def gSetAutToAut (σ : gSetAut G S) : Aut_ G S :=
  Action.mkIso σ.1.toIso fun g ↦ by
    ext x
    have hσ : (MulAction.toPermHom G S) g * σ.1 = σ.1 * (MulAction.toPermHom G S) g :=
      (show σ.1 ∈ centralizer ((MulAction.toPermHom G S).range : Set (Equiv.Perm S)) from σ.2)
        _ ⟨g, rfl⟩
    simpa [Action.ofMulAction_apply] using
      (congrArg (fun τ : Equiv.Perm S ↦ τ x) hσ).symm

/-- The intrinsic automorphism group `Aut_G S` is canonically equivalent to its concrete
centralizer view in `Equiv.Perm S`. -/
noncomputable def autMulEquivGSetAut (G : Type u) (S : Type v) [Group G] [MulAction G S] :
    Aut_ G S ≃* gSetAut G S where
  toFun := autToGSetAut
  invFun := gSetAutToAut
  left_inv f := by
    ext x
    rfl
  right_inv σ := by
    ext x
    rfl
  map_mul' f g := by
    ext x
    rfl

private noncomputable def permCongrMulEquiv {α : Type u} {β : Type v} (e : α ≃ β) :
    Equiv.Perm α ≃* Equiv.Perm β where
  toFun := e.permCongr
  invFun := e.symm.permCongr
  left_inv σ := by
    ext x
    simp [Equiv.permCongr_apply]
  right_inv σ := by
    ext x
    simp [Equiv.permCongr_apply]
  map_mul' σ τ := by
    ext x
    simp [Equiv.permCongr_apply]

private noncomputable abbrev normalizerInvOpHom (H : Subgroup G) :
    normalizer (H : Set G) →* (normalizer (H : Set G)).op where
  toFun n := ⟨MulOpposite.op ((n : G)⁻¹), by
    exact (n⁻¹).2⟩
  map_one' := by
    ext
    simp
  map_mul' := by
    intro x y
    ext
    simp

/-- Right translation by the normalizer induces permutations of `G ⧸ H`. -/
private noncomputable abbrev rightQuotientPermHom (H : Subgroup G) :
    normalizer (H : Set G) →* Equiv.Perm (G ⧸ H) :=
  (MulAction.toPermHom (normalizer (H : Set G)).op (G ⧸ H)).comp (normalizerInvOpHom H)

/-- The kernel of the right-translation action on `G ⧸ H` is the induced copy of `H` inside its
normalizer. -/
-- Proof sketch: a normalizer element acts trivially on `G ⧸ H` exactly when its right
-- translation fixes the identity coset, which is equivalent to lying in `H`.
private theorem rightQuotientPermHom_ker_eq (H : Subgroup G) :
    (rightQuotientPermHom H).ker = H.subgroupOf (normalizer (H : Set G)) := by
  ext n
  constructor
  · intro hn
    rw [MonoidHom.mem_ker] at hn
    -- Evaluate the trivial permutation at the identity coset to read off membership in `H`.
    have hfix := congrArg (fun σ : Equiv.Perm (G ⧸ H) ↦ σ (((1 : G) : G ⧸ H))) hn
    simp [rightQuotientPermHom, normalizerInvOpHom, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hfix ⊢
    exact hfix
  · intro hn
    rw [MonoidHom.mem_ker]
    have hn' : (n : G) ∈ H := by
      simpa [Subgroup.mem_subgroupOf] using hn
    -- An element of `H` acts trivially on every left coset by right translation.
    ext q
    refine Quotient.inductionOn' q fun g ↦ ?_
    simp [rightQuotientPermHom, normalizerInvOpHom, hn']

/-- Helper for Lemma 3.4.5: a concrete `G`-set automorphism commutes with the left `G`-action. -/
private theorem gSetAut_apply_smul (σ : gSetAut G S) (g : G) (x : S) :
    σ.1 (g • x) = g • σ.1 x := by
  -- Centralizing the image of `toPermHom` is exactly equivariance.
  have hcomm : (MulAction.toPermHom G S) g * σ.1 = σ.1 * (MulAction.toPermHom G S) g :=
    (Subgroup.mem_centralizer_iff.mp σ.2) _ ⟨g, rfl⟩
  have happly := congrArg (fun τ : Equiv.Perm S ↦ τ x) hcomm
  simpa using happly.symm

/-- Helper for Lemma 3.4.5: the image of the identity coset determines a unique normalizer
element producing the same quotient permutation. -/
private theorem gset_aut_eq_rightQuotientPermHom_of_apply_one (H : Subgroup G)
    (σ : gSetAut G (G ⧸ H)) :
    ∃ n : normalizer (H : Set G), rightQuotientPermHom H n = σ.1 := by
  let q₀ : G ⧸ H := σ.1 (((1 : G) : G ⧸ H))
  let n : G := q₀.out
  have hσcomm : ∀ g : G, σ.1 ((g : G ⧸ H)) = g • q₀ := by
    intro g
    -- Equivariance lets us compute `σ` on every coset from its value at `1H`.
    simpa [q₀] using gSetAut_apply_smul (G := G) (S := G ⧸ H) σ g (((1 : G) : G ⧸ H))
  have hn_normalizer : n ∈ normalizer (H : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro h
    constructor
    · intro hh
      -- If `h ∈ H`, then `h` fixes `1H`, so equivariance forces it to fix `q₀`.
      have hfix : h • q₀ = q₀ := by
        calc
          h • q₀ = σ.1 ((h : G) • (((1 : G) : G ⧸ H))) := by
            rw [gSetAut_apply_smul (G := G) (S := G ⧸ H) σ h (((1 : G) : G ⧸ H))]
          _ = σ.1 (((1 : G) : G ⧸ H)) := by simp [QuotientGroup.eq, hh]
          _ = q₀ := rfl
      have hquot : ((h * n : G) : G ⧸ H) = ((n : G) : G ⧸ H) := by
        calc
          ((h * n : G) : G ⧸ H) = h • ((n : G) : G ⧸ H) := by rfl
          _ = h • q₀ := by rw [QuotientGroup.out_eq' q₀]
          _ = q₀ := hfix
          _ = ((n : G) : G ⧸ H) := (QuotientGroup.out_eq' q₀).symm
      rw [QuotientGroup.eq] at hquot
      have hquot_inv : ((h * n)⁻¹ * n)⁻¹ ∈ H := H.inv_mem hquot
      simpa [n, mul_assoc] using hquot_inv
    · intro hh
      have hquot : ((h * n : G) : G ⧸ H) = ((n : G) : G ⧸ H) := by
        rw [QuotientGroup.eq]
        have hquot_inv : ((h * n)⁻¹ * n) ∈ H := by
          have hhinv : (n⁻¹ * h * n)⁻¹ ∈ H := H.inv_mem hh
          simpa [n, mul_assoc] using hhinv
        exact hquot_inv
      have hfix : h • q₀ = q₀ := by
        calc
          h • q₀ = h • ((n : G) : G ⧸ H) := by rw [QuotientGroup.out_eq' q₀]
          _ = ((h * n : G) : G ⧸ H) := by rfl
          _ = ((n : G) : G ⧸ H) := hquot
          _ = q₀ := QuotientGroup.out_eq' q₀
      -- Injectivity of `σ` brings the fixed-point condition back to the base coset.
      have hσeq : σ.1 ((h : G ⧸ H)) = σ.1 (((1 : G) : G ⧸ H)) := by
        calc
          σ.1 ((h : G ⧸ H)) = h • q₀ := hσcomm h
          _ = q₀ := hfix
          _ = σ.1 (((1 : G) : G ⧸ H)) := rfl
      have hbase : ((h : G) : G ⧸ H) = (((1 : G) : G) : G ⧸ H) := σ.1.injective hσeq
      simpa [QuotientGroup.eq] using hbase
  refine ⟨⟨n⁻¹, inv_mem hn_normalizer⟩, ?_⟩
  -- The chosen witness sends `1H` to `q₀`, so equivariance forces agreement on all cosets.
  ext q
  refine Quotient.inductionOn' q fun g ↦ ?_
  calc
    rightQuotientPermHom H ⟨n⁻¹, inv_mem hn_normalizer⟩ ((g : G ⧸ H)) = ((g * n : G) : G ⧸ H) := by
      simp [rightQuotientPermHom, normalizerInvOpHom]
    _ = g • q₀ := by
      rw [← QuotientGroup.out_eq' q₀]
      rfl
    _ = σ.1 ((g : G ⧸ H)) := by rw [hσcomm]

/-- Every `G`-equivariant automorphism of `G ⧸ H` comes from right translation by the normalizer. -/
-- Proof sketch: an equivariant automorphism is determined by the image of the identity coset, and
-- that image must be a coset `nH` with `n` normalizing `H`; this gives the required range
-- description.
private theorem rightQuotientPermHom_range_eq (H : Subgroup G) :
    (rightQuotientPermHom H).range = gSetAut G (G ⧸ H) := by
  ext σ
  constructor
  · intro hσ
    rcases hσ with ⟨n, rfl⟩
    -- Left multiplication commutes with right multiplication on cosets.
    rw [Subgroup.mem_centralizer_iff]
    intro τ hτ
    rcases hτ with ⟨g, rfl⟩
    ext q
    refine Quotient.inductionOn' q fun x ↦ ?_
    simp [rightQuotientPermHom, normalizerInvOpHom, mul_assoc]
  · intro hσ
    -- Reconstruct the normalizer element from the image of `1H`.
    rcases gset_aut_eq_rightQuotientPermHom_of_apply_one (G := G) H ⟨σ, hσ⟩ with ⟨n, hn⟩
    exact ⟨n, hn⟩

/-- The Weyl group `N_G(H) / H` in the concrete permutation-centralizer view of
`Aut_G (G ⧸ H)`. -/
noncomputable def weylGroupMulEquivQuotientGSetAut (H : Subgroup G) :
    Subgroup.weylGroup H ≃* gSetAut G (G ⧸ H) :=
  (QuotientGroup.quotientMulEquivOfEq (rightQuotientPermHom_ker_eq H)).symm.trans
    ((QuotientGroup.quotientKerEquivRange (rightQuotientPermHom H)).trans
      (MulEquiv.subgroupCongr (rightQuotientPermHom_range_eq H)))

/-- The Weyl group `N_G(H) / H` is canonically isomorphic to `Aut_G (G ⧸ H)`. -/
noncomputable def weylGroupMulEquivQuotientAut (H : Subgroup G) :
    Subgroup.weylGroup H ≃* Aut_ G (G ⧸ H) :=
  (weylGroupMulEquivQuotientGSetAut H).trans
    (autMulEquivGSetAut G (G ⧸ H)).symm

namespace Subgroup

/-- For a normal subgroup `H`, its Weyl group is canonically the quotient `G ⧸ H`. -/
noncomputable def weylGroupMulEquivQuotientOfNormal (H : Subgroup G) [H.Normal] :
    weylGroup H ≃* G ⧸ H :=
  let h_normalizer : normalizer (H : Set G) = ⊤ :=
    H.normalizer_eq_top
  let e₁ :
      normalizer H ⧸ H.subgroupOf (normalizer H) ≃*
        (⊤ : Subgroup G) ⧸ H.subgroupOf (⊤ : Subgroup G) :=
    QuotientGroup.equivQuotientSubgroupOfOfEq rfl h_normalizer
  let e₂ :
      (⊤ : Subgroup G) ⧸ H.subgroupOf (⊤ : Subgroup G) ≃* G ⧸ H :=
    QuotientGroup.congr
      (H.subgroupOf (⊤ : Subgroup G))
      H
      topEquiv
      (map_subgroupOf_eq_of_le le_top)
  e₁.trans e₂

end Subgroup

section QuotientStabilizer

variable {G : Type u} {S : Type v} [Group G] [MulAction G S]

/-- Helper for Lemma 3.4.5: the inverse quotient-stabilizer equivalence sends an element of `S`
to a quotient representative mapping back to it. -/
private theorem quotientStabilizerEquivOfIsPretransitive_symm_apply
    [MulAction.IsPretransitive G S] (s : S) (x : S) :
    MulAction.ofQuotientStabilizer G s
      ((quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s).symm x) = x := by
  have hx : quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s
      ((quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s).symm x) = x :=
    (quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s).apply_symm_apply x
  rwa [quotientStabilizerEquivOfIsPretransitive_apply] at hx

/-- Helper for Lemma 3.4.5: the inverse quotient-stabilizer equivalence is `G`-equivariant. -/
private theorem quotientStabilizerEquivOfIsPretransitive_symm_equivariant
    [MulAction.IsPretransitive G S] (s : S) (g : G) (x : S) :
    (quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s).symm (g • x) =
      g • (quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s).symm x := by
  let e := quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s
  -- Apply the forward equivariant equivalence to reduce the claim to the known equivariance law.
  apply e.injective
  calc
    e (e.symm (g • x)) = g • x := by simp [e]
    _ = MulAction.ofQuotientStabilizer G s (g • e.symm x) := by
          symm
          simpa [quotientStabilizerEquivOfIsPretransitive_apply, e] using
            quotientStabilizerEquivOfIsPretransitive_equivariant (G := G) (S := S) s g (e.symm x)
    _ = e (g • e.symm x) := by rfl

private noncomputable def quotientStabilizerGSetAutMulEquiv
    [MulAction.IsPretransitive G S] (s : S) :
    gSetAut G (G ⧸ MulAction.stabilizer G s) ≃* gSetAut G S where
  toFun σ :=
    let e := quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s
    ⟨permCongrMulEquiv e σ.1, by
      -- Conjugating by an equivariant equivalence preserves commutation with the left action.
      rw [Subgroup.mem_centralizer_iff]
      intro τ hτ
      rcases hτ with ⟨g, rfl⟩
      ext x
      calc
        ((MulAction.toPermHom G S) g * permCongrMulEquiv e σ.1) x = g • e (σ.1 (e.symm x)) := by
          simp [permCongrMulEquiv, Equiv.permCongr_apply]
        _ = e (g • σ.1 (e.symm x)) := by
          simpa [quotientStabilizerEquivOfIsPretransitive_apply] using
            (quotientStabilizerEquivOfIsPretransitive_equivariant (G := G) (S := S) s g
              (σ.1 (e.symm x))).symm
        _ = e (σ.1 (e.symm (g • x))) := by
          rw [quotientStabilizerEquivOfIsPretransitive_symm_equivariant (G := G) (S := S),
            gSetAut_apply_smul (G := G) (S := G ⧸ MulAction.stabilizer G s)]
        _ = (permCongrMulEquiv e σ.1 * (MulAction.toPermHom G S) g) x := by
          simp [permCongrMulEquiv, Equiv.permCongr_apply]⟩
  invFun τ :=
    let e := quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s
    ⟨(permCongrMulEquiv e).symm τ.1, by
      -- The same conjugation argument works in the reverse direction.
      rw [Subgroup.mem_centralizer_iff]
      intro ρ hρ
      rcases hρ with ⟨g, rfl⟩
      ext x
      calc
        ((MulAction.toPermHom G (G ⧸ MulAction.stabilizer G s)) g * (permCongrMulEquiv e).symm τ.1) x
            = g • e.symm (τ.1 (e x)) := by
              simp [permCongrMulEquiv]
        _ = e.symm (g • τ.1 (e x)) := by
              rw [← quotientStabilizerEquivOfIsPretransitive_symm_equivariant (G := G) (S := S)]
        _ = e.symm (τ.1 (g • e x)) := by
              rw [gSetAut_apply_smul (G := G) (S := S)]
        _ = e.symm (τ.1 (e (g • x))) := by
              rw [quotientStabilizerEquivOfIsPretransitive_equivariant (G := G) (S := S)]
        _ = ((permCongrMulEquiv e).symm τ.1 * (MulAction.toPermHom G (G ⧸ MulAction.stabilizer G s)) g) x := by
              simp [permCongrMulEquiv]⟩
  left_inv := by
    intro σ
    -- The forward and backward conjugations cancel pointwise.
    let e := quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s
    ext x
    have hcancel : e.symm (e (σ.1 (e.symm (e x)))) = σ.1 x := by
      rw [e.symm_apply_apply, e.symm_apply_apply]
    simpa [permCongrMulEquiv, Equiv.permCongr_apply, e,
      quotientStabilizerEquivOfIsPretransitive_apply] using hcancel
  right_inv := by
    intro τ
    -- The same cancellation gives the inverse identity on `S`.
    let e := quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s
    ext x
    have hcancel : e (e.symm (τ.1 (e (e.symm x)))) = τ.1 x := by
      rw [e.apply_symm_apply, e.apply_symm_apply]
    simpa [permCongrMulEquiv, Equiv.permCongr_apply, e,
      quotientStabilizerEquivOfIsPretransitive_apply] using hcancel
  map_mul' := by
    intro σ τ
    -- Conjugation is multiplicative on permutations.
    ext x
    simp [permCongrMulEquiv, Equiv.permCongr_apply]

/-- Lemma 3.4.5: if `G` acts transitively on `S` and `H = G_s`, then the Weyl group
`N_G(H) / H` is canonically isomorphic to the automorphism group `Aut_G S` of the `G`-set `S`. -/
noncomputable def weylGroup_stabilizer_mulEquiv_aut [MulAction.IsPretransitive G S] (s : S) :
    Subgroup.weylGroup (MulAction.stabilizer G s) ≃* Aut_ G S :=
  (weylGroupMulEquivQuotientAut (MulAction.stabilizer G s)).trans
    ((autMulEquivGSetAut G (G ⧸ MulAction.stabilizer G s)).trans
      ((quotientStabilizerGSetAutMulEquiv s).trans (autMulEquivGSetAut G S).symm))

/-- Evaluating the Weyl-group equivalence amounts to first identify the Weyl group with
`Aut_G (G ⧸ G_s)`, pass to the concrete centralizer model, and then transport along the
quotient-stabilizer equivariant equivalence with `S`. -/
-- Proof sketch: unfold `weylGroup_stabilizer_mulEquiv_aut` and evaluate the composite
-- equivalence on the given quotient element.
theorem weylGroup_stabilizer_mulEquiv_aut_apply [MulAction.IsPretransitive G S] (s : S)
    (x : Subgroup.weylGroup (MulAction.stabilizer G s)) :
    weylGroup_stabilizer_mulEquiv_aut s x =
      (autMulEquivGSetAut G S).symm
        (quotientStabilizerGSetAutMulEquiv s
          ((autMulEquivGSetAut G (G ⧸ MulAction.stabilizer G s))
            (weylGroupMulEquivQuotientAut (MulAction.stabilizer G s) x))) := by
  -- This is exactly the value of the composite equivalence after unfolding the definition.
  rfl

end QuotientStabilizer
