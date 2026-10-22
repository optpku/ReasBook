/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

variable {H G : Type u}
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Helper for Problem 3.9.2: the kernel of a covering homomorphism inherits the discrete
topology from the fiber over `1`. -/
private theorem kernel_discreteTopology_of_covering
    (p : H →ₜ* G) (hp : IsCoveringMap (p : H → G)) :
    DiscreteTopology p.ker := by
  -- The kernel is exactly the fiber over the identity element.
  simpa using (hp 1).discreteTopology_fiber

/-- Helper for Problem 3.9.2: the conjugation map into a discrete normal subgroup is constant on a
connected group. -/
private theorem conjugation_to_discrete_normal_subgroup_constant
    [ConnectedSpace G] {N : Subgroup G} [DiscreteTopology N] [hN : N.Normal]
    (n : G) (hn : n ∈ N) :
    ∀ g : G, (⟨g * n * g⁻¹, hN.conj_mem n hn g⟩ : N) = ⟨n, hn⟩ := by
  let c : G → N := fun x ↦ ⟨x * n * x⁻¹, hN.conj_mem n hn x⟩
  -- A continuous map from a connected space to a discrete space must be constant.
  have hc : Continuous c := by
    exact Continuous.subtype_mk
      ((continuous_id.mul continuous_const).mul continuous_inv)
      (fun x ↦ hN.conj_mem n hn x)
  intro g
  simpa [c] using TotallyDisconnectedSpace.eq_of_continuous c hc g 1

/-- Helper for Problem 3.9.2: a covering-space automorphism preserves the base projection
pointwise. -/
private theorem covering_space_aut_comm
    (p : H →ₜ* G) (α : Aut (Over.mk (TopCat.ofHom p.toContinuousMap))) (x : H) :
    p (α.hom.left.hom x) = p x := by
  -- Evaluate the commutative triangle defining the morphism in `Over`.
  have hx := congrArg
    (fun f : TopCat.of H ⟶ TopCat.of G ↦ f.hom x)
    (Over.w α.hom)
  simpa [ContinuousMap.comp_apply] using hx

/-- Problem 3.9.2 (1): the kernel of a covering homomorphism is a discrete normal subgroup. -/
-- Proof sketch: the kernel is the fiber over `1`, so its discreteness comes from the covering
-- condition. Normality is the usual kernel-normality property of a group homomorphism.
theorem kernel_discrete_and_normal
    (p : H →ₜ* G) (hp : IsCoveringMap (p : H → G)) :
    DiscreteTopology p.ker ∧ p.ker.Normal := by
  -- Combine the covering-space discreteness of the fiber with kernel normality.
  refine ⟨kernel_discreteTopology_of_covering p hp, ?_⟩
  simpa using p.toMonoidHom.normal_ker

/-- Problem 3.9.2 (2): a discrete normal subgroup of a connected topological group is central. -/
-- Proof sketch: for each `n ∈ N`, the conjugation map `g ↦ g * n * g⁻¹` is continuous from the
-- connected space `G` into the discrete subgroup `N`, hence constant. Evaluating at `1` shows
-- every conjugate of `n` equals `n`.
theorem discreteNormalSubgroup_le_center
    [ConnectedSpace G] {N : Subgroup G} [DiscreteTopology N] [N.Normal] :
    N ≤ Subgroup.center G := by
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  -- The conjugation map is constant, so the conjugate of `n` by `g` is again `n`.
  have hconj := congrArg Subtype.val
    (conjugation_to_discrete_normal_subgroup_constant (N := N) n hn g)
  have hconj' : g * n * g⁻¹ = n := by
    simpa using hconj
  calc
    g * n = (g * n * g⁻¹) * g := by group
    _ = n * g := by rw [hconj']

-- Left translation by a kernel element lies over the covering homomorphism `p`.
-- Proof sketch: if `k ∈ ker p`, then `p (k * h) = p k * p h = p h`, so left translation by `k`
-- commutes with the map `p`.
private theorem kernelLeftTranslation_over
    (p : H →ₜ* G) (k : p.ker) :
    TopCat.ofHom (Homeomorph.mulLeft (k : H)) ≫ TopCat.ofHom p.toContinuousMap =
      TopCat.ofHom p.toContinuousMap := by
  -- Evaluate the commutative triangle pointwise and use `p k = 1`.
  ext x
  have hk : p (k : H) = 1 := k.2
  simp [Homeomorph.coe_mulLeft, hk, map_mul]

/-- Left translation by a kernel element defines a covering-space automorphism of `p`. -/
def kernelLeftTranslationAut
    (p : H →ₜ* G) (k : p.ker) :
    Aut (Over.mk (TopCat.ofHom p.toContinuousMap)) :=
  Over.isoMk
    ((TopCat.isoOfHomeo (Homeomorph.mulLeft (k : H))) : TopCat.of H ≅ TopCat.of H)
    (kernelLeftTranslation_over p k)

/-- Left translation by the identity kernel element is the identity covering automorphism. -/
-- Proof sketch: multiplication by `1` is the identity map on `H`, hence also the identity in the
-- over-category.
theorem kernelLeftTranslationAut_one
    (p : H →ₜ* G) :
    kernelLeftTranslationAut p (1 : p.ker) = 1 := by
  -- It suffices to compare the underlying morphisms in `Over`.
  apply Iso.ext
  apply CostructuredArrow.hom_ext
  ext x
  change ((Homeomorph.mulLeft (1 : H)) x : H) = x
  simp [Homeomorph.coe_mulLeft]

/-- Left translation sends multiplication in the kernel to multiplication in the covering
automorphism group. -/
-- Proof sketch: the composite of left translations by `k` and `l` is left translation by
-- `k * l`, and multiplication in `Aut` is composition.
theorem kernelLeftTranslationAut_mul
    (p : H →ₜ* G) (k l : p.ker) :
    kernelLeftTranslationAut p (k * l) =
      kernelLeftTranslationAut p k * kernelLeftTranslationAut p l := by
  -- The underlying homeomorphisms compose exactly by multiplication in the group.
  have hIso :
      (TopCat.isoOfHomeo (Homeomorph.mulLeft (((k * l : p.ker) : H))) :
          TopCat.of H ≅ TopCat.of H) =
        (TopCat.isoOfHomeo (Homeomorph.mulLeft (l : H)) :
            TopCat.of H ≅ TopCat.of H) ≪≫
          (TopCat.isoOfHomeo (Homeomorph.mulLeft (k : H)) :
            TopCat.of H ≅ TopCat.of H) := by
    apply Iso.ext
    ext x
    change (↑(k * l) : H) * x = ↑k * (↑l * x)
    change (↑k * ↑l) * x = ↑k * (↑l * x)
    simp [mul_assoc]
  rw [CategoryTheory.Aut.Aut_mul_def]
  apply Iso.ext
  apply CostructuredArrow.hom_ext
  simpa [kernelLeftTranslationAut, TopCat.isoOfHomeo_hom, CategoryTheory.Iso.trans_hom] using
    congrArg Iso.hom hIso

/-- The canonical homomorphism from `ker p` to covering-space automorphisms is given by left
translation. -/
def kernelLeftTranslationAutHom
    (p : H →ₜ* G) :
    p.ker →* Aut (Over.mk (TopCat.ofHom p.toContinuousMap)) where
  toFun := kernelLeftTranslationAut p
  map_one' := kernelLeftTranslationAut_one p
  map_mul' := kernelLeftTranslationAut_mul p

section ConnectedTotalSpace

variable [ConnectedSpace H]

/-- Helper for Problem 3.9.2: the image of `1` under a covering-space automorphism lies in the
kernel. -/
private theorem autInvFun_mem_kernel
    (p : H →ₜ* G) (α : Aut (Over.mk (TopCat.ofHom p.toContinuousMap))) :
    α.hom.left.hom (1 : H) ∈ p.ker := by
  -- The automorphism lies over `p`, so it preserves the basepoint value.
  simpa using covering_space_aut_comm p α (1 : H)

/-- Helper for Problem 3.9.2: evaluating a covering-space automorphism at `1` gives the candidate
kernel element inverse to left translation. -/
private def autInvFun
    (p : H →ₜ* G) :
    Aut (Over.mk (TopCat.ofHom p.toContinuousMap)) → p.ker :=
  fun α ↦ ⟨α.hom.left.hom (1 : H), autInvFun_mem_kernel p α⟩

/-- Helper for Problem 3.9.2: the evaluation map at `1` is a left inverse to left translation. -/
private theorem autInvFun_leftInverse
    (p : H →ₜ* G) :
    Function.LeftInverse (autInvFun p) (kernelLeftTranslationAutHom p) := by
  intro k
  -- Left translation by `k` sends `1` to `k`.
  ext
  change (k : H) * 1 = k
  simp

/-- Helper for Problem 3.9.2: on a connected total space, every covering-space automorphism is the
left translation by its value at `1`. -/
private theorem autInvFun_rightInverse
    (p : H →ₜ* G) (hp : IsCoveringMap (p : H → G)) :
    Function.RightInverse (autInvFun p) (kernelLeftTranslationAutHom p) := by
  letI : DiscreteTopology p.ker := kernel_discreteTopology_of_covering p hp
  intro α
  let f : H → H := α.hom.left.hom
  have hf : Continuous f := α.hom.left.hom.continuous
  -- The ratio `f y * y⁻¹` lands in the discrete kernel, so connectedness forces it to be constant.
  have hratio_mem : ∀ y : H, f y * y⁻¹ ∈ p.ker := by
    intro y
    show p (f y * y⁻¹) = 1
    have hy := covering_space_aut_comm p α y
    rw [map_mul, map_inv, hy]
    simp
  let ratio : H → p.ker := fun y ↦ ⟨f y * y⁻¹, hratio_mem y⟩
  have hratio : Continuous ratio := by
    exact Continuous.subtype_mk (hf.mul continuous_inv) hratio_mem
  have hconst : ∀ y : H, ratio y = ratio (1 : H) := by
    intro y
    exact TotallyDisconnectedSpace.eq_of_continuous ratio hratio y 1
  have hratio_val : ∀ y : H, f y * y⁻¹ = autInvFun p α := by
    intro y
    have hy := hconst y
    have hval : (ratio y : H) = ratio (1 : H) := congrArg (fun z : p.ker ↦ (z : H)) hy
    simpa [ratio, autInvFun, f] using hval
  apply Iso.ext
  apply CostructuredArrow.hom_ext
  ext x
  let xH : H := x
  -- Rewrite the automorphism value using the constant ratio.
  have happly :
      ((kernelLeftTranslationAutHom p (autInvFun p α)).hom.left.hom x : H) =
        (autInvFun p α : H) * xH := by
    change ((Homeomorph.mulLeft (autInvFun p α : H)) x : H) =
      (autInvFun p α : H) * xH
    rfl
  have htranslate :
      ((kernelLeftTranslationAutHom p (autInvFun p α)).hom.left.hom x : H) = f xH := by
    calc
      ((kernelLeftTranslationAutHom p (autInvFun p α)).hom.left.hom x : H)
          = (autInvFun p α : H) * xH := happly
      _ = (f xH * xH⁻¹) * xH := by rw [hratio_val xH]
      _ = f xH := by group
  simpa [f, xH] using htranslate

/-- The canonical homomorphism from `ker p` to covering automorphisms is bijective when the total
space `H` is connected. -/
-- Proof sketch: injectivity follows by evaluating a deck transformation at `1`. For
-- surjectivity, any covering automorphism sends `1` to some kernel element `k`, and uniqueness of
-- lifts on the connected total space `H` forces the automorphism to be left translation by `k`.
theorem kernelLeftTranslationAutHom_bijective
    (p : H →ₜ* G) (hp : IsCoveringMap (p : H → G)) :
    Function.Bijective (kernelLeftTranslationAutHom p) := by
  -- The explicit inverse is evaluation at `1`.
  refine ⟨(autInvFun_leftInverse p).injective, ?_⟩
  intro α
  exact ⟨autInvFun p α, autInvFun_rightInverse p hp α⟩

/-- Problem 3.9.2 (3): if the total group `H` is connected, left translation `h ↦ k * h`
identifies `ker p` with the automorphism group of the covering space `p`. -/
noncomputable def kernelMulEquivCoveringSpaceAut
    (p : H →ₜ* G) (hp : IsCoveringMap (p : H → G)) :
    p.ker ≃* Aut (Over.mk (TopCat.ofHom p.toContinuousMap)) :=
  MulEquiv.ofBijective
    (kernelLeftTranslationAutHom p)
    (kernelLeftTranslationAutHom_bijective p hp)

/-- The equivalence `kernelMulEquivCoveringSpaceAut` sends a kernel element to its left-translation
covering automorphism. -/
-- Proof sketch: unfold `kernelMulEquivCoveringSpaceAut`; `MulEquiv.ofBijective` keeps the same
-- underlying forward map as `kernelLeftTranslationAutHom`.
@[simp] theorem kernelMulEquivCoveringSpaceAut_apply
    (p : H →ₜ* G) (hp : IsCoveringMap (p : H → G)) (k : p.ker) :
    kernelMulEquivCoveringSpaceAut p hp k = kernelLeftTranslationAut p k := by
  -- `MulEquiv.ofBijective` preserves the original forward map.
  rfl

/-- Applying the inverse equivalence recovers the kernel element whose left translation realizes
a given covering automorphism. -/
-- Proof sketch: this is the inverse-direction analogue of
-- `kernelMulEquivCoveringSpaceAut_apply`, using the defining inverse property of the
-- multiplicative equivalence.
@[simp] theorem kernelMulEquivCoveringSpaceAut_symm_apply
    (p : H →ₜ* G) (hp : IsCoveringMap (p : H → G))
    (α : Aut (Over.mk (TopCat.ofHom p.toContinuousMap))) :
    kernelLeftTranslationAut p ((kernelMulEquivCoveringSpaceAut p hp).symm α) = α := by
  -- Apply the inverse property of the multiplicative equivalence.
  simpa using (kernelMulEquivCoveringSpaceAut p hp).apply_symm_apply α

/-- The equivalence `kernelMulEquivCoveringSpaceAut` is realized by the canonical homomorphism
`kernelLeftTranslationAutHom`. -/
-- Proof sketch: unfold `kernelMulEquivCoveringSpaceAut`; `MulEquiv.ofBijective` keeps the same
-- underlying monoid homomorphism.
@[simp] theorem kernelMulEquivCoveringSpaceAut_toMonoidHom
    (p : H →ₜ* G) (hp : IsCoveringMap (p : H → G)) :
    (kernelMulEquivCoveringSpaceAut p hp).toMonoidHom = kernelLeftTranslationAutHom p := by
  -- This is definitional for `MulEquiv.ofBijective`.
  rfl

end ConnectedTotalSpace
