/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.TransferInstance
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_17
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_14
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_16
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_19
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_9
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_9
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient Pointwise
open InnerProductSpace (toDualMap)

noncomputable section

universe u v

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [hrawTupleFiniteDimensional : FiniteDimensional ℝ ((i : ι) → Ei i)]

local instance : DecidableEq ι := Classical.decEq ι
attribute [-instance] Pi.seminormedAddCommGroup Pi.normedAddCommGroup Pi.normedSpace
private abbrev rawTupleFiniteDimensionalBase :
    FiniteDimensional ℝ ((i : ι) → Ei i) :=
  hrawTupleFiniteDimensional

/-- Helper for Theorem 11.1: the canonical continuous linear equivalence from raw tuples to the
Euclidean `PiLp` product owner. -/
private def rawToPiLp : ((i : ι) → Ei i) ≃L[ℝ] PiLp 2 Ei :=
  ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)

/-- Helper for Theorem 11.1: transport the ambient raw tuple norm to the Euclidean `PiLp`
product norm so the Chapter 3 stationary-point owner matches the source's Euclidean geometry. -/
instance rawTupleNormedAddCommGroup :
    NormedAddCommGroup ((i : ι) → Ei i) :=
  PiLp.normedAddCommGroupToPi (p := (2 : ENNReal)) Ei

/-- Helper for Theorem 11.1: the transported ambient scalar action is the one induced by the
canonical `PiLp` Euclidean product owner. -/
instance rawTupleNormedSpace :
    NormedSpace ℝ ((i : ι) → Ei i) := by
  exact PiLp.normedSpaceSeminormedAddCommGroupToPi (p := (2 : ENNReal)) (α := Ei)

/-- Helper for Theorem 11.1: the ambient raw tuple owner carries the Euclidean-product inner
product transported from the canonical `PiLp` model. -/
instance rawTupleInnerProductSpace :
    InnerProductSpace ℝ ((i : ι) → Ei i) := by
  refine
    { rawTupleNormedSpace (ι := ι) (Ei := Ei) with
      inner := fun x y ↦
        inner ℝ
          (((rawToPiLp (ι := ι) (Ei := Ei)) x : PiLp 2 Ei))
          (((rawToPiLp (ι := ι) (Ei := Ei)) y : PiLp 2 Ei))
      norm_sq_eq_re_inner := ?_
      conj_inner_symm := ?_
      add_left := ?_
      smul_left := ?_ }
  · intro x
    change ‖(((rawToPiLp (ι := ι) (Ei := Ei)) x : PiLp 2 Ei))‖ ^ 2 =
      RCLike.re
        (inner ℝ
          (((rawToPiLp (ι := ι) (Ei := Ei)) x : PiLp 2 Ei))
          (((rawToPiLp (ι := ι) (Ei := Ei)) x : PiLp 2 Ei)))
    simpa using
      (InnerProductSpace.norm_sq_eq_re_inner
        (𝕜 := ℝ)
        (E := PiLp 2 Ei)
        (((rawToPiLp (ι := ι) (Ei := Ei)) x : PiLp 2 Ei)))
  · intro x y
    simpa using
      (real_inner_comm
        (((rawToPiLp (ι := ι) (Ei := Ei)) x : PiLp 2 Ei))
        (((rawToPiLp (ι := ι) (Ei := Ei)) y : PiLp 2 Ei)))
  · intro x y z
    simpa using
      (inner_add_left
        (((rawToPiLp (ι := ι) (Ei := Ei)) x : PiLp 2 Ei))
        (((rawToPiLp (ι := ι) (Ei := Ei)) y : PiLp 2 Ei))
        (((rawToPiLp (ι := ι) (Ei := Ei)) z : PiLp 2 Ei)))
  · intro x y r
    simpa using
      (inner_smul_left
        (((rawToPiLp (ι := ι) (Ei := Ei)) x : PiLp 2 Ei))
        (((rawToPiLp (ι := ι) (Ei := Ei)) y : PiLp 2 Ei))
        r)

attribute [instance] rawTupleNormedAddCommGroup rawTupleNormedSpace rawTupleInnerProductSpace

/-- Helper for Theorem 11.1: the assumed finite-dimensional raw tuple owner is compatible with
the transported Euclidean-product norm and inner product. -/
instance rawTupleFiniteDimensional :
    @FiniteDimensional ℝ ((i : ι) → Ei i) Real.instDivisionRing
      rawTupleNormedAddCommGroup.toAddCommGroup
      rawTupleInnerProductSpace.toModule := by
  exact rawTupleFiniteDimensionalBase (ι := ι) (Ei := Ei)

/-- Helper for Theorem 11.1: the transported finite-dimensional raw tuple owner is complete. -/
instance rawTupleCompleteSpace :
    @CompleteSpace ((i : ι) → Ei i)
      rawTupleNormedAddCommGroup.toUniformSpace := by
  letI := rawTupleNormedAddCommGroup (ι := ι) (Ei := Ei)
  letI := rawTupleNormedSpace (ι := ι) (Ei := Ei)
  letI := rawTupleInnerProductSpace (ι := ι) (Ei := Ei)
  letI :
      @FiniteDimensional ℝ ((i : ι) → Ei i) Real.instDivisionRing
        rawTupleNormedAddCommGroup.toAddCommGroup
        rawTupleInnerProductSpace.toModule :=
    rawTupleFiniteDimensional (ι := ι) (Ei := Ei)
  exact FiniteDimensional.complete ℝ ((i : ι) → Ei i)

/-- Helper for Theorem 11.1: each block space inherits finite dimensionality from the ambient
product space. -/
instance blockFiniteDimensional (j : ι) : FiniteDimensional ℝ (Ei j) := by
  let projj : ((i : ι) → Ei i) →ₗ[ℝ] Ei j := LinearMap.proj j
  let hsurj : Function.Surjective projj := by
    intro y
    refine ⟨Pi.single j y, ?_⟩
    change Pi.single j y j = y
    simp
  exact FiniteDimensional.of_surjective projj hsurj

/-- Helper for Theorem 11.1: every block space is proper because it is finite-dimensional. -/
instance blockProperSpace (j : ι) : ProperSpace (Ei j) :=
  FiniteDimensional.proper ℝ (Ei j)

/-- Helper for Theorem 11.1: every block space is complete because it is finite-dimensional. -/
instance blockCompleteSpace (j : ι) : CompleteSpace (Ei j) :=
  FiniteDimensional.complete ℝ (Ei j)

/-- Helper for Theorem 11.1: the raw product-space interior of `effective_domain f` maps back to
the transported tuple-space interior used by the Chapter 3 stationary-point owner. -/
private lemma memInteriorEffectiveDomain_of_rawMemInterior
    {f : ((i : ι) → Ei i) → EReal} {x : (i : ι) → Ei i}
    (hx : x ∈ @interior ((i : ι) → Ei i) Pi.topologicalSpace (effective_domain f)) :
    x ∈ interior (effective_domain f) := by
  simpa using hx

section Main

variable {f : ((i : ι) → Ei i) → EReal}
variable {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ} {Lf : NNReal} {Li : (i : ι) → PosReal}

/-- Helper for Theorem 11.1: the translated one-block update differs from the base point by the
singleton block insertion of the translated coordinate. -/
private lemma blockCoordinateUpdate_sub_eq_single
    (x : (i : ι) → Ei i) (j : ι) (d : Ei j) :
    block_coordinate_update x j d - x = Pi.single j d := by
  -- Compare coordinates directly: the updated block contributes `d`, all others vanish.
  ext i
  by_cases hij : i = j
  · subst i
    simp [block_coordinate_update]
  · simp [block_coordinate_update, hij]

/-- Helper for Theorem 11.1: negating the Riesz functional is the same as taking the Riesz
functional of the negated vector. -/
private lemma negToDual_eq_toDualMap_neg {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (v : E) :
    (-InnerProductSpace.toDual ℝ E v : Module.Dual ℝ E) =
      InnerProductSpace.toDualMap ℝ E (-v) := by
  -- Compare the two dual vectors pointwise on an arbitrary test vector.
  ext y
  simp [InnerProductSpace.toDual_apply_eq_toDualMap_apply]

/-- Helper for Theorem 11.1: the raw Chapter 11 block residual vanishes exactly when the negative
block gradient lies in the Euclidean subdifferential of the corresponding block penalty. -/
private lemma rawBlockResidual_eq_zero_iff_negativeBlockGradient_memEuclideanSubdifferential
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (M : PosReal) (x : (i : ι) → Ei i) (i : ι) [ProperSpace (Ei i)] :
    G[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = 0 ↔
      -(block_gradient i x) ∈ euclideanSubdifferential (g i) (x i) := by
  have hM_pos : 0 < (1 / M : ℝ) := one_div_pos.mpr (PosReal.coe_pos M)
  have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt (PosReal.coe_pos M)
  have hscaled :=
    scaled_function_pcc_of_pos
      (g i)
      (hg_proper i)
      (hg_closed i)
      (hg_convex i)
      (1 / M)
  constructor
  · intro hG
    have hfixed : T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = x i := by
      -- Expand the residual and cancel the positive stepsize.
      rw [block_partial_gradient_mapping_def] at hG
      rcases smul_eq_zero.mp hG with hM | hsub
      · exact (hM_ne hM).elim
      · exact (sub_eq_zero.mp hsub).symm
    have hprox :
        prox[((((1 / M : PosReal) : EReal) • g i))]
          (x i - (1 / M : ℝ) • block_gradient i x) = {x i} := by
      -- The fixed-point form is exactly the singleton proximal characterization.
      calc
        prox[((((1 / M : PosReal) : EReal) • g i))]
            (x i - (1 / M : ℝ) • block_gradient i x) =
            {T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i} := by
              simpa using
                block_partial_prox_grad_point_eq_singleton
                  g
                  block_gradient
                  hg_proper
                  hg_closed
                  hg_convex
                  M
                  i
                  x
        _ = {x i} := by rw [hfixed]
    have hsub_scaled :
        (InnerProductSpace.toDualMap ℝ (Ei i)
          (-(1 / M : ℝ) • block_gradient i x) : Module.Dual ℝ (Ei i)) ∈
          subdifferential ((((1 / M : PosReal) : EReal) • g i)) (x i) := by
      have hstrong :
          InnerProductSpace.toDualMap ℝ (Ei i)
              ((x i - (1 / M : ℝ) • block_gradient i x) - x i) ∈
            strongDualSubdifferential ((((1 / M : PosReal) : EReal) • g i)) (x i) :=
        (prox_eq_singleton_iff_toDualMap_sub_mem_strongDualSubdifferential
          ((((1 / M : PosReal) : EReal) • g i))
          hscaled.1
          hscaled.2.2
          (x i - (1 / M : ℝ) • block_gradient i x)
          (x i)).mp hprox
      -- Rewrite the forward-point displacement as the scaled negative block gradient.
      rw [mem_strongDualSubdifferential] at hstrong
      simpa [sub_eq_add_neg, smul_neg, neg_smul, add_assoc, add_left_comm, add_comm] using hstrong
    have hsub :
        (InnerProductSpace.toDualMap ℝ (Ei i) (-(block_gradient i x)) :
            Module.Dual ℝ (Ei i)) ∈
          subdifferential (g i) (x i) := by
      -- Remove the positive scaling factor on the block penalty.
      have htransport :=
        (mem_subdifferential_pos_real_mul_iff
          (g i)
          (1 / M : ℝ)
          hM_pos
          (x i)
          (InnerProductSpace.toDualMap ℝ (Ei i)
            (-(1 / M : ℝ) • block_gradient i x))).mp hsub_scaled
      simpa [smul_smul, one_div, hM_ne, inv_mul_cancel₀, smul_neg, neg_smul] using htransport
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential]
    simpa [smul_smul, one_div, hM_ne, inv_mul_cancel₀, smul_neg, neg_smul] using hsub
  · intro hsub
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential] at hsub
    have hsub_scaled :
        (InnerProductSpace.toDualMap ℝ (Ei i)
          (-(1 / M : ℝ) • block_gradient i x) : Module.Dual ℝ (Ei i)) ∈
          subdifferential ((((1 / M : PosReal) : EReal) • g i)) (x i) := by
      -- Push the unscaled block subgradient forward to the scaled penalty.
      refine
        (mem_subdifferential_pos_real_mul_iff
          (g i)
          (1 / M : ℝ)
          hM_pos
          (x i)
          (InnerProductSpace.toDualMap ℝ (Ei i)
            (-(1 / M : ℝ) • block_gradient i x))).mpr ?_
      simpa [smul_smul, one_div, hM_ne, inv_mul_cancel₀, smul_neg, neg_smul] using hsub
    have hprox :
        prox[((((1 / M : PosReal) : EReal) • g i))]
          (x i - (1 / M : ℝ) • block_gradient i x) = {x i} := by
      -- Rebuild the singleton proximal description from the scaled subgradient condition.
      refine
        (prox_eq_singleton_iff_toDualMap_sub_mem_strongDualSubdifferential
          ((((1 / M : PosReal) : EReal) • g i))
          hscaled.1
          hscaled.2.2
          (x i - (1 / M : ℝ) • block_gradient i x)
          (x i)).mpr ?_
      rw [mem_strongDualSubdifferential]
      simpa [sub_eq_add_neg, smul_neg, neg_smul, add_assoc, add_left_comm, add_comm] using hsub_scaled
    have hfixed : T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = x i := by
      -- Equal singleton proximal sets have the same chosen point.
      apply Set.singleton_injective
      calc
        {T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i} =
            prox[((((1 / M : PosReal) : EReal) • g i))]
              (x i - (1 / M : ℝ) • block_gradient i x) := by
                symm
                simpa using
                  block_partial_prox_grad_point_eq_singleton
                    g
                    block_gradient
                    hg_proper
                    hg_closed
                    hg_convex
                    M
                    i
                    x
        _ = {x i} := hprox
    -- Substitute the fixed-point identity back into the residual definition.
    rw [block_partial_gradient_mapping_def, hfixed, sub_self, smul_zero]

/-- Helper for Theorem 11.1: the owner-level Chapter 11 block residual vanishes exactly when the
negative block gradient lies in the Euclidean subdifferential of the corresponding penalty. -/
lemma blockResidual_eq_zero_iff_negativeBlockGradient_memEuclideanSubdifferential
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ} {Li : (i : ι) → PosReal}
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (M : PosReal) (x : (i : ι) → Ei i) (i : ι) [ProperSpace (Ei i)] :
    G[M; hproblem] x i = 0 ↔
      -(block_gradient i x) ∈ euclideanSubdifferential (g i) (x i) := by
  exact
    rawBlockResidual_eq_zero_iff_negativeBlockGradient_memEuclideanSubdifferential
      (g := g)
      (block_gradient := block_gradient)
      hproblem.block_g_proper
      hproblem.block_g_closed
      hproblem.block_g_convex
      M
      x
      i

/-- Helper for Theorem 11.1: coordinatewise Euclidean subdifferential membership already implies
that the raw tuple lies in the effective domain of the block-separable penalty. This is the
feasibility half of the reverse direction, independent of the unresolved raw/`PiLp` stationarity
transport. -/
private lemma mem_effectiveDomain_separableSum_of_forall_memEuclideanSubdifferential
    (hcoord : ∀ i, -(block_gradient i x) ∈ euclideanSubdifferential (g i) (x i)) :
    x ∈ effective_domain (separableSum g) := by
  rw [mem_effective_domain, separableSum_apply]
  refine ereal_sum_lt_top Finset.univ (fun i ↦ g i (x i)) ?_
  intro i _
  have hi :
      x i ∈ effective_domain (g i) := by
    have hmem := hcoord i
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential, mem_subdifferential] at hmem
    exact hmem.1
  exact mem_effective_domain.mp hi

/-- Helper for Theorem 11.1: replacing one coordinate by another finite block value preserves the
effective domain of the block-separable penalty. -/
private lemma blockCoordinateUpdate_mem_effectiveDomain_separableSum
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    {x : (i : ι) → Ei i} (hx : x ∈ effective_domain (separableSum g))
    {i : ι} {yi : Ei i} (hyi : yi ∈ effective_domain (g i)) :
    block_coordinate_update x i (yi - x i) ∈ effective_domain (separableSum g) := by
  classical
  rw [mem_effective_domain, separableSum_apply]
  refine ereal_sum_lt_top Finset.univ (fun j ↦ g j ((block_coordinate_update x i (yi - x i)) j)) ?_
  intro j _
  by_cases hji : j = i
  · subst j
    have hsame : block_coordinate_update x i (yi - x i) i = yi := by
      -- The active block update installs the replacement value `yi`.
      rw [block_coordinate_update_apply_same]
      abel
    simpa [hsame] using mem_effective_domain.mp hyi
  · have hxj :
      x j ∈ effective_domain (g j) :=
        block_mem_effective_domain_of_mem_separableSum_effective_domain
          g
          hg_proper
          hx
          j
    -- All inactive blocks keep their original finite values.
    simpa [block_coordinate_update_apply_ne, hji] using mem_effective_domain.mp hxj

/-- Helper for Theorem 11.1: a finite sum of coerced real numbers is the coercion of the
corresponding real sum. -/
private lemma erealCoeFinsetSum {α : Type*} (s : Finset α) (φ : α → ℝ) :
    Finset.sum s (fun a ↦ (((φ a : ℝ)) : EReal)) =
      (((Finset.sum s φ : ℝ)) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha hs =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hs, EReal.coe_add]

/-- Helper for Theorem 11.1: at any finite point of the block-separable penalty, the aggregate
value is the coercion of the real sum of its blockwise values. -/
private lemma separableSum_eq_coe_toRealSum
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    {x : (i : ι) → Ei i}
    (hx : x ∈ effective_domain (separableSum g)) :
    separableSum g x = ((((∑ j, (g j (x j)).toReal : ℝ)) : ℝ) : EReal) := by
  have hxj : ∀ j, x j ∈ effective_domain (g j) := by
    intro j
    exact
      block_mem_effective_domain_of_mem_separableSum_effective_domain
        g
        hg_proper
        hx
        j
  rw [separableSum_apply]
  calc
    ∑ j, g j (x j) = ∑ j, ((((g j (x j)).toReal : ℝ)) : EReal) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      exact
        (EReal.coe_toReal
          (mem_effective_domain.mp (hxj j)).ne
          ((hg_proper j).ne_bot _)).symm
    _ = ((((∑ j, (g j (x j)).toReal : ℝ)) : ℝ) : EReal) := by
      simpa using erealCoeFinsetSum (s := Finset.univ) (φ := fun j ↦ (g j (x j)).toReal)

/-- Helper for Theorem 11.1: the raw tuple-space Riesz functional evaluates as the finite sum of
the blockwise inner products. -/
private lemma tupleToDualMap_apply_eq_sum
    (v w : (i : ι) → Ei i) :
    (InnerProductSpace.toDualMap ℝ ((i : ι) → Ei i) v) w =
      ∑ i, inner ℝ (v i) (w i) := by
  -- Rewrite the transported raw-tuple pairing through the canonical `PiLp` owner.
  rw [InnerProductSpace.toDualMap_apply_apply]
  change inner ℝ ((rawToPiLp (ι := ι) (Ei := Ei)) v) ((rawToPiLp (ι := ι) (Ei := Ei)) w) =
    ∑ i, inner ℝ (v i) (w i)
  simpa [rawToPiLp] using
    (PiLp.inner_apply
      ((rawToPiLp (ι := ι) (Ei := Ei)) v)
      ((rawToPiLp (ι := ι) (Ei := Ei)) w))

/-- Helper for Theorem 11.1: changing one coordinate updates the aggregate separable penalty by
exactly the corresponding blockwise `toReal` difference. -/
private lemma separableSum_toRealDiff_blockCoordinateUpdate
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    {x : (i : ι) → Ei i} (hx : x ∈ effective_domain (separableSum g))
    {i : ι} {yi : Ei i} (hyi : yi ∈ effective_domain (g i)) :
    (separableSum g (block_coordinate_update x i (yi - x i))).toReal -
        (separableSum g x).toReal =
      (g i yi).toReal - (g i (x i)).toReal := by
  classical
  let y := block_coordinate_update x i (yi - x i)
  have hy : y ∈ effective_domain (separableSum g) :=
    blockCoordinateUpdate_mem_effectiveDomain_separableSum
      (g := g)
      hg_proper
      hx
      hyi
  have hsum_x :
      (separableSum g x).toReal = ∑ j, (g j (x j)).toReal := by
    rw [separableSum_eq_coe_toRealSum (g := g) hg_proper hx, EReal.toReal_coe]
  have hsum_y :
      (separableSum g y).toReal = ∑ j, (g j (y j)).toReal := by
    rw [separableSum_eq_coe_toRealSum (g := g) hg_proper hy, EReal.toReal_coe]
  have hsum_x_split :
      ∑ j, (g j (x j)).toReal =
        (g i (x i)).toReal +
          Finset.sum (Finset.univ.erase i) (fun j ↦ (g j (x j)).toReal) := by
    symm
    exact Finset.add_sum_erase Finset.univ (fun j ↦ (g j (x j)).toReal) (Finset.mem_univ i)
  have hsum_y_split :
      ∑ j, (g j (y j)).toReal =
        (g i yi).toReal +
          Finset.sum (Finset.univ.erase i) (fun j ↦ (g j (x j)).toReal) := by
    calc
      ∑ j, (g j (y j)).toReal =
          (g i (y i)).toReal +
            Finset.sum (Finset.univ.erase i) (fun j ↦ (g j (y j)).toReal) := by
            symm
            exact Finset.add_sum_erase Finset.univ (fun j ↦ (g j (y j)).toReal) (Finset.mem_univ i)
      _ = (g i yi).toReal +
            Finset.sum (Finset.univ.erase i) (fun j ↦ (g j (x j)).toReal) := by
        congr 1
        · have hsame : y i = yi := by
            dsimp [y]
            rw [block_coordinate_update_apply_same]
            abel
          simpa [y, hsame]
        · refine Finset.sum_congr rfl ?_
          intro j hj
          have hji : j ≠ i := (Finset.mem_erase.mp hj).1
          simp [y, block_coordinate_update_apply_ne, hji]
  -- Cancel the untouched block sum from both sides of the aggregate real identity.
  rw [hsum_x, hsum_y, hsum_x_split, hsum_y_split]
  linarith

/-- Helper for Theorem 11.1: for two feasible points, the aggregate separable-sum real-value
difference is the sum of the coordinatewise real-value differences. -/
private lemma separableSum_toRealDiff_eq_sum_coordinateDiff
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    {x y : (i : ι) → Ei i}
    (hx : x ∈ effective_domain (separableSum g))
    (hy : y ∈ effective_domain (separableSum g)) :
    (separableSum g y).toReal - (separableSum g x).toReal =
      ∑ j, ((g j (y j)).toReal - (g j (x j)).toReal) := by
  -- Rewrite both aggregate values as finite sums of blockwise real values and subtract.
  rw [separableSum_eq_coe_toRealSum (g := g) hg_proper hy,
    separableSum_eq_coe_toRealSum (g := g) hg_proper hx, EReal.toReal_coe, EReal.toReal_coe]
  rw [Finset.sum_sub_distrib]

/-- Helper for Theorem 11.1: evaluating the ambient tuple-space Riesz functional on a singleton
block direction recovers the block Riesz pairing on that coordinate. -/
private lemma ambientToDual_apply_single_eq_blockToDual_apply
    (j : ι) (v : (i : ι) → Ei i) (d : Ei j) :
    (InnerProductSpace.toDualMap ℝ ((i : ι) → Ei i) v) (Pi.single j d : (i : ι) → Ei i) =
      (InnerProductSpace.toDualMap ℝ (Ei j) (v j)) d := by
  rw [tupleToDualMap_apply_eq_sum, InnerProductSpace.toDualMap_apply_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

/-- Helper for Theorem 11.1: differentiating the raw one-block update in the coordinate variable
recovers the owner-stable singleton insertion map. -/
private lemma rawBlockCoordinateUpdate_hasFDerivAt
    (x : (i : ι) → Ei i) (j : ι) :
    HasFDerivAt
      (fun y : Ei j ↦ block_coordinate_update x j (y - x j))
      (.pi (Pi.single j (.id ℝ (Ei j))))
      (x j) := by
  have hrewrite :
      (fun y : Ei j ↦ block_coordinate_update x j (y - x j)) = Function.update x j := by
    funext y
    ext i
    by_cases hij : i = j
    · subst i
      simp [block_coordinate_update, Function.update]
    · simp [block_coordinate_update, Function.update, hij]
  -- The translated block update is exactly the standard `Function.update` map in the active block.
  rw [hrewrite]
  simpa using hasFDerivAt_update x (i := j) (y := x j)

/-- Helper for Theorem 11.1: the owner-stable singleton insertion map applies to a block vector
exactly as the expected `Pi.single` insertion. -/
private lemma rawSingletonLinearMap_apply_eq_single
    (j : ι) (d : Ei j) :
    (ContinuousLinearMap.pi (Pi.single j (ContinuousLinearMap.id ℝ (Ei j)))) d =
      (Pi.single j d : (i : ι) → Ei i) := by
  -- Compare coordinates directly: the inserted block is `d` and every other block vanishes.
  ext i
  by_cases hij : i = j
  · subst i
    simp
  · simp [hij]

/-- Helper for Theorem 11.1: the owner-stable singleton insertion map is exactly the canonical
`ContinuousLinearMap.single`. -/
private lemma rawSingletonLinearMap_eq_single
    (j : ι) :
    ContinuousLinearMap.pi (Pi.single j (ContinuousLinearMap.id ℝ (Ei j))) =
      ContinuousLinearMap.single ℝ Ei j := by
  -- Compare both linear maps coordinatewise on an arbitrary block vector.
  ext d i
  by_cases hij : i = j
  · subst i
    simp
  · simp [hij]

/-- Helper for Theorem 11.1: differentiating the raw one-block update in the coordinate variable
recovers the canonical singleton insertion map. -/
private lemma rawBlockCoordinateUpdate_hasFDerivAt_single
    (x : (i : ι) → Ei i) (j : ι) :
    HasFDerivAt
      (fun y : Ei j ↦ block_coordinate_update x j (y - x j))
      (ContinuousLinearMap.single ℝ Ei j)
      (x j) := by
  -- Rewrite the owner-stable derivative into the canonical singleton insertion spelling once.
  simpa [rawSingletonLinearMap_eq_single (Ei := Ei) j] using
    rawBlockCoordinateUpdate_hasFDerivAt (Ei := Ei) x j

/-- Helper for Theorem 11.1: translating the one-block slice from displacement `0` to the actual
coordinate `x_j` preserves the prescribed block derivative. -/
private lemma translatedBlockCoordinateSlice_hasFDerivAt
    (hf_toReal_differentiableOn_interior_effective_domain :
      DifferentiableOn ℝ (fun y ↦ (f y).toReal) (interior (effective_domain f)))
    (hblock_partial_gradient_spec :
      ∀ i {x : (j : ι) → Ei j},
        x ∈ interior (effective_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    {xPoint : (i : ι) → Ei i}
    (hxPoint : xPoint ∈ interior (effective_domain f))
    (j : ι) :
    HasFDerivAt
      (fun y : Ei j ↦ (f (block_coordinate_update xPoint j (y - xPoint j))).toReal)
      (InnerProductSpace.toDualMap ℝ (Ei j) (block_gradient j xPoint))
      (xPoint j) := by
  -- Re-center the block slice from the displacement variable `0` to the actual coordinate `x_j`.
  have hsub :
      HasFDerivAt
        (fun y : Ei j ↦ y - xPoint j)
        (ContinuousLinearMap.id ℝ (Ei j))
        (xPoint j) := by
    simpa using (hasFDerivAt_sub_const (xPoint j) (x := xPoint j))
  have hblockAt :
      HasFDerivAt
        (block_coordinate_slice f xPoint j)
        (InnerProductSpace.toDualMap ℝ (Ei j) (block_gradient j xPoint))
        (xPoint j - xPoint j) := by
    simpa using hblock_partial_gradient_spec j hxPoint
  -- First translate the one-block slice from displacement `0` to the actual block coordinate.
  simpa [block_coordinate_slice_apply, Function.comp] using
    (HasFDerivAt.comp
      (f := fun y : Ei j ↦ y - xPoint j)
      (g := block_coordinate_slice f xPoint j)
      (x := xPoint j)
      hblockAt
      hsub)

/-- Helper for Theorem 11.1: composing the ambient tuple-space Riesz functional with the
singleton block insertion recovers the block Riesz functional on the chosen coordinate. -/
private lemma ambientToDual_comp_blockSingle_eq_blockToDual
    (j : ι) (v : (i : ι) → Ei i) :
    (InnerProductSpace.toDualMap ℝ ((i : ι) → Ei i) v).comp
        (ContinuousLinearMap.single ℝ Ei j) =
      InnerProductSpace.toDualMap ℝ (Ei j) (v j) := by
  ext d
  simpa [ContinuousLinearMap.comp_apply] using
    ambientToDual_apply_single_eq_blockToDual_apply (Ei := Ei) j v d

/-- Helper for Theorem 11.1: on `interior (effective_domain f)`, the `j`-th ambient gradient
coordinate of `x ↦ (f x).toReal` agrees with the Chapter 11 block gradient. -/
private lemma ambientGradientCoordinate_eq_blockGradient
    (hf_toReal_differentiableOn_interior_effective_domain :
      DifferentiableOn ℝ (fun y ↦ (f y).toReal) (interior (effective_domain f)))
    (hblock_partial_gradient_spec :
      ∀ i {x : (j : ι) → Ei j},
        x ∈ interior (effective_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    {xPoint : (i : ι) → Ei i}
    (hxPoint : xPoint ∈ interior (effective_domain f))
    (j : ι) :
    (∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) xPoint) j = block_gradient j xPoint := by
  have htranslated :
      HasFDerivAt
        (fun y : Ei j ↦ (f (block_coordinate_update xPoint j (y - xPoint j))).toReal)
        (InnerProductSpace.toDualMap ℝ (Ei j) (block_gradient j xPoint))
        (xPoint j) := by
    -- Re-center the one-block slice from displacement `0` to the actual coordinate `x_j`.
    simpa [block_coordinate_slice_apply] using
      (translatedBlockCoordinateSlice_hasFDerivAt
        (f := f)
        (block_gradient := block_gradient)
        hf_toReal_differentiableOn_interior_effective_domain
        hblock_partial_gradient_spec
        hxPoint
        j)
  have hdiffAt :
      DifferentiableAt ℝ (fun y : (i : ι) → Ei i ↦ (f y).toReal) xPoint := by
    exact
      (hf_toReal_differentiableOn_interior_effective_domain xPoint hxPoint).differentiableAt
        (isOpen_interior.mem_nhds hxPoint)
  have hambient :
      HasFDerivAt
        (fun y : (i : ι) → Ei i ↦ (f y).toReal)
        (InnerProductSpace.toDualMap ℝ ((i : ι) → Ei i)
          (∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) xPoint))
        xPoint := by
    -- Rewrite the ambient differentiability witness into the `HasFDerivAt` form used for
    -- restriction along the singleton block insertion.
    simpa using hdiffAt.hasGradientAt.hasFDerivAt
  have hcomp :
      HasFDerivAt
        (fun y : Ei j ↦ (f (block_coordinate_update xPoint j (y - xPoint j))).toReal)
        ((InnerProductSpace.toDualMap ℝ ((i : ι) → Ei i)
            (∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) xPoint)).comp
          (ContinuousLinearMap.single ℝ Ei j))
        (xPoint j) := by
    have hupdate :
        block_coordinate_update xPoint j (xPoint j - xPoint j) = xPoint := by
      ext i
      by_cases hij : i = j
      · subst i
        simp [block_coordinate_update]
      · simp [block_coordinate_update]
    have hambientAtUpdate :
        HasFDerivAt
          (fun y : (i : ι) → Ei i ↦ (f y).toReal)
          (InnerProductSpace.toDualMap ℝ ((i : ι) → Ei i)
            (∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) xPoint))
          (block_coordinate_update xPoint j (xPoint j - xPoint j)) := by
      exact hupdate.symm ▸ hambient
    -- Restrict the ambient derivative to the singleton block direction.
    simpa [Function.comp, hupdate] using
      hambientAtUpdate.comp (xPoint j)
        (rawBlockCoordinateUpdate_hasFDerivAt_single (Ei := Ei) xPoint j)
  have hdual :
      InnerProductSpace.toDualMap ℝ (Ei j)
          ((∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) xPoint) j) =
        InnerProductSpace.toDualMap ℝ (Ei j) (block_gradient j xPoint) := by
    calc
      InnerProductSpace.toDualMap ℝ (Ei j)
          ((∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) xPoint) j) =
          (InnerProductSpace.toDualMap ℝ ((i : ι) → Ei i)
              (∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) xPoint)).comp
            (ContinuousLinearMap.single ℝ Ei j) := by
              symm
              exact
                ambientToDual_comp_blockSingle_eq_blockToDual
                  (Ei := Ei)
                  j
                  (∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) xPoint)
      _ = InnerProductSpace.toDualMap ℝ (Ei j) (block_gradient j xPoint) := by
            exact hcomp.unique htranslated
  exact (InnerProductSpace.toDualMap ℝ (Ei j)).injective hdual

/-- Helper for Theorem 11.1: a raw interior point of `effective_domain f` becomes an interior
point of `finite_domain f` for the transported tuple owner when `f` is proper. -/
private lemma memInteriorFiniteDomain_of_rawMemInterior
    (hf_proper : IsProperExtendedRealFunction f)
    {x : (i : ι) → Ei i}
    (hx : x ∈ @interior ((i : ι) → Ei i) Pi.topologicalSpace (effective_domain f)) :
    x ∈ interior (finite_domain f) := by
  -- Properness identifies `finite_domain f` with `effective_domain f`, so the existing owner
  -- transport for `effective_domain` immediately yields the finite-domain interior statement.
  have hx' : x ∈ interior (effective_domain f) :=
    memInteriorEffectiveDomain_of_rawMemInterior (f := f) hx
  simpa [finite_domain_eq_effective_domain (f := f) (fun y ↦ hf_proper.ne_bot y)] using hx'

/-- Helper for Theorem 11.1: an aggregate subgradient inequality for the separable sum can be read
in `ℝ` at any feasible comparison point. -/
private lemma separableSumSubgradient_eval_le_toReal_sub
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    {x y : (i : ι) → Ei i}
    {ξ : Module.Dual ℝ ((i : ι) → Ei i)}
    (hξ : ξ ∈ subdifferential (separableSum g) x)
    (hy : y ∈ effective_domain (separableSum g)) :
    ξ (y - x) ≤ (separableSum g y).toReal - (separableSum g x).toReal := by
  let hsep_proper : IsProperExtendedRealFunction (separableSum g) := separableSum_proper g hg_proper
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hξ
  rcases hξ with ⟨hx, hineq⟩
  have hx_ne_bot : separableSum g x ≠ ⊥ := hsep_proper.ne_bot x
  have hy_ne_bot : separableSum g y ≠ ⊥ := hsep_proper.ne_bot y
  have hx_ne_top : separableSum g x ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hx)
  have hy_ne_top : separableSum g y ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hy)
  have hreal_add :
      (separableSum g x).toReal + ξ (y - x) ≤ (separableSum g y).toReal := by
    -- Rewrite the aggregate `EReal` support inequality into a finite real inequality.
    have hineq' := hineq y hy
    rw [ge_iff_le, (EReal.coe_toReal hy_ne_top hy_ne_bot).symm,
      (EReal.coe_toReal hx_ne_top hx_ne_bot).symm] at hineq'
    have hineq'' :
        (((separableSum g x).toReal : ℝ) : EReal) + ((ξ (y - x) : ℝ) : EReal) ≤
          (((separableSum g y).toReal : ℝ) : EReal) := by
      simpa [EReal.coe_add] using hineq'
    exact_mod_cast hineq''
  linarith

/-- Helper for Theorem 11.1: evaluating the stationary negative-gradient functional on a singleton
block direction gives the corresponding negative block-gradient pairing. -/
private lemma negGradientDual_apply_single_eq_negativeBlockPairing
    (hf_toReal_differentiableOn_interior_effective_domain :
      DifferentiableOn ℝ (fun y ↦ (f y).toReal) (interior (effective_domain f)))
    (hblock_partial_gradient_spec :
      ∀ i {x : (j : ι) → Ei j},
        x ∈ interior (effective_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    {xPoint : (i : ι) → Ei i}
    (hxPoint : xPoint ∈ interior (effective_domain f))
    (j : ι)
    (d : Ei j) :
    ((-InnerProductSpace.toDual ℝ ((i : ι) → Ei i)
        (∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) xPoint) :
        Module.Dual ℝ ((i : ι) → Ei i))) (Pi.single j d : (i : ι) → Ei i) =
      inner ℝ (-(block_gradient j xPoint)) d := by
  have hcoord :
      (∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) xPoint) j = block_gradient j xPoint :=
    ambientGradientCoordinate_eq_blockGradient
      (f := f)
      (block_gradient := block_gradient)
      hf_toReal_differentiableOn_interior_effective_domain
      hblock_partial_gradient_spec
      hxPoint
      j
  calc
    ((-InnerProductSpace.toDual ℝ ((i : ι) → Ei i)
        (∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) xPoint) :
        Module.Dual ℝ ((i : ι) → Ei i))) (Pi.single j d : (i : ι) → Ei i) =
        (InnerProductSpace.toDualMap ℝ ((i : ι) → Ei i)
          (-(∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) xPoint)) :
            Module.Dual ℝ ((i : ι) → Ei i)) (Pi.single j d : (i : ι) → Ei i) := by
          rw [negToDual_eq_toDualMap_neg]
    _ = (InnerProductSpace.toDualMap ℝ (Ei j)
          ((-(∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) xPoint)) j)) d := by
          exact ambientToDual_apply_single_eq_blockToDual_apply (Ei := Ei) j _ d
    _ = inner ℝ (-(block_gradient j xPoint)) d := by
          simp [InnerProductSpace.toDualMap_apply_apply, hcoord]

/-- Helper for Theorem 11.1: a real-valued support inequality for the aggregate separable sum
rewrites back to the corresponding Chapter 3 `EReal` subgradient inequality. -/
private lemma separableSumSupport_toERealInequality
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    {x y : (i : ι) → Ei i}
    (hx : x ∈ effective_domain (separableSum g))
    (hy : y ∈ effective_domain (separableSum g))
    {r : ℝ}
    (hreal : r ≤ (separableSum g y).toReal - (separableSum g x).toReal) :
    separableSum g y ≥ separableSum g x + ((r : ℝ) : EReal) := by
  let hsep_proper : IsProperExtendedRealFunction (separableSum g) := separableSum_proper g hg_proper
  have hx_ne_bot : separableSum g x ≠ ⊥ := hsep_proper.ne_bot x
  have hy_ne_bot : separableSum g y ≠ ⊥ := hsep_proper.ne_bot y
  have hx_ne_top : separableSum g x ≠ ⊤ := (mem_effective_domain.mp hx).ne
  have hy_ne_top : separableSum g y ≠ ⊤ := (mem_effective_domain.mp hy).ne
  have hreal_add :
      (separableSum g x).toReal + r ≤ (separableSum g y).toReal := by
    linarith
  have hcoe :
      ((((separableSum g x).toReal + r : ℝ)) : EReal) ≤
        (((separableSum g y).toReal : ℝ) : EReal) := by
    exact_mod_cast hreal_add
  rw [ge_iff_le, (EReal.coe_toReal hy_ne_top hy_ne_bot).symm,
    (EReal.coe_toReal hx_ne_top hx_ne_bot).symm]
  simpa [EReal.coe_add, add_comm, add_left_comm, add_assoc] using hcoe

/-- Helper for Theorem 11.1: Euclidean block-subgradient membership gives the real-valued support
inequality against every feasible comparison point. -/
private lemma blockSubgradient_eval_le_toReal_sub
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    {x : (i : ι) → Ei i} {i : ι}
    (hmem : -(block_gradient i x) ∈ euclideanSubdifferential (g i) (x i))
    {yi : Ei i} (hyi : yi ∈ effective_domain (g i)) :
    inner ℝ (-(block_gradient i x)) (yi - x i) ≤
      (g i yi).toReal - (g i (x i)).toReal := by
  rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential, mem_subdifferential,
    is_subgradient_at_iff_forall_mem_effective_domain] at hmem
  rcases hmem with ⟨hxi, hineq⟩
  have hxi_ne_bot : g i (x i) ≠ ⊥ := (hg_proper i).ne_bot (x i)
  have hyi_ne_bot : g i yi ≠ ⊥ := (hg_proper i).ne_bot yi
  have hxi_ne_top : g i (x i) ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hxi)
  have hyi_ne_top : g i yi ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hyi)
  have hreal_add :
      (g i (x i)).toReal +
          InnerProductSpace.toDualMap ℝ (Ei i) (-(block_gradient i x)) (yi - x i) ≤
        (g i yi).toReal := by
    -- Rewrite the owner inequality into `ℝ` after identifying both function values as finite.
    have hineq' := hineq yi hyi
    rw [ge_iff_le, (EReal.coe_toReal hyi_ne_top hyi_ne_bot).symm,
      (EReal.coe_toReal hxi_ne_top hxi_ne_bot).symm] at hineq'
    have hineq'' :
        (((g i (x i)).toReal : ℝ) : EReal) +
            (((InnerProductSpace.toDualMap ℝ (Ei i) (-(block_gradient i x)) (yi - x i)) : ℝ) :
              EReal) ≤
          (((g i yi).toReal : ℝ) : EReal) := by
      simpa [EReal.coe_add] using hineq'
    exact_mod_cast hineq''
  have hpair :
      (g i (x i)).toReal + inner ℝ (-(block_gradient i x)) (yi - x i) ≤
        (g i yi).toReal := by
    simpa [InnerProductSpace.toDualMap_apply_apply] using hreal_add
  linarith

/-- Helper for Theorem 11.1: a real-valued block support inequality rewrites back to the Chapter 3
`EReal` subgradient inequality on the active block. -/
private lemma blockSupport_toERealInequality
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    {x : (i : ι) → Ei i} {i : ι} {yi : Ei i}
    (hxi : x i ∈ effective_domain (g i))
    (hyi : yi ∈ effective_domain (g i))
    (hreal :
      inner ℝ (-(block_gradient i x)) (yi - x i) ≤
        (g i yi).toReal - (g i (x i)).toReal) :
    g i yi ≥
      g i (x i) +
        (((InnerProductSpace.toDualMap ℝ (Ei i) (-(block_gradient i x)) (yi - x i) : ℝ)) : EReal) := by
  have hxi_ne_bot : g i (x i) ≠ ⊥ := (hg_proper i).ne_bot (x i)
  have hyi_ne_bot : g i yi ≠ ⊥ := (hg_proper i).ne_bot yi
  have hxi_ne_top : g i (x i) ≠ ⊤ := (mem_effective_domain.mp hxi).ne
  have hyi_ne_top : g i yi ≠ ⊤ := (mem_effective_domain.mp hyi).ne
  have hreal_add :
      (g i (x i)).toReal +
          InnerProductSpace.toDualMap ℝ (Ei i) (-(block_gradient i x)) (yi - x i) ≤
        (g i yi).toReal := by
    simpa [InnerProductSpace.toDualMap_apply_apply] using hreal
  have hcoe :
      ((((g i (x i)).toReal +
          InnerProductSpace.toDualMap ℝ (Ei i) (-(block_gradient i x)) (yi - x i) : ℝ)) :
          EReal) ≤
        (((g i yi).toReal : ℝ) : EReal) := by
    exact_mod_cast hreal_add
  rw [ge_iff_le, (EReal.coe_toReal hyi_ne_top hyi_ne_bot).symm,
    (EReal.coe_toReal hxi_ne_top hxi_ne_bot).symm]
  simpa [EReal.coe_add] using hcoe

/-- Helper for Theorem 11.1: aggregate stationary subdifferential membership forces the
coordinatewise Euclidean support inequality on each block. -/
private lemma blockSubgradient_eval_le_toReal_sub_of_negGradientDual_memSubdifferentialSeparableSum
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hf_toReal_differentiableOn_interior_effective_domain :
      DifferentiableOn ℝ (fun y ↦ (f y).toReal) (interior (effective_domain f)))
    (hblock_partial_gradient_spec :
      ∀ i {x : (j : ι) → Ei j},
        x ∈ interior (effective_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    {x : (i : ι) → Ei i}
    (hx : x ∈ interior (effective_domain f))
    (hnegSub :
      ((-InnerProductSpace.toDual ℝ ((i : ι) → Ei i)
          (∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) x) :
          Module.Dual ℝ ((i : ι) → Ei i))) ∈
        subdifferential (separableSum g) x)
    {i : ι} {yi : Ei i} (hyi : yi ∈ effective_domain (g i)) :
    inner ℝ (-(block_gradient i x)) (yi - x i) ≤
      (g i yi).toReal - (g i (x i)).toReal := by
  let negDeriv : Module.Dual ℝ ((i : ι) → Ei i) :=
    ((-InnerProductSpace.toDual ℝ ((i : ι) → Ei i)
        (∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) x) :
      Module.Dual ℝ ((i : ι) → Ei i)))
  have hnegSub' := hnegSub
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hnegSub'
  rcases hnegSub' with ⟨hxSep, _⟩
  let y : (i : ι) → Ei i := block_coordinate_update x i (yi - x i)
  have hy :
      y ∈ effective_domain (separableSum g) :=
    blockCoordinateUpdate_mem_effectiveDomain_separableSum
      (g := g)
      hg_proper
      hxSep
      hyi
  have haggReal :
      negDeriv (y - x) ≤ (separableSum g y).toReal - (separableSum g x).toReal :=
    separableSumSubgradient_eval_le_toReal_sub
      (g := g)
      hg_proper
      hnegSub
      hy
  calc
    inner ℝ (-(block_gradient i x)) (yi - x i) =
        negDeriv (Pi.single i (yi - x i)) := by
          symm
          simpa [negDeriv] using
            negGradientDual_apply_single_eq_negativeBlockPairing
              (f := f)
              (block_gradient := block_gradient)
              hf_toReal_differentiableOn_interior_effective_domain
              hblock_partial_gradient_spec
              hx
              i
              (yi - x i)
    _ = negDeriv (y - x) := by
          simp [y, blockCoordinateUpdate_sub_eq_single]
    _ ≤ (separableSum g y).toReal - (separableSum g x).toReal := haggReal
    _ = (g i yi).toReal - (g i (x i)).toReal := by
          simpa [y] using
            (separableSum_toRealDiff_blockCoordinateUpdate
              (g := g)
              hg_proper
              hxSep
              hyi)

/-- Helper for Theorem 11.1: aggregate stationary subdifferential membership yields the
coordinatewise Euclidean block-subgradient conditions. -/
private lemma coordinatewiseEuclideanSubdifferential_of_negGradientDual_memSubdifferentialSeparableSum
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hf_toReal_differentiableOn_interior_effective_domain :
      DifferentiableOn ℝ (fun y ↦ (f y).toReal) (interior (effective_domain f)))
    (hblock_partial_gradient_spec :
      ∀ i {x : (j : ι) → Ei j},
        x ∈ interior (effective_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    {x : (i : ι) → Ei i}
    (hx : x ∈ interior (effective_domain f)) :
    ((-InnerProductSpace.toDual ℝ ((i : ι) → Ei i)
        (∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) x) :
        Module.Dual ℝ ((i : ι) → Ei i))) ∈ subdifferential (separableSum g) x →
      ∀ i, -(block_gradient i x) ∈ euclideanSubdifferential (g i) (x i) := by
  intro hnegSub i
  have hnegSub' := hnegSub
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hnegSub'
  rcases hnegSub' with ⟨hxSep, _⟩
  have hxi :
      x i ∈ effective_domain (g i) :=
    block_mem_effective_domain_of_mem_separableSum_effective_domain g hg_proper hxSep i
  rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential, mem_subdifferential,
    is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨hxi, ?_⟩
  intro yi hyi
  have hblockReal :
      inner ℝ (-(block_gradient i x)) (yi - x i) ≤
        (g i yi).toReal - (g i (x i)).toReal :=
    blockSubgradient_eval_le_toReal_sub_of_negGradientDual_memSubdifferentialSeparableSum
      (f := f)
      (g := g)
      (block_gradient := block_gradient)
      hg_proper
      hf_toReal_differentiableOn_interior_effective_domain
      hblock_partial_gradient_spec
      hx
      hnegSub
      hyi
  -- Convert the real block support inequality back to the Chapter 3 owner form.
  exact
    blockSupport_toERealInequality
      (g := g)
      (block_gradient := block_gradient)
      hg_proper
      hxi
      hyi
      hblockReal

/-- Helper for Theorem 11.1: the stationary negative-gradient functional evaluates on a tuple
displacement as the sum of the blockwise negative-gradient pairings. -/
private lemma negGradientDual_apply_displacement_eq_sumBlockPairings_of_forall_coordinatewise
    (hf_toReal_differentiableOn_interior_effective_domain :
      DifferentiableOn ℝ (fun y ↦ (f y).toReal) (interior (effective_domain f)))
    (hblock_partial_gradient_spec :
      ∀ i {x : (j : ι) → Ei j},
        x ∈ interior (effective_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    {x : (i : ι) → Ei i}
    (hx : x ∈ interior (effective_domain f))
    {y : (i : ι) → Ei i} :
    ((-InnerProductSpace.toDual ℝ ((i : ι) → Ei i)
        (∇ (fun z : (i : ι) → Ei i ↦ (f z).toReal) x) :
        Module.Dual ℝ ((i : ι) → Ei i))) (y - x) =
      ∑ j, inner ℝ (-(block_gradient j x)) ((y - x) j) := by
  let negDeriv : Module.Dual ℝ ((i : ι) → Ei i) :=
    ((-InnerProductSpace.toDual ℝ ((i : ι) → Ei i)
        (∇ (fun z : (i : ι) → Ei i ↦ (f z).toReal) x) :
      Module.Dual ℝ ((i : ι) → Ei i)))
  have hcoord :
      ∀ j, (∇ (fun z : (i : ι) → Ei i ↦ (f z).toReal) x) j = block_gradient j x := by
    intro j
    exact
      ambientGradientCoordinate_eq_blockGradient
        (f := f)
        (block_gradient := block_gradient)
        hf_toReal_differentiableOn_interior_effective_domain
        hblock_partial_gradient_spec
        hx
        j
  calc
    negDeriv (y - x) =
        (InnerProductSpace.toDualMap ℝ ((i : ι) → Ei i)
            (-(∇ (fun z : (i : ι) → Ei i ↦ (f z).toReal) x)) :
            Module.Dual ℝ ((i : ι) → Ei i)) (y - x) := by
          change ((-InnerProductSpace.toDual ℝ ((i : ι) → Ei i)
              (∇ (fun z : (i : ι) → Ei i ↦ (f z).toReal) x) :
              Module.Dual ℝ ((i : ι) → Ei i))) (y - x) = _
          rw [negToDual_eq_toDualMap_neg]
    _ = ∑ j, inner ℝ ((-(∇ (fun z : (i : ι) → Ei i ↦ (f z).toReal) x)) j) ((y - x) j) := by
          simpa using
            (tupleToDualMap_apply_eq_sum
              (Ei := Ei)
              (v := -(∇ (fun z : (i : ι) → Ei i ↦ (f z).toReal) x))
              (w := y - x))
    _ = ∑ j, inner ℝ (-(block_gradient j x)) ((y - x) j) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          simp [hcoord j]

/-- Helper for Theorem 11.1: coordinatewise Euclidean block-subgradient conditions imply the
aggregate stationary support inequality on the separable sum. -/
private lemma negGradientDual_eval_le_separableSum_toRealDiff_of_forall_coordinatewise
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hf_toReal_differentiableOn_interior_effective_domain :
      DifferentiableOn ℝ (fun y ↦ (f y).toReal) (interior (effective_domain f)))
    (hblock_partial_gradient_spec :
      ∀ i {x : (j : ι) → Ei j},
        x ∈ interior (effective_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    {x : (i : ι) → Ei i}
    (hx : x ∈ interior (effective_domain f))
    (hcoord : ∀ i, -(block_gradient i x) ∈ euclideanSubdifferential (g i) (x i))
    {y : (i : ι) → Ei i}
    (hy : y ∈ effective_domain (separableSum g)) :
    ((-InnerProductSpace.toDual ℝ ((i : ι) → Ei i)
        (∇ (fun z : (i : ι) → Ei i ↦ (f z).toReal) x) :
        Module.Dual ℝ ((i : ι) → Ei i))) (y - x) ≤
      (separableSum g y).toReal - (separableSum g x).toReal := by
  let negDeriv : Module.Dual ℝ ((i : ι) → Ei i) :=
    ((-InnerProductSpace.toDual ℝ ((i : ι) → Ei i)
        (∇ (fun z : (i : ι) → Ei i ↦ (f z).toReal) x) :
      Module.Dual ℝ ((i : ι) → Ei i)))
  have hxSep :
      x ∈ effective_domain (separableSum g) :=
    mem_effectiveDomain_separableSum_of_forall_memEuclideanSubdifferential
      (g := g)
      (block_gradient := block_gradient)
      (x := x)
      hcoord
  have hcoordReal :
      ∀ j, inner ℝ (-(block_gradient j x)) (y j - x j) ≤
        (g j (y j)).toReal - (g j (x j)).toReal := by
    intro j
    have hyj :
        y j ∈ effective_domain (g j) :=
      block_mem_effective_domain_of_mem_separableSum_effective_domain g hg_proper hy j
    exact
      blockSubgradient_eval_le_toReal_sub
        (g := g)
        (block_gradient := block_gradient)
        hg_proper
        (hcoord j)
        hyj
  calc
    negDeriv (y - x) = ∑ j, inner ℝ (-(block_gradient j x)) ((y - x) j) := by
          exact
            negGradientDual_apply_displacement_eq_sumBlockPairings_of_forall_coordinatewise
              (f := f)
              (block_gradient := block_gradient)
              hf_toReal_differentiableOn_interior_effective_domain
              hblock_partial_gradient_spec
              hx
    _ ≤ ∑ j, ((g j (y j)).toReal - (g j (x j)).toReal) := by
          refine Finset.sum_le_sum ?_
          intro j _
          exact hcoordReal j
    _ = (separableSum g y).toReal - (separableSum g x).toReal := by
          symm
          exact separableSum_toRealDiff_eq_sum_coordinateDiff (g := g) hg_proper hxSep hy

/-- Helper for Theorem 11.1: coordinatewise Euclidean block-subgradient conditions imply the
aggregate stationary subdifferential condition. -/
private lemma negGradientDual_memSubdifferentialSeparableSum_of_forall_coordinatewise
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hf_toReal_differentiableOn_interior_effective_domain :
      DifferentiableOn ℝ (fun y ↦ (f y).toReal) (interior (effective_domain f)))
    (hblock_partial_gradient_spec :
      ∀ i {x : (j : ι) → Ei j},
        x ∈ interior (effective_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    {x : (i : ι) → Ei i}
    (hx : x ∈ interior (effective_domain f))
    (hcoord : ∀ i, -(block_gradient i x) ∈ euclideanSubdifferential (g i) (x i)) :
    ((-InnerProductSpace.toDual ℝ ((i : ι) → Ei i)
        (∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) x) :
        Module.Dual ℝ ((i : ι) → Ei i))) ∈
      subdifferential (separableSum g) x := by
  let negDeriv : Module.Dual ℝ ((i : ι) → Ei i) :=
    ((-InnerProductSpace.toDual ℝ ((i : ι) → Ei i)
        (∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) x) :
      Module.Dual ℝ ((i : ι) → Ei i)))
  have hxSep :
      x ∈ effective_domain (separableSum g) :=
    mem_effectiveDomain_separableSum_of_forall_memEuclideanSubdifferential
      (g := g)
      (block_gradient := block_gradient)
      (x := x)
      hcoord
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨hxSep, ?_⟩
  intro y hy
  have hreal :
      negDeriv (y - x) ≤ (separableSum g y).toReal - (separableSum g x).toReal :=
    negGradientDual_eval_le_separableSum_toRealDiff_of_forall_coordinatewise
      (f := f)
      (g := g)
      (block_gradient := block_gradient)
      hg_proper
      hf_toReal_differentiableOn_interior_effective_domain
      hblock_partial_gradient_spec
      hx
      hcoord
      hy
  -- Convert the real aggregate support inequality back to the Chapter 3 owner inequality.
  exact
    separableSumSupport_toERealInequality
      (g := g)
      hg_proper
      hxSep
      hy
      hreal

/-- Helper for Theorem 11.1: package the transported finite-dimensional tuple instance in the
form expected by the stationary-point owner. Assuming the source hypotheses that each block
penalty `g_i` is proper,
closed, and convex, that `f` is proper and closed with convex effective domain, that
`effective_domain (separableSum g)` lies in `interior (effective_domain f)`, and that the chosen
block map `block_gradient i x` is the gradient of the `i`-th block slice `d ↦ f(x + 𝒰[i] d)` on
that interior, a point `x` is stationary for `f + separableSum g` if and only if every block
satisfies the coordinatewise subdifferential condition `-(block_gradient i x) ∈
euclideanSubdifferential (g i) (x i)`. -/
private abbrev rawTupleFiniteDimensionalMain :
    FiniteDimensional ℝ ((i : ι) → Ei i) :=
  rawTupleFiniteDimensionalBase (ι := ι) (Ei := Ei)

/-- Helper for Theorem 11.1: raw stationarity implies the coordinatewise Euclidean
subdifferential conditions. -/
private lemma coordinatewiseEuclideanSubdifferential_of_isStationaryPoint
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain (separableSum g) ⊆ interior (effective_domain f))
    (hf_toReal_differentiableOn_interior_effective_domain :
      DifferentiableOn ℝ (fun y ↦ (f y).toReal) (interior (effective_domain f)))
    (hblock_partial_gradient_spec :
      ∀ i {x : (j : ι) → Ei j},
        x ∈ interior (effective_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    (x : (i : ι) → Ei i) :
    is_stationary_point f (separableSum g) x →
      ∀ i, -(block_gradient i x) ∈ euclideanSubdifferential (g i) (x i) := by
  intro hstationary
  rw [is_stationary_point_iff] at hstationary
  rcases hstationary with ⟨_, hnegSub⟩
  have hnegSub' := hnegSub
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hnegSub'
  rcases hnegSub' with ⟨hxSep, _⟩
  have hx : x ∈ interior (effective_domain f) :=
    hg_effective_domain_subset_interior_f_effective_domain hxSep
  exact
    coordinatewiseEuclideanSubdifferential_of_negGradientDual_memSubdifferentialSeparableSum
      (f := f)
      (g := g)
      (block_gradient := block_gradient)
      hg_proper
      hf_toReal_differentiableOn_interior_effective_domain
      hblock_partial_gradient_spec
      hx
      hnegSub

/-- Helper for Theorem 11.1: the coordinatewise Euclidean subdifferential conditions imply raw
stationarity. -/
private lemma isStationaryPoint_of_coordinatewiseEuclideanSubdifferential
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain (separableSum g) ⊆ interior (effective_domain f))
    (hf_toReal_differentiableOn_interior_effective_domain :
      DifferentiableOn ℝ (fun y ↦ (f y).toReal) (interior (effective_domain f)))
    (hblock_partial_gradient_spec :
      ∀ i {x : (j : ι) → Ei j},
        x ∈ interior (effective_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    (x : (i : ι) → Ei i) :
    (∀ i, -(block_gradient i x) ∈ euclideanSubdifferential (g i) (x i)) →
      is_stationary_point f (separableSum g) x := by
  intro hcoord
  have hxSep :
      x ∈ effective_domain (separableSum g) :=
    mem_effectiveDomain_separableSum_of_forall_memEuclideanSubdifferential
      (g := g)
      (block_gradient := block_gradient)
      (x := x)
      hcoord
  have hx : x ∈ interior (effective_domain f) :=
    hg_effective_domain_subset_interior_f_effective_domain hxSep
  have hdiff :
      is_differentiable_at f x := by
    refine ⟨?_, ?_⟩
    · simpa [finite_domain_eq_effective_domain (f := f) (fun y ↦ hf_proper.ne_bot y)] using hx
    · exact
        (hf_toReal_differentiableOn_interior_effective_domain x hx).differentiableAt
          (isOpen_interior.mem_nhds hx)
  have hnegSub :
      (-InnerProductSpace.toDual ℝ ((i : ι) → Ei i)
          (∇ (fun y : (i : ι) → Ei i ↦ (f y).toReal) x) :
          Module.Dual ℝ ((i : ι) → Ei i)) ∈
        subdifferential (separableSum g) x :=
    negGradientDual_memSubdifferentialSeparableSum_of_forall_coordinatewise
      (f := f)
      (g := g)
      (block_gradient := block_gradient)
      hg_proper
      hf_toReal_differentiableOn_interior_effective_domain
      hblock_partial_gradient_spec
      hx
      hcoord
  rw [is_stationary_point_iff]
  exact ⟨hdiff, hnegSub⟩

/-- Theorem 11.1 (1): assuming the source hypotheses that each block penalty `g_i` is proper,
closed, and convex, that `f` is proper and closed with convex effective domain, that
`effective_domain (separableSum g)` lies in `interior (effective_domain f)`, and that the chosen
block map `block_gradient i x` is the gradient of the `i`-th block slice `d ↦ f(x + 𝒰[i] d)` on
that interior, a point `x` is stationary for `f + separableSum g` if and only if every block
satisfies the coordinatewise subdifferential condition `-(block_gradient i x) ∈
euclideanSubdifferential (g i) (x i)`. -/
theorem is_stationary_point_iff_coordinatewise_negative_block_gradient_mem_euclideanSubdifferential
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (hf_closed : LowerSemicontinuous f)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain (separableSum g) ⊆ interior (effective_domain f))
    (hf_toReal_differentiableOn_interior_effective_domain :
      DifferentiableOn ℝ (fun y ↦ (f y).toReal) (interior (effective_domain f)))
    (hblock_partial_gradient_spec :
      ∀ i {x : (j : ι) → Ei j},
        x ∈ interior (effective_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    (x : (i : ι) → Ei i) :
    @is_stationary_point ((i : ι) → Ei i)
      (rawTupleNormedAddCommGroup (ι := ι) (Ei := Ei))
      (rawTupleInnerProductSpace (ι := ι) (Ei := Ei))
      (rawTupleFiniteDimensionalMain (ι := ι) (Ei := Ei))
      f
      (separableSum g)
      x ↔
      ∀ i, -(block_gradient i x) ∈ euclideanSubdifferential (g i) (x i) := by
  constructor
  · exact
      coordinatewiseEuclideanSubdifferential_of_isStationaryPoint
        (f := f)
        (g := g)
        (block_gradient := block_gradient)
        hg_proper
        hg_effective_domain_subset_interior_f_effective_domain
        hf_toReal_differentiableOn_interior_effective_domain
        hblock_partial_gradient_spec
        x
  · exact
      isStationaryPoint_of_coordinatewiseEuclideanSubdifferential
        (f := f)
        (g := g)
        (block_gradient := block_gradient)
        hf_proper
        hg_proper
        hg_effective_domain_subset_interior_f_effective_domain
        hf_toReal_differentiableOn_interior_effective_domain
        hblock_partial_gradient_spec
        x

/-- Helper for Theorem 11.1: under the same source hypotheses as part (1), stationarity forces
every positive-stepsize block residual to vanish. For any positive block
stepsizes `M_i > 0` and any point `x`, stationarity of `f + separableSum g` is equivalent to the
vanishing of the raw Chapter 11 block residuals `G[M i; g, block_gradient, hg_proper, hg_closed,
hg_convex] x i` for every block `i`. -/
private lemma blockPartialGradientMapping_eq_zero_of_isStationaryPoint
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (hf_closed : LowerSemicontinuous f)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain (separableSum g) ⊆ interior (effective_domain f))
    (hf_toReal_differentiableOn_interior_effective_domain :
      DifferentiableOn ℝ (fun y ↦ (f y).toReal) (interior (effective_domain f)))
    (hblock_partial_gradient_spec :
      ∀ i {x : (j : ι) → Ei j},
        x ∈ interior (effective_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    (M : (i : ι) → PosReal) (x : (i : ι) → Ei i) :
    is_stationary_point f (separableSum g) x →
      ∀ i, G[M i; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = 0 := by
  intro hstationary i
  have hcoord :
      ∀ j, -(block_gradient j x) ∈ euclideanSubdifferential (g j) (x j) :=
    (is_stationary_point_iff_coordinatewise_negative_block_gradient_mem_euclideanSubdifferential
      (f := f)
      (g := g)
      (block_gradient := block_gradient)
      hf_proper
      hg_proper
      hg_closed
      hg_convex
      hf_closed
      hf_effective_domain_convex
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_differentiableOn_interior_effective_domain
      hblock_partial_gradient_spec
      x).1 hstationary
  exact
    (rawBlockResidual_eq_zero_iff_negativeBlockGradient_memEuclideanSubdifferential
      (g := g)
      (block_gradient := block_gradient)
      hg_proper
      hg_closed
      hg_convex
      (M i)
      x
      i).2
      (hcoord i)

/-- Helper for Theorem 11.1: vanishing of all block residuals implies stationarity. -/
private lemma isStationaryPoint_of_blockPartialGradientMapping_eq_zero
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (hf_closed : LowerSemicontinuous f)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain (separableSum g) ⊆ interior (effective_domain f))
    (hf_toReal_differentiableOn_interior_effective_domain :
      DifferentiableOn ℝ (fun y ↦ (f y).toReal) (interior (effective_domain f)))
    (hblock_partial_gradient_spec :
      ∀ i {x : (j : ι) → Ei j},
        x ∈ interior (effective_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    (M : (i : ι) → PosReal) (x : (i : ι) → Ei i) :
    (∀ i, G[M i; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = 0) →
      is_stationary_point f (separableSum g) x := by
  intro hzero
  refine
    (is_stationary_point_iff_coordinatewise_negative_block_gradient_mem_euclideanSubdifferential
      (f := f)
      (g := g)
      (block_gradient := block_gradient)
      hf_proper
      hg_proper
      hg_closed
      hg_convex
      hf_closed
      hf_effective_domain_convex
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_differentiableOn_interior_effective_domain
      hblock_partial_gradient_spec
      x).2 ?_
  intro i
  exact
    (rawBlockResidual_eq_zero_iff_negativeBlockGradient_memEuclideanSubdifferential
      (g := g)
      (block_gradient := block_gradient)
      hg_proper
      hg_closed
      hg_convex
      (M i)
      x
      i).1
      (hzero i)

/-- Part (2) of Theorem 11.1: under the same source hypotheses as part (1), for any positive block
stepsizes `M_i > 0` and any point `x`, stationarity of `f + separableSum g` is equivalent to the
vanishing of the raw Chapter 11 block residuals `G[M i; g, block_gradient, hg_proper, hg_closed,
hg_convex] x i` for every block `i`. -/
theorem is_stationary_point_iff_block_partial_gradient_mapping_eq_zero
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (hf_closed : LowerSemicontinuous f)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain (separableSum g) ⊆ interior (effective_domain f))
    (hf_toReal_differentiableOn_interior_effective_domain :
      DifferentiableOn ℝ (fun y ↦ (f y).toReal) (interior (effective_domain f)))
    (hblock_partial_gradient_spec :
      ∀ i {x : (j : ι) → Ei j},
        x ∈ interior (effective_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    (M : (i : ι) → PosReal) (x : (i : ι) → Ei i) :
    @is_stationary_point ((i : ι) → Ei i)
      (rawTupleNormedAddCommGroup (ι := ι) (Ei := Ei))
      (rawTupleInnerProductSpace (ι := ι) (Ei := Ei))
      (rawTupleFiniteDimensionalMain (ι := ι) (Ei := Ei))
      f
      (separableSum g)
      x ↔
      ∀ i, G[M i; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = 0 := by
  constructor
  · exact
      blockPartialGradientMapping_eq_zero_of_isStationaryPoint
        (f := f)
        (g := g)
        (block_gradient := block_gradient)
        hf_proper
        hg_proper
        hg_closed
        hg_convex
        hf_closed
        hf_effective_domain_convex
        hg_effective_domain_subset_interior_f_effective_domain
        hf_toReal_differentiableOn_interior_effective_domain
        hblock_partial_gradient_spec
        M
        x
  · exact
      isStationaryPoint_of_blockPartialGradientMapping_eq_zero
        (f := f)
        (g := g)
        (block_gradient := block_gradient)
        hf_proper
        hg_proper
        hg_closed
        hg_convex
        hf_closed
        hf_effective_domain_convex
        hg_effective_domain_subset_interior_f_effective_domain
        hf_toReal_differentiableOn_interior_effective_domain
        hblock_partial_gradient_spec
        M
        x

end Main

end
