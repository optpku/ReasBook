/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_5
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Theorem_11_2

noncomputable section

universe u v

open scoped Gradient

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)]
variable [∀ i, InnerProductSpace ℝ (Ei i)]

variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : ι) → PosReal}

/- Lemma 11.1 is `source-facing`: it compares the aggregate Chapter 10 proximal-gradient owners
for the block-separable regularizer with the Chapter 11 one-block operators. The aggregate side
should therefore use the canonical finite-product owner `PiLp 2 Ei` together with
`PiLp.separableSum`, while the Chapter 11 block maps remain the `bridge/view` layer on raw block
tuples through `hproblem.toIsBlockProximalGradientProblem`. The primitive data are the block
assumptions `hproblem`; properness, lower semicontinuity, and convexity of the aggregate
regularizer on `PiLp 2 Ei` are derived locally rather than exposed as public theorem arguments. -/

namespace BlockProximalGradientAssumptions

variable [hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li]

local instance : DecidableEq ι := Classical.decEq ι

local notation "hcore" => hproblem.toIsBlockProximalGradientProblem
local notation "toPiLp" =>
  ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)

/-- Helper for Lemma 11.1: composing the ambient `PiLp` dual functional with the canonical
singleton block insertion recovers the block dual functional on the chosen coordinate. -/
lemma ambient_toDual_comp_single_eq_block_toDual
    (j : ι) (v : PiLp 2 Ei) :
    (InnerProductSpace.toDualMap ℝ (PiLp 2 Ei) v).comp
        (((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.single ℝ Ei j)) =
      InnerProductSpace.toDualMap ℝ (Ei j) (v j) := by
  classical
  -- Compare both dual maps after evaluating them on an arbitrary block vector.
  apply ContinuousLinearMap.ext
  intro d
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [InnerProductSpace.toDualMap_apply_apply, InnerProductSpace.toDualMap_apply_apply]
  -- Transport the singleton direction to the canonical `PiLp` owner and collapse the finite sum.
  change inner ℝ v (toPiLp (Pi.single j d)) = inner ℝ (v j) d
  rw [PiLp.coe_symm_continuousLinearEquiv, PiLp.toLp_single, PiLp.inner_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

/-- Helper for Lemma 11.1: the transported affine one-block update on `PiLp 2 Ei` has derivative
given by the canonical singleton insertion map on the active block. -/
lemma piLp_block_update_hasFDerivAt
    (x : ((j : ι) → Ei j))
    (i : ι) :
    HasFDerivAt
      (fun y : Ei i ↦ WithLp.toLp 2 (block_coordinate_update x i (y - x i)))
      ((((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm.toContinuousLinearMap)).comp
        (ContinuousLinearMap.single ℝ Ei i))
      (x i) := by
  have hsingle :
      HasFDerivAt
        (fun y : Ei i ↦ Pi.single i y)
        (ContinuousLinearMap.single ℝ Ei i)
        (x i - x i) := by
    simpa using (ContinuousLinearMap.single ℝ Ei i).hasFDerivAt
  have hsub :
      HasFDerivAt
        (fun y : Ei i ↦ y - x i)
        (ContinuousLinearMap.id ℝ (Ei i))
        (x i) := by
    simpa using (hasFDerivAt_sub_const (x i) (x := x i))
  have hupdate :
      HasFDerivAt
        (fun y : Ei i ↦ block_coordinate_update x i (y - x i))
        (ContinuousLinearMap.single ℝ Ei i)
        (x i) := by
    -- Differentiate the affine coordinate translation before reinserting it in the product.
    simpa [block_coordinate_update] using
      (HasFDerivAt.comp
        (f := fun y : Ei i ↦ y - x i)
        (g := fun z : Ei i ↦ Pi.single i z)
        (x := x i)
        hsingle
        hsub).const_add x
  -- Compose the raw affine update with the canonical `WithLp.toLp` transport once.
  simpa using
    (PiLp.hasFDerivAt_toLp (p := (2 : ENNReal)) (𝕜 := ℝ)
      (E := Ei) (f := block_coordinate_update x i (x i - x i))).comp (x i) hupdate

/-- Helper for Lemma 11.1: restricting the ambient `PiLp` Fréchet derivative of
`z ↦ (f z).toReal` to the singleton `i`-th block direction recovers the Chapter 11 block dual
functional. -/
lemma ambient_fderiv_comp_single_eq_block_toDual
    (hprob : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    [∀ i, CompleteSpace (Ei i)] [∀ i, ProperSpace (Ei i)]
    (x : ((j : ι) → Ei j))
    (hx : x ∈ interior (effective_domain f))
    (i : ι) :
    (fderiv ℝ (fun z : PiLp 2 Ei ↦ (f z).toReal) (WithLp.toLp 2 x)).comp
        ((((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm.toContinuousLinearMap)).comp
          (ContinuousLinearMap.single ℝ Ei i)) =
      InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x) := by
  let ambientFun : PiLp 2 Ei → ℝ := fun z ↦ (f z).toReal
  let singlePi : Ei i →L[ℝ] PiLp 2 Ei :=
    (((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm.toContinuousLinearMap)).comp
      (ContinuousLinearMap.single ℝ Ei i)
  have hblock :
      HasGradientAt (block_coordinate_slice f x i) (block_gradient i x) 0 :=
    hprob.toIsBlockProximalGradientProblem.block_partial_gradient_hasGradientAt i hx
  have htranslated :
      HasFDerivAt
        (fun y : Ei i ↦ ambientFun (WithLp.toLp 2 (block_coordinate_update x i (y - x i))))
        (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x))
        (x i) := by
    -- The Chapter 11 translated one-block slice is exactly the ambient `PiLp` function along the
    -- singleton block-update curve.
    simpa [ambientFun, block_coordinate_slice_apply] using
      (translated_block_coordinate_slice_hasGradientAt
        (i := i)
        (x := x)
        hblock).hasFDerivAt
  have hrawDiffAt :
      DifferentiableAt ℝ (fun y : ((j : ι) → Ei j) ↦ (f y).toReal) x := by
    have hdiffOn := hprob.f_toReal_differentiableOn_interior_effective_domain
    exact (hdiffOn x hx).differentiableAt (isOpen_interior.mem_nhds hx)
  have hambientDiffAt :
      DifferentiableAt ℝ ambientFun (WithLp.toLp 2 x) := by
    -- Transport differentiability from raw tuples to the canonical `PiLp` owner.
    have hcomp :
        DifferentiableAt ℝ (ambientFun ∘ toPiLp) x := by
      simpa [ambientFun, Function.comp] using hrawDiffAt
    exact ((ContinuousLinearEquiv.comp_right_differentiableAt_iff
      (iso := (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm)
      (f := ambientFun) (x := x))).1 hcomp
  have hambient :
      HasFDerivAt ambientFun (fderiv ℝ ambientFun (WithLp.toLp 2 x)) (WithLp.toLp 2 x) :=
    hambientDiffAt.hasFDerivAt
  have hambientAt :
      HasFDerivAt
        ambientFun
        (fderiv ℝ ambientFun (WithLp.toLp 2 x))
        (WithLp.toLp 2 (block_coordinate_update x i (x i - x i))) := by
    simpa [block_coordinate_update] using hambient
  have hcomp :
      HasFDerivAt
        (fun y : Ei i ↦ ambientFun (WithLp.toLp 2 (block_coordinate_update x i (y - x i))))
        ((fderiv ℝ ambientFun (WithLp.toLp 2 x)).comp singlePi)
        (x i) := by
    -- Restrict the ambient derivative to the singleton block direction.
    simpa [ambientFun, Function.comp] using
      hambientAt.comp (x i) (piLp_block_update_hasFDerivAt x i)
  exact hcomp.unique htranslated

/-- Helper for Lemma 11.1: on `interior (effective_domain f)`, the `i`-th coordinate of the
ambient `PiLp` gradient of `z ↦ (f z).toReal` agrees with the Chapter 11 block gradient. -/
lemma ambient_gradient_coordinate_eq_block_gradient
    (hprob : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    [∀ i, CompleteSpace (Ei i)] [∀ i, ProperSpace (Ei i)]
    (x : ((i : ι) → Ei i))
    (hx : x ∈ interior (effective_domain f))
    (i : ι) :
    (∇ (fun z : PiLp 2 Ei ↦ (f z).toReal) (WithLp.toLp 2 x)) i =
      block_gradient i x := by
  let ambientFun : PiLp 2 Ei → ℝ := fun z ↦ (f z).toReal
  let singlePi : Ei i →L[ℝ] PiLp 2 Ei :=
    (((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm.toContinuousLinearMap)).comp
      (ContinuousLinearMap.single ℝ Ei i)
  have hrawDiffAt :
      DifferentiableAt ℝ (fun y : ((j : ι) → Ei j) ↦ (f y).toReal) x := by
    have hdiffOn := hprob.f_toReal_differentiableOn_interior_effective_domain
    exact (hdiffOn x hx).differentiableAt (isOpen_interior.mem_nhds hx)
  have hambientDiffAt :
      DifferentiableAt ℝ ambientFun (WithLp.toLp 2 x) := by
    -- The ambient `PiLp` model is just the raw tuple model viewed through `toPiLp`.
    have hcomp :
        DifferentiableAt ℝ (ambientFun ∘ toPiLp) x := by
      simpa [ambientFun, Function.comp] using hrawDiffAt
    exact ((ContinuousLinearEquiv.comp_right_differentiableAt_iff
      (iso := (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm)
      (f := ambientFun) (x := x))).1 hcomp
  have hambientGrad :
      HasGradientAt ambientFun (∇ ambientFun (WithLp.toLp 2 x)) (WithLp.toLp 2 x) :=
    hambientDiffAt.hasGradientAt
  have hfderiv :
      fderiv ℝ ambientFun (WithLp.toLp 2 x) =
        InnerProductSpace.toDualMap ℝ (PiLp 2 Ei) (∇ ambientFun (WithLp.toLp 2 x)) := by
    simpa using hambientGrad.hasFDerivAt.fderiv
  have hdual :
      InnerProductSpace.toDualMap ℝ (Ei i) ((∇ ambientFun (WithLp.toLp 2 x)) i) =
        InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x) := by
    -- Compare the two block dual functionals through the restricted ambient derivative.
    calc
      InnerProductSpace.toDualMap ℝ (Ei i) ((∇ ambientFun (WithLp.toLp 2 x)) i) =
          (InnerProductSpace.toDualMap ℝ (PiLp 2 Ei)
            (∇ ambientFun (WithLp.toLp 2 x))).comp singlePi := by
            symm
            simpa [singlePi] using
              ambient_toDual_comp_single_eq_block_toDual i
                (∇ ambientFun (WithLp.toLp 2 x))
      _ = (fderiv ℝ ambientFun (WithLp.toLp 2 x)).comp singlePi := by
            rw [hfderiv]
      _ = InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x) := by
            exact ambient_fderiv_comp_single_eq_block_toDual hprob x hx i
  exact (InnerProductSpace.toDualMap ℝ (Ei i)).injective hdual

/-- Helper for Lemma 11.1: on the canonical `PiLp 2 Ei` aggregate owner, the ambient gradient of
`z ↦ (f z).toReal` at the transported point `WithLp.toLp 2 x` is the `PiLp` block vector with
coordinates `block_gradient i x`. -/
theorem ambientHasGradientAt_blockGradient
    (hprob : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    [∀ i, CompleteSpace (Ei i)] [∀ i, ProperSpace (Ei i)]
    (x : ((i : ι) → Ei i))
    (hx : x ∈ interior (effective_domain f)) :
    HasGradientAt
      (fun z : PiLp 2 Ei ↦ (f z).toReal)
      (WithLp.toLp 2 (fun i ↦ block_gradient i x))
      (WithLp.toLp 2 x) := by
  let ambientFun : PiLp 2 Ei → ℝ := fun z ↦ (f z).toReal
  have hrawDiffAt :
      DifferentiableAt ℝ (fun y : ((j : ι) → Ei j) ↦ (f y).toReal) x := by
    have hdiffOn := hprob.f_toReal_differentiableOn_interior_effective_domain
    exact (hdiffOn x hx).differentiableAt (isOpen_interior.mem_nhds hx)
  have hambientDiffAt :
      DifferentiableAt ℝ ambientFun (WithLp.toLp 2 x) := by
    -- Transport differentiability of `f.toReal` to the canonical `PiLp` ambient model.
    have hcomp :
        DifferentiableAt ℝ (ambientFun ∘ toPiLp) x := by
      simpa [ambientFun, Function.comp] using hrawDiffAt
    exact ((ContinuousLinearEquiv.comp_right_differentiableAt_iff
      (iso := (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm)
      (f := ambientFun) (x := x))).1 hcomp
  have hambientGrad :
      HasGradientAt ambientFun (∇ ambientFun (WithLp.toLp 2 x)) (WithLp.toLp 2 x) :=
    hambientDiffAt.hasGradientAt
  have hgrad_eq :
      ∇ ambientFun (WithLp.toLp 2 x) = WithLp.toLp 2 (fun i ↦ block_gradient i x) := by
    -- Identify the ambient gradient coordinatewise with the block gradients.
    ext i
    exact ambient_gradient_coordinate_eq_block_gradient hprob x hx i
  -- Replace the abstract ambient gradient by the explicit block-gradient tuple.
  simpa [ambientFun, hgrad_eq] using hambientGrad

/-- Helper for Lemma 11.1: scaling the aggregate `PiLp` separable sum by a scalar is the same as
scaling each coordinate penalty before summing. -/
lemma scaled_piLp_separableSum_eq_coordinatewise
    (μ : PosReal) :
    ((((μ : EReal) • PiLp.separableSum g) : PiLp 2 Ei → EReal)) =
      PiLp.separableSum (fun j ↦ ((μ : EReal) • g j)) := by
  funext z
  -- Evaluate both sides pointwise and push the scalar through the finite coordinate sum.
  rw [Pi.smul_apply, PiLp.separableSum_apply, PiLp.separableSum_apply]
  simp_rw [Pi.smul_apply, smul_eq_mul]
  -- The finite coordinate sum distributes over multiplication by the positive scalar `(μ : EReal)`.
  have hμ_nonneg : (0 : EReal) ≤ (μ : EReal) := by
    exact_mod_cast (show (0 : ℝ) ≤ (μ : ℝ) by exact le_of_lt μ.2)
  have hμ_ne_top : (μ : EReal) ≠ ⊤ := by simp
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha hs =>
      simp [Finset.sum_insert, ha]
      rw [EReal.left_distrib_of_nonneg_of_ne_top hμ_nonneg hμ_ne_top, hs]

/-- Applying the aggregate Chapter 10 prox-gradient operator on the canonical `PiLp 2 Ei` owner
and reading the `i`-th coordinate recovers the Chapter 11 one-block prox point `T_L^i(x)`. The
aggregate regularizer hypotheses are supplied locally by `hproblem`. -/
theorem prox_grad_operator_eq_block_partial_prox_grad_point_apply
    [∀ i, ProperSpace (Ei i)] [ProperSpace (PiLp 2 Ei)]
    (L : PosReal)
    (x : ((i : ι) → Ei i))
    (hx : x ∈ interior (effective_domain f))
    (i : ι) :
    hproblem.aggregate_prox_grad_operator L (WithLp.toLp 2 x) i =
      T[L; hcore] x i := by
  let μ : PosReal := 1 / L
  let μE : EReal := (μ : EReal)
  let z : PiLp 2 Ei :=
    WithLp.toLp 2 x - (1 / L : ℝ) • WithLp.toLp 2 (fun j ↦ block_gradient j x)
  letI : IsProperExtendedRealFunction (PiLp.separableSum g) := hproblem.piLp_separableSum_proper
  letI : Fact (LowerSemicontinuous (PiLp.separableSum g)) := hproblem.piLp_separableSum_closed
  letI : Fact (is_convex_function (PiLp.separableSum g)) := hproblem.piLp_separableSum_convex
  have hscaled :
      ∀ j, IsProperExtendedRealFunction (μE • g j) := by
    intro j
    exact
      (scaled_function_proper_closed_convex_of_pos
        (g j)
        (hproblem.block_g_proper j)
        (hproblem.block_g_closed j)
        (hproblem.block_g_convex j)
        (1 / L)).1
  have hambientGrad :
      ∇ (fun z : PiLp 2 Ei ↦ (f z).toReal) (WithLp.toLp 2 x) =
        WithLp.toLp 2 (fun j ↦ block_gradient j x) :=
    (ambientHasGradientAt_blockGradient hproblem x hx).gradient
  have hsingleton :
      prox[(μE • PiLp.separableSum g)] z =
        {hproblem.aggregate_prox_grad_operator L (WithLp.toLp 2 x)} := by
    -- Route correction: first identify the aggregate Chapter 10 forward point, then use the
    -- singleton characterization of the prox-gradient operator once.
    simpa [μ, μE, z, BlockProximalGradientAssumptions.aggregate_prox_grad_operator,
      proximal_gradient_step, interior_effective_domain_point_of_real, hambientGrad] using
      (prox_grad_operator_eq_singleton
        ((fun z : PiLp 2 Ei ↦ (f z).toReal).toEReal)
        (PiLp.separableSum g)
        L
        (interior_effective_domain_point_of_real
          (fun z : PiLp 2 Ei ↦ (f z).toReal)
          (WithLp.toLp 2 x)))
  have hmemAggregate :
      hproblem.aggregate_prox_grad_operator L (WithLp.toLp 2 x) ∈ prox[(μE • PiLp.separableSum g)] z := by
    rw [hsingleton]
    simp
  have hmemCoordinatewise :
      ∀ j,
        hproblem.aggregate_prox_grad_operator L (WithLp.toLp 2 x) j ∈
          prox[μE • g j] (x j - (1 / L : ℝ) • block_gradient j x) := by
    -- Split the aggregate proximal membership into the coordinatewise Chapter 6 conditions.
    have hmemRewritten :
        hproblem.aggregate_prox_grad_operator L (WithLp.toLp 2 x) ∈
          prox[PiLp.separableSum (fun j ↦ μE • g j)] z := by
      simpa [μE, scaled_piLp_separableSum_eq_coordinatewise (g := g) μ] using hmemAggregate
    have hcoords :=
      (mem_prox_separableSum_iff (f := fun j ↦ μE • g j) hscaled
        (x := z)
        (y := hproblem.aggregate_prox_grad_operator L (WithLp.toLp 2 x))).1
        hmemRewritten
    intro j
    simpa [z, μ] using hcoords j
  have hi_singleton :
      prox[μE • g i] (x i - (1 / L : ℝ) • block_gradient i x) =
        {T[L; hcore] x i} := by
    simpa [μ, μE] using IsBlockProximalGradientProblem.prox_point_eq_singleton hcore L i x
  have hi_mem := hmemCoordinatewise i
  rw [hi_singleton] at hi_mem
  simpa using hi_mem

/-- Applying the aggregate Chapter 10 gradient mapping on the canonical `PiLp 2 Ei` owner and
reading the `i`-th coordinate recovers the Chapter 11 block residual `G_L^i(x)`. -/
theorem gradient_mapping_eq_block_partial_gradient_mapping_apply
    [∀ i, ProperSpace (Ei i)] [ProperSpace (PiLp 2 Ei)]
    (L : PosReal)
    (x : ((i : ι) → Ei i))
    (hx : x ∈ interior (effective_domain f))
    (i : ι) :
    hproblem.aggregate_gradient_mapping L (WithLp.toLp 2 x) i =
      G[L; hcore] x i := by
  -- Expand both gradient mappings as the stepsize-scaled residual of the current point and prox
  -- point, then substitute the coordinatewise prox-point bridge.
  calc
    hproblem.aggregate_gradient_mapping L (WithLp.toLp 2 x) i =
        ((L : ℝ) •
          ((WithLp.toLp 2 x) -
            hproblem.aggregate_prox_grad_operator L (WithLp.toLp 2 x))) i := by
          rfl
    _ = (L : ℝ) • (x i - hproblem.aggregate_prox_grad_operator L (WithLp.toLp 2 x) i) := by
          simp
    _ = (L : ℝ) • (x i - T[L; hcore] x i) := by
          rw [prox_grad_operator_eq_block_partial_prox_grad_point_apply
            L
            x
            hx
            i]
    _ = G[L; hcore] x i := by
          rw [IsBlockProximalGradientProblem.gradient_mapping_def hcore]

/-- Lemma 11.1 (1): on the canonical `PiLp 2 Ei` aggregate owner, the full Chapter 10
prox-gradient update for `PiLp.separableSum g` is the `PiLp` block vector whose coordinates are
the Chapter 11 one-block prox points `T_L^i(x)`. -/
theorem prox_grad_operator_eq_block_partial_prox_grad_point_tuple
    [∀ i, ProperSpace (Ei i)] [ProperSpace (PiLp 2 Ei)]
    (L : PosReal)
    (x : ((i : ι) → Ei i))
    (hx : x ∈ interior (effective_domain f)) :
    hproblem.aggregate_prox_grad_operator L (WithLp.toLp 2 x) =
      WithLp.toLp 2 (fun i ↦ T[L; hcore] x i) := by
  -- The tuple identity is exactly the coordinatewise prox-point bridge on every block.
  ext i
  simpa using prox_grad_operator_eq_block_partial_prox_grad_point_apply
    L
    x
    hx
    i

/-- Lemma 11.1 (2): on the canonical `PiLp 2 Ei` aggregate owner, the full Chapter 10 gradient
mapping for `PiLp.separableSum g` is the `PiLp` block vector whose coordinates are the Chapter 11
block residuals `G_L^i(x)`. -/
theorem gradient_mapping_eq_block_partial_gradient_mapping_tuple
    [∀ i, ProperSpace (Ei i)] [ProperSpace (PiLp 2 Ei)]
    (L : PosReal)
    (x : ((i : ι) → Ei i))
    (hx : x ∈ interior (effective_domain f)) :
    hproblem.aggregate_gradient_mapping L (WithLp.toLp 2 x) =
      WithLp.toLp 2 (fun i ↦ G[L; hcore] x i) := by
  -- The tuple identity is exactly the coordinatewise residual bridge on every block.
  ext i
  simpa using gradient_mapping_eq_block_partial_gradient_mapping_apply
    L
    x
    hx
    i

end BlockProximalGradientAssumptions

end
