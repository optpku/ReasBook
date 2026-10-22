/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_17
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_35
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Theorem_11_1
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Theorem_11_2
import FirstOrderMethodsOptimization_Beck_2017.Chap14.AlternatingMinimizationCompositeModel
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Definition_14_2
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Proposition_14_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped BigOperators Gradient

section

/- `Lemma 14.2` is a `bridge/view` item. The source-facing coordinatewise minimum owner is
`is_coordinatewise_minimum`, the canonical Chapter 14 regularity owner is
`IsAlternatingMinimizationCompositeModel`, and the downstream Chapter 3 owner is
`is_stationary_point`. The theorem should therefore expose the model assumptions through the
existing owner class instead of restating its fields as a second public hypothesis bundle.

This file must use the canonical raw-tuple Euclidean owner imported from Chapter 11, not an
arbitrary ambient inner product on `((i : Fin p) → Ei i)`, because the source proof identifies the
one-block gradient `∇ \\tilde f_i (x_i^*)` with the canonical block gradient `∇_i f (x^*)`. -/

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [hrawTupleFiniteDimensional : FiniteDimensional ℝ ((i : Fin p) → Ei i)]

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}

local notation "F" => composite_model_objective f (separableSum g)
local notation "toPiLp" =>
  ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)

attribute [-instance] Pi.seminormedAddCommGroup Pi.normedAddCommGroup Pi.normedSpace

local instance lemma14_2_rawTupleNormedAddCommGroup :
    NormedAddCommGroup ((i : Fin p) → Ei i) :=
  rawTupleNormedAddCommGroup (ι := Fin p) (Ei := Ei)

local instance lemma14_2_rawTupleNormedSpace : NormedSpace ℝ ((i : Fin p) → Ei i) :=
  rawTupleNormedSpace (ι := Fin p) (Ei := Ei)

local instance lemma14_2_rawTupleInnerProductSpace :
    InnerProductSpace ℝ ((i : Fin p) → Ei i) :=
  rawTupleInnerProductSpace (ι := Fin p) (Ei := Ei)

local instance lemma14_2_rawTupleFiniteDimensional :
    FiniteDimensional ℝ ((i : Fin p) → Ei i) :=
  rawTupleFiniteDimensional (ι := Fin p) (Ei := Ei)

local instance lemma14_2_blockFiniteDimensional (i : Fin p) : FiniteDimensional ℝ (Ei i) :=
  blockFiniteDimensional (ι := Fin p) (Ei := Ei) i

local instance lemma14_2_blockCompleteSpace (i : Fin p) : CompleteSpace (Ei i) :=
  blockCompleteSpace (ι := Fin p) (Ei := Ei) i

/-- Helper for Lemma 14.2: the singleton block insertion is additive in the ambient product
owner. -/
private lemma ambientBlockSingle_map_add
    (i : Fin p) (x y : Ei i) :
    (Pi.single i (x + y) : (j : Fin p) → Ei j) =
      Pi.single i x + Pi.single i y := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [Pi.single_eq_of_ne hji]

/-- Helper for Lemma 14.2: the singleton block insertion respects scalar multiplication in the
ambient product owner. -/
private lemma ambientBlockSingle_map_smul
    (i : Fin p) (c : ℝ) (x : Ei i) :
    (Pi.single i (c • x) : (j : Fin p) → Ei j) =
      c • Pi.single i x := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [Pi.single_eq_of_ne hji]

/-- Helper for Lemma 14.2: singleton insertion is continuous for the ambient product norm. -/
private lemma ambientBlockSingle_continuous
    (i : Fin p) :
    Continuous (Pi.single i : Ei i → ((j : Fin p) → Ei j)) := by
  let L : Ei i →ₗ[ℝ] ((j : Fin p) → Ei j) :=
    { toFun := Pi.single i
      map_add' := ambientBlockSingle_map_add i
      map_smul' := ambientBlockSingle_map_smul i }
  exact L.continuous_of_finiteDimensional

/-- Helper for Lemma 14.2: a coordinate-wise minimum of `f + separableSum g` already lies in the
effective domain of the block-separable penalty. -/
private lemma memEffectiveDomainSeparableSum_of_coordinatewiseMinimum
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    {xStar : (i : Fin p) → Ei i}
    (hcoord : is_coordinatewise_minimum F xStar) :
    xStar ∈ effective_domain (separableSum g) := by
  -- A `⊤` value of the separable term would force the composite objective to be `⊤` as well.
  refine mem_effective_domain.mpr <| lt_top_iff_ne_top.mpr ?_
  intro hxStar_top
  have hF_top : F xStar = ⊤ := by
    rw [composite_model_objective_apply, hxStar_top]
    simpa using EReal.add_top_of_ne_bot (hmodel.f_ne_bot xStar)
  exact (lt_top_iff_ne_top.mp (mem_effective_domain.mp hcoord.mem_effective_domain)) hF_top

/-- Helper for Lemma 14.2: a finite sum of coerced real numbers is the coercion of the
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

/-- Helper for Lemma 14.2: replacing one block by another feasible block value preserves
membership in `effective_domain (separableSum g)`. -/
private lemma update_memEffectiveDomainSeparableSum_of_mem
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    {x : (i : Fin p) → Ei i}
    (hx : x ∈ effective_domain (separableSum g))
    (i : Fin p)
    {yi : Ei i}
    (hyi : yi ∈ effective_domain (g i)) :
    Function.update x i yi ∈ effective_domain (separableSum g) := by
  let y : (i : Fin p) → Ei i := Function.update x i yi
  have hy_block :
      ∀ j : Fin p, y j ∈ effective_domain (g j) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simpa [y]
    · simpa [y, Function.update, hji] using
        block_mem_effective_domain_of_mem_separableSum_effective_domain
          g hmodel.g_proper hx j
  have hy_sum :
      separableSum g y = ((((∑ j : Fin p, (g j (y j)).toReal : ℝ)) : ℝ) : EReal) := by
    rw [separableSum_apply]
    calc
      ∑ j : Fin p, g j (y j) = ∑ j : Fin p, ((((g j (y j)).toReal : ℝ)) : EReal) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        exact
          (EReal.coe_toReal
            (mem_effective_domain.mp (hy_block j)).ne
            ((hmodel.g_proper j).ne_bot (y j))).symm
      _ = ((((∑ j : Fin p, (g j (y j)).toReal : ℝ)) : ℝ) : EReal) := by
        simpa using erealCoeFinsetSum Finset.univ (fun j ↦ (g j (y j)).toReal)
  -- Once every block value is finite, the whole separable sum is finite as well.
  refine mem_effective_domain.mpr ?_
  rw [hy_sum]
  simp

/-- Helper for Lemma 14.2: the raw tuple-space Riesz functional evaluates as the finite sum of
the blockwise inner products. -/
private lemma tupleToDualMap_apply_eq_sum
    (v w : (i : Fin p) → Ei i) :
    (InnerProductSpace.toDualMap ℝ ((i : Fin p) → Ei i) v) w =
      ∑ i, inner ℝ (v i) (w i) := by
  -- Route correction: this needs the ambient product inner product to be the canonical tuple one.
  -- Under the canonical raw-tuple Euclidean owner imported from Chapter 11, the displayed
  -- finite-sum formula is exactly the required blockwise pairing identity.
  rw [InnerProductSpace.toDualMap_apply_apply]
  change
    inner ℝ
        ((ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)) v)
        ((ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)) w) =
      ∑ i, inner ℝ (v i) (w i)
  simpa using PiLp.inner_apply (toPiLp v) (toPiLp w)

/-- Helper for Lemma 14.2: evaluating the ambient dual functional on a singleton block direction
recovers the block dual pairing on the chosen coordinate. -/
private lemma ambientToDual_apply_single_eq_blockToDual_apply
    (i : Fin p) (v : (j : Fin p) → Ei j) (d : Ei i) :
    (InnerProductSpace.toDualMap ℝ ((j : Fin p) → Ei j) v) (Pi.single i d : (j : Fin p) → Ei j) =
      (InnerProductSpace.toDualMap ℝ (Ei i) (v i)) d := by
  -- Route correction: expand the ambient tuple pairing directly in the raw owner instead of
  -- transporting through a second product owner.
  rw [tupleToDualMap_apply_eq_sum, InnerProductSpace.toDualMap_apply_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- Helper for Lemma 14.2: differentiating the translated one-block update in the coordinate
variable recovers the canonical singleton insertion map. -/
private lemma rawBlockCoordinateUpdate_hasFDerivAt_single
    (x : (i : Fin p) → Ei i) (i : Fin p) :
    HasFDerivAt
      (fun y : Ei i ↦ block_coordinate_update x i (y - x i))
      (.pi (Pi.single i (.id ℝ (Ei i))))
      (x i) := by
  have hrewrite :
      (fun y : Ei i ↦ block_coordinate_update x i (y - x i)) = Function.update x i := by
    funext y
    ext j
    by_cases hji : j = i
    · subst j
      simp [block_coordinate_update, Function.update]
    · simp [block_coordinate_update, Function.update, hji]
  -- Route correction: rewrite the translated block update to the canonical `Function.update`
  -- map, then reuse the owner-stable `pi` derivative returned by `hasFDerivAt_update`.
  rw [hrewrite]
  simpa using
    (hasFDerivAt_update x (x i) :
      HasFDerivAt (Function.update x i) (.pi (Pi.single i (.id ℝ (Ei i)))) (x i))

/-- Helper for Lemma 14.2: the raw singleton insertion map applies to a block vector as the
expected `Pi.single` insertion. -/
private lemma rawSingletonLinearMap_apply_eq_single
    (i : Fin p) (d : Ei i) :
    (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Ei i)))) d =
      (Pi.single i d : (j : Fin p) → Ei j) := by
  -- Compare coordinates directly: the inserted block is `d` and every other block vanishes.
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- Helper for Lemma 14.2: restricting the ambient derivative of `x ↦ (f x).toReal` to one block
recovers the derivative of the coordinate-update slice `y ↦ (f (Function.update x i y)).toReal`.
-/
private lemma coordinateUpdate_toReal_hasFDerivAt
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    (x : (i : Fin p) → Ei i)
    (hx : x ∈ interior (effective_domain f))
    (i : Fin p) :
    HasFDerivAt
      (fun y : Ei i ↦ (f (Function.update x i y)).toReal)
      (InnerProductSpace.toDualMap ℝ (Ei i) ((∇ (fun z : (j : Fin p) → Ei j ↦ (f z).toReal) x) i))
      (x i) := by
  classical
  have hdiffAt :
      DifferentiableAt ℝ (fun z : (j : Fin p) → Ei j ↦ (f z).toReal) x := by
    exact
      (hmodel.f_toReal_differentiableOn_interior_effective_domain x hx).differentiableAt
        (isOpen_interior.mem_nhds hx)
  have hambient :
      HasFDerivAt
        (fun z : (j : Fin p) → Ei j ↦ (f z).toReal)
        (InnerProductSpace.toDualMap ℝ ((j : Fin p) → Ei j)
          (∇ (fun z : (j : Fin p) → Ei j ↦ (f z).toReal) x))
        x := by
    -- Rewrite the ambient differentiability witness into the `HasFDerivAt` form used for
    -- restriction along the active block direction.
    simpa using hdiffAt.hasGradientAt.hasFDerivAt
  have hupdate :
      block_coordinate_update x i (x i - x i) = x := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [block_coordinate_update]
    · simp [block_coordinate_update, hji]
  have hambientAtUpdate :
      HasFDerivAt
        (fun z : (j : Fin p) → Ei j ↦ (f z).toReal)
        (InnerProductSpace.toDualMap ℝ ((j : Fin p) → Ei j)
          (∇ (fun z : (j : Fin p) → Ei j ↦ (f z).toReal) x))
        (block_coordinate_update x i (x i - x i)) := by
    exact hupdate.symm ▸ hambient
  have hrewrite :
      (fun y : Ei i ↦ block_coordinate_update x i (y - x i)) = Function.update x i := by
    funext y
    ext j
    by_cases hji : j = i
    · subst j
      simp [block_coordinate_update, Function.update]
    · simp [block_coordinate_update, Function.update, hji]
  have hcomp :
      HasFDerivAt
        (fun y : Ei i ↦ (f (block_coordinate_update x i (y - x i))).toReal)
        ((InnerProductSpace.toDualMap ℝ ((j : Fin p) → Ei j)
            (∇ (fun z : (j : Fin p) → Ei j ↦ (f z).toReal) x)).comp
          (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Ei i)))))
        (x i) := by
    -- Restrict the ambient derivative to the singleton block insertion map.
    simpa [Function.comp, hupdate] using
      hambientAtUpdate.comp (x i) (rawBlockCoordinateUpdate_hasFDerivAt_single x i)
  have hfunRewrite :
      (fun y : Ei i ↦ (f (block_coordinate_update x i (y - x i))).toReal) =
        fun y : Ei i ↦ (f (Function.update x i y)).toReal := by
    funext y
    exact congrArg (fun z : (j : Fin p) → Ei j ↦ (f z).toReal) (congrFun hrewrite y)
  have hdual :
      (InnerProductSpace.toDualMap ℝ ((j : Fin p) → Ei j)
          (∇ (fun z : (j : Fin p) → Ei j ↦ (f z).toReal) x)).comp
        (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Ei i)))) =
      InnerProductSpace.toDualMap ℝ (Ei i)
        ((∇ (fun z : (j : Fin p) → Ei j ↦ (f z).toReal) x) i) := by
    -- Compare the two dual maps on an arbitrary block direction.
    ext d
    rw [ContinuousLinearMap.comp_apply, rawSingletonLinearMap_apply_eq_single]
    exact
      ambientToDual_apply_single_eq_blockToDual_apply
        i
        (∇ (fun z : (j : Fin p) → Ei j ↦ (f z).toReal) x)
        d
  -- Rewrite the translated block update back to the coordinate-update slice and replace the
  -- composed ambient dual by the block dual.
  exact hfunRewrite ▸ (hdual ▸ hcomp)

/-- Helper for Lemma 14.2: the Chapter 11 block slice
`d ↦ (f (block_coordinate_update x i d)).toReal` has derivative given by the `i`-th ambient
gradient coordinate. -/
private lemma blockCoordinateSlice_hasFDerivAt_ambientGradient
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    (x : (i : Fin p) → Ei i)
    (hx : x ∈ interior (effective_domain f))
    (i : Fin p) :
    HasFDerivAt
      (block_coordinate_slice f x i)
      (InnerProductSpace.toDualMap ℝ (Ei i) ((∇ (fun z : (j : Fin p) → Ei j ↦ (f z).toReal) x) i))
      0 := by
  have hshift :
      HasFDerivAt
        (fun d : Ei i ↦ x i + d)
        (ContinuousLinearMap.id ℝ (Ei i))
        0 := by
    -- Translate the displacement variable `d` back to the coordinate variable `y = x_i + d`.
    simpa [add_comm] using (hasFDerivAt_id (0 : Ei i)).const_add (x i)
  have hcoordAtShift :
      HasFDerivAt
        (fun y : Ei i ↦ (f (Function.update x i y)).toReal)
        (InnerProductSpace.toDualMap ℝ (Ei i) ((∇ (fun z : (j : Fin p) → Ei j ↦ (f z).toReal) x) i))
        (x i + 0) := by
    simpa using coordinateUpdate_toReal_hasFDerivAt hmodel x hx i
  have hcoord :
      HasFDerivAt
        (fun d : Ei i ↦ (f (Function.update x i (x i + d))).toReal)
        (InnerProductSpace.toDualMap ℝ (Ei i) ((∇ (fun z : (j : Fin p) → Ei j ↦ (f z).toReal) x) i))
        0 := by
    -- Compose the coordinate-update derivative with the translation `d ↦ d + x_i`.
    simpa [Function.comp] using hcoordAtShift.comp 0 hshift
  have hslice :
      block_coordinate_slice f x i =
        fun d : Ei i ↦ (f (Function.update x i (x i + d))).toReal := by
    funext d
    simp [block_coordinate_slice_apply, block_coordinate_update_eq_update, add_assoc, add_comm,
      add_left_comm]
  -- Normalize the translated coordinate-update slice back to the Chapter 11 displacement slice.
  rw [hslice]
  exact hcoord

/-- Helper for Lemma 14.2: feasible block replacements stay in the interior finite domain of the
one-block smooth slice. -/
private lemma memInteriorFiniteDomain_updateSlice_of_mem_effectiveDomain
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    {xStar : (i : Fin p) → Ei i}
    (hxSep : xStar ∈ effective_domain (separableSum g))
    (i : Fin p)
    {yi : Ei i}
    (hyi : yi ∈ effective_domain (g i)) :
    yi ∈ interior (finite_domain (fun y : Ei i ↦ f (Function.update xStar i y))) := by
  classical
  let φ : Ei i → ((j : Fin p) → Ei j) := Function.update xStar i
  have hφ :
      Continuous φ := by
    have hφeq : φ = fun y : Ei i ↦ xStar + Pi.single i (y - xStar i) := by
      funext y
      ext j
      by_cases hji : j = i
      · subst j
        simp [φ, Function.update]
      · simp [φ, Function.update, hji]
    rw [hφeq]
    exact
      continuous_const.add
        ((ambientBlockSingle_continuous i).comp (continuous_id.sub continuous_const))
  have hyUpdateSep :
      Function.update xStar i yi ∈ effective_domain (separableSum g) :=
    update_memEffectiveDomainSeparableSum_of_mem hmodel hxSep i hyi
  have hyUpdateInt :
      Function.update xStar i yi ∈ interior (effective_domain f) :=
    hmodel.g_effective_domain_subset_interior_f_effective_domain hyUpdateSep
  have hpull :
      yi ∈ interior (φ ⁻¹' effective_domain f) := by
    have hpre : yi ∈ φ ⁻¹' interior (effective_domain f) := hyUpdateInt
    exact preimage_interior_subset_interior_preimage hφ hpre
  -- Properness of `f` identifies the finite domain of the update slice with its effective domain.
  simpa [φ, effective_domain,
    finite_domain_eq_effective_domain
      (f := fun y : Ei i ↦ f (Function.update xStar i y))
      (fun y ↦ hmodel.f_ne_bot (Function.update xStar i y))] using hpull

-- Proof sketch: fix a block `i`. The coordinate-wise minimum inequalities for `F` imply that
-- `xStar i` globally minimizes the one-block slice `y ↦ f (Function.update xStar i y) + g i y`.
-- The standing Assumption 14.6 owner `IsAlternatingMinimizationCompositeModel f g` supplies the
-- regularity hypotheses needed for the one-block first-order optimality theorem, giving
-- `-∇ᵢ f(xStar) ∈ ∂ g_i(xStar_i)` for every block. The block-separable regularizer then
-- identifies these coordinatewise subgradient conditions with the Chapter 3 stationary-point
-- predicate for `f + separableSum g`.
/-- Companion API for Lemma 14.2: under the standing composite-model assumptions from
Assumption 14.6, a coordinate-wise minimum of `F(x) = f(x) + ∑ i, g_i(x_i)` satisfies the
blockwise Euclidean subdifferential condition for every block. This keeps the Chapter 11
coordinatewise first-order condition available without forcing downstream files to restate the
full regularity bundle carried by `IsAlternatingMinimizationCompositeModel f g`. -/
theorem coordinatewise_negative_gradient_mem_euclideanSubdifferential_of_coordinatewise_minimum
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    {xStar : (i : Fin p) → Ei i}
    (hcoord : is_coordinatewise_minimum F xStar) :
    ∀ i : Fin p,
      -((∇ (fun y : (i : Fin p) → Ei i ↦ (f y).toReal) xStar) i) ∈
        euclideanSubdifferential (g i) (xStar i) := by
  intro i
  have hxSep :
      xStar ∈ effective_domain (separableSum g) :=
    memEffectiveDomainSeparableSum_of_coordinatewiseMinimum hmodel hcoord
  have hxInterior :
      xStar ∈ interior (effective_domain f) :=
    hmodel.g_effective_domain_subset_interior_f_effective_domain hxSep
  have hxBlock :
      xStar i ∈ effective_domain (g i) := by
    simpa using
      block_mem_effective_domain_of_mem_separableSum_effective_domain
        g
        hmodel.g_proper
        hxSep
        i
  have hinactive_ne_bot :
      (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xStar j else xStar j)) ≠ ⊥ := by
    simpa using
      ereal_sum_ne_bot
        (Finset.univ.erase i)
        (fun j ↦ g j (xStar j))
        (fun j _ ↦ (hmodel.g_proper j).ne_bot (xStar j))
  have hactive_ne_bot :
      alternating_minimization_composite_block_objective f g xStar xStar i (xStar i) ≠ ⊥ := by
    -- At the current block value, both the smooth term and the active penalty are finite below.
    simpa [alternating_minimization_composite_block_objective,
      alternating_minimization_block_objective_base_apply] using
      ((EReal.add_ne_bot_iff : f xStar + g i (xStar i) ≠ ⊥ ↔
          f xStar ≠ ⊥ ∧ g i (xStar i) ≠ ⊥).2
        ⟨hmodel.f_ne_bot xStar, (hmodel.g_proper i).ne_bot (xStar i)⟩)
  have hinactive :
      (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xStar j else xStar j)) =
        (((∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xStar j else xStar j)).toReal : ℝ) :
          EReal) := by
    -- Proposition 14.2 needs the frozen inactive penalty term to be a genuine finite constant.
    refine
      inactive_penalty_eq_coe_toReal_of_ne_bot_of_mem_effective_domain
        (f := f)
        (g := g)
        (xk := xStar)
        (xNext := xStar)
        (i := i)
        hinactive_ne_bot
        hactive_ne_bot
        ?_
    simpa using hcoord.mem_effective_domain
  have hminBlock :
      IsMinOn
        (alternating_minimization_composite_block_objective f g xStar xStar i)
        Set.univ
        (xStar i) := by
    -- Proposition 14.2 rewrites the full block minimum into the displayed one-block objective.
    exact
      (isMinOn_alternating_minimization_full_objective_iff_isMinOn_composite_block_objective
        (f := f)
        (g := g)
        (xk := xStar)
        (xNext := xStar)
        (i := i)
        hinactive
        (xStar i)).1
        (hcoord.isMinOn i)
  have hfBlockProper :
      IsProperExtendedRealFunction (alternating_minimization_block_objective f xStar xStar i) := by
    refine
      { ne_bot := ?_, effective_domain_nonempty := ?_ }
    · intro y
      simpa [alternating_minimization_block_objective_base_apply] using
        hmodel.f_ne_bot (Function.update xStar i y)
    · refine ⟨xStar i, ?_⟩
      simpa [alternating_minimization_block_objective_base_apply] using interior_subset hxInterior
  have hdomBlock :
      effective_domain (g i) ⊆
        interior (finite_domain (alternating_minimization_block_objective f xStar xStar i)) := by
    have hblockEq :
        alternating_minimization_block_objective f xStar xStar i =
          fun y : Ei i ↦ f (Function.update xStar i y) := by
      funext y
      simp [alternating_minimization_block_objective_base_apply]
    intro yi hyi
    -- Pull back the ambient interior-domain condition through the coordinate-update map.
    rw [hblockEq]
    exact
      memInteriorFiniteDomain_updateSlice_of_mem_effectiveDomain
        hmodel
        hxSep
        i
        hyi
  have hdiffBlock :
      is_differentiable_at (alternating_minimization_block_objective f xStar xStar i) (xStar i) := by
    refine ⟨hdomBlock hxBlock, ?_⟩
    -- The ambient derivative restriction gives differentiability of the one-block smooth slice.
    simpa [alternating_minimization_block_objective_base_apply] using
      (coordinateUpdate_toReal_hasFDerivAt hmodel xStar hxInterior i).differentiableAt
  have hlocal :
      IsLocalMin
        (alternating_minimization_composite_block_objective f g xStar xStar i)
        (xStar i) :=
    hminBlock.isLocalMin (by simp)
  have hstationary :
      is_stationary_point
        (alternating_minimization_block_objective f xStar xStar i)
        (g i)
        (xStar i) :=
    is_stationary_point_of_isLocalMin
      hfBlockProper
      (hmodel.g_proper i)
      (hmodel.g_convex i)
      hdomBlock
      hxBlock
      hdiffBlock
      hlocal
  rw [is_stationary_point_iff] at hstationary
  have hupdateGradient :
      ∇ (fun y : Ei i ↦ (f (Function.update xStar i y)).toReal) (xStar i) =
        ((∇ (fun y : (j : Fin p) → Ei j ↦ (f y).toReal) xStar) i) := by
    have hgradHasFDerivAt :
        HasFDerivAt
          (fun y : Ei i ↦ (f (Function.update xStar i y)).toReal)
          (InnerProductSpace.toDualMap ℝ (Ei i)
            (∇ (fun y : Ei i ↦ (f (Function.update xStar i y)).toReal) (xStar i)))
          (xStar i) := by
      -- The update slice has a unique gradient at `xStar i`.
      simpa using
        (coordinateUpdate_toReal_hasFDerivAt hmodel xStar hxInterior i).differentiableAt.hasGradientAt.hasFDerivAt
    have hdual :
        InnerProductSpace.toDualMap ℝ (Ei i)
          (∇ (fun y : Ei i ↦ (f (Function.update xStar i y)).toReal) (xStar i)) =
        InnerProductSpace.toDualMap ℝ (Ei i)
          ((∇ (fun y : (j : Fin p) → Ei j ↦ (f y).toReal) xStar) i) := by
      exact hgradHasFDerivAt.unique
        (coordinateUpdate_toReal_hasFDerivAt hmodel xStar hxInterior i)
    exact (InnerProductSpace.toDualMap ℝ (Ei i)).injective hdual
  have hnegDual :
      (-InnerProductSpace.toDual ℝ (Ei i)
          (∇ (fun y : Ei i ↦ (f (Function.update xStar i y)).toReal) (xStar i)) :
          Module.Dual ℝ (Ei i)) =
        InnerProductSpace.toDualMap ℝ (Ei i)
          (-((∇ (fun y : (j : Fin p) → Ei j ↦ (f y).toReal) xStar) i)) := by
    -- Rewrite the stationary dual vector into the Euclidean subgradient spelling on `Ei i`.
    ext d
    simp [InnerProductSpace.toDual_apply_eq_toDualMap_apply, hupdateGradient]
  rw [mem_euclideanSubdifferential_iff]
  simpa [hnegDual] using hstationary.2

/-- Lemma 14.2: under the standing composite-model assumptions from Assumption 14.6, every
coordinate-wise minimum of the composite objective `F(x) = f(x) + ∑ i, g_i(x_i)` is a stationary
point of the composite problem `(14.9)`. The coordinate-wise minimum hypothesis uses the
source-facing owner predicate from Definition 14.2 directly on the block product, while the
regularity assumptions are supplied canonically by
`IsAlternatingMinimizationCompositeModel f g`. The proof route factors through the companion
blockwise subdifferential theorem
`coordinatewise_negative_gradient_mem_euclideanSubdifferential_of_coordinatewise_minimum`. -/
theorem is_stationary_point_of_coordinatewise_minimum
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    {xStar : (i : Fin p) → Ei i}
    (hcoord : is_coordinatewise_minimum F xStar) :
    is_stationary_point f (separableSum g) xStar := by
  -- Route correction: use the Chapter 11 stationarity equivalence only after proving the ambient
  -- block-slice derivative formula directly in the displacement variable.
  exact
    (is_stationary_point_iff_coordinatewise_negative_block_gradient_mem_euclideanSubdifferential
      hmodel.f_proper
      hmodel.g_proper
      hmodel.g_closed
      hmodel.g_convex
      hmodel.f_closed
      hmodel.f_effective_domain_convex
      hmodel.g_effective_domain_subset_interior_f_effective_domain
      hmodel.f_toReal_differentiableOn_interior_effective_domain
      (fun i {x} hx ↦ blockCoordinateSlice_hasFDerivAt_ambientGradient hmodel x hx i)
      xStar).2
      (coordinatewise_negative_gradient_mem_euclideanSubdifferential_of_coordinatewise_minimum
        hmodel
        hcoord)

end
