/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_6
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.6 is `source-facing` in the chapter Fenchel-duality API. Its owner declarations are
 already upstream: `effective_domain` from Definition 2.1, `IsProperExtendedRealFunction` from
Definition 2.5, `is_convex_function` from Definition 2.6, `intrinsicInterior ℝ` from Definition
3.7, and the Chapter 4 dual objects `conjugate_function`, `fenchel_dual_objective`, and
`fenchel_dual_problem_value` from Definitions 4.1 and 4.8. This file therefore keeps only the
duality and attainment statements, reusing those owners directly instead of repeating parallel
local copies. -/

recall effective_domain
recall IsProperExtendedRealFunction
recall is_convex_function
recall subdifferential
recall mem_subdifferential
recall subdifferential_nonempty_at_relativeInterior_point
recall intrinsicInterior
recall translatedEffectiveDomainZero_mem_interior
recall fenchel_split_lagrangian
recall fenchel_split_lagrangian_apply
recall fenchel_dual_objective
recall fenchel_dual_objective_eq_sInf_split_lagrangian
recall fenchel_dual_problem_value
recall fenchel_dual_problem_value_eq_sSup

/-- Helper for Theorem 4.6: the perturbation value function
`d ↦ inf_u (f u + g (u + d))` whose value at `0` is the primal infimum. -/
private noncomputable def zeroCaseValue
    (f g : E → EReal) : E → EReal :=
  fun d ↦ sInf (Set.range fun u : E ↦ f u + g (u + d))

/-- Helper for Theorem 4.6: any feasible pair `(u, u + d)` puts `d` in the effective domain of the
perturbation value function. -/
private theorem mem_effectiveDomain_zeroCaseValue_of_mem_domains
    (f g : E → EReal)
    {u d : E} (hu₁ : u ∈ effective_domain f) (hu₂ : u + d ∈ effective_domain g) :
    d ∈ effective_domain (zeroCaseValue f g) := by
  rw [mem_effective_domain]
  have hu₁_top : f u ≠ ⊤ := lt_top_iff_ne_top.mp hu₁
  have hu₂_top : g (u + d) ≠ ⊤ := lt_top_iff_ne_top.mp hu₂
  -- Insert the concrete feasible witness and note that its value is finite.
  by_cases hbot₁ : f u = ⊥
  · exact lt_of_le_of_lt (sInf_le ⟨u, rfl⟩) <| by simp [hbot₁]
  · by_cases hbot₂ : g (u + d) = ⊥
    · exact lt_of_le_of_lt (sInf_le ⟨u, rfl⟩) <| by simp [hbot₂]
    · refine lt_of_le_of_lt (sInf_le ⟨u, rfl⟩) ?_
      exact
        lt_top_iff_ne_top.mpr <|
          (EReal.add_ne_top_iff_ne_top₂ hbot₁ hbot₂).mpr
            ⟨hu₁_top, hu₂_top⟩

/-- Helper for Theorem 4.6: under pointwise `≠ ⊥`, membership in the perturbation effective domain
is exactly the existence of a feasible finite pair. -/
private theorem mem_effectiveDomain_zeroCaseValue_iff_exists
    (f g : E → EReal) (hf_ne_bot : ∀ x : E, f x ≠ ⊥) (hg_ne_bot : ∀ x : E, g x ≠ ⊥)
    {d : E} :
    d ∈ effective_domain (zeroCaseValue f g) ↔
      ∃ u : E, u ∈ effective_domain f ∧ u + d ∈ effective_domain g := by
  constructor
  · intro hd
    rw [mem_effective_domain] at hd
    rcases exists_lt_of_csInf_lt (Set.range_nonempty (fun u : E ↦ f u + g (u + d))) hd with
      ⟨a, ⟨u, rfl⟩, hau⟩
    have hsum_ne_top : f u + g (u + d) ≠ ⊤ := lt_top_iff_ne_top.mp hau
    have hsplit :
        f u ≠ ⊤ ∧ g (u + d) ≠ ⊤ :=
      (EReal.add_ne_top_iff_ne_top₂ (hf_ne_bot u) (hg_ne_bot (u + d))).mp hsum_ne_top
    exact ⟨u, lt_top_iff_ne_top.mpr hsplit.1, lt_top_iff_ne_top.mpr hsplit.2⟩
  · rintro ⟨u, hu₁, hu₂⟩
    exact mem_effectiveDomain_zeroCaseValue_of_mem_domains f g hu₁ hu₂

/-- Helper for Theorem 4.6: the perturbation value function is convex because it is a partial
infimum of a jointly convex kernel. -/
private theorem zeroCaseValue_isConvex
    (f g : E → EReal) (hf_ne_bot : ∀ x : E, f x ≠ ⊥) (hg_ne_bot : ∀ x : E, g x ≠ ⊥)
    (hf_convex : is_convex_function f) (hg_convex : is_convex_function g) :
    is_convex_function (zeroCaseValue f g) := by
  let K : E × E → EReal := fun p ↦ f p.2 + g (p.2 + p.1)
  have hSecond : is_convex_function (fun p : E × E ↦ f p.2) := by
    -- The first kernel factor is `f` pulled back along the second projection.
    simpa using
      is_convex_function_precompose_linearMap_add
        hf_convex
        (LinearMap.snd ℝ E E)
        (0 : E)
  have hSum : is_convex_function (fun p : E × E ↦ g (p.2 + p.1)) := by
    -- The second kernel factor is `g` pulled back along the sum map `(d, u) ↦ u + d`.
    simpa [add_comm] using
      is_convex_function_precompose_linearMap_add
        hg_convex
        (LinearMap.snd ℝ E E + LinearMap.fst ℝ E E)
        (0 : E)
  have hKernel : is_convex_function K := by
    -- Add the two jointly convex factors pointwise.
    simpa [K] using
      is_convex_function_pointwise_add
        hSecond hSum
        (fun p ↦ hf_ne_bot p.2)
        (fun p ↦ hg_ne_bot (p.2 + p.1))
  -- Partial minimization preserves convexity of the perturbation value function.
  simpa [zeroCaseValue, K] using
    partial_infimum_is_convex_function hKernel

/-- Helper for Theorem 4.6: evaluating the perturbation value function at `0` recovers the primal
infimum `inf_x (f x + g x)`. -/
private theorem zeroCaseValue_zero_eq_primalValue
    (f g : E → EReal) :
    zeroCaseValue f g (0 : E) = sInf (Set.range fun x : E ↦ f x + g x) := by
  -- The origin fiber is exactly the unsplit primal objective.
  simp [zeroCaseValue]

/-- Helper for Theorem 4.6: the common relative-interior qualification transports to the origin of
the perturbation effective domain. -/
private theorem zero_mem_intrinsicInterior_effectiveDomain_zeroCaseValue
    (f g : E → EReal)
    (hf_ne_bot : ∀ x : E, f x ≠ ⊥) (hg_ne_bot : ∀ x : E, g x ≠ ⊥)
    (hqual :
      (intrinsicInterior ℝ (effective_domain f) ∩
        intrinsicInterior ℝ (effective_domain g)).Nonempty) :
    (0 : E) ∈ intrinsicInterior ℝ (effective_domain (zeroCaseValue f g)) := by
  -- Route correction: once both summands avoid `⊥`, the perturbation-domain geometry is governed
  -- by feasible pairs in the two effective domains and the subtraction map.
  rcases hqual with ⟨x₀, hx₀₁, hx₀₂⟩
  have hxdom₁ : x₀ ∈ effective_domain f := intrinsicInterior_subset hx₀₁
  have hxdom₂ : x₀ ∈ effective_domain g := intrinsicInterior_subset hx₀₂
  let D : Set E := effective_domain (zeroCaseValue f g)
  let P₁ : Submodule ℝ E := (affineSpan ℝ (effective_domain f)).direction
  let P₂ : Submodule ℝ E := (affineSpan ℝ (effective_domain g)).direction
  let U₁ : Set P₁ := {v : P₁ | x₀ + (v : E) ∈ effective_domain f}
  let U₂ : Set P₂ := {v : P₂ | x₀ + (v : E) ∈ effective_domain g}
  have hU₁_zero : (0 : P₁) ∈ interior U₁ := by
    -- Translate the first relative-interior point into an honest interior neighborhood at `0`.
    simpa [U₁, P₁] using translatedEffectiveDomainZero_mem_interior f x₀ hx₀₁
  have hU₂_zero : (0 : P₂) ∈ interior U₂ := by
    -- Apply the same translation argument to the second effective domain.
    simpa [U₂, P₂] using translatedEffectiveDomainZero_mem_interior g x₀ hx₀₂
  let diffLinear : P₁ × P₂ →ₗ[ℝ] E :=
    { toFun := fun p ↦ (p.2 : E) - (p.1 : E)
      map_add' := by
        intro p q
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro a p
        simp [sub_eq_add_neg] }
  let W : Submodule ℝ E := LinearMap.range diffLinear
  let diffToRange : P₁ × P₂ →ₗ[ℝ] W := diffLinear.rangeRestrict
  let U : Set (P₁ × P₂) := U₁ ×ˢ U₂
  have hU_zero : (0 : P₁ × P₂) ∈ interior U := by
    -- The product of the two translated neighborhoods is still an interior neighborhood of `0`.
    rw [show U = U₁ ×ˢ U₂ by rfl, interior_prod_eq]
    exact ⟨hU₁_zero, hU₂_zero⟩
  have hImage_subset :
      diffToRange '' U ⊆ ((↑) ⁻¹' D : Set W) := by
    intro w hw
    rcases hw with ⟨p, hp, rfl⟩
    rcases hp with ⟨hp₁, hp₂⟩
    -- A pair of translated domain points yields a feasible witness for the fiber difference.
    refine
      mem_effectiveDomain_zeroCaseValue_of_mem_domains f g
        (u := x₀ + (p.1 : E)) (d := (p.2 : E) - (p.1 : E)) ?_ ?_
    · simpa [U₁] using hp₁
    · simpa [U₂, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hp₂
  have hDiffOpen : IsOpenMap diffToRange :=
    diffToRange.isOpenMap_of_finiteDimensional (LinearMap.surjective_rangeRestrict diffLinear)
  let O : Set W := diffToRange '' interior U
  have hO_zero : (0 : W) ∈ O := by
    -- The open-map image contains the origin because the source neighborhood contains the zero pair.
    refine ⟨0, hU_zero, ?_⟩
    simp [diffToRange, diffLinear]
  have hO_open : IsOpen O := by
    -- The image of the interior product neighborhood is open in the range subspace.
    exact hDiffOpen _ isOpen_interior
  have hO_subset : O ⊆ ((↑) ⁻¹' D : Set W) := by
    intro w hw
    rcases hw with ⟨p, hp, rfl⟩
    exact hImage_subset ⟨p, interior_subset hp, rfl⟩
  have hW_zero : (0 : W) ∈ interior ((↑) ⁻¹' D : Set W) := by
    -- Move the open product neighborhood through the subtraction map, then enlarge to the full
    -- preimage of the perturbation effective domain in the range space.
    exact hO_open.mem_nhds hO_zero |> mem_interior_iff_mem_nhds.2 |> interior_mono hO_subset
  have hpreimage_span_top : Submodule.span ℝ (((↑) ⁻¹' D : Set W)) = ⊤ := by
    -- A nonempty interior neighborhood of `0` spans the whole range subspace.
    apply Submodule.eq_top_of_nonempty_interior'
    refine ⟨0, ?_⟩
    refine interior_mono ?_ hW_zero
    exact Submodule.subset_span
  have hDomain_subset_W : D ⊆ (W : Set E) := by
    intro d hd
    rcases (mem_effectiveDomain_zeroCaseValue_iff_exists f g hf_ne_bot hg_ne_bot).1 hd with
      ⟨u, hu₁, hu₂⟩
    have hu₁_aff : u ∈ affineSpan ℝ (effective_domain f) :=
      subset_affineSpan ℝ (effective_domain f) hu₁
    have hx₀_aff₁ : x₀ ∈ affineSpan ℝ (effective_domain f) :=
      subset_affineSpan ℝ (effective_domain f) hxdom₁
    have hu₂_aff : u + d ∈ affineSpan ℝ (effective_domain g) :=
      subset_affineSpan ℝ (effective_domain g) hu₂
    have hx₀_aff₂ : x₀ ∈ affineSpan ℝ (effective_domain g) :=
      subset_affineSpan ℝ (effective_domain g) hxdom₂
    have hp₁_mem :
        u - x₀ ∈ (affineSpan ℝ (effective_domain f)).direction := by
      simpa [P₁] using
        (affineSpan ℝ (effective_domain f)).vsub_mem_direction hu₁_aff hx₀_aff₁
    have hp₂_mem :
        u + d - x₀ ∈ (affineSpan ℝ (effective_domain g)).direction := by
      simpa [P₂] using
        (affineSpan ℝ (effective_domain g)).vsub_mem_direction hu₂_aff hx₀_aff₂
    let p₁ : P₁ := ⟨u - x₀, hp₁_mem⟩
    let p₂ : P₂ := ⟨u + d - x₀, hp₂_mem⟩
    refine ⟨⟨p₁, p₂⟩, ?_⟩
    -- The witness decomposition places `d` in the subtraction-map range.
    simp [diffLinear, p₁, p₂, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have himage_preimage :
      (Submodule.subtype W) '' (((↑) ⁻¹' D : Set W)) = D := by
    ext d
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hd
      refine ⟨⟨d, hDomain_subset_W hd⟩, hd, rfl⟩
  have hspan_D : Submodule.span ℝ D = W := by
    -- Map the full linear span of the preimage through the subtype inclusion back into `E`.
    calc
      Submodule.span ℝ D =
          Submodule.map (Submodule.subtype W) (Submodule.span ℝ (((↑) ⁻¹' D : Set W))) := by
            rw [Submodule.map_span, himage_preimage]
      _ = Submodule.map (Submodule.subtype W) ⊤ := by rw [hpreimage_span_top]
      _ = W := by simp
  have hzero_mem_D : (0 : E) ∈ D := by
    -- The qualification witness itself produces the zero difference.
    simpa [D] using
      (mem_effectiveDomain_zeroCaseValue_of_mem_domains
        f g (u := x₀) (d := 0) hxdom₁ (by simpa using hxdom₂))
  have hD_le : affineSpan ℝ D ≤ W.toAffineSubspace := by
    -- The domain already lies in the range subspace, so its affine hull does as well.
    simpa [hspan_D] using (affineSpan_le_toAffineSubspace_span (k := ℝ) (s := D))
  have hW_le : W.toAffineSubspace ≤ affineSpan ℝ D := by
    intro x hx
    have hvectorSpan_D :
        vectorSpan ℝ D = Submodule.span ℝ D := by
      simpa using
        (vectorSpan_eq_span_vsub_set_right (k := ℝ) (s := D) hzero_mem_D)
    have hvec : x ∈ vectorSpan ℝ D := by
      rw [hvectorSpan_D, hspan_D]
      simpa [Submodule.mem_toAffineSubspace] using hx
    have hzero_aff : (0 : E) ∈ affineSpan ℝ D := mem_affineSpan ℝ hzero_mem_D
    -- Because `0 ∈ D`, every vector in the span of `D` is also a point in its affine hull.
    simpa using
      vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan (s := D) hzero_aff hvec
  have hspan_D_aff : affineSpan ℝ D = W.toAffineSubspace :=
    le_antisymm hD_le hW_le
  -- Rewrite the intrinsic-interior ambient affine span as the range subspace and use the open
  -- neighborhood already constructed there.
  rw [mem_intrinsicInterior, hspan_D_aff]
  refine ⟨⟨(0 : E), by simp [Submodule.mem_toAffineSubspace]⟩, ?_, rfl⟩
  simpa [D, Submodule.mem_toAffineSubspace] using hW_zero

/-- Helper for Theorem 4.6: the split dual objective is always bounded above by the unsplit primal
infimum by testing the split infimum at `z = x`. -/
private theorem fenchelDualProblemValue_le_zeroCaseValue_zero
    (f g : E → EReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : IsProperExtendedRealFunction g) :
    fenchel_dual_problem_value f g ≤ zeroCaseValue f g (0 : E) := by
  rw [fenchel_dual_problem_value_eq_sSup]
  refine sSup_le ?_
  rintro _ ⟨y, rfl⟩
  rw [fenchel_dual_objective_eq_sInf_split_lagrangian f g hf_proper hg_proper y]
  refine le_sInf ?_
  rintro _ ⟨x, rfl⟩
  -- Evaluating the split infimum at the diagonal witness `(x, x)` recovers the primal fiber value.
  simpa [zeroCaseValue, fenchel_split_lagrangian] using
    (sInf_le ⟨(x, x), rfl⟩ :
      sInf (Set.range fun xz : E × E ↦ fenchel_split_lagrangian f g xz.1 xz.2 y) ≤
        fenchel_split_lagrangian f g x x y)

/-- Helper for Theorem 4.6: a subgradient of the perturbation value function at the origin yields a
dual vector whose Fenchel objective dominates the primal value. -/
private theorem zeroCaseValue_le_fenchelDualObjective_of_mem_subdifferential_zero
    (f g : E → EReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : IsProperExtendedRealFunction g)
    {η : Module.Dual ℝ E}
    (hη : η ∈ subdifferential (zeroCaseValue f g) (0 : E)) :
    zeroCaseValue f g (0 : E) ≤ fenchel_dual_objective f g (-η) := by
  have hf_ne_bot : ∀ x : E, f x ≠ ⊥ := hf_proper.ne_bot
  have hg_ne_bot : ∀ x : E, g x ≠ ⊥ := hg_proper.ne_bot
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hη
  rcases hη with ⟨_, hsupport⟩
  rw [fenchel_dual_objective_eq_sInf_split_lagrangian f g hf_proper hg_proper (-η)]
  refine le_sInf ?_
  rintro _ ⟨p, rfl⟩
  rcases p with ⟨x, z⟩
  dsimp
  by_cases hx : x ∈ effective_domain f
  · by_cases hz : z ∈ effective_domain g
    · let d : E := z - x
      have hzd : x + d ∈ effective_domain g := by
        simpa [d, sub_eq_add_neg, add_assoc] using hz
      have hd : d ∈ effective_domain (zeroCaseValue f g) := by
        simpa [d, sub_eq_add_neg, add_assoc] using
          (mem_effectiveDomain_zeroCaseValue_of_mem_domains f g hx hzd)
      have hsupport' :
          zeroCaseValue f g d ≥ zeroCaseValue f g (0 : E) + (η (d - 0) : EReal) :=
        hsupport d hd
      have hupper :
          zeroCaseValue f g d ≤ f x + g z := by
        -- The feasible pair `(x, z)` gives an upper witness in the defining infimum.
        simpa [zeroCaseValue, d, sub_eq_add_neg, add_assoc] using
          (sInf_le ⟨x, rfl⟩ :
            zeroCaseValue f g d ≤ f x + g (x + d))
      have hcombined :
          zeroCaseValue f g (0 : E) + (η (z - x) : EReal) ≤ f x + g z := by
        simpa [d] using hsupport'.trans hupper
      have hshift :
          zeroCaseValue f g (0 : E) ≤ f x + g z - (η (z - x) : EReal) := by
        exact
          (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot (η (z - x))))
            (.inl (EReal.coe_ne_top (η (z - x))))).2
            hcombined
      have hneg_eval :
          ((-η) (z - x) : EReal) = -(η (z - x) : EReal) := by
        have hreal : (-η) (z - x) = -(η (z - x)) := by
          simp
        exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal
      -- Rewrite the shifted bound into the split Lagrangian normalization at `-η`.
      calc
        zeroCaseValue f g (0 : E) ≤ f x + g z - (η (z - x) : EReal) := hshift
        _ = f x + g z + (-(η (z - x) : EReal)) := by
          rw [sub_eq_add_neg]
        _ = f x + g z + ((-η) (z - x) : EReal) := by
          rw [hneg_eval]
        _ = fenchel_split_lagrangian f g x z (-η) := by
          symm
          rw [fenchel_split_lagrangian_apply, hneg_eval]
    · have hgz_top : g z = ⊤ := by
        refine le_antisymm le_top (not_lt.mp ?_)
        simpa [mem_effective_domain] using hz
      -- Outside the effective domain of `g`, the split Lagrangian is `⊤`.
      have htail_ne_bot : -((η (z - x) : EReal)) ≠ ⊥ := by
        intro hbot
        have htop : ((η (z - x) : EReal)) = ⊤ :=
          EReal.neg_eq_bot_iff.mp hbot
        exact EReal.coe_ne_top (η (z - x)) htop
      have hvalue_top : f x + g z + -((η (z - x) : EReal)) = ⊤ := by
        rw [hgz_top]
        rw [EReal.add_top_of_ne_bot (hf_ne_bot x)]
        rw [EReal.top_add_of_ne_bot htail_ne_bot]
      calc
        zeroCaseValue f g (0 : E) ≤ ⊤ := le_top
        _ = f x + g z + -((η (z - x) : EReal)) := hvalue_top.symm
  · have hfx_top : f x = ⊤ := by
      refine le_antisymm le_top (not_lt.mp ?_)
      simpa [mem_effective_domain] using hx
    -- Outside the effective domain of `f`, the split Lagrangian is `⊤`.
    have htail_ne_bot : -((η (z - x) : EReal)) ≠ ⊥ := by
      intro hbot
      have htop : ((η (z - x) : EReal)) = ⊤ :=
        EReal.neg_eq_bot_iff.mp hbot
      exact EReal.coe_ne_top (η (z - x)) htop
    have hvalue_top : f x + g z + -((η (z - x) : EReal)) = ⊤ := by
      rw [hfx_top]
      rw [EReal.top_add_of_ne_bot (hg_ne_bot z)]
      rw [EReal.top_add_of_ne_bot htail_ne_bot]
    calc
      zeroCaseValue f g (0 : E) ≤ ⊤ := le_top
      _ = f x + g z + -((η (z - x) : EReal)) := hvalue_top.symm

-- Proof sketch: apply Fenchel--Rockafellar duality to the separable objective on `E × E` composed
-- with the diagonal map `x ↦ (x, x)`. The relative-interior qualification is exactly the standard
-- constraint qualification for this formulation. The source displays a primal `min`, but the
-- canonical Chapter 4 owner records the corresponding primal optimal value as the infimum
-- `sInf (Set.range fun x ↦ f x + g x)`; the dual side remains the same supremum problem
-- `y ↦ -f*(y) - g*(-y)`.
/-- Theorem 4.6 (1): Fenchel's duality. For proper convex extended-real-valued functions on a
finite-dimensional real normed space whose effective domains have intersecting relative interiors,
the source's displayed primal `min` is formalized here as the equality of optimal values
`sInf (Set.range fun x ↦ f x + g x) = fenchel_dual_problem_value f g`; equivalently, this is the
equality between the primal infimum of `f + g` and the supremum of
`y ↦ -f*(y) - g*(-y)`. -/
theorem fenchel_duality_value_eq (f g : E → EReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : IsProperExtendedRealFunction g)
    (hf_convex : is_convex_function f)
    (hg_convex : is_convex_function g)
    (hqual :
      (intrinsicInterior ℝ (effective_domain f) ∩
        intrinsicInterior ℝ (effective_domain g)).Nonempty) :
    sInf (Set.range fun x : E ↦ f x + g x) = fenchel_dual_problem_value f g := by
  have hf_ne_bot : ∀ x : E, f x ≠ ⊥ := hf_proper.ne_bot
  have hg_ne_bot : ∀ x : E, g x ≠ ⊥ := hg_proper.ne_bot
  have hψ_convex :
      is_convex_function (zeroCaseValue f g) :=
    zeroCaseValue_isConvex f g hf_ne_bot hg_ne_bot hf_convex hg_convex
  have hψ_ri :
      (0 : E) ∈ intrinsicInterior ℝ (effective_domain (zeroCaseValue f g)) :=
    zero_mem_intrinsicInterior_effectiveDomain_zeroCaseValue f g hf_ne_bot hg_ne_bot hqual
  rcases subdifferential_nonempty_at_relativeInterior_point
      (zeroCaseValue f g) (0 : E) hψ_convex hψ_ri with
    ⟨η, hη⟩
  have hlower :
      zeroCaseValue f g (0 : E) ≤ fenchel_dual_problem_value f g := by
    -- The perturbation subgradient at `0` yields one dual witness, hence a lower bound on the dual supremum.
    calc
      zeroCaseValue f g (0 : E) ≤ fenchel_dual_objective f g (-η) :=
        zeroCaseValue_le_fenchelDualObjective_of_mem_subdifferential_zero f g hf_proper hg_proper hη
      _ ≤ fenchel_dual_problem_value f g := by
        rw [fenchel_dual_problem_value_eq_sSup]
        exact le_sSup (Set.mem_range_self (-η))
  have hupper :
      fenchel_dual_problem_value f g ≤ zeroCaseValue f g (0 : E) :=
    fenchelDualProblemValue_le_zeroCaseValue_zero f g hf_proper hg_proper
  have hzero_eq :
      zeroCaseValue f g (0 : E) = fenchel_dual_problem_value f g :=
    le_antisymm hlower hupper
  -- Replace the perturbation value at `0` by the primal infimum.
  simpa [zeroCaseValue_zero_eq_primalValue] using hzero_eq

-- Proof sketch: under the same qualification, Fenchel--Rockafellar duality gives existence of a
-- dual maximizer whenever the dual problem value is a real number. Rephrase the attained maximum
-- as an `IsGreatest` statement for the range of `fenchel_dual_objective`.
/-- Theorem 4.6 (2): If Fenchel's dual problem value is finite, then the dual optimization
problem attains its maximum. -/
theorem exists_isGreatest_fenchel_dual_objective_of_finite_value (f g : E → EReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : IsProperExtendedRealFunction g)
    (hf_convex : is_convex_function f)
    (hg_convex : is_convex_function g)
    (hqual :
      (intrinsicInterior ℝ (effective_domain f) ∩
        intrinsicInterior ℝ (effective_domain g)).Nonempty)
    (hfinite : ∃ r : ℝ, fenchel_dual_problem_value f g = (r : EReal)) :
    ∃ y : Module.Dual ℝ E,
      IsGreatest (Set.range (fenchel_dual_objective f g)) (fenchel_dual_objective f g y) := by
  let _ := hfinite
  have hf_ne_bot : ∀ x : E, f x ≠ ⊥ := hf_proper.ne_bot
  have hg_ne_bot : ∀ x : E, g x ≠ ⊥ := hg_proper.ne_bot
  have hψ_convex :
      is_convex_function (zeroCaseValue f g) :=
    zeroCaseValue_isConvex f g hf_ne_bot hg_ne_bot hf_convex hg_convex
  have hψ_ri :
      (0 : E) ∈ intrinsicInterior ℝ (effective_domain (zeroCaseValue f g)) :=
    zero_mem_intrinsicInterior_effectiveDomain_zeroCaseValue f g hf_ne_bot hg_ne_bot hqual
  rcases subdifferential_nonempty_at_relativeInterior_point
      (zeroCaseValue f g) (0 : E) hψ_convex hψ_ri with
    ⟨η, hη⟩
  have hzero_eq :
      zeroCaseValue f g (0 : E) = fenchel_dual_problem_value f g := by
    -- Reuse the value theorem to identify the perturbation value at `0` with the dual supremum.
    simpa [zeroCaseValue_zero_eq_primalValue] using
      fenchel_duality_value_eq f g hf_proper hg_proper hf_convex hg_convex hqual
  have hdual_le_obj :
      fenchel_dual_problem_value f g ≤ fenchel_dual_objective f g (-η) := by
    -- The same perturbation subgradient produces a dual witness attaining the common optimal value.
    calc
      fenchel_dual_problem_value f g = zeroCaseValue f g (0 : E) := hzero_eq.symm
      _ ≤ fenchel_dual_objective f g (-η) :=
        zeroCaseValue_le_fenchelDualObjective_of_mem_subdifferential_zero f g hf_proper hg_proper hη
  have hobj_le_dual :
      fenchel_dual_objective f g (-η) ≤ fenchel_dual_problem_value f g := by
    rw [fenchel_dual_problem_value_eq_sSup]
    exact le_sSup (Set.mem_range_self (-η))
  have hattain :
      fenchel_dual_problem_value f g = fenchel_dual_objective f g (-η) :=
    le_antisymm hdual_le_obj hobj_le_dual
  refine ⟨-η, ?_⟩
  refine ⟨Set.mem_range_self (-η), ?_⟩
  intro w hw
  rcases hw with ⟨y, rfl⟩
  -- Every dual objective value is bounded above by the dual supremum, which this witness attains.
  calc
    fenchel_dual_objective f g y ≤ fenchel_dual_problem_value f g := by
      rw [fenchel_dual_problem_value_eq_sSup]
      exact le_sSup (Set.mem_range_self y)
    _ = fenchel_dual_objective f g (-η) := hattain

end
