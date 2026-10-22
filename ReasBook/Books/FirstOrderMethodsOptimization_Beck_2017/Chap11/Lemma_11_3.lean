/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped BigOperators Gradient

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]

variable [Fintype ι]

-- Proof sketch: let `x⁺ = x + 𝒰_i(T_M^i(x) - x_i)`. The block descent lemma gives the quadratic
-- upper bound on `f x⁺` because `x ∈ effective_domain (separableSum g)` implies
-- `x ∈ interior (effective_domain f)`, and the updated point stays in the effective domain of the
-- block-separable regularizer, hence also in `interior (effective_domain f)`. The second prox
-- theorem controls the linear term together with the change in `g i`, while the remaining block
-- penalties are unchanged. Finally rewrite the residual `M • (x_i - T_M^i(x))` as `G_M^i(x)`.

namespace IsBlockProximalGradientProblem

variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
variable {Li : (i : ι) → PosReal}

local notation "F" => composite_model_objective f (separableSum g)

/- Domain sampling for this refinement:
- `IsBlockProximalGradientProblem.prox_point` and `gradient_mapping` from `Definition_11_4` are
  the canonical owner-level one-block update and residual.
- `IsBlockProximalGradientProblem.block_coordinate_update_prox_point_mem_effective_domain` from
  `Definition_11_4` is the canonical owner-level domain-preservation bridge for that update.
- `BlockProximalGradientAssumptions` is the source-facing owner extending the core block-problem
  owner by the convexity data used in Lemma 11.3.
- `BlockProximalGradientAssumptions.block_coordinate_descent_lemma` from `Lemma_11_2` is the
  upstream one-block quadratic upper-model bridge.

Lemma 11.3 is `source-facing`: it proves the textbook sufficient-decrease inequality for one block.
Its best owner layer is still the Chapter 11 block-problem owner; the convexity and arbitrary
block-Lipschitz constant `M` remain theorem hypotheses rather than new packaged data. -/

omit [Fintype ι] in
/-- Helper for Lemma 11.3: convexity of `effective_domain f` makes the admissible one-block slice
domain convex. -/
theorem blockCoordinateSliceDomainConvexOfConvexEffectiveDomain
    {x : (j : ι) → Ei j} (i : ι)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f)) :
    Convex ℝ {d : Ei i | x + 𝒰[i] d ∈ interior (effective_domain f)} := by
  let hinterior : Convex ℝ (interior (effective_domain f)) :=
    hf_effective_domain_convex.interior
  intro d hd e he a b ha hb hab
  -- Push the ambient convexity through the affine one-block update map.
  have hcomb := hinterior hd he ha hb hab
  have hcomb' :
      a • (x + 𝒰[i] d) + b • (x + 𝒰[i] e) ∈ interior (effective_domain f) := by
    simpa using hcomb
  have hcomb'' :
      x + 𝒰[i] (a • d + b • e) ∈ interior (effective_domain f) := by
    classical
    have hcombo_eq :
        a • (x + 𝒰[i] d) + b • (x + 𝒰[i] e) =
          x + 𝒰[i] (a • d + b • e) := by
      ext j
      by_cases hji : j = i
      · subst j
        have hleft :
            (a • (x + 𝒰[i] d) + b • (x + 𝒰[i] e)) i =
              a • (x i + d) + b • (x i + e) := by
          simp
        have hx :
            a • x i + b • x i = x i := by
          simpa [hab] using (add_smul a b (x i)).symm
        have hmiddle :
            a • (x i + d) + b • (x i + e) = x i + (a • d + b • e) := by
          calc
            a • (x i + d) + b • (x i + e)
                = a • x i + a • d + (b • x i + b • e) := by
                    simp [smul_add, add_assoc, add_comm]
            _ = (a • x i + b • x i) + (a • d + b • e) := by
                  abel
            _ = x i + (a • d + b • e) := by
                  rw [hx]
        have hright :
            x i + (a • d + b • e) = (x + 𝒰[i] (a • d + b • e)) i := by
          simp
        exact hleft.trans (hmiddle.trans hright)
      · calc
          (a • (x + 𝒰[i] d) + b • (x + 𝒰[i] e)) j = a • x j + b • x j := by
            simp [Pi.single_eq_of_ne, hji]
          _ = (a + b) • x j := by
            rw [← add_smul]
          _ = x j := by
            rw [hab, one_smul]
          _ = (x + 𝒰[i] (a • d + b • e)) j := by
            simp [Pi.single_eq_of_ne, hji]
    rw [hcombo_eq] at hcomb'
    exact hcomb'
  simpa using hcomb''

/-- Helper for Lemma 11.3: the fixed-block Lipschitz hypothesis makes the frozen one-block slice
`M`-smooth on its admissible update domain. -/
theorem blockCoordinateSliceIsLSmoothOnOfBlockLipschitz
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (i : ι) [CompleteSpace (Ei i)] (M : PosReal) {x : (j : ι) → Ei j}
    (h_block_gradient_lipschitz :
      ∀ (x : (i : ι) → Ei i) (d : Ei i)
        (_ : x ∈ interior (effective_domain f))
        (_ : block_coordinate_update x i d ∈ interior (effective_domain f)),
          ‖block_gradient i x - block_gradient i (block_coordinate_update x i d)‖ ≤
            (M : ℝ) * ‖d‖) :
    is_l_smooth_on
      (block_coordinate_slice f x i)
      {d : Ei i | x + 𝒰[i] d ∈ interior (effective_domain f)}
      (PosReal.toNNReal M) := by
  rw [is_l_smooth_on_iff_forall_norm_sub_le]
  refine ⟨?_, ?_⟩
  · intro d hd
    -- The gradient of the recentered slice is the chosen block gradient at the updated point.
    exact (hproblem.block_coordinate_slice_hasGradientAt i hd).differentiableAt
  · intro d hd e he
    have hde :
        block_coordinate_update (block_coordinate_update x i d) i (e - d) =
          block_coordinate_update x i e := by
      classical
      ext j
      by_cases hji : j = i
      · subst j
        simp [block_coordinate_update, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      · simp [block_coordinate_update, hji]
    have he' :
        block_coordinate_update (block_coordinate_update x i d) i (e - d) ∈
          interior (effective_domain f) := by
      rw [hde]
      exact he
    have hlip :=
      h_block_gradient_lipschitz
        (block_coordinate_update x i d)
        (e - d)
        hd
        he'
    have hdgrad :
        HasGradientAt
          (block_coordinate_slice f x i)
          (block_gradient i (block_coordinate_update x i d))
          d :=
      hproblem.block_coordinate_slice_hasGradientAt i hd
    have hegrad :
        HasGradientAt
          (block_coordinate_slice f x i)
          (block_gradient i (block_coordinate_update x i e))
          e :=
      hproblem.block_coordinate_slice_hasGradientAt i he
    -- Rewrite the second updated state back to the direct update at `e`.
    simpa [hde, hdgrad.gradient, hegrad.gradient, norm_sub_rev] using hlip

/-- Helper for Lemma 11.3: proximal optimality for the selected block controls the smooth linear
term by the block-penalty gap and the negative quadratic residual. -/
theorem proxPointLinearTermLeToReal
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (i : ι) [ProperSpace (Ei i)] (M : PosReal)
    (x : effective_domain (separableSum g)) :
    let x' : (j : ι) → Ei j := x
    let xPlus := T[M; hproblem] x' i
    inner ℝ (block_gradient i x') (xPlus - x' i) ≤
      -(M : ℝ) * ‖xPlus - x' i‖ ^ (2 : ℕ) +
        (g i (x' i)).toReal - (g i xPlus).toReal := by
  let x' : (j : ι) → Ei j := x
  let xPlus := T[M; hproblem] x' i
  let z : Ei i := x' i - (1 / M : ℝ) • block_gradient i x'
  have hprox :
      prox[((((1 / M : PosReal) : EReal) • g i))] z = {xPlus} := by
    -- Expand the owner-level prox point back to the singleton proximal set.
    simpa [x', xPlus, z] using hproblem.prox_point_eq_singleton M i x'
  rcases scaled_prox_singleton_support_of_proper_convex
      (f := g i)
      (μ := 1 / M)
      (hproblem.block_g_proper i)
      (hproblem.block_g_convex i)
      z
      xPlus
      hprox with
    ⟨hxPlus_eff, hsupport⟩
  have hxi :
      x' i ∈ effective_domain (g i) :=
    block_mem_effective_domain_of_mem_separableSum_effective_domain
      g
      hproblem.block_g_proper
      x.2
      i
  have hx_val :
      g i (x' i) = (((g i (x' i)).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxi).ne
        ((hproblem.block_g_proper i).ne_bot _)).symm
  have hxPlus_val :
      g i xPlus = (((g i xPlus).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxPlus_eff).ne
        ((hproblem.block_g_proper i).ne_bot _)).symm
  have hsupport_real :
      inner ℝ ((1 / (1 / M : PosReal) : ℝ) • (z - xPlus)) (x' i - xPlus) ≤
        (g i (x' i)).toReal - (g i xPlus).toReal := by
    have hsupportE := hsupport (x' i) hxi
    rw [hx_val, hxPlus_val] at hsupportE
    have hsupportE' :
        (((inner ℝ ((1 / (1 / M : PosReal) : ℝ) • (z - xPlus)) (x' i - xPlus) : ℝ)) : EReal) ≤
          ((((g i (x' i)).toReal - (g i xPlus).toReal : ℝ)) : EReal) := by
      simpa [EReal.coe_sub] using hsupportE
    exact EReal.coe_le_coe_iff.mp hsupportE'
  have hM :
      (1 / (1 / M : PosReal) : ℝ) = (M : ℝ) := by
    simp
  have hleft :
      inner ℝ ((1 / (1 / M : PosReal) : ℝ) • (z - xPlus)) (x' i - xPlus) =
        (M : ℝ) * ‖x' i - xPlus‖ ^ (2 : ℕ) -
          inner ℝ (block_gradient i x') (x' i - xPlus) := by
    -- Expanding the forward point isolates the residual square and the linear gradient term.
    have hz_sub :
        z - xPlus = (x' i - xPlus) - (1 / M : ℝ) • block_gradient i x' := by
      dsimp [z]
      abel
    rw [hM, hz_sub, smul_sub, inner_sub_left]
    have hnorm :
        inner ℝ ((M : ℝ) • (x' i - xPlus)) (x' i - xPlus) =
          (M : ℝ) * ‖x' i - xPlus‖ ^ (2 : ℕ) := by
      calc
        inner ℝ ((M : ℝ) • (x' i - xPlus)) (x' i - xPlus) =
            (starRingEnd ℝ) (M : ℝ) * inner ℝ (x' i - xPlus) (x' i - xPlus) := by
          rw [inner_smul_left]
        _ = (M : ℝ) * ‖x' i - xPlus‖ ^ (2 : ℕ) := by
          simp
    have hgrad :
        inner ℝ ((M : ℝ) • ((1 / M : ℝ) • block_gradient i x')) (x' i - xPlus) =
          inner ℝ (block_gradient i x') (x' i - xPlus) := by
      rw [smul_smul]
      have hcancel : ((M : ℝ) * (1 / M : ℝ)) = 1 := by
        field_simp [show (M : ℝ) ≠ 0 by exact (PosReal.coe_pos M).ne']
      rw [hcancel, one_smul]
    rw [hnorm, hgrad]
  have haux :
      -inner ℝ (block_gradient i x') (x' i - xPlus) ≤
        -(M : ℝ) * ‖x' i - xPlus‖ ^ (2 : ℕ) +
          (g i (x' i)).toReal - (g i xPlus).toReal := by
    rw [hleft] at hsupport_real
    linarith
  have hdir :
      inner ℝ (block_gradient i x') (xPlus - x' i) =
        -inner ℝ (block_gradient i x') (x' i - xPlus) := by
    have hsub : xPlus - x' i = -(x' i - xPlus) := by
      abel
    rw [hsub, inner_neg_right]
  -- Replace the forward displacement by the negative residual and use norm symmetry.
  simpa [x', xPlus, hdir, norm_sub_rev] using haux

/-- Helper for Lemma 11.3: at any finite point of the block-separable regularizer, the value is
the coerced real sum of its blockwise finite values. -/
theorem separableSumEqCoeToRealSum
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    {x : (i : ι) → Ei i} (hx : x ∈ effective_domain (separableSum g)) :
    separableSum g x = ((((∑ j, (g j (x j)).toReal : ℝ)) : ℝ) : EReal) := by
  have hxj : ∀ j, x j ∈ effective_domain (g j) := by
    intro j
    exact
      block_mem_effective_domain_of_mem_separableSum_effective_domain
        g
        hproblem.block_g_proper
        hx
        j
  rw [separableSum_apply]
  calc
    ∑ j, g j (x j) = ∑ j, ((((g j (x j)).toReal : ℝ) : EReal)) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      exact
        (EReal.coe_toReal (mem_effective_domain.mp (hxj j)).ne
          ((hproblem.block_g_proper j).ne_bot _)).symm
    _ = ((((∑ j, (g j (x j)).toReal : ℝ)) : ℝ) : EReal) := by
      classical
      have hsum_coe :
          ∀ s : Finset ι,
            Finset.sum s (fun j ↦ (((g j (x j)).toReal : ℝ) : EReal)) =
              ((Finset.sum s fun j ↦ (g j (x j)).toReal : ℝ) : EReal) := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
            simp
        | @insert a s ha ih =>
            simp [Finset.sum_insert, ha, ih, EReal.coe_add]
      simpa using hsum_coe (Finset.univ : Finset ι)

/-- Helper for Lemma 11.3: a real inequality involving the active block and the smooth term at
the updated point upgrades to the corresponding `EReal` inequality for the full composite
objective. -/
theorem fullObjectiveSufficientDecreaseOfActiveRealInequality
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    {i : ι} {x : (j : ι) → Ei j} {yi : Ei i} {c : ℝ}
    (hxg : x ∈ effective_domain (separableSum g))
    (hyg : block_coordinate_update x i (yi - x i) ∈ effective_domain (separableSum g))
    (hx : x ∈ interior (effective_domain f))
    (hy : block_coordinate_update x i (yi - x i) ∈ interior (effective_domain f))
    (hreal :
      c + (f (block_coordinate_update x i (yi - x i))).toReal + (g i yi).toReal ≤
        (f x).toReal + (g i (x i)).toReal) :
    (((c : ℝ) : EReal)) + F (block_coordinate_update x i (yi - x i)) ≤ F x := by
  classical
  let y := block_coordinate_update x i (yi - x i)
  have hsum_x :
      separableSum g x = ((((∑ j, (g j (x j)).toReal : ℝ)) : ℝ) : EReal) :=
    hproblem.separableSumEqCoeToRealSum hxg
  have hsum_y :
      separableSum g y = ((((∑ j, (g j (y j)).toReal : ℝ)) : ℝ) : EReal) :=
    hproblem.separableSumEqCoeToRealSum hyg
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
            exact
              Finset.add_sum_erase
                Finset.univ
                (fun j ↦ (g j (y j)).toReal)
                (Finset.mem_univ i)
      _ = (g i yi).toReal +
            Finset.sum (Finset.univ.erase i) (fun j ↦ (g j (x j)).toReal) := by
        congr 1
        · simp [y, block_coordinate_update, sub_eq_add_neg, add_left_comm]
        · refine Finset.sum_congr rfl ?_
          intro j hj
          have hji : j ≠ i := (Finset.mem_erase.mp hj).1
          simp [y, block_coordinate_update_apply_ne, hji]
  have hreal_full :
      c + ((f y).toReal + (∑ j, (g j (y j)).toReal)) ≤
        (f x).toReal + (∑ j, (g j (x j)).toReal) := by
    rw [hsum_x_split, hsum_y_split]
    linarith
  have hfx_val :
      f x = (((f x).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp (interior_subset hx)).ne
        (hproblem.f_ne_bot x)).symm
  have hfy_val :
      f y = (((f y).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp (interior_subset hy)).ne
        (hproblem.f_ne_bot y)).symm
  have hF_x :
      F x = ((((f x).toReal + (∑ j, (g j (x j)).toReal) : ℝ)) : EReal) := by
    rw [composite_model_objective_apply, hfx_val, hsum_x]
    simp [EReal.coe_add]
  have hF_y :
      F y = ((((f y).toReal + (∑ j, (g j (y j)).toReal) : ℝ)) : EReal) := by
    rw [composite_model_objective_apply, hfy_val, hsum_y]
    simp [EReal.coe_add]
  have hreal_fullE :
      ((((c + ((f y).toReal + (∑ j, (g j (y j)).toReal)) : ℝ)) : EReal)) ≤
        ((((f x).toReal + (∑ j, (g j (x j)).toReal) : ℝ)) : EReal) :=
    EReal.coe_le_coe hreal_full
  rw [hF_x, hF_y]
  simpa [EReal.coe_add, add_assoc] using hreal_fullE

/-- Lemma 11.3: if the `i`-th block partial gradient is `M`-Lipschitz along block updates and
the block-separable effective domain lies in `interior (effective_domain f)`, then replacing the
`i`-th block by its one-block proximal-gradient update decreases the composite objective by at
least `(1 / (2 M)) ‖G_M^i(x)‖^2`. -/
theorem block_partial_gradient_sufficient_decrease_of_block_lipschitz
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (i : ι) [ProperSpace (Ei i)] (M : PosReal)
    (h_block_gradient_lipschitz :
      ∀ (x : (i : ι) → Ei i) (d : Ei i)
        (_ : x ∈ interior (effective_domain f))
        (_ : block_coordinate_update x i d ∈ interior (effective_domain f)),
          ‖block_gradient i x - block_gradient i (block_coordinate_update x i d)‖ ≤
            (M : ℝ) * ‖d‖)
    (x : effective_domain (separableSum g)) :
    let x' : (j : ι) → Ei j := x
    let xPlus := block_coordinate_update x' i (T[M; hproblem] x' i - x' i)
    F x' - F xPlus ≥
      ((((1 : ℝ) / (2 * (M : ℝ))) *
          ‖G[M; hproblem] x' i‖ ^ (2 : ℕ) : ℝ) : EReal) :=
  by
    let x' : (j : ι) → Ei j := x
    let xiPlus := T[M; hproblem] x' i
    let xPlus := block_coordinate_update x' i (xiPlus - x' i)
    have hx :
        x' ∈ interior (effective_domain f) :=
      hproblem.mem_interior_effective_domain_of_mem_g_effective_domain x.2
    have hxPlus_eff :
        xPlus ∈ effective_domain (separableSum g) := by
      -- The one-block prox update preserves the effective domain of the block-separable penalty.
      simpa [x', xiPlus, xPlus] using
        hproblem.block_coordinate_update_prox_point_mem_effective_domain M x i
    have hxPlus :
        xPlus ∈ interior (effective_domain f) :=
      hproblem.mem_interior_effective_domain_of_mem_g_effective_domain hxPlus_eff
    have hdescent :
        (f xPlus).toReal ≤
          (f x').toReal + inner ℝ (block_gradient i x') (xiPlus - x' i) +
            ((M : ℝ) / 2) * ‖xiPlus - x' i‖ ^ (2 : ℕ) := by
      -- The slice descent lemma gives the quadratic upper model along the chosen block update.
      simpa [x', xiPlus, xPlus, block_coordinate_update] using
        block_coordinate_descent_lemma_of_slice_smooth
          f
          block_gradient
          (PosReal.toNNReal M)
          i
          (blockCoordinateSliceDomainConvexOfConvexEffectiveDomain
            (f := f)
            (i := i)
            hf_effective_domain_convex)
          (blockCoordinateSliceIsLSmoothOnOfBlockLipschitz
            (hproblem := hproblem)
            (i := i)
            (M := M)
            (x := x')
            h_block_gradient_lipschitz)
          (hproblem.block_partial_gradient_hasGradientAt i hx)
          hx
          hxPlus
    have hprox :
        inner ℝ (block_gradient i x') (xiPlus - x' i) ≤
          -(M : ℝ) * ‖xiPlus - x' i‖ ^ (2 : ℕ) +
            (g i (x' i)).toReal - (g i xiPlus).toReal := by
      -- Proximal optimality contributes the block-penalty gap and the negative quadratic term.
      simpa [x', xiPlus] using hproblem.proxPointLinearTermLeToReal i M x
    have hreal_active :
        ((M : ℝ) / 2) * ‖xiPlus - x' i‖ ^ (2 : ℕ) +
            (f xPlus).toReal + (g i xiPlus).toReal ≤
          (f x').toReal + (g i (x' i)).toReal := by
      linarith
    have hbridge :
        ((((M : ℝ) / 2) * ‖xiPlus - x' i‖ ^ (2 : ℕ) : ℝ) : EReal) + F xPlus ≤
          F x' := by
      -- Convert the real active-block inequality into the corresponding `EReal` objective bound.
      simpa [x', xiPlus, xPlus] using
        hproblem.fullObjectiveSufficientDecreaseOfActiveRealInequality
          (i := i)
          (x := x')
          (yi := xiPlus)
          (c := ((M : ℝ) / 2) * ‖xiPlus - x' i‖ ^ (2 : ℕ))
          x.2
          hxPlus_eff
          hx
          hxPlus
          hreal_active
    have hF_xPlus_ne_bot : F xPlus ≠ ⊥ := by
      have hsum_ne_bot : separableSum g xPlus ≠ ⊥ :=
        (separableSum_proper g hproblem.block_g_proper).ne_bot xPlus
      rw [composite_model_objective_apply, EReal.add_ne_bot_iff]
      exact ⟨hproblem.f_ne_bot xPlus, hsum_ne_bot⟩
    have hF_xPlus_ne_top : F xPlus ≠ ⊤ := by
      rw [composite_model_objective_apply]
      exact
        EReal.add_ne_top
          (mem_effective_domain.mp (interior_subset hxPlus)).ne
          (mem_effective_domain.mp hxPlus_eff).ne
    have hstep_decrease :
        ((((M : ℝ) / 2) * ‖xiPlus - x' i‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
          F x' - F xPlus := by
      exact
        (EReal.le_sub_iff_add_le (Or.inl hF_xPlus_ne_bot) (Or.inl hF_xPlus_ne_top)).2
          hbridge
    have hcoeff :
        ((((1 : ℝ) / (2 * (M : ℝ))) * ‖G[M; hproblem] x' i‖ ^ (2 : ℕ) : ℝ) : EReal) =
          ((((M : ℝ) / 2) * ‖xiPlus - x' i‖ ^ (2 : ℕ) : ℝ) : EReal) := by
      have hcoeff_real :
          (((1 : ℝ) / (2 * (M : ℝ))) * ‖G[M; hproblem] x' i‖ ^ (2 : ℕ) : ℝ) =
            (((M : ℝ) / 2) * ‖xiPlus - x' i‖ ^ (2 : ℕ) : ℝ) := by
        have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt M.2
        have hGdef :
            G[M; hproblem] x' i = (M : ℝ) • (x' i - xiPlus) := by
          have hgrad := hproblem.gradient_mapping_def M x' i
          dsimp [xiPlus] at hgrad
          exact hgrad
        rw [hGdef]
        rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ (M : ℝ) by exact le_of_lt M.2),
          norm_sub_rev, pow_two, pow_two]
        field_simp [hM_ne]
      simpa using congrArg (fun r : ℝ ↦ (r : EReal)) hcoeff_real
    rw [← hcoeff] at hstep_decrease
    simpa [x', xPlus, xiPlus] using hstep_decrease

end IsBlockProximalGradientProblem

namespace BlockProximalGradientAssumptions

variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : ι) → PosReal}

local notation "F" => composite_model_objective f (separableSum g)

/-- Under the Chapter 11 owner assumptions, the textbook one-block update with stepsize `L_i`
satisfies the sufficient-decrease estimate from Lemma 11.3. -/
theorem block_partial_gradient_sufficient_decrease
    (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (i : ι) [ProperSpace (Ei i)] (x : effective_domain (separableSum g)) :
    let hcore : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li :=
      hproblem.toIsBlockProximalGradientProblem;
    let x' : (j : ι) → Ei j := x
    let xPlus := block_coordinate_update x' i (T[Li i; hcore] x' i - x' i)
    F x' - F xPlus ≥
      ((((1 : ℝ) / (2 * (Li i : ℝ))) *
          ‖G[Li i; hcore] x' i‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  let hcore : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li :=
    hproblem.toIsBlockProximalGradientProblem
  -- Specialize the owner theorem above to the standing block-Lipschitz constant `L_i`.
  simpa [hcore] using
    IsBlockProximalGradientProblem.block_partial_gradient_sufficient_decrease_of_block_lipschitz
      (hproblem := hcore)
      (hf_effective_domain_convex := hproblem.f_effective_domain_convex)
      (i := i)
      (M := Li i)
      (h_block_gradient_lipschitz := fun x d hx hxd ↦
        by simpa using hproblem.block_partial_gradient_lipschitz i hx hxd)
      x

end BlockProximalGradientAssumptions

end
