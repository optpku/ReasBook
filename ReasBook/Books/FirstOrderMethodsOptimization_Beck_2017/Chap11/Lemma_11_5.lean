/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_4
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_2
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Theorem_11_2
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_42

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

open scoped BigOperators Gradient

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable [Nonempty (Fin p)]

variable {Li : (i : Fin p) → PosReal}

/-- The constant `C` from equation (11.13) in the version-II sufficient-decrease estimate for the
cyclic block proximal-gradient method. -/
def cbpg_sufficient_decrease_constant (Lf : NNReal) (Li : (i : Fin p) → PosReal) : ℝ :=
  ((cbpg_min_block_stepsize Li : PosReal) : ℝ) /
    (2 *
      (((Lf : ℝ) + 2 * ((cbpg_max_block_stepsize Li : PosReal) : ℝ) +
            Real.sqrt
              (((cbpg_min_block_stepsize Li : PosReal) : ℝ) *
                ((cbpg_max_block_stepsize Li : PosReal) : ℝ))) ^
        (2 : ℕ)))

/-- Expanding `cbpg_sufficient_decrease_constant` yields the textbook coefficient
`L_min / (2 (L_f + 2 L_max + sqrt (L_min L_max))^2)` with the canonical finite-step owners
`L_min = cbpg_min_block_stepsize Li` and `L_max = cbpg_max_block_stepsize Li`. -/
@[simp] theorem cbpg_sufficient_decrease_constant_def
    (Lf : NNReal) (Li : (i : Fin p) → PosReal) :
    cbpg_sufficient_decrease_constant Lf Li =
      ((cbpg_min_block_stepsize Li : PosReal) : ℝ) /
        (2 *
          (((Lf : ℝ) + 2 * ((cbpg_max_block_stepsize Li : PosReal) : ℝ) +
                Real.sqrt
                  (((cbpg_min_block_stepsize Li : PosReal) : ℝ) *
                    ((cbpg_max_block_stepsize Li : PosReal) : ℝ))) ^
            (2 : ℕ))) :=
  rfl

end

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable [Nonempty (Fin p)]
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}
variable {block_gradient : (i : Fin p) → ((j : Fin p) → Ei j) → Ei i}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : Fin p) → PosReal}

variable (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
variable (x0 : effective_domain (separableSum g))

local notation "hcore" => hproblem.toIsBlockProximalGradientProblem
local notation "x0I" => hproblem.interior_effective_domain_point x0
local notation "x[" k "]" => cyclic_block_proximal_gradient_method hproblem x0I k
local notation "x[" k "," m "]" => cyclic_block_proximal_gradient_inner_iterate hproblem x[k] m
local notation "F" => composite_model_objective f (separableSum g)
local notation "Lmin" => cbpg_min_block_stepsize Li
local notation "Lmax" => cbpg_max_block_stepsize Li
local notation "Gcbpg[" k "]" => fun i ↦ G[Lmin; hcore] x[k] i
local notation "toPiLp" =>
  ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)

local instance : DecidableEq (Fin p) := Classical.decEq _

omit [Nonempty (Fin p)] [∀ i, ProperSpace (Ei i)] in
/-- Helper for Lemma 11.5: the raw product sup norm is bounded by the canonical `PiLp` `L²`
norm after transporting along `toPiLp`. -/
lemma raw_ambient_norm_le_toPiLp_norm
    (v : (i : Fin p) → Ei i) :
    ‖v‖ ≤ ‖toPiLp v‖ := by
  -- Rewrite the raw product norm as the finite supremum of the coordinate norms.
  suffices hnn : ‖v‖₊ ≤ ‖toPiLp v‖₊ by
    exact_mod_cast hnn
  rw [Pi.nnnorm_def]
  refine Finset.sup_le ?_
  intro i hi
  have hi_norm :
      ‖v i‖ ≤ ‖toPiLp v‖ := by
    simpa [PiLp.coe_symm_continuousLinearEquiv] using
      (PiLp.norm_apply_le (toPiLp v) i)
  exact_mod_cast hi_norm

omit [Nonempty (Fin p)] in
/-- Helper for Lemma 11.5: restricting the ambient Fréchet derivative of `x ↦ (f x).toReal` to
the `j`-th singleton block direction recovers the dual map of the Chapter 11 block gradient. -/
lemma fderiv_comp_single_eq_block_toDual
    (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (j : Fin p)
    (x : (i : Fin p) → Ei i)
    (hx : x ∈ interior (effective_domain f)) :
    (fderiv ℝ (fun y : (i : Fin p) → Ei i ↦ (f y).toReal) x).comp
        (ContinuousLinearMap.single ℝ Ei j) =
      InnerProductSpace.toDualMap ℝ (Ei j) (block_gradient j x) := by
  have hblock :
      HasGradientAt (block_coordinate_slice f x j) (block_gradient j x) 0 :=
    hproblem.toIsBlockProximalGradientProblem.block_partial_gradient_hasGradientAt j hx
  have htranslated :
      HasFDerivAt
        (fun y : Ei j ↦ (f (block_coordinate_update x j (y - x j))).toReal)
        (InnerProductSpace.toDualMap ℝ (Ei j) (block_gradient j x))
        (x j) := by
    -- Translate the primitive block-slice derivative from displacement `0` to the coordinate.
    simpa [block_coordinate_slice_apply] using
      (translated_block_coordinate_slice_hasGradientAt
        (i := j)
        (x := x)
        hblock).hasFDerivAt
  have hdiffAt :
      DifferentiableAt ℝ (fun y : (i : Fin p) → Ei i ↦ (f y).toReal) x := by
    have hdiffOn := hproblem.f_toReal_differentiableOn_interior_effective_domain
    exact (hdiffOn x hx).differentiableAt (isOpen_interior.mem_nhds hx)
  have hsingle :
      HasFDerivAt
        (fun y : Ei j ↦ Pi.single j y)
        (ContinuousLinearMap.single ℝ Ei j)
        (x j - x j) := by
    simpa using (ContinuousLinearMap.single ℝ Ei j).hasFDerivAt
  have hsub :
      HasFDerivAt
        (fun y : Ei j ↦ y - x j)
        (ContinuousLinearMap.id ℝ (Ei j))
        (x j) := by
    simpa using (HasFDerivAt.sub_const (x j) (hasFDerivAt_id (x j)))
  have hupdate :
      HasFDerivAt
        (fun y : Ei j ↦ block_coordinate_update x j (y - x j))
        (ContinuousLinearMap.single ℝ Ei j)
        (x j) := by
    -- The affine block update differentiates to the singleton insertion.
    simpa [block_coordinate_update] using
      (HasFDerivAt.comp
        (f := fun y : Ei j ↦ y - x j)
        (g := fun z : Ei j ↦ Pi.single j z)
        (x := x j)
        hsingle
        hsub).const_add x
  have hambient :
      HasFDerivAt
        (fun y : (i : Fin p) → Ei i ↦ (f y).toReal)
        (fderiv ℝ (fun y : (i : Fin p) → Ei i ↦ (f y).toReal) x)
        (block_coordinate_update x j (x j - x j)) := by
    simpa [block_coordinate_update] using hdiffAt.hasFDerivAt
  have hcomp :
      HasFDerivAt
        (fun y : Ei j ↦ (f (block_coordinate_update x j (y - x j))).toReal)
        ((fderiv ℝ (fun y : (i : Fin p) → Ei i ↦ (f y).toReal) x).comp
          (ContinuousLinearMap.single ℝ Ei j))
        (x j) := by
    -- Compose the ambient derivative with the singleton block insertion derivative.
    simpa [Function.comp] using
      hambient.comp (x j) hupdate
  exact hcomp.unique htranslated

omit [Nonempty (Fin p)] in
/-- Helper for Lemma 11.5: on `interior (effective_domain f)`, each block gradient is
`Lf`-Lipschitz with respect to the canonical block `L²` norm transported by `toPiLp`. -/
lemma cbpg_block_gradient_difference_le_lf_mul_toPiLp_norm
    (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (j : Fin p)
    (x y : (i : Fin p) → Ei i)
    (hx : x ∈ interior (effective_domain f))
    (hy : y ∈ interior (effective_domain f)) :
    ‖block_gradient j x - block_gradient j y‖ ≤
      (Lf : ℝ) * ‖toPiLp x - toPiLp y‖ := by
  have hambient :
      ‖fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) x -
          fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) y‖ ≤
        (Lf : ℝ) * ‖x - y‖ := by
    exact (is_l_smooth_on_iff.mp hproblem.f_toReal_smooth_on_interior_effective_domain).2 x hx y hy
  have hcoord :
      ‖block_gradient j x - block_gradient j y‖ ≤
        ‖fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) x -
            fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) y‖ := by
    have hcomp :
        ‖((fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) x -
              fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) y).comp
            (ContinuousLinearMap.single ℝ Ei j))‖ ≤
          ‖fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) x -
              fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) y‖ := by
      calc
        ‖((fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) x -
              fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) y).comp
            (ContinuousLinearMap.single ℝ Ei j))‖ ≤
            ‖fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) x -
                fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) y‖ *
              ‖ContinuousLinearMap.single ℝ Ei j‖ := by
          exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) x -
              fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) y‖ := by
          have hsingle_norm :
              ‖ContinuousLinearMap.single ℝ Ei j‖ ≤ (1 : ℝ) :=
            ContinuousLinearMap.norm_single_le_one (𝕜 := ℝ) (E := Ei) j
          nlinarith [norm_nonneg
            (fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) x -
              fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) y)]
    have hdual :
        ((fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) x -
            fderiv ℝ (fun z : (i : Fin p) → Ei i ↦ (f z).toReal) y).comp
          (ContinuousLinearMap.single ℝ Ei j)) =
          InnerProductSpace.toDualMap ℝ (Ei j) (block_gradient j x - block_gradient j y) := by
      ext d
      simp [fderiv_comp_single_eq_block_toDual (hproblem := hproblem) (j := j) (x := x) hx,
        fderiv_comp_single_eq_block_toDual (hproblem := hproblem) (j := j) (x := y) hy,
        InnerProductSpace.toDualMap_apply_apply]
    have hnorm :
        ‖InnerProductSpace.toDualMap ℝ (Ei j) (block_gradient j x - block_gradient j y)‖ =
          ‖block_gradient j x - block_gradient j y‖ := by
      simpa using
        (InnerProductSpace.toDual ℝ (Ei j)).norm_map
          (block_gradient j x - block_gradient j y)
    rw [← hnorm, ← hdual]
    exact hcomp
  have hraw :
      ‖x - y‖ ≤ ‖toPiLp x - toPiLp y‖ := by
    -- Compare the raw ambient norm with the canonical `PiLp` norm only once at the end.
    simpa [map_sub] using raw_ambient_norm_le_toPiLp_norm (v := x - y)
  have hLf_nonneg : 0 ≤ (Lf : ℝ) := by
    exact_mod_cast Lf.2
  exact hcoord.trans <|
    hambient.trans <|
      mul_le_mul_of_nonneg_left hraw hLf_nonneg

omit [Nonempty (Fin p)] in
/-- Helper for Lemma 11.5: before the cyclic method reaches block `j`, the `j`-th coordinate of
the auxiliary iterate still agrees with the outer iterate. -/
lemma cbpg_auxiliary_iterate_apply_eq_outer_iterate
    (k m : ℕ) (j : Fin p) (hj : m ≤ j.1) :
    x[k, m] j = x[k] j := by
  induction m with
  | zero =>
      -- The initial auxiliary stage is the current outer iterate itself.
      simp
  | succ m ihm =>
      have hm_lt_j : m < j.1 := Nat.lt_of_succ_le hj
      have hm_lt_p : m < p := lt_of_lt_of_le hm_lt_j (Nat.le_of_lt j.2)
      have hsucc :
          x[k, m + 1] =
            block_coordinate_update
              x[k, m]
              ⟨m, hm_lt_p⟩
              (hproblem.toIsBlockProximalGradientProblem.prox_point
                (Li ⟨m, hm_lt_p⟩)
                ⟨m, hm_lt_p⟩
                x[k, m] -
                x[k, m] ⟨m, hm_lt_p⟩) := by
        -- The successor auxiliary stage updates only the active block `⟨m, hm_lt_p⟩`.
        simpa [block_coordinate_update] using
          (cyclic_block_proximal_gradient_method_inner_succ hproblem x0I k hm_lt_p)
      have hne : (⟨m, hm_lt_p⟩ : Fin p) ≠ j := by
        intro hEq
        exact (Nat.ne_of_lt hm_lt_j) (congrArg Fin.val hEq)
      -- Since the updated block is still strictly before `j`, coordinate `j` is unchanged.
      rw [hsucc]
      simpa [block_coordinate_update, hne] using ihm (Nat.le_of_lt hm_lt_j)

omit [Nonempty (Fin p)] in
/-- Helper for Lemma 11.5: once the cyclic method has updated block `j`, every later auxiliary
stage keeps the `j`-th coordinate equal to the outer successor. -/
lemma cbpg_auxiliary_iterate_apply_eq_outer_successor_of_lt
    (k m : ℕ) (j : Fin p) (hj : j.1 < m) (hm : m ≤ p) :
    x[k, m] j = x[k + 1] j := by
  have hsuffix :
      ∀ r : ℕ, j.1 + 1 + r ≤ p →
        x[k, j.1 + 1 + r] j = x[k, j.1 + 1] j := by
    intro r hr
    induction r with
    | zero =>
        -- The suffix of length zero is exactly the stage right after block `j` is updated.
        simp
    | succ r ihr =>
        have hstage_lt : j.1 + 1 + r < p := Nat.lt_of_succ_le hr
        let jr : Fin p := ⟨j.1 + 1 + r, hstage_lt⟩
        have hsucc :
            x[k, j.1 + 1 + r + 1] =
              block_coordinate_update
                x[k, j.1 + 1 + r]
                jr
                (hproblem.toIsBlockProximalGradientProblem.prox_point
                    (Li jr) jr x[k, j.1 + 1 + r] -
                  x[k, j.1 + 1 + r] jr) := by
          -- Every later auxiliary step updates only its active block `jr`.
          simpa [jr, block_coordinate_update] using
            cyclic_block_proximal_gradient_method_inner_succ hproblem x0I k hstage_lt
        have hne : j ≠ jr := by
          intro hEq
          have hval : j.1 = j.1 + 1 + r := by
            simpa [jr] using congrArg Fin.val hEq
          have hlt : j.1 < j.1 + 1 + r := by
            exact lt_of_lt_of_le (Nat.lt_succ_self j.1) (Nat.le_add_right _ _)
          exact (Nat.ne_of_lt hlt) hval
        -- Route correction: after block `j` is updated, later block updates are all at indices
        -- strictly larger than `j`, so coordinate `j` stays fixed along the suffix.
        calc
          x[k, j.1 + 1 + (r + 1)] j =
              block_coordinate_update
                x[k, j.1 + 1 + r]
                jr
                (hproblem.toIsBlockProximalGradientProblem.prox_point
                    (Li jr) jr x[k, j.1 + 1 + r] -
                  x[k, j.1 + 1 + r] jr) j := by
            simpa [Nat.add_assoc] using congrArg (fun z : (i : Fin p) → Ei i ↦ z j) hsucc
          _ = x[k, j.1 + 1 + r] j := by
            simp [block_coordinate_update_apply_ne, hne]
          _ = x[k, j.1 + 1] j := by
            exact ihr (Nat.le_of_succ_le hr)
  have hj_succ : j.1 + 1 ≤ m := Nat.succ_le_of_lt hj
  let r : ℕ := m - (j.1 + 1)
  have hr : j.1 + 1 + r = m := by
    dsimp [r]
    exact Nat.add_sub_of_le hj_succ
  have hstable :
      x[k, p] j = x[k, j.1 + 1] j := by
    let rp : ℕ := p - (j.1 + 1)
    have hrp : j.1 + 1 + rp = p := by
      dsimp [rp]
      exact Nat.add_sub_of_le (Nat.succ_le_of_lt j.2)
    have hsuffix_rp : x[k, j.1 + 1 + rp] j = x[k, j.1 + 1] j := by
      exact hsuffix rp (by simp [hrp])
    simpa [rp, hrp] using hsuffix_rp
  calc
    x[k, m] j = x[k, j.1 + 1] j := by
      simpa [r, hr] using hsuffix r (by simpa [hr] using hm)
    _ = x[k, p] j := by
      exact hstable.symm
    _ = x[k + 1] j := by
      rw [cyclic_block_proximal_gradient_method_succ]

omit [Nonempty (Fin p)] in
/-- Helper for Lemma 11.5: the prefix displacement accumulated before stage `m` is coordinatewise
a truncation of the full outer-step displacement, so its transported `PiLp` norm is no larger. -/
lemma cbpg_prefix_displacement_toPiLp_le_outer_step
    (k m : ℕ) (hm : m ≤ p) :
    ‖toPiLp x[k] - toPiLp x[k, m]‖ ≤ ‖toPiLp x[k] - toPiLp x[k + 1]‖ := by
  have hsq :
      ‖toPiLp x[k] - toPiLp x[k, m]‖ ^ (2 : ℕ) ≤
        ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) := by
    -- Rewrite both squared `PiLp` norms as sums of squared block-coordinate norms.
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum ?_
    intro i hi
    by_cases him : m ≤ i.1
    · have hcoord :
          x[k, m] i = x[k] i :=
        cbpg_auxiliary_iterate_apply_eq_outer_iterate hproblem x0 k m i him
      -- If block `i` has not been visited yet, the prefix displacement vanishes in that coordinate.
      simp [hcoord]
    · have him_lt : i.1 < m := Nat.lt_of_not_ge him
      have hcoord :
          x[k, m] i = x[k + 1] i :=
        cbpg_auxiliary_iterate_apply_eq_outer_successor_of_lt hproblem x0 k m i him_lt hm
      -- If block `i` has already been visited, the prefix displacement matches the full outer step.
      simp [hcoord]
  -- Nonnegativity of norms lets us pass from the squared inequality back to the norm inequality.
  nlinarith [hsq, norm_nonneg (toPiLp x[k] - toPiLp x[k, m]),
    norm_nonneg (toPiLp x[k] - toPiLp x[k + 1])]

omit [Nonempty (Fin p)] in
/-- Helper for Lemma 11.5: if two points agree in the active block `j`, then the corresponding
same-stepsize partial gradient mappings differ by at most the block-gradient drift. -/
lemma cbpg_partial_gradient_mapping_difference_le_block_gradient_difference_of_eq_coord
    (M : PosReal) (j : Fin p)
    (x y : (i : Fin p) → Ei i)
    (hxy : x j = y j) :
    ‖G[M; hcore] x j - G[M; hcore] y j‖ ≤ ‖block_gradient j x - block_gradient j y‖ := by
  let zx : Ei j := x j - (1 / (M : ℝ)) • block_gradient j x
  let zy : Ei j := y j - (1 / (M : ℝ)) • block_gradient j y
  let ux : Ei j := hproblem.toIsBlockProximalGradientProblem.prox_point M j x
  let uy : Ei j := hproblem.toIsBlockProximalGradientProblem.prox_point M j y
  have hscaled :=
    scaled_function_proper_closed_convex_of_pos
      (g j)
      (hproblem.block_g_proper j)
      (hproblem.block_g_closed j)
      (hproblem.block_g_convex j)
      (1 / M)
  have hprox_x :
      prox[((((1 / M : PosReal) : EReal) • g j))] zx = {ux} := by
    -- The owner-level prox point at `x` is the singleton proximal point of the frozen block model.
    simpa [zx, ux] using
      hproblem.toIsBlockProximalGradientProblem.prox_point_eq_singleton M j x
  have hprox_y :
      prox[((((1 / M : PosReal) : EReal) • g j))] zy = {uy} := by
    -- The same singleton description holds for the frozen block model based at `y`.
    simpa [zy, uy] using
      hproblem.toIsBlockProximalGradientProblem.prox_point_eq_singleton M j y
  have hprox_nonexp :
      ‖ux - uy‖ ≤ ‖zx - zy‖ := by
    -- Apply proximal nonexpansiveness to the common scaled block penalty.
    exact
      prox_eq_singleton_nonexpansive
        (f := (((1 / M : PosReal) : EReal) • g j))
        zx
        zy
        ux
        uy
        hscaled.1
        hscaled.2.1
        hscaled.2.2
        hprox_x
        hprox_y
  have hgrad_map :
      G[M; hcore] x j - G[M; hcore] y j = (M : ℝ) • (uy - ux) := by
    -- Expand both residuals and cancel the shared block value `x j = y j`.
    calc
      G[M; hcore] x j - G[M; hcore] y j =
          (M : ℝ) • (x j - ux) - (M : ℝ) • (y j - uy) := by
        rw [hproblem.toIsBlockProximalGradientProblem.gradient_mapping_def M x j,
          hproblem.toIsBlockProximalGradientProblem.gradient_mapping_def M y j]
      _ = (M : ℝ) • ((x j - ux) - (y j - uy)) := by
        rw [← smul_sub]
      _ = (M : ℝ) • (uy - ux) := by
        rw [hxy]
        congr 1
        abel_nf
  have hz :
      zx - zy = -((1 / (M : ℝ)) • (block_gradient j x - block_gradient j y)) := by
    -- The forward points differ only through the block-gradient drift because the active block
    -- coordinate is shared.
    dsimp [zx, zy]
    rw [hxy]
    rw [smul_sub]
    abel_nf
  have hM_nonneg : 0 ≤ (M : ℝ) := le_of_lt M.2
  have hMinv_nonneg : 0 ≤ (1 / (M : ℝ)) := by positivity
  have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt M.2
  calc
    ‖G[M; hcore] x j - G[M; hcore] y j‖ = ‖(M : ℝ) • (uy - ux)‖ := by
      rw [hgrad_map]
    _ = (M : ℝ) * ‖uy - ux‖ := by
      rw [norm_smul, Real.norm_of_nonneg hM_nonneg]
    _ = (M : ℝ) * ‖ux - uy‖ := by
      rw [norm_sub_rev]
    _ ≤ (M : ℝ) * ‖zx - zy‖ := by
      exact mul_le_mul_of_nonneg_left hprox_nonexp hM_nonneg
    _ = (M : ℝ) * ((1 / (M : ℝ)) * ‖block_gradient j x - block_gradient j y‖) := by
      rw [hz, norm_neg, norm_smul, Real.norm_of_nonneg hMinv_nonneg]
    _ = ‖block_gradient j x - block_gradient j y‖ := by
      field_simp [hM_ne]

omit [Nonempty (Fin p)] in
/-- Helper for Lemma 11.5: the outer-step objective gap is represented by a real difference,
because both endpoint objective values are finite. -/
lemma cbpg_objective_gap_eq_coe_toReal_sub
    (k : ℕ) :
    F x[k] - F x[k + 1] =
      ((((F x[k]).toReal - (F x[k + 1]).toReal : ℝ)) : EReal) := by
  have hk_val : F x[k] = ((((F x[k]).toReal : ℝ)) : EReal) := by
    -- The current outer objective value is finite, so it is exactly its `toReal` coercion.
    exact
      (EReal.coe_toReal
        (cbpg_objective_value_finite hproblem x0 k).1
        (cbpg_objective_value_finite hproblem x0 k).2).symm
  have hk1_val : F x[k + 1] = ((((F x[k + 1]).toReal : ℝ)) : EReal) := by
    -- The next outer objective value is finite for the same reason.
    exact
      (EReal.coe_toReal
        (cbpg_objective_value_finite hproblem x0 (k + 1)).1
        (cbpg_objective_value_finite hproblem x0 (k + 1)).2).symm
  -- Once both endpoints are rewritten as real coercions, the objective gap is a real subtraction.
  rw [hk_val, hk1_val, EReal.coe_sub]
  simp

omit [Nonempty (Fin p)] in
/-- Helper for Lemma 11.5: at stage `j`, the textbook residual term
`(1 / (2 L_j)) ‖G^j_{L_j}(x^{k,j})‖²` is exactly the corresponding step-norm term
`(L_j / 2) ‖x^{k,j} - x^{k,j+1}‖²`. -/
lemma cbpg_auxiliary_gradient_mapping_term_eq_step_norm_term
    (k : ℕ) (j : Fin p) :
    ((1 : ℝ) / (2 * (Li j : ℝ))) * ‖G[Li j; hcore] x[k, j.1] j‖ ^ (2 : ℕ) =
      ((Li j : ℝ) / 2) * ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) := by
  have hsucc :
      x[k, j.1 + 1] =
        block_coordinate_update
          x[k, j.1]
          j
          (hproblem.toIsBlockProximalGradientProblem.prox_point (Li j) j x[k, j.1] -
            x[k, j.1] j) := by
    -- The successor auxiliary iterate is the canonical one-block prox update at stage `j`.
    simpa [block_coordinate_update] using
      cyclic_block_proximal_gradient_method_inner_succ hproblem x0I k j.2
  have hprox :
      hproblem.toIsBlockProximalGradientProblem.prox_point (Li j) j x[k, j.1] =
        x[k, j.1 + 1] j := by
    -- Reading the active coordinate of the stage update recovers the prox point itself.
    simpa [block_coordinate_update] using
      congrArg (fun z : (i : Fin p) → Ei i ↦ z j) hsucc.symm
  have hstage_map :
      G[Li j; hcore] x[k, j.1] j =
        (Li j : ℝ) • (x[k, j.1] j - x[k, j.1 + 1] j) := by
    -- The stage residual is exactly the stepsize times the active block displacement.
    calc
      G[Li j; hcore] x[k, j.1] j =
          (Li j : ℝ) •
            (x[k, j.1] j -
              hproblem.toIsBlockProximalGradientProblem.prox_point (Li j) j x[k, j.1]) := by
        rw [hproblem.toIsBlockProximalGradientProblem.gradient_mapping_def
          (Li j) x[k, j.1] j]
      _ = (Li j : ℝ) • (x[k, j.1] j - x[k, j.1 + 1] j) := by
        rw [hprox]
  have hLi_pos : 0 < (Li j : ℝ) := (Li j).2
  have hLi_ne : (Li j : ℝ) ≠ 0 := hLi_pos.ne'
  -- Replace the gradient-mapping norm by the active block step norm and simplify the scalar.
  rw [hstage_map, norm_smul, Real.norm_of_nonneg (le_of_lt hLi_pos),
    cbpg_auxiliary_step_norm_eq_block_norm hproblem x0 k j]
  field_simp [hLi_ne]

/-- Helper for Lemma 11.5: rewriting the outer-step objective gap as a real scalar `Δk`
packages both the full-cycle step bound and the active-stage residual bound into ordinary real
inequalities. -/
lemma cbpg_objective_gap_real_bounds
    (k : ℕ) (j : Fin p) :
    let Δk : ℝ := (F x[k]).toReal - (F x[k + 1]).toReal
    0 ≤ Δk ∧
      ((Lmin : ℝ) / 2) * ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) ≤ Δk ∧
      ((1 : ℝ) / (2 * (Li j : ℝ))) * ‖G[Li j; hcore] x[k, j.1] j‖ ^ (2 : ℕ) ≤ Δk := by
  dsimp
  have houterE := cbpg_sufficient_decrease_outer_step hproblem x0 k
  have houterR :
      ((Lmin : ℝ) / 2) * ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) ≤
        (F x[k]).toReal - (F x[k + 1]).toReal := by
    -- Rewrite the outer-step decrease bound through the real gap `Δk`.
    rw [cbpg_objective_gap_eq_coe_toReal_sub hproblem x0 k] at houterE
    exact_mod_cast houterE
  have houterCoeff_nonneg :
      0 ≤ ((Lmin : ℝ) / 2) * ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) := by
    -- The full-cycle decrease term is a positive coefficient times a squared norm.
    refine mul_nonneg ?_ (sq_nonneg _)
    exact div_nonneg (le_of_lt (PosReal.coe_pos Lmin)) (by positivity)
  have hgap_nonneg :
      0 ≤ (F x[k]).toReal - (F x[k + 1]).toReal :=
    le_trans houterCoeff_nonneg houterR
  have hsummand_nonneg :
      ∀ i : Fin p,
        0 ≤ ((((Li i : ℝ) / 2) * ‖x[k, i.1] - x[k, i.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    intro i
    exact_mod_cast (show 0 ≤ ((Li i : ℝ) / 2) * ‖x[k, i.1] - x[k, i.1 + 1]‖ ^ (2 : ℕ) by
      refine mul_nonneg ?_ (sq_nonneg _)
      exact div_nonneg (le_of_lt (Li i).2) (by positivity))
  have hsumE :
      Finset.sum Finset.univ
          (fun i : Fin p ↦
            ((((Li i : ℝ) / 2) * ‖x[k, i.1] - x[k, i.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)) ≤
        F x[k] - F x[k + 1] := by
    have hfinite : F x[k + 1] ≠ ⊤ ∧ F x[k + 1] ≠ ⊥ :=
      cbpg_objective_value_finite hproblem x0 (k + 1)
    -- The additive telescope packages the whole cycle decrease as a sum of nonnegative block
    -- contributions.
    exact
      (EReal.le_sub_iff_add_le (.inl hfinite.2) (.inl hfinite.1)).2
        (cbpg_outer_cycle_additive_telescope hproblem x0 k)
  let stageTerm : EReal :=
    ((((Li j : ℝ) / 2) * ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)
  have hstageTerm_le :
      stageTerm ≤ F x[k] - F x[k + 1] := by
    have hterm_le_sum :
        stageTerm ≤
          Finset.sum Finset.univ
            (fun i : Fin p ↦
              ((((Li i : ℝ) / 2) * ‖x[k, i.1] - x[k, i.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
      -- A single nonnegative stage contribution is bounded by the sum over the whole cycle.
      simpa [stageTerm] using
        (Finset.single_le_sum
          (fun i _ ↦ hsummand_nonneg i)
          (Finset.mem_univ j))
    exact hterm_le_sum.trans hsumE
  have hresidualE :
      ((((1 : ℝ) / (2 * (Li j : ℝ))) * ‖G[Li j; hcore] x[k, j.1] j‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        F x[k] - F x[k + 1] := by
    have hterm_eq :
        ((((1 : ℝ) / (2 * (Li j : ℝ))) * ‖G[Li j; hcore] x[k, j.1] j‖ ^ (2 : ℕ) : ℝ) : EReal) =
          stageTerm := by
      -- Replace the stage residual term by the equivalent stage step-norm term from equation
      -- (11.10).
      exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal))
        (cbpg_auxiliary_gradient_mapping_term_eq_step_norm_term hproblem x0 k j)
    rw [hterm_eq]
    exact hstageTerm_le
  have hresidualR :
      ((1 : ℝ) / (2 * (Li j : ℝ))) * ‖G[Li j; hcore] x[k, j.1] j‖ ^ (2 : ℕ) ≤
        (F x[k]).toReal - (F x[k + 1]).toReal := by
    -- Rewrite the residual estimate through the same real gap `Δk`.
    rw [cbpg_objective_gap_eq_coe_toReal_sub hproblem x0 k] at hresidualE
    exact_mod_cast hresidualE
  exact ⟨hgap_nonneg, houterR, hresidualR⟩

/-- Helper for Lemma 11.5: the full outer-step displacement is bounded by the square root of the
real objective gap `Δk`. -/
lemma cbpg_outer_step_norm_le_sqrt_gap
    (k : ℕ) :
    let Δk : ℝ := (F x[k]).toReal - (F x[k + 1]).toReal
    ‖toPiLp x[k] - toPiLp x[k + 1]‖ ≤
      (Real.sqrt 2 / Real.sqrt (Lmin : ℝ)) * Real.sqrt Δk := by
  dsimp
  classical
  let j0 : Fin p := Classical.choice ‹Nonempty (Fin p)›
  obtain ⟨hΔ_nonneg, houterR, _⟩ :=
    cbpg_objective_gap_real_bounds hproblem x0 k j0
  have hLmin_pos : 0 < (Lmin : ℝ) := PosReal.coe_pos Lmin
  have hright_nonneg :
      0 ≤
        (Real.sqrt 2 / Real.sqrt (Lmin : ℝ)) *
          Real.sqrt ((F x[k]).toReal - (F x[k + 1]).toReal) := by
    exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  -- Square both sides and use the outer-step quadratic decrease bound from equation (11.11).
  have hsquare :
      ((Real.sqrt 2 / Real.sqrt (Lmin : ℝ)) *
          Real.sqrt ((F x[k]).toReal - (F x[k + 1]).toReal)) ^ (2 : ℕ) =
        (2 / (Lmin : ℝ)) * ((F x[k]).toReal - (F x[k + 1]).toReal) := by
    calc
      ((Real.sqrt 2 / Real.sqrt (Lmin : ℝ)) *
          Real.sqrt ((F x[k]).toReal - (F x[k + 1]).toReal)) ^ (2 : ℕ) =
          (Real.sqrt ((2 : ℝ) / (Lmin : ℝ)) *
            Real.sqrt ((F x[k]).toReal - (F x[k + 1]).toReal)) ^ (2 : ℕ) := by
        rw [Real.sqrt_div (show 0 ≤ (2 : ℝ) by norm_num)]
      _ = (Real.sqrt (((2 : ℝ) / (Lmin : ℝ)) *
            ((F x[k]).toReal - (F x[k + 1]).toReal))) ^ (2 : ℕ) := by
        rw [← Real.sqrt_mul (show 0 ≤ (2 : ℝ) / (Lmin : ℝ) by positivity)]
      _ = (2 / (Lmin : ℝ)) * ((F x[k]).toReal - (F x[k + 1]).toReal) := by
        simpa [pow_two] using
          (Real.sq_sqrt (show 0 ≤
            ((2 : ℝ) / (Lmin : ℝ)) * ((F x[k]).toReal - (F x[k + 1]).toReal) by
              exact mul_nonneg (by positivity) hΔ_nonneg))
  have hsq :
      ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) ≤
        ((Real.sqrt 2 / Real.sqrt (Lmin : ℝ)) *
          Real.sqrt ((F x[k]).toReal - (F x[k + 1]).toReal)) ^ (2 : ℕ) := by
    rw [hsquare]
    have hc_pos : 0 < ((Lmin : ℝ) / 2) := by positivity
    have houterR' :
        ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) * ((Lmin : ℝ) / 2) ≤
          (F x[k]).toReal - (F x[k + 1]).toReal := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using houterR
    have hdiv :
        ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) ≤
          ((F x[k]).toReal - (F x[k + 1]).toReal) / ((Lmin : ℝ) / 2) := by
      exact (le_div_iff₀ hc_pos).2 houterR'
    have hdiv_eq :
        ((F x[k]).toReal - (F x[k + 1]).toReal) / ((Lmin : ℝ) / 2) =
          (2 / (Lmin : ℝ)) * ((F x[k]).toReal - (F x[k + 1]).toReal) := by
      field_simp [ne_of_gt hLmin_pos]
    rw [hdiv_eq] at hdiv
    exact hdiv
  exact (sq_le_sq₀ (norm_nonneg _) hright_nonneg).mp hsq

/-- Helper for Lemma 11.5: the active stage residual is bounded by the square root of the same
real objective gap `Δk`. -/
lemma cbpg_stage_residual_norm_le_sqrt_gap
    (k : ℕ) (j : Fin p) :
    let Δk : ℝ := (F x[k]).toReal - (F x[k + 1]).toReal
    ‖G[Li j; hcore] x[k, j.1] j‖ ≤
      Real.sqrt (2 * (Li j : ℝ)) * Real.sqrt Δk := by
  dsimp
  obtain ⟨hΔ_nonneg, _, hstageR⟩ :=
    cbpg_objective_gap_real_bounds hproblem x0 k j
  have hright_nonneg :
      0 ≤
        Real.sqrt (2 * (Li j : ℝ)) *
          Real.sqrt ((F x[k]).toReal - (F x[k + 1]).toReal) := by
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- Square both sides and use the stagewise decrease estimate from equation (11.14).
  have hsquare :
      (Real.sqrt (2 * (Li j : ℝ)) *
          Real.sqrt ((F x[k]).toReal - (F x[k + 1]).toReal)) ^ (2 : ℕ) =
        (2 * (Li j : ℝ)) * ((F x[k]).toReal - (F x[k + 1]).toReal) := by
    calc
      (Real.sqrt (2 * (Li j : ℝ)) *
          Real.sqrt ((F x[k]).toReal - (F x[k + 1]).toReal)) ^ (2 : ℕ) =
          (Real.sqrt ((2 * (Li j : ℝ)) *
            ((F x[k]).toReal - (F x[k + 1]).toReal))) ^ (2 : ℕ) := by
        have hLi_nonneg : 0 ≤ (Li j : ℝ) := le_of_lt (Li j).2
        rw [← Real.sqrt_mul (show 0 ≤ 2 * (Li j : ℝ) by nlinarith)]
      _ = (2 * (Li j : ℝ)) * ((F x[k]).toReal - (F x[k + 1]).toReal) := by
        have hprod_nonneg :
            0 ≤ (2 * (Li j : ℝ)) * ((F x[k]).toReal - (F x[k + 1]).toReal) := by
          have htwoLi_nonneg : 0 ≤ 2 * (Li j : ℝ) := by
            have hLi_nonneg : 0 ≤ (Li j : ℝ) := le_of_lt (Li j).2
            nlinarith
          exact mul_nonneg htwoLi_nonneg hΔ_nonneg
        simpa [pow_two] using Real.sq_sqrt hprod_nonneg
  have hsq :
      ‖G[Li j; hcore] x[k, j.1] j‖ ^ (2 : ℕ) ≤
        (Real.sqrt (2 * (Li j : ℝ)) *
          Real.sqrt ((F x[k]).toReal - (F x[k + 1]).toReal)) ^ (2 : ℕ) := by
    rw [hsquare]
    have hc_pos : 0 < 1 / (2 * (Li j : ℝ)) := by
      have hLi_pos : 0 < (Li j : ℝ) := (Li j).2
      positivity
    have hstageR' :
        ‖G[Li j; hcore] x[k, j.1] j‖ ^ (2 : ℕ) * (1 / (2 * (Li j : ℝ))) ≤
          (F x[k]).toReal - (F x[k + 1]).toReal := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hstageR
    have hdiv :
        ‖G[Li j; hcore] x[k, j.1] j‖ ^ (2 : ℕ) ≤
          ((F x[k]).toReal - (F x[k + 1]).toReal) / (1 / (2 * (Li j : ℝ))) := by
      exact (le_div_iff₀ hc_pos).2 hstageR'
    have hdiv_eq :
        ((F x[k]).toReal - (F x[k + 1]).toReal) / (1 / (2 * (Li j : ℝ))) =
          (2 * (Li j : ℝ)) * ((F x[k]).toReal - (F x[k + 1]).toReal) := by
      field_simp [show (2 * (Li j : ℝ)) ≠ 0 by
        have hLi_pos : 0 < (Li j : ℝ) := (Li j).2
        nlinarith]
    rw [hdiv_eq] at hdiv
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdiv
  exact (sq_le_sq₀ (norm_nonneg _) hright_nonneg).mp hsq

/-- Helper for Lemma 11.5: the fixed-block residual at the outer iterate `x^k` is bounded by the
uniform textbook coefficient times `sqrt Δk`. -/
lemma cbpg_per_block_gradient_mapping_norm_le_textbook_coeff_mul_sqrt_gap
    (k : ℕ) (j : Fin p) :
    let Δk : ℝ := (F x[k]).toReal - (F x[k + 1]).toReal
    ‖G[Lmin; hcore] x[k] j‖ ≤
      ((Real.sqrt 2 / Real.sqrt (Lmin : ℝ)) *
          ((Lf : ℝ) + 2 * (Lmax : ℝ) + Real.sqrt ((Lmin : ℝ) * (Lmax : ℝ)))) *
        Real.sqrt Δk := by
  dsimp
  have hΔ_nonneg :
      0 ≤ (F x[k]).toReal - (F x[k + 1]).toReal := by
    exact (cbpg_objective_gap_real_bounds hproblem x0 k j).1
  have hxk_g :
      x[k] ∈ effective_domain (separableSum g) := by
    simpa using cbpg_auxiliary_iterate_mem_effective_domain hproblem x0 k 0 (Nat.zero_le p)
  have hxk_int :
      x[k] ∈ interior (effective_domain f) := by
    exact
      IsBlockProximalGradientProblem.mem_interior_effective_domain_of_mem_g_effective_domain
        hproblem.toIsBlockProximalGradientProblem
        hxk_g
  have hxstage_g :
      x[k, j.1] ∈ effective_domain (separableSum g) :=
    cbpg_auxiliary_iterate_mem_effective_domain hproblem x0 k j.1 (Nat.le_of_lt j.2)
  have hxstage_int :
      x[k, j.1] ∈ interior (effective_domain f) := by
    exact
      IsBlockProximalGradientProblem.mem_interior_effective_domain_of_mem_g_effective_domain
        hproblem.toIsBlockProximalGradientProblem
        hxstage_g
  have hcoord :
      x[k, j.1] j = x[k] j := by
    simpa using
      cbpg_auxiliary_iterate_apply_eq_outer_iterate hproblem x0 k j.1 j (Nat.le_refl _)
  have hsame :
      ‖G[Li j; hcore] x[k] j - G[Li j; hcore] x[k, j.1] j‖ ≤
        ‖block_gradient j x[k] - block_gradient j x[k, j.1]‖ := by
    exact
      cbpg_partial_gradient_mapping_difference_le_block_gradient_difference_of_eq_coord
        hproblem
        (Li j)
        j
        x[k]
        x[k, j.1]
        hcoord.symm
  have hdrift :
      ‖G[Li j; hcore] x[k] j - G[Li j; hcore] x[k, j.1] j‖ ≤
        (Lf : ℝ) *
          ((Real.sqrt 2 / Real.sqrt (Lmin : ℝ)) *
            Real.sqrt ((F x[k]).toReal - (F x[k + 1]).toReal)) := by
    have hbase :
        ‖block_gradient j x[k] - block_gradient j x[k, j.1]‖ ≤
          (Lf : ℝ) * ‖toPiLp x[k] - toPiLp x[k, j.1]‖ :=
      cbpg_block_gradient_difference_le_lf_mul_toPiLp_norm
        hproblem
        j
        x[k]
        x[k, j.1]
        hxk_int
        hxstage_int
    have hprefix :
        ‖toPiLp x[k] - toPiLp x[k, j.1]‖ ≤ ‖toPiLp x[k] - toPiLp x[k + 1]‖ :=
      cbpg_prefix_displacement_toPiLp_le_outer_step hproblem x0 k j.1 (Nat.le_of_lt j.2)
    have houter :
        ‖toPiLp x[k] - toPiLp x[k + 1]‖ ≤
          (Real.sqrt 2 / Real.sqrt (Lmin : ℝ)) *
            Real.sqrt ((F x[k]).toReal - (F x[k + 1]).toReal) :=
      by
        simpa using cbpg_outer_step_norm_le_sqrt_gap hproblem x0 k
    have hLf_nonneg : 0 ≤ (Lf : ℝ) := by
      exact_mod_cast Lf.2
    exact hsame.trans <|
      hbase.trans <|
        (mul_le_mul_of_nonneg_left (hprefix.trans houter) hLf_nonneg)
  have hstage :
      ‖G[Li j; hcore] x[k, j.1] j‖ ≤
        Real.sqrt (2 * (Li j : ℝ)) *
          Real.sqrt ((F x[k]).toReal - (F x[k + 1]).toReal) :=
    by
      simpa using cbpg_stage_residual_norm_le_sqrt_gap hproblem x0 k j
  have htri :
      ‖G[Li j; hcore] x[k] j‖ ≤
        ‖G[Li j; hcore] x[k] j - G[Li j; hcore] x[k, j.1] j‖ +
          ‖G[Li j; hcore] x[k, j.1] j‖ := by
    calc
      ‖G[Li j; hcore] x[k] j‖ =
          ‖(G[Li j; hcore] x[k] j - G[Li j; hcore] x[k, j.1] j) +
              G[Li j; hcore] x[k, j.1] j‖ := by
        congr 1
        abel_nf
      _ ≤ ‖G[Li j; hcore] x[k] j - G[Li j; hcore] x[k, j.1] j‖ +
            ‖G[Li j; hcore] x[k, j.1] j‖ := by
        exact norm_add_le _ _
      _ = ‖G[Li j; hcore] x[k] j - G[Li j; hcore] x[k, j.1] j‖ +
            ‖G[Li j; hcore] x[k, j.1] j‖ := by
          rfl
  let A : ℝ := Real.sqrt 2 / Real.sqrt (Lmin : ℝ)
  have hraw :
      ‖G[Li j; hcore] x[k] j‖ ≤
        ((Lf : ℝ) * A + Real.sqrt (2 * (Li j : ℝ))) *
          Real.sqrt ((F x[k]).toReal - (F x[k + 1]).toReal) := by
    -- Route correction: keep the source triangle-split skeleton, but use the stronger
    -- same-coordinate drift bound before adding the stage residual term.
    have hsum := htri.trans (add_le_add hdrift hstage)
    simpa [A, mul_assoc, left_distrib, right_distrib, add_comm, add_left_comm, add_assoc] using hsum
  have hLj_le_max :
      (Li j : ℝ) ≤ (Lmax : ℝ) := by
    rw [cbpg_max_block_stepsize_def]
    exact Finset.le_sup' (s := (Finset.univ : Finset (Fin p))) (f := Li) (Finset.mem_univ j)
  have hsqrt_term :
      Real.sqrt (2 * (Li j : ℝ)) ≤ A * Real.sqrt ((Lmin : ℝ) * (Lmax : ℝ)) := by
    calc
      Real.sqrt (2 * (Li j : ℝ)) = Real.sqrt 2 * Real.sqrt (Li j : ℝ) := by
        rw [Real.sqrt_mul (show 0 ≤ (2 : ℝ) by norm_num)]
      _ ≤ Real.sqrt 2 * Real.sqrt (Lmax : ℝ) := by
        gcongr
      _ = A * Real.sqrt ((Lmin : ℝ) * (Lmax : ℝ)) := by
        dsimp [A]
        rw [Real.sqrt_mul (show 0 ≤ (Lmin : ℝ) by
          exact le_of_lt (PosReal.coe_pos Lmin))]
        field_simp [Real.sqrt_ne_zero'.2 (PosReal.coe_pos Lmin)]
  have hcoeff :
      (Lf : ℝ) * A + Real.sqrt (2 * (Li j : ℝ)) ≤
        A * ((Lf : ℝ) + 2 * (Lmax : ℝ) + Real.sqrt ((Lmin : ℝ) * (Lmax : ℝ))) := by
    have hcoeff' :
        (Lf : ℝ) * A + Real.sqrt (2 * (Li j : ℝ)) ≤
          (Lf : ℝ) * A + A * Real.sqrt ((Lmin : ℝ) * (Lmax : ℝ)) := by
      exact add_le_add_right hsqrt_term ((Lf : ℝ) * A)
    have hA_nonneg : 0 ≤ A := by
      dsimp [A]
      exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hslack :
        0 ≤ A * (2 * (Lmax : ℝ)) := by
      have htwoLmax_nonneg : 0 ≤ 2 * (Lmax : ℝ) := by
        have hLmax_nonneg : 0 ≤ (Lmax : ℝ) := le_of_lt (PosReal.coe_pos Lmax)
        nlinarith
      exact mul_nonneg hA_nonneg htwoLmax_nonneg
    have htarget :
        (Lf : ℝ) * A + A * Real.sqrt ((Lmin : ℝ) * (Lmax : ℝ)) ≤
          A * ((Lf : ℝ) + 2 * (Lmax : ℝ) + Real.sqrt ((Lmin : ℝ) * (Lmax : ℝ))) := by
      nlinarith [hslack]
    exact hcoeff'.trans htarget
  have hbound_Li :
      ‖G[Li j; hcore] x[k] j‖ ≤
        (A * ((Lf : ℝ) + 2 * (Lmax : ℝ) + Real.sqrt ((Lmin : ℝ) * (Lmax : ℝ)))) *
          Real.sqrt ((F x[k]).toReal - (F x[k + 1]).toReal) := by
    exact hraw.trans (mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg _))
  have hLmin_le :
      Lmin ≤ Li j := by
    simpa [cbpg_min_block_stepsize] using
      (Finset.inf'_le (s := (Finset.univ : Finset (Fin p))) (f := Li) (Finset.mem_univ j))
  have hblock :
      HasGradientAt (block_coordinate_slice f x[k] j) (block_gradient j x[k]) 0 :=
    hproblem.toIsBlockProximalGradientProblem.block_partial_gradient_hasGradientAt j hxk_int
  have hmono :
      ‖G[Lmin; hcore] x[k] j‖ ≤ ‖G[Li j; hcore] x[k] j‖ := by
    simpa using
      (block_partial_gradient_mapping_norm_monotone
        (f := f)
        (g := g)
        (block_gradient := block_gradient)
        (hg_proper := hproblem.block_g_proper)
        (hg_closed := hproblem.block_g_closed)
        (hg_convex := hproblem.block_g_convex)
        (i := j)
        (L₁ := Li j)
        (L₂ := Lmin)
        hLmin_le
        x[k]
        hblock)
  exact hmono.trans hbound_Li

/-- Helper for Lemma 11.5: each block of the residual tuple at `x^k` satisfies the real
sufficient-decrease inequality with the uniform textbook constant `C`. -/
lemma cbpg_sufficient_decrease_per_block_real
    (k : ℕ) (j : Fin p) :
    (cbpg_sufficient_decrease_constant Lf Li) * ‖G[Lmin; hcore] x[k] j‖ ^ (2 : ℕ) ≤
      ((F x[k]).toReal - (F x[k + 1]).toReal) := by
  let Δk : ℝ := (F x[k]).toReal - (F x[k + 1]).toReal
  let A : ℝ := (Lf : ℝ) + 2 * (Lmax : ℝ) + Real.sqrt ((Lmin : ℝ) * (Lmax : ℝ))
  have hΔ_nonneg : 0 ≤ Δk := by
    exact (cbpg_objective_gap_real_bounds hproblem x0 k j).1
  have hnorm :
      ‖G[Lmin; hcore] x[k] j‖ ≤
        ((Real.sqrt 2 / Real.sqrt (Lmin : ℝ)) * A) * Real.sqrt Δk := by
    simpa [Δk, A, mul_assoc] using
      cbpg_per_block_gradient_mapping_norm_le_textbook_coeff_mul_sqrt_gap hproblem x0 k j
  have hsq :
      ‖G[Lmin; hcore] x[k] j‖ ^ (2 : ℕ) ≤ ((2 / (Lmin : ℝ)) * A ^ (2 : ℕ)) * Δk := by
    have hsq_bound :=
      pow_le_pow_left₀ (norm_nonneg (G[Lmin; hcore] x[k] j)) hnorm 2
    have hratio_sq :
        (Real.sqrt 2 / Real.sqrt (Lmin : ℝ)) ^ (2 : ℕ) = 2 / (Lmin : ℝ) := by
      have hLmin_pos : 0 < (Lmin : ℝ) := PosReal.coe_pos Lmin
      rw [div_pow, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num),
        Real.sq_sqrt (le_of_lt hLmin_pos)]
    have hcoeff_sq :
        (((Real.sqrt 2 / Real.sqrt (Lmin : ℝ)) * A) * Real.sqrt Δk) ^ (2 : ℕ) =
          ((2 / (Lmin : ℝ)) * A ^ (2 : ℕ)) * Δk := by
      calc
        (((Real.sqrt 2 / Real.sqrt (Lmin : ℝ)) * A) * Real.sqrt Δk) ^ (2 : ℕ) =
            (((Real.sqrt 2 / Real.sqrt (Lmin : ℝ)) * A) ^ (2 : ℕ)) *
              (Real.sqrt Δk) ^ (2 : ℕ) := by
          rw [mul_pow]
        _ = (((Real.sqrt 2 / Real.sqrt (Lmin : ℝ)) * A) ^ (2 : ℕ)) * Δk := by
          rw [Real.sq_sqrt hΔ_nonneg]
        _ = ((Real.sqrt 2 / Real.sqrt (Lmin : ℝ)) ^ (2 : ℕ) * A ^ (2 : ℕ)) * Δk := by
          rw [mul_pow]
        _ = ((2 / (Lmin : ℝ)) * A ^ (2 : ℕ)) * Δk := by
          rw [hratio_sq]
    rw [hcoeff_sq] at hsq_bound
    exact hsq_bound
  have hA_pos : 0 < A := by
    have hLf_nonneg : 0 ≤ (Lf : ℝ) := by exact_mod_cast Lf.2
    have htwoLmax_nonneg : 0 ≤ 2 * (Lmax : ℝ) := by
      have hLmax_nonneg : 0 ≤ (Lmax : ℝ) := le_of_lt (PosReal.coe_pos Lmax)
      nlinarith
    have hsqrt_pos : 0 < Real.sqrt ((Lmin : ℝ) * (Lmax : ℝ)) := by
      apply Real.sqrt_pos.2
      exact mul_pos (PosReal.coe_pos Lmin) (PosReal.coe_pos Lmax)
    dsimp [A]
    nlinarith
  have hconst_nonneg : 0 ≤ cbpg_sufficient_decrease_constant Lf Li := by
    rw [cbpg_sufficient_decrease_constant_def]
    exact div_nonneg (le_of_lt (PosReal.coe_pos Lmin)) (by positivity)
  have hconst_def :
      cbpg_sufficient_decrease_constant Lf Li = (Lmin : ℝ) / (2 * A ^ (2 : ℕ)) := by
    simp [A, cbpg_sufficient_decrease_constant_def]
  have hconst_mul :
      cbpg_sufficient_decrease_constant Lf Li * ((2 / (Lmin : ℝ)) * A ^ (2 : ℕ)) = 1 := by
    rw [hconst_def]
    have hLmin_ne : (Lmin : ℝ) ≠ 0 := ne_of_gt (PosReal.coe_pos Lmin)
    have hA_ne : A ≠ 0 := hA_pos.ne'
    have hA_sq_ne : A ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hA_ne
    field_simp [hLmin_ne, hA_sq_ne]
  -- Square the fixed-block norm bound, then cancel the textbook coefficient algebraically.
  calc
    (cbpg_sufficient_decrease_constant Lf Li) * ‖G[Lmin; hcore] x[k] j‖ ^ (2 : ℕ) ≤
        (cbpg_sufficient_decrease_constant Lf Li) * (((2 / (Lmin : ℝ)) * A ^ (2 : ℕ)) * Δk) := by
      exact mul_le_mul_of_nonneg_left hsq hconst_nonneg
    _ = Δk := by
      calc
        (cbpg_sufficient_decrease_constant Lf Li) * (((2 / (Lmin : ℝ)) * A ^ (2 : ℕ)) * Δk) =
            (cbpg_sufficient_decrease_constant Lf Li * ((2 / (Lmin : ℝ)) * A ^ (2 : ℕ))) * Δk := by
          ring
        _ = Δk := by
          rw [hconst_mul, one_mul]

/-- Lemma 11.5: under Assumption 11.1, if `x^k` is generated by the cyclic block proximal
gradient method, then for every `k ≥ 0` the sufficient-decrease estimate
`F(x^k) - F(x^(k+1)) ≥ (C / p) * ‖G_{L_min}(x^k)‖^2` holds in the canonical block `L²` norm,
where
`C = L_min / (2 (L_f + 2 L_max + sqrt (L_min L_max))^2)`. -/
theorem cbpg_sufficient_decrease_gradient_mapping
    (k : ℕ) :
    F x[k] - F x[k + 1] ≥
      (((cbpg_sufficient_decrease_constant Lf Li / (p : ℝ)) *
          ‖toPiLp Gcbpg[k]‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  let Δk : ℝ := (F x[k]).toReal - (F x[k + 1]).toReal
  have hp_pos_nat : 0 < p := by
    simpa [Fintype.card_fin] using (Fintype.card_pos_iff.mpr ‹Nonempty (Fin p)›)
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast hp_pos_nat
  have hnorm_sq :
      ‖toPiLp Gcbpg[k]‖ ^ (2 : ℕ) =
        ∑ j : Fin p, ‖G[Lmin; hcore] x[k] j‖ ^ (2 : ℕ) := by
    simpa using
      (PiLp.norm_sq_eq_of_L2 (fun j : Fin p ↦ Ei j) (toPiLp Gcbpg[k]))
  have hsum :
      (cbpg_sufficient_decrease_constant Lf Li) * ‖toPiLp Gcbpg[k]‖ ^ (2 : ℕ) ≤
        (p : ℝ) * Δk := by
    calc
      (cbpg_sufficient_decrease_constant Lf Li) * ‖toPiLp Gcbpg[k]‖ ^ (2 : ℕ) =
          (cbpg_sufficient_decrease_constant Lf Li) *
            ∑ j : Fin p, ‖G[Lmin; hcore] x[k] j‖ ^ (2 : ℕ) := by
        rw [hnorm_sq]
      _ = ∑ j : Fin p,
            (cbpg_sufficient_decrease_constant Lf Li) * ‖G[Lmin; hcore] x[k] j‖ ^ (2 : ℕ) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ _j : Fin p, Δk := by
        refine Finset.sum_le_sum ?_
        intro j hj
        exact cbpg_sufficient_decrease_per_block_real hproblem x0 k j
      _ = (p : ℝ) * Δk := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hreal :
      (cbpg_sufficient_decrease_constant Lf Li / (p : ℝ)) * ‖toPiLp Gcbpg[k]‖ ^ (2 : ℕ) ≤ Δk := by
    have hdiv :
        ((cbpg_sufficient_decrease_constant Lf Li) * ‖toPiLp Gcbpg[k]‖ ^ (2 : ℕ)) /
            (p : ℝ) ≤
          Δk := by
      exact (div_le_iff₀ hp_pos).2 (by simpa [Δk, mul_comm, mul_left_comm, mul_assoc] using hsum)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  -- Rewrite the objective gap once as a real coercion and cast the summed real estimate to
  -- `EReal` only at the end.
  rw [cbpg_objective_gap_eq_coe_toReal_sub hproblem x0 k]
  exact EReal.coe_le_coe (by simpa [Δk] using hreal)

end
