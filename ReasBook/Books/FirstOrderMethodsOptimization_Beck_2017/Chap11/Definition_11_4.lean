/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_10
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_30
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_3
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped BigOperators Gradient

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}

/-- A finite value of the block-separable regularizer forces each coordinate penalty to be finite.
-/
theorem block_mem_effective_domain_of_mem_separableSum_effective_domain
    (g : (i : ι) → Ei i → EReal)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    {x : (i : ι) → Ei i} (hx : x ∈ effective_domain (separableSum g)) (i : ι) :
    x i ∈ effective_domain (g i) := by
  classical
  refine mem_effective_domain.mpr <| lt_top_iff_ne_top.mpr ?_
  intro hgi_top
  have hrest_ne_bot :
      Finset.sum (Finset.univ.erase i) (fun j ↦ g j (x j)) ≠ ⊥ := by
    exact ereal_sum_ne_bot (Finset.univ.erase i) (fun j ↦ g j (x j))
      (fun j _ ↦ (hg_proper j).ne_bot (x j))
  have hsum :
      Finset.sum Finset.univ (fun j ↦ g j (x j)) =
        g i (x i) + Finset.sum (Finset.univ.erase i) (fun j ↦ g j (x j)) := by
    symm
    exact Finset.add_sum_erase Finset.univ (fun j ↦ g j (x j)) (Finset.mem_univ i)
  have hsum_eq_top : separableSum g x = ⊤ := by
    rw [separableSum_apply, hsum, hgi_top, EReal.top_add_of_ne_bot hrest_ne_bot]
  exact (lt_top_iff_ne_top.mp (mem_effective_domain.mp hx)) hsum_eq_top

end

-- DIAGNOSTIC_BOUNDARY
section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, TopologicalSpace (Ei i)]

/-- Helper for Definition 11.4: composing a block penalty with the coordinate projection preserves
lower semicontinuity. -/
lemma coordinate_eval_lowerSemicontinuous
    (g : (i : ι) → Ei i → EReal) (i : ι)
    (hg : LowerSemicontinuous (g i)) :
    LowerSemicontinuous (fun x : ((j : ι) → Ei j) ↦ g i (x i)) := by
  -- Pull back lower semicontinuity along the continuous coordinate projection.
  simpa [Function.comp] using hg.comp (continuous_apply i)

end

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, TopologicalSpace (Ei i)]

/-- Helper for Definition 11.4: a finite sum of `EReal`-valued lower semicontinuous functions is
lower semicontinuous. -/
lemma lowerSemicontinuous_finset_sum_ereal
    {κ α : Type*} [TopologicalSpace α] (a : Finset κ) (f : κ → α → EReal)
    (ha : ∀ i ∈ a, LowerSemicontinuous (f i)) :
    LowerSemicontinuous (fun x : α ↦ Finset.sum a (fun i ↦ f i x)) := by
  classical
  revert ha
  refine Finset.induction_on a ?_ ?_
  · intro _ha
    -- The empty sum is the constant zero function.
    simpa using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : α ↦ (0 : EReal)))
  · intro i s hi ih hs
    have hi_lsc : LowerSemicontinuous (f i) := hs i (by simp)
    have hs_lsc : LowerSemicontinuous (fun x : α ↦ Finset.sum s (fun j ↦ f j x)) := by
      -- Restrict the family hypothesis to the tail of the finite sum.
      refine ih ?_
      intro j hj
      exact hs j (by simp [hj])
    -- Route correction: use the liminf characterization and `EReal.le_liminf_add` instead of the
    -- unavailable `[ContinuousAdd EReal]` finite-sum API.
    refine (lowerSemicontinuous_iff_le_liminf).2 ?_
    intro x
    have hi_le : f i x ≤ Filter.liminf (f i) (nhds x) := hi_lsc.le_liminf x
    have hs_le :
        Finset.sum s (fun j ↦ f j x) ≤
          Filter.liminf (fun y ↦ Finset.sum s (fun j ↦ f j y)) (nhds x) := hs_lsc.le_liminf x
    -- Rewrite the inserted sum as a head-plus-tail decomposition, then combine the liminf bounds.
    calc
      Finset.sum (insert i s) (fun j ↦ f j x) = f i x + Finset.sum s (fun j ↦ f j x) := by
        simp [Finset.sum_insert, hi]
      _ ≤
          Filter.liminf (f i) (nhds x) +
            Filter.liminf (fun y ↦ Finset.sum s (fun j ↦ f j y)) (nhds x) :=
        add_le_add hi_le hs_le
      _ ≤ Filter.liminf (fun y ↦ f i y + Finset.sum s (fun j ↦ f j y)) (nhds x) :=
        EReal.le_liminf_add
      _ = Filter.liminf (fun y ↦ Finset.sum (insert i s) (fun j ↦ f j y)) (nhds x) := by
        simp [hi]

/-- The block-separable regularizer `x ↦ ∑ i, g_i(x_i)` is lower semicontinuous when every block
penalty `g_i` is lower semicontinuous. -/
theorem separableSum_closed
    (g : (i : ι) → Ei i → EReal)
    (hg_closed : ∀ i, LowerSemicontinuous (g i)) :
    LowerSemicontinuous (separableSum g) := by
  classical
  have hcoord :
      ∀ i, LowerSemicontinuous (fun x : ((j : ι) → Ei j) ↦ g i (x i)) := by
    intro i
    -- Each summand is the pullback of a block penalty along the `i`-th coordinate evaluation map.
    exact coordinate_eval_lowerSemicontinuous g i (hg_closed i)
  -- Apply the `EReal`-specific finite-sum lemma to the coordinate summands.
  simpa [separableSum] using
    lowerSemicontinuous_finset_sum_ereal
      (a := Finset.univ)
      (f := fun i ↦ fun x : ((j : ι) → Ei j) ↦ g i (x i))
      (fun i _ ↦ hcoord i)

instance instFactLowerSemicontinuousSeparableSum
    (g : (i : ι) → Ei i → EReal) [∀ i, Fact (LowerSemicontinuous (g i))] :
    Fact (LowerSemicontinuous (separableSum g)) :=
  ⟨separableSum_closed g (fun i ↦ (Fact.out : LowerSemicontinuous (g i)))⟩

end

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, AddCommMonoid (Ei i)] [∀ i, Module ℝ (Ei i)]

/-- The block-separable regularizer `x ↦ ∑ i, g_i(x_i)` is convex when every block penalty `g_i`
is proper and convex. -/
theorem separableSum_convex
    (g : (i : ι) → Ei i → EReal)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_convex : ∀ i, is_convex_function (g i)) :
    is_convex_function (separableSum g) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let G : Fin (Fintype.card ι) → ((i : ι) → Ei i) → EReal :=
    fun k x ↦ g (e.symm k) (x (e.symm k))
  let x0 : (i : ι) → Ei i := fun i ↦ Classical.choose (hg_proper i).effective_domain_nonempty
  have hx0 : ∀ i, x0 i ∈ effective_domain (g i) := by
    intro i
    exact Classical.choose_spec (hg_proper i).effective_domain_nonempty
  have hG_proper : ∀ k : Fin (Fintype.card ι), IsProperExtendedRealFunction (G k) := by
    intro k
    refine ⟨?_, ?_⟩
    · intro x
      simpa [G] using (hg_proper (e.symm k)).ne_bot (x (e.symm k))
    · refine ⟨x0, ?_⟩
      simpa [G] using hx0 (e.symm k)
  have hG : ∀ k : Fin (Fintype.card ι), is_convex_function (G k) := by
    intro k
    -- Each coordinate summand inherits convexity directly from the corresponding block penalty.
    letI : IsProperExtendedRealFunction (G k) := hG_proper k
    letI : IsProperExtendedRealFunction (g (e.symm k)) := hg_proper (e.symm k)
    rw [is_convex_function_iff_segment_ineq]
    intro x hx y hy t ht
    simpa [G] using
      (is_convex_function_iff_segment_ineq (f := g (e.symm k))).1
        (hg_convex (e.symm k))
        (x (e.symm k))
        hx
        (y (e.symm k))
        hy
        ht
  have hsum :
      is_convex_function
        (fun x : ((i : ι) → Ei i) ↦
          ∑ k : Fin (Fintype.card ι), G k x) := by
    simpa using
      is_convex_function_finset_nonneg_weighted_sum
        (s := Finset.univ)
        (f := G)
        (fun k _ ↦ hG k)
        (fun k _ x ↦ (hG_proper k).ne_bot x)
        (fun _ ↦ (1 : NNReal))
  have hsum_eq :
      (fun x : ((i : ι) → Ei i) ↦
        ∑ k : Fin (Fintype.card ι), G k x) = separableSum g := by
    funext x
    -- Reindex the finite sum from `Fin (card ι)` back to the original block index type.
    simpa [G, e, separableSum] using
      (Fintype.sum_equiv e
        (fun i ↦ g i (x i))
        (fun k ↦ G k x)
        (fun i ↦ by
          simpa [G] using congrArg (fun j : ι ↦ g j (x j)) (e.left_inv i).symm)).symm
  simpa [hsum_eq] using hsum

instance instFactIsConvexFunctionSeparableSum
    (g : (i : ι) → Ei i → EReal)
    [∀ i, IsProperExtendedRealFunction (g i)] [∀ i, Fact (is_convex_function (g i))] :
    Fact (is_convex_function (separableSum g)) :=
  ⟨separableSum_convex g
      (fun i ↦ (inferInstance : IsProperExtendedRealFunction (g i)))
      (fun i ↦ (Fact.out : is_convex_function (g i)))⟩

end

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, Zero (Ei i)]

/- The canonical dependent-product block insertion map is the existing owner `Pi.single`; the
source-facing Chapter 11 surface uses the textbook notation `𝒰[i]`. -/
notation "𝒰[" i "]" => @Pi.single _ _ _ (Classical.decEq _) i

end

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, AddZeroClass (Ei i)]

local instance : DecidableEq ι := Classical.decEq ι

/-- Updating only the `i`-th block of `x` by the displacement `d`, equivalently `x + 𝒰[i] d`. -/
def block_coordinate_update
    (x : (i : ι) → Ei i) (i : ι) (d : Ei i) : (i : ι) → Ei i :=
  x + 𝒰[i] d

-- Proof sketch: in the updated block we add the inserted displacement `d` to `x i`.
/-- The `i`-th coordinate of the one-block update is `x i + d`. -/
@[simp] theorem block_coordinate_update_apply_same
    (x : (i : ι) → Ei i) (i : ι) (d : Ei i) :
    block_coordinate_update x i d i = x i + d := by
  -- At the updated coordinate, `Pi.single` contributes exactly the inserted displacement.
  classical
  simp [block_coordinate_update]

-- Proof sketch: away from the updated block the inserted displacement vanishes.
/-- Away from the updated block, `block_coordinate_update` agrees with the original point. -/
@[simp] theorem block_coordinate_update_apply_ne
    (x : (i : ι) → Ei i) {i j : ι} (d : Ei i) (hji : j ≠ i) :
    block_coordinate_update x i d j = x j := by
  -- Away from the chosen block, `Pi.single` vanishes.
  classical
  simp [block_coordinate_update, hji]

-- Proof sketch: compare `block_coordinate_update x i d` and `Function.update x i (x i + d)`
-- coordinatewise; both agree with `x i + d` at the active block and with `x` elsewhere.
/-- Updating block `i` by the displacement `d` is the same as `Function.update` at the new block
value `x i + d`. -/
theorem block_coordinate_update_eq_update
    [DecidableEq ι]
    (x : (i : ι) → Ei i) (i : ι) (d : Ei i) :
    block_coordinate_update x i d =
      Function.update x i (x i + d) := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [block_coordinate_update]
  · simp [block_coordinate_update, Function.update, hj]

/-- Fixing all blocks except the `i`-th one turns the smooth term `f` into the one-block slice
`d ↦ f(x + 𝒰[i] d)`. -/
def block_coordinate_slice (f : ((i : ι) → Ei i) → EReal)
    (x : (i : ι) → Ei i) (i : ι) : Ei i → ℝ :=
  fun d ↦ (f (block_coordinate_update x i d)).toReal

-- Proof sketch: unfold `block_coordinate_slice`; evaluation at `d` is exactly the translated
-- one-block slice `f (x + 𝒰[i] d)`.
/-- Evaluating the `i`-th block slice at `d` gives
`(f (x + 𝒰[i] d)).toReal`. -/
@[simp] theorem block_coordinate_slice_apply
    (f : ((i : ι) → Ei i) → EReal) (x : (i : ι) → Ei i) (i : ι) (d : Ei i) :
    block_coordinate_slice f x i d = (f (block_coordinate_update x i d)).toReal :=
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- Positive scaling preserves properness, lower semicontinuity, and convexity. -/
lemma scaled_function_pcc_of_pos
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) (lam : PosReal) :
    IsProperExtendedRealFunction (((lam : EReal) • f)) ∧
      LowerSemicontinuous (((lam : EReal) • f)) ∧
      is_convex_function (((lam : EReal) • f)) := by
  -- Reuse the canonical Chapter 6 scaling package instead of duplicating the epigraph argument.
  simpa using
    scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam

end

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]

/-- The one-block proximal-gradient update determined by the block partial gradient
`block_gradient i x`. -/
def block_partial_prox_grad_point
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (M : PosReal) (i : ι) [ProperSpace (Ei i)] (x : (i : ι) → Ei i) : Ei i :=
  let hg_scaled := scaled_function_pcc_of_pos
    (g i) (hg_proper i) (hg_closed i) (hg_convex i) (1 / M)
  Classical.choose <|
    prox_eq_singleton_of_proper_closed_convex
      ((((1 / M : PosReal) : EReal) • g i))
      hg_scaled.1
      hg_scaled.2.1
      hg_scaled.2.2
      (x i - (1 / M : ℝ) • block_gradient i x)

/-- The block partial gradient mapping `G^i_M(x)` is the stepsize-scaled residual of the current
block and its one-block proximal-gradient update. -/
def block_partial_gradient_mapping
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (M : PosReal) (i : ι) [ProperSpace (Ei i)] (x : (i : ι) → Ei i) : Ei i :=
  (M : ℝ) •
    (x i - block_partial_prox_grad_point g block_gradient hg_proper hg_closed hg_convex M i x)

/-- Textbook notation for the Chapter 11 one-block proximal-gradient update `T_M^i(x)`. -/
scoped[Gradient] notation3:max
    "T[" M "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" =>
  fun x i ↦
    block_partial_prox_grad_point g block_gradient hg_proper hg_closed hg_convex M i x

/-- Direct-application form of the Chapter 11 notation `T_M^i(x)`. -/
scoped[Gradient] notation3:max
    "T[" M "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" x:arg
      i:arg =>
  block_partial_prox_grad_point g block_gradient hg_proper hg_closed hg_convex M i x

/-- Textbook notation for the Chapter 11 block partial gradient mapping `G_M^i(x)`. -/
scoped[Gradient] notation3:max
    "G[" M "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" =>
  fun x i ↦
    block_partial_gradient_mapping g block_gradient hg_proper hg_closed hg_convex M i x

/-- Direct-application form of the Chapter 11 notation `G_M^i(x)`. -/
scoped[Gradient] notation3:max
    "G[" M "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" x:arg
      i:arg =>
  block_partial_gradient_mapping g block_gradient hg_proper hg_closed hg_convex M i x

-- Proof sketch: unfold `block_partial_gradient_mapping`; the statement is exactly the defining
-- residual formula `M • (x_i - T_M^i(x))`.
/-- Evaluating the block partial gradient mapping gives the stepsize-scaled residual
`M • (x_i - T_M^i(x))`. -/
@[simp] theorem block_partial_gradient_mapping_def
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (M : PosReal) (x : (i : ι) → Ei i) (i : ι) [ProperSpace (Ei i)] :
    block_partial_gradient_mapping g block_gradient hg_proper hg_closed hg_convex M i x =
      (M : ℝ) •
        (x i -
          block_partial_prox_grad_point g block_gradient hg_proper hg_closed hg_convex M i x) :=
  rfl

/-- The Chapter 11 one-block proximal-gradient update is the unique point of the corresponding
scaled proximal singleton. -/
theorem block_partial_prox_grad_point_eq_singleton
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (M : PosReal) (i : ι) [ProperSpace (Ei i)] (x : (i : ι) → Ei i) :
    prox[((((1 / M : PosReal) : EReal) • g i))]
      (x i - (1 / M : ℝ) • block_gradient i x) =
        {block_partial_prox_grad_point g block_gradient hg_proper hg_closed hg_convex M i x} := by
  let hscaled :=
    scaled_function_pcc_of_pos
      (g i) (hg_proper i) (hg_closed i) (hg_convex i) (1 / M)
  simpa [block_partial_prox_grad_point, hscaled] using
    (Classical.choose_spec <|
      prox_eq_singleton_of_proper_closed_convex
        ((((1 / M : PosReal) : EReal) • g i))
        hscaled.1
        hscaled.2.1
        hscaled.2.2
        (x i - (1 / M : ℝ) • block_gradient i x))

end

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]

/- The blockwise data common to Definitions 11.4 and 11.13 already form a reusable Chapter 11
`core/canonical` owner. The source-facing items then add only their genuinely extra hypotheses:
Definition 11.4 adds convexity of `effective_domain f` together with a global `L_f`-smoothness
bound, while Definition 11.13 adds convexity and mere differentiability of `f`. -/

/-- The Chapter 11 core owner for block proximal-gradient problems packages the blockwise penalty
assumptions, the domain-compatibility and optimizer data, and the one-block gradient/Lipschitz
clauses determined by the explicit block constants `L_i`. -/
class IsBlockProximalGradientProblem
    (f : ((i : ι) → Ei i) → EReal) (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (XStar : Set ((i : ι) → Ei i)) (FOpt : ℝ)
    (Li : (i : ι) → PosReal) : Prop where
  f_ne_bot (x) : f x ≠ ⊥
  block_g_proper (i) : IsProperExtendedRealFunction (g i)
  block_g_closed (i) : LowerSemicontinuous (g i)
  block_g_convex (i) : is_convex_function (g i)
  f_closed : LowerSemicontinuous f
  g_effective_domain_subset_interior_f_effective_domain :
    effective_domain (separableSum g) ⊆ interior (effective_domain f)
  optimal_set_eq :
    XStar =
      unconstrained_problem_solutions
        (composite_model_objective f (separableSum g))
  optimal_set_nonempty : XStar.Nonempty
  optimal_value_isGLB :
    IsGLB
      (Set.range (composite_model_objective f (separableSum g)))
      (FOpt : EReal)
  block_partial_gradient_spec
      (i : ι) {x : (i : ι) → Ei i}
      (hx : x ∈ interior (effective_domain f)) :
      HasFDerivAt (block_coordinate_slice f x i)
        (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0
  block_partial_gradient_lipschitz
      (i : ι) {x : (i : ι) → Ei i} {d : Ei i}
      (hx : x ∈ interior (effective_domain f))
      (hxd : block_coordinate_update x i d ∈ interior (effective_domain f)) :
      ‖block_gradient i x - block_gradient i (block_coordinate_update x i d)‖ ≤
        (Li i : ℝ) * ‖d‖

/- Definition 11.4 is `source-facing`: it fixes the standing assumptions for the block proximal
gradient method in their textbook blockwise form. With the shared Chapter 11 core owner above,
the only additional primitive data here are the convexity of `effective_domain f` and the global
`L_f`-smoothness of `(fun x ↦ (f x).toReal)` on `interior (effective_domain f)`. The Chapter 10
owner `IsCompositeSmoothMinimizationProblem` remains the downstream `bridge/view`. -/

/-- Definition 11.4: assumptions (A)-(E) for the block proximal-gradient method mean that each
block penalty `g_i : E_i → (-∞, ∞]` is proper, closed, and convex; the smooth term
`f : (Π i, E_i) → (-∞, ∞]` never takes the value `-∞`, is closed with convex effective domain,
the effective domain of `x ↦ ∑ i, g_i(x_i)` lies in the interior of the effective domain of `f`,
and `x ↦ (f x).toReal` is differentiable and `L_f`-smooth on that interior, so these clauses imply
that `f` is proper; for each block index `i`, the chosen block gradient map
`block_gradient i x = ∇_i f(x)` is the gradient of the one-block slice
`d ↦ f(x + 𝒰[i] d)` at `d = 0` and is `L_i`-Lipschitz along the `i`-th block direction;
and `XStar = X^*` is the nonempty optimal set of the composite objective with optimal value
`FOpt = F_opt`. -/
class BlockProximalGradientAssumptions
    (f : ((i : ι) → Ei i) → EReal) (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (XStar : Set ((i : ι) → Ei i)) (FOpt : ℝ)
    (Lf : NNReal) (Li : (i : ι) → PosReal) : Prop
    extends IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li where
  f_effective_domain_convex : Convex ℝ (effective_domain f)
  f_toReal_smooth_on_interior_effective_domain :
    is_l_smooth_on (fun x ↦ (f x).toReal) (interior (effective_domain f)) Lf

/-- The source-facing Chapter 11 assumptions inherit the shared block proximal-gradient problem
owner. -/
instance instIsBlockProximalGradientProblemOfBlockProximalGradientAssumptions
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li :=
  h.toIsBlockProximalGradientProblem

namespace IsBlockProximalGradientProblem

/-- The canonical one-block proximal-gradient update attached to a Chapter 11 block problem owner.
-/
abbrev prox_point
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (M : PosReal) (i : ι) [ProperSpace (Ei i)] (x : (i : ι) → Ei i) : Ei i :=
  block_partial_prox_grad_point
    g
    block_gradient
    h.block_g_proper
    h.block_g_closed
    h.block_g_convex
    M
    i
    x

/-- The canonical one-block partial gradient mapping attached to a Chapter 11 block problem owner.
-/
abbrev gradient_mapping
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (M : PosReal) (i : ι) [ProperSpace (Ei i)] (x : (i : ι) → Ei i) : Ei i :=
  block_partial_gradient_mapping
    g
    block_gradient
    h.block_g_proper
    h.block_g_closed
    h.block_g_convex
    M
    i
    x

/-- Evaluating the owner-level one-block residual map gives the textbook formula
`M • (x_i - T_M^i(x))`. -/
@[simp] theorem gradient_mapping_def
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (M : PosReal) (x : (i : ι) → Ei i) (i : ι) [ProperSpace (Ei i)] :
    h.gradient_mapping M i x = (M : ℝ) • (x i - h.prox_point M i x) :=
  rfl

/-- The owner-level one-block prox point lies in the effective domain of the selected block
penalty. -/
theorem prox_point_eq_singleton
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (M : PosReal) (i : ι) [ProperSpace (Ei i)] (x : (j : ι) → Ei j) :
    prox[((((1 / M : PosReal) : EReal) • g i))]
      (x i - (1 / M : ℝ) • block_gradient i x) =
        {h.prox_point M i x} := by
  simpa [IsBlockProximalGradientProblem.prox_point] using
    block_partial_prox_grad_point_eq_singleton
      g
      block_gradient
      h.block_g_proper
      h.block_g_closed
      h.block_g_convex
      M
      i
      x

/-- The owner-level one-block prox point lies in the effective domain of the selected block
penalty. -/
theorem prox_point_mem_effective_domain
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (M : PosReal) (i : ι) [ProperSpace (Ei i)] (x : (j : ι) → Ei j) :
    h.prox_point M i x ∈ effective_domain (g i) := by
  rcases scaled_prox_singleton_support_of_proper_convex
      (f := g i)
      (μ := 1 / M)
      (h.block_g_proper i)
      (h.block_g_convex i)
      (x i - (1 / M : ℝ) • block_gradient i x)
      (h.prox_point M i x)
      (h.prox_point_eq_singleton M i x) with
    ⟨hmem, _⟩
  simpa using hmem

/-- Replacing one block by the owner-level prox point preserves the effective domain of the
block-separable regularizer. -/
theorem block_coordinate_update_prox_point_mem_effective_domain
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (M : PosReal) (x : effective_domain (separableSum g)) (i : ι) [ProperSpace (Ei i)] :
    let x' : (j : ι) → Ei j := x.1
    block_coordinate_update x' i (h.prox_point M i x' - x' i) ∈
      effective_domain (separableSum g) := by
  let x' : (j : ι) → Ei j := x.1
  let xPlus : (j : ι) → Ei j :=
    block_coordinate_update x' i (h.prox_point M i x' - x' i)
  have hx_top : ∀ j, g j (x' j) < ⊤ := by
    intro j
    exact
      mem_effective_domain.mp
        (block_mem_effective_domain_of_mem_separableSum_effective_domain g h.block_g_proper x.2 j)
  have hxPlus_top : ∀ j, g j (xPlus j) < ⊤ := by
    intro j
    by_cases hji : j = i
    · subst j
      have hi_mem : h.prox_point M i x' ∈ effective_domain (g i) :=
        h.prox_point_mem_effective_domain M i x'
      simpa [xPlus, block_coordinate_update] using mem_effective_domain.mp hi_mem
    · simpa [xPlus, block_coordinate_update, hji] using hx_top j
  rw [mem_effective_domain, separableSum_apply]
  exact ereal_sum_lt_top Finset.univ (fun j ↦ g j (xPlus j)) (fun j _ ↦ hxPlus_top j)

/- Textbook notation for the Chapter 11 one-block proximal-gradient update `T_M^i(x)` attached
to a block-problem owner. -/
set_option quotPrecheck false in
scoped[Gradient] notation:max "T[" M "; " h "]" =>
  fun x i ↦ IsBlockProximalGradientProblem.prox_point h M i x

/- Direct-application form of the Chapter 11 owner notation `T_M^i(x)`. -/
set_option quotPrecheck false in
scoped[Gradient] notation:max "T[" M "; " h "]" x:arg i:arg =>
  IsBlockProximalGradientProblem.prox_point h M i x

/- Textbook notation for the Chapter 11 block partial gradient mapping `G_M^i(x)` attached to a
block-problem owner. -/
set_option quotPrecheck false in
scoped[Gradient] notation:max "G[" M "; " h "]" =>
  fun x i ↦ IsBlockProximalGradientProblem.gradient_mapping h M i x

/- Direct-application form of the Chapter 11 owner notation `G_M^i(x)`. -/
set_option quotPrecheck false in
scoped[Gradient] notation:max "G[" M "; " h "]" x:arg i:arg =>
  IsBlockProximalGradientProblem.gradient_mapping h M i x

/-- Under blockwise completeness, the primitive Fréchet-derivative specification recovers the
usual gradient formulation for the one-block slice. -/
-- Proof sketch: `HasGradientAt` is the Hilbert-space reformulation of `HasFDerivAt` through
-- `InnerProductSpace.toDualMap`, so the class field already provides the desired statement.
theorem block_partial_gradient_hasGradientAt
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (i : ι) [CompleteSpace (Ei i)] {x : (i : ι) → Ei i}
    (hx : x ∈ interior (effective_domain f)) :
    HasGradientAt (block_coordinate_slice f x i) (block_gradient i x) 0 := by
  -- The class field is already the Fréchet-derivative version of the desired gradient statement.
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa using h.block_partial_gradient_spec i hx

/-- The blockwise properness assumptions and the domain-compatibility clause force
`effective_domain f` to be nonempty. -/
-- Proof sketch: use a finite point in `effective_domain (separableSum g)` from blockwise
-- properness, then push it into `interior (effective_domain f)` via the compatibility field.
theorem f_effective_domain_nonempty
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li) :
    (effective_domain f).Nonempty := by
  rcases (separableSum_proper g h.block_g_proper).effective_domain_nonempty with ⟨x, hx⟩
  -- The compatibility field moves a finite point of `separableSum g` into the interior of
  -- `effective_domain f`, hence in particular into `effective_domain f` itself.
  exact ⟨x, interior_subset (h.g_effective_domain_subset_interior_f_effective_domain hx)⟩

/-- Under the Chapter 11 block proximal-gradient assumptions, every point of the effective domain
of the block-separable regularizer lies in `interior (effective_domain f)`. -/
theorem mem_interior_effective_domain_of_mem_g_effective_domain
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    {x : (i : ι) → Ei i} (hx : x ∈ effective_domain (separableSum g)) :
    x ∈ interior (effective_domain f) :=
  h.g_effective_domain_subset_interior_f_effective_domain hx

/-- A point in the effective domain of the block-separable regularizer canonically determines a
point of `interior (effective_domain f)` under the Chapter 11 assumptions. -/
def interior_effective_domain_point
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (x : effective_domain (separableSum g)) : interior (effective_domain f) :=
  ⟨x, h.mem_interior_effective_domain_of_mem_g_effective_domain x.2⟩

/-- Coercing the canonical interior-domain point attached to
`x ∈ effective_domain (separableSum g)` recovers `x`. -/
@[simp] theorem interior_effective_domain_point_coe
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (x : effective_domain (separableSum g)) :
    ((h.interior_effective_domain_point x : interior (effective_domain f)) :
        ((i : ι) → Ei i)) = x :=
  rfl

/-- The Chapter 11 block proximal-gradient assumptions canonically provide properness of `f`. -/
-- Proof sketch: combine the primitive non-`⊥` field with the derived nonemptiness of
-- `effective_domain f`.
theorem f_proper
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li) :
    IsProperExtendedRealFunction f := by
  refine ⟨h.f_ne_bot, h.f_effective_domain_nonempty⟩

/-- The smooth term of a Chapter 11 block proximal-gradient problem is proper. -/
instance instIsProperExtendedRealFunctionOfIsBlockProximalGradientProblem
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li) :
    IsProperExtendedRealFunction f :=
  h.f_proper

end IsBlockProximalGradientProblem

namespace BlockProximalGradientAssumptions

/-- The source-facing block proximal-gradient assumptions canonically induce the Chapter 10
composite smooth minimization owner for the aggregate regularizer
`x ↦ ∑ i, g_i(x_i)`. -/
-- Proof sketch: populate the Chapter 10 owner field-by-field from the Chapter 11 blockwise
-- assumptions and the separable-sum bridge lemmas for properness, closedness, and convexity.
theorem toIsCompositeSmoothMinimizationProblem
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h :
      BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    IsCompositeSmoothMinimizationProblem
      f (separableSum g) XStar FOpt Lf := by
  -- Populate the Chapter 10 owner directly from the Chapter 11 owner fields and the
  -- aggregate regularizer bridge lemmas available on `separableSum`.
  refine
    { f_ne_bot := h.f_ne_bot
      g_proper := separableSum_proper g h.block_g_proper
      f_closed := h.f_closed
      g_closed := separableSum_closed g h.block_g_closed
      g_convex := separableSum_convex g h.block_g_proper h.block_g_convex
      f_effective_domain_convex := h.f_effective_domain_convex
      g_effective_domain_subset_interior_f_effective_domain :=
        h.g_effective_domain_subset_interior_f_effective_domain
      f_toReal_smooth_on_interior_effective_domain :=
        h.f_toReal_smooth_on_interior_effective_domain
      optimal_set_eq := h.optimal_set_eq
      optimal_set_nonempty := h.optimal_set_nonempty
      optimal_value_isGLB := h.optimal_value_isGLB }

/-- The induced aggregate regularizer `x ↦ ∑ i, g_i(x_i)` is proper. -/
theorem separableSum_proper
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h :
      BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    IsProperExtendedRealFunction (separableSum g) :=
  (toIsCompositeSmoothMinimizationProblem h).g_proper

/-- The aggregate regularizer `separableSum g` is proper under the Chapter 11 block assumptions.
-/
instance instIsProperExtendedRealFunctionSeparableSumOfBlockProximalGradientAssumptions
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h :
      BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    IsProperExtendedRealFunction (separableSum g) :=
  h.separableSum_proper

/-- The induced aggregate regularizer `x ↦ ∑ i, g_i(x_i)` is lower semicontinuous. -/
theorem separableSum_closed
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h :
      BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    LowerSemicontinuous (separableSum g) :=
  (toIsCompositeSmoothMinimizationProblem h).g_closed

/-- The aggregate regularizer `separableSum g` is lower semicontinuous under the Chapter 11 block
assumptions. -/
instance instFactLowerSemicontinuousSeparableSumOfBlockProximalGradientAssumptions
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h :
      BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    Fact (LowerSemicontinuous (separableSum g)) :=
  ⟨h.separableSum_closed⟩

/-- The induced aggregate regularizer `x ↦ ∑ i, g_i(x_i)` is convex. -/
theorem separableSum_convex
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h :
      BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    is_convex_function (separableSum g) :=
  (toIsCompositeSmoothMinimizationProblem h).g_convex

/-- The aggregate regularizer `separableSum g` is convex under the Chapter 11 block assumptions.
-/
instance instFactIsConvexFunctionSeparableSumOfBlockProximalGradientAssumptions
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h :
      BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    Fact (is_convex_function (separableSum g)) :=
  ⟨h.separableSum_convex⟩

/-- The aggregate `PiLp` regularizer `x ↦ ∑ i, g_i(x_i)` is proper under the Chapter 11 block
assumptions. -/
theorem piLp_separableSum_proper
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h :
      BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    IsProperExtendedRealFunction (PiLp.separableSum g) := by
  letI : IsProperExtendedRealFunction (separableSum g) := h.separableSum_proper
  exact PiLp.instIsProperExtendedRealFunctionSeparableSum g

/-- The aggregate `PiLp` regularizer `x ↦ ∑ i, g_i(x_i)` is lower semicontinuous under the
Chapter 11 block assumptions. -/
theorem piLp_separableSum_closed
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h :
      BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    Fact (LowerSemicontinuous (PiLp.separableSum g)) := by
  letI : Fact (LowerSemicontinuous (separableSum g)) := ⟨h.separableSum_closed⟩
  exact PiLp.instFactLowerSemicontinuousSeparableSum g

/-- The aggregate `PiLp` regularizer `x ↦ ∑ i, g_i(x_i)` is convex under the Chapter 11 block
assumptions. -/
theorem piLp_separableSum_convex
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h :
      BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    Fact (is_convex_function (PiLp.separableSum g)) := by
  letI : Fact (is_convex_function (separableSum g)) := ⟨h.separableSum_convex⟩
  exact PiLp.instFactIsConvexFunctionSeparableSum g

/-- The Chapter 10 prox-gradient operator on the canonical aggregate `PiLp` owner induced by the
Chapter 11 block assumptions. This is a thin `bridge/view`: it reuses `T[...]` and supplies only
the derived regularity facts for `PiLp.separableSum g`. -/
abbrev aggregate_prox_grad_operator
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    [ProperSpace (PiLp 2 Ei)]
    (h : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (L : PosReal) : PiLp 2 Ei → PiLp 2 Ei :=
  let _ : IsProperExtendedRealFunction (PiLp.separableSum g) := h.piLp_separableSum_proper
  let _ : Fact (LowerSemicontinuous (PiLp.separableSum g)) := h.piLp_separableSum_closed
  let _ : Fact (is_convex_function (PiLp.separableSum g)) := h.piLp_separableSum_convex
  prox_gradient_operator (fun z ↦ (f z).toReal) (PiLp.separableSum g) L

/-- The Chapter 10 gradient mapping on the canonical aggregate `PiLp` owner induced by the
Chapter 11 block assumptions. This is the companion `bridge/view` to
`aggregate_prox_grad_operator`. -/
abbrev aggregate_gradient_mapping
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    [ProperSpace (PiLp 2 Ei)]
    (h : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (L : PosReal) : PiLp 2 Ei → PiLp 2 Ei :=
  let _ : IsProperExtendedRealFunction (PiLp.separableSum g) := h.piLp_separableSum_proper
  let _ : Fact (LowerSemicontinuous (PiLp.separableSum g)) := h.piLp_separableSum_closed
  let _ : Fact (is_convex_function (PiLp.separableSum g)) := h.piLp_separableSum_convex
  prox_gradient_mapping (fun z ↦ (f z).toReal) (PiLp.separableSum g) L

/-- The Chapter 10 smoothness owner reused by Definition 11.4 already implies differentiability
of `x ↦ (f x).toReal` on `interior (effective_domain f)`. -/
-- Proof sketch: the `L_f`-smoothness field in the induced Chapter 10 owner yields a derivative at
-- each interior-domain point, hence differentiability on that set.
theorem f_toReal_differentiableOn_interior_effective_domain
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h :
      BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    DifferentiableOn ℝ (fun x ↦ (f x).toReal) (interior (effective_domain f)) := by
  intro x hx
  -- Smoothness on the interior gives pointwise differentiability there, and `DifferentiableOn`
  -- is the within-set version of that pointwise statement.
  have hsmooth :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf :=
    (toIsCompositeSmoothMinimizationProblem h).f_toReal_smooth_on_interior_effective_domain
  exact (hsmooth.1 x hx).differentiableWithinAt

end BlockProximalGradientAssumptions

end
