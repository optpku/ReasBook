/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v

noncomputable section

section SeparableSum

variable {ι : Type v} [Fintype ι]
variable {E : ι → Type u}

/-- The separable sum of coordinatewise extended-real-valued functions on a finite dependent
product. -/
def separableSum (f : ∀ i, E i → EReal) : ((i : ι) → E i) → EReal :=
  fun x ↦ ∑ i, f i (x i)

-- Proof sketch: unfold `separableSum`; it is definitionally the finite coordinatewise sum.
/-- Evaluating `separableSum f` at `x` gives the finite sum of the coordinate functions applied to
the corresponding coordinates of `x`. -/
@[simp] theorem separableSum_apply (f : ∀ i, E i → EReal) (x : (i : ι) → E i) :
    separableSum f x = ∑ i, f i (x i) :=
  rfl

namespace PiLp

/-- The canonical `PiLp` view of the owner `separableSum`, obtained by evaluating the same
coordinatewise sum on the underlying block family. -/
abbrev separableSum (f : ∀ i, E i → EReal) : PiLp (2 : ENNReal) E → EReal :=
  fun x ↦ _root_.separableSum f x

/-- Evaluating the `PiLp` view `PiLp.separableSum` gives the same coordinatewise finite sum. -/
@[simp] theorem separableSum_apply (f : ∀ i, E i → EReal) (x : PiLp (2 : ENNReal) E) :
    PiLp.separableSum f x = ∑ i, f i (x i) :=
  rfl

end PiLp

end SeparableSum

section PiLpSeparableSumRegularity

variable {ι : Type v} [Fintype ι]
variable {E : ι → Type u}
variable [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, InnerProductSpace ℝ (E i)]
variable [∀ i, CompleteSpace (E i)]

namespace PiLp

/-- The `PiLp` owner `PiLp.separableSum` inherits properness from the canonical owner
`_root_.separableSum` via the `L²` product equivalence. -/
instance instIsProperExtendedRealFunctionSeparableSum
    (f : ∀ i, E i → EReal) [IsProperExtendedRealFunction (_root_.separableSum f)] :
    IsProperExtendedRealFunction (PiLp.separableSum f) := by
  let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ E
  let hsum_proper : IsProperExtendedRealFunction (_root_.separableSum f) := inferInstance
  refine
    { ne_bot := ?_
      effective_domain_nonempty := ?_ }
  · intro z
    simpa [PiLp.separableSum, e] using hsum_proper.ne_bot (e z)
  · rcases hsum_proper.effective_domain_nonempty with ⟨z, hz⟩
    refine ⟨e.symm z, ?_⟩
    simpa [PiLp.separableSum, e, mem_effective_domain] using hz

/-- The `PiLp` owner `PiLp.separableSum` inherits lower semicontinuity from the canonical owner
`_root_.separableSum` by precomposition with the `L²` product equivalence. -/
instance instFactLowerSemicontinuousSeparableSum
    (f : ∀ i, E i → EReal) [Fact (LowerSemicontinuous (_root_.separableSum f))] :
    Fact (LowerSemicontinuous (PiLp.separableSum f)) := by
  let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ E
  let hsum_closed : LowerSemicontinuous (_root_.separableSum f) := Fact.out
  exact ⟨by
    simpa [Function.comp, PiLp.separableSum, e] using hsum_closed.comp e.continuous⟩

/-- The `PiLp` owner `PiLp.separableSum` inherits convexity from the canonical owner
`_root_.separableSum` by precomposition with the `L²` product equivalence. -/
instance instFactIsConvexFunctionSeparableSum
    (f : ∀ i, E i → EReal) [Fact (is_convex_function (_root_.separableSum f))] :
    Fact (is_convex_function (PiLp.separableSum f)) := by
  let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ E
  let hsum_convex : is_convex_function (_root_.separableSum f) := Fact.out
  exact ⟨by
    simpa [PiLp.separableSum, e] using
      is_convex_function_precompose_linearMap_add hsum_convex e.toLinearMap 0⟩

end PiLp

end PiLpSeparableSumRegularity

section SeparableProx

variable {ι : Type v} [Fintype ι]
variable {E : ι → Type u}
variable [∀ i, NormedAddCommGroup (E i)]

/- Theorem 6.6 is `source-facing`: it asserts that the proximal operator of a separable sum on a
finite product is the product of the coordinatewise proximal operators. Domain sampling shows that
the canonical proximal owner already exists upstream as Chapter 6's set-valued mapping
`prox[...]`, while the genuinely new source-facing object here is only the coordinatewise finite
sum `separableSum`; on `PiLp (2 : ENNReal) E` it is used through the thin bridge
`PiLp.separableSum`. For
`EReal`-valued summands, the separability claim needs the textbook properness of each coordinate
function: no summand may take `⊥`, and every summand must have a nonempty finite domain. The
nonempty-domain part rules out degenerate everywhere-`⊤` coordinates, which would make the
product-space proximal objective identically `⊤` and destroy the coordinatewise product formula.
The theorem is therefore stated directly on `prox[...]`, with the product set expressed by
coordinatewise proximal membership and with coordinatewise properness retained from the textbook
closed proper convex setting.
-/

-- Proof sketch: unfold `prox[PiLp.separableSum f] x` and `prox[f i] (x i)` via
-- `mem_proximal_mapping_iff`, then unfold `proximal_objective` and `PiLp.separableSum`. Use
-- `PiLp.norm_sq_eq_of_L2` to rewrite the product-space quadratic term as the sum of the
-- coordinatewise quadratic terms. Properness supplies both the no-`⊥` condition and a finite
-- comparison point in every coordinate, so points with a `⊤` coordinate cannot become vacuous
-- minimizers of an identically infinite product objective. Under these hypotheses, `IsMinOn` over
-- `Set.univ` separates into the conjunction that each coordinate is a minimizer of its own
-- proximal objective.
-- Theorem 6.6 is proved below after the local coordinate-separation helpers.
/-- Helper for Theorem 6.6: coercing a finite real sum into `EReal` agrees with summing the
coerced real terms. -/
lemma ereal_coe_sum {κ : Type*} (s : Finset κ) (φ : κ → ℝ) :
    (((∑ i ∈ s, φ i : ℝ) : EReal)) = ∑ i ∈ s, ((φ i : ℝ) : EReal) := by
  classical
  -- Induct over the finite set and push the coercion through one inserted term at a time.
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, hs]

/-- Helper for Theorem 6.6: the proximal objective of a separable sum is the finite sum of the
coordinatewise proximal objectives. -/
lemma separable_proximal_objective_eq_sum_coordinate_objectives
    (f : ∀ i, E i → EReal) (x y : PiLp (2 : ENNReal) E) :
    proximal_objective (PiLp.separableSum f) x y =
      ∑ i, proximal_objective (f i) (x i) (y i) := by
  -- Expand both the separable term and the `L²` penalty into coordinatewise finite sums.
  rw [proximal_objective_apply, PiLp.separableSum_apply, PiLp.norm_sq_eq_of_L2]
  simp_rw [PiLp.sub_apply]
  have hquad :
      ((((1 / 2 : ℝ) * ∑ i, ‖y i - x i‖ ^ (2 : ℕ)) : ℝ) : EReal) =
        ∑ i, ((((1 / 2 : ℝ) * ‖y i - x i‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
    rw [Finset.mul_sum]
    simpa using
      (ereal_coe_sum Finset.univ
        (fun i : ι ↦ (1 / 2 : ℝ) * ‖y i - x i‖ ^ (2 : ℕ)))
  -- After distributing the quadratic penalty, each coordinate contributes independently.
  rw [hquad, ← Finset.sum_add_distrib]
  simp [proximal_objective_apply]

/-- Helper for Theorem 6.6: a finite sum of extended-real terms is never `⊥` when no summand is
`⊥`. -/
lemma ereal_sum_ne_bot {κ : Type*} (s : Finset κ) (φ : κ → EReal)
    (hφ : ∀ i ∈ s, φ i ≠ ⊥) :
    (∑ i ∈ s, φ i) ≠ ⊥ := by
  classical
  revert hφ
  refine Finset.induction_on s ?_ ?_
  · intro hφ
    simp
  · intro a s ha hs hφ
    -- Split off the head term and use `EReal.add_ne_bot_iff`.
    rw [Finset.sum_insert ha, EReal.add_ne_bot_iff]
    refine ⟨hφ a (by simp), hs ?_⟩
    intro i hi
    exact hφ i (by simp [hi])

/-- Helper for Theorem 6.6: a finite sum of extended-real terms is `< ⊤` when every summand is
`< ⊤`. -/
lemma ereal_sum_lt_top {κ : Type*} (s : Finset κ) (φ : κ → EReal)
    (hφ : ∀ i ∈ s, φ i < ⊤) :
    (∑ i ∈ s, φ i) < ⊤ := by
  classical
  revert hφ
  refine Finset.induction_on s ?_ ?_
  · intro hφ
    simp
  · intro a s ha hs hφ
    have ha_top : φ a < ⊤ := hφ a (by simp)
    have hs_top : (∑ i ∈ s, φ i) < ⊤ := hs (fun i hi ↦ hφ i (by simp [hi]))
    -- Adding one more finite head term keeps the finite sum finite.
    rw [Finset.sum_insert ha]
    exact EReal.add_lt_top (lt_top_iff_ne_top.mp ha_top) (lt_top_iff_ne_top.mp hs_top)

/-- The finite block-separable objective `x ↦ ∑ i, f_i(x_i)` is proper when every coordinate
summand is proper. This generic regularity theorem belongs with the canonical owner
`separableSum`, so downstream chapters can reuse it without importing Chapter 11 problem-specific
APIs. -/
theorem separableSum_proper
    (f : ∀ i, E i → EReal)
    (hf_proper : ∀ i, IsProperExtendedRealFunction (f i)) :
    IsProperExtendedRealFunction (separableSum f) := by
  classical
  refine ⟨?_, ?_⟩
  · intro x
    rw [separableSum_apply]
    exact ereal_sum_ne_bot Finset.univ (fun i ↦ f i (x i))
      (fun i _ ↦ (hf_proper i).ne_bot (x i))
  · let x : (i : ι) → E i := fun i ↦ Classical.choose (hf_proper i).effective_domain_nonempty
    have hx : ∀ i, x i ∈ effective_domain (f i) := by
      intro i
      exact Classical.choose_spec (hf_proper i).effective_domain_nonempty
    refine ⟨x, ?_⟩
    rw [mem_effective_domain, separableSum_apply]
    exact ereal_sum_lt_top Finset.univ (fun i ↦ f i (x i))
      (fun i _ ↦ mem_effective_domain.mp (hx i))

/-- Typeclass form of `separableSum_proper` for the canonical finite-product owner
`separableSum`. -/
instance instIsProperExtendedRealFunctionSeparableSum
    (f : ∀ i, E i → EReal) [∀ i, IsProperExtendedRealFunction (f i)] :
    IsProperExtendedRealFunction (separableSum f) :=
  separableSum_proper f (fun i ↦ inferInstance)

/-- Helper for Theorem 6.6: a global minimizer of the separable proximal objective has finite
coordinatewise proximal objectives. -/
lemma coordinate_objective_lt_top_of_isMinOn_separable
    (f : ∀ i, E i → EReal) (hf_proper : ∀ i, IsProperExtendedRealFunction (f i))
    (x y : PiLp (2 : ENNReal) E)
    (hy : IsMinOn (proximal_objective (PiLp.separableSum f) x) Set.univ y) (i : ι) :
    proximal_objective (f i) (x i) (y i) < ⊤ := by
  classical
  let G : ∀ i, E i → EReal := fun j u ↦ proximal_objective (f j) (x j) u
  have hG_ne_bot : ∀ j u, G j u ≠ ⊥ := by
    intro j u
    -- Properness rules out `⊥`, and the quadratic term is always finite.
    simpa [G, proximal_objective_apply, EReal.add_ne_bot_iff] using
      (show f j u ≠ ⊥ ∧ ((((1 / 2 : ℝ) * ‖u - x j‖ ^ (2 : ℕ)) : ℝ) : EReal) ≠ ⊥ from
        ⟨(hf_proper j).ne_bot u, EReal.coe_ne_bot _⟩)
  choose w hw using fun j ↦ (hf_proper j).effective_domain_nonempty
  let z : PiLp (2 : ENNReal) E := WithLp.toLp 2 w
  have hGz_top : ∀ j, G j (z j) < ⊤ := by
    intro j
    -- The properness witness gives a finite function value, and the quadratic term is finite.
    have hw_top : f j (w j) < ⊤ := by
      simpa using hw j
    simpa [G, z, proximal_objective_apply] using
      EReal.add_lt_top (lt_top_iff_ne_top.mp hw_top) (EReal.coe_ne_top _)
  have hz_top : proximal_objective (PiLp.separableSum f) x z < ⊤ := by
    -- Summing the finite coordinate objectives keeps the comparison point finite.
    rw [separable_proximal_objective_eq_sum_coordinate_objectives]
    exact ereal_sum_lt_top Finset.univ (fun j ↦ G j (z j)) (fun j _ ↦ hGz_top j)
  have hy_univ :
      ∀ v,
        proximal_objective (PiLp.separableSum f) x y ≤
          proximal_objective (PiLp.separableSum f) x v :=
    isMinOn_univ_iff.mp hy
  have hy_top :
      proximal_objective (PiLp.separableSum f) x y < ⊤ :=
    lt_of_le_of_lt (hy_univ z) hz_top
  have hsum_y_top :
      (∑ j, G j (y j)) < ⊤ := by
    rw [← separable_proximal_objective_eq_sum_coordinate_objectives (f := f) (x := x) (y := y)]
    exact hy_top
  by_contra htop
  have hrest_ne_bot :
      Finset.sum (Finset.univ.erase i) (fun j ↦ G j (y j)) ≠ ⊥ :=
    ereal_sum_ne_bot (Finset.univ.erase i) (fun j ↦ G j (y j))
      (fun j hj ↦ hG_ne_bot j (y j))
  have hsum_eq_top : (∑ j, G j (y j)) = ⊤ := by
    -- A single `⊤` coordinate forces the whole finite sum to be `⊤`.
    calc
      ∑ j, G j (y j) = G i (y i) + Finset.sum (Finset.univ.erase i) (fun j ↦ G j (y j)) := by
        symm
        exact Finset.add_sum_erase Finset.univ (fun j ↦ G j (y j)) (Finset.mem_univ i)
      _ = ⊤ := by
        rw [
          show G i (y i) = ⊤ by exact le_antisymm le_top (not_lt.mp htop),
          EReal.top_add_of_ne_bot hrest_ne_bot
        ]
  exact (lt_top_iff_ne_top.mp hsum_y_top) hsum_eq_top

/-- Helper for Theorem 6.6: minimizing the separable proximal objective is equivalent to
minimizing each coordinatewise proximal objective. -/
lemma isMinOn_proximal_objective_separable_iff
    (f : ∀ i, E i → EReal) (hf_proper : ∀ i, IsProperExtendedRealFunction (f i))
    (x y : PiLp (2 : ENNReal) E) :
    IsMinOn (proximal_objective (PiLp.separableSum f) x) Set.univ y ↔
      ∀ i, IsMinOn (proximal_objective (f i) (x i)) Set.univ (y i) := by
  classical
  let G : ∀ i, E i → EReal := fun i u ↦ proximal_objective (f i) (x i) u
  have hG_ne_bot : ∀ i u, G i u ≠ ⊥ := by
    intro i u
    -- Properness rules out `⊥` at every coordinate objective.
    simpa [G, proximal_objective_apply, EReal.add_ne_bot_iff] using
      (show f i u ≠ ⊥ ∧ ((((1 / 2 : ℝ) * ‖u - x i‖ ^ (2 : ℕ)) : ℝ) : EReal) ≠ ⊥ from
        ⟨(hf_proper i).ne_bot u, EReal.coe_ne_bot _⟩)
  constructor
  · intro hy
    have hy_univ :
        ∀ z,
          proximal_objective (PiLp.separableSum f) x y ≤
            proximal_objective (PiLp.separableSum f) x z :=
      isMinOn_univ_iff.mp hy
    intro i
    rw [isMinOn_univ_iff]
    intro u
    let z : PiLp (2 : ENNReal) E := WithLp.toLp 2 (Function.update (fun j ↦ y j) i u)
    let r : EReal := Finset.sum (Finset.univ.erase i) (fun j ↦ G j (y j))
    have hr_ne_bot : r ≠ ⊥ := by
      -- The unchanged coordinates stay away from `⊥`.
      exact ereal_sum_ne_bot (Finset.univ.erase i) (fun j ↦ G j (y j))
        (fun j hj ↦ hG_ne_bot j (y j))
    have hGy_top : ∀ j, G j (y j) < ⊤ := by
      intro j
      exact coordinate_objective_lt_top_of_isMinOn_separable f hf_proper x y hy j
    have hr_top : r < ⊤ := by
      -- The unchanged remainder is finite because every coordinate objective at `y` is finite.
      exact ereal_sum_lt_top (Finset.univ.erase i) (fun j ↦ G j (y j))
        (fun j hj ↦ hGy_top j)
    have hr_coe : ((r.toReal : ℝ) : EReal) = r :=
      EReal.coe_toReal (lt_top_iff_ne_top.mp hr_top) hr_ne_bot
    have hyz :
        ∑ j, G j (y j) ≤ ∑ j, G j (z j) := by
      -- Rewrite the global minimizer inequality using the separable decomposition.
      rw [← separable_proximal_objective_eq_sum_coordinate_objectives (f := f) (x := x) (y := y),
        ← separable_proximal_objective_eq_sum_coordinate_objectives (f := f) (x := x) (y := z)]
      exact hy_univ z
    have hsum_y :
        ∑ j, G j (y j) = G i (y i) + r := by
      -- Split the finite sum into the `i`-th coordinate plus the unchanged remainder.
      calc
        ∑ j, G j (y j) = G i (y i) + Finset.sum (Finset.univ.erase i) (fun j ↦ G j (y j)) := by
          symm
          exact Finset.add_sum_erase Finset.univ (fun j ↦ G j (y j)) (Finset.mem_univ i)
        _ = G i (y i) + r := by simp [r]
    have hsum_z_rest :
        Finset.sum (Finset.univ.erase i) (fun j ↦ G j (z j)) =
          Finset.sum (Finset.univ.erase i) (fun j ↦ G j (y j)) := by
      -- Away from the updated coordinate, the new point has the same coordinates as `y`.
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [z, Function.update, hj_ne]
    have hsum_z :
        ∑ j, G j (z j) = G i u + r := by
      -- The update point changes only the `i`-th coordinate, so the remainder is identical.
      calc
        ∑ j, G j (z j) = G i (z i) + Finset.sum (Finset.univ.erase i) (fun j ↦ G j (z j)) := by
          symm
          exact Finset.add_sum_erase Finset.univ (fun j ↦ G j (z j)) (Finset.mem_univ i)
        _ = G i u + Finset.sum (Finset.univ.erase i) (fun j ↦ G j (z j)) := by
          simp [z, Function.update]
        _ = G i u + Finset.sum (Finset.univ.erase i) (fun j ↦ G j (y j)) := by
          rw [hsum_z_rest]
        _ = G i u + r := by simp [r]
    have hcancel :
        G i (y i) + ((r.toReal : ℝ) : EReal) ≤
          G i u + ((r.toReal : ℝ) : EReal) := by
      simpa [hsum_y, hsum_z, hr_coe] using hyz
    -- Cancel the common finite remainder to recover the coordinatewise minimizing inequality.
    exact ((EReal.addLECancellable_coe r.toReal).add_le_add_iff_right).mp hcancel
  · intro hy
    rw [isMinOn_univ_iff]
    intro z
    have hy_univ : ∀ i u, G i (y i) ≤ G i u := by
      intro i u
      exact isMinOn_univ_iff.mp (hy i) u
    -- Sum the coordinatewise minimizing inequalities to recover the product-space minimizer.
    rw [separable_proximal_objective_eq_sum_coordinate_objectives (f := f) (x := x) (y := y),
      separable_proximal_objective_eq_sum_coordinate_objectives (f := f) (x := x) (y := z)]
    exact Finset.sum_le_sum (fun i hi ↦ hy_univ i (z i))

/-- Theorem 6.6: for a separable extended-real-valued function on a finite Cartesian product,
the proximal operator at `x` is the set of points whose `i`-th coordinate lies in the proximal
operator of the `i`-th summand at `x i`. This is the textbook identity
`prox_f (x₁, …, x_m) = prox_{f₁} (x₁) × ⋯ × prox_{f_m} (x_m)` expressed on
`PiLp (2 : ENNReal) E`. -/
theorem prox_separableSum_eq_coordinatewise
    (f : ∀ i, E i → EReal) (hf_proper : ∀ i, IsProperExtendedRealFunction (f i))
    (x : PiLp (2 : ENNReal) E) :
    prox[PiLp.separableSum f] x = {y : PiLp (2 : ENNReal) E | ∀ i, y i ∈ prox[f i] (x i)} := by
  ext y
  -- Rewrite both sides as global minimizer statements and separate the finite sum by coordinates.
  rw [mem_proximal_mapping_iff,
    isMinOn_proximal_objective_separable_iff (f := f) (hf_proper := hf_proper) (x := x) (y := y)]
  simp [mem_proximal_mapping_iff]

-- Proof sketch: rewrite membership using `prox_separableSum_eq_coordinatewise`; membership in the
-- resulting set is exactly the coordinatewise proximal-membership condition.
/-- A point `y` belongs to the proximal set of a finite separable sum exactly when each coordinate
belongs to the proximal set of the corresponding summand. -/
@[simp] theorem mem_prox_separableSum_iff
    {f : ∀ i, E i → EReal} (hf_proper : ∀ i, IsProperExtendedRealFunction (f i))
    {x y : PiLp (2 : ENNReal) E} :
    y ∈ prox[PiLp.separableSum f] x ↔ ∀ i, y i ∈ prox[f i] (x i) := by
  rw [prox_separableSum_eq_coordinatewise f hf_proper x]
  rfl

end SeparableProx
