/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_41

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace (nonnegativeOrthant)
open scoped StandardSimplex

variable {n : ℕ} {m : ℕ+}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Δₙ" => Δ[n]

/- Proposition 7.18 lies in Chapter 7's linear-packing / simplex-normalization domain.

Sampled owner-style declarations:
- `LinearPackingProblem`, `LinearPackingProblem.gauge`, `LinearPackingProblem.scaledGauge`,
  `LinearPackingProblem.mem_feasibleSet_iff`, and `LinearPackingProblem.optimalValue` in
  `Chap07/Definition_7_41`, the chapter owner carrying the packing data `(a_i, b, c)` together
  with the positivity assumptions `b_i > 0` and `c_j > 0`;
- `maxTypeObjective` and `maxTypeObjective_le_iff` in `Chap02/Lemma_2_18`, the chapter owner for
  finite maxima over a nonempty family;
- `stdSimplex` and the Chapter 6 notation `Δ[n]` in `Chap06/Definition_6_11`, the canonical owner
  of the standard simplex.

Best owner abstraction:
- source-facing: Proposition 7.18's reciprocal normalized formulations of the packing value `ψ*`;
- core/canonical: `LinearPackingProblem (m : ℕ) n`, its owner value `problem.optimalValue`, the
  feasible-set owner `problem.feasibleSet`, `maxTypeObjective`, and `Δ[n]`;
- bridge/view: the normalized constraint gauge `problem.gauge`, the derived feasibility criterion
  `problem.gauge ≤ 1`, the normalized slice `problem.normalizedSlice`, and the simplex rescaling
  `problem.scaledGauge`.

Primitive data:
- one owner `problem : LinearPackingProblem (m : ℕ) n`.

Derived API:
- the gauge `y ↦ max_i ⟪a_i, y⟫ / b_i`;
- the equivalent gauge presentation of `problem.feasibleSet`;
- the normalized slice `problem.normalizedSlice = {y ∈ ℝⁿ_+ | ⟪c, y⟫ = 1}`;
- the simplex gauge obtained from the diagonal change of variables `x_j = c_j y_j`.

This refinement removes the duplicate local supremum owner. Proposition 7.18 is now stated
directly on the chapter packing owner `LinearPackingProblem.optimalValue : EReal`, while the
textbook ratio expressions are kept as thin source-facing bridge theorems, with the reciprocal
recorded through `ℝ≥0∞` so the zero-minimum and empty-slice regimes remain faithful. -/

namespace LinearPackingProblem

-- Proof sketch: use `problem.mem_feasibleSet_iff` to rewrite feasibility as the coordinatewise
-- inequalities `⟪a_i, y⟫ ≤ b_i`, then divide by the positive owner data `b_i > 0` and collect the
-- resulting family through `maxTypeObjective_le_iff`.
/-- The packing-feasibility condition is equivalently the gauge inequality
`max_i (⟪a_i, y⟫ / b_i) ≤ 1`. -/
theorem mem_feasibleSet_iff_gauge_le_one
    (problem : LinearPackingProblem (m : ℕ) n) {y : E} :
    y ∈ problem.feasibleSet ↔ y ∈ nonnegativeOrthant n ∧ problem.gauge y ≤ 1 := by
  rw [problem.mem_feasibleSet_iff, gauge]
  constructor
  · intro hy
    refine ⟨hy.1, ?_⟩
    rw [maxTypeObjective_le_iff]
    intro i
    have hi : inner ℝ (problem.a i) y ≤ 1 * problem.b i := by
      simpa using hy.2 i
    exact (_root_.div_le_iff₀ (problem.b_pos_apply i)).2 hi
  · rintro ⟨hy_nonneg, hy_gauge⟩
    refine ⟨hy_nonneg, ?_⟩
    rw [maxTypeObjective_le_iff] at hy_gauge
    intro i
    have hi : inner ℝ (problem.a i) y / problem.b i ≤ 1 := by
      simpa using hy_gauge i
    have hi' : inner ℝ (problem.a i) y ≤ 1 * problem.b i :=
      (_root_.div_le_iff₀ (problem.b_pos_apply i)).1 hi
    simpa using hi'

/-- Helper for Proposition 7.18: the packing objective is nonnegative on the nonnegative orthant. -/
private theorem objective_nonneg_of_mem_nonnegativeOrthant
    (problem : LinearPackingProblem (m : ℕ) n) {y : E} (hy : y ∈ nonnegativeOrthant n) :
    0 ≤ problem.objective y := by
  -- Rewrite the objective as a coordinate dot product with nonnegative terms.
  have hc : 0 ≤ (problem.c : Fin n → ℝ) := by
    intro j
    exact (problem.c_pos_apply j).le
  have hy' : 0 ≤ (y : Fin n → ℝ) := by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hy
  have hdot : 0 ≤ dotProduct problem.c y := dotProduct_nonneg_of_nonneg hc hy'
  have hinner : inner ℝ problem.c y = dotProduct problem.c y := by
    have hraw := EuclideanSpace.inner_eq_star_dotProduct problem.c y
    simpa [dotProduct_comm] using hraw
  rw [LinearPackingProblem.objective, hinner]
  exact hdot

/-- Helper for Proposition 7.18: the packing gauge is nonnegative on the nonnegative orthant. -/
private theorem gauge_nonneg_of_mem_nonnegativeOrthant
    (problem : LinearPackingProblem (m : ℕ) n) {y : E} (hy : y ∈ nonnegativeOrthant n) :
    0 ≤ problem.gauge y := by
  -- Each constraint ratio is nonnegative, so their finite maximum is also nonnegative.
  have hy' : 0 ≤ (y : Fin n → ℝ) := by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hy
  have hinner_nonneg : ∀ i : Fin (m : ℕ), 0 ≤ inner ℝ (problem.a i) y := by
    intro i
    have ha : 0 ≤ (problem.a i : Fin n → ℝ) := by
      intro j
      exact problem.a_nonneg_apply i j
    have hdot : 0 ≤ dotProduct (problem.a i) y := dotProduct_nonneg_of_nonneg ha hy'
    have hinner : inner ℝ (problem.a i) y = dotProduct (problem.a i) y := by
      have hraw := EuclideanSpace.inner_eq_star_dotProduct (problem.a i) y
      simpa [dotProduct_comm] using hraw
    rw [hinner]
    exact hdot
  rw [gauge, maxTypeObjective_apply]
  let f : Fin (m : ℕ) → ℝ := fun i ↦ inner ℝ (problem.a i) y / problem.b i
  have hne : Nonempty (Fin (m : ℕ)) := inferInstance
  rcases hne with ⟨i⟩
  have hfi : 0 ≤ f i := by
    dsimp [f]
    exact div_nonneg (hinner_nonneg i) (problem.b_pos_apply i).le
  exact le_trans hfi (Finset.le_sup' f (by simp))

/-- Helper for Proposition 7.18: a nonnegative scalar factors through the finite gauge maximum. -/
private theorem gauge_finset_smul_max
    (problem : LinearPackingProblem (m : ℕ) n) (y : E) {t : ℝ} (ht : 0 ≤ t) :
    Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (m : ℕ) ↦ inner ℝ (problem.a i) (t • y) / problem.b i) =
      t * Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (m : ℕ) ↦ inner ℝ (problem.a i) y / problem.b i) := by
  let f : Fin (m : ℕ) → ℝ := fun i ↦ inner ℝ (problem.a i) y / problem.b i
  have hrewrite :
      Finset.univ.sup' Finset.univ_nonempty
          (fun i : Fin (m : ℕ) ↦ inner ℝ (problem.a i) (t • y) / problem.b i) =
        Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (m : ℕ) ↦ t * f i) := by
    -- Rewrite each component after pulling the scalar through the inner product.
    refine Finset.sup'_congr Finset.univ_nonempty rfl ?_
    intro i hi
    dsimp [f]
    rw [inner_smul_right, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
  rw [hrewrite]
  refine le_antisymm ?_ ?_
  · -- The scaled family is bounded above by scaling the unscaled finite maximum.
    rw [Finset.sup'_le_iff]
    intro i hi
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' f hi) ht
  · obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
    -- Evaluating at an index attaining the original maximum gives the reverse inequality.
    rw [hsup]
    exact Finset.le_sup' (fun j : Fin (m : ℕ) ↦ t * f j) hi

/-- Helper for Proposition 7.18: the gauge is positively homogeneous. -/
private theorem gauge_smul_of_nonneg
    (problem : LinearPackingProblem (m : ℕ) n) (y : E) {t : ℝ} (ht : 0 ≤ t) :
    problem.gauge (t • y) = t * problem.gauge y := by
  -- Expand the max-type objective and extract the common nonnegative scalar.
  change
    Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (m : ℕ) ↦ inner ℝ (problem.a i) (t • y) / problem.b i) =
      t * Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (m : ℕ) ↦ inner ℝ (problem.a i) y / problem.b i)
  exact problem.gauge_finset_smul_max y ht

/-- Helper for Proposition 7.18: every feasible point contributes its objective value below the
packing optimum. -/
private theorem feasible_value_le_optimalValue
    (problem : LinearPackingProblem (m : ℕ) n) {z : E} (hz : z ∈ problem.feasibleSet) :
    ((problem.objective z : ℝ) : EReal) ≤ problem.optimalValue := by
  -- Open the owner supremum once and insert the explicit feasible witness.
  rw [problem.optimalValue_eq_sSup_image]
  exact le_sSup (Set.mem_image_of_mem (fun y ↦ (problem.objective y : EReal)) hz)

/-- Helper for Proposition 7.18: positive gauge lets us rescale a normalized-slice point onto the
feasible boundary with reciprocal objective value. -/
private theorem rescale_normalizedSlice_mem_feasible_of_gauge_pos
    (problem : LinearPackingProblem (m : ℕ) n) {y : E}
    (hy : y ∈ problem.normalizedSlice) (hg : 0 < problem.gauge y) :
    (problem.gauge y)⁻¹ • y ∈ problem.feasibleSet ∧
      problem.objective ((problem.gauge y)⁻¹ • y) = (problem.gauge y)⁻¹ := by
  rcases problem.mem_normalizedSlice_iff.mp hy with ⟨hy_nonneg, hy_obj⟩
  have hy_coords : ∀ j : Fin n, 0 ≤ y j := by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hy_nonneg
  have h_inv_nonneg : 0 ≤ (problem.gauge y)⁻¹ := inv_nonneg.2 hg.le
  constructor
  · -- The reciprocal rescaling preserves the orthant and normalizes the gauge to `1`.
    rw [problem.mem_feasibleSet_iff_gauge_le_one]
    constructor
    · simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using
        (fun j : Fin n ↦ mul_nonneg h_inv_nonneg (hy_coords j))
    · rw [problem.gauge_smul_of_nonneg y h_inv_nonneg]
      norm_num [hg.ne']
  · -- The same rescaling turns the slice equation `⟪c, y⟫ = 1` into the reciprocal objective.
    rw [LinearPackingProblem.objective, inner_smul_right, hy_obj, mul_one]

/-- Helper for Proposition 7.18: a normalized-slice point with zero gauge yields an unbounded
feasible ray, so the packing optimum is `⊤`. -/
private theorem optimalValue_eq_top_of_normalizedSlice_gauge_eq_zero
    (problem : LinearPackingProblem (m : ℕ) n) {y : E}
    (hy : y ∈ problem.normalizedSlice) (hg0 : problem.gauge y = 0) :
    problem.optimalValue = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro r
  rcases problem.mem_normalizedSlice_iff.mp hy with ⟨hy_nonneg, hy_obj⟩
  have hy_coords : ∀ j : Fin n, 0 ≤ y j := by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hy_nonneg
  let t : ℝ := max r 0 + 1
  have ht_pos : 0 < t := by
    dsimp [t]
    linarith [le_max_right r 0]
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have hfeasible : t • y ∈ problem.feasibleSet := by
    -- The whole ray stays feasible because the gauge remains zero under nonnegative scaling.
    rw [problem.mem_feasibleSet_iff_gauge_le_one]
    constructor
    · simpa [EuclideanSpace.mem_nonnegativeOrthant_iff, t] using
        (fun j : Fin n ↦ mul_nonneg ht_nonneg (hy_coords j))
    · rw [problem.gauge_smul_of_nonneg y ht_nonneg, hg0, mul_zero]
      norm_num
  have hvalue : ((t : ℝ) : EReal) ≤ problem.optimalValue := by
    -- This feasible ray point contributes its scaled objective value to the supremum.
    have hfeasible_value := problem.feasible_value_le_optimalValue hfeasible
    simpa [LinearPackingProblem.objective, inner_smul_right, hy_obj, t] using hfeasible_value
  have hrt : r < t := by
    dsimp [t]
    linarith [le_max_left r 0]
  exact lt_of_lt_of_le (by exact_mod_cast hrt) hvalue

/-- Helper for Proposition 7.18: a feasible point with positive objective normalizes onto the
slice `⟪c, y⟫ = 1`, and its normalized gauge is bounded by the reciprocal objective. -/
private theorem normalize_feasible_to_slice_of_objective_pos
    (problem : LinearPackingProblem (m : ℕ) n) {z : E}
    (hz : z ∈ problem.feasibleSet) (hobj : 0 < problem.objective z) :
    (problem.objective z)⁻¹ • z ∈ problem.normalizedSlice ∧
      problem.gauge ((problem.objective z)⁻¹ • z) ≤ (problem.objective z)⁻¹ := by
  rcases (problem.mem_feasibleSet_iff_gauge_le_one (y := z)).mp hz with ⟨hz_nonneg, hz_gauge⟩
  have hz_coords : ∀ j : Fin n, 0 ≤ z j := by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hz_nonneg
  have h_inv_nonneg : 0 ≤ (problem.objective z)⁻¹ := inv_nonneg.2 hobj.le
  constructor
  · -- Divide by the positive objective value to land on the normalized slice.
    rw [problem.mem_normalizedSlice_iff]
    constructor
    · simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using
        (fun j : Fin n ↦ mul_nonneg h_inv_nonneg (hz_coords j))
    · rw [LinearPackingProblem.objective, inner_smul_right]
      exact inv_mul_cancel₀ hobj.ne'
  · -- The feasible gauge inequality scales linearly under the same positive rescaling.
    rw [problem.gauge_smul_of_nonneg z h_inv_nonneg]
    calc
      (problem.objective z)⁻¹ * problem.gauge z ≤ (problem.objective z)⁻¹ * 1 := by
        exact mul_le_mul_of_nonneg_left hz_gauge h_inv_nonneg
      _ = (problem.objective z)⁻¹ := by ring

/-- Helper for Proposition 7.18: every feasible objective value is bounded above by the reciprocal
of the normalized-slice gauge infimum. -/
private theorem feasible_objective_le_inv_normalizedGaugeInf
    (problem : LinearPackingProblem (m : ℕ) n) {z : E} (hz : z ∈ problem.feasibleSet) :
    ((problem.objective z : ℝ) : EReal) ≤
      ((((sInf ((fun y ↦ ENNReal.ofReal (problem.gauge y)) '' problem.normalizedSlice))⁻¹ :
            ENNReal) : EReal)) := by
  let S : Set ENNReal := (fun y ↦ ENNReal.ofReal (problem.gauge y)) '' problem.normalizedSlice
  rcases (problem.mem_feasibleSet_iff_gauge_le_one (y := z)).mp hz with ⟨hz_nonneg, _⟩
  have hobj_nonneg : 0 ≤ problem.objective z :=
    problem.objective_nonneg_of_mem_nonnegativeOrthant hz_nonneg
  by_cases hobj0 : problem.objective z = 0
  · -- The zero-objective branch is immediate because the right-hand side is nonnegative.
    have hrhs_nonneg :
        (0 : EReal) ≤ ((((sInf S)⁻¹ : ENNReal) : EReal)) := by
      exact_mod_cast (show (0 : ENNReal) ≤ (sInf S)⁻¹ by exact bot_le)
    have hleft : ((problem.objective z : ℝ) : EReal) = 0 := by
      simpa [hobj0]
    rw [hleft]
    exact hrhs_nonneg
  · have hobj : 0 < problem.objective z := by
      exact lt_of_le_of_ne hobj_nonneg (by intro h; exact hobj0 h.symm)
    rcases problem.normalize_feasible_to_slice_of_objective_pos hz hobj with ⟨hy_mem, hy_gauge⟩
    have hsInf_le :
        sInf S ≤ ENNReal.ofReal (problem.gauge ((problem.objective z)⁻¹ • z)) := by
      exact sInf_le (Set.mem_image_of_mem (fun y ↦ ENNReal.ofReal (problem.gauge y)) hy_mem)
    have hto_objInv :
        ENNReal.ofReal (problem.gauge ((problem.objective z)⁻¹ • z)) ≤
          ENNReal.ofReal ((problem.objective z)⁻¹) := by
      exact ENNReal.ofReal_le_ofReal hy_gauge
    have hobj_le_scaled_inv :
        ENNReal.ofReal (problem.objective z) ≤
          (ENNReal.ofReal (problem.gauge ((problem.objective z)⁻¹ • z)))⁻¹ := by
      -- Reverse the normalized gauge bound by taking reciprocals in `ℝ≥0∞`.
      have htmp := ENNReal.inv_le_inv' hto_objInv
      rw [ENNReal.ofReal_inv_of_pos hobj, inv_inv] at htmp
      exact htmp
    have hscaled_inv_le :
        (ENNReal.ofReal (problem.gauge ((problem.objective z)⁻¹ • z)))⁻¹ ≤ (sInf S)⁻¹ := by
      -- The chosen slice witness dominates the infimum, so its reciprocal is bounded by the
      -- reciprocal infimum.
      exact ENNReal.inv_le_inv' hsInf_le
    have hmain :
        ENNReal.ofReal (problem.objective z) ≤ (sInf S)⁻¹ := by
      exact le_trans hobj_le_scaled_inv hscaled_inv_le
    -- Convert the final `ℝ≥0∞` inequality back to the requested `EReal` statement.
    have hcast :
        ((ENNReal.ofReal (problem.objective z) : ENNReal) : EReal) ≤
          ((((sInf S)⁻¹ : ENNReal) : EReal)) := by
      exact EReal.coe_ennreal_le_coe_ennreal_iff.2 hmain
    have hleft :
        ((problem.objective z : ℝ) : EReal) =
          ((ENNReal.ofReal (problem.objective z) : ENNReal) : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left hobj_nonneg]
    exact hleft.le.trans hcast

/-- Helper for Proposition 7.18: every normalized-slice point contributes its reciprocal gauge
value as a lower bound on the packing optimum. -/
private theorem normalizedSlice_reciprocal_le_optimalValue
    (problem : LinearPackingProblem (m : ℕ) n) {y : E} (hy : y ∈ problem.normalizedSlice) :
    ((((ENNReal.ofReal (problem.gauge y))⁻¹ : ENNReal) : EReal) ≤ problem.optimalValue) := by
  -- Route correction: separate the source ray proof into the zero-gauge unbounded branch and the
  -- positive-gauge feasible-rescaling branch before doing the final cast rewrite.
  by_cases hg0 : problem.gauge y = 0
  · -- Zero gauge produces a feasible ray of arbitrarily large objective, so the optimum is `⊤`.
    have htop := problem.optimalValue_eq_top_of_normalizedSlice_gauge_eq_zero hy hg0
    simpa [hg0, htop] using (le_rfl : (⊤ : EReal) ≤ ⊤)
  · have hy_nonneg : y ∈ nonnegativeOrthant n := (problem.mem_normalizedSlice_iff.mp hy).1
    have hg_nonneg : 0 ≤ problem.gauge y :=
      problem.gauge_nonneg_of_mem_nonnegativeOrthant hy_nonneg
    have hg : 0 < problem.gauge y := by
      exact lt_of_le_of_ne hg_nonneg (by intro h; exact hg0 h.symm)
    rcases problem.rescale_normalizedSlice_mem_feasible_of_gauge_pos hy hg with ⟨hz_feas, hz_obj⟩
    have hfeasible_value := problem.feasible_value_le_optimalValue hz_feas
    have hreal :
        (((problem.gauge y)⁻¹ : ℝ) : EReal) ≤ problem.optimalValue := by
      have hobj_cast :
          (((problem.gauge y)⁻¹ : ℝ) : EReal) =
            ((problem.objective ((problem.gauge y)⁻¹ • y) : ℝ) : EReal) := by
        exact_mod_cast hz_obj.symm
      exact hobj_cast.le.trans hfeasible_value
    have hcast :
        ((((ENNReal.ofReal (problem.gauge y))⁻¹ : ENNReal) : EReal)) =
          (((problem.gauge y)⁻¹ : ℝ) : EReal) := by
      rw [← ENNReal.ofReal_inv_of_pos hg, EReal.coe_ennreal_ofReal, max_eq_left]
      exact inv_nonneg.2 hg.le
    simpa [hcast] using hreal

-- Proof sketch: rescale any feasible nonnegative `y` by its positive `c`-pairing to land on the
-- slice `⟪c, y⟫ = 1`, compare the packing value with the reciprocal normalized gauge infimum, and
-- interpret that reciprocal in `ℝ≥0∞` so the zero-infimum / unbounded branch remains visible.
/-- Proposition 7.18: viewed in the canonical owner `EReal`, the packing value `ψ*` is the
reciprocal of the normalized gauge infimum on the slice `⟪c, y⟫ = 1`, with the reciprocal taken
in `ℝ≥0∞` so a zero infimum yields `⊤`. -/
theorem optimalValue_eq_inv_normalizedMin
    (problem : LinearPackingProblem (m : ℕ) n) :
    problem.optimalValue =
      (((sInf ((fun y ↦ ENNReal.ofReal (problem.gauge y)) '' problem.normalizedSlice))⁻¹ :
          ENNReal) : EReal) := by
  let S : Set ENNReal := (fun y ↦ ENNReal.ofReal (problem.gauge y)) '' problem.normalizedSlice
  have hupper :
      problem.optimalValue ≤ ((((sInf S)⁻¹ : ENNReal) : EReal)) := by
    -- The supremum over feasible objective values is bounded by the reciprocal slice infimum.
    rw [problem.optimalValue_eq_sSup_image]
    refine sSup_le ?_
    intro w hw
    rcases hw with ⟨z, hz, rfl⟩
    simpa [S] using problem.feasible_objective_le_inv_normalizedGaugeInf hz
  have hzero_feasible : (0 : E) ∈ problem.feasibleSet := by
    -- The origin is feasible, so the packing optimum is nonnegative.
    rw [problem.mem_feasibleSet_iff]
    constructor
    · simpa [EuclideanSpace.mem_nonnegativeOrthant_iff]
    · intro i
      simpa using (problem.b_pos_apply i).le
  have hopt_nonneg : (0 : EReal) ≤ problem.optimalValue := by
    simpa using problem.feasible_value_le_optimalValue hzero_feasible
  have hlower_toENNReal :
      (sInf S)⁻¹ ≤ problem.optimalValue.toENNReal := by
    -- Each normalized-slice reciprocal lies below the optimum, so their supremum does too.
    rw [ENNReal.inv_sInf]
    refine iSup_le ?_
    intro a
    refine iSup_le ?_
    intro ha
    rcases ha with ⟨y, hy, rfl⟩
    have hy_bound := problem.normalizedSlice_reciprocal_le_optimalValue hy
    simpa [S] using EReal.toENNReal_le_toENNReal hy_bound
  have hlower :
      ((((sInf S)⁻¹ : ENNReal) : EReal)) ≤ problem.optimalValue := by
    -- Convert the `ℝ≥0∞` lower bound back to `EReal` using nonnegativity of the optimum.
    have hcast :
        ((((sInf S)⁻¹ : ENNReal) : EReal)) ≤ ((problem.optimalValue.toENNReal : ENNReal) : EReal) := by
      exact EReal.coe_ennreal_le_coe_ennreal_iff.2 hlower_toENNReal
    simpa [EReal.coe_toENNReal hopt_nonneg] using hcast
  exact le_antisymm hupper hlower

/-- Helper for Proposition 7.18: the diagonal change of variables `x_j = c_j y_j`. -/
private def sliceToSimplexCoords
    (problem : LinearPackingProblem (m : ℕ) n) (y : E) : Fin n → ℝ :=
  fun j ↦ problem.c j * y j

/-- Helper for Proposition 7.18: the forward diagonal substitution cancels inside the coordinate
dot product. -/
private theorem diagonal_dotProduct_slice
    (problem : LinearPackingProblem (m : ℕ) n) (u y : E) :
    dotProduct (fun j ↦ u j / problem.c j) (problem.sliceToSimplexCoords y) = inner ℝ u y := by
  -- Rewrite the inner product as a coordinate sum and cancel the positive diagonal entries.
  have hinner : inner ℝ u y = dotProduct u y := by
    have hraw := EuclideanSpace.inner_eq_star_dotProduct u y
    simpa [dotProduct_comm] using hraw
  rw [hinner, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [sliceToSimplexCoords]
  field_simp [(problem.c_pos_apply j).ne']

/-- Helper for Proposition 7.18: the slice coordinates `x_j = c_j y_j` lie in the simplex. -/
private theorem sliceToSimplexCoords_mem_stdSimplex
    (problem : LinearPackingProblem (m : ℕ) n) {y : E} (hy : y ∈ problem.normalizedSlice) :
    problem.sliceToSimplexCoords y ∈ Δₙ := by
  rcases problem.mem_normalizedSlice_iff.mp hy with ⟨hy_nonneg, hy_norm⟩
  have hy_coords : ∀ j : Fin n, 0 ≤ y j := by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hy_nonneg
  -- Expand simplex membership into coordinatewise nonnegativity and total mass one.
  change (∀ j, 0 ≤ problem.sliceToSimplexCoords y j) ∧
      ∑ j, problem.sliceToSimplexCoords y j = 1
  constructor
  · intro j
    simp [sliceToSimplexCoords, hy_coords j]
  · have hinner : inner ℝ problem.c y = dotProduct problem.c y := by
      have hraw := EuclideanSpace.inner_eq_star_dotProduct problem.c y
      simpa [dotProduct_comm] using hraw
    rw [hinner] at hy_norm
    simpa [sliceToSimplexCoords, dotProduct] using hy_norm

/-- Helper for Proposition 7.18: package the diagonal slice coordinates as a simplex point. -/
private def sliceToSimplex
    (problem : LinearPackingProblem (m : ℕ) n) (y : E) (hy : y ∈ problem.normalizedSlice) : Δₙ :=
  ⟨problem.sliceToSimplexCoords y, problem.sliceToSimplexCoords_mem_stdSimplex hy⟩

/-- Helper for Proposition 7.18: the slice gauge matches the simplex scaled gauge after the
diagonal change of variables. -/
private theorem gauge_eq_scaledGauge_sliceToSimplex
    (problem : LinearPackingProblem (m : ℕ) n) {y : E} (hy : y ∈ problem.normalizedSlice) :
    problem.gauge y = problem.scaledGauge (problem.sliceToSimplex y hy) := by
  -- Rewrite each simplex-gauge component by the diagonal cancellation lemma.
  rw [gauge, scaledGauge, maxTypeObjective_apply, maxTypeObjective_apply]
  refine Finset.sup'_congr Finset.univ_nonempty rfl ?_
  intro i hi
  simpa [sliceToSimplex] using
    congrArg (fun z : ℝ ↦ z / problem.b i)
      (problem.diagonal_dotProduct_slice (u := problem.a i) (y := y)).symm

/-- Helper for Proposition 7.18: the inverse diagonal change of variables `y_j = x_j / c_j`. -/
private def simplexToSliceCoords
    (problem : LinearPackingProblem (m : ℕ) n) (x : Δₙ) : E :=
  WithLp.toLp 2 (fun j ↦ x.1 j / problem.c j)

/-- Helper for Proposition 7.18: the inverse diagonal substitution cancels inside the objective
and gauge inner products. -/
private theorem diagonal_inner_simplexToSlice
    (problem : LinearPackingProblem (m : ℕ) n) (u : E) (x : Δₙ) :
    inner ℝ u (problem.simplexToSliceCoords x) =
      dotProduct (fun j ↦ u j / problem.c j) x.1 := by
  -- Expand the Euclidean inner product into coordinates and move the inverse factor across.
  have hinner : inner ℝ u (problem.simplexToSliceCoords x) =
      dotProduct u (problem.simplexToSliceCoords x) := by
    have hraw := EuclideanSpace.inner_eq_star_dotProduct u (problem.simplexToSliceCoords x)
    simpa [dotProduct_comm] using hraw
  rw [hinner, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro j hj
  simpa [simplexToSliceCoords, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Proposition 7.18: dividing simplex coordinates by the positive diagonal entries
lands on the normalized slice. -/
private theorem simplexToSlice_mem_normalizedSlice
    (problem : LinearPackingProblem (m : ℕ) n) (x : Δₙ) :
    problem.simplexToSliceCoords x ∈ problem.normalizedSlice := by
  have hx_nonneg : ∀ j : Fin n, 0 ≤ x.1 j := x.2.1
  have hx_sum : ∑ j, x.1 j = 1 := x.2.2
  rw [problem.mem_normalizedSlice_iff]
  constructor
  · -- Positive diagonal entries preserve nonnegativity after division.
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff, simplexToSliceCoords] using
      (fun j : Fin n ↦ div_nonneg (hx_nonneg j) (problem.c_pos_apply j).le)
  · -- With `u = c`, the diagonal cancellation lemma turns the objective into the simplex mass.
    calc
      inner ℝ problem.c (problem.simplexToSliceCoords x)
          = dotProduct (fun j ↦ problem.c j / problem.c j) x.1 := by
              simpa using problem.diagonal_inner_simplexToSlice (u := problem.c) (x := x)
      _ = ∑ j, x.1 j := by
            rw [dotProduct]
            refine Finset.sum_congr rfl ?_
            intro j hj
            field_simp [(problem.c_pos_apply j).ne']
      _ = 1 := hx_sum

/-- Helper for Proposition 7.18: the inverse diagonal substitution recovers the simplex scaled
gauge value. -/
private theorem gauge_simplexToSlice_eq_scaledGauge
    (problem : LinearPackingProblem (m : ℕ) n) (x : Δₙ) :
    problem.gauge (problem.simplexToSliceCoords x) = problem.scaledGauge x := by
  -- Rewrite each gauge component by the inverse diagonal cancellation lemma.
  rw [gauge, scaledGauge, maxTypeObjective_apply, maxTypeObjective_apply]
  refine Finset.sup'_congr Finset.univ_nonempty rfl ?_
  intro i hi
  simpa using
    congrArg (fun z : ℝ ↦ z / problem.b i)
      (problem.diagonal_inner_simplexToSlice (u := problem.a i) (x := x))

/-- Helper for Proposition 7.18: the normalized-slice gauge image equals the simplex scaled-gauge
range. -/
private theorem normalizedGaugeImage_eq_scaledGaugeRange
    (problem : LinearPackingProblem (m : ℕ) n) :
    ((fun y ↦ ENNReal.ofReal (problem.gauge y)) '' problem.normalizedSlice) =
      Set.range (fun x : Δₙ ↦ ENNReal.ofReal (problem.scaledGauge x)) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    -- Every slice point maps to the corresponding simplex point by `x_j = c_j y_j`.
    refine ⟨problem.sliceToSimplex y hy, ?_⟩
    simp [problem.gauge_eq_scaledGauge_sliceToSimplex hy]
  · rintro ⟨x, rfl⟩
    -- Every simplex point maps back by dividing coordinates by the positive diagonal.
    refine ⟨problem.simplexToSliceCoords x, problem.simplexToSlice_mem_normalizedSlice x, ?_⟩
    simp [problem.gauge_simplexToSlice_eq_scaledGauge x]

-- Proof sketch: apply the change of variables `x_j = c_j y_j`, use the owner positivity
-- `problem.c_pos_apply j` to identify the normalized orthant slice `⟪c, y⟫ = 1` with `Δ[n]`, and
-- rewrite the gauge in terms of the scaled rows `j ↦ aᵢⱼ / c_j`.
/-- The normalized orthant minimum from Proposition 7.18 is carried to the corresponding simplex
infimum by the diagonal rescaling determined by the positive objective vector `c`. -/
theorem normalizedMin_eq_simplexMin_scaledGauge
    (problem : LinearPackingProblem (m : ℕ) n) :
    sInf ((fun y ↦ ENNReal.ofReal (problem.gauge y)) '' problem.normalizedSlice) =
      sInf (Set.range fun x : Δₙ ↦ ENNReal.ofReal (problem.scaledGauge x)) := by
  -- The two infima agree because the slice image and simplex range are the same set.
  rw [problem.normalizedGaugeImage_eq_scaledGaugeRange]

-- Proof sketch: combine `optimalValue_eq_inv_normalizedMin` with the simplex reparametrization
-- `normalizedMin_eq_simplexMin_scaledGauge`.
/-- Proposition 7.18 in simplex form: the packing value `ψ*` is the reciprocal of the simplex
gauge infimum over `Δ_n`, with the reciprocal taken in `ℝ≥0∞` so a zero infimum yields `⊤` in the
canonical owner codomain `EReal`. -/
theorem optimalValue_eq_inv_simplexMin_scaledGauge
    (problem : LinearPackingProblem (m : ℕ) n) :
    problem.optimalValue =
      (((sInf (Set.range fun x : Δₙ ↦ ENNReal.ofReal (problem.scaledGauge x)))⁻¹ :
          ENNReal) : EReal) := by
  -- Combine the normalized-slice formula with the exact slice/simplex reparametrization.
  rw [problem.optimalValue_eq_inv_normalizedMin, problem.normalizedMin_eq_simplexMin_scaledGauge]

end LinearPackingProblem

end
