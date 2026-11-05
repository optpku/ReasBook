/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_2.ch8_sec8_2_1_example_8_15
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finsupp.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Domain sampling summary:
-- * primary domain: Gilmore-Gomory cutting-stock pattern families and their finite usage vectors
-- * sampled project owners:
--   - Example 8.15: `cutting_patterns`
--   - Example 8.15: `gilmore_gomory_feasible_set`
--   - Example 8.15: `gilmore_gomory_objective`
-- * source-facing layer here: finitely supported usage vectors on the canonical pattern owner
--   `cutting_patterns W w`
-- * core/canonical owners reused here: Example 8.15's feasible-set and objective declarations
-- * bridge/view added here: the active finite pattern family and its total multiplicity profile

noncomputable section Theorem819

variable {m : ℕ}

/-- A cutting-stock usage vector records finitely supported pattern multiplicities over the
canonical pattern owner `cutting_patterns W w`. -/
abbrev cutting_stock_usage (w : Fin m → ℕ) (W : ℕ) :=
  cutting_patterns W w →₀ ℕ

namespace cutting_stock_usage

/-- The finite family of active cutting patterns used by `x`. -/
def patterns
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) : Finset (Fin m → ℕ) :=
  x.support.map ⟨Subtype.val, fun _ _ h ↦ Subtype.ext h⟩

/-- The finitely supported multiplicity profile on all patterns, extending `x` by zero away from
`cutting_patterns W w`. -/
def patternCount
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) : (Fin m → ℕ) →₀ ℕ :=
  Finsupp.embDomain
    ⟨Subtype.val, fun _ _ h ↦ Subtype.ext h⟩
    x

/-- The total multiplicity profile on all patterns, viewed as an ordinary function. -/
abbrev toPatternCount
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) : (Fin m → ℕ) → ℕ :=
  x.patternCount

@[simp] theorem toPatternCount_apply_of_mem
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) (s : Fin m → ℕ) (hs : s ∈ cutting_patterns W w) :
    x.toPatternCount s = x ⟨s, hs⟩ := by
  simpa [toPatternCount, patternCount] using
    Finsupp.embDomain_apply_self
      ⟨Subtype.val, fun _ _ h ↦ Subtype.ext h⟩
      x
      ⟨s, hs⟩

@[simp] theorem toPatternCount_apply_of_not_mem
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) (s : Fin m → ℕ) (hs : s ∉ cutting_patterns W w) :
    x.toPatternCount s = 0 := by
  refine Finsupp.embDomain_notin_range
    ⟨Subtype.val, fun _ _ h ↦ Subtype.ext h⟩
    x
    s
    ?_
  rintro ⟨t, rfl⟩
  exact hs t.2

@[simp] theorem support_patternCount
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) :
    x.patternCount.support = x.patterns := by
  rw [patternCount, patterns]
  exact Finsupp.support_embDomain
    ⟨Subtype.val, fun _ _ h ↦ Subtype.ext h⟩
    x

/-- The active pattern family has exactly one element for each nonzero usage entry. -/
@[simp] theorem card_patterns
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) :
    x.patterns.card = x.support.card := by
  rw [patterns]
  exact Finset.card_map ⟨Subtype.val, fun _ _ h ↦ Subtype.ext h⟩

/-- A pattern-usage vector is feasible when its total multiplicity profile satisfies the
Gilmore-Gomory demand system on its active pattern family. -/
def Feasible
    {w : Fin m → ℕ} {W : ℕ}
    (b : Fin m → ℕ) (x : cutting_stock_usage w W) : Prop :=
  x.toPatternCount ∈ gilmore_gomory_feasible_set b x.patterns

/-- Unfolding characterization of cutting-stock feasibility through the canonical
Gilmore-Gomory feasible-set owner from Example 8.15. -/
theorem feasible_iff
    {w : Fin m → ℕ} {W : ℕ}
    (b : Fin m → ℕ) (x : cutting_stock_usage w W) :
    x.Feasible b ↔ ∀ i, b i ≤ x.patterns.sum (fun s ↦ s i * x.toPatternCount s) := by
  rw [Feasible, mem_gilmore_gomory_feasible_set_iff]

/-- The objective value of a cutting-stock solution is the Gilmore-Gomory roll count of its active
pattern family. -/
def objective
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) : ℕ :=
  gilmore_gomory_objective x.patterns x.toPatternCount

/-- Unfolding characterization of the cutting-stock objective through the canonical
Gilmore-Gomory objective owner from Example 8.15. -/
theorem objective_def
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) :
    x.objective = x.patterns.sum x.toPatternCount := by
  rw [objective, gilmore_gomory_objective_eq]

/-- A cutting-stock solution is optimal when it is feasible and minimizes the number of used
stock rolls among all feasible solutions. -/
def IsOptimal
    {w : Fin m → ℕ} {W : ℕ}
    (b : Fin m → ℕ) (x : cutting_stock_usage w W) : Prop :=
  x.Feasible b ∧
    ∀ y : cutting_stock_usage w W,
      y.Feasible b → x.objective ≤ y.objective

/-- Unfolding characterization of optimality for the cutting-stock problem. -/
theorem isOptimal_iff
    {w : Fin m → ℕ} {W : ℕ}
    (b : Fin m → ℕ) (x : cutting_stock_usage w W) :
    x.IsOptimal b ↔
      x.Feasible b ∧
        ∀ y : cutting_stock_usage w W, y.Feasible b → x.objective ≤ y.objective :=
  Iff.rfl

end cutting_stock_usage

/-- Helper for Theorem 8.19: exact demand means that the raw pattern-count profile hits the
requested demand vector coordinatewise with equality. -/
def ExactDemand
    {w : Fin m → ℕ} {W : ℕ}
    (b : Fin m → ℕ) (x : cutting_stock_usage w W) : Prop :=
  ∀ i, x.patternCount.sum (fun s n ↦ s i * n) = b i

/-- Helper for Theorem 8.19: active raw patterns are exactly those with positive multiplicity in
`toPatternCount`. -/
lemma memPatterns_iff_toPatternCount_pos
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) (s : Fin m → ℕ) :
    s ∈ x.patterns ↔ 0 < x.toPatternCount s := by
  -- Rewrite support membership through the raw pattern-count profile.
  rw [← cutting_stock_usage.support_patternCount, Finsupp.mem_support_iff]
  simpa only [cutting_stock_usage.toPatternCount] using
    (Nat.pos_iff_ne_zero.symm : x.patternCount s ≠ 0 ↔ 0 < x.patternCount s)

/-- Helper for Theorem 8.19: summing over `patternCount` is the same as summing over the active
raw pattern family `patterns`. -/
lemma patternCount_sum_eq_patterns_sum
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) (i : Fin m) :
    x.patternCount.sum (fun s n ↦ s i * n) =
      x.patterns.sum (fun s ↦ s i * x.toPatternCount s) := by
  -- The two sums have the same support and the same summand on each active pattern.
  rw [Finsupp.sum, cutting_stock_usage.support_patternCount]

/-- Helper for Theorem 8.19: an exact-demand usage is automatically feasible for the covering
formulation. -/
lemma ExactDemand.feasible
    {w : Fin m → ℕ} {W : ℕ}
    {b : Fin m → ℕ} {x : cutting_stock_usage w W}
    (hx : ExactDemand b x) :
    x.Feasible b := by
  -- Replace the support sum in the feasibility predicate by the exact pattern-count sum.
  rw [cutting_stock_usage.feasible_iff]
  intro i
  rw [← hx i, ← patternCount_sum_eq_patterns_sum x i]

/-- Helper for Theorem 8.19: summing delivered copies over the subtype support agrees with the raw
active-pattern sum. -/
lemma supportWeightedSum_eq_patternsWeightedSum
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) (i : Fin m) :
    x.support.sum (fun s : cutting_patterns W w ↦ s.1 i * x s) =
      x.patterns.sum (fun s ↦ s i * x.toPatternCount s) := by
  -- Forget the subtype wrapper on the active support and relabel the finite sum.
  simpa [cutting_stock_usage.patterns, cutting_stock_usage.toPatternCount] using
    (Finset.sum_map
      (f := fun s : Fin m → ℕ ↦ s i * x.toPatternCount s)
      ⟨Subtype.val, fun _ _ h ↦ Subtype.ext h⟩
      x.support).symm


/-- Helper for Theorem 8.19: exact demand can be read as a support-indexed weighted sum identity.
-/
lemma supportCoordinateSum_eq_exactDemand
    {w : Fin m → ℕ} {W : ℕ}
    {b : Fin m → ℕ} {x : cutting_stock_usage w W}
    (hx : ExactDemand b x) (i : Fin m) :
    x.support.sum (fun s : cutting_patterns W w ↦ s.1 i * x s) = b i := by
  -- Transport the exact-demand identity from `patternCount` to the subtype support.
  calc
    x.support.sum (fun s : cutting_patterns W w ↦ s.1 i * x s) =
        x.patterns.sum (fun s ↦ s i * x.toPatternCount s) :=
      supportWeightedSum_eq_patternsWeightedSum x i
    _ = x.patternCount.sum (fun s n ↦ s i * n) := (patternCount_sum_eq_patterns_sum x i).symm
    _ = b i := hx i

/-- Helper for Theorem 8.19: the coordinatewise subset-sum map on active patterns. -/
def supportSubsetSum
    {w : Fin m → ℕ} {W : ℕ}
    (U : Finset (cutting_patterns W w)) : Fin m → ℕ :=
  fun i ↦ U.sum (fun s ↦ s.1 i)

/-- Helper for Theorem 8.19: every subset of the active support contributes at most the exact
demand in each coordinate. -/
lemma supportSubsetSum_le_of_exactDemand
    {w : Fin m → ℕ} {W : ℕ}
    {b : Fin m → ℕ} {x : cutting_stock_usage w W}
    (hx : ExactDemand b x)
    {U : Finset (cutting_patterns W w)}
    (hU : U ⊆ x.support) (i : Fin m) :
    supportSubsetSum U i ≤ b i := by
  -- First compare each selected pattern with the same pattern weighted by its positive
  -- multiplicity, then enlarge the finite sum from `U` to the full support.
      calc
    supportSubsetSum U i = U.sum (fun s : cutting_patterns W w ↦ s.1 i) := rfl
    _ ≤ U.sum (fun s : cutting_patterns W w ↦ s.1 i * x s) := by
      refine Finset.sum_le_sum ?_
      intro s hs
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (hU hs)))
    _ ≤ x.support.sum (fun s : cutting_patterns W w ↦ s.1 i * x s) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hU ?_
      intro s hs_support hs_not_mem
      exact Nat.zero_le _
    _ = b i := supportCoordinateSum_eq_exactDemand hx i

/-- Helper for Theorem 8.19: base-2 logarithms turn a finite product of nonzero real factors into
the corresponding finite sum. -/
lemma logb_prod_two
    {α : Type*}
    (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, f a ≠ 0) :
    Real.logb 2 (s.prod f) = s.sum (fun a ↦ Real.logb 2 (f a)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty product is `1`, and the empty logarithmic sum vanishes.
      simp
  | @insert a s ha hs =>
      have hfa : f a ≠ 0 := hf a (by simp [ha])
      have hfs : ∀ b ∈ s, f b ≠ 0 := fun b hb ↦ hf b (by simp [hb, ha])
      have hprod : s.prod f ≠ 0 := Finset.prod_ne_zero_iff.mpr hfs
      -- Peel off one factor and apply the induction hypothesis to the remaining product.
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Real.logb_mul hfa hprod, hs hfs]


/-- Helper for Theorem 8.19: collision-free subset sums on the active support force the support
cardinality bound from the Eisenbrand-Shmonin counting argument. -/
lemma supportCardLeLogSumOfCollisionFree
    {w : Fin m → ℕ} {W : ℕ}
    {b : Fin m → ℕ} {x : cutting_stock_usage w W}
    (hx : ExactDemand b x)
    (hinj :
      Set.InjOn
        (fun U : Finset (cutting_patterns W w) ↦ supportSubsetSum U)
        (x.support.powerset : Set (Finset (cutting_patterns W w)))) :
    (x.support.card : ℝ) ≤
      ∑ i, Real.logb 2 ((b i : ℝ) + 1) := by
  classical
  let subsetSumFin :
      {U // U ∈ x.support.powerset} → ∀ i, Fin (b i + 1) :=
    fun U i ↦
      ⟨supportSubsetSum U.1 i,
        Nat.lt_succ_of_le
          (supportSubsetSum_le_of_exactDemand hx (Finset.mem_powerset.mp U.2) i)⟩
  have hsubsetSumFin_injective : Function.Injective subsetSumFin := by
    intro U V hUV
    apply Subtype.ext
    -- Equality in the finite codomain recovers equality of the underlying subset-sum vectors.
    apply hinj U.2 V.2
    funext i
    exact congrArg Fin.val (congrArg (fun f ↦ f i) hUV)
  have hsubset_card :
      x.support.powerset.attach.card ≤ Fintype.card (∀ i : Fin m, Fin (b i + 1)) := by
    calc
      x.support.powerset.attach.card =
          (x.support.powerset.attach.image subsetSumFin).card := by
        symm
        exact Finset.card_image_of_injective _ hsubsetSumFin_injective
      _ ≤ Fintype.card (∀ i : Fin m, Fin (b i + 1)) := Finset.card_le_univ _
  have hpi :
      Fintype.card (∀ i : Fin m, Fin (b i + 1)) = ∏ i : Fin m, (b i + 1) := by
    simp
  have hpow_nat : 2 ^ x.support.card ≤ ∏ i : Fin m, (b i + 1) := by
    -- Count the powerset through the injective subset-sum map into `Π i, Fin (b i + 1)`.
    simpa [hpi] using hsubset_card
  have hpow_real : (((2 ^ x.support.card : ℕ) : ℝ)) ≤ ∏ i : Fin m, ((b i : ℝ) + 1) := by
    exact_mod_cast hpow_nat
  have hlog_le :
      Real.logb 2 (((2 ^ x.support.card : ℕ) : ℝ)) ≤
        Real.logb 2 (∏ i : Fin m, ((b i : ℝ) + 1)) := by
    -- Apply monotonicity of `logb 2` on positive reals to the counted cardinality inequality.
    exact Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num) (by positivity) hpow_real
  have hlog_prod :
      Real.logb 2 (∏ i : Fin m, ((b i : ℝ) + 1)) =
        ∑ i, Real.logb 2 ((b i : ℝ) + 1) := by
    -- Convert the logarithm of the product bound into a sum of coordinatewise logarithms.
    exact logb_prod_two
      (s := Finset.univ)
      (f := fun i : Fin m ↦ (b i : ℝ) + 1)
      (fun i _ ↦ by positivity)
  -- Rewrite the left logarithm as `logb 2 (2 ^ |support|) = |support|` and finish.
  calc
    (x.support.card : ℝ) = Real.logb 2 (((2 ^ x.support.card : ℕ) : ℝ)) := by
      rw [show (((2 ^ x.support.card : ℕ) : ℝ)) = (2 : ℝ) ^ x.support.card by norm_num]
      rw [Real.logb_pow]
      norm_num
    _ ≤ Real.logb 2 (∏ i : Fin m, ((b i : ℝ) + 1)) := hlog_le
    _ = ∑ i, Real.logb 2 ((b i : ℝ) + 1) := hlog_prod

/-- Helper for Theorem 8.19: lowering one coordinate of a raw pattern by one copy. -/
def decrementCoordinatePattern
    (s : Fin m → ℕ) (i : Fin m) : Fin m → ℕ :=
  s - Pi.single i 1

/-- Helper for Theorem 8.19: decrementing one positive coordinate keeps a cutting pattern feasible.
-/
lemma decrementCoordinatePattern_mem
    {w : Fin m → ℕ} {W : ℕ}
    {s : Fin m → ℕ} {i : Fin m}
    (hs : s ∈ cutting_patterns W w)
    (hsi : 0 < s i) :
    decrementCoordinatePattern s i ∈ cutting_patterns W w := by
  -- Compare the decremented pattern coordinatewise with the original feasible pattern.
  rw [mem_cutting_patterns_iff]
  have hle :
      ∀ j : Fin m, w j * decrementCoordinatePattern s i j ≤ w j * s j := by
    intro j
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  exact le_trans (Finset.sum_le_sum fun j _ ↦ hle j) ((mem_cutting_patterns_iff W w s).mp hs)

/-- Helper for Theorem 8.19: away from the decremented coordinate, the raw pattern is unchanged.
-/
lemma decrementCoordinatePattern_apply_ne
    {s : Fin m → ℕ} {i j : Fin m}
    (hji : j ≠ i) :
    decrementCoordinatePattern s i j = s j := by
  -- Off the active coordinate, subtracting `Pi.single i 1` does nothing.
  simp [decrementCoordinatePattern, Pi.single_apply, hji]

/-- Helper for Theorem 8.19: at the decremented coordinate, one copy is removed. -/
lemma decrementCoordinatePattern_apply_self
    {s : Fin m → ℕ} {i : Fin m}
    (hsi : 0 < s i) :
    decrementCoordinatePattern s i i = s i - 1 := by
  -- At the active coordinate, `Pi.single i 1` subtracts exactly one unit.
  simp [decrementCoordinatePattern, Pi.single_apply, hsi]

/-- Helper for Theorem 8.19: the total item count of a decremented pattern drops by one. -/
lemma sum_decrementCoordinatePattern_add_one
    {s : Fin m → ℕ} {i : Fin m}
    (hsi : 0 < s i) :
    (∑ j, decrementCoordinatePattern s i j) + 1 = ∑ j, s j := by
  -- Isolate the modified coordinate and use the off-coordinate normalization lemmas.
  have hErase :
      (Finset.univ.erase i).sum (fun j : Fin m ↦ decrementCoordinatePattern s i j) =
        (Finset.univ.erase i).sum (fun j : Fin m ↦ s j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hji : j ≠ i := by
      simpa [Finset.mem_erase] using hj
    exact decrementCoordinatePattern_apply_ne hji
  calc
    (∑ j, decrementCoordinatePattern s i j) + 1 =
        ((Finset.univ.erase i).sum (fun j : Fin m ↦ decrementCoordinatePattern s i j) +
          decrementCoordinatePattern s i i) + 1 := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    _ = ((Finset.univ.erase i).sum (fun j : Fin m ↦ s j) + (s i - 1)) + 1 := by
      rw [hErase, decrementCoordinatePattern_apply_self hsi]
    _ = (Finset.univ.erase i).sum (fun j : Fin m ↦ s j) + s i := by
      have hs_step : s i - 1 + 1 = s i := by
        simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hsi
      rw [Nat.add_assoc, hs_step]
    _ = ∑ j, s j := by
      symm
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]

/-- Helper for Theorem 8.19: the singleton pattern `Pi.single i 1` fits in one stock roll. -/
lemma singleItemPattern_mem
    (w : Fin m → ℕ) (W : ℕ)
    (hw_le : ∀ i, w i ≤ W)
    (i : Fin m) :
    Pi.single i (1 : ℕ) ∈ cutting_patterns W w := by
  -- The weighted width of a singleton pattern is exactly the width of its unique active item.
  rw [mem_cutting_patterns_iff]
  simpa [Pi.single_apply] using hw_le i

/-- Helper for Theorem 8.19: the canonical exact feasible witness uses one singleton pattern for
each item class, repeated `b i` times. -/
def singleItemUsage
    (w : Fin m → ℕ) (W : ℕ) (b : Fin m → ℕ)
    (hw_le : ∀ i, w i ≤ W) :
    cutting_stock_usage w W :=
  ∑ i, Finsupp.single ⟨Pi.single i (1 : ℕ), singleItemPattern_mem w W hw_le i⟩ (b i)

/-- Helper for Theorem 8.19: the raw pattern-count profile of `singleItemUsage` is the obvious sum
of singleton raw patterns. -/
lemma singleItemUsage_patternCount
    (w : Fin m → ℕ) (W : ℕ) (b : Fin m → ℕ)
    (hw_le : ∀ i, w i ≤ W) :
    (singleItemUsage w W b hw_le).patternCount =
      ∑ i, Finsupp.single (Pi.single i (1 : ℕ)) (b i) := by
  classical
  -- Push the subtype-to-raw embedding through the finite sum of singleton usage entries.
  rw [singleItemUsage, cutting_stock_usage.patternCount, Finsupp.embDomain_eq_mapDomain]
  rw [Finsupp.mapDomain_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp

/-- Helper for Theorem 8.19: the explicit singleton raw-pattern family delivers exactly `b j` in
coordinate `j`. -/
lemma singletonPatternFamily_exactCoordinate
    (b : Fin m → ℕ) (j : Fin m) :
    (∑ i, Finsupp.single (Pi.single i (1 : ℕ)) (b i)).sum
        (fun s n ↦ s j * n) = b j := by
  let delivered : ((Fin m → ℕ) →₀ ℕ) →+ ℕ :=
    { toFun := fun x ↦ x.sum (fun s n ↦ s j * n)
      map_zero' := by
        simp
      map_add' := by
        intro x y
        -- Distribute the coordinate-delivery functional across addition of raw pattern counts.
        rw [Finsupp.sum_add_index']
        · intro s
          simp
        · intro s
          exact Nat.left_distrib (s j) }
  -- Evaluate the additive coordinate-delivery functional on the finite singleton sum.
  change delivered (∑ i, Finsupp.single (Pi.single i (1 : ℕ)) (b i)) = b j
  rw [map_sum]
  simp [delivered, Pi.single_apply]

/-- Helper for Theorem 8.19: `singleItemUsage` realizes the demand vector exactly. -/
lemma singleItemUsage_exactDemand
    (w : Fin m → ℕ) (W : ℕ) (b : Fin m → ℕ)
    (hw_le : ∀ i, w i ≤ W) :
    ExactDemand b (singleItemUsage w W b hw_le) := by
  intro j
  -- Rewrite the raw pattern-count profile to the explicit sum of singleton patterns.
  rw [singleItemUsage_patternCount]
  -- Evaluate the resulting singleton family through the reusable coordinate-delivery helper.
  exact singletonPatternFamily_exactCoordinate b j

/-- Helper for Theorem 8.19: the singleton-pattern witness is feasible for the cutting-stock
problem. -/
lemma singleItemUsage_feasible
    (w : Fin m → ℕ) (W : ℕ) (b : Fin m → ℕ)
    (hw_le : ∀ i, w i ≤ W) :
    (singleItemUsage w W b hw_le).Feasible b :=
  (singleItemUsage_exactDemand w W b hw_le).feasible

/-- Helper for Theorem 8.19: minimizing the natural-valued objective over the nonempty feasible set
produces an optimal cutting-stock usage. -/
lemma existsOptimalUsage
    (w : Fin m → ℕ) (W : ℕ) (b : Fin m → ℕ)
    (hw_le : ∀ i, w i ≤ W) :
    ∃ x : cutting_stock_usage w W, x.IsOptimal b := by
  classical
  let P : ℕ → Prop := fun t ↦ ∃ x : cutting_stock_usage w W, x.Feasible b ∧ x.objective = t
  have hP : ∃ t, P t := by
    -- The singleton-pattern witness certifies nonemptiness of the feasible set.
    refine ⟨(singleItemUsage w W b hw_le).objective, singleItemUsage w W b hw_le, ?_, rfl⟩
    exact singleItemUsage_feasible w W b hw_le
  rcases Nat.find_spec hP with ⟨x, hx_feasible, hx_objective⟩
  refine ⟨x, ?_⟩
  constructor
  · exact hx_feasible
  · intro y hy
    -- Any competing feasible solution contributes another admissible objective value.
    have hmin : Nat.find hP ≤ y.objective := by
      exact Nat.find_min' hP ⟨y, hy, rfl⟩
    simpa [hx_objective] using hmin

/-- Helper for Theorem 8.19: the cutting-stock objective is the support sum of multiplicities. -/
lemma objective_eq_supportSum
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) :
    x.objective = x.sum (fun _ n ↦ n) := by
  -- Forget the subtype support and relabel the objective over the raw active pattern family.
  rw [cutting_stock_usage.objective_def, Finsupp.sum]
  simpa [cutting_stock_usage.patterns, cutting_stock_usage.toPatternCount] using
    (Finset.sum_map
      (f := fun s : Fin m → ℕ ↦ x.toPatternCount s)
      ⟨Subtype.val, fun _ _ h ↦ Subtype.ext h⟩
      x.support).symm

/-- Helper for Theorem 8.19: the total delivered mass counts all items cut across all rolls. -/
def deliveryMass
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) : ℕ :=
  x.sum (fun s n ↦ (∑ i, s.1 i) * n)

/-- Helper for Theorem 8.19: a positive delivered coordinate must come from some active pattern
with a positive entry in that coordinate. -/
lemma exists_mem_support_with_pos_of_coordinate_sum_pos
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W) (i : Fin m)
    (hpos : 0 < x.support.sum (fun s : cutting_patterns W w ↦ s.1 i * x s)) :
    ∃ s ∈ x.support, 0 < s.1 i := by
  classical
  by_contra hnone
  have hsum_zero :
      x.support.sum (fun s : cutting_patterns W w ↦ s.1 i * x s) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro s hs
    have hs_zero : s.1 i = 0 := by
      by_contra hs_pos
      exact hnone ⟨s, hs, Nat.pos_of_ne_zero hs_pos⟩
    simp [hs_zero]
  simpa [hsum_zero] using hpos

/-- Helper for Theorem 8.19: the decremented raw pattern, viewed again as a cutting pattern. -/
abbrev decrementedSupportPattern
    {w : Fin m → ℕ} {W : ℕ}
    (s : cutting_patterns W w) (i : Fin m) (hsi : 0 < s.1 i) :
    cutting_patterns W w :=
  ⟨decrementCoordinatePattern s.1 i, decrementCoordinatePattern_mem s.2 hsi⟩

/-- Helper for Theorem 8.19: decrementing a positive coordinate really changes the active pattern.
-/
lemma decrementedSupportPattern_ne
    {w : Fin m → ℕ} {W : ℕ}
    {s : cutting_patterns W w} {i : Fin m}
    (hsi : 0 < s.1 i) :
    decrementedSupportPattern s i hsi ≠ s := by
  -- Compare the decremented coordinate to the original positive coordinate.
  intro hEq
  have hcoord :
      decrementCoordinatePattern s.1 i i = s.1 i := by
    exact congrArg (fun t : cutting_patterns W w ↦ t.1 i) hEq
  rw [decrementCoordinatePattern_apply_self hsi] at hcoord
  have hlt : s.1 i - 1 < s.1 i := by
    simpa [Nat.pred_eq_sub_one] using Nat.pred_lt (Nat.ne_of_gt hsi)
  exact (Nat.ne_of_lt hlt) hcoord


/-- Helper for Theorem 8.19: trim one oversupplied item from one active pattern and transfer that
roll multiplicity to the decremented pattern. -/
def trimmedUsage
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W)
    (s : cutting_patterns W w) (i : Fin m) (hsi : 0 < s.1 i) :
    cutting_stock_usage w W :=
  let sDec := decrementedSupportPattern s i hsi
  (x.update s (x s - 1)).update sDec (x sDec + 1)

/-- Helper for Theorem 8.19: every additive statistic on multiplicities changes by exchanging one
copy of `s` for one copy of its decremented pattern. -/
lemma trimmedUsage_sum_exchange
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W)
    {s : cutting_patterns W w} {i : Fin m}
    (hs : s ∈ x.support) (hsi : 0 < s.1 i)
    (g : cutting_patterns W w → ℕ → ℕ)
    (hg0 : ∀ t, g t 0 = 0)
    (hadd : ∀ t a₁ a₂, g t (a₁ + a₂) = g t a₁ + g t a₂) :
    (trimmedUsage x s i hsi).sum g + g s 1 =
      x.sum g + g (decrementedSupportPattern s i hsi) 1 := by
  classical
  let sDec : cutting_patterns W w := decrementedSupportPattern s i hsi
  have hs_pos : 0 < x s := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hs)
  have hsDec_ne : sDec ≠ s := decrementedSupportPattern_ne hsi
  have hs_cancel : g s (x s - 1) + g s 1 = g s (x s) := by
    -- Regroup the removed copy as `x s = (x s - 1) + 1`.
    calc
      g s (x s - 1) + g s 1 = g s ((x s - 1) + 1) := by
        symm
        exact hadd s (x s - 1) 1
      _ = g s (x s) := by
        have hs_step : x s - 1 + 1 = x s := by
          simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hs_pos
        rw [hs_step]
  have hsDec_split : g sDec (x sDec + 1) = g sDec (x sDec) + g sDec 1 := by
    -- The new decremented pattern contributes one extra copy.
    simpa [sDec] using hadd sDec (x sDec) 1
  have hfirst :
      (trimmedUsage x s i hsi).sum g + g sDec (x sDec) =
        (x.update s (x s - 1)).sum g + (g sDec (x sDec) + g sDec 1) := by
    -- Expand the second update and use that it acts away from `s`.
    simpa [trimmedUsage, sDec, hsDec_ne, hsDec_split, add_assoc] using
      (Finsupp.sum_update_add
        (f := x.update s (x s - 1))
        (i := sDec) (a := x sDec + 1)
        (g := g) hg0 hadd)
  have hsecond :
      (x.update s (x s - 1)).sum g + g s 1 = x.sum g := by
    -- Expand the first update and use that `s` had positive multiplicity.
    have hupdate :
        (x.update s (x s - 1)).sum g + g s (x s) =
          x.sum g + g s (x s - 1) := by
      simpa using
        (Finsupp.sum_update_add
          (f := x) (i := s) (a := x s - 1)
          (g := g) hg0 hadd)
    have hupdate' :
        ((x.update s (x s - 1)).sum g + g s 1) + g s (x s - 1) =
          x.sum g + g s (x s - 1) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hs_cancel] using hupdate
    exact Nat.add_right_cancel hupdate'
  have htrim :
      (trimmedUsage x s i hsi).sum g =
        (x.update s (x s - 1)).sum g + g sDec 1 := by
    have hfirst' :
        (trimmedUsage x s i hsi).sum g + g sDec (x sDec) =
          ((x.update s (x s - 1)).sum g + g sDec 1) + g sDec (x sDec) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfirst
    exact Nat.add_right_cancel hfirst'
  calc
    (trimmedUsage x s i hsi).sum g + g s 1 =
        ((x.update s (x s - 1)).sum g + g sDec 1) + g s 1 := by
      rw [htrim]
    _ = x.sum g + g sDec 1 := by
      have hsecond' :
          ((x.update s (x s - 1)).sum g + g s 1) + g sDec 1 =
            x.sum g + g sDec 1 := by
        exact congrArg (fun n ↦ n + g sDec 1) hsecond
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsecond'

/-- Helper for Theorem 8.19: trimming one oversupplied coordinate lowers exactly that coordinate's
delivered sum by one and leaves all other coordinates unchanged. -/
lemma trimmedUsage_coordinateSum
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W)
    {s : cutting_patterns W w} {i : Fin m}
    (hs : s ∈ x.support) (hsi : 0 < s.1 i)
    (j : Fin m) :
    (trimmedUsage x s i hsi).sum (fun t n ↦ t.1 j * n) + (if j = i then 1 else 0) =
      x.sum (fun t n ↦ t.1 j * n) := by
  classical
  let sDec : cutting_patterns W w := decrementedSupportPattern s i hsi
  have hExchange :
      (trimmedUsage x s i hsi).sum (fun t n ↦ t.1 j * n) + s.1 j =
        x.sum (fun t n ↦ t.1 j * n) + sDec.1 j := by
    -- Use the generic one-copy exchange on the coordinate-delivery statistic.
    simpa [sDec] using
      trimmedUsage_sum_exchange x hs hsi
        (g := fun t n ↦ t.1 j * n)
        (hg0 := by intro t; simp)
        (hadd := by
          intro t a₁ a₂
          change t.1 j * (a₁ + a₂) = t.1 j * a₁ + t.1 j * a₂
          exact Nat.left_distrib _ _ _)
  by_cases hji : j = i
  · have hsDec_coord : sDec.1 j + 1 = s.1 j := by
      -- At the trimmed coordinate the decremented pattern loses exactly one copy.
      rw [hji]
      change decrementCoordinatePattern s.1 i i + 1 = s.1 i
      rw [decrementCoordinatePattern_apply_self hsi]
      exact Nat.succ_pred_eq_of_pos hsi
    have htrim_j :
        (trimmedUsage x s i hsi).sum (fun t n ↦ t.1 j * n) + 1 =
          x.sum (fun t n ↦ t.1 j * n) := by
      have hExchange' :
          ((trimmedUsage x s i hsi).sum (fun t n ↦ t.1 j * n) + 1) + sDec.1 j =
            x.sum (fun t n ↦ t.1 j * n) + sDec.1 j := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hsDec_coord] using hExchange
      exact Nat.add_right_cancel hExchange'
    simpa [hji] using htrim_j
  · have hsDec_coord : sDec.1 j = s.1 j := by
      -- Away from the trimmed coordinate the raw pattern is unchanged.
      change decrementCoordinatePattern s.1 i j = s.1 j
      exact decrementCoordinatePattern_apply_ne hji
    have htrim_j :
        (trimmedUsage x s i hsi).sum (fun t n ↦ t.1 j * n) =
          x.sum (fun t n ↦ t.1 j * n) := by
      have hExchange' :
          (trimmedUsage x s i hsi).sum (fun t n ↦ t.1 j * n) + s.1 j =
            x.sum (fun t n ↦ t.1 j * n) + s.1 j := by
        simpa [hsDec_coord] using hExchange
      exact Nat.add_right_cancel hExchange'
    simpa [hji] using htrim_j

/-- Helper for Theorem 8.19: trimming one oversupplied coordinate lowers the total delivered item
mass by exactly one. -/
lemma trimmedUsage_deliveryMass
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W)
    {s : cutting_patterns W w} {i : Fin m}
    (hs : s ∈ x.support) (hsi : 0 < s.1 i) :
    deliveryMass (trimmedUsage x s i hsi) + 1 = deliveryMass x := by
  classical
  let sDec : cutting_patterns W w := decrementedSupportPattern s i hsi
  have hExchange :
      deliveryMass (trimmedUsage x s i hsi) + (∑ j, s.1 j) =
        deliveryMass x + (∑ j, sDec.1 j) := by
    -- Apply the generic exchange to the total delivered-item statistic.
    simpa [deliveryMass, sDec] using
      trimmedUsage_sum_exchange x hs hsi
        (g := fun t n ↦ (∑ j, t.1 j) * n)
        (hg0 := by intro t; simp)
        (hadd := by
          intro t a₁ a₂
          change (∑ j, t.1 j) * (a₁ + a₂) = (∑ j, t.1 j) * a₁ + (∑ j, t.1 j) * a₂
          exact Nat.left_distrib _ _ _)
  have hsDec_sum : (∑ j, sDec.1 j) + 1 = ∑ j, s.1 j := by
    -- The decremented pattern loses exactly one total item.
    simpa [sDec] using sum_decrementCoordinatePattern_add_one (s := s.1) (i := i) hsi
  have hExchange' :
      (deliveryMass (trimmedUsage x s i hsi) + 1) + ∑ j, sDec.1 j =
        deliveryMass x + ∑ j, sDec.1 j := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hsDec_sum] using hExchange
  exact Nat.add_right_cancel hExchange'


/-- Helper for Theorem 8.19: minimizing total delivered mass among optimal usages yields an exact
optimal usage. -/
lemma existsExactOptimalUsage
    (w : Fin m → ℕ) (W : ℕ) (b : Fin m → ℕ)
    (hw_le : ∀ i, w i ≤ W) :
    ∃ x : cutting_stock_usage w W, x.IsOptimal b ∧ ExactDemand b x := by
  classical
  let P : ℕ → Prop := fun t ↦ ∃ x : cutting_stock_usage w W, x.IsOptimal b ∧ deliveryMass x = t
  have hP : ∃ t, P t := by
    -- The set of optimal usages is nonempty because the feasible set is nonempty.
    obtain ⟨x, hxOptimal⟩ := existsOptimalUsage w W b hw_le
    exact ⟨deliveryMass x, x, hxOptimal, rfl⟩
  rcases Nat.find_spec hP with ⟨x, hxOptimal, hxMass⟩
  refine ⟨x, hxOptimal, ?_⟩
  by_contra hxNotExact
  have hxSupportNotExact : ¬ ∀ i, x.sum (fun s n ↦ s.1 i * n) = b i := by
    -- Rewrite exact demand through the subtype-indexed weighted support sums.
    intro hSupportExact
    apply hxNotExact
    intro i
    calc
      x.patternCount.sum (fun s n ↦ s i * n) =
          x.patterns.sum (fun s ↦ s i * x.toPatternCount s) :=
        patternCount_sum_eq_patterns_sum x i
      _ = x.sum (fun s n ↦ s.1 i * n) :=
        (supportWeightedSum_eq_patternsWeightedSum x i).symm
      _ = b i := hSupportExact i
  obtain ⟨i, hiNotExact⟩ := not_forall.mp hxSupportNotExact
  have hfeasible_i :
      b i ≤ x.sum (fun s n ↦ s.1 i * n) := by
    -- Feasibility gives the lower bound on each delivered coordinate.
    calc
      b i ≤ x.patterns.sum (fun s ↦ s i * x.toPatternCount s) :=
        (cutting_stock_usage.feasible_iff b x).mp hxOptimal.1 i
      _ = x.sum (fun s n ↦ s.1 i * n) :=
        (supportWeightedSum_eq_patternsWeightedSum x i).symm
  have hoversupply :
      b i < x.sum (fun s n ↦ s.1 i * n) := by
    exact Nat.lt_of_le_of_ne hfeasible_i (by
      intro hEq
      exact hiNotExact hEq.symm)
  have hcoordinate_pos :
      0 < x.sum (fun s n ↦ s.1 i * n) := by
    exact lt_of_lt_of_le (Nat.succ_pos _) (Nat.succ_le_of_lt hoversupply)
  obtain ⟨s, hs, hsi⟩ := exists_mem_support_with_pos_of_coordinate_sum_pos x i hcoordinate_pos
  let y : cutting_stock_usage w W := trimmedUsage x s i hsi
  have hyFeasible : y.Feasible b := by
    -- The trimmed usage only reduces the oversupplied coordinate by one.
    rw [cutting_stock_usage.feasible_iff]
    intro j
    have hxj :
        b j ≤ x.sum (fun t n ↦ t.1 j * n) := by
      calc
        b j ≤ x.patterns.sum (fun s ↦ s j * x.toPatternCount s) :=
          (cutting_stock_usage.feasible_iff b x).mp hxOptimal.1 j
        _ = x.sum (fun t n ↦ t.1 j * n) :=
          (supportWeightedSum_eq_patternsWeightedSum x j).symm
    have htrim_j :
        y.sum (fun t n ↦ t.1 j * n) + (if j = i then 1 else 0) =
          x.sum (fun t n ↦ t.1 j * n) :=
      trimmedUsage_coordinateSum x hs hsi j
    by_cases hji : j = i
    · have htrim_eq :
          y.sum (fun t n ↦ t.1 j * n) + 1 =
            x.sum (fun t n ↦ t.1 j * n) := by
        simpa [hji] using htrim_j
      have hxj' : b j + 1 ≤ x.sum (fun t n ↦ t.1 j * n) := by
        simpa [hji] using hoversupply
      have hyj' : b j ≤ y.sum (fun t n ↦ t.1 j * n) := by
        have hstep : b j + 1 ≤ y.sum (fun t n ↦ t.1 j * n) + 1 := by
          simpa [htrim_eq] using hxj'
        exact Nat.succ_le_succ_iff.mp hstep
      calc
        b j ≤ y.sum (fun t n ↦ t.1 j * n) := hyj'
        _ = y.patterns.sum (fun s ↦ s j * y.toPatternCount s) :=
          supportWeightedSum_eq_patternsWeightedSum y j
    · have htrim_eq :
          y.sum (fun t n ↦ t.1 j * n) =
            x.sum (fun t n ↦ t.1 j * n) := by
        simpa [hji] using htrim_j
      have hyj' : b j ≤ y.sum (fun t n ↦ t.1 j * n) := by
        simpa [htrim_eq] using hxj
      calc
        b j ≤ y.sum (fun t n ↦ t.1 j * n) := hyj'
        _ = y.patterns.sum (fun s ↦ s j * y.toPatternCount s) :=
          supportWeightedSum_eq_patternsWeightedSum y j
  have hyObjective : y.objective = x.objective := by
    -- The trim exchanges one active roll for another, so the objective is unchanged.
    have hsum_eq :
        y.sum (fun _ n ↦ n) = x.sum (fun _ n ↦ n) := by
      have hExchange :
          y.sum (fun _ n ↦ n) + 1 = x.sum (fun _ n ↦ n) + 1 := by
        simpa [y] using
          trimmedUsage_sum_exchange x hs hsi
            (g := fun _ n ↦ n)
            (hg0 := by intro t; rfl)
            (hadd := by intro t a₁ a₂; rfl)
      exact Nat.add_right_cancel hExchange
    calc
      y.objective = y.sum (fun _ n ↦ n) := objective_eq_supportSum y
      _ = x.sum (fun _ n ↦ n) := hsum_eq
      _ = x.objective := (objective_eq_supportSum x).symm
  have hyOptimal : y.IsOptimal b := by
    constructor
    · exact hyFeasible
    · intro z hz
      rw [hyObjective]
      exact hxOptimal.2 z hz
  have hyMass_lt : deliveryMass y < deliveryMass x := by
    -- The trim removes exactly one delivered item from the oversupplied coordinate.
    have hmass : deliveryMass y + 1 = deliveryMass x := by
      simpa [y] using trimmedUsage_deliveryMass x hs hsi
    simpa [hmass] using Nat.lt_succ_self (deliveryMass y)
  have hmin : Nat.find hP ≤ deliveryMass y := by
    exact Nat.find_min' hP ⟨y, hyOptimal, rfl⟩
  have hx_le_y : deliveryMass x ≤ deliveryMass y := by
    simpa [hxMass] using hmin
  exact (Nat.not_lt_of_ge hx_le_y) hyMass_lt

/-- Helper for Theorem 8.19: among exact optimal usages, one can minimize support cardinality. -/
lemma existsExactOptimalUsageMinimizingSupport
    (w : Fin m → ℕ) (W : ℕ) (b : Fin m → ℕ)
    (hw_le : ∀ i, w i ≤ W) :
    ∃ x : cutting_stock_usage w W,
      x.IsOptimal b ∧
        ExactDemand b x ∧
          ∀ y : cutting_stock_usage w W,
            y.IsOptimal b → ExactDemand b y → x.support.card ≤ y.support.card := by
  classical
  let P : ℕ → Prop := fun t ↦
    ∃ x : cutting_stock_usage w W, x.IsOptimal b ∧ ExactDemand b x ∧ x.support.card = t
  have hP : ∃ t, P t := by
    -- Exact optimal usages are nonempty by the delivery-mass minimization argument.
    obtain ⟨x, hxOptimal, hxExact⟩ := existsExactOptimalUsage w W b hw_le
    exact ⟨x.support.card, x, hxOptimal, hxExact, rfl⟩
  rcases Nat.find_spec hP with ⟨x, hxOptimal, hxExact, hxCard⟩
  refine ⟨x, hxOptimal, hxExact, ?_⟩
  intro y hyOptimal hyExact
  have hmin : Nat.find hP ≤ y.support.card := by
    exact Nat.find_min' hP ⟨y, hyOptimal, hyExact, rfl⟩
  simpa [hxCard] using hmin

/-- Helper for Theorem 8.19: the constant multiplicity profile `ξ` supported on the finite family
`U`. -/
def supportMultiplicity
    {w : Fin m → ℕ} {W : ℕ}
    (U : Finset (cutting_patterns W w)) (ξ : ℕ) :
    cutting_stock_usage w W :=
  ∑ s ∈ U, Finsupp.single s ξ

/-- Helper for Theorem 8.19: `supportMultiplicity U ξ` is `ξ` on `U` and `0` away from `U`. -/
lemma supportMultiplicity_apply
    {w : Fin m → ℕ} {W : ℕ}
    (U : Finset (cutting_patterns W w)) (ξ : ℕ) (s : cutting_patterns W w) :
    supportMultiplicity U ξ s = if s ∈ U then ξ else 0 := by
  classical
  -- Collapse the finite sum of singleton multiplicities at the queried pattern.
  simp [supportMultiplicity]

/-- Helper for Theorem 8.19: the support of `supportMultiplicity U ξ` stays inside `U`. -/
lemma supportMultiplicity_support_subset
    {w : Fin m → ℕ} {W : ℕ}
    (U : Finset (cutting_patterns W w)) (ξ : ℕ) :
    (supportMultiplicity U ξ).support ⊆ U := by
  classical
  -- Any nonzero coordinate of the constant subusage must come from a pattern in `U`.
  intro s hs
  by_contra hsU
  rw [Finsupp.mem_support_iff] at hs
  simp [supportMultiplicity_apply, hsU] at hs

/-- Helper for Theorem 8.19: if every pattern in `U` appears at least `ξ` times in `x`, then the
constant subusage on `U` is bounded by `x`. -/
lemma supportMultiplicity_le
    {w : Fin m → ℕ} {W : ℕ}
    (x : cutting_stock_usage w W)
    {U : Finset (cutting_patterns W w)} {ξ : ℕ}
    (hξ : ∀ s ∈ U, ξ ≤ x s) :
    supportMultiplicity U ξ ≤ x := by
  classical
  -- Evaluate the supported correction pointwise and split on membership in `U`.
  intro s
  by_cases hsU : s ∈ U
  · simpa [supportMultiplicity_apply, hsU] using hξ s hsU
  · simp [supportMultiplicity_apply, hsU]

/-- Helper for Theorem 8.19: additive statistics on the constant subusage reduce to a finite sum
over the supporting family. -/
lemma supportMultiplicity_sum
    {w : Fin m → ℕ} {W : ℕ}
    (U : Finset (cutting_patterns W w)) (ξ : ℕ)
    (g : cutting_patterns W w → ℕ → ℕ)
    (hg0 : ∀ s, g s 0 = 0)
    (hadd : ∀ s a₁ a₂, g s (a₁ + a₂) = g s a₁ + g s a₂) :
    (supportMultiplicity U ξ).sum g = U.sum (fun s ↦ g s ξ) := by
  classical
  -- Push the additive statistic through the finite sum of singleton multiplicity profiles.
  rw [supportMultiplicity, Finsupp.sum_finsetSum_index]
  · simp [hg0]
  · exact hg0
  · exact hadd

/-- Helper for Theorem 8.19: the coordinate-delivery statistic of a constant subusage is the
common multiplicity times the subset-sum vector. -/
lemma supportMultiplicity_coordinateSum
    {w : Fin m → ℕ} {W : ℕ}
    (U : Finset (cutting_patterns W w)) (ξ : ℕ) (i : Fin m) :
    (supportMultiplicity U ξ).sum (fun s n ↦ s.1 i * n) = ξ * supportSubsetSum U i := by
  -- Collapse the constant subusage to a plain finite sum and factor out the common multiplicity.
  rw [supportMultiplicity_sum]
  · simp [supportSubsetSum, Finset.mul_sum, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  · intro s
    simp
  · intro s a₁ a₂
    exact Nat.left_distrib _ _ _

/-- Helper for Theorem 8.19: the objective statistic of a constant subusage is its support size
times the common multiplicity. -/
lemma supportMultiplicity_objectiveSum
    {w : Fin m → ℕ} {W : ℕ}
    (U : Finset (cutting_patterns W w)) (ξ : ℕ) :
    (supportMultiplicity U ξ).sum (fun _ n ↦ n) = U.card * ξ := by
  -- A constant subusage contributes the same multiplicity `ξ` at each point of `U`.
  rw [supportMultiplicity_sum]
  · simp
  · intro s
    rfl
  · intro s a₁ a₂
    rfl

/-- Helper for Theorem 8.19: replacing a bounded subusage `δ₁ ≤ x` by another subusage `δ₂`
with the same additive statistic preserves the total statistic of `x`. -/
lemma exchangeSum_eq_of_le
    {w : Fin m → ℕ} {W : ℕ}
    (x δ₁ δ₂ : cutting_stock_usage w W)
    (hδ₁ : δ₁ ≤ x)
    (g : cutting_patterns W w → ℕ → ℕ)
    (hg0 : ∀ s, g s 0 = 0)
    (hadd : ∀ s a₁ a₂, g s (a₁ + a₂) = g s a₁ + g s a₂)
    (hstat : δ₁.sum g = δ₂.sum g) :
    (x - δ₁ + δ₂).sum g = x.sum g := by
  -- Expand both totals across the same base usage `x - δ₁`.
  calc
    (x - δ₁ + δ₂).sum g = (x - δ₁).sum g + δ₂.sum g := by
      rw [Finsupp.sum_add_index' hg0 hadd]
    _ = (x - δ₁).sum g + δ₁.sum g := by rw [hstat]
    _ = (x - δ₁ + δ₁).sum g := by
      rw [Finsupp.sum_add_index' hg0 hadd]
    _ = x.sum g := by rw [tsub_add_cancel_of_le hδ₁]

/-- Helper for Theorem 8.19: replacing a bounded subusage `δ₁ ≤ x` by another subusage `δ₂`
whose additive statistic is smaller cannot increase the total statistic of `x`. -/
lemma exchangeSum_le_of_le
    {w : Fin m → ℕ} {W : ℕ}
    (x δ₁ δ₂ : cutting_stock_usage w W)
    (hδ₁ : δ₁ ≤ x)
    (g : cutting_patterns W w → ℕ → ℕ)
    (hg0 : ∀ s, g s 0 = 0)
    (hadd : ∀ s a₁ a₂, g s (a₁ + a₂) = g s a₁ + g s a₂)
    (hstat : δ₂.sum g ≤ δ₁.sum g) :
    (x - δ₁ + δ₂).sum g ≤ x.sum g := by
  -- Compare both totals after expanding along the same base usage `x - δ₁`.
  calc
    (x - δ₁ + δ₂).sum g = (x - δ₁).sum g + δ₂.sum g := by
      rw [Finsupp.sum_add_index' hg0 hadd]
    _ ≤ (x - δ₁).sum g + δ₁.sum g := by
      exact add_le_add_left hstat _
    _ = (x - δ₁ + δ₁).sum g := by
      rw [Finsupp.sum_add_index' hg0 hadd]
    _ = x.sum g := by rw [tsub_add_cancel_of_le hδ₁]

/-- Helper for Theorem 8.19: evaluating an exchanged usage is pointwise subtraction followed by
addition. -/
lemma exchangeUsage_apply
    {w : Fin m → ℕ} {W : ℕ}
    (x δ₁ δ₂ : cutting_stock_usage w W)
    (t : cutting_patterns W w) :
    (x - δ₁ + δ₂) t = (x t - δ₁ t) + δ₂ t := by
  rw [Finsupp.add_apply, Finsupp.tsub_apply]

/-- Helper for Theorem 8.19: if the exchanged-out multiplicity equals the original multiplicity and
the exchanged-in multiplicity vanishes at `t`, then the exchanged usage also vanishes at `t`. -/
lemma exchangeUsage_apply_eq_zero_of_cancel
    {w : Fin m → ℕ} {W : ℕ}
    (x δ₁ δ₂ : cutting_stock_usage w W)
    (t : cutting_patterns W w)
    (hδ₁ : δ₁ t = x t)
    (hδ₂ : δ₂ t = 0) :
    (x - δ₁ + δ₂) t = 0 := by
  rw [exchangeUsage_apply, hδ₁, tsub_self, hδ₂]

/-- Helper for Theorem 8.19: if all three usage vectors vanish at `t`, then the exchanged usage
also vanishes at `t`. -/
lemma exchangeUsage_apply_eq_zero_of_zero
    {w : Fin m → ℕ} {W : ℕ}
    (x δ₁ δ₂ : cutting_stock_usage w W)
    (t : cutting_patterns W w)
    (hx : x t = 0)
    (hδ₁ : δ₁ t = 0)
    (hδ₂ : δ₂ t = 0) :
    (x - δ₁ + δ₂) t = 0 := by
  rw [exchangeUsage_apply, hx, hδ₁, hδ₂]

/-- Helper for Theorem 8.19: equal support subset sums remain equal after disjointizing by
set-theoretic difference. -/
lemma supportSubsetSum_sdiff_eq_of_eq
    {w : Fin m → ℕ} {W : ℕ}
    {U V : Finset (cutting_patterns W w)}
    (hEq : supportSubsetSum U = supportSubsetSum V) :
    supportSubsetSum (U \ V) = supportSubsetSum (V \ U) := by
  -- Separate both subset sums into their disjoint part plus the common intersection.
  funext i
  have hUi :
      supportSubsetSum U i =
        supportSubsetSum (U \ V) i + supportSubsetSum (U ∩ V) i := by
    simpa [supportSubsetSum] using
      (Finset.sum_sdiff (s := U) (t := U ∩ V) (Finset.inter_subset_left : U ∩ V ⊆ U)).symm
  have hVi :
      supportSubsetSum V i =
        supportSubsetSum (V \ U) i + supportSubsetSum (U ∩ V) i := by
    simpa [supportSubsetSum, Finset.inter_comm] using
      (Finset.sum_sdiff (s := V) (t := V ∩ U) (Finset.inter_subset_left : V ∩ U ⊆ V)).symm
  have hEqi : supportSubsetSum U i = supportSubsetSum V i := congrArg (fun f ↦ f i) hEq
  have hcancel :
      supportSubsetSum (U \ V) i + supportSubsetSum (U ∩ V) i =
        supportSubsetSum (V \ U) i + supportSubsetSum (U ∩ V) i := by
    rw [← hUi, ← hVi, hEqi]
  exact Nat.add_right_cancel hcancel


/-- Helper for Theorem 8.19: a disjoint support-subset collision on an exact optimal usage can be
exchanged to produce another exact optimal usage with strictly smaller support. -/
lemma existsSmallerSupportExactOptimal_of_disjointCollision
    {w : Fin m → ℕ} {W : ℕ} {b : Fin m → ℕ}
    {x : cutting_stock_usage w W}
    (hxOptimal : x.IsOptimal b) (hxExact : ExactDemand b x)
    {U V : Finset (cutting_patterns W w)}
    (hU : U ⊆ x.support) (hV : V ⊆ x.support)
    (hDisj : Disjoint U V) (hUne : U.Nonempty)
    (hEq : supportSubsetSum U = supportSubsetSum V)
    (hCard : V.card ≤ U.card) :
    ∃ y : cutting_stock_usage w W,
      y.IsOptimal b ∧ ExactDemand b y ∧ y.support.card < x.support.card := by
  classical
  let ξ : ℕ := (U.image x).min' (by
    rcases hUne with ⟨s, hs⟩
    exact ⟨x s, Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩)
  let δU : cutting_stock_usage w W := supportMultiplicity U ξ
  let δV : cutting_stock_usage w W := supportMultiplicity V ξ
  let y : cutting_stock_usage w W := x - δU + δV
  have hξ_le : ∀ s ∈ U, ξ ≤ x s := by
    intro s hs
    -- The chosen multiplicity `ξ` is the minimum value of `x` on `U`.
    have hsImage : x s ∈ U.image x := Finset.mem_image.mpr ⟨s, hs, rfl⟩
    simpa [ξ] using Finset.min'_le (U.image x) (x s) hsImage
  have hs0_image : ξ ∈ U.image x := by
    -- The minimum value is attained on the finite image `U.image x`.
    simpa [ξ] using
      Finset.min'_mem
        (U.image x)
        (by
          rcases hUne with ⟨s, hs⟩
          exact ⟨x s, Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩)
  obtain ⟨s0, hs0U, hs0ξ⟩ := Finset.mem_image.mp hs0_image
  have hs0Support : s0 ∈ x.support := hU hs0U
  have hξ_pos : 0 < ξ := by
    -- The minimizer still lies in `x.support`, so its multiplicity is positive.
    have hs0_pos : 0 < x s0 := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hs0Support)
    simpa [hs0ξ] using hs0_pos
  have hδU_le : δU ≤ x := by
    -- Every pattern in `U` appears at least `ξ` times in `x`.
    exact supportMultiplicity_le x hξ_le
  have hyCoordinateSum :
      ∀ i, y.sum (fun s n ↦ s.1 i * n) = x.sum (fun s n ↦ s.1 i * n) := by
    intro i
    have hstat :
        δU.sum (fun s n ↦ s.1 i * n) = δV.sum (fun s n ↦ s.1 i * n) := by
      -- The exchanged subusages deliver the same coordinate totals by the subset-sum collision.
      have hEqi : supportSubsetSum U i = supportSubsetSum V i := congrArg (fun f ↦ f i) hEq
      rw [δU, δV, supportMultiplicity_coordinateSum, supportMultiplicity_coordinateSum, hEqi]
    simpa [y] using
      exchangeSum_eq_of_le
        x
        δU
        δV
        hδU_le
        (fun s n ↦ s.1 i * n)
        (by
          intro s
          simp)
        (by
          intro s a₁ a₂
          exact Nat.left_distrib _ _ _)
        hstat
  have hyExact : ExactDemand b y := by
    intro i
    -- Convert the preserved subtype-support coordinate sums back to `ExactDemand`.
    calc
      y.patternCount.sum (fun s n ↦ s i * n) =
          y.patterns.sum (fun s ↦ s i * y.toPatternCount s) :=
        patternCount_sum_eq_patterns_sum y i
      _ = y.sum (fun s n ↦ s.1 i * n) :=
        (supportWeightedSum_eq_patternsWeightedSum y i).symm
      _ = x.sum (fun s n ↦ s.1 i * n) := hyCoordinateSum i
      _ = b i := supportCoordinateSum_eq_exactDemand hxExact i
  have hyObjectiveLe : y.objective ≤ x.objective := by
    -- The larger support side loses `ξ` copies while the smaller side gains `ξ` copies.
    have hsum_le : y.sum (fun _ n ↦ n) ≤ x.sum (fun _ n ↦ n) := by
      have hstat :
          δV.sum (fun _ n ↦ n) ≤ δU.sum (fun _ n ↦ n) := by
        rw [δU, δV, supportMultiplicity_objectiveSum, supportMultiplicity_objectiveSum]
        exact Nat.mul_le_mul_right ξ hCard
      simpa [y] using
        exchangeSum_le_of_le
          x
          δU
          δV
          hδU_le
          (fun _ n ↦ n)
          (by
            intro s
            rfl)
          (by
            intro s a₁ a₂
            rfl)
          hstat
    calc
      y.objective = y.sum (fun _ n ↦ n) := objective_eq_supportSum y
      _ ≤ x.sum (fun _ n ↦ n) := hsum_le
      _ = x.objective := (objective_eq_supportSum x).symm
  have hs0_not_mem_V : s0 ∉ V := by
    -- The collision families are disjoint, so the minimizing pattern is removed but not re-added.
    intro hs0V
    exact (Finset.disjoint_left.mp hDisj hs0U hs0V).elim
  have hy_s0_zero : y s0 = 0 := by
    -- At `s0` the exchange subtracts exactly `ξ = x s0` and adds nothing back.
    have hδUs0 : δU s0 = ξ := by
      simp [δU, supportMultiplicity_apply, hs0U]
    have hδVs0 : δV s0 = 0 := by
      simp [δV, supportMultiplicity_apply, hs0_not_mem_V]
    have hδUs0' : δU s0 = x s0 := by
      simpa [hs0ξ] using hδUs0
    simpa [y] using
      exchangeUsage_apply_eq_zero_of_cancel x δU δV s0 hδUs0' hδVs0
  have hySupportSubset : y.support ⊆ x.support.erase s0 := by
    intro t ht
    have hyt_ne : y t ≠ 0 := Finsupp.mem_support_iff.mp ht
    have ht_mem_x : t ∈ x.support := by
      -- Outside `x.support`, both exchanged subusages also vanish, so `y` vanishes too.
      by_contra htx
      have hxt_zero : x t = 0 := by
        by_contra hxt_ne
        exact htx (Finsupp.mem_support_iff.mpr hxt_ne)
      have ht_not_mem_U : t ∉ U := by
        intro htU
        exact htx (hU htU)
      have ht_not_mem_V : t ∉ V := by
        intro htV
        exact htx (hV htV)
      have hδUt_zero : δU t = 0 := by
        simp [δU, supportMultiplicity_apply, ht_not_mem_U]
      have hδVt_zero : δV t = 0 := by
        simp [δV, supportMultiplicity_apply, ht_not_mem_V]
      have hyt_zero : y t = 0 := by
        simpa [y] using
          exchangeUsage_apply_eq_zero_of_zero x δU δV t hxt_zero hδUt_zero hδVt_zero
      exact hyt_ne hyt_zero
    have ht_ne_s0 : t ≠ s0 := by
      intro hts0
      exact hyt_ne (hts0 ▸ hy_s0_zero)
    exact Finset.mem_erase.mpr ⟨ht_ne_s0, ht_mem_x⟩
  have hySupportLt : y.support.card < x.support.card := by
    -- The exchanged usage is supported on a proper subset of `x.support`.
    have hySubset : y.support ⊆ x.support := by
      intro t ht
      exact (Finset.mem_erase.mp (hySupportSubset ht)).2
    have hs0_not_mem_y : s0 ∉ y.support := by
      simp [Finsupp.mem_support_iff, hy_s0_zero]
    have hySSubset : y.support ⊂ x.support := by
      exact (Finset.ssubset_iff_of_subset hySubset).2 ⟨s0, hs0Support, hs0_not_mem_y⟩
    exact Finset.card_lt_card hySSubset
  refine ⟨y, ?_, hyExact, hySupportLt⟩
  constructor
  · exact hyExact.feasible
  · intro z hz
    -- Optimality is preserved because the exchange does not increase the objective.
    exact le_trans hyObjectiveLe (hxOptimal.2 z hz)

/-- Helper for Theorem 8.19: an exact optimal usage with minimal support has injective support
subset sums on its powerset. -/
lemma supportSubsetSum_injective_of_minimalSupport
    {w : Fin m → ℕ} {W : ℕ} {b : Fin m → ℕ}
    {x : cutting_stock_usage w W}
    (hxOptimal : x.IsOptimal b) (hxExact : ExactDemand b x)
    (hxMinSupport :
      ∀ y : cutting_stock_usage w W,
        y.IsOptimal b → ExactDemand b y → x.support.card ≤ y.support.card) :
    Set.InjOn
      (fun U : Finset (cutting_patterns W w) ↦ supportSubsetSum U)
      (x.support.powerset : Set (Finset (cutting_patterns W w))) := by
  classical
  intro U hUmem V hVmem hEq
  by_contra hne
  have hUsub : U ⊆ x.support := Finset.mem_powerset.mp hUmem
  have hVsub : V ⊆ x.support := Finset.mem_powerset.mp hVmem
  have hsdiffEq : supportSubsetSum (U \ V) = supportSubsetSum (V \ U) :=
    supportSubsetSum_sdiff_eq_of_eq hEq
  have hdiff_nonempty : (U \ V).Nonempty ∨ (V \ U).Nonempty := by
    -- Distinct subsets must differ on at least one side after disjointization.
    by_cases hUV : U \ V = ∅
    · by_cases hVU : V \ U = ∅
      · have hUeqV : U = V := by
          exact Finset.Subset.antisymm
            (Finset.sdiff_eq_empty_iff_subset.mp hUV)
            (Finset.sdiff_eq_empty_iff_subset.mp hVU)
        exact hne hUeqV
      · exact Or.inr (Finset.nonempty_iff_ne_empty.mpr hVU)
    · exact Or.inl (Finset.nonempty_iff_ne_empty.mpr hUV)
  have hDisj : Disjoint (U \ V) (V \ U) := by
    -- The set differences are disjoint by construction.
    refine Finset.disjoint_left.mpr ?_
    intro s hsUV hsVU
    exact (Finset.mem_sdiff.mp hsUV).2 (Finset.mem_of_mem_sdiff hsVU)
  have hUdiff : U \ V ⊆ x.support := by
    intro s hs
    exact hUsub (Finset.mem_of_mem_sdiff hs)
  have hVdiff : V \ U ⊆ x.support := by
    intro s hs
    exact hVsub (Finset.mem_of_mem_sdiff hs)
  cases Nat.le_total ((U \ V).card) ((V \ U).card) with
  | inl hCard =>
      have hVdiff_nonempty : (V \ U).Nonempty := by
        -- The larger disjointized side cannot be empty unless both are empty.
        by_contra hEmpty
        rcases hdiff_nonempty with hUne | hVne
        · have hUpos : 0 < (U \ V).card := Finset.card_pos.mpr hUne
          have hVzero : (V \ U).card = 0 := Finset.card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hEmpty)
          rw [hVzero] at hCard
          exact (Nat.not_lt_of_ge hCard) hUpos
        · exact hEmpty hVne
      obtain ⟨y, hyOptimal, hyExact, hyLt⟩ :=
        existsSmallerSupportExactOptimal_of_disjointCollision
          hxOptimal
          hxExact
          hVdiff
          hUdiff
          hDisj.symm
          hVdiff_nonempty
          hsdiffEq.symm
          hCard
      exact (Nat.not_lt_of_ge (hxMinSupport y hyOptimal hyExact)) hyLt
  | inr hCard =>
      have hUdiff_nonempty : (U \ V).Nonempty := by
        -- Symmetrically, the larger first side cannot be empty unless both sides are empty.
        by_contra hEmpty
        rcases hdiff_nonempty with hUne | hVne
        · exact hEmpty hUne
        · have hVpos : 0 < (V \ U).card := Finset.card_pos.mpr hVne
          have hUzero : (U \ V).card = 0 := Finset.card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hEmpty)
          rw [hUzero] at hCard
          exact (Nat.not_lt_of_ge hCard) hVpos
      obtain ⟨y, hyOptimal, hyExact, hyLt⟩ :=
        existsSmallerSupportExactOptimal_of_disjointCollision
          hxOptimal
          hxExact
          hUdiff
          hVdiff
          hDisj
          hUdiff_nonempty
          hsdiffEq
          hCard
      exact (Nat.not_lt_of_ge (hxMinSupport y hyOptimal hyExact)) hyLt

/-- Theorem 8.19. If every item width is positive and every single item fits into one stock roll,
then there exists an optimal solution for the cutting stock problem that uses at most
`∑ i, log₂ (b i + 1)` patterns. -/
theorem exists_optimal_cutting_stock_solution_with_log_pattern_bound
    (w : Fin m → ℕ) (W : ℕ) (b : Fin m → ℕ)
    (hw_pos : ∀ i, 0 < w i)
    (hw_le : ∀ i, w i ≤ W) :
    ∃ x : cutting_stock_usage w W,
      x.IsOptimal b ∧
        (x.patterns.card : ℝ) ≤
          ∑ i, Real.logb 2 ((b i : ℝ) + 1) := by
  let _ := hw_pos
  obtain ⟨x, hxOptimal, hxExact, hxMinSupport⟩ :=
    existsExactOptimalUsageMinimizingSupport w W b hw_le
  refine ⟨x, hxOptimal, ?_⟩
  have hinj :
      Set.InjOn
        (fun U : Finset (cutting_patterns W w) ↦ supportSubsetSum U)
        (x.support.powerset : Set (Finset (cutting_patterns W w))) :=
    supportSubsetSum_injective_of_minimalSupport hxOptimal hxExact hxMinSupport
  have hsupport :
      (x.support.card : ℝ) ≤ ∑ i, Real.logb 2 ((b i : ℝ) + 1) :=
    supportCardLeLogSumOfCollisionFree hxExact hinj
  -- Rewrite the support-cardinality bound into the active raw-pattern count.
  simpa [cutting_stock_usage.card_patterns] using hsupport

end Theorem819
