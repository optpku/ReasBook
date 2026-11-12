/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace ADMM.RefinedEndpoint

/-- A rational enclosure of a real quantity. Endpoint inequalities are separate
proof obligations, so no unchecked rounding operation enters a theorem. -/
structure RatInterval where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq

namespace RatInterval

def Contains (I : RatInterval) (x : ℝ) : Prop :=
  (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)

def point (q : ℚ) : RatInterval := ⟨q, q⟩
def add (I J : RatInterval) : RatInterval := ⟨I.lower + J.lower, I.upper + J.upper⟩
def neg (I : RatInterval) : RatInterval := ⟨-I.upper, -I.lower⟩
def sub (I J : RatInterval) : RatInterval := I.add J.neg
def mul (I J : RatInterval) : RatInterval :=
  ⟨min (min (I.lower * J.lower) (I.lower * J.upper))
      (min (I.upper * J.lower) (I.upper * J.upper)),
    max (max (I.lower * J.lower) (I.lower * J.upper))
      (max (I.upper * J.lower) (I.upper * J.upper))⟩
def scale (q : ℚ) (I : RatInterval) : RatInterval := (point q).mul I
def half (I : RatInterval) : RatInterval := scale (1 / 2) I

@[simp] theorem contains_point (q : ℚ) : (point q).Contains (q : ℝ) := ⟨le_rfl, le_rfl⟩

theorem Contains.add {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.add J).Contains (x + y) := by
  change ((I.lower + J.lower : ℚ) : ℝ) ≤ x + y ∧
    x + y ≤ ((I.upper + J.upper : ℚ) : ℝ)
  constructor <;> push_cast
  · exact add_le_add hx.1 hy.1
  · exact add_le_add hx.2 hy.2

theorem Contains.neg {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) : I.neg.Contains (-x) := by
  change ((-I.upper : ℚ) : ℝ) ≤ -x ∧ -x ≤ ((-I.lower : ℚ) : ℝ)
  constructor <;> push_cast
  · exact neg_le_neg hx.2
  · exact neg_le_neg hx.1

theorem Contains.sub {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.sub J).Contains (x - y) := by
  change (I.add J.neg).Contains (x + -y)
  exact hx.add hy.neg

/-- Bilinear interpolation on a rectangle bounds a product by its four corners,
including intervals of arbitrary sign. -/
private theorem product_bounds {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
      x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have lac : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ a*c :=
    (min_le_left _ _).trans (min_le_left _ _)
  have lad : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ a*d :=
    (min_le_left _ _).trans (min_le_right _ _)
  have lbc : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ b*c :=
    (min_le_right _ _).trans (min_le_left _ _)
  have lbd : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ b*d :=
    (min_le_right _ _).trans (min_le_right _ _)
  have uac : a*c ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) :=
    (le_max_left _ _).trans (le_max_left _ _)
  have uad : a*d ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) :=
    (le_max_right _ _).trans (le_max_left _ _)
  have ubc : b*c ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have ubd : b*d ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  by_cases hxx : 0 ≤ x
  · constructor
    · have hxy : x*c ≤ x*y := mul_le_mul_of_nonneg_left hy.1 hxx
      by_cases hcc : 0 ≤ c
      · exact lac.trans ((mul_le_mul_of_nonneg_right hx.1 hcc).trans hxy)
      · exact lbc.trans ((mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hcc)).trans hxy)
    · have hxy : x*y ≤ x*d := mul_le_mul_of_nonneg_left hy.2 hxx
      by_cases hdd : 0 ≤ d
      · exact hxy.trans ((mul_le_mul_of_nonneg_right hx.2 hdd).trans ubd)
      · exact hxy.trans ((mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hdd)).trans uad)
  · have hxx' : x ≤ 0 := le_of_not_ge hxx
    constructor
    · have hxy : x*d ≤ x*y := mul_le_mul_of_nonpos_left hy.2 hxx'
      by_cases hdd : 0 ≤ d
      · exact lad.trans ((mul_le_mul_of_nonneg_right hx.1 hdd).trans hxy)
      · exact lbd.trans ((mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hdd)).trans hxy)
    · have hxy : x*y ≤ x*c := mul_le_mul_of_nonpos_left hy.1 hxx'
      by_cases hcc : 0 ≤ c
      · exact hxy.trans ((mul_le_mul_of_nonneg_right hx.2 hcc).trans ubc)
      · exact hxy.trans ((mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hcc)).trans uac)

theorem Contains.mul {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.mul J).Contains (x * y) := by
  simpa only [RatInterval.mul, Contains, Rat.cast_min, Rat.cast_max, Rat.cast_mul] using
    product_bounds hx hy

theorem Contains.scale {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) (q : ℚ) : (scale q I).Contains ((q : ℝ) * x) :=
  (contains_point q).mul hx

theorem Contains.half {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) : I.half.Contains (x / 2) := by
  change (RatInterval.scale (1 / 2) I).Contains (x / 2)
  convert hx.scale (1 / 2) using 1
  norm_num
  ring

/-- Soundness of any outward enclosure proposed by an integer-square-root routine.
The endpoint checks are rational inequalities suitable for kernel evaluation. -/
theorem contains_sqrt {I J : RatInterval} {x : ℝ} (hx : I.Contains x)
    (hLowerNonneg : 0 ≤ J.lower) (hInputNonneg : 0 ≤ I.lower)
    (hLowerSquare : J.lower ^ 2 ≤ I.lower)
    (hUpperNonneg : 0 ≤ J.upper) (hUpperSquare : I.upper ≤ J.upper ^ 2) :
    J.Contains (Real.sqrt x) := by
  constructor
  · apply (Real.le_sqrt (by exact_mod_cast hLowerNonneg)
      ((by exact_mod_cast hInputNonneg : (0 : ℝ) ≤ I.lower).trans hx.1)).2
    exact (by exact_mod_cast hLowerSquare : (J.lower : ℝ) ^ 2 ≤ I.lower).trans hx.1
  · apply (Real.sqrt_le_left (by exact_mod_cast hUpperNonneg)).2
    exact hx.2.trans (by exact_mod_cast hUpperSquare)

theorem Contains.weaken {I J : RatInterval} {x : ℝ} (hx : I.Contains x)
    (hLower : J.lower ≤ I.lower) (hUpper : I.upper ≤ J.upper) : J.Contains x :=
  ⟨(by exact_mod_cast hLower : (J.lower : ℝ) ≤ I.lower).trans hx.1,
    hx.2.trans (by exact_mod_cast hUpper : (I.upper : ℝ) ≤ J.upper)⟩

theorem Contains.positive {I : RatInterval} {x : ℝ} (hx : I.Contains x)
    (hLower : 0 < I.lower) : 0 < x :=
  (by exact_mod_cast hLower : (0 : ℝ) < I.lower).trans_le hx.1

/-- Exact interval accumulation; any outward rounding is checked separately by `weaken`. -/
def sum (boxes : List RatInterval) : RatInterval := boxes.foldr RatInterval.add (point 0)

theorem Contains.sum {boxes : List RatInterval} {values : List ℝ}
    (h : List.Forall₂ RatInterval.Contains boxes values) :
    (RatInterval.sum boxes).Contains values.sum := by
  induction h with
  | nil => simpa only [RatInterval.sum, List.foldr_nil, List.sum_nil,
      Rat.cast_zero] using contains_point 0
  | cons hx _ ih => exact hx.add ih

theorem contains_sum_map {ι : Type*} (l : List ι)
    (boxes : ι → RatInterval) (values : ι → ℝ)
    (h : ∀ i ∈ l, (boxes i).Contains (values i)) :
    (RatInterval.sum (l.map boxes)).Contains (l.map values).sum := by
  induction l with
  | nil => simpa only [List.map_nil, RatInterval.sum, List.foldr_nil,
      List.sum_nil, Rat.cast_zero] using contains_point 0
  | cons i l ih =>
    exact (h i (List.mem_cons_self)).add
      (ih (fun j hj ↦ h j (List.mem_cons_of_mem i hj)))

def finsetSum {ι : Type*} (s : Finset ι) (boxes : ι → RatInterval) : RatInterval :=
  ⟨∑ i ∈ s, (boxes i).lower, ∑ i ∈ s, (boxes i).upper⟩

theorem contains_finsetSum {ι : Type*} (s : Finset ι)
    (boxes : ι → RatInterval) (values : ι → ℝ)
    (h : ∀ i ∈ s, (boxes i).Contains (values i)) :
    (finsetSum s boxes).Contains (∑ i ∈ s, values i) := by
  constructor
  · change ((∑ i ∈ s, (boxes i).lower : ℚ) : ℝ) ≤ ∑ i ∈ s, values i
    push_cast
    exact Finset.sum_le_sum (fun i hi ↦ (h i hi).1)
  · change (∑ i ∈ s, values i) ≤ ((∑ i ∈ s, (boxes i).upper : ℚ) : ℝ)
    push_cast
    exact Finset.sum_le_sum (fun i hi ↦ (h i hi).2)

end RatInterval
end ADMM.RefinedEndpoint
