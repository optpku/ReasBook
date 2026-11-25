/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.FixedPoint

@[expose] public section

namespace ConsensusADMM.RefinedEndpoint.Certificate

open ADMM.RefinedEndpoint

def IntInterval.zero : IntInterval := ⟨0, 0⟩
def IntInterval.add (A B : IntInterval) : IntInterval :=
  ⟨A.lower + B.lower, A.upper + B.upper⟩
def IntInterval.neg (A : IntInterval) : IntInterval := ⟨-A.upper, -A.lower⟩
def IntInterval.sub (A B : IntInterval) : IntInterval := A.add B.neg
def IntInterval.scale (c : ℤ) (A : IntInterval) : IntInterval :=
  if 0 ≤ c then ⟨c * A.lower, c * A.upper⟩ else ⟨c * A.upper, c * A.lower⟩
def IntInterval.sum (boxes : List IntInterval) : IntInterval :=
  boxes.foldr IntInterval.add IntInterval.zero

@[simp] theorem IntInterval.toRat_zero (s : ℤ) :
    IntInterval.zero.toRat s = RatInterval.point 0 := by
  apply congrArg₂ RatInterval.mk <;> simp [IntInterval.zero, toRat, RatInterval.point]

theorem IntInterval.toRat_add (A B : IntInterval) (s : ℤ) :
    (A.add B).toRat s = (A.toRat s).add (B.toRat s) := by
  apply congrArg₂ RatInterval.mk <;> simp [IntInterval.add, toRat, RatInterval.add, add_div]

theorem IntInterval.toRat_neg (A : IntInterval) (s : ℤ) :
    A.neg.toRat s = (A.toRat s).neg := by
  apply congrArg₂ RatInterval.mk <;> simp [IntInterval.neg, toRat, RatInterval.neg, neg_div]

theorem IntInterval.toRat_sub (A B : IntInterval) (s : ℤ) :
    (A.sub B).toRat s = (A.toRat s).sub (B.toRat s) := by
  simp only [IntInterval.sub, toRat_add, toRat_neg, RatInterval.sub]

theorem IntInterval.contains_add {A B : IntInterval} {s : ℤ} {x y : ℝ}
    (hx : (A.toRat s).Contains x) (hy : (B.toRat s).Contains y) :
    ((A.add B).toRat s).Contains (x + y) := by
  rw [toRat_add]
  exact hx.add hy

theorem IntInterval.contains_neg {A : IntInterval} {s : ℤ} {x : ℝ}
    (hx : (A.toRat s).Contains x) : (A.neg.toRat s).Contains (-x) := by
  rw [toRat_neg]
  exact hx.neg

theorem IntInterval.contains_sub {A B : IntInterval} {s : ℤ} {x y : ℝ}
    (hx : (A.toRat s).Contains x) (hy : (B.toRat s).Contains y) :
    ((A.sub B).toRat s).Contains (x - y) := by
  rw [toRat_sub]
  exact hx.sub hy

/-- A scalar check is performed on integer endpoints, but encloses the same real product. -/
theorem IntInterval.contains_scale {A : IntInterval} {s : ℤ} {x : ℝ}
    (hx : (A.toRat s).Contains x) (c : ℤ) :
    ((IntInterval.scale c A).toRat s).Contains ((c : ℝ) * x) := by
  simp only [toRat, RatInterval.Contains, Rat.cast_div, Rat.cast_intCast] at hx ⊢
  by_cases hc : 0 ≤ c
  · have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
    simp only [IntInterval.scale, if_pos hc, Int.cast_mul]
    exact ⟨by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hx.1 hc',
      by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hx.2 hc'⟩
  · have hc' : (c : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hc)
    simp only [IntInterval.scale, if_neg hc, Int.cast_mul]
    exact ⟨by simpa only [mul_div_assoc] using mul_le_mul_of_nonpos_left hx.2 hc',
      by simpa only [mul_div_assoc] using mul_le_mul_of_nonpos_left hx.1 hc'⟩

theorem IntInterval.contains_sum {s : ℤ} {boxes : List IntInterval} {values : List ℝ}
    (h : List.Forall₂ (fun I x ↦ (I.toRat s).Contains x) boxes values) :
    ((IntInterval.sum boxes).toRat s).Contains values.sum := by
  induction h with
  | nil => simpa only [IntInterval.sum, List.foldr_nil, toRat_zero,
      List.sum_nil, Rat.cast_zero] using RatInterval.contains_point 0
  | cons hx _ ih => exact contains_add hx ih

theorem IntInterval.contains_sum_map {ι : Type*} (l : List ι)
    (boxes : ι → IntInterval) (values : ι → ℝ) (s : ℤ)
    (h : ∀ i ∈ l, ((boxes i).toRat s).Contains (values i)) :
    ((IntInterval.sum (l.map boxes)).toRat s).Contains (l.map values).sum := by
  induction l with
  | nil => simpa only [List.map_nil, IntInterval.sum, List.foldr_nil, toRat_zero,
      List.sum_nil, Rat.cast_zero] using RatInterval.contains_point 0
  | cons i l ih =>
    exact contains_add (h i List.mem_cons_self)
      (ih (fun j hj ↦ h j (List.mem_cons_of_mem i hj)))

/-- Enlarging the common denominator by a positive integer divides the enclosed real value. -/
theorem IntInterval.contains_divisor {A : IntInterval} {s : ℤ} {x : ℝ}
    (hx : (A.toRat s).Contains x) (k : ℤ) (hk : 0 < k) :
    (A.toRat (k * s)).Contains (x / (k : ℝ)) := by
  simp only [toRat, RatInterval.Contains, Rat.cast_div, Rat.cast_intCast] at hx ⊢
  have hk' : (0 : ℝ) ≤ k := (by exact_mod_cast hk : (0 : ℝ) < k).le
  constructor
  · simpa only [Int.cast_mul, div_eq_mul_inv, mul_inv_rev, mul_assoc,
      mul_comm, mul_left_comm] using div_le_div_of_nonneg_right hx.1 hk'
  · simpa only [Int.cast_mul, div_eq_mul_inv, mul_inv_rev, mul_assoc,
      mul_comm, mul_left_comm] using div_le_div_of_nonneg_right hx.2 hk'

end ConsensusADMM.RefinedEndpoint.Certificate
