/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

/- Proposition 3.21 lies in finite-family convex analysis.

Sampled owner-style declarations:
- mathlib `ConvexOn.map_sum_le`, the canonical finite operational convexity API;
- mathlib `convexOn_exp`, the canonical convexity owner for `Real.exp`;
- mathlib `strictConcaveOn_log_Ioi`, the canonical logarithm concavity API on positive reals.

Best owner abstraction:
- `ConvexOn` on a common domain, with the finite family carried by a `Finset` rather than by a
  concrete `Fin m` index model.

Primitive data:
- a set `s : Set E`;
- a finite index set `t : Finset ι`;
- a nonemptiness witness `ht : t.Nonempty`;
- a family `f : ι → E → ℝ`;
- convexity witnesses `hf : ∀ i ∈ t, ConvexOn ℝ s (f i)`.

Derived API:
- the finite log-sum-exp objective `x ↦ log (∑ i ∈ t, exp (f i x))`;
- `Fin m` and whole-space specializations obtained by taking `t = Finset.univ` and
  `s = Set.univ`.

Source/core/bridge triage:
- source-facing/core: this theorem itself, which is the chapter owner for finite log-sum-exp
  convexity on a common domain;
- bridge/view: downstream `Fin m` and `Set.univ` specializations.
-/

variable {ι E : Type*}
variable [AddCommMonoid E] [Module ℝ E]

/-- Helper for Proposition 3.21: exponentiating the convexity inequality turns the affine bound
into a multiplicative bound. -/
lemma exp_convex_combination_le
    {s : Set E} {g : E → ℝ} (hg : ConvexOn ℝ s g)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Real.exp (g (a • x + b • y)) ≤ (Real.exp (g x)) ^ a * (Real.exp (g y)) ^ b := by
  -- Rewrite the convexity bound into the multiplicative exponential form used later in the sum.
  have hconv : g (a • x + b • y) ≤ a * g x + b * g y := by
    simpa [smul_eq_mul] using hg.2 hx hy ha hb hab
  calc
    Real.exp (g (a • x + b • y)) ≤ Real.exp (a * g x + b * g y) := Real.exp_le_exp.mpr hconv
    _ = Real.exp (a * g x) * Real.exp (b * g y) := by rw [Real.exp_add]
    _ = (Real.exp (g x)) ^ a * (Real.exp (g y)) ^ b := by
      rw [mul_comm a _, mul_comm b _, Real.exp_mul, Real.exp_mul]

omit [AddCommMonoid E] [Module ℝ E] in
/-- Helper for Proposition 3.21: a nonempty finite sum of exponentials is strictly positive. -/
lemma sum_exp_pos
    {t : Finset ι} (ht : t.Nonempty) (f : ι → E → ℝ) (x : E) :
    0 < ∑ i ∈ t, Real.exp (f i x) := by
  -- Every summand is positive, so the whole finite sum is positive on a nonempty index set.
  exact Finset.sum_pos (fun i hi ↦ Real.exp_pos _) ht

omit [AddCommMonoid E] [Module ℝ E] in
/-- Helper for Proposition 3.21: finite Hölder yields the weighted geometric mean estimate for a
sum of nonnegative terms. -/
lemma weighted_geometric_mean_sum_le
    (t : Finset ι) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (u v : ι → ℝ) (hu : ∀ i ∈ t, 0 ≤ u i) (hv : ∀ i ∈ t, 0 ≤ v i) :
    ∑ i ∈ t, (u i) ^ a * (v i) ^ b ≤ (∑ i ∈ t, u i) ^ a * (∑ i ∈ t, v i) ^ b := by
  -- Apply finite Hölder to the sequences `u^a` and `v^b`, then simplify the exponents.
  let p : ℝ := 1 / a
  let q : ℝ := 1 / b
  have ha_lt_one : a < 1 := by nlinarith [hb, hab]
  have hpq : p.HolderConjugate q := by
    refine Real.holderConjugate_iff.mpr ?_
    constructor
    · dsimp [p]
      simpa [one_div] using (one_lt_inv₀ ha).2 ha_lt_one
    · dsimp [p, q]
      field_simp [ha.ne', hb.ne']
      nlinarith [hab]
  have hHolder := Real.inner_le_Lp_mul_Lq_of_nonneg (s := t) (p := p) (q := q) hpq
    (f := fun i ↦ (u i) ^ a) (g := fun i ↦ (v i) ^ b)
    (by intro i hi; exact Real.rpow_nonneg (hu i hi) _)
    (by intro i hi; exact Real.rpow_nonneg (hv i hi) _)
  have hsum_u : ∑ i ∈ t, ((u i) ^ a) ^ p = ∑ i ∈ t, u i := by
    -- The conjugate exponent `p = 1 / a` exactly inverts the power `a`.
    refine Finset.sum_congr rfl ?_
    intro i hi
    dsimp [p]
    rw [← Real.rpow_mul (hu i hi)]
    field_simp [ha.ne']
    rw [Real.rpow_one]
  have hsum_v : ∑ i ∈ t, ((v i) ^ b) ^ q = ∑ i ∈ t, v i := by
    -- The same simplification holds for the `v`-sequence with exponent `q = 1 / b`.
    refine Finset.sum_congr rfl ?_
    intro i hi
    dsimp [q]
    rw [← Real.rpow_mul (hv i hi)]
    field_simp [hb.ne']
    rw [Real.rpow_one]
  have hp_inv : 1 / p = a := by
    dsimp [p]
    field_simp [ha.ne']
  have hq_inv : 1 / q = b := by
    dsimp [q]
    field_simp [hb.ne']
  rw [hsum_u, hsum_v, hp_inv, hq_inv] at hHolder
  simpa using hHolder

omit [AddCommMonoid E] [Module ℝ E] in
/-- Helper for Proposition 3.21: the logarithm of the product of two positive real powers splits
into the expected weighted sum. -/
lemma log_rpow_mul_rpow
    {A B a b : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Real.log (A ^ a * B ^ b) = a * Real.log A + b * Real.log B := by
  -- Positivity lets us expand the logarithm across the product and then across each power.
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hA, Real.log_rpow hB]

/-- Proposition 3.21: the log-sum-exp of a nonempty finite family of convex functions is convex on
their common domain. -/
-- Proof sketch: apply convexity of each `f i` to the convex combination of two points, then
-- exponentiate and sum the resulting inequalities. Hölder's inequality gives the key estimate
-- `∑ i, exp (f i (θ • x + (1 - θ) • y)) ≤ (∑ i, exp (f i x))^θ (∑ i, exp (f i y))^(1 - θ)`,
-- and taking `Real.log` yields the convexity inequality.
theorem convexOn_log_sum_exp_of_convexOn
    (s : Set E) {t : Finset ι} {f : ι → E → ℝ}
    (ht : t.Nonempty) (hf : ∀ i ∈ t, ConvexOn ℝ s (f i)) :
    ConvexOn ℝ s (fun x ↦ Real.log (∑ i ∈ t, Real.exp (f i x))) := by
  refine ⟨?_, ?_⟩
  · -- Any one family member already carries the common-domain convexity of `s`.
    rcases ht with ⟨i, hi⟩
    exact (hf i hi).1
  · intro x hx y hy a b ha hb hab
    -- Rewrite scalar multiplication on `ℝ` as ordinary multiplication before the final estimate.
    simp only [smul_eq_mul]
    by_cases ha0 : a = 0
    · -- Endpoint `a = 0`: the convex combination collapses to `y`.
      subst a
      have hb1 : b = 1 := by nlinarith [hab]
      simp [hb1]
    · by_cases hb0 : b = 0
      · -- Endpoint `b = 0`: the convex combination collapses to `x`.
        subst b
        have ha1 : a = 1 := by nlinarith [hab]
        simp [ha1]
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
        have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb0)
        have hsum_le_weighted :
            ∑ i ∈ t, Real.exp (f i (a • x + b • y))
              ≤ ∑ i ∈ t, (Real.exp (f i x)) ^ a * (Real.exp (f i y)) ^ b := by
          -- Sum the pointwise convexity estimates after exponentiating each one.
          refine Finset.sum_le_sum ?_
          intro i hi
          exact exp_convex_combination_le (hf i hi) hx hy ha hb hab
        have hweighted :
            ∑ i ∈ t, (Real.exp (f i x)) ^ a * (Real.exp (f i y)) ^ b
              ≤ (∑ i ∈ t, Real.exp (f i x)) ^ a * (∑ i ∈ t, Real.exp (f i y)) ^ b := by
          -- This is the finite Hölder step from the textbook proof.
          exact
            weighted_geometric_mean_sum_le t ha_pos hb_pos hab
              (fun i ↦ Real.exp (f i x)) (fun i ↦ Real.exp (f i y))
              (fun i hi ↦ (Real.exp_pos _).le) (fun i hi ↦ (Real.exp_pos _).le)
        have hsum_pos_xy : 0 < ∑ i ∈ t, Real.exp (f i (a • x + b • y)) :=
          sum_exp_pos ht f (a • x + b • y)
        have hsum_pos_x : 0 < ∑ i ∈ t, Real.exp (f i x) := sum_exp_pos ht f x
        have hsum_pos_y : 0 < ∑ i ∈ t, Real.exp (f i y) := sum_exp_pos ht f y
        calc
          Real.log (∑ i ∈ t, Real.exp (f i (a • x + b • y)))
              ≤ Real.log ((∑ i ∈ t, Real.exp (f i x)) ^ a * (∑ i ∈ t, Real.exp (f i y)) ^ b) :=
            Real.log_le_log hsum_pos_xy (hsum_le_weighted.trans hweighted)
          _ = a * Real.log (∑ i ∈ t, Real.exp (f i x))
                + b * Real.log (∑ i ∈ t, Real.exp (f i y)) :=
            log_rpow_mul_rpow hsum_pos_x hsum_pos_y

end
