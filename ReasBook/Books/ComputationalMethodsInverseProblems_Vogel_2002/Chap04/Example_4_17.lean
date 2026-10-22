/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_15.Likelihood
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_17.PoissonLikelihood

public section

open PoissonLikelihood
open scoped NNReal

universe u

section

variable {ι : Type u} [Fintype ι]

/-- Helper for Example 4.17: taking `Real.log` of a single Poisson mass factor produces the
expected affine-log expression. -/
lemma log_poissonMassFactor_eq {k : ℕ} {r : ℝ≥0} (hr : 0 < (r : ℝ)) :
    Real.log (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / ((Nat.factorial k : ℝ))) =
      -(r : ℝ) + (k : ℝ) * Real.log (r : ℝ) - Real.log ((Nat.factorial k : ℝ)) := by
  -- Split the logarithm of the Poisson factor into exponential, power, and factorial pieces.
  rw [Real.log_div (by positivity) (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k))]
  rw [Real.log_mul (Real.exp_pos _).ne' (pow_ne_zero _ hr.ne')]
  rw [show ((r : ℝ) ^ k) = (r : ℝ) ^ (k : ℝ) by rw [Real.rpow_natCast]]
  rw [Real.log_exp, Real.log_rpow hr]

/-- Helper for Example 4.17: the one-dimensional Poisson objective `x ↦ x - a * log x` is
strictly convex on `(0, ∞)` when `a > 0`. -/
lemma poissonCoordinateStrictConvexOn {a : ℝ} (ha : 0 < a) :
    StrictConvexOn ℝ (Set.Ioi 0) (fun x : ℝ ↦ x - a * Real.log x) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy hxy α β hα hβ hαβ
  -- Strict concavity of `log` gives the only strict step; the affine part is exact.
  have hlog :
      α * Real.log x + β * Real.log y < Real.log (α * x + β * y) := by
    simpa [smul_eq_mul] using strictConcaveOn_log_Ioi.2 hx hy hxy hα hβ hαβ
  have hscaled :
      a * (α * Real.log x + β * Real.log y) < a * Real.log (α * x + β * y) :=
    mul_lt_mul_of_pos_left hlog ha
  calc
    (α * x + β * y) - a * Real.log (α * x + β * y) <
        (α * x + β * y) - a * (α * Real.log x + β * Real.log y) := by
      linarith
    _ = α * (x - a * Real.log x) + β * (y - a * Real.log y) := by
      ring

/-- Helper for Example 4.17: for positive `a` and `b`, the scalar Poisson objective is minimized
at `b = a`. -/
lemma poissonCoordinateObjective_le_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a - a * Real.log a ≤ b - a * Real.log b := by
  -- Apply the standard bound `log t ≤ t - 1` to `t = b / a` and rearrange.
  have hscaled :
      a * Real.log (b / a) ≤ b - a := by
    calc
      a * Real.log (b / a) ≤ a * (b / a - 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hb ha)) ha.le
      _ = b - a := by
        calc
          a * (b / a - 1) = a * (b / a) - a := by ring
          _ = a * (b * a⁻¹) - a := by rw [div_eq_mul_inv]
          _ = (a * a⁻¹) * b - a := by ring
          _ = b - a := by rw [mul_inv_cancel₀ ha.ne', one_mul]
  have hrearranged :
      a * Real.log b - a * Real.log a ≤ b - a := by
    simpa [Real.log_div hb.ne' ha.ne', mul_sub] using hscaled
  linarith

/-- Helper for Example 4.17: each scalar Poisson mass factor is maximized at the observed count,
including the boundary case `r = 0`. -/
lemma poissonMassFactor_le_at_observedCount (k : ℕ) (r : ℝ≥0) :
    Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / ((Nat.factorial k : ℝ)) ≤
      Real.exp (-(k : ℝ)) * (k : ℝ) ^ k / ((Nat.factorial k : ℝ)) := by
  rcases eq_or_ne k 0 with rfl | hk0
  · -- When the observed count is zero, only the exponential term remains.
    have hrnonneg : 0 ≤ (r : ℝ) := by exact_mod_cast r.2
    have hexp : Real.exp (-(r : ℝ)) ≤ Real.exp 0 := by
      exact Real.exp_le_exp.mpr (by linarith)
    convert hexp using 1 <;> simp
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    rcases eq_or_ne r 0 with rfl | hr0
    · -- For positive counts, the boundary rate `r = 0` makes the mass factor vanish.
      have hright :
          0 ≤ Real.exp (-(k : ℝ)) * (k : ℝ) ^ k / ((Nat.factorial k : ℝ)) := by
        positivity
      simpa [hk.ne'] using hright
    · have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
      have hr : 0 < (r : ℝ) := by
        exact_mod_cast (show 0 < r from pos_iff_ne_zero.mpr hr0)
      have hobjective :
          -(r : ℝ) + (k : ℝ) * Real.log (r : ℝ) ≤
            -(k : ℝ) + (k : ℝ) * Real.log (k : ℝ) := by
        have hmin := poissonCoordinateObjective_le_of_pos hkReal hr
        linarith
      have hprod :
          Real.exp (-(r : ℝ)) * (r : ℝ) ^ k ≤
            Real.exp (-(k : ℝ)) * (k : ℝ) ^ k := by
        have hexp :
            Real.exp (-(r : ℝ) + (k : ℝ) * Real.log (r : ℝ)) ≤
              Real.exp (-(k : ℝ) + (k : ℝ) * Real.log (k : ℝ)) :=
          Real.exp_le_exp.mpr hobjective
        have hleft :
            Real.exp (-(r : ℝ) + (k : ℝ) * Real.log (r : ℝ)) =
              Real.exp (-(r : ℝ)) * (r : ℝ) ^ k := by
          calc
            Real.exp (-(r : ℝ) + (k : ℝ) * Real.log (r : ℝ)) =
                Real.exp (-(r : ℝ)) * Real.exp ((k : ℝ) * Real.log (r : ℝ)) := by
              rw [Real.exp_add]
            _ = Real.exp (-(r : ℝ)) * Real.exp (Real.log ((r : ℝ) ^ (k : ℝ))) := by
              rw [← Real.log_rpow hr (k : ℝ)]
            _ = Real.exp (-(r : ℝ)) * ((r : ℝ) ^ (k : ℝ)) := by
              rw [Real.exp_log (by positivity)]
            _ = Real.exp (-(r : ℝ)) * (r : ℝ) ^ k := by
              rw [Real.rpow_natCast]
        have hright :
            Real.exp (-(k : ℝ) + (k : ℝ) * Real.log (k : ℝ)) =
              Real.exp (-(k : ℝ)) * (k : ℝ) ^ k := by
          calc
            Real.exp (-(k : ℝ) + (k : ℝ) * Real.log (k : ℝ)) =
                Real.exp (-(k : ℝ)) * Real.exp ((k : ℝ) * Real.log (k : ℝ)) := by
              rw [Real.exp_add]
            _ = Real.exp (-(k : ℝ)) * Real.exp (Real.log ((k : ℝ) ^ (k : ℝ))) := by
              rw [← Real.log_rpow hkReal (k : ℝ)]
            _ = Real.exp (-(k : ℝ)) * ((k : ℝ) ^ (k : ℝ)) := by
              rw [Real.exp_log (by positivity)]
            _ = Real.exp (-(k : ℝ)) * (k : ℝ) ^ k := by
              rw [Real.rpow_natCast]
        rw [hleft, hright] at hexp
        exact hexp
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hprod (by positivity : 0 ≤ ((Nat.factorial k : ℝ)⁻¹))

/-- First claim of Example 4.17: for strictly positive rates, the negative log-likelihood of the
finite
Poisson model is `poissonNegLogLikelihood d (fun i ↦ (rate i : ℝ)) +
poissonNegLogLikelihoodConst d`. -/
theorem negLog_poissonLikelihood_eq (d : ι → ℕ) (rate : ι → ℝ≥0)
    (hpos : ∀ i, 0 < (rate i : ℝ)) :
    -Real.log
        (ProbabilityTheory.likelihood
          (fun rate x ↦ (ProbabilityTheory.poissonVector rate).real {x})
          (fun i ↦ (d i : ℝ))
          rate) =
      poissonNegLogLikelihood d (fun i ↦ (rate i : ℝ)) + poissonNegLogLikelihoodConst d := by
  -- Rewrite the finite likelihood as a product and then take logarithms factorwise.
  rw [likelihood_poissonVector_eq]
  rw [Real.log_prod (s := (Finset.univ : Finset ι))]
  · calc
      -∑ i, Real.log
          (Real.exp (-(rate i : ℝ)) * (rate i : ℝ) ^ d i / ((Nat.factorial (d i) : ℝ))) =
          ∑ i, -Real.log
            (Real.exp (-(rate i : ℝ)) * (rate i : ℝ) ^ d i / ((Nat.factorial (d i) : ℝ))) := by
        rw [← Finset.sum_neg_distrib]
      _ =
          ∑ i,
            ((rate i : ℝ) - (d i : ℝ) * Real.log (rate i : ℝ) +
              Real.log ((Nat.factorial (d i) : ℝ))) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [log_poissonMassFactor_eq (k := d i) (r := rate i) (hpos i)]
        ring
      _ =
          (∑ i, ((rate i : ℝ) - (d i : ℝ) * Real.log (rate i : ℝ))) +
            ∑ i, Real.log ((Nat.factorial (d i) : ℝ)) := by
        rw [Finset.sum_add_distrib]
      _ = poissonNegLogLikelihood d (fun i ↦ (rate i : ℝ)) + poissonNegLogLikelihoodConst d := by
        rw [poissonNegLogLikelihood_def, poissonNegLogLikelihoodConst_def]
  · intro i hi
    exact div_ne_zero
      (mul_ne_zero (Real.exp_pos _).ne' (pow_ne_zero _ (hpos i).ne'))
      (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero (d i)))

/-- Strict-convexity claim used in Example 4.17: if every observed count is strictly positive,
then the Poisson negative
log-likelihood is strictly convex on the positive orthant. The extra hypothesis is required for
the strict-convexity claim to be mathematically correct. -/
theorem poissonNegLogLikelihood_strictConvexOn (d : ι → ℕ) (hposd : ∀ i, 0 < d i) :
    StrictConvexOn ℝ (positiveOrthant ι) (poissonNegLogLikelihood d) := by
  refine ⟨?_, ?_⟩
  · -- The positive orthant is a product of convex open rays.
    have hset : positiveOrthant ι = Set.pi Set.univ (fun _ : ι ↦ Set.Ioi (0 : ℝ)) := by
      ext x
      simp [mem_positiveOrthant_iff]
    rw [hset]
    exact
      convex_pi (s := Set.univ) (t := fun _ : ι ↦ Set.Ioi (0 : ℝ))
        (fun {_} _ ↦ convex_Ioi (0 : ℝ))
  · intro x hx y hy hxy a b ha hb hab
    -- Extract coordinatewise positivity and one coordinate where the vectors differ.
    have hxpos : ∀ i, 0 < x i := (mem_positiveOrthant_iff x).1 hx
    have hypos : ∀ i, 0 < y i := (mem_positiveOrthant_iff y).1 hy
    obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ y i := by
      by_contra h
      apply hxy
      funext i
      by_contra hxyi
      exact h ⟨i, hxyi⟩
    have hsum :
        ∑ i, (a * x i + b * y i - (d i : ℝ) * Real.log (a * x i + b * y i)) <
          ∑ i,
            (a * (x i - (d i : ℝ) * Real.log (x i)) +
              b * (y i - (d i : ℝ) * Real.log (y i))) := by
      refine Finset.sum_lt_sum ?_ ?_
      · intro i hi
        have hcoord :=
          (poissonCoordinateStrictConvexOn
            (a := (d i : ℝ)) (by exact_mod_cast hposd i)).convexOn
        exact hcoord.2 (hxpos i) (hypos i) ha.le hb.le hab
      · refine ⟨i0, Finset.mem_univ _, ?_⟩
        exact
          (poissonCoordinateStrictConvexOn
            (a := (d i0 : ℝ)) (by exact_mod_cast hposd i0)).2
            (hxpos i0) (hypos i0) hi0 ha hb hab
    -- Sum the coordinatewise strict inequalities to recover the full objective.
    calc
      poissonNegLogLikelihood d (a • x + b • y) =
          ∑ i, (a * x i + b * y i - (d i : ℝ) * Real.log (a * x i + b * y i)) := by
        simp [poissonNegLogLikelihood_def, smul_eq_mul]
      _ <
          ∑ i,
            (a * (x i - (d i : ℝ) * Real.log (x i)) +
              b * (y i - (d i : ℝ) * Real.log (y i))) :=
        hsum
      _ =
          a * poissonNegLogLikelihood d x + b * poissonNegLogLikelihood d y := by
        rw [poissonNegLogLikelihood_def, poissonNegLogLikelihood_def]
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Example 4.17: the observed count vector is a maximum-likelihood estimator on the closed
parameter space `ι → ℝ≥0`. -/
theorem isPoissonMLE_observedCountVector (d : ι → ℕ) :
    ProbabilityTheory.IsMLE
      (ProbabilityTheory.likelihood
        (fun rate x ↦ (ProbabilityTheory.poissonVector rate).real {x})
        (fun i ↦ (d i : ℝ)))
      (fun i ↦ (d i : ℝ≥0)) := by
  -- Route correction: the boundary `rate i = 0` belongs to the parameter space, so maximize the
  -- likelihood directly instead of passing through the positive-orthant log-likelihood formula.
  rw [ProbabilityTheory.isMLE_iff, isMaxOn_univ_iff]
  intro rate
  rw [likelihood_poissonVector_eq, likelihood_poissonVector_eq]
  refine Finset.prod_le_prod ?_ ?_
  · intro i hi
    positivity
  · intro i hi
    simpa using poissonMassFactor_le_at_observedCount (d i) (rate i)

end
