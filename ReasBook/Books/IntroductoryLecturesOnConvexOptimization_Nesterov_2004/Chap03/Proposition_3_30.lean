/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_35

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Proposition 3.30 lies in the finite-dimensional Nemirovski hard-instance minimization domain.

Mandatory domain-style sampling before refinement:
- `f_k`, `FirstKIndex`, and `firstKCoordinateFamily` in `Definition_3_35`, the chapter owner
  surface for the hard-instance objective and its first-`k` coordinate family;
- `IsMinOn` and `isMinOn_univ_iff`, the canonical owner API for unconstrained minimizers on
  `Set.univ`;
- `EuclideanSpace.equiv` and `EuclideanSpace.norm_eq`, the canonical coordinate and norm API on
  `EuclideanSpace ℝ (Fin n)`.

Best owner abstraction:
- source-facing: the explicit optimizer/value statement for `f_k`;
- core/canonical: `f_k`, `IsMinOn`, `EuclideanSpace.equiv`, and the Euclidean norm;
- bridge/view: the coordinate evaluation lemma for the explicit optimizer.

Primitive data:
- the ambient dimension `n`;
- the prefix length `k`;
- the hard-instance parameters `μ` and `γ`.

Derived API:
- the explicit vector `f_k_minimizer`;
- the coordinate formula `f_k_minimizer_apply`;
- the minimizing property, attained value, and norm formula below.

Source/core/bridge triage:
- source-facing: the explicit optimizer/value/norm formulas in Proposition 3.30;
- core/canonical: `f_k`, `IsMinOn`, `EuclideanSpace.equiv`, and `‖·‖`;
- bridge/view: the coordinate evaluation lemma for the pointwise minimizer.

This file keeps the source-facing explicit optimizer, but it no longer rebuilds the first-`k`
support through a basis-sum package. The primitive owner data is the pointwise coordinate formula,
and the explicit coordinate theorem is the public bridge back to the textbook description. -/

/-- The explicit minimizer from Proposition 3.30, with constant value `-γ / (μ k)` on the first
`k` coordinates and value `0` afterwards. -/
def f_k_minimizer (n k : ℕ) (μ γ : ℝ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun i ↦ if i.1 < k then -(γ / (μ * (k : ℝ))) else 0)

/-- The coordinates of `f_k_minimizer` are constant on the first `k` slots and vanish afterwards. -/
@[simp] theorem f_k_minimizer_apply (n k : ℕ) (μ γ : ℝ) (i : Fin n) :
    f_k_minimizer n k μ γ i = if i.1 < k then -(γ / (μ * (k : ℝ))) else 0 :=
  rfl

section

variable (n k : ℕ) (μ γ : ℝ)

/-- Helper for Proposition 3.30: each of the first `k` coordinates is bounded above by the
prefix maximum. -/
theorem first_k_coordinate_le_first_k_coordinate_max
    (hk : 0 < k) (hkn : k ≤ n) (x : EuclideanSpace ℝ (Fin n)) (i : Fin k) :
    x (Fin.castLE hkn i) ≤ first_k_coordinate_max n k x := by
  let _ : Nonempty (FirstKIndex n k) := firstKIndex_nonempty (n := n) hk hkn
  -- Rewrite the real-valued maximum as the finite supremum over the restricted coordinate family.
  rw [← WithTop.coe_le_coe]
  rw [coe_first_k_coordinate_max_eq_pointwiseSupremumOn_univ (n := n) (k := k) (x := x)]
  rw [pointwiseSupremumOn_univ_eq_sup']
  let j : FirstKIndex n k := ⟨Fin.castLE hkn i, by simp [i.2]⟩
  have hj : j ∈ (Finset.univ : Finset (FirstKIndex n k)) := by
    simp [j]
  exact Finset.le_sup' (fun a : FirstKIndex n k ↦ firstKCoordinateFamily n k x a) hj

/-- Helper for Proposition 3.30: the average of the first `k` coordinates is bounded above by the
prefix maximum. -/
theorem sum_prefix_coordinates_le_mul_first_k_coordinate_max
    (hk : 0 < k) (hkn : k ≤ n) (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i : Fin k, x (Fin.castLE hkn i) ≤ (k : ℝ) * first_k_coordinate_max n k x := by
  have hcoord : ∀ i : Fin k, x (Fin.castLE hkn i) ≤ first_k_coordinate_max n k x := by
    -- Bound each active coordinate by the common prefix maximum.
    intro i
    exact first_k_coordinate_le_first_k_coordinate_max n k hk hkn x i
  -- Summing the coordinatewise bounds yields the textbook average-max inequality.
  calc
    ∑ i : Fin k, x (Fin.castLE hkn i) ≤ ∑ i : Fin k, first_k_coordinate_max n k x := by
      exact Finset.sum_le_sum fun i _ ↦ hcoord i
    _ = (k : ℝ) * first_k_coordinate_max n k x := by
      simp [mul_comm]

/-- Helper for Proposition 3.30: completing the square in a single active coordinate. -/
theorem complete_square_f_k_prefix_term (hk : 0 < k) (hμ : 0 < μ) (t : ℝ) :
    (μ / 2) * t ^ 2 + (γ / (k : ℝ)) * t =
      (μ / 2) * (t + γ / (μ * (k : ℝ))) ^ 2 - γ ^ 2 / (2 * μ * (k : ℝ) ^ 2) := by
  -- The source proof uses a direct scalar square-completion identity.
  field_simp [hk.ne', hμ.ne']
  ring

/-- Helper for Proposition 3.30: the source lower bound
`-(γ^2) / (2 μ k) ≤ f_k(x)` for all `x`. -/
theorem f_k_ge_neg_sq_div_two_mul_mu_mul_k
    (hk : 0 < k) (hkn : k ≤ n) (hμ : 0 < μ) (hγ : 0 ≤ γ)
    (x : EuclideanSpace ℝ (Fin n)) :
    -(γ ^ 2) / (2 * μ * (k : ℝ)) ≤ f_k n k μ γ x := by
  let sq : ℕ → ℝ := fun i ↦ if hi : i < n then x ⟨i, hi⟩ ^ 2 else 0
  let coord : ℕ → ℝ := fun i ↦ if hi : i < n then x ⟨i, hi⟩ else 0
  have hprefix :
      (γ / (k : ℝ)) * ∑ i : Fin k, x (Fin.castLE hkn i) ≤ γ * first_k_coordinate_max n k x := by
    -- Multiply the textbook average-max inequality by `γ / k` and simplify the right-hand side.
    have hsum := sum_prefix_coordinates_le_mul_first_k_coordinate_max n k hk hkn x
    have hscaled := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ γ / (k : ℝ))
    calc
      (γ / (k : ℝ)) * ∑ i : Fin k, x (Fin.castLE hkn i) ≤
          (γ / (k : ℝ)) * ((k : ℝ) * first_k_coordinate_max n k x) := hscaled
      _ = γ * first_k_coordinate_max n k x := by
        field_simp [hk.ne']
  have hnorm :
      ‖x‖ ^ 2 = ∑ i ∈ Finset.range n, sq i := by
    -- Rewrite the squared norm as a finite sum of coordinate squares.
    calc
      ‖x‖ ^ 2 = ∑ i : Fin n, x i ^ 2 := by
        simpa using (EuclideanSpace.real_norm_sq_eq x)
      _ = ∑ i : Fin n, sq i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [sq]
      _ = ∑ i ∈ Finset.range n, sq i := Fin.sum_univ_eq_sum_range sq n
  have hprefix_bound :
      -(γ ^ 2) / (2 * μ * (k : ℝ)) ≤
        Finset.sum (Finset.range k) (fun i ↦ (μ / 2) * sq i + (γ / (k : ℝ)) * coord i) := by
    -- Complete the square coordinatewise on the active prefix.
    have hconst_sum :
        Finset.sum (Finset.range k) (fun _ ↦ -(γ ^ 2) / (2 * μ * (k : ℝ) ^ 2)) =
          -(γ ^ 2) / (2 * μ * (k : ℝ)) := by
      simp
      field_simp [hk.ne', hμ.ne']
    calc
      -(γ ^ 2) / (2 * μ * (k : ℝ)) =
          Finset.sum (Finset.range k) (fun _ ↦ -(γ ^ 2) / (2 * μ * (k : ℝ) ^ 2)) := by
            rw [hconst_sum]
      _ ≤ Finset.sum (Finset.range k) (fun i ↦ (μ / 2) * sq i + (γ / (k : ℝ)) * coord i) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hi_lt_n : i < n := lt_of_lt_of_le (Finset.mem_range.mp hi) hkn
            have hsquare :
                0 ≤ (μ / 2) * (x ⟨i, hi_lt_n⟩ + γ / (μ * (k : ℝ))) ^ 2 := by
              positivity
            have hterm :
                -(γ ^ 2) / (2 * μ * (k : ℝ) ^ 2) ≤
                  (μ / 2) * (x ⟨i, hi_lt_n⟩) ^ 2 + (γ / (k : ℝ)) * x ⟨i, hi_lt_n⟩ := by
              rw [complete_square_f_k_prefix_term (k := k) (μ := μ) (γ := γ) hk hμ
                (x ⟨i, hi_lt_n⟩)]
              calc
                -(γ ^ 2) / (2 * μ * (k : ℝ) ^ 2) =
                    (0 : ℝ) - (γ ^ 2) / (2 * μ * (k : ℝ) ^ 2) := by
                      ring
                _ ≤ (μ / 2) * (x ⟨i, hi_lt_n⟩ + γ / (μ * (k : ℝ))) ^ 2 -
                      (γ ^ 2) / (2 * μ * (k : ℝ) ^ 2) := by
                      exact sub_le_sub_right hsquare ((γ ^ 2) / (2 * μ * (k : ℝ) ^ 2))
            simpa [sq, coord, hi_lt_n] using hterm
  have htail_nonneg :
      0 ≤ Finset.sum (Finset.Ico k n) (fun i ↦ (μ / 2) * sq i) := by
    -- The tail contributes only nonnegative quadratic terms.
    refine Finset.sum_nonneg ?_
    intro i hi
    have hi_lt_n : i < n := (Finset.mem_Ico.mp hi).2
    have hterm : 0 ≤ (μ / 2) * x ⟨i, hi_lt_n⟩ ^ 2 := by
      positivity
    simpa [sq, hi_lt_n] using hterm
  have hsq_decomp :
      (μ / 2) * (∑ i ∈ Finset.range n, sq i) + (γ / (k : ℝ)) * ∑ i : Fin k, x (Fin.castLE hkn i) =
        Finset.sum (Finset.range k) (fun i ↦ (μ / 2) * sq i + (γ / (k : ℝ)) * coord i) +
          Finset.sum (Finset.Ico k n) (fun i ↦ (μ / 2) * sq i) := by
    -- Split the norm square into prefix and tail coordinates and collect like terms.
    have hcoord_sum :
        (γ / (k : ℝ)) * ∑ i : Fin k, x (Fin.castLE hkn i) =
          Finset.sum (Finset.range k) (fun i ↦ (γ / (k : ℝ)) * coord i) := by
      calc
        (γ / (k : ℝ)) * ∑ i : Fin k, x (Fin.castLE hkn i) =
            ∑ i : Fin k, (γ / (k : ℝ)) * coord i := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i _
              have hi_lt_n : (i : ℕ) < n := lt_of_lt_of_le i.2 hkn
              have hcast : (Fin.castLE hkn i : Fin n) = ⟨i, hi_lt_n⟩ := by
                ext
                simp
              simp [coord, hi_lt_n, hcast]
        _ = Finset.sum (Finset.range k) (fun i ↦ (γ / (k : ℝ)) * coord i) := by
              simpa using (Fin.sum_univ_eq_sum_range (fun i ↦ (γ / (k : ℝ)) * coord i) k)
    calc
      (μ / 2) * (∑ i ∈ Finset.range n, sq i) + (γ / (k : ℝ)) * ∑ i : Fin k, x (Fin.castLE hkn i) =
          (μ / 2) * ((Finset.sum (Finset.range k) sq) + Finset.sum (Finset.Ico k n) sq) +
            Finset.sum (Finset.range k) (fun i ↦ (γ / (k : ℝ)) * coord i) := by
              rw [← Finset.sum_range_add_sum_Ico sq hkn, hcoord_sum]
      _ =
          Finset.sum (Finset.range k) (fun i ↦ (μ / 2) * sq i) +
            Finset.sum (Finset.Ico k n) (fun i ↦ (μ / 2) * sq i) +
            Finset.sum (Finset.range k) (fun i ↦ (γ / (k : ℝ)) * coord i) := by
              rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      _ =
          Finset.sum (Finset.Ico k n) (fun i ↦ (μ / 2) * sq i) +
            (Finset.sum (Finset.range k) (fun i ↦ (μ / 2) * sq i) +
              Finset.sum (Finset.range k) (fun i ↦ (γ / (k : ℝ)) * coord i)) := by
              ring
      _ =
          Finset.sum (Finset.Ico k n) (fun i ↦ (μ / 2) * sq i) +
            Finset.sum (Finset.range k) (fun i ↦ (μ / 2) * sq i + (γ / (k : ℝ)) * coord i) := by
              rw [← Finset.sum_add_distrib]
      _ =
          Finset.sum (Finset.range k) (fun i ↦ (μ / 2) * sq i + (γ / (k : ℝ)) * coord i) +
            Finset.sum (Finset.Ico k n) (fun i ↦ (μ / 2) * sq i) := by
              ring
  have hsquares :
      -(γ ^ 2) / (2 * μ * (k : ℝ)) ≤
        (μ / 2) * (∑ i ∈ Finset.range n, sq i) + (γ / (k : ℝ)) * ∑ i : Fin k, x (Fin.castLE hkn i) := by
    -- The completed-square lower bound plus tail nonnegativity gives the scalar lower bound.
    rw [hsq_decomp]
    nlinarith
  -- Replace the prefix average term by the larger maximum term and return to `f_k`.
  rw [f_k_def, hnorm]
  have hmain :
      (μ / 2) * (∑ i ∈ Finset.range n, sq i) + (γ / (k : ℝ)) * ∑ i : Fin k, x (Fin.castLE hkn i) ≤
        (μ / 2) * (∑ i ∈ Finset.range n, sq i) + γ * first_k_coordinate_max n k x := by
    nlinarith
  linarith

/-- Helper for Proposition 3.30: the prefix maximum of the explicit minimizer is its common active
coordinate value. -/
theorem first_k_coordinate_max_f_k_minimizer
    (hk : 0 < k) (hkn : k ≤ n) :
    first_k_coordinate_max n k (f_k_minimizer n k μ γ) = -(γ / (μ * (k : ℝ))) := by
  let _ : Nonempty (FirstKIndex n k) := firstKIndex_nonempty (n := n) hk hkn
  -- All active coordinates are equal, so the finite supremum is that same constant.
  rw [← WithTop.coe_inj]
  rw [coe_first_k_coordinate_max_eq_pointwiseSupremumOn_univ (n := n) (k := k)
    (x := f_k_minimizer n k μ γ)]
  rw [pointwiseSupremumOn_univ_eq_sup']
  have hconst :
      ∀ i : FirstKIndex n k,
        firstKCoordinateFamily n k (f_k_minimizer n k μ γ) i =
          (-(γ / (μ * (k : ℝ))) : WithTop ℝ) := by
    -- Every element of `FirstKIndex n k` lies in the constant active block of the minimizer.
    intro i
    simp [firstKCoordinateFamily, f_k_minimizer_apply, i.2]
  simp [hconst]

/-- Helper for Proposition 3.30: the explicit minimizer has the expected squared norm. -/
theorem norm_sq_f_k_minimizer
    (hk : 0 < k) (hkn : k ≤ n) (hμ : 0 < μ) :
    ‖f_k_minimizer n k μ γ‖ ^ 2 = γ ^ 2 / (μ ^ 2 * (k : ℝ)) := by
  let sq : ℕ → ℝ := fun i ↦ if hi : i < n then (f_k_minimizer n k μ γ) ⟨i, hi⟩ ^ 2 else 0
  have hnorm :
      ‖f_k_minimizer n k μ γ‖ ^ 2 = ∑ i ∈ Finset.range n, sq i := by
    -- Rewrite the squared norm as the finite sum of coordinate squares.
    calc
      ‖f_k_minimizer n k μ γ‖ ^ 2 =
          ∑ i : Fin n, (f_k_minimizer n k μ γ) i ^ 2 := by
            simpa using (EuclideanSpace.real_norm_sq_eq (f_k_minimizer n k μ γ))
      _ = ∑ i : Fin n, sq i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [sq]
      _ = ∑ i ∈ Finset.range n, sq i := Fin.sum_univ_eq_sum_range sq n
  rw [hnorm]
  rw [← Finset.sum_range_add_sum_Ico sq hkn]
  have htail : ∑ i ∈ Finset.Ico k n, sq i = 0 := by
    -- The minimizer vanishes on all coordinates beyond the active prefix.
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_lt_n : i < n := (Finset.mem_Ico.mp hi).2
    have hk_le_i : k ≤ i := (Finset.mem_Ico.mp hi).1
    simp [sq, hi_lt_n, f_k_minimizer_apply, not_lt.mpr hk_le_i]
  rw [htail, add_zero]
  calc
    ∑ i ∈ Finset.range k, sq i = ∑ i ∈ Finset.range k, (γ / (μ * (k : ℝ))) ^ 2 := by
      -- On the active prefix, every coordinate has the same absolute value.
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hi_lt_n : i < n := lt_of_lt_of_le (Finset.mem_range.mp hi) hkn
      have hi_lt_k : i < k := Finset.mem_range.mp hi
      simp [sq, hi_lt_n, f_k_minimizer_apply, hi_lt_k]
    _ = (k : ℝ) * (γ / (μ * (k : ℝ))) ^ 2 := by
      simp
    _ = γ ^ 2 / (μ ^ 2 * (k : ℝ)) := by
      field_simp [hk.ne', hμ.ne']

/-- Helper for Proposition 3.30: evaluating `f_k` at the explicit minimizer gives the displayed
optimal value. -/
theorem f_k_minimizer_value_eq
    (hk : 0 < k) (hkn : k ≤ n) (hμ : 0 < μ) :
    f_k n k μ γ (f_k_minimizer n k μ γ) = -(γ ^ 2) / (2 * μ * (k : ℝ)) := by
  -- Evaluate `f_k` by inserting the explicit norm and prefix-maximum formulas.
  rw [f_k_def]
  rw [first_k_coordinate_max_f_k_minimizer n k μ γ hk hkn]
  rw [norm_sq_f_k_minimizer n k μ γ hk hkn hμ]
  field_simp [hk.ne', hμ.ne']
  ring

-- Proof sketch: for `γ ≥ 0`, bound the first-coordinate maximum from below by the average of the
-- first `k` coordinates, complete the square, and evaluate the resulting lower bound at
-- `f_k_minimizer`.
/-- Proposition 3.30: if `0 < k ≤ n`, `μ > 0`, and `γ ≥ 0`, then the explicit vector
`f_k_minimizer n k μ γ` is a global minimizer of `f_k n k μ γ`. -/
theorem isMinOn_f_k_minimizer (hk : 0 < k) (hkn : k ≤ n) (hμ : 0 < μ) (hγ : 0 ≤ γ) :
    IsMinOn (f_k n k μ γ) Set.univ (f_k_minimizer n k μ γ) := by
  rw [isMinOn_univ_iff]
  intro x
  -- Compare every point to the common lower bound attained by the explicit minimizer.
  have hlower := f_k_ge_neg_sq_div_two_mul_mu_mul_k n k μ γ hk hkn hμ hγ x
  have hvalue := f_k_minimizer_value_eq n k μ γ hk hkn hμ
  linarith

/-- If `0 < k ≤ n`, `μ > 0`, and `γ ≥ 0`, evaluating `f_k` at the explicit minimizer gives the
value `-γ^2 / (2 μ k)`. -/
theorem f_k_minimizer_value (hk : 0 < k) (hkn : k ≤ n) (hμ : 0 < μ) (_hγ : 0 ≤ γ) :
    f_k n k μ γ (f_k_minimizer n k μ γ) = -(γ ^ 2) / (2 * μ * (k : ℝ)) := by
  -- This is the explicit evaluation established in the helper above.
  exact f_k_minimizer_value_eq n k μ γ hk hkn hμ

-- Proof sketch: compute the squared norm from the `k` equal nonzero coordinates and then take the
-- square root, using `k ≤ n` to identify exactly how many coordinates contribute.
/-- If `0 < k ≤ n`, `μ > 0`, and `γ ≥ 0`, the norm of the explicit minimizer is
`γ / (μ √k)`. -/
theorem f_k_minimizer_norm_eq (hk : 0 < k) (hkn : k ≤ n) (hμ : 0 < μ) (hγ : 0 ≤ γ) :
    ‖f_k_minimizer n k μ γ‖ = γ / (μ * Real.sqrt (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by
    exact_mod_cast hk
  have hsqrtk_ne : Real.sqrt (k : ℝ) ≠ 0 := by
    exact Real.sqrt_ne_zero'.mpr hkR
  have hsq :
      ‖f_k_minimizer n k μ γ‖ ^ 2 =
        (γ / (μ * Real.sqrt (k : ℝ))) ^ 2 := by
    -- Rewrite the squared norm into the square of the claimed closed form.
    rw [norm_sq_f_k_minimizer n k μ γ hk hkn hμ]
    field_simp [hk.ne', hμ.ne', hsqrtk_ne]
    rw [Real.sq_sqrt hkR.le]
  have hsqrt := congrArg Real.sqrt hsq
  -- Taking square roots is valid because both sides are nonnegative.
  rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ γ / (μ * Real.sqrt (k : ℝ)))] at hsqrt

end
