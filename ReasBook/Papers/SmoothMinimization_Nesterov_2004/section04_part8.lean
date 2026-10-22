/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import SmoothMinimization_Nesterov_2004.section04_part7

open scoped NNReal

/-- Definition 1.4.2.1.
Let `p ≥ 1` and let `m_j > 0` be weights. Given locations `c_j ∈ ℝ^n` for `j = 1, ..., p` and a
radius `\bar r > 0`, define the continuous location problem by the optimal value
`f* = min_x { f(x) := ∑_{j=1}^p m_j ‖x - c_j‖_1 : ‖x‖_1 ≤ \bar r }` (4.15). -/
noncomputable def continuousLocationOptimalValue (p n : ℕ) (m : Fin p → ℝ)
    (c : Fin p → (Fin n → ℝ)) (rbar : ℝ) : ℝ :=
  let f : (Fin n → ℝ) → ℝ := fun x => ∑ j, m j * ‖x - c j‖
  sInf (f '' { x : Fin n → ℝ | ‖x‖ ≤ rbar })

namespace continuousLocation

open scoped BigOperators

/-- On `Fin n → ℝ` with the `Pi` (sup) norm, constant functions have the same norm as their value,
provided the index type is nonempty. -/
lemma norm_const_fin (n : ℕ) (hn : 0 < n) (r : ℝ) :
    ‖(fun _ : Fin n => r)‖ = ‖r‖ := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    refine ⟨⟨0, hn⟩, by simp⟩
  simp [Pi.norm_def, Finset.sup_const hne]

/-- The constant `1` function on `Fin n` has norm `1` when `n > 0`. -/
lemma norm_const_one_fin (n : ℕ) (hn : 0 < n) : ‖(fun _ : Fin n => (1 : ℝ))‖ = (1 : ℝ) := by
  simpa using (norm_const_fin (n := n) hn (r := (1 : ℝ)))

/-- The prox-diameter term `D1` for `d1(x) = (1/2)‖x‖^2` on the ball `‖x‖ ≤ rbar`. -/
lemma D1_eq_half_rbar_sq (n : ℕ) (rbar : ℝ) (hn : 0 < n) (hrbar : 0 ≤ rbar) :
    let Q1 : Set (Fin n → ℝ) := { x | ‖x‖ ≤ rbar }
    let d1 : (Fin n → ℝ) → ℝ := fun x => (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ)
    sSup (d1 '' Q1) = (1 / 2 : ℝ) * rbar ^ (2 : ℕ) := by
  classical
  intro Q1 d1
  have hQ1_ne : (d1 '' Q1).Nonempty := by
    refine ⟨d1 0, ?_⟩
    refine ⟨0, ?_, rfl⟩
    simp [Q1, hrbar]
  have hQ1_bdd : BddAbove (d1 '' Q1) := by
    refine ⟨(1 / 2 : ℝ) * rbar ^ (2 : ℕ), ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hxpow : ‖x‖ ^ (2 : ℕ) ≤ rbar ^ (2 : ℕ) := by
      -- monotonicity of squaring on `ℝ` for nonnegative terms
      simpa [pow_two] using (mul_le_mul hx hx (norm_nonneg _) hrbar)
    exact mul_le_mul_of_nonneg_left hxpow (by norm_num)
  have hsup_le : sSup (d1 '' Q1) ≤ (1 / 2 : ℝ) * rbar ^ (2 : ℕ) := by
    refine csSup_le hQ1_ne ?_
    rintro y ⟨x, hx, rfl⟩
    have hxpow : ‖x‖ ^ (2 : ℕ) ≤ rbar ^ (2 : ℕ) := by
      simpa [pow_two] using (mul_le_mul hx hx (norm_nonneg _) hrbar)
    exact mul_le_mul_of_nonneg_left hxpow (by norm_num)
  -- attain the upper bound at the constant point `x ≡ rbar`
  let x0 : Fin n → ℝ := fun _ => rbar
  have hx0_mem : x0 ∈ Q1 := by
    have hnorm : ‖x0‖ = rbar := by
      have : ‖x0‖ = ‖rbar‖ := norm_const_fin (n := n) hn (r := rbar)
      simpa [Real.norm_eq_abs, abs_of_nonneg hrbar] using this
    simp [Q1, x0, hnorm]
  have hx0_val : d1 x0 = (1 / 2 : ℝ) * rbar ^ (2 : ℕ) := by
    have hnorm : ‖x0‖ = rbar := by
      have : ‖x0‖ = ‖rbar‖ := norm_const_fin (n := n) hn (r := rbar)
      simpa [Real.norm_eq_abs, abs_of_nonneg hrbar] using this
    simp [d1, x0, hnorm]
  have hle_sup : (1 / 2 : ℝ) * rbar ^ (2 : ℕ) ≤ sSup (d1 '' Q1) := by
    refine le_csSup hQ1_bdd ?_
    exact ⟨x0, hx0_mem, hx0_val⟩
  exact le_antisymm hsup_le hle_sup

/-- The prox-diameter term `D2` for `d2(u) = (1/2)‖u‖_2^2` with `‖u‖_2^2 = ∑ m_j ‖u_j‖^2`
over the set `‖u_j‖ ≤ 1`. -/
lemma D2_eq_half_P (p n : ℕ) (m : Fin p → ℝ) (hn : 0 < n) (hm : ∀ j, 0 ≤ m j) :
    let Q2 : Set (Fin p → (Fin n → ℝ)) := { u | ∀ j, ‖u j‖ ≤ 1 }
    let norm2 : (Fin p → (Fin n → ℝ)) → ℝ :=
      fun u => Real.sqrt (∑ j, m j * ‖u j‖ ^ (2 : ℕ))
    let d2 : (Fin p → (Fin n → ℝ)) → ℝ := fun u => (1 / 2 : ℝ) * (norm2 u) ^ (2 : ℕ)
    let P : ℝ := ∑ j, m j
    sSup (d2 '' Q2) = (1 / 2 : ℝ) * P := by
  classical
  intro Q2 norm2 d2 P
  have hP_nonneg : 0 ≤ P := by
    simpa [P] using Finset.sum_nonneg (fun j _ => hm j)
  have hQ2_ne : (d2 '' Q2).Nonempty := by
    refine ⟨d2 0, ?_⟩
    refine ⟨0, ?_, rfl⟩
    intro j
    simp
  have hd2_le : ∀ u, u ∈ Q2 → d2 u ≤ (1 / 2 : ℝ) * P := by
    intro u hu
    set S : ℝ := ∑ j, m j * ‖u j‖ ^ (2 : ℕ)
    have hS_nonneg : 0 ≤ S := by
      refine Finset.sum_nonneg ?_
      intro j hj
      exact mul_nonneg (hm j) (pow_nonneg (norm_nonneg _) _)
    have hS_le : S ≤ P := by
      have hterm_le :
          ∀ j : Fin p, m j * ‖u j‖ ^ (2 : ℕ) ≤ m j := by
        intro j
        have huj : ‖u j‖ ≤ 1 := hu j
        have hsq : ‖u j‖ ^ (2 : ℕ) ≤ (1 : ℝ) ^ (2 : ℕ) := by
          simpa [pow_two] using (mul_le_mul huj huj (norm_nonneg _) (by norm_num))
        have hsq' : ‖u j‖ ^ (2 : ℕ) ≤ 1 := by simpa using hsq
        simpa [mul_one] using mul_le_mul_of_nonneg_left hsq' (hm j)
      -- sum the pointwise bounds
      have : S ≤ ∑ j, m j := by
        refine Finset.sum_le_sum ?_
        intro j hj
        simpa [S] using hterm_le j
      simpa [P] using this
    have hd2 : d2 u = (1 / 2 : ℝ) * S := by
      simp [d2, norm2, S, Real.sq_sqrt hS_nonneg]
    calc
      d2 u = (1 / 2 : ℝ) * S := hd2
      _ ≤ (1 / 2 : ℝ) * P := mul_le_mul_of_nonneg_left hS_le (by norm_num)
  have hQ2_bdd : BddAbove (d2 '' Q2) := by
    refine ⟨(1 / 2 : ℝ) * P, ?_⟩
    rintro y ⟨u, hu, rfl⟩
    exact hd2_le u hu
  -- attain the bound by taking all blocks equal to the constant `1` function
  let v : Fin n → ℝ := fun _ => (1 : ℝ)
  have hv_norm : ‖v‖ = (1 : ℝ) := norm_const_one_fin (n := n) hn
  let u0 : Fin p → (Fin n → ℝ) := fun _ => v
  have hu0_mem : u0 ∈ Q2 := by
    intro j
    simp [u0, hv_norm]
  have hu0_val : d2 u0 = (1 / 2 : ℝ) * P := by
    have :
        (∑ j, m j * ‖u0 j‖ ^ (2 : ℕ)) = P := by
      simp [P, u0, hv_norm]
    simp [d2, norm2, this, Real.sq_sqrt hP_nonneg]
  have hle_sup : (1 / 2 : ℝ) * P ≤ sSup (d2 '' Q2) := by
    refine le_csSup hQ2_bdd ?_
    exact ⟨u0, hu0_mem, hu0_val⟩
  have hsup_le : sSup (d2 '' Q2) ≤ (1 / 2 : ℝ) * P := by
    refine csSup_le hQ2_ne ?_
    rintro y ⟨u, hu, rfl⟩
    exact hd2_le u hu
  exact le_antisymm hsup_le hle_sup

/-- Algebraic simplification used in the final step of Proposition 1.4.2.1. -/
lemma rate_sqrt_simplify (P rbar : ℝ) (hP : 0 ≤ P) (hrbar : 0 ≤ rbar) (N : ℕ) :
    (4 * Real.sqrt P) / ((N : ℝ) + 1) *
        Real.sqrt (((1 / 2 : ℝ) * rbar ^ (2 : ℕ)) * ((1 / 2 : ℝ) * P)) =
      (2 * P * rbar) / ((N : ℝ) + 1) := by
  have hden : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hden' : (N : ℝ) + 1 ≠ 0 := ne_of_gt hden
  have hsqrt :
      Real.sqrt (((1 / 2 : ℝ) * rbar ^ (2 : ℕ)) * ((1 / 2 : ℝ) * P)) =
        (rbar * Real.sqrt P) / 2 := by
    have hrbar2 : 0 ≤ rbar ^ (2 : ℕ) := by positivity
    calc
      Real.sqrt (((1 / 2 : ℝ) * rbar ^ (2 : ℕ)) * ((1 / 2 : ℝ) * P)) =
          Real.sqrt (P * (rbar ^ (2 : ℕ) / 4)) := by
            congr 1
            ring
      _ = Real.sqrt P * Real.sqrt (rbar ^ (2 : ℕ) / 4) := by
          simpa [mul_assoc] using (Real.sqrt_mul hP (rbar ^ (2 : ℕ) / 4))
      _ = Real.sqrt P * (rbar / 2) := by
          have hsqrt_quarter : Real.sqrt (1 / 4 : ℝ) = (1 / 2 : ℝ) := by norm_num
          have hsqrt_rbar : Real.sqrt (rbar ^ (2 : ℕ)) = rbar := by
            -- `rbar ^ 2 = rbar * rbar` and `sqrt (x*x) = x` for `x ≥ 0`
            simpa [pow_two] using (Real.sqrt_mul_self hrbar)
          have hsqrt_div4 : Real.sqrt (rbar ^ (2 : ℕ) / 4) = rbar / 2 := by
            have hmul :
                Real.sqrt (rbar ^ (2 : ℕ) / 4) =
                  Real.sqrt (rbar ^ (2 : ℕ)) * Real.sqrt (1 / 4 : ℝ) := by
              simp [div_eq_mul_inv]
            calc
              Real.sqrt (rbar ^ (2 : ℕ) / 4) =
                  Real.sqrt (rbar ^ (2 : ℕ)) *
                    Real.sqrt (1 / 4 : ℝ) := by
                      exact hmul
              _ = rbar * (1 / 2 : ℝ) := by
                  rw [hsqrt_rbar, hsqrt_quarter]
              _ = rbar / 2 := by ring
          simp [hsqrt_div4]
      _ = (rbar * Real.sqrt P) / 2 := by ring
  calc
    (4 * Real.sqrt P) / ((N : ℝ) + 1) *
        Real.sqrt (((1 / 2 : ℝ) * rbar ^ (2 : ℕ)) * ((1 / 2 : ℝ) * P)) =
        (4 * Real.sqrt P) / ((N : ℝ) + 1) * ((rbar * Real.sqrt P) / 2) := by
          rw [hsqrt]
    _ = (2 * P * rbar) / ((N : ℝ) + 1) := by
          field_simp [hden']
          have hmul : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt hP
          nlinarith [hmul]

/-- Convert an `f`-bound into the corresponding bound for the rescaled objective `ftilde`. -/
lemma ftilde_bound_from_f_bound {P fval fstar rbar : ℝ} {N : ℕ} (hP : 0 ≤ P) (hrbar : 0 ≤ rbar)
    (h : fval - fstar ≤ (2 * P * rbar) / ((N : ℝ) + 1)) :
    (1 / P) * fval - (1 / P) * fstar ≤ (2 * rbar) / ((N : ℝ) + 1) := by
  by_cases hP0 : P = 0
  · subst hP0
    have : 0 ≤ (2 * rbar) / ((N : ℝ) + 1) := by positivity
    simpa using this
  · have hPpos : 0 < P := lt_of_le_of_ne hP (Ne.symm hP0)
    have hPinv_nonneg : 0 ≤ (1 / P) := by positivity
    have hR : (1 / P) * ((2 * P * rbar) / ((N : ℝ) + 1)) = (2 * rbar) / ((N : ℝ) + 1) := by
      have hnum : (1 / P) * (2 * P * rbar) = (2 * rbar) := by
        field_simp [hP0]
      calc
        (1 / P) * ((2 * P * rbar) / ((N : ℝ) + 1)) =
            ((1 / P) * (2 * P * rbar)) / ((N : ℝ) + 1) := by
              simp [mul_div_assoc]
        _ = (2 * rbar) / ((N : ℝ) + 1) := by
            rw [hnum]
    have hmul : (1 / P) * (fval - fstar) ≤ (1 / P) * ((2 * P * rbar) / ((N : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left h hPinv_nonneg
    have hL : (1 / P) * fval - (1 / P) * fstar = (1 / P) * (fval - fstar) := by ring
    calc
      (1 / P) * fval - (1 / P) * fstar = (1 / P) * (fval - fstar) := hL
      _ ≤ (1 / P) * ((2 * P * rbar) / ((N : ℝ) + 1)) := hmul
      _ = (2 * rbar) / ((N : ℝ) + 1) := hR

end continuousLocation

/-- Proposition 1.4.2.1.
In the setting of Definition 1.4.2.1, take `‖·‖_1` to be the Euclidean norm on `ℝ^n` and
`d1(x) = (1/2) ‖x‖_1^2` on `Q1 = {x : ‖x‖_1 ≤ rbar}`. Then `σ1 = 1` and
`D1 = max_{x ∈ Q1} d1(x) = (1/2) rbar^2`. Let `E2 = (E1*)^p` and
`Q2 = {u = (u_1, ..., u_p) : ‖u_j‖_{1,*} ≤ 1}`. Choose
`‖u‖_2 = (∑_{j=1}^p m_j ‖u_j‖_{1,*}^2)^{1/2}` and `d2(u) = (1/2) ‖u‖_2^2`. Then `σ2 = 1` and,
with `P = ∑ m_j`, `D2 = max_{u ∈ Q2} d2(u) = (1/2) P` and `‖A‖_{1,2} = P^{1/2}`. Since
`fhat ≡ 0` in (4.1), the estimate (4.3) yields the rate
`f(xhat) - f* ≤ 2 P rbar / (N+1)` (4.16), and for `tilde f = (1/P) f` we have
`tilde f(xhat) - tilde f* ≤ 2 rbar / (N+1)`. -/
theorem continuousLocation_euclidean_prox_rate (p n : ℕ) (m : Fin p → ℝ)
    (c : Fin p → (Fin n → ℝ)) (rbar : ℝ)
    (A : (Fin n → ℝ) →L[ℝ] ((Fin p → (Fin n → ℝ)) →L[ℝ] ℝ)) (N : ℕ)
    (xhat : Fin n → ℝ) (hn : 0 < n) (hrbar : 0 ≤ rbar) (hm : ∀ j, 0 ≤ m j) :
    let Q1 : Set (Fin n → ℝ) := { x | ‖x‖ ≤ rbar }
    let d1 : (Fin n → ℝ) → ℝ := fun x => (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ)
    let Q2 : Set (Fin p → (Fin n → ℝ)) := { u | ∀ j, ‖u j‖ ≤ 1 }
    let norm2 : (Fin p → (Fin n → ℝ)) → ℝ :=
      fun u => Real.sqrt (∑ j, m j * ‖u j‖ ^ (2 : ℕ))
    let d2 : (Fin p → (Fin n → ℝ)) → ℝ := fun u => (1 / 2 : ℝ) * (norm2 u) ^ (2 : ℕ)
    let D1 : ℝ := sSup (d1 '' Q1)
    let D2 : ℝ := sSup (d2 '' Q2)
    let P : ℝ := ∑ j, m j
    let A' : (Fin n → ℝ) →ₗ[ℝ] Module.Dual ℝ (Fin p → (Fin n → ℝ)) :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro r x
          ext u
          simp }
    let f : (Fin n → ℝ) → ℝ := fun x => ∑ j, m j * ‖x - c j‖
    let fstar : ℝ := continuousLocationOptimalValue p n m c rbar
    let ftilde : (Fin n → ℝ) → ℝ := fun x => (1 / P) * f x
    let ftilde_star : ℝ := (1 / P) * fstar
    OperatorNormDef A' = Real.sqrt P →
      f xhat - fstar ≤ (4 * OperatorNormDef A') / ((N : ℝ) + 1) * Real.sqrt (D1 * D2) →
        D1 = (1 / 2 : ℝ) * rbar ^ (2 : ℕ) ∧
          D2 = (1 / 2 : ℝ) * P ∧
          f xhat - fstar ≤ (2 * P * rbar) / ((N : ℝ) + 1) ∧
          ftilde xhat - ftilde_star ≤ (2 * rbar) / ((N : ℝ) + 1) := by
  classical
  dsimp
  intro hOp hgap
  have hD1 : sSup ((fun x : Fin n → ℝ => (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ)) '' { x | ‖x‖ ≤ rbar }) =
      (1 / 2 : ℝ) * rbar ^ (2 : ℕ) :=
    continuousLocation.D1_eq_half_rbar_sq (n := n) (rbar := rbar) hn hrbar
  have hD2 :
      sSup
          ((fun u : Fin p → Fin n → ℝ =>
                (1 / 2 : ℝ) *
                  (Real.sqrt (∑ j, m j * ‖u j‖ ^ (2 : ℕ))) ^ (2 : ℕ)) '' { u | ∀ j, ‖u j‖ ≤ 1 }) =
        (1 / 2 : ℝ) * (∑ j, m j) :=
    continuousLocation.D2_eq_half_P (p := p) (n := n) (m := m) hn hm
  have hD1_simp :
      sSup ((fun x : Fin n → ℝ => (2 : ℝ)⁻¹ * ‖x‖ ^ 2) '' { x | ‖x‖ ≤ rbar }) =
        (2 : ℝ)⁻¹ * rbar ^ 2 := by
    simpa [one_div] using hD1
  have hD2_simp :
      sSup
          ((fun u : Fin p → Fin n → ℝ =>
                (2 : ℝ)⁻¹ *
                  (Real.sqrt (∑ j, m j * ‖u j‖ ^ 2)) ^ 2) '' { u | ∀ j, ‖u j‖ ≤ 1 }) =
        (2 : ℝ)⁻¹ * (∑ j, m j) := by
    simpa [one_div] using hD2
  have hP_nonneg : 0 ≤ (∑ j, m j) := by
    simpa using Finset.sum_nonneg (fun j _ => hm j)
  have hgap' :
      (∑ j, m j * ‖xhat - c j‖) - continuousLocationOptimalValue p n m c rbar ≤
        (4 * Real.sqrt (∑ j, m j)) / ((N : ℝ) + 1) *
          Real.sqrt (((1 / 2 : ℝ) * rbar ^ (2 : ℕ)) * ((1 / 2 : ℝ) * (∑ j, m j))) := by
    simpa [hOp, hD1_simp, hD2_simp] using hgap
  have hfinal :
      (∑ j, m j * ‖xhat - c j‖) - continuousLocationOptimalValue p n m c rbar ≤
        (2 * (∑ j, m j) * rbar) / ((N : ℝ) + 1) := by
    -- simplify the `sqrt` factor
    simpa using
      (le_trans hgap'
        (le_of_eq (continuousLocation.rate_sqrt_simplify (P := ∑ j, m j) (rbar := rbar)
          hP_nonneg hrbar N)))
  refine ⟨hD1, ?_, hfinal, ?_⟩
  · simpa using hD2
  · -- divide by `P` to get the scaled bound
    have :=
      continuousLocation.ftilde_bound_from_f_bound (P := ∑ j, m j)
        (fval := ∑ j, m j * ‖xhat - c j‖)
        (fstar := continuousLocationOptimalValue p n m c rbar)
        (rbar := rbar) (N := N) hP_nonneg hrbar hfinal
    simpa using this

/-- Under nonnegative weights, the prox-term `d2(u) = (1/2) * (sqrt (∑ m_j ‖u_j‖^2))^2` simplifies
to the weighted sum `d2(u) = (1/2) * ∑ m_j ‖u_j‖^2`. -/
lemma d2_eq_half_sum_weighted_norm_sq (p n : ℕ) (m : Fin p → ℝ) (hm : ∀ j, 0 ≤ m j)
    (u : Fin p → (Fin n → ℝ)) :
    (1 / 2 : ℝ) *
        (Real.sqrt (∑ j, m j * ‖u j‖ ^ (2 : ℕ))) ^ (2 : ℕ) =
      (1 / 2 : ℝ) * ∑ j, m j * ‖u j‖ ^ (2 : ℕ) := by
  set S : ℝ := ∑ j, m j * ‖u j‖ ^ (2 : ℕ)
  have hS_nonneg : 0 ≤ S := by
    refine Finset.sum_nonneg ?_
    intro j hj
    exact mul_nonneg (hm j) (pow_nonneg (norm_nonneg _) _)
  have hsqrt : (Real.sqrt S) ^ (2 : ℕ) = S := by
    simpa using (Real.sq_sqrt hS_nonneg)
  simp [S, hsqrt]

/-- The coordinatewise sign vector, with entries `±1`, used to saturate the `‖·‖∞` unit ball. -/
noncomputable def signVec {n : ℕ} (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if 0 ≤ y i then 1 else -1

/-- For the `Pi` (sup) norm on `Fin n → ℝ`, each coordinate is bounded by the total norm. -/
lemma abs_apply_le_norm {n : ℕ} (u : Fin n → ℝ) (i : Fin n) : |u i| ≤ ‖u‖ := by
  classical
  have hle :
      ‖u i‖₊ ≤ Finset.univ.sup (fun j : Fin n => ‖u j‖₊) := by
    refine Finset.le_sup (s := (Finset.univ : Finset (Fin n))) (f := fun j => ‖u j‖₊) ?_
    simp
  have hle' :
      (‖u i‖₊ : ℝ) ≤ (↑(Finset.univ.sup (fun j : Fin n => ‖u j‖₊)) : ℝ) := by
    exact_mod_cast hle
  simpa [Pi.norm_def, Real.norm_eq_abs] using hle'

/-- The `signVec` has `‖signVec y‖ ≤ 1` in the `Pi` (sup) norm. -/
lemma norm_signVec_le_one {n : ℕ} (y : Fin n → ℝ) : ‖signVec y‖ ≤ (1 : ℝ) := by
  classical
  rw [Pi.norm_def]
  have hsup :
      (Finset.univ.sup fun i : Fin n => ‖signVec y i‖₊) ≤ (1 : ℝ≥0) := by
    refine Finset.sup_le ?_
    intro i hi
    by_cases h : 0 ≤ y i <;> simp [signVec, h]
  exact_mod_cast hsup

/-- `signVec` attains the dual pairing with the `‖·‖∞` unit ball: `∑ sign(y_i) * y_i = ∑ |y_i|`. -/
lemma sum_signVec_mul {n : ℕ} (y : Fin n → ℝ) :
    (∑ i, signVec y i * y i) = ∑ i, |y i| := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases h : 0 ≤ y i
  · simp [signVec, h, abs_of_nonneg h]
  · have hneg : y i < 0 := lt_of_not_ge h
    simp [signVec, h, abs_of_neg hneg]

/-- For the `Pi` (sup) norm on `Fin n → ℝ`, the dot product is bounded by `‖u‖ * ∑ |y_i|`. -/
lemma dot_le_norm_mul_sum_abs {n : ℕ} (u y : Fin n → ℝ) :
    (∑ i, u i * y i) ≤ ‖u‖ * (∑ i, |y i|) := by
  classical
  -- bound each term and then sum
  have hterm : ∀ i : Fin n, u i * y i ≤ ‖u‖ * |y i| := by
    intro i
    have hy : 0 ≤ |y i| := abs_nonneg _
    have hu : |u i| ≤ ‖u‖ := abs_apply_le_norm u i
    calc
      u i * y i ≤ |u i * y i| := le_abs_self _
      _ = |u i| * |y i| := by simp [abs_mul]
      _ ≤ ‖u‖ * |y i| := by
        -- first replace `|u i|` by `‖u‖`
        have : |u i| * |y i| ≤ ‖u‖ * |y i| := mul_le_mul_of_nonneg_right hu hy
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
  calc
    (∑ i, u i * y i) ≤ ∑ i, ‖u‖ * |y i| := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact hterm i
    _ = ‖u‖ * (∑ i, |y i|) := by simp [Finset.mul_sum]

/-- Piecewise evaluation of `ψμ(τ) = max_{γ∈[0,1]} (γ τ - (μ/2) γ^2)` for `μ > 0` and `τ ≥ 0`. -/
lemma psi_mu_piecewise (μ τ : ℝ) (hμ : 0 < μ) (hτ : 0 ≤ τ) :
    sSup
        ((fun γ : ℝ => γ * τ - (1 / 2 : ℝ) * μ * γ ^ (2 : ℕ)) '' Set.Icc (0 : ℝ) 1) =
      (if τ ≤ μ then τ ^ (2 : ℕ) / (2 * μ) else τ - μ / 2) := by
  classical
  set g : ℝ → ℝ := fun γ => γ * τ - (1 / 2 : ℝ) * μ * γ ^ (2 : ℕ)
  have hIcc_ne : (Set.Icc (0 : ℝ) 1).Nonempty := ⟨0, by simp⟩
  have hImg_ne : (g '' Set.Icc (0 : ℝ) 1).Nonempty := by
    rcases hIcc_ne with ⟨γ, hγ⟩
    exact ⟨g γ, ⟨γ, hγ, rfl⟩⟩
  have hIcc_comp : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have hg_cont : Continuous g := by
    continuity
  have hIcc_bdd : BddAbove (g '' Set.Icc (0 : ℝ) 1) := (hIcc_comp.image hg_cont).bddAbove
  by_cases hτμ : τ ≤ μ
  · have hμne : μ ≠ 0 := ne_of_gt hμ
    have hγ_mem : (τ / μ) ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg hτ (le_of_lt hμ), ?_⟩
      -- `τ / μ ≤ 1` since `τ ≤ μ` and `μ > 0`
      have : τ / μ ≤ 1 := (div_le_one hμ).2 hτμ
      simpa using this
    have h_upper : ∀ γ ∈ Set.Icc (0 : ℝ) 1, g γ ≤ τ ^ (2 : ℕ) / (2 * μ) := by
      intro γ hγ
      have hsq : 0 ≤ (γ - τ / μ) ^ (2 : ℕ) := by positivity
      have hrewrite :
          g γ = τ ^ (2 : ℕ) / (2 * μ) - (μ / 2) * (γ - τ / μ) ^ (2 : ℕ) := by
        field_simp [g, hμne]
        ring
      have hμ2 : 0 ≤ μ / 2 := by linarith [le_of_lt hμ]
      have : 0 ≤ (μ / 2) * (γ - τ / μ) ^ (2 : ℕ) := mul_nonneg hμ2 hsq
      have : τ ^ (2 : ℕ) / (2 * μ) - (μ / 2) * (γ - τ / μ) ^ (2 : ℕ) ≤ τ ^ (2 : ℕ) / (2 * μ) := by
        linarith
      simpa [hrewrite] using this
    have hsup_le : sSup (g '' Set.Icc (0 : ℝ) 1) ≤ τ ^ (2 : ℕ) / (2 * μ) := by
      refine csSup_le hImg_ne ?_
      rintro _ ⟨γ, hγ, rfl⟩
      exact h_upper γ hγ
    have hval : g (τ / μ) = τ ^ (2 : ℕ) / (2 * μ) := by
      simp [g]
      field_simp [hμne]
      ring
    have hle_sup : τ ^ (2 : ℕ) / (2 * μ) ≤ sSup (g '' Set.Icc (0 : ℝ) 1) := by
      refine le_csSup hIcc_bdd ?_
      exact ⟨τ / μ, hγ_mem, hval⟩
    have hsup : sSup (g '' Set.Icc (0 : ℝ) 1) = τ ^ (2 : ℕ) / (2 * μ) :=
      le_antisymm hsup_le hle_sup
    simp [hτμ, hsup]
  · have hμleτ : μ ≤ τ := le_of_not_ge hτμ
    have h_upper : ∀ γ ∈ Set.Icc (0 : ℝ) 1, g γ ≤ τ - μ / 2 := by
      intro γ hγ
      have hγle : γ ≤ 1 := hγ.2
      have h1γ : 0 ≤ 1 - γ := sub_nonneg.mpr hγle
      have haux : 0 ≤ τ - (μ / 2) * (1 + γ) := by
        have hbound : (μ / 2) * (1 + γ) ≤ (μ / 2) * 2 := by
          have : 1 + γ ≤ (2 : ℝ) := by linarith [hγle]
          exact mul_le_mul_of_nonneg_left this (by linarith [le_of_lt hμ])
        have : (μ / 2) * 2 = μ := by ring
        have : (μ / 2) * (1 + γ) ≤ μ := by simpa [this] using hbound
        linarith
      have hdiff :
          (τ - μ / 2) - g γ = (1 - γ) * (τ - (μ / 2) * (1 + γ)) := by
        simp [g, pow_two]
        ring
      have hdiff_nonneg : 0 ≤ (τ - μ / 2) - g γ := by
        have : 0 ≤ (1 - γ) * (τ - (μ / 2) * (1 + γ)) := mul_nonneg h1γ haux
        simpa [hdiff] using this
      linarith
    have hsup_le : sSup (g '' Set.Icc (0 : ℝ) 1) ≤ τ - μ / 2 := by
      refine csSup_le hImg_ne ?_
      rintro _ ⟨γ, hγ, rfl⟩
      exact h_upper γ hγ
    have hle_sup : τ - μ / 2 ≤ sSup (g '' Set.Icc (0 : ℝ) 1) := by
      refine le_csSup hIcc_bdd ?_
      refine ⟨1, by simp, ?_⟩
      -- evaluate `g` at the endpoint `γ = 1`
      simp [g, pow_two]
      ring
    have hsup : sSup (g '' Set.Icc (0 : ℝ) 1) = τ - μ / 2 :=
      le_antisymm hsup_le hle_sup
    simp [hτμ, hsup]
set_option maxHeartbeats 800000 in -- proof is long; allow extra heartbeats
/-- Proposition 1.4.2.2.
In the setting of Proposition 1.4.2.1, the smoothed function `f_μ` admits the explicit
representation `f_μ(x) = ∑_{j=1}^p m_j ψ_μ(‖x - c_j‖_1)`, where `ψ_μ : [0,∞) → ℝ` is given by
`ψ_μ(τ) = max_{γ ∈ [0,1]} {γ τ - (1/2) μ γ^2}` and equals the piecewise formula in (4.17):
`ψ_μ(τ) = τ^2/(2 μ)` for `0 ≤ τ ≤ μ`, and `ψ_μ(τ) = τ - μ/2` for `μ ≤ τ`. -/
theorem continuousLocation_smoothedFunction_explicit (p n : ℕ) (m : Fin p → ℝ)
    (c : Fin p → (Fin n → ℝ)) (μ : ℝ)
    (A : (Fin n → ℝ) →L[ℝ] ((Fin p → (Fin n → ℝ)) →L[ℝ] ℝ))
    (phihat : (Fin p → (Fin n → ℝ)) → ℝ) (hμ : 0 < μ) (hm : ∀ j, 0 ≤ m j)
    (hA :
      ∀ x u,
        A x u = ∑ j, m j * (∑ i, u j i * x i))
    (hphihat :
      ∀ u,
        phihat u = ∑ j, m j * (∑ i, u j i * c j i)) :
    let Q2 : Set (Fin p → (Fin n → ℝ)) := { u | ∀ j, ‖u j‖ ≤ 1 }
    let norm2 : (Fin p → (Fin n → ℝ)) → ℝ :=
      fun u => Real.sqrt (∑ j, m j * ‖u j‖ ^ (2 : ℕ))
    let d2 : (Fin p → (Fin n → ℝ)) → ℝ := fun u => (1 / 2 : ℝ) * (norm2 u) ^ (2 : ℕ)
    let fμ : (Fin n → ℝ) → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    let ψμ : ℝ → ℝ :=
      fun τ =>
        sSup
          ((fun γ => γ * τ - (1 / 2 : ℝ) * μ * γ ^ (2 : ℕ)) '' (Set.Icc (0 : ℝ) 1))
    (∀ x, fμ x = ∑ j, m j * ψμ (∑ i, |x i - c j i|)) ∧
      (∀ τ, 0 ≤ τ →
        ψμ τ =
          (if τ ≤ μ then τ ^ (2 : ℕ) / (2 * μ) else τ - μ / 2)) := by
  classical
  intro Q2 norm2 d2 fμ ψμ
  have hIcc_comp : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have hIcc_bdd (τ : ℝ) :
      BddAbove
        ((fun γ : ℝ => γ * τ - (1 / 2 : ℝ) * μ * γ ^ (2 : ℕ)) '' Set.Icc (0 : ℝ) 1) := by
    have hcont :
        Continuous fun γ : ℝ => γ * τ - (1 / 2 : ℝ) * μ * γ ^ (2 : ℕ) := by
      continuity
    simpa using (hIcc_comp.image hcont).bddAbove
  have hd2_simp :
      ∀ u : Fin p → (Fin n → ℝ), d2 u = (1 / 2 : ℝ) * ∑ j, m j * ‖u j‖ ^ (2 : ℕ) := by
    intro u
    simpa [d2, norm2] using
      (d2_eq_half_sum_weighted_norm_sq (p := p) (n := n) (m := m) hm u)
  have hpsi_piece : ∀ τ : ℝ, 0 ≤ τ →
      ψμ τ = (if τ ≤ μ then τ ^ (2 : ℕ) / (2 * μ) else τ - μ / 2) := by
    intro τ hτ
    simpa [ψμ] using (psi_mu_piecewise (μ := μ) (τ := τ) hμ hτ)
  have hmain : ∀ x : Fin n → ℝ, fμ x = ∑ j, m j * ψμ (∑ i, |x i - c j i|) := by
    intro x
    set F : (Fin p → (Fin n → ℝ)) → ℝ :=
      fun u => A x u - phihat u - μ * d2 u
    have hne : (F '' Q2).Nonempty := by
      refine ⟨F 0, ?_⟩
      refine ⟨0, ?_, rfl⟩
      intro j
      simp
    have hF_simp :
        ∀ u : Fin p → (Fin n → ℝ),
          F u =
            ∑ j, m j *
              ((∑ i, u j i * (x i - c j i)) -
                (1 / 2 : ℝ) * μ * ‖u j‖ ^ (2 : ℕ)) := by
      intro u
      have hA' : A x u = ∑ j, m j * (∑ i, u j i * x i) := hA x u
      have hphihat' : phihat u = ∑ j, m j * (∑ i, u j i * c j i) := hphihat u
      have hd2' : d2 u = (1 / 2 : ℝ) * ∑ j, m j * ‖u j‖ ^ (2 : ℕ) := hd2_simp u
      -- rewrite `A x u - phihat u` as a sum over blocks
      have hinner :
          ∀ j : Fin p,
            (∑ i, u j i * x i) - (∑ i, u j i * c j i) = ∑ i, u j i * (x i - c j i) := by
        intro j
        calc
          (∑ i, u j i * x i) - (∑ i, u j i * c j i) =
              ∑ i, (u j i * x i - u j i * c j i) := by
                simp [Finset.sum_sub_distrib]
          _ = ∑ i, u j i * (x i - c j i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [mul_sub]
      have hdiff :
          (∑ j, m j * (∑ i, u j i * x i)) - (∑ j, m j * (∑ i, u j i * c j i)) =
            ∑ j, m j * (∑ i, u j i * (x i - c j i)) := by
        calc
          (∑ j, m j * (∑ i, u j i * x i)) - (∑ j, m j * (∑ i, u j i * c j i)) =
              ∑ j, (m j * (∑ i, u j i * x i) - m j * (∑ i, u j i * c j i)) := by
                simp [Finset.sum_sub_distrib]
          _ = ∑ j, m j * ((∑ i, u j i * x i) - (∑ i, u j i * c j i)) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                simp [mul_sub]
          _ = ∑ j, m j * (∑ i, u j i * (x i - c j i)) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                simp [hinner j]
      -- now combine with the `d2` term
      dsimp [F]
      rw [hA', hphihat', hd2']
      -- rewrite the difference of the first two sums using `hdiff`
      rw [hdiff]
      -- commute the scalar `μ` with `(1/2)`
      have hmuls :
          μ * ((1 / 2 : ℝ) * ∑ j, m j * ‖u j‖ ^ (2 : ℕ)) =
            (1 / 2 : ℝ) * μ * (∑ j, m j * ‖u j‖ ^ (2 : ℕ)) := by
        ring
      -- rewrite the remaining expression into a blockwise sum
      have hsplit :
          (∑ j, m j * (∑ i, u j i * (x i - c j i))) -
              (1 / 2 : ℝ) * μ * (∑ j, m j * ‖u j‖ ^ (2 : ℕ)) =
            ∑ j, m j *
              ((∑ i, u j i * (x i - c j i)) - (1 / 2 : ℝ) * μ * ‖u j‖ ^ (2 : ℕ)) := by
        -- rewrite the penalty term as a sum, then combine termwise
        calc
          (∑ j, m j * (∑ i, u j i * (x i - c j i))) -
              (1 / 2 : ℝ) * μ * (∑ j, m j * ‖u j‖ ^ (2 : ℕ)) =
              (∑ j, m j * (∑ i, u j i * (x i - c j i))) -
                ∑ j, ((1 / 2 : ℝ) * μ) * (m j * ‖u j‖ ^ (2 : ℕ)) := by
                  -- rewrite the scalar multiple of a finite sum
                  rw [Finset.mul_sum]
          _ = ∑ j,
                (m j * (∑ i, u j i * (x i - c j i)) -
                  ((1 / 2 : ℝ) * μ) * (m j * ‖u j‖ ^ (2 : ℕ))) := by
                  exact
                    (Finset.sum_sub_distrib
                      (f := fun j : Fin p => m j * (∑ i, u j i * (x i - c j i)))
                      (g := fun j : Fin p => ((1 / 2 : ℝ) * μ) * (m j * ‖u j‖ ^ (2 : ℕ)))).symm
          _ = ∑ j, m j *
                ((∑ i, u j i * (x i - c j i)) - (1 / 2 : ℝ) * μ * ‖u j‖ ^ (2 : ℕ)) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  ring
      rw [hmuls]
      exact hsplit
    have hF_le :
        ∀ u ∈ Q2,
          F u ≤ ∑ j, m j * ψμ (∑ i, |x i - c j i|) := by
      intro u hu
      have hblock :
          ∀ j : Fin p,
            ((∑ i, u j i * (x i - c j i)) -
                  (1 / 2 : ℝ) * μ * ‖u j‖ ^ (2 : ℕ)) ≤
              ψμ (∑ i, |x i - c j i|) := by
        intro j
        have hdot :
            (∑ i, u j i * (x i - c j i)) ≤ ‖u j‖ * (∑ i, |x i - c j i|) :=
          dot_le_norm_mul_sum_abs (u := u j) (y := fun i => x i - c j i)
        have hjmem : ‖u j‖ ∈ Set.Icc (0 : ℝ) 1 := ⟨norm_nonneg _, hu j⟩
        have hval_le :
            ((∑ i, u j i * (x i - c j i)) -
                  (1 / 2 : ℝ) * μ * ‖u j‖ ^ (2 : ℕ)) ≤
              (‖u j‖) * (∑ i, |x i - c j i|) - (1 / 2 : ℝ) * μ * (‖u j‖) ^ (2 : ℕ) := by
          linarith [hdot]
        have hmem :
            (‖u j‖ * (∑ i, |x i - c j i|) - (1 / 2 : ℝ) * μ * (‖u j‖) ^ (2 : ℕ)) ∈
              ((fun γ : ℝ =>
                    γ * (∑ i, |x i - c j i|) - (1 / 2 : ℝ) * μ * γ ^ (2 : ℕ)) ''
                Set.Icc (0 : ℝ) 1) := by
          exact ⟨‖u j‖, hjmem, rfl⟩
        have hle_sup :
            (‖u j‖ * (∑ i, |x i - c j i|) - (1 / 2 : ℝ) * μ * (‖u j‖) ^ (2 : ℕ)) ≤
              ψμ (∑ i, |x i - c j i|) := by
          exact le_csSup (hIcc_bdd (∑ i, |x i - c j i|)) hmem
        exact le_trans hval_le hle_sup
      have hsum_le :
          ∑ j, m j *
              ((∑ i, u j i * (x i - c j i)) -
                (1 / 2 : ℝ) * μ * ‖u j‖ ^ (2 : ℕ)) ≤
            ∑ j, m j * ψμ (∑ i, |x i - c j i|) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        exact mul_le_mul_of_nonneg_left (hblock j) (hm j)
      -- conclude the bound on `F u` by rewriting with `hF_simp`
      calc
        F u =
            ∑ j, m j *
              ((∑ i, u j i * (x i - c j i)) - (1 / 2 : ℝ) * μ * ‖u j‖ ^ (2 : ℕ)) := hF_simp u
        _ ≤ ∑ j, m j * ψμ (∑ i, |x i - c j i|) := hsum_le
    have hupper :
        sSup (F '' Q2) ≤ ∑ j, m j * ψμ (∑ i, |x i - c j i|) := by
      refine csSup_le hne ?_
      rintro _ ⟨u, hu, rfl⟩
      exact hF_le u hu
    have hlower :
        (∑ j, m j * ψμ (∑ i, |x i - c j i|)) ≤ sSup (F '' Q2) := by
      -- choose `u*` built from `γ* = min(1, τ/μ)`
      set γstar : Fin p → ℝ :=
        fun j => if (∑ i, |x i - c j i|) ≤ μ then (∑ i, |x i - c j i|) / μ else 1
      set uStar : Fin p → (Fin n → ℝ) :=
        fun j => (γstar j) • signVec (fun i => x i - c j i)
      have huStar : uStar ∈ Q2 := by
        intro j
        by_cases hτ : (∑ i, |x i - c j i|) ≤ μ
        · have hτ_nonneg : 0 ≤ ∑ i, |x i - c j i| := by
            refine Finset.sum_nonneg ?_
            intro i hi
            exact abs_nonneg _
          have hγ0 : 0 ≤ γstar j := by
            -- `γstar j = τ/μ` in this branch
            simpa only [γstar, hτ] using div_nonneg hτ_nonneg (le_of_lt hμ)
          have hγ1 : γstar j ≤ 1 := by
            -- `τ/μ ≤ 1` when `τ ≤ μ` and `μ > 0`
            have hdiv : (∑ i, |x i - c j i|) / μ ≤ 1 := (div_le_one hμ).2 hτ
            simpa [γstar, hτ] using hdiv
          have hv : ‖signVec (fun i => x i - c j i)‖ ≤ (1 : ℝ) :=
            norm_signVec_le_one (y := fun i => x i - c j i)
          have hnorm :
              ‖uStar j‖ ≤ γstar j := by
            have : ‖uStar j‖ = |γstar j| * ‖signVec (fun i => x i - c j i)‖ := by
              simp [uStar, norm_smul]
            have habs : |γstar j| = γstar j := abs_of_nonneg hγ0
            calc
              ‖uStar j‖ = |γstar j| * ‖signVec (fun i => x i - c j i)‖ := this
              _ ≤ |γstar j| * 1 := by gcongr
              _ = γstar j := by simp [habs]
          exact le_trans hnorm hγ1
        · -- in the `μ < τ` regime, `γstar = 1`
          have hγ : γstar j = 1 := by simp [γstar, hτ]
          simpa [hγ, uStar] using norm_signVec_le_one (y := fun i => x i - c j i)
      have hF_ge : (∑ j, m j * ψμ (∑ i, |x i - c j i|)) ≤ F uStar := by
        have hF_simp_uStar :
            F uStar =
              ∑ j, m j *
                ((∑ i, uStar j i * (x i - c j i)) -
                  (1 / 2 : ℝ) * μ * ‖uStar j‖ ^ (2 : ℕ)) := hF_simp uStar
        have hterm :
            ∀ j : Fin p,
              ψμ (∑ i, |x i - c j i|) ≤
                (∑ i, uStar j i * (x i - c j i)) -
                  (1 / 2 : ℝ) * μ * ‖uStar j‖ ^ (2 : ℕ) := by
          intro j
          set τj : ℝ := ∑ i, |x i - c j i|
          have hτ_nonneg : 0 ≤ τj := by
            refine Finset.sum_nonneg ?_
            intro i hi
            exact abs_nonneg _
          have hτ_nonneg_sum : 0 ≤ ∑ i, |x i - c j i| := by
            simpa [τj] using hτ_nonneg
          have hdot :
              (∑ i, uStar j i * (x i - c j i)) = (γstar j) * τj := by
            calc
              ∑ i, uStar j i * (x i - c j i) =
                  ∑ i, (γstar j * signVec (fun i => x i - c j i) i) * (x i - c j i) := by
                    simp [uStar]
              _ =
                  ∑ i, γstar j * (signVec (fun i => x i - c j i) i * (x i - c j i)) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    ring
              _ = γstar j * ∑ i, signVec (fun i => x i - c j i) i * (x i - c j i) := by
                    symm
                    exact
                      Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
                        (a := γstar j)
                        (f := fun i => signVec (fun i => x i - c j i) i * (x i - c j i))
              _ = γstar j * ∑ i, |x i - c j i| := by
                    simp [sum_signVec_mul]
              _ = (γstar j) * τj := by rfl
          have hnorm_le :
              ‖uStar j‖ ≤ γstar j := by
            by_cases hτ : τj ≤ μ
            · have hτ_sum : ∑ i, |x i - c j i| ≤ μ := by
                simpa [τj] using hτ
              have hγ : γstar j = (∑ i, |x i - c j i|) / μ := by
                simp [γstar, hτ_sum]
              have hγ0 : 0 ≤ γstar j := by
                simpa [hγ] using (div_nonneg hτ_nonneg_sum (le_of_lt hμ))
              have hv : ‖signVec (fun i => x i - c j i)‖ ≤ (1 : ℝ) :=
                norm_signVec_le_one (y := fun i => x i - c j i)
              have : ‖uStar j‖ = |γstar j| * ‖signVec (fun i => x i - c j i)‖ := by
                simp [uStar, norm_smul]
              have habs : |γstar j| = γstar j := abs_of_nonneg hγ0
              calc
                ‖uStar j‖ = |γstar j| * ‖signVec (fun i => x i - c j i)‖ := this
                _ ≤ |γstar j| * 1 := by gcongr
                _ = γstar j := by simp [habs]
            · have hτ_sum : ¬ ∑ i, |x i - c j i| ≤ μ := by
                simpa [τj] using hτ
              have hγ : γstar j = 1 := by simp [γstar, hτ_sum]
              -- `‖uStar‖ ≤ 1 = γstar`
              simpa [uStar, hγ] using norm_signVec_le_one (y := fun i => x i - c j i)
          have hpow : ‖uStar j‖ ^ (2 : ℕ) ≤ (γstar j) ^ (2 : ℕ) := by
            have h0 : 0 ≤ ‖uStar j‖ := norm_nonneg _
            have h1 : 0 ≤ γstar j := by
              by_cases hτ : τj ≤ μ
              · have hτ_sum : ∑ i, |x i - c j i| ≤ μ := by
                  simpa [τj] using hτ
                have hγ : γstar j = (∑ i, |x i - c j i|) / μ := by
                  simp [γstar, hτ_sum]
                simpa [hγ] using (div_nonneg hτ_nonneg_sum (le_of_lt hμ))
              · have hτ_sum : ¬ ∑ i, |x i - c j i| ≤ μ := by
                  simpa [τj] using hτ
                simp [γstar, hτ_sum]
            simpa [pow_two] using (mul_le_mul hnorm_le hnorm_le h0 h1)
          have hpen :
              - (1 / 2 : ℝ) * μ * (γstar j) ^ (2 : ℕ) ≤
                - (1 / 2 : ℝ) * μ * ‖uStar j‖ ^ (2 : ℕ) := by
            have hμ2 : 0 ≤ (1 / 2 : ℝ) * μ := by nlinarith [le_of_lt hμ]
            have : (1 / 2 : ℝ) * μ * ‖uStar j‖ ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * μ * (γstar j) ^ (2 : ℕ) :=
              mul_le_mul_of_nonneg_left hpow hμ2
            linarith
          -- connect `ψμ τj` to `g (γstar j)`
          have hpsi :
              ψμ τj = (γstar j) * τj - (1 / 2 : ℝ) * μ * (γstar j) ^ (2 : ℕ) := by
            by_cases hτ : τj ≤ μ
            · have hpsi' : ψμ τj = τj ^ (2 : ℕ) / (2 * μ) := by
                simpa [hτ] using (hpsi_piece τj hτ_nonneg)
              have hμne : μ ≠ 0 := ne_of_gt hμ
              have hcalc :
                  (τj / μ) * τj - (1 / 2 : ℝ) * μ * (τj / μ) ^ (2 : ℕ) =
                    τj ^ (2 : ℕ) / (2 * μ) := by
                field_simp [hμne]
                ring
              calc
                ψμ τj = τj ^ (2 : ℕ) / (2 * μ) := hpsi'
                _ =
                    (τj / μ) * τj - (1 / 2 : ℝ) * μ * (τj / μ) ^ (2 : ℕ) := by
                      symm
                      exact hcalc
                _ = (γstar j) * τj - (1 / 2 : ℝ) * μ * (γstar j) ^ (2 : ℕ) := by
                      have hτ_sum : ∑ i, |x i - c j i| ≤ μ := by
                        simpa [τj] using hτ
                      simp [γstar, hτ_sum, τj]
            · have hpsi' : ψμ τj = τj - μ / 2 := by
                simpa [hτ] using (hpsi_piece τj hτ_nonneg)
              have hpsi'' : ψμ τj = τj - (1 / 2 : ℝ) * μ := by
                simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hpsi'
              calc
                ψμ τj = τj - (1 / 2 : ℝ) * μ := hpsi''
                _ = (γstar j) * τj - (1 / 2 : ℝ) * μ * (γstar j) ^ (2 : ℕ) := by
                      have hτ_sum : ¬ ∑ i, |x i - c j i| ≤ μ := by
                        simpa [τj] using hτ
                      simp [γstar, hτ_sum, τj, mul_comm, mul_left_comm]
          have :
              (γstar j) * τj - (1 / 2 : ℝ) * μ * (γstar j) ^ (2 : ℕ) ≤
                (γstar j) * τj - (1 / 2 : ℝ) * μ * ‖uStar j‖ ^ (2 : ℕ) := by
            linarith [hpen]
          simpa [τj, hpsi, hdot] using this
        have hsum :
            ∑ j, m j * ψμ (∑ i, |x i - c j i|) ≤
              ∑ j, m j *
                ((∑ i, uStar j i * (x i - c j i)) -
                  (1 / 2 : ℝ) * μ * ‖uStar j‖ ^ (2 : ℕ)) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact mul_le_mul_of_nonneg_left (hterm j) (hm j)
        simpa [hF_simp_uStar] using hsum
      have hbd : BddAbove (F '' Q2) := by
        refine ⟨∑ j, m j * ψμ (∑ i, |x i - c j i|), ?_⟩
        rintro _ ⟨u, hu, rfl⟩
        exact hF_le u hu
      have hmem : F uStar ∈ (F '' Q2) := ⟨uStar, huStar, rfl⟩
      have hle_sup : F uStar ≤ sSup (F '' Q2) := le_csSup hbd hmem
      exact le_trans hF_ge hle_sup
    have :
        fμ x = ∑ j, m j * ψμ (∑ i, |x i - c j i|) := by
      -- unwrap `fμ` and the definition of `SmoothedMaxFunction`
      have : fμ x = sSup (F '' Q2) := by simp [fμ, SmoothedMaxFunction, F]
      -- combine bounds
      have hle : fμ x ≤ ∑ j, m j * ψμ (∑ i, |x i - c j i|) := by
        simpa [this] using hupper
      have hge : (∑ j, m j * ψμ (∑ i, |x i - c j i|)) ≤ fμ x := by
        simpa [this] using hlower
      exact le_antisymm hle hge
    exact this
  refine ⟨hmain, ?_⟩
  exact hpsi_piece
