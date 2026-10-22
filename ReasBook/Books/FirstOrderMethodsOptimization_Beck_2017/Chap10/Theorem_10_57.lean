/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Proposition_10_56
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Proposition_10_58
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_34
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_41

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

variable {f h hμ : E → ℝ} {g : E → EReal} {XStar : Set E} {HOpt : ℝ}
variable {Lf : NNReal} {α β : PosReal}

/- Theorem 10.57 is `source-facing`: it is the explicit `O(1 / ε)` iteration-complexity bound for
the S-FISTA iterates.

Domain sampling in the local Chapter 10 API identifies the existing owners that should remain on
the public surface:
- `IsSFISTAProblem` from Proposition 10.56 for Assumption 10.56;
- `IsSmoothApproximation` from Definition 10.43 for the chosen smoothing `h_μ`;
- `IsSFISTAProblem.bounded_real_sublevel_radius` from Proposition 10.56 for the canonical
  sublevel-radius owner used at the real level corresponding to `H(x⁰) + ε / 2`;
- `s_fista_curvature_bound` from Proposition 10.58 for the source-facing smoothed curvature
  parameter `L̃ = L_f + α / μ`;
- `s_fista_x` from Proposition 10.58 as the canonical S-FISTA iterate owner.

The genuinely new source data in this item are the explicit smoothing parameter `μ` and the scalar
quantity `Γ = (R_{H(x⁰) + ε / 2} + ‖x⁰‖)^2`, so these are added as thin helper definitions rather
than wrapped into a new trajectory or problem package. The regularizer side conditions needed by
`s_fista_x` are already supplied canonically by the `IsSFISTAProblem.sFistaX` bridge from
Proposition 10.58. -/
-- Semantic recall: `lean_leansearch` did not return a useful generic mathlib owner for this
-- chapter-specific statement, and the local verified owners are `IsSFISTAProblem`,
-- `IsSmoothApproximation`, `s_fista_x`, and `IsSFISTAProblem.bounded_real_sublevel_radius`.

-- Proof sketch: the numerator `√(α / β) * ε` is positive and the denominator
-- `√(αβ) + √(αβ + L_f ε)` is positive, so their quotient is positive.
/-- The explicit smoothing parameter used in Theorem 10.57 has positive real value. -/
theorem s_fista_complexity_smoothing_parameter_pos
    (ε : PosReal) (α β : PosReal) (Lf : NNReal) :
    0 <
      ((Real.sqrt ((α : ℝ) / (β : ℝ))) * (ε : ℝ)) /
        (Real.sqrt ((α : ℝ) * (β : ℝ)) +
          Real.sqrt ((α : ℝ) * (β : ℝ) + (Lf : ℝ) * (ε : ℝ))) := by
  -- The numerator is positive because both the square-root factor and `ε` are positive.
  have hnum :
      0 < Real.sqrt ((α : ℝ) / (β : ℝ)) * (ε : ℝ) := by
    refine mul_pos ?_ (PosReal.coe_pos ε)
    apply Real.sqrt_pos.2
    exact div_pos (PosReal.coe_pos α) (PosReal.coe_pos β)
  -- The denominator is positive because it is a sum of nonnegative square roots with a positive
  -- first term.
  have hden :
      0 <
        Real.sqrt ((α : ℝ) * (β : ℝ)) +
          Real.sqrt ((α : ℝ) * (β : ℝ) + (Lf : ℝ) * (ε : ℝ)) := by
    refine add_pos_of_pos_of_nonneg ?_ (Real.sqrt_nonneg _)
    apply Real.sqrt_pos.2
    exact mul_pos (PosReal.coe_pos α) (PosReal.coe_pos β)
  exact div_pos hnum hden

/-- The smoothing parameter
`μ = (√(α / β) * ε) / (√(αβ) + √(αβ + L_f ε))` used in Theorem 10.57. -/
def s_fista_complexity_smoothing_parameter
    (ε : PosReal) (α β : PosReal) (Lf : NNReal) : PosReal :=
  ⟨((Real.sqrt ((α : ℝ) / (β : ℝ))) * (ε : ℝ)) /
      (Real.sqrt ((α : ℝ) * (β : ℝ)) +
        Real.sqrt ((α : ℝ) * (β : ℝ) + (Lf : ℝ) * (ε : ℝ))),
    s_fista_complexity_smoothing_parameter_pos ε α β Lf⟩

-- Proof sketch: unfold `s_fista_complexity_smoothing_parameter`; coercing the resulting
-- `PosReal` to `ℝ` returns exactly the defining formula.
/-- Coercing the smoothing parameter from Theorem 10.57 to `ℝ` recovers its defining formula. -/
@[simp] theorem s_fista_complexity_smoothing_parameter_coe
    (ε : PosReal) (α β : PosReal) (Lf : NNReal) :
    ((s_fista_complexity_smoothing_parameter ε α β Lf : PosReal) : ℝ) =
      ((Real.sqrt ((α : ℝ) / (β : ℝ))) * (ε : ℝ)) /
        (Real.sqrt ((α : ℝ) * (β : ℝ)) +
          Real.sqrt ((α : ℝ) * (β : ℝ) + (Lf : ℝ) * (ε : ℝ))) := by
  -- The packaged `PosReal` stores exactly this real number in its carrier field.
  rfl

/-- The quantity `Γ = (R_{H(x⁰) + ε / 2} + ‖x⁰‖)^2` appearing in the S-FISTA complexity bound. -/
def s_fista_complexity_gamma (Rlevel : PosReal) (x0 : E) : ℝ :=
  ((Rlevel : ℝ) + ‖x0‖) ^ (2 : ℕ)

/-- Helper for Theorem 10.57: multiplying `β` by `√(α / β)` recovers `√(αβ)`. -/
lemma beta_mul_sqrtDiv_eq_sqrtMul (α β : PosReal) :
    (β : ℝ) * Real.sqrt ((α : ℝ) / (β : ℝ)) =
      Real.sqrt ((α : ℝ) * (β : ℝ)) := by
  have hβ_nonneg : 0 ≤ (β : ℝ) := le_of_lt (PosReal.coe_pos β)
  have hβ_ne : (β : ℝ) ≠ 0 := ne_of_gt (PosReal.coe_pos β)
  -- Replace `β` by `√(β²)` and merge the two square roots into `√(αβ)`.
  calc
    (β : ℝ) * Real.sqrt ((α : ℝ) / (β : ℝ))
        = Real.sqrt ((β : ℝ) * (β : ℝ)) * Real.sqrt ((α : ℝ) / (β : ℝ)) := by
            rw [Real.sqrt_mul_self hβ_nonneg]
    _ = Real.sqrt (((β : ℝ) * (β : ℝ)) * ((α : ℝ) / (β : ℝ))) := by
          rw [← Real.sqrt_mul (mul_nonneg hβ_nonneg hβ_nonneg)]
    _ = Real.sqrt ((α : ℝ) * (β : ℝ)) := by
          congr 1
          field_simp [hβ_ne]

/-- Helper for Theorem 10.57: dividing `α` by `√(α / β)` also recovers `√(αβ)`. -/
lemma alpha_div_sqrtDiv_eq_sqrtMul (α β : PosReal) :
    (α : ℝ) / Real.sqrt ((α : ℝ) / (β : ℝ)) =
      Real.sqrt ((α : ℝ) * (β : ℝ)) := by
  have hβ_ne : (β : ℝ) ≠ 0 := ne_of_gt (PosReal.coe_pos β)
  have hsqrt_pos : 0 < Real.sqrt ((α : ℝ) / (β : ℝ)) := by
    apply Real.sqrt_pos.2
    exact div_pos (PosReal.coe_pos α) (PosReal.coe_pos β)
  have hsqrt_ne : Real.sqrt ((α : ℝ) / (β : ℝ)) ≠ 0 := ne_of_gt hsqrt_pos
  have hdiv_nonneg : 0 ≤ (α : ℝ) / (β : ℝ) := by
    exact div_nonneg (le_of_lt (PosReal.coe_pos α)) (le_of_lt (PosReal.coe_pos β))
  have hsq :
      Real.sqrt ((α : ℝ) / (β : ℝ)) * Real.sqrt ((α : ℝ) / (β : ℝ)) =
        (α : ℝ) / (β : ℝ) := by
    simpa [pow_two] using Real.sq_sqrt hdiv_nonneg
  calc
    (α : ℝ) / Real.sqrt ((α : ℝ) / (β : ℝ))
        = ((β : ℝ) * ((α : ℝ) / (β : ℝ))) / Real.sqrt ((α : ℝ) / (β : ℝ)) := by
            field_simp [hβ_ne]
    _ = ((β : ℝ) * (Real.sqrt ((α : ℝ) / (β : ℝ)) *
            Real.sqrt ((α : ℝ) / (β : ℝ)))) / Real.sqrt ((α : ℝ) / (β : ℝ)) := by
          rw [hsq]
    _ = (β : ℝ) * Real.sqrt ((α : ℝ) / (β : ℝ)) := by
          field_simp [hsqrt_ne]
    _ = Real.sqrt ((α : ℝ) * (β : ℝ)) := beta_mul_sqrtDiv_eq_sqrtMul α β

/-- Helper for Theorem 10.57: the product `√(α / β) * √(αβ)` recovers `α`. -/
lemma sqrtDiv_mul_sqrtMul_eq_alpha (α β : PosReal) :
    Real.sqrt ((α : ℝ) / (β : ℝ)) * Real.sqrt ((α : ℝ) * (β : ℝ)) = (α : ℝ) := by
  calc
    Real.sqrt ((α : ℝ) / (β : ℝ)) * Real.sqrt ((α : ℝ) * (β : ℝ))
        = Real.sqrt ((α : ℝ) / (β : ℝ)) *
            ((β : ℝ) * Real.sqrt ((α : ℝ) / (β : ℝ))) := by
              rw [beta_mul_sqrtDiv_eq_sqrtMul]
    _ = (β : ℝ) * (Real.sqrt ((α : ℝ) / (β : ℝ)) * Real.sqrt ((α : ℝ) / (β : ℝ))) := by
          ring
    _ = (β : ℝ) * ((α : ℝ) / (β : ℝ)) := by
          have hdiv_nonneg : 0 ≤ (α : ℝ) / (β : ℝ) := by
            exact div_nonneg (le_of_lt (PosReal.coe_pos α)) (le_of_lt (PosReal.coe_pos β))
          have hsq :
              Real.sqrt ((α : ℝ) / (β : ℝ)) * Real.sqrt ((α : ℝ) / (β : ℝ)) =
                (α : ℝ) / (β : ℝ) := by
            simpa [pow_two] using Real.sq_sqrt hdiv_nonneg
          rw [hsq]
    _ = (α : ℝ) := by
          field_simp [ne_of_gt (PosReal.coe_pos β)]

-- Proof sketch: rewrite `β * μ` using the explicit formula for `μ`, compare the denominator with
-- `2 * √(αβ)`, and then cancel the common positive factor.
/-- Helper for Theorem 10.57: the chosen smoothing parameter satisfies
`β * μ ≤ ε / 2`. -/
lemma sFistaSmoothingErrorLeHalfEpsilon
    (ε : PosReal) (α β : PosReal) (Lf : NNReal) :
    (β : ℝ) * ((s_fista_complexity_smoothing_parameter ε α β Lf : PosReal) : ℝ) ≤
      (ε : ℝ) / 2 := by
  -- Route correction: the source formula is `(√(α / β) * ε) / (...)`, so we first normalize
  -- `β * √(α / β)` to `√(αβ)` and then compare the denominator with `2 * √(αβ)`.
  have hβ_nonneg : 0 ≤ (β : ℝ) := le_of_lt (PosReal.coe_pos β)
  have hbeta_sqrt :
      (β : ℝ) * Real.sqrt ((α : ℝ) / (β : ℝ)) =
        Real.sqrt ((α : ℝ) * (β : ℝ)) := by
    -- Normalize the mixed square-root factor once so the denominator comparison becomes scalar.
    exact beta_mul_sqrtDiv_eq_sqrtMul α β
  let den : ℝ :=
    Real.sqrt ((α : ℝ) * (β : ℝ)) +
      Real.sqrt ((α : ℝ) * (β : ℝ) + (Lf : ℝ) * (ε : ℝ))
  have hsqrt_pos : 0 < Real.sqrt ((α : ℝ) * (β : ℝ)) := by
    -- The leading square root is strictly positive because `αβ > 0`.
    apply Real.sqrt_pos.2
    exact mul_pos (PosReal.coe_pos α) (PosReal.coe_pos β)
  have hden_lower_raw :
      Real.sqrt ((α : ℝ) * (β : ℝ)) ≤
        Real.sqrt ((α : ℝ) * (β : ℝ) + (Lf : ℝ) * (ε : ℝ)) := by
    -- The second square root dominates the first since `Lf * ε ≥ 0`.
    apply Real.sqrt_le_sqrt
    nlinarith [NNReal.coe_nonneg Lf, PosReal.coe_pos ε]
  have hden_lower : 2 * Real.sqrt ((α : ℝ) * (β : ℝ)) ≤ den := by
    -- Summing the dominant square root with the first one gives the required denominator bound.
    dsimp [den]
    nlinarith [hden_lower_raw]
  have hden_pos : 0 < den := by
    -- The denominator is strictly positive because its first summand already is.
    dsimp [den]
    exact add_pos_of_pos_of_nonneg hsqrt_pos (Real.sqrt_nonneg _)
  have hnum_assoc :
      (β : ℝ) * (Real.sqrt ((α : ℝ) / (β : ℝ)) * (ε : ℝ)) =
        ((β : ℝ) * Real.sqrt ((α : ℝ) / (β : ℝ))) * (ε : ℝ) := by
    ring
  -- Rewrite `β * μ` into a single quotient and clear the denominator.
  rw [s_fista_complexity_smoothing_parameter_coe, ← mul_div_assoc, hnum_assoc, hbeta_sqrt]
  refine (div_le_iff₀ hden_pos).2 ?_
  -- Scale the denominator lower bound by the positive factor `ε / 2`.
  nlinarith [hden_lower, PosReal.coe_pos ε]

section

variable
  (ε : PosReal)
  (x0 : E)

local notation "μ" => s_fista_complexity_smoothing_parameter ε α β Lf
local notation "Hsf" => H[f.toEReal, h.toEReal, g]

namespace IsSFISTAProblem

/-- Helper for Theorem 10.57: the scalar quantity `Γ = (R + ‖x⁰‖)^2` is nonnegative. -/
lemma sFistaGamma_nonneg (Rlevel : PosReal) :
    0 ≤ s_fista_complexity_gamma Rlevel x0 := by
  -- `Γ` is a square, so it is automatically nonnegative.
  dsimp [s_fista_complexity_gamma]
  positivity

/-- Helper for Theorem 10.57: the explicit iteration threshold is strictly positive. -/
lemma sFistaIterationThresholdPos (Rlevel : PosReal) :
    0 <
      2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) / (ε : ℝ) +
        Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) / Real.sqrt (ε : ℝ) := by
  have hGamma_pos : 0 < s_fista_complexity_gamma Rlevel x0 := by
    -- The explicit radius term is positive, so its square `Γ` is positive as well.
    dsimp [s_fista_complexity_gamma]
    have hsum_pos : 0 < (Rlevel : ℝ) + ‖x0‖ := by
      nlinarith [PosReal.coe_pos Rlevel, norm_nonneg x0]
    positivity
  have hsqrt₁_pos :
      0 < Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) := by
    have htwiceAlphaBeta_pos : 0 < 2 * (α : ℝ) * (β : ℝ) := by
      nlinarith [PosReal.coe_pos α, PosReal.coe_pos β]
    have hinside_pos :
        0 < 2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0 := by
      exact mul_pos htwiceAlphaBeta_pos hGamma_pos
    exact Real.sqrt_pos.2 hinside_pos
  have hsqrt₂_nonneg :
      0 ≤ Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) := by
    exact Real.sqrt_nonneg _
  have hε_pos : 0 < (ε : ℝ) := PosReal.coe_pos ε
  have hsqrtε_pos : 0 < Real.sqrt (ε : ℝ) := Real.sqrt_pos.2 hε_pos
  have hfirst_pos :
      0 <
        2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) /
          (ε : ℝ) := by
    exact div_pos (mul_pos (by norm_num) hsqrt₁_pos) hε_pos
  have hsecond_nonneg :
      0 ≤
        Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) / Real.sqrt (ε : ℝ) := by
    exact div_nonneg hsqrt₂_nonneg hsqrtε_pos.le
  exact add_pos_of_pos_of_nonneg hfirst_pos hsecond_nonneg

/-- Helper for Theorem 10.57: a smoothed minimizer lies in the original
`H(x⁰) + ε / 2` sublevel, so its distance from `x⁰` is bounded by `Γ`. -/
lemma sFistaDistanceSqLeGamma
    (_problem : IsSFISTAProblem f h g XStar HOpt Lf α β)
    (hhμ : IsSmoothApproximation h hμ α β μ)
    {HμOpt : ℝ}
    (_hfast :
      IsFastProximalGradientProblem (fun x ↦ f x + hμ x) g
        (unconstrained_problem_solutions H[f.toEReal, hμ.toEReal, g])
        HμOpt
        (Lf + PosReal.toNNReal α / PosReal.toNNReal μ))
    (Rlevel : PosReal)
    (hlevel :
      ∀ ⦃x : E⦄,
        Hsf x ≤
          Hsf x0 + (((ε : ℝ) / 2 : ℝ) : EReal) →
            ‖x‖ ≤ (Rlevel : ℝ))
    {xμStar : E}
    (hxμStar :
      xμStar ∈ unconstrained_problem_solutions H[f.toEReal, hμ.toEReal, g]) :
    ‖x0 - xμStar‖ ^ (2 : ℕ) ≤ s_fista_complexity_gamma Rlevel x0 := by
  let Hμ : E → EReal := H[f.toEReal, hμ.toEReal, g]
  have hxμStar_min : ∀ y : E, Hμ xμStar ≤ Hμ y := by
    -- The smoothed optimizer minimizes the smoothed objective over the whole space.
    exact mem_unconstrained_problem_solutions_iff_forall_le.mp hxμStar
  have hsmoothed_le_original (x : E) : Hμ x ≤ Hsf x := by
    -- Replacing `hμ` by `h` can only increase the objective because `hμ ≤ h`.
    have hlower : ((hμ x : ℝ) : EReal) ≤ (h x : EReal) := by
      exact_mod_cast hhμ.lower_le x
    calc
      Hμ x = ((f x : EReal) + hμ x) + g x := by
        simp [Hμ, Function.toEReal, add_assoc]
      _ ≤ ((f x : EReal) + h x) + g x := by
        have hsum_with_g :
            ((hμ x : EReal) + g x) ≤ ((h x : EReal) + g x) := by
          simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hlower (g x)
        have htotal :
            (((hμ x : EReal) + g x) + f x) ≤ (((h x : EReal) + g x) + f x) := by
          exact add_le_add_left hsum_with_g (f x : EReal)
        simpa [add_assoc, add_left_comm, add_comm] using htotal
      _ = Hsf x := by
        simp [Function.toEReal, add_assoc]
  have horiginal_le_smoothed_add (x : E) :
      Hsf x ≤ Hμ x + ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal)) := by
    -- The smooth-approximation upper bound shifts the original objective by at most `β μ`.
    have hupper :
        (h x : EReal) ≤ (((hμ x + (β : ℝ) * (μ : ℝ) : ℝ) : ℝ) : EReal) := by
      exact_mod_cast hhμ.upper_le x
    calc
      Hsf x = ((f x : EReal) + h x) + g x := by
        simp [Function.toEReal, add_assoc]
      _ ≤ ((f x : EReal) + (((hμ x + (β : ℝ) * (μ : ℝ) : ℝ) : EReal))) + g x := by
        have hsum_with_g :
            ((h x : EReal) + g x) ≤
              ((((hμ x + (β : ℝ) * (μ : ℝ) : ℝ) : EReal)) + g x) := by
          simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hupper (g x)
        have htotal :
            (((h x : EReal) + g x) + f x) ≤
              (((((hμ x + (β : ℝ) * (μ : ℝ) : ℝ) : EReal)) + g x) + f x) := by
          exact add_le_add_left hsum_with_g (f x : EReal)
        simpa [add_assoc, add_left_comm, add_comm] using htotal
      _ = Hμ x + ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal)) := by
        simp [Hμ, Function.toEReal, add_assoc, add_comm]
  have hβμ_le_halfε :
      ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal)) ≤ ((((ε : ℝ) / 2 : ℝ) : EReal)) := by
    exact_mod_cast sFistaSmoothingErrorLeHalfEpsilon ε α β Lf
  have hxμStar_sublevel :
      Hsf xμStar ≤ Hsf x0 + ((((ε : ℝ) / 2 : ℝ) : EReal)) := by
    -- Compare `H` and `Hμ` at the minimizer and at the initial point, then use `β μ ≤ ε / 2`.
    calc
      Hsf xμStar ≤ Hμ xμStar + ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal)) :=
        horiginal_le_smoothed_add xμStar
      _ ≤ Hμ x0 + ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal)) := by
        simpa [add_assoc, add_left_comm, add_comm] using
          add_le_add_left (hxμStar_min x0) ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal))
      _ ≤ Hsf x0 + ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal)) := by
        simpa [add_assoc, add_left_comm, add_comm] using
          add_le_add_left (hsmoothed_le_original x0) ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal))
      _ ≤ Hsf x0 + ((((ε : ℝ) / 2 : ℝ) : EReal)) := by
        simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left hβμ_le_halfε (Hsf x0)
  have hxμStar_norm : ‖xμStar‖ ≤ (Rlevel : ℝ) := hlevel hxμStar_sublevel
  have hdist :
      ‖x0 - xμStar‖ ≤ ‖x0‖ + ‖xμStar‖ := by
    -- The distance to the smoothed optimizer is controlled by the triangle inequality.
    simpa [sub_eq_add_neg] using norm_add_le x0 (-xμStar)
  have hdist' :
      ‖x0 - xμStar‖ ≤ (Rlevel : ℝ) + ‖x0‖ := by
    nlinarith [hdist, hxμStar_norm]
  -- Squaring the distance bound yields the announced `Λ ≤ Γ` estimate.
  have hsum_nonneg : 0 ≤ (Rlevel : ℝ) + ‖x0‖ := by
    nlinarith [PosReal.coe_pos Rlevel, norm_nonneg x0]
  dsimp [s_fista_complexity_gamma]
  nlinarith [hdist', norm_nonneg (x0 - xμStar), hsum_nonneg]

section

variable [IsProperExtendedRealFunction g]
variable [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]

/-- Helper for Theorem 10.57: for any base point, the constant schedule
`L_k = L_f + α / μ` is the admissible constant branch of the Chapter 10 generic FISTA rule for
the smoothed fast problem. -/
lemma smoothedGenericConstantScheduleRule
    {HμOpt : ℝ}
    (hfast :
      IsFastProximalGradientProblem (fun x ↦ f x + hμ x) g
        (unconstrained_problem_solutions H[f.toEReal, hμ.toEReal, g])
        HμOpt
        (Lf + PosReal.toNNReal α / PosReal.toNNReal μ))
    (z : E) :
    hfast.SublinearRateStepsizeRule
      (fista_y (fun x ↦ f x + hμ x) g z
        (fun _ ↦ s_fista_curvature_bound Lf α μ))
      (fun _ ↦ s_fista_curvature_bound Lf α μ) 1 := by
  -- The generic smoothed FISTA recursion is in the constant-schedule branch when every
  -- curvature estimate is exactly `L̃ = L_f + α / μ`.
  left
  constructor
  · norm_num
  · intro k
    change
      ((s_fista_curvature_bound Lf α μ : PosReal) : ℝ) =
        (Lf : ℝ) + (α : ℝ) / (μ : ℝ)
    simp [s_fista_curvature_bound_coe]

/-- Helper for Theorem 10.57: every positive smoothed S-FISTA iterate inherits the same
`O(1 / k^2)` objective-gap estimate from the generic FISTA rate theorem. -/
lemma sFistaSmoothedObjectiveGapRateDivSq
    (problem : IsSFISTAProblem f h g XStar HOpt Lf α β)
    {HμOpt : ℝ}
    (hfast :
      IsFastProximalGradientProblem (fun x ↦ f x + hμ x) g
        (unconstrained_problem_solutions H[f.toEReal, hμ.toEReal, g])
        HμOpt
        (Lf + PosReal.toNNReal α / PosReal.toNNReal μ))
    {xμStar : E}
    (hxμStar :
      xμStar ∈ unconstrained_problem_solutions H[f.toEReal, hμ.toEReal, g])
    {k : ℕ} (hk : 1 ≤ k) :
    H[f.toEReal, hμ.toEReal, g] (problem.sFistaX hμ μ x0 k) -
      (HμOpt : EReal) ≤
        ((2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) *
            ‖x0 - xμStar‖ ^ (2 : ℕ) /
            (k : ℝ) ^ (2 : ℕ) : ℝ) : EReal) := by
  letI :
      IsFastProximalGradientProblem (fun x ↦ f x + hμ x) g
        (unconstrained_problem_solutions H[f.toEReal, hμ.toEReal, g])
        HμOpt
        (Lf + PosReal.toNNReal α / PosReal.toNNReal μ) := hfast
  have hrate :
      H[f.toEReal, hμ.toEReal, g] (problem.sFistaX hμ μ x0 k) -
          (HμOpt : EReal) ≤
        ((2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) *
            ‖x0 - xμStar‖ ^ (2 : ℕ) /
            (k + 1 : ℝ) ^ (2 : ℕ) : ℝ) : EReal) := by
    simpa [IsSFISTAProblem.sFistaX,
      IsSFISTAProblem.smoothed_objective_eq_fast_prox_objective,
      s_fista_curvature_bound_coe, PosReal.coe_toNNReal, mul_assoc, mul_left_comm, mul_comm] using
      (fista_objective_gap_le_two_alpha_Lf_dist_sq_div_sq
        (f := fun x ↦ f x + hμ x) (g := g)
        (XStar := unconstrained_problem_solutions H[f.toEReal, hμ.toEReal, g])
        (FOpt := HμOpt)
        (Lf := Lf + PosReal.toNNReal α / PosReal.toNNReal μ)
        (x0 := x0)
        (L := fun _ ↦ s_fista_curvature_bound Lf α μ)
        (α := 1)
        (hproblem := hfast)
        (xStar := xμStar)
        (smoothedGenericConstantScheduleRule
          (ε := ε) (hμ := hμ) (hfast := hfast) x0)
        hxμStar k hk)
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hnum_nonneg :
      0 ≤ 2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) *
        ‖x0 - xμStar‖ ^ (2 : ℕ) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (le_of_lt (PosReal.coe_pos (s_fista_curvature_bound Lf α μ))))
      (sq_nonneg ‖x0 - xμStar‖)
  have hreal :
      2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) *
          ‖x0 - xμStar‖ ^ (2 : ℕ) /
          (k + 1 : ℝ) ^ (2 : ℕ) ≤
        2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) *
          ‖x0 - xμStar‖ ^ (2 : ℕ) / (k : ℝ) ^ (2 : ℕ) := by
    refine (div_le_div_iff₀ (sq_pos_of_pos (by positivity)) (sq_pos_of_pos hk_pos)).2 ?_
    nlinarith
  exact le_trans hrate (by exact_mod_cast hreal)

end

/-- Helper for Theorem 10.57: the smoothed optimal value is bounded above by the original
optimal value because evaluating `H_μ` at an original optimizer can only decrease the objective. -/
lemma smoothedOptimalValueLeOriginalOptimalValue
    (problem : IsSFISTAProblem f h g XStar HOpt Lf α β)
    (hhμ : IsSmoothApproximation h hμ α β μ)
    {HμOpt : ℝ}
    (hfast :
      IsFastProximalGradientProblem (fun x ↦ f x + hμ x) g
        (unconstrained_problem_solutions H[f.toEReal, hμ.toEReal, g])
        HμOpt
        (Lf + PosReal.toNNReal α / PosReal.toNNReal μ)) :
    ((HμOpt : ℝ) : EReal) ≤ (HOpt : EReal) := by
  obtain ⟨xStar, hxStar⟩ := problem.optimal_set_nonempty
  have hxStar_lower :
      xStar ∈ unconstrained_problem_solutions H[f.toEReal, h.toEReal, g] := by
    simpa [problem.optimal_set_eq] using hxStar
  have hxStar_min :
      ∀ y : E, H[f.toEReal, h.toEReal, g] xStar ≤ H[f.toEReal, h.toEReal, g] y := by
    -- Read the original optimizer as a global minimizer of `H`.
    exact mem_unconstrained_problem_solutions_iff_forall_le.mp hxStar_lower
  have hxStar_value :
      H[f.toEReal, h.toEReal, g] xStar = (HOpt : EReal) := by
    -- Compare the optimizer value with the stored greatest lower bound in both directions.
    apply le_antisymm
    · exact problem.optimal_value_isGLB.2 <| by
        rintro _ ⟨y, rfl⟩
        exact hxStar_min y
    · exact problem.optimal_value_isGLB.1 ⟨xStar, rfl⟩
  have hsmoothed_le_original :
      H[f.toEReal, hμ.toEReal, g] xStar ≤ H[f.toEReal, h.toEReal, g] xStar := by
    -- Replace `h_μ` by `h` using the lower approximation inequality `h_μ ≤ h`.
    have hlower : ((hμ xStar : ℝ) : EReal) ≤ (h xStar : EReal) := by
      exact_mod_cast hhμ.lower_le xStar
    calc
      H[f.toEReal, hμ.toEReal, g] xStar
          = ((f xStar : EReal) + hμ xStar) + g xStar := by
              simp [Function.toEReal, add_assoc]
      _ ≤ ((f xStar : EReal) + h xStar) + g xStar := by
            have hsum_with_g :
                ((hμ xStar : EReal) + g xStar) ≤ ((h xStar : EReal) + g xStar) := by
              simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hlower (g xStar)
            have htotal :
                (((hμ xStar : EReal) + g xStar) + f xStar) ≤
                  (((h xStar : EReal) + g xStar) + f xStar) := by
              exact add_le_add_left hsum_with_g (f xStar : EReal)
            simpa [add_assoc, add_left_comm, add_comm] using htotal
      _ = H[f.toEReal, h.toEReal, g] xStar := by
            simp [Function.toEReal, add_assoc]
  -- Compare `H_{μ,opt}` with the value of `H_μ` at an original optimizer.
  calc
    ((HμOpt : ℝ) : EReal)
        ≤ composite_model_objective (Function.toEReal (fun x ↦ f x + hμ x)) g xStar := by
            exact hfast.optimal_value_isGLB.1 ⟨xStar, rfl⟩
    _ = H[f.toEReal, hμ.toEReal, g] xStar := by
          simp
    _ ≤ H[f.toEReal, h.toEReal, g] xStar := hsmoothed_le_original
    _ = (HOpt : EReal) := hxStar_value

/-- Helper for Theorem 10.57: the textbook optimized threshold
`K_Γ = (√(2 α β Γ) + √(2 α β Γ + 2 L_f Γ ε)) / ε`
is bounded above by the displayed iteration lower bound. -/
lemma sFistaOptimizedThresholdLeIterate
    (Rlevel : PosReal) (k : ℕ)
    (hiter :
      2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) / (ε : ℝ) +
          Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) /
            Real.sqrt (ε : ℝ) ≤
        (k : ℝ)) :
    (Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) +
        Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0 +
          2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0 * (ε : ℝ))) / (ε : ℝ) ≤
      (k : ℝ) := by
  have hε_pos : 0 < (ε : ℝ) := PosReal.coe_pos ε
  have hsqrtε_pos : 0 < Real.sqrt (ε : ℝ) := Real.sqrt_pos.2 hε_pos
  have hGamma_nonneg : 0 ≤ s_fista_complexity_gamma Rlevel x0 := by
    dsimp [s_fista_complexity_gamma]
    positivity
  have hα_nonneg : 0 ≤ (α : ℝ) := le_of_lt (PosReal.coe_pos α)
  have hβ_nonneg : 0 ≤ (β : ℝ) := le_of_lt (PosReal.coe_pos β)
  have hLf_nonneg : 0 ≤ (Lf : ℝ) := NNReal.coe_nonneg Lf
  have hε_nonneg : 0 ≤ (ε : ℝ) := le_of_lt (PosReal.coe_pos ε)
  have ha_nonneg :
      0 ≤ 2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0 := by
    positivity
  have hb_nonneg :
      0 ≤ 2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0 * (ε : ℝ) := by
    positivity
  have hsqrt_add :
      Real.sqrt
          (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0 +
            2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0 * (ε : ℝ)) ≤
        Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) +
          Real.sqrt
            (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0 * (ε : ℝ)) := by
    refine (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1 ?_
    rw [Real.sq_sqrt (add_nonneg ha_nonneg hb_nonneg)]
    have hcross :
        0 ≤
          2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) *
            Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0 * (ε : ℝ)) := by
      positivity
    nlinarith [Real.sq_sqrt ha_nonneg, Real.sq_sqrt hb_nonneg, hcross]
  have hmul :
      Real.sqrt
          (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0 * (ε : ℝ)) =
        Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) *
          Real.sqrt (ε : ℝ) := by
    rw [show 2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0 * (ε : ℝ) =
        (ε : ℝ) * (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) by ring]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Real.sqrt_mul hε_nonneg (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0))
  have hnum :
      (Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) +
          Real.sqrt
            (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0 +
              2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0 * (ε : ℝ))) /
        (ε : ℝ) ≤
        2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) / (ε : ℝ) +
          Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) / Real.sqrt (ε : ℝ) := by
    refine (div_le_iff₀ hε_pos).2 ?_
    have hright :
        (2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) / (ε : ℝ) +
            Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) / Real.sqrt (ε : ℝ)) *
            (ε : ℝ) =
          2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) +
            Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) *
              Real.sqrt (ε : ℝ) := by
      have hsqrtε_ne : Real.sqrt (ε : ℝ) ≠ 0 := ne_of_gt hsqrtε_pos
      calc
        (2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) / (ε : ℝ) +
            Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) / Real.sqrt (ε : ℝ)) *
            (ε : ℝ)
            =
          (2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) /
              (ε : ℝ)) * (ε : ℝ) +
            (Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) /
              Real.sqrt (ε : ℝ)) * (ε : ℝ) := by
                ring
        _ =
          2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) +
            (Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) /
              Real.sqrt (ε : ℝ)) * (ε : ℝ) := by
                field_simp [hε_pos.ne']
        _ =
          2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) +
            Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) *
              Real.sqrt (ε : ℝ) := by
                have hdiv :
                    (ε : ℝ) / Real.sqrt (ε : ℝ) = Real.sqrt (ε : ℝ) := by
                  apply (div_eq_iff hsqrtε_ne).2
                  symm
                  simpa [pow_two] using Real.sq_sqrt hε_nonneg
                calc
                  2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) +
                      Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) *
                        (Real.sqrt (ε : ℝ))⁻¹ * (ε : ℝ)
                      =
                    2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) +
                      Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) *
                        ((ε : ℝ) / Real.sqrt (ε : ℝ)) := by
                          rw [div_eq_mul_inv]
                          ring
                  _ =
                    2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) +
                      Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) *
                        Real.sqrt (ε : ℝ) := by
                          rw [hdiv]
    rw [hright]
    have haux :
        Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) +
            Real.sqrt
              (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0 +
                2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0 * (ε : ℝ)) ≤
          2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) +
            Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) *
              Real.sqrt (ε : ℝ) := by
      nlinarith [hsqrt_add, hmul]
    exact haux
  exact le_trans hnum hiter

/-- Helper for Theorem 10.57: once `k` dominates the textbook threshold `K_Γ`, the smoothed rate
term together with the smoothing error is at most `ε`. -/
lemma sFistaOptimizedEnvelopeBound
    (Rlevel : PosReal) (k : ℕ)
    (hK :
      (Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) +
          Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0 +
            2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0 * (ε : ℝ))) / (ε : ℝ) ≤
        (k : ℝ)) :
    2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) *
        s_fista_complexity_gamma Rlevel x0 / (k : ℝ) ^ (2 : ℕ) +
      (β : ℝ) * (μ : ℝ) ≤ (ε : ℝ) := by
  let s : ℝ := Real.sqrt ((α : ℝ) * (β : ℝ))
  let t : ℝ := Real.sqrt ((α : ℝ) * (β : ℝ) + (Lf : ℝ) * (ε : ℝ))
  let Γ : ℝ := s_fista_complexity_gamma Rlevel x0
  have hε_pos : 0 < (ε : ℝ) := PosReal.coe_pos ε
  have hΓ_pos : 0 < Γ := by
    dsimp [Γ, s_fista_complexity_gamma]
    have hsum_pos : 0 < (Rlevel : ℝ) + ‖x0‖ := by
      nlinarith [PosReal.coe_pos Rlevel, norm_nonneg x0]
    positivity
  have hs_pos : 0 < s := by
    dsimp [s]
    apply Real.sqrt_pos.2
    exact mul_pos (PosReal.coe_pos α) (PosReal.coe_pos β)
  have ht_pos : 0 < t := by
    dsimp [t]
    apply Real.sqrt_pos.2
    nlinarith [PosReal.coe_pos α, PosReal.coe_pos β, NNReal.coe_nonneg Lf, PosReal.coe_pos ε]
  have hs_add_t_pos : 0 < s + t := add_pos hs_pos ht_pos
  have hα_nonneg : 0 ≤ (α : ℝ) := le_of_lt (PosReal.coe_pos α)
  have hβ_nonneg : 0 ≤ (β : ℝ) := le_of_lt (PosReal.coe_pos β)
  have hLf_nonneg : 0 ≤ (Lf : ℝ) := NNReal.coe_nonneg Lf
  have hε_nonneg : 0 ≤ (ε : ℝ) := le_of_lt hε_pos
  have hbetaμ :
      (β : ℝ) * (μ : ℝ) = (ε : ℝ) * s / (s + t) := by
    dsimp [s, t]
    rw [s_fista_complexity_smoothing_parameter_coe]
    field_simp [hs_add_t_pos.ne']
    rw [beta_mul_sqrtDiv_eq_sqrtMul]
    ring
  have hcurvature :
      ((s_fista_curvature_bound Lf α μ : PosReal) : ℝ) = t * (s + t) / (ε : ℝ) := by
    dsimp [s, t]
    rw [s_fista_curvature_bound_coe]
    have halphaOverMu :
        (α : ℝ) / (μ : ℝ) =
          Real.sqrt ((α : ℝ) * (β : ℝ)) *
            (Real.sqrt ((α : ℝ) * (β : ℝ)) +
              Real.sqrt ((α : ℝ) * (β : ℝ) + (Lf : ℝ) * (ε : ℝ))) / (ε : ℝ) := by
      rw [s_fista_complexity_smoothing_parameter_coe]
      have hsqrtDiv_pos : 0 < Real.sqrt ((α : ℝ) / (β : ℝ)) := by
        apply Real.sqrt_pos.2
        exact div_pos (PosReal.coe_pos α) (PosReal.coe_pos β)
      have hsqrtDiv_ne : Real.sqrt ((α : ℝ) / (β : ℝ)) ≠ 0 := ne_of_gt hsqrtDiv_pos
      field_simp [hε_pos.ne', hsqrtDiv_ne]
      rw [sqrtDiv_mul_sqrtMul_eq_alpha]
    rw [halphaOverMu]
    field_simp [hε_pos.ne']
    have hs_sq :
        s ^ (2 : ℕ) = (α : ℝ) * (β : ℝ) := by
      dsimp [s]
      rw [Real.sq_sqrt (by nlinarith [PosReal.coe_pos α, PosReal.coe_pos β])]
    have ht_sq :
        t ^ (2 : ℕ) = (α : ℝ) * (β : ℝ) + (Lf : ℝ) * (ε : ℝ) := by
      dsimp [t]
      rw [Real.sq_sqrt
        (add_nonneg (mul_nonneg hα_nonneg hβ_nonneg) (mul_nonneg hLf_nonneg hε_nonneg))]
    nlinarith [hs_sq, ht_sq]
  have hK_rewrite :
      (Real.sqrt (2 * (α : ℝ) * (β : ℝ) * Γ) +
          Real.sqrt (2 * (α : ℝ) * (β : ℝ) * Γ + 2 * (Lf : ℝ) * Γ * (ε : ℝ))) /
        (ε : ℝ) =
        Real.sqrt (2 * Γ) * (s + t) / (ε : ℝ) := by
    have hfirst :
        Real.sqrt (2 * (α : ℝ) * (β : ℝ) * Γ) = Real.sqrt (2 * Γ) * s := by
      dsimp [s]
      rw [show 2 * (α : ℝ) * (β : ℝ) * Γ = (2 * Γ) * ((α : ℝ) * (β : ℝ)) by ring]
      rw [Real.sqrt_mul]
      positivity
    have hsecond :
        Real.sqrt (2 * (α : ℝ) * (β : ℝ) * Γ + 2 * (Lf : ℝ) * Γ * (ε : ℝ)) =
          Real.sqrt (2 * Γ) * t := by
      dsimp [t]
      rw [show 2 * (α : ℝ) * (β : ℝ) * Γ + 2 * (Lf : ℝ) * Γ * (ε : ℝ) =
          (2 * Γ) * ((α : ℝ) * (β : ℝ) + (Lf : ℝ) * (ε : ℝ)) by ring]
      rw [Real.sqrt_mul]
      positivity
    rw [hfirst, hsecond]
    ring
  have hK' : Real.sqrt (2 * Γ) * (s + t) / (ε : ℝ) ≤ (k : ℝ) := by
    have hK0 :
        (Real.sqrt (2 * (α : ℝ) * (β : ℝ) * Γ) +
            Real.sqrt (2 * (α : ℝ) * (β : ℝ) * Γ + 2 * (Lf : ℝ) * Γ * (ε : ℝ))) /
          (ε : ℝ) ≤
          (k : ℝ) := by
      simpa [Γ] using hK
    rw [hK_rewrite] at hK0
    exact hK0
  have hK_pos : 0 < Real.sqrt (2 * Γ) * (s + t) / (ε : ℝ) := by
    have hsqrt_pos : 0 < Real.sqrt (2 * Γ) := by
      apply Real.sqrt_pos.2
      positivity
    exact div_pos (mul_pos hsqrt_pos hs_add_t_pos) hε_pos
  have hk_pos : 0 < (k : ℝ) := lt_of_lt_of_le hK_pos hK'
  have hKsq :
      2 * Γ * (s + t) ^ (2 : ℕ) / (ε : ℝ) ^ (2 : ℕ) ≤ (k : ℝ) ^ (2 : ℕ) := by
    have hsq := (sq_le_sq₀ (le_of_lt hK_pos) (le_of_lt hk_pos)).2 hK'
    have hsq_rewrite :
        (Real.sqrt (2 * Γ) * (s + t) / (ε : ℝ)) ^ (2 : ℕ) =
          2 * Γ * (s + t) ^ (2 : ℕ) / (ε : ℝ) ^ (2 : ℕ) := by
      field_simp [hε_pos.ne']
      rw [Real.sq_sqrt (by nlinarith [hΓ_pos])]
    rw [hsq_rewrite] at hsq
    exact hsq
  have hrate_le :
      2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) * Γ / (k : ℝ) ^ (2 : ℕ) ≤
        (ε : ℝ) * t / (s + t) := by
    refine (div_le_iff₀ (pow_pos hk_pos _)).2 ?_
    have hfactor_nonneg : 0 ≤ (ε : ℝ) * t / (s + t) := by
      positivity
    have hmul_bound :
        ((ε : ℝ) * t / (s + t)) * (2 * Γ * (s + t) ^ (2 : ℕ) / (ε : ℝ) ^ (2 : ℕ)) ≤
          ((ε : ℝ) * t / (s + t)) * (k : ℝ) ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hKsq hfactor_nonneg
    have htarget :
        2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) * Γ ≤
          ((ε : ℝ) * t / (s + t)) * (2 * Γ * (s + t) ^ (2 : ℕ) / (ε : ℝ) ^ (2 : ℕ)) := by
      rw [hcurvature]
      field_simp [hε_pos.ne', hs_add_t_pos.ne']
      ring
      norm_num
    exact le_trans htarget hmul_bound
  calc
    2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) * Γ / (k : ℝ) ^ (2 : ℕ) +
        (β : ℝ) * (μ : ℝ)
        ≤ (ε : ℝ) * t / (s + t) + (ε : ℝ) * s / (s + t) := by
            rw [hbetaμ]
            nlinarith [hrate_le]
    _ = (ε : ℝ) := by
          field_simp [hs_add_t_pos.ne']
          ring

/-- Bridge/view theorem: if a radius `R_{H(x⁰) + ε / 2}` is supplied explicitly as a sublevel
bound, then the corresponding lower bound on `k` yields an `ε`-accurate S-FISTA iterate for the
original objective `H`. -/
theorem sFistaObjectiveGapLeEpsilonOfIterationBoundOfSublevelRadius
    (problem : IsSFISTAProblem f h g XStar HOpt Lf α β)
    (hhμ : IsSmoothApproximation h hμ α β μ)
    (Rlevel : PosReal)
    (hlevel :
      ∀ ⦃x : E⦄,
        Hsf x ≤
        Hsf x0 + (((ε : ℝ) / 2 : ℝ) : EReal) →
            ‖x‖ ≤ (Rlevel : ℝ))
    (k : ℕ)
    (hiter :
      2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) / (ε : ℝ) +
          Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) /
            Real.sqrt (ε : ℝ) ≤
        (k : ℝ)) :
    Hsf (problem.sFistaX hμ μ x0 k) -
      (HOpt : EReal) ≤
        ((ε : ℝ) : EReal) := by
  obtain ⟨HμOpt, hfast⟩ := problem.toIsFastProximalGradientProblem (hμ := hμ) hhμ
  letI : IsProperExtendedRealFunction g := problem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨problem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨problem.g_convex⟩
  obtain ⟨xμStar, hxμStar⟩ := hfast.optimal_set_nonempty
  have hk_pos : 0 < (k : ℝ) := by
    have hthreshold_pos :=
      sFistaIterationThresholdPos
        (ε := ε) (x0 := x0) (α := α) (β := β) (Lf := Lf) (Rlevel := Rlevel)
    exact lt_of_lt_of_le hthreshold_pos hiter
  have hk : 1 ≤ k := by
    exact Nat.succ_le_of_lt (Nat.cast_pos.mp hk_pos)
  have hdistGamma :
      ‖x0 - xμStar‖ ^ (2 : ℕ) ≤ s_fista_complexity_gamma Rlevel x0 := by
    exact problem.sFistaDistanceSqLeGamma
      (ε := ε) (x0 := x0) (hμ := hμ) hhμ hfast Rlevel hlevel hxμStar
  have hsmoothedRate :
      H[f.toEReal, hμ.toEReal, g] (problem.sFistaX hμ μ x0 k) -
        (HμOpt : EReal) ≤
          ((2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) *
              ‖x0 - xμStar‖ ^ (2 : ℕ) /
              (k : ℝ) ^ (2 : ℕ) : ℝ) : EReal) := by
    exact problem.sFistaSmoothedObjectiveGapRateDivSq
      (ε := ε) (x0 := x0) (hμ := hμ) hfast hxμStar hk
  have hsmoothedRateGamma :
      H[f.toEReal, hμ.toEReal, g] (problem.sFistaX hμ μ x0 k) -
        (HμOpt : EReal) ≤
          ((2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) *
              s_fista_complexity_gamma Rlevel x0 /
              (k : ℝ) ^ (2 : ℕ) : ℝ) : EReal) := by
    have hfactor_nonneg :
        0 ≤
          2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) /
            (k : ℝ) ^ (2 : ℕ) := by
      exact div_nonneg
        (mul_nonneg (by norm_num)
          (le_of_lt (s_fista_curvature_bound Lf α μ).2))
        (pow_nonneg (Nat.cast_nonneg k) _)
    have hreal :
        2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) *
            ‖x0 - xμStar‖ ^ (2 : ℕ) /
            (k : ℝ) ^ (2 : ℕ) ≤
          2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) *
            s_fista_complexity_gamma Rlevel x0 /
            (k : ℝ) ^ (2 : ℕ) := by
      have hmul :=
        mul_le_mul_of_nonneg_left hdistGamma hfactor_nonneg
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    exact le_trans hsmoothedRate (by exact_mod_cast hreal)
  have hK :
      (Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) +
          Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0 +
            2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0 * (ε : ℝ))) / (ε : ℝ) ≤
        (k : ℝ) := by
    exact sFistaOptimizedThresholdLeIterate
      (ε := ε) (x0 := x0) (Rlevel := Rlevel) (k := k) hiter
  have henvelope :
      2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) *
          s_fista_complexity_gamma Rlevel x0 / (k : ℝ) ^ (2 : ℕ) +
        (β : ℝ) * (μ : ℝ) ≤ (ε : ℝ) := by
    exact sFistaOptimizedEnvelopeBound
      (ε := ε) (x0 := x0) (Rlevel := Rlevel) (k := k) hK
  have horiginal_le_smoothed_add :
      Hsf (problem.sFistaX hμ μ x0 k) ≤
        H[f.toEReal, hμ.toEReal, g] (problem.sFistaX hμ μ x0 k) +
          ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal)) := by
    -- The smoothing approximation raises the original objective by at most `β μ`.
    have hupper :
        (h (problem.sFistaX hμ μ x0 k) : EReal) ≤
          (((hμ (problem.sFistaX hμ μ x0 k) + (β : ℝ) * (μ : ℝ) : ℝ) : ℝ) : EReal) := by
      exact_mod_cast hhμ.upper_le (problem.sFistaX hμ μ x0 k)
    calc
      Hsf (problem.sFistaX hμ μ x0 k)
          = ((f (problem.sFistaX hμ μ x0 k) : EReal) + h (problem.sFistaX hμ μ x0 k)) +
              g (problem.sFistaX hμ μ x0 k) := by
                simp [Function.toEReal, add_assoc]
      _ ≤ ((f (problem.sFistaX hμ μ x0 k) : EReal) +
            (((hμ (problem.sFistaX hμ μ x0 k) + (β : ℝ) * (μ : ℝ) : ℝ) : EReal))) +
              g (problem.sFistaX hμ μ x0 k) := by
            have hsum_with_g :
                ((h (problem.sFistaX hμ μ x0 k) : EReal) +
                    g (problem.sFistaX hμ μ x0 k)) ≤
                  ((((hμ (problem.sFistaX hμ μ x0 k) + (β : ℝ) * (μ : ℝ) : ℝ) : EReal)) +
                    g (problem.sFistaX hμ μ x0 k)) := by
              simpa [add_assoc, add_left_comm, add_comm] using
                add_le_add_right hupper (g (problem.sFistaX hμ μ x0 k))
            have htotal :
                (((h (problem.sFistaX hμ μ x0 k) : EReal) +
                    g (problem.sFistaX hμ μ x0 k)) + f (problem.sFistaX hμ μ x0 k)) ≤
                  (((((hμ (problem.sFistaX hμ μ x0 k) + (β : ℝ) * (μ : ℝ) : ℝ) : EReal)) +
                      g (problem.sFistaX hμ μ x0 k)) +
                    f (problem.sFistaX hμ μ x0 k)) := by
              exact add_le_add_left hsum_with_g (f (problem.sFistaX hμ μ x0 k) : EReal)
            simpa [add_assoc, add_left_comm, add_comm] using htotal
      _ = H[f.toEReal, hμ.toEReal, g] (problem.sFistaX hμ μ x0 k) +
            ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal)) := by
            simp only [Function.toEReal, Function.comp_apply, composite_model_objective_apply,
              EReal.coe_add]
            have hg_bot : g (problem.sFistaX hμ μ x0 k) ≠ ⊥ :=
              problem.g_proper.ne_bot _
            by_cases hg_top : g (problem.sFistaX hμ μ x0 k) = ⊤
            · rw [hg_top]
              rw [EReal.add_top_of_ne_bot ((EReal.add_ne_bot_iff).2
                ⟨EReal.coe_ne_bot _, (EReal.add_ne_bot_iff).2
                  ⟨EReal.coe_ne_bot _, EReal.coe_ne_bot _⟩⟩)]
              rw [EReal.add_top_of_ne_bot ((EReal.add_ne_bot_iff).2
                ⟨EReal.coe_ne_bot _, EReal.coe_ne_bot _⟩)]
              exact (EReal.top_add_coe _).symm
            · lift g (problem.sFistaX hμ μ x0 k) to ℝ using ⟨hg_top, hg_bot⟩ with gx
              norm_cast
              ring
  have hμopt_le_hopt :
      ((HμOpt : ℝ) : EReal) ≤ (HOpt : EReal) := by
    exact smoothedOptimalValueLeOriginalOptimalValue
      (ε := ε) (problem := problem) (hμ := hμ) hhμ hfast
  have hsmoothedPlusError :
      H[f.toEReal, hμ.toEReal, g] (problem.sFistaX hμ μ x0 k) -
        (HμOpt : EReal) +
        ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal)) ≤
          ((ε : ℝ) : EReal) := by
    have hsum :
        H[f.toEReal, hμ.toEReal, g] (problem.sFistaX hμ μ x0 k) -
            (HμOpt : EReal) +
            ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal)) ≤
          ((2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) *
              s_fista_complexity_gamma Rlevel x0 /
              (k : ℝ) ^ (2 : ℕ) : ℝ) : EReal) +
            ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal)) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_right hsmoothedRateGamma ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal))
    have henvelopeE :
        (((2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) *
            s_fista_complexity_gamma Rlevel x0 / (k : ℝ) ^ (2 : ℕ) +
            (β : ℝ) * (μ : ℝ) : ℝ) : EReal)) ≤ ((ε : ℝ) : EReal) := by
      exact_mod_cast henvelope
    calc
      H[f.toEReal, hμ.toEReal, g] (problem.sFistaX hμ μ x0 k) -
          (HμOpt : EReal) +
          ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal))
          ≤
        ((2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) *
            s_fista_complexity_gamma Rlevel x0 /
            (k : ℝ) ^ (2 : ℕ) : ℝ) : EReal) +
          ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal)) := hsum
      _ =
        (((2 * (((s_fista_curvature_bound Lf α μ : PosReal) : ℝ)) *
            s_fista_complexity_gamma Rlevel x0 / (k : ℝ) ^ (2 : ℕ) +
            (β : ℝ) * (μ : ℝ) : ℝ) : EReal)) := by
              simp
      _ ≤ ((ε : ℝ) : EReal) := henvelopeE
  calc
    Hsf (problem.sFistaX hμ μ x0 k) - (HOpt : EReal)
        = Hsf (problem.sFistaX hμ μ x0 k) + -(HOpt : EReal) := by
            rw [sub_eq_add_neg]
    _ ≤ (H[f.toEReal, hμ.toEReal, g] (problem.sFistaX hμ μ x0 k) +
          ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal))) + -(HμOpt : EReal) := by
            have hneg :
                -(HOpt : EReal) ≤ -(HμOpt : EReal) := by
              exact EReal.neg_le_neg_iff.2 hμopt_le_hopt
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              add_le_add horiginal_le_smoothed_add hneg
    _ = H[f.toEReal, hμ.toEReal, g] (problem.sFistaX hμ μ x0 k) -
          (HμOpt : EReal) +
          ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal)) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ ≤ ((ε : ℝ) : EReal) := hsmoothedPlusError

end IsSFISTAProblem

-- Proof sketch: derive the required sublevel-radius witness from the canonical bridge
-- `IsSFISTAProblem.bounded_real_sublevel_radius` once at the fixed level `H(x⁰) + ε / 2`, then
-- apply the explicit-radius theorem above uniformly in `k`.
/-- Theorem 10.57: assuming Proposition 10.56, if `hμ` is the smoothing used by S-FISTA with
`μ = (√(α / β) * ε) / (√(αβ) + √(αβ + L_f ε))` and if `x⁰ ∈ dom(H)`, then there exists a radius
`R_{H(x⁰) + ε / 2}` controlling the real sublevel set at level `H(x⁰) + ε / 2`, and for every
iteration index `k`, if
`2 √(2 α β Γ) / ε + √(2 L_f Γ) / √ε ≤ k` with
`Γ = (R_{H(x⁰) + ε / 2} + ‖x⁰‖)^2`, then the original objective gap at the `k`th S-FISTA iterate
is at most `ε`. -/
theorem s_fista_objective_gap_le_epsilon_of_iteration_bound
    [problem : IsSFISTAProblem f h g XStar HOpt Lf α β]
    (hhμ :
      IsSmoothApproximation h hμ α β μ)
    (hx0 : x0 ∈ effective_domain Hsf) :
    ∃ Rlevel : PosReal,
      (∀ ⦃x : E⦄,
        Hsf x ≤
          Hsf x0 + (((ε : ℝ) / 2 : ℝ) : EReal) →
            ‖x‖ ≤ (Rlevel : ℝ)) ∧
      ∀ k : ℕ,
        2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) / (ε : ℝ) +
            Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) /
              Real.sqrt (ε : ℝ) ≤
        (k : ℝ) →
          Hsf (problem.sFistaX hμ μ x0 k) -
            (HOpt : EReal) ≤
              ((ε : ℝ) : EReal) := by
  obtain ⟨Rlevel, hRlevel⟩ :=
    problem.bounded_real_sublevel_radius (((Hsf x0).toReal + (ε : ℝ) / 2 : ℝ))
  have hx0_ne_top : Hsf x0 ≠ ⊤ := (mem_effective_domain.mp hx0).ne
  have hx0_ne_bot : Hsf x0 ≠ ⊥ := by
    simpa [Function.toEReal, add_assoc] using problem.g_proper.ne_bot x0
  have hx0_coe_toReal : (((Hsf x0).toReal : ℝ) : EReal) = Hsf x0 := by
    exact EReal.coe_toReal hx0_ne_top hx0_ne_bot
  have hlevel :
      ∀ ⦃x : E⦄,
        Hsf x ≤
          Hsf x0 + (((ε : ℝ) / 2 : ℝ) : EReal) →
            ‖x‖ ≤ (Rlevel : ℝ) := by
    intro x hx
    -- Replace the finite base value `Hsf x0` by its exact `toReal` coercion.
    have hthreshold :
        Hsf x0 + (((ε : ℝ) / 2 : ℝ) : EReal) =
          ((((ε : ℝ) / 2 : ℝ) : EReal) + (((Hsf x0).toReal : ℝ) : EReal)) := by
      calc
        Hsf x0 + (((ε : ℝ) / 2 : ℝ) : EReal)
            = (((Hsf x0).toReal : ℝ) : EReal) + ((((ε : ℝ) / 2 : ℝ) : EReal)) := by
                rw [hx0_coe_toReal]
        _ = ((((ε : ℝ) / 2 : ℝ) : EReal) + (((Hsf x0).toReal : ℝ) : EReal)) := by
              rw [add_comm]
    apply hRlevel
    have hx_toReal :
        Hsf x ≤
          ((((ε : ℝ) / 2 : ℝ) : EReal) + (((Hsf x0).toReal : ℝ) : EReal)) := by
      rw [← hthreshold]
      exact hx
    simpa [add_assoc, add_left_comm, add_comm] using hx_toReal
  refine ⟨Rlevel, hlevel, ?_⟩
  intro k hk
  exact
    IsSFISTAProblem.sFistaObjectiveGapLeEpsilonOfIterationBoundOfSublevelRadius
      ε x0 problem hhμ Rlevel hlevel k hk

end

end
