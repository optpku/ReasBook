/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E]

/-- Helper for Corollary 6.56: the Moreau quadratic kernel only takes finite real values, so it
never attains `⊥`. -/
lemma moreau_quadratic_kernel_ne_bot (μ : PosReal) : ∀ z : E, ω(μ) z ≠ ⊥ := by
  intro z
  -- The quadratic kernel is defined by an `EReal` coercion of a real number.
  rw [moreau_quadratic_kernel_apply]
  exact EReal.coe_ne_bot _

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Corollary 6.56: every dual-pairing term in the quadratic conjugand is bounded above
by the quadratic value `ω(1 / μ) y`. -/
lemma dual_pairing_sub_moreau_quadratic_le
    (μ : PosReal) (y : StrongDual ℝ E) (x : E) :
    ((y x : ℝ) : EReal) - ω(μ) x ≤ ω(1 / μ) y := by
  -- Rewrite both quadratic terms into their explicit real-valued formulas.
  rw [moreau_quadratic_kernel_apply, moreau_quadratic_kernel_apply]
  -- Bound the dual pairing by the operator norm.
  have hyx : y x ≤ ‖y‖ * ‖x‖ := by
    have habs : |y x| ≤ ‖y‖ * ‖x‖ := by
      simpa using (ContinuousLinearMap.le_opNorm y x)
    exact le_trans (le_abs_self _) habs
  -- Complete the square after clearing the positive denominator `2 μ`.
  have hμ : 0 < (μ : ℝ) := μ.2
  have hmul :
      2 * (μ : ℝ) * (y x) - ‖x‖ ^ (2 : ℕ) ≤
        (μ : ℝ) ^ (2 : ℕ) * ‖y‖ ^ (2 : ℕ) := by
    have hsq : 0 ≤ (‖x‖ - (μ : ℝ) * ‖y‖) ^ (2 : ℕ) := sq_nonneg _
    nlinarith
  have hdiv :
      (2 * (μ : ℝ) * (y x) - ‖x‖ ^ (2 : ℕ)) / (2 * (μ : ℝ)) ≤
        ((μ : ℝ) ^ (2 : ℕ) * ‖y‖ ^ (2 : ℕ)) / (2 * (μ : ℝ)) := by
    exact div_le_div_of_nonneg_right hmul (by positivity)
  have hreal :
      y x - (1 / (2 * (μ : ℝ))) * ‖x‖ ^ (2 : ℕ) ≤
        (1 / (2 * ((1 / μ : PosReal) : ℝ))) * ‖y‖ ^ (2 : ℕ) := by
    have hreal' :
        y x - (1 / (2 * (μ : ℝ))) * ‖x‖ ^ (2 : ℕ) ≤
          ((μ : ℝ) / 2) * ‖y‖ ^ (2 : ℕ) := by
      convert hdiv using 1 <;> field_simp [ne_of_gt hμ]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using hreal'
  exact_mod_cast hreal

/-- Helper for Corollary 6.56: evaluating the quadratic conjugand at the scaled vector
`μ (y u) u` yields the exact quadratic lower-bound value `(μ / 2) (y u)^2`. -/
lemma dual_pairing_sub_moreau_quadratic_eq_scaled_apply
    (μ : PosReal) (y : StrongDual ℝ E) (u : E) (hu : ‖u‖ = 1) :
    (((y (((μ : ℝ) * (y u)) • u) : ℝ) : EReal) - ω(μ) (((μ : ℝ) * (y u)) • u)) =
      ((((μ : ℝ) / 2) * (y u) ^ (2 : ℕ) : ℝ) : EReal) := by
  let x : E := (((μ : ℝ) * (y u)) • u)
  -- Expand the conjugand at the chosen test point.
  change (((y x : ℝ) : EReal) - ω(μ) x) =
    ((((μ : ℝ) / 2) * (y u) ^ (2 : ℕ) : ℝ) : EReal)
  rw [moreau_quadratic_kernel_apply]
  have hx_def : x = (((μ : ℝ) * (y u)) • u) := rfl
  have hy_apply : y x = ((μ : ℝ) * (y u)) * (y u) := by
    rw [hx_def]
    simp [mul_comm, mul_left_comm]
  rw [hy_apply]
  have hnorm : ‖x‖ ^ (2 : ℕ) = (((μ : ℝ) * (y u)) ^ (2 : ℕ)) := by
    rw [hx_def]
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
  have hμ : (μ : ℝ) ≠ 0 := ne_of_gt μ.2
  rw [hnorm]
  -- The remaining identity is a scalar algebra calculation.
  have hreal :
      (μ : ℝ) * (y u) * (y u) -
          (1 / (2 * (μ : ℝ))) * (((μ : ℝ) * (y u)) ^ (2 : ℕ)) =
        ((μ : ℝ) / 2) * (y u) ^ (2 : ℕ) := by
    field_simp [hμ]
    ring
  exact_mod_cast hreal

/-- Helper for Corollary 6.56: every strict lower target below `ω(1 / μ) y` is attained strictly
below the quadratic conjugate supremum by a suitable test point. -/
lemma strict_lower_bound_lt_conjugand
    (μ : PosReal) (y : StrongDual ℝ E) (r : ℝ)
    (hr_nonneg : 0 ≤ r) (hr_lt : ((2 * r) / (μ : ℝ)) < ‖y‖ ^ (2 : ℕ)) :
    ∃ x : E, (r : EReal) < ((y x : ℝ) : EReal) - ω(μ) x := by
  let s : ℝ := Real.sqrt ((2 * r) / (μ : ℝ))
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have harg_nonneg : 0 ≤ (2 * r) / (μ : ℝ) := by
    exact div_nonneg (by positivity) (le_of_lt μ.2)
  have hs_sq : s ^ (2 : ℕ) = (2 * r) / (μ : ℝ) := by
    -- This identifies the square root parameter with the chosen normalized level.
    dsimp [s]
    rw [Real.sq_sqrt harg_nonneg]
  have hs_lt : s < ‖y‖ := by
    -- Strict inequality of squares upgrades to strict inequality of the nonnegative roots.
    have hslt_sq : s ^ (2 : ℕ) < ‖y‖ ^ (2 : ℕ) := by
      simpa [hs_sq] using hr_lt
    have habs : |s| < |‖y‖| := (sq_lt_sq).1 hslt_sq
    simpa [abs_of_nonneg hs_nonneg, abs_of_nonneg (norm_nonneg _)] using habs
  have hs_lt_nnnorm : (Subtype.mk s hs_nonneg : NNReal) < ‖y‖₊ := hs_lt
  obtain ⟨u, hu_norm_nnnorm, hu_apply⟩ :=
    ContinuousLinearMap.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm y hs_lt_nnnorm
  have hu_norm : ‖u‖ = 1 := congrArg (fun t : NNReal ↦ (t : ℝ)) hu_norm_nnnorm
  have h_abs : s < |y u| := by
    -- The approximate norm-attainment statement is expressed through the real absolute value.
    simpa [Real.norm_eq_abs] using hu_apply
  have habs_sq : s ^ (2 : ℕ) < (y u) ^ (2 : ℕ) := by
    have habs_sq' : s ^ (2 : ℕ) < |y u| ^ (2 : ℕ) := by
      nlinarith
    simpa [sq_abs] using habs_sq'
  have hcomp : (2 * r) / (μ : ℝ) < (y u) ^ (2 : ℕ) := by
    simpa [hs_sq] using habs_sq
  have hμ : 0 < (μ : ℝ) := μ.2
  have htarget : r < ((μ : ℝ) / 2) * (y u) ^ (2 : ℕ) := by
    -- Clear the positive denominator `μ` and compare the resulting scalar quadratics.
    have hmul : 2 * r < (y u) ^ (2 : ℕ) * (μ : ℝ) := (div_lt_iff₀ hμ).1 hcomp
    nlinarith [hmul]
  let x : E := ((μ : ℝ) * (y u)) • u
  have hx_lt :
      (r : EReal) < ((y x : ℝ) : EReal) - ω(μ) x := by
    -- The scaled test point realizes exactly the quadratic value from `htarget`.
    rw [show x = ((μ : ℝ) * (y u)) • u by rfl]
    rw [dual_pairing_sub_moreau_quadratic_eq_scaled_apply μ y u hu_norm]
    exact_mod_cast htarget
  exact ⟨x, hx_lt⟩

/-- Helper for Corollary 6.56: the Fenchel conjugate of the Moreau quadratic kernel `ω(μ)` on the
continuous dual is the reciprocal-parameter kernel `ω(1 / μ)`. -/
lemma conjugate_moreau_quadratic_kernel_eq_inv
    (μ : PosReal) (y : StrongDual ℝ E) :
    conjugate_function (ω(μ)) (y : Module.Dual ℝ E) = ω(1 / μ) y := by
  rw [conjugate_function_apply]
  refine le_antisymm ?_ ?_
  · -- The upper bound comes from the pointwise quadratic majorization of the conjugand.
    refine sSup_le ?_
    intro z hz
    rcases hz with ⟨x, rfl⟩
    exact dual_pairing_sub_moreau_quadratic_le μ y x
  · -- For the reverse inequality, approximate the dual norm from below inside the supremum.
    refine le_of_forall_lt ?_
    intro c hc
    have hS_bdd :
        BddAbove (Set.range fun x : E ↦ ((y x : ℝ) : EReal) - ω(μ) x) := by
      refine ⟨ω(1 / μ) y, ?_⟩
      intro z hz
      rcases hz with ⟨x, rfl⟩
      exact dual_pairing_sub_moreau_quadratic_le μ y x
    have hzero_mem :
        (0 : EReal) ∈ Set.range fun x : E ↦ ((y x : ℝ) : EReal) - ω(μ) x := by
      have hzero_eval :
          ((y (0 : E) : ℝ) : EReal) - ω(μ) (0 : E) = 0 := by
        simp [moreau_quadratic_kernel_apply]
      exact ⟨0, hzero_eval⟩
    cases c with
    | bot =>
        exact lt_csSup_of_lt hS_bdd hzero_mem (by simp)
    | top =>
        exfalso
        simp at hc
    | coe r =>
        by_cases hr_nonneg : 0 ≤ r
        · -- A nonnegative lower target can be encoded by a square-root threshold.
          have hc_real :
              ((2 * r) / (μ : ℝ)) < ‖y‖ ^ (2 : ℕ) := by
            simp [moreau_quadratic_kernel_apply] at hc
            have hc'' : r < ((μ : ℝ) / 2) * ‖y‖ ^ (2 : ℕ) := by
              exact_mod_cast hc
            have hmul : 2 * r < ‖y‖ ^ (2 : ℕ) * (μ : ℝ) := by
              nlinarith [hc'']
            exact (div_lt_iff₀ μ.2).2 (by simpa [mul_comm] using hmul)
          obtain ⟨x, hx⟩ := strict_lower_bound_lt_conjugand μ y r hr_nonneg hc_real
          exact lt_csSup_of_lt hS_bdd ⟨x, rfl⟩ hx
        · -- Negative lower targets are already below the zero conjugand value at `x = 0`.
          have hneg : (r : EReal) < 0 := by
            exact_mod_cast lt_of_not_ge hr_nonneg
          exact lt_csSup_of_lt hS_bdd hzero_mem (by simpa using hneg)

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Corollary 6.56 is `source-facing` in the chapter's Fenchel-conjugacy/Moreau-envelope domain.
Domain sampling identifies the relevant owner-level declarations already present in the project:
- `conjugate_function` from Definition 4.1, the chapter's `core/canonical` Fenchel-conjugate
  owner, used both on `Module.Dual ℝ E` and on `StrongDual ℝ E` through the canonical coercion;
- `M[μ, f]` and `ω(μ)` from Definition 6.7 for the Moreau envelope and its quadratic kernel;
- `conjugate_function_infimal_convolution_eq_add` from Theorem 4.7 for conjugates of infimal
  convolutions under the primitive hypothesis `∀ x, f x ≠ ⊥`;
- `half_squared_norm_conjugate_eq_half_dualNorm_sq` from Proposition 4.22 for the quadratic
  conjugate formula on `Module.Dual ℝ E`.

Owner choice: the main corollary should stay on the source-facing primal-space surface
`f∗ x`, while the continuous-dual statement is only a companion bridge.

Primitive data: `f`, `μ`, the primal vector `x`, and the non-`⊥` hypothesis on `f`.
Derived API: the continuous-dual reformulation at `y : StrongDual ℝ E`, expressed by the same
owner `conjugate_function` through the canonical coercion `StrongDual ℝ E → Module.Dual ℝ E`. -/
recall conjugate_function
recall conjugate_function_primal
recall moreau_quadratic_kernel

-- Proof sketch: rewrite the source conjugate as the Chapter 4 owner `conjugate_function`
-- evaluated through `f∗`, unfold `M[μ, f]` as `f □ ω(μ)`, apply the
-- owner-level
-- infimal-convolution conjugacy formula using only `hf_ne_bot` and the obvious non-`⊥` property
-- of `ω(μ)` for `μ > 0`, and then identify the quadratic conjugate through the Riesz isometry.
/-- Corollary 6.56: if `f` never takes the value `⊥` and `μ > 0`, then the Fenchel conjugate of
the Moreau envelope, viewed on the primal space through `toDualMap ℝ E`, is the conjugate of `f`
plus the chapter quadratic owner `ω(1 / μ) x`, i.e. `(μ / 2) ‖x‖²`. -/
theorem conjugate_moreau_envelope_eq_add_quadratic
    (f : E → EReal) (hf_ne_bot : ∀ x, f x ≠ ⊥) (μ : PosReal) (x : E) :
    ((M[μ, f])∗) x = (f∗) x + ω(1 / μ) x := by
  -- Route correction: prove the source-facing primal identity directly by evaluating the owner
  -- infimal-convolution conjugacy theorem at the Riesz image `toDualMap ℝ E x`.
  rw [conjugate_function_primal_apply, conjugate_function_primal_apply]
  have hconj :
      conjugate_function (M[μ, f]) (InnerProductSpace.toDualMap ℝ E x) =
        conjugate_function f (InnerProductSpace.toDualMap ℝ E x) +
          conjugate_function (ω(μ))
            (InnerProductSpace.toDualMap ℝ E x : Module.Dual ℝ E) := by
    simpa only [moreau_envelope, Pi.add_apply] using
      congrFun
        (conjugate_function_infimal_convolution_eq_add
          f (ω(μ)) hf_ne_bot (moreau_quadratic_kernel_ne_bot μ))
        (InnerProductSpace.toDualMap ℝ E x)
  -- The remaining term is exactly the primal specialization of the quadratic-conjugate helper.
  calc
    conjugate_function (M[μ, f]) (InnerProductSpace.toDualMap ℝ E x)
        = conjugate_function f (InnerProductSpace.toDualMap ℝ E x) +
            conjugate_function (ω(μ))
              (InnerProductSpace.toDualMap ℝ E x : Module.Dual ℝ E) := hconj
    _ = conjugate_function f (InnerProductSpace.toDualMap ℝ E x) +
          ω(1 / μ) (InnerProductSpace.toDualMap ℝ E x) := by
          rw [conjugate_moreau_quadratic_kernel_eq_inv
            (μ := μ) (y := InnerProductSpace.toDualMap ℝ E x)]
    _ = conjugate_function f (InnerProductSpace.toDualMap ℝ E x) + ω(1 / μ) x := by
          congr 1
          rw [moreau_quadratic_kernel_apply, moreau_quadratic_kernel_apply,
            (InnerProductSpace.toDualMap ℝ E).norm_map]
    _ = (f∗) x + ω(1 / μ) x := by
          rw [conjugate_function_primal_apply]

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Companion `bridge/view` layer: the same identity on the continuous dual is expressed directly
with the canonical owner `conjugate_function`, using the coercion `StrongDual ℝ E → Module.Dual ℝ
E`. The quadratic term should stay on the chapter owner surface `ω(1 / μ)`, now evaluated on
`StrongDual ℝ E`. This is derived API, not the source-facing main statement of the corollary. -/
recall conjugate_function
recall moreau_quadratic_kernel

-- Proof sketch: unfold `M[μ, f]` as `f □ ω(μ)`, apply the owner-level infimal-convolution
-- conjugacy formula at the continuous dual point `y`, and identify the conjugate of `ω(μ)` with
-- the same chapter quadratic owner `ω(1 / μ)` on `StrongDual ℝ E`.
/-- Continuous-dual bridge form of Corollary 6.56: if `f` never takes the value `⊥` and `μ > 0`,
then the Fenchel conjugate of the Moreau envelope on `StrongDual ℝ E` is the conjugate of `f`
plus the chapter quadratic owner `ω(1 / μ) y`. -/
theorem conjugate_moreau_envelope_strongDual_eq_add_quadratic
    (f : E → EReal) (hf_ne_bot : ∀ x, f x ≠ ⊥) (μ : PosReal) (y : StrongDual ℝ E) :
    conjugate_function (M[μ, f]) y =
      conjugate_function f y + ω(1 / μ) y := by
  -- Apply the owner-level infimal-convolution conjugacy theorem at the continuous-dual point `y`.
  have hconj :
      conjugate_function (M[μ, f]) y =
        conjugate_function f y + conjugate_function (ω(μ)) (y : Module.Dual ℝ E) := by
    simpa only [moreau_envelope, Pi.add_apply] using
      congrFun
        (conjugate_function_infimal_convolution_eq_add
          f (ω(μ)) hf_ne_bot (moreau_quadratic_kernel_ne_bot μ))
        y
  -- Then replace the quadratic conjugate term by the reciprocal-parameter kernel.
  calc
    conjugate_function (M[μ, f]) y
        = conjugate_function f y + conjugate_function (ω(μ)) (y : Module.Dual ℝ E) := hconj
    _ = conjugate_function f y + ω(1 / μ) y := by
          rw [conjugate_moreau_quadratic_kernel_eq_inv (μ := μ) (y := y)]

end
