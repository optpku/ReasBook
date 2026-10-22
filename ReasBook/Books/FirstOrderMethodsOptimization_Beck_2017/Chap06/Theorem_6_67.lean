/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_10
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_10
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_30
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_45

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open InnerProductSpace (toDualMap)
open scoped Pointwise

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

recall moreau_quadratic_kernel
recall moreau_envelope
recall moreau_quadratic_kernel_apply
recall moreau_envelope_eq_of_scaled_prox_eq_singleton

/- Theorem 6.67 is `source-facing` in the chapter's Moreau-envelope/Fenchel-conjugacy domain.
Domain sampling identifies the owner chain already fixed upstream:

- `M[μ, f]` and `ω(μ)` from Definition 6.7 are the `core/canonical` owners for the Moreau
  envelope and its quadratic term;
- the source-facing primal conjugate surface is the notation `f∗` from Definition 4.1;
- Theorem 6.3 supplies the canonical singleton proximal point for the scaled function `μ f`;
- Theorem 6.45 is the owner-level Moreau decomposition for those two scaled proximal problems;
- Theorem 4.10 provides the Fenchel--Young equality bridge at the resulting primal/dual pair.

Primitive data: `f`, `μ`, `x`, and the source hypotheses `hf_proper`, `hf_closed`, `hf_convex`,
with positivity carried by the parameter type. The proper/closed/convex hypotheses are
semantically active because they produce the singleton proximal point of `μ f` needed to evaluate
the Moreau envelope and to invoke the scaled Moreau-decomposition theorem. Derived API: the
quadratic term should be stated through the chapter owner `ω(μ)`, not by a duplicate inline
formula. -/
recall conjugate_function_primal
recall conjugate_function_primal_pos_real_mul
recall pairing_eq_add_conjugate_iff_mem_subdifferential
recall prox_eq_singleton_of_proper_closed_convex
recall prox_scaled_conjugate_sum_eq_singleton
recall scaled_function_proper_closed_convex_of_pos
recall toDualMap_sub_mem_strongDualSubdifferential_iff_forall_inner_le

/-- Helper for Theorem 6.67: dividing the primal conjugate by `μ` is the same as scaling it by
the reciprocal parameter `1 / μ`. -/
lemma conjugate_div_eq_inv_pos_smul
    (f : E → EReal) (μ : PosReal) :
    (fun y : E ↦ (f∗) y / (μ : EReal)) = ((((1 / μ : PosReal) : EReal) • (f∗))) := by
  -- Rewrite the pointwise scalar action on functions into the textbook division form.
  funext y
  change (f∗) y * (μ : EReal)⁻¹ = (((1 / μ : PosReal) : EReal) * (f∗) y)
  rw [mul_comm]
  congr 1
  show (μ : EReal)⁻¹ = (((1 / μ : PosReal) : EReal))
  simpa using (EReal.coe_inv (μ : ℝ)).symm

/-- Helper for Theorem 6.67: the dual proximal point paired with `u = prox_{μ f}(x)` is exactly
`μ⁻¹ • (x - u)` on the conjugate Moreau problem. -/
lemma dual_moreau_prox_eq_singleton
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (μ : PosReal) (x u : E) (hprox : prox[((μ : EReal) • f)] x = {u}) :
    prox[((((1 / μ : PosReal) : EReal) • (f∗)))] ((μ : ℝ)⁻¹ • x) =
      {((μ : ℝ)⁻¹ • (x - u))} := by
  have hdual_singleton :
      prox[(((μ : EReal) • f)∗)] x = {x - u} :=
    prox_scaled_function_conjugate_eq_singleton_residual
      f hf_proper hf_closed hf_convex μ x u hprox
  have htransport :
      (μ : ℝ) • prox[fun y ↦ (f∗) y / (μ : EReal)] ((μ : ℝ)⁻¹ • x) = {x - u} := by
    -- First transport the dual proximal problem through the canonical scaling equivalence.
    calc
      (μ : ℝ) • prox[fun y ↦ (f∗) y / (μ : EReal)] ((μ : ℝ)⁻¹ • x)
          = prox[(((μ : EReal) • f)∗)] x := by
            symm
            rw [conjugate_function_primal_pos_real_mul f (μ : ℝ) μ.2]
            simpa [smul_eq_mul] using
              proximal_mapping_smul_precompose_inv_smul (g := f∗) (lam := (μ : ℝ))
                (ne_of_gt μ.2) x
      _ = {x - u} := hdual_singleton
  have hdescaled :
      prox[fun y ↦ (f∗) y / (μ : EReal)] ((μ : ℝ)⁻¹ • x) = {((μ : ℝ)⁻¹ • (x - u))} := by
    -- Then cancel the nonzero scalar `μ` on the singleton proximal set.
    ext z
    have hμ : (μ : ℝ) ≠ 0 := ne_of_gt μ.2
    have hsmul :
        (μ : ℝ) • z ∈ (μ : ℝ) • prox[fun y ↦ (f∗) y / (μ : EReal)] ((μ : ℝ)⁻¹ • x) ↔
          z ∈ prox[fun y ↦ (f∗) y / (μ : EReal)] ((μ : ℝ)⁻¹ • x) := by
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ (a := (μ : ℝ))
        (A := prox[fun y ↦ (f∗) y / (μ : EReal)] ((μ : ℝ)⁻¹ • x)) (x := (μ : ℝ) • z)
        (ha := hμ)]
      simpa [smul_smul, inv_mul_cancel₀ hμ]
    calc
      z ∈ prox[fun y ↦ (f∗) y / (μ : EReal)] ((μ : ℝ)⁻¹ • x) ↔
          (μ : ℝ) • z ∈ (μ : ℝ) • prox[fun y ↦ (f∗) y / (μ : EReal)] ((μ : ℝ)⁻¹ • x) := by
            simpa using hsmul.symm
      _ ↔ (μ : ℝ) • z ∈ {x - u} := by rw [htransport]
      _ ↔ z ∈ {((μ : ℝ)⁻¹ • (x - u))} := by
            simp only [Set.mem_singleton_iff]
            constructor
            · intro hz
              rw [← hz]
              simpa [smul_smul, inv_mul_cancel₀ hμ]
            · intro hz
              rw [hz]
              simpa [smul_smul, mul_inv_cancel₀ hμ]
  -- Finally rewrite the divided conjugate objective into the textbook `(1 / μ) • f∗` form.
  simpa [conjugate_div_eq_inv_pos_smul] using hdescaled

/-- Helper for Theorem 6.67: the scaled proximal singleton gives the Fenchel--Young equality for
the primal point `u` and the dual residual `μ⁻¹ • (x - u)`. -/
lemma fenchel_young_eq_of_scaled_prox_singleton
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (μ : PosReal) (x u : E)
    (hprox : prox[((μ : EReal) • f)] x = {u}) :
    f u + (f∗) ((μ : ℝ)⁻¹ • (x - u)) =
      ((inner ℝ u ((μ : ℝ)⁻¹ • (x - u)) : ℝ) : EReal) := by
  rcases scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex μ with
    ⟨hscaled_proper, _, hscaled_convex⟩
  have hsub :
      toDualMap ℝ E (x - u) ∈ strongDualSubdifferential (((μ : EReal) • f)) u := by
    -- The primal proximal singleton gives the residual subgradient for the scaled problem.
    exact
      (prox_eq_singleton_iff_toDualMap_sub_mem_strongDualSubdifferential
        (((μ : EReal) • f)) hscaled_proper hscaled_convex x u).mp hprox
  have hsupport_scaled :=
      (toDualMap_sub_mem_strongDualSubdifferential_iff_forall_inner_le
        (((μ : EReal) • f)) hscaled_proper x u).1 hsub
  have hu_scaled_eff : u ∈ effective_domain (((μ : EReal) • f)) := hsupport_scaled.1
  have hu_top : f u ≠ ⊤ := by
    -- Finite scaled value at `u` forces the original value `f u` to be finite.
    intro hfu_top
    rw [mem_effective_domain] at hu_scaled_eff
    rw [Pi.smul_apply, smul_eq_mul, hfu_top, EReal.mul_top_of_pos (by exact_mod_cast μ.2)] at hu_scaled_eff
    exact not_lt_of_ge le_top hu_scaled_eff
  have hu_eff : u ∈ effective_domain f :=
    mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hu_top)
  let fu : ℝ := (f u).toReal
  have hu_val : f u = ((fu : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne (hf_proper.ne_bot u)).symm
  have hmem :
      ((toDualMap ℝ E ((μ : ℝ)⁻¹ • (x - u)) : StrongDual ℝ E) : Module.Dual ℝ E) ∈
        subdifferential f u := by
    -- Descale the supporting inequality directly on the subdifferential owner predicate.
    rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
    refine ⟨hu_eff, ?_⟩
    intro y hy
    let fy : ℝ := (f y).toReal
    have hy_val : f y = ((fy : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hy).ne (hf_proper.ne_bot y)).symm
    have hy_scaled : y ∈ effective_domain (((μ : EReal) • f)) := by
      rw [mem_effective_domain]
      calc
        (((μ : EReal) • f) y) = (((μ : EReal) * ((fy : ℝ) : EReal)) : EReal) := by
          rw [Pi.smul_apply, smul_eq_mul, hy_val]
        _ = ((((μ : ℝ) * fy : ℝ)) : EReal) := by
              rw [← EReal.coe_mul]
        _ < ⊤ := EReal.coe_lt_top _
    have hineq_scaled := hsupport_scaled.2 y hy_scaled
    have hy_scaled_val : (((μ : EReal) • f) y) = ((((μ : ℝ) * fy : ℝ)) : EReal) := by
      calc
        (((μ : EReal) • f) y) = (((μ : EReal) * ((fy : ℝ) : EReal)) : EReal) := by
          rw [Pi.smul_apply, smul_eq_mul, hy_val]
        _ = ((((μ : ℝ) * fy : ℝ)) : EReal) := by
              rw [← EReal.coe_mul]
    have hu_scaled_val : (((μ : EReal) • f) u) = ((((μ : ℝ) * fu : ℝ)) : EReal) := by
      calc
        (((μ : EReal) • f) u) = (((μ : EReal) * ((fu : ℝ) : EReal)) : EReal) := by
          rw [Pi.smul_apply, smul_eq_mul, hu_val]
        _ = ((((μ : ℝ) * fu : ℝ)) : EReal) := by
              rw [← EReal.coe_mul]
    have hineq_scaled' :
        ((inner ℝ (x - u) (y - u) : ℝ) : EReal) ≤
          ((((μ : ℝ) * fy - (μ : ℝ) * fu : ℝ)) : EReal) := by
      calc
        ((inner ℝ (x - u) (y - u) : ℝ) : EReal)
            ≤ (((μ : EReal) • f) y) - (((μ : EReal) • f) u) := hineq_scaled
        _ = ((((μ : ℝ) * fy : ℝ)) : EReal) - ((((μ : ℝ) * fu : ℝ)) : EReal) := by
              rw [hy_scaled_val, hu_scaled_val]
        _ = ((((μ : ℝ) * fy - (μ : ℝ) * fu : ℝ)) : EReal) := by
              rw [EReal.coe_sub]
    have hineq_real : inner ℝ (x - u) (y - u) ≤ (μ : ℝ) * fy - (μ : ℝ) * fu := by
      exact EReal.coe_le_coe_iff.mp hineq_scaled'
    have hineq_real' : fu + (μ : ℝ)⁻¹ * inner ℝ (x - u) (y - u) ≤ fy := by
      have hμpos : 0 < (μ : ℝ) := μ.2
      have hμ : (μ : ℝ) ≠ 0 := ne_of_gt hμpos
      have hstep : inner ℝ (x - u) (y - u) + (μ : ℝ) * fu ≤ (μ : ℝ) * fy := by
        nlinarith [hineq_real]
      have hmul :
          (μ : ℝ) * (fu + (μ : ℝ)⁻¹ * inner ℝ (x - u) (y - u)) ≤ (μ : ℝ) * fy := by
        calc
          (μ : ℝ) * (fu + (μ : ℝ)⁻¹ * inner ℝ (x - u) (y - u))
              = (μ : ℝ) * fu + inner ℝ (x - u) (y - u) := by
                  field_simp [hμ]
          _ = inner ℝ (x - u) (y - u) + (μ : ℝ) * fu := by
                ring
          _ ≤ (μ : ℝ) * fy := hstep
      exact le_of_mul_le_mul_left hmul hμpos
    rw [hy_val, hu_val]
    change ((fy : ℝ) : EReal) ≥ ((fu : ℝ) : EReal) +
      (((inner ℝ ((μ : ℝ)⁻¹ • (x - u)) (y - u) : ℝ)) : EReal)
    rw [real_inner_smul_left, ← EReal.coe_add]
    exact_mod_cast hineq_real'
  have hfenchel :
      (((toDualMap ℝ E ((μ : ℝ)⁻¹ • (x - u)) : StrongDual ℝ E) : Module.Dual ℝ E) u : EReal) =
        f u + conjugate_function f
          (((toDualMap ℝ E ((μ : ℝ)⁻¹ • (x - u)) : StrongDual ℝ E) : Module.Dual ℝ E)) := by
    -- Apply the Fenchel--Young equality criterion at the unscaled primal/dual pair.
    exact
      (pairing_eq_add_conjugate_iff_mem_subdifferential
        f hf_proper.ne_bot u
        (((toDualMap ℝ E ((μ : ℝ)⁻¹ • (x - u)) : StrongDual ℝ E) : Module.Dual ℝ E))).2 hmem
  have hinner_sub : inner ℝ u (x - u) = inner ℝ x u - ‖u‖ ^ (2 : ℕ) := by
    -- Expand the residual pairing into the textbook `⟪x, u⟫ - ‖u‖²` form.
    calc
      inner ℝ u (x - u) = inner ℝ u x - inner ℝ u u := by
        rw [inner_sub_right]
      _ = inner ℝ x u - ‖u‖ ^ (2 : ℕ) := by
            rw [real_inner_comm, real_inner_self_eq_norm_sq]
  have hinner :
      inner ℝ u ((μ : ℝ)⁻¹ • (x - u)) = (μ : ℝ)⁻¹ * (inner ℝ x u - ‖u‖ ^ (2 : ℕ)) := by
    rw [real_inner_smul_right, hinner_sub]
  simpa [conjugate_function_primal_apply, InnerProductSpace.toDualMap_apply_apply, hinner] using
    hfenchel.symm

/-- Helper for Theorem 6.67: the dual quadratic term at the residual point simplifies to the
scaled norm of `u`. -/
lemma dual_quadratic_term_eq_scaled_norm
    (μ : PosReal) (x u : E) :
    ((((1 / (2 * ((1 / μ : PosReal) : ℝ)) : ℝ) *
        ‖((μ : ℝ)⁻¹ • x) - ((μ : ℝ)⁻¹ • (x - u) )‖ ^ (2 : ℕ)) : ℝ) : EReal) =
      ((((1 / (2 * (μ : ℝ)) : ℝ) * ‖u‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  have hμ : (μ : ℝ) ≠ 0 := ne_of_gt μ.2
  have hdiff :
      ((μ : ℝ)⁻¹ • x) - ((μ : ℝ)⁻¹ • (x - u)) = (μ : ℝ)⁻¹ • u := by
    -- The dual residual difference is the scaled primal point `u`.
    rw [smul_sub]
    abel
  have hreal :
      (1 / (2 * ((1 / μ : PosReal) : ℝ)) : ℝ) *
          ‖((μ : ℝ)⁻¹ • x) - ((μ : ℝ)⁻¹ • (x - u))‖ ^ (2 : ℕ) =
        (1 / (2 * (μ : ℝ)) : ℝ) * ‖u‖ ^ (2 : ℕ) := by
    -- After rewriting the norm of a scalar multiple, the coefficient simplifies by field algebra.
    rw [hdiff, norm_smul]
    have hinv_pos : 0 < (μ : ℝ)⁻¹ := by
      exact inv_pos.mpr μ.2
    rw [Real.norm_of_nonneg (le_of_lt hinv_pos)]
    rw [show ((1 / μ : PosReal) : ℝ) = (μ : ℝ)⁻¹ by simp [one_div]]
    field_simp [hμ]
  exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hreal

-- Proof sketch: let `u` be the unique point with `prox[fun y ↦ (μ : EReal) * f y] x = {u}`,
-- supplied by Theorem 6.3. Then Theorem 6.45 identifies the companion proximal set
-- `prox[fun y ↦ (f∗) y / (μ : EReal)] ((μ : ℝ)⁻¹ • x)` with the singleton
-- `{(μ : ℝ)⁻¹ • (x - u)}`. Applying `moreau_envelope_eq_of_scaled_prox_eq_singleton` to `f` and
-- `f∗` evaluates both Moreau envelopes at these canonical minimizing points. The proximal
-- optimality conditions give the Fenchel--Young equality
-- `f u + (f∗) ((μ : ℝ)⁻¹ • (x - u)) = ⟪u, (μ : ℝ)⁻¹ • (x - u)⟫`, and simplifying the quadratic
-- terms yields exactly `ω(μ) x`.
/-- Theorem 6.67: Moreau envelope decomposition. For a proper closed convex extended-real-valued
function `f` on a finite-dimensional real inner product space and `μ > 0`, the Moreau envelope of
`f` at `x` plus the Moreau envelope of the conjugate `f∗`, evaluated at `μ⁻¹ • x`, equals the
chapter quadratic owner `ω(μ) x`. -/
theorem moreau_envelope_decomposition
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (μ : PosReal) (x : E) :
    M[μ, f] x + M[1 / μ, f∗] ((μ : ℝ)⁻¹ • x) = ω(μ) x := by
  rcases scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex μ with
    ⟨hscaled_proper, hscaled_closed, hscaled_convex⟩
  rcases prox_eq_singleton_of_proper_closed_convex (((μ : EReal) • f))
      hscaled_proper hscaled_closed hscaled_convex x with ⟨u, hprox⟩
  let q1 : ℝ := (1 / (2 * (μ : ℝ)) : ℝ) * ‖x - u‖ ^ (2 : ℕ)
  let q2 : ℝ := (1 / (2 * ((1 / μ : PosReal) : ℝ)) : ℝ) *
      ‖((μ : ℝ)⁻¹ • x) - ((μ : ℝ)⁻¹ • (x - u))‖ ^ (2 : ℕ)
  have hprimal : M[μ, f] x = f u + ((q1 : ℝ) : EReal) := by
    -- Evaluate the primal Moreau envelope at its unique proximal point.
    simpa [q1] using
      moreau_envelope_eq_of_scaled_prox_eq_singleton (f := f) (μ := μ) (x := x) (u := u) hprox
  have hdual_prox :
      prox[((((1 / μ : PosReal) : EReal) • (f∗)))] ((μ : ℝ)⁻¹ • x) =
        {((μ : ℝ)⁻¹ • (x - u))} :=
    dual_moreau_prox_eq_singleton f hf_proper hf_closed hf_convex μ x u hprox
  have hdual :
      M[1 / μ, f∗] ((μ : ℝ)⁻¹ • x) =
        (f∗) ((μ : ℝ)⁻¹ • (x - u)) + ((q2 : ℝ) : EReal) := by
    -- Evaluate the dual Moreau envelope at the transported residual singleton.
    simpa [q2] using
      moreau_envelope_eq_of_scaled_prox_eq_singleton (f := f∗) (μ := 1 / μ)
        (x := (μ : ℝ)⁻¹ • x) (u := (μ : ℝ)⁻¹ • (x - u)) hdual_prox
  have hfenchel :
      f u + (f∗) ((μ : ℝ)⁻¹ • (x - u)) =
        ((inner ℝ u ((μ : ℝ)⁻¹ • (x - u)) : ℝ) : EReal) :=
    fenchel_young_eq_of_scaled_prox_singleton f hf_proper hf_closed hf_convex μ x u hprox
  have hq2 :
      ((q2 : ℝ) : EReal) = (((1 / (2 * (μ : ℝ)) : ℝ) * ‖u‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    -- The transported dual quadratic penalty is the scaled norm-square of `u`.
    simpa [q2] using dual_quadratic_term_eq_scaled_norm (E := E) μ x u
  have hreal :
      inner ℝ u ((μ : ℝ)⁻¹ • (x - u)) + q1 + (1 / (2 * (μ : ℝ)) : ℝ) * ‖u‖ ^ (2 : ℕ) =
        (1 / (2 * (μ : ℝ)) : ℝ) * ‖x‖ ^ (2 : ℕ) := by
    have hμ : (μ : ℝ) ≠ 0 := ne_of_gt μ.2
    have hnorm :
        ‖x‖ ^ (2 : ℕ) = ‖x - u‖ ^ (2 : ℕ) + 2 * inner ℝ (x - u) u + ‖u‖ ^ (2 : ℕ) := by
      -- Rewrite `x` as residual plus proximal point, then expand the squared norm.
      calc
        ‖x‖ ^ (2 : ℕ) = ‖(x - u) + u‖ ^ (2 : ℕ) := by
          congr 1
          abel
        _ = ‖x - u‖ ^ (2 : ℕ) + 2 * inner ℝ (x - u) u + ‖u‖ ^ (2 : ℕ) := by
              rw [norm_add_sq_real]
    have hinner :
        inner ℝ u ((μ : ℝ)⁻¹ • (x - u)) = (μ : ℝ)⁻¹ * inner ℝ (x - u) u := by
      rw [real_inner_smul_right, real_inner_comm]
    have hscaled := congrArg (fun t : ℝ ↦ (1 / (2 * (μ : ℝ)) : ℝ) * t) hnorm
    -- Scale the norm expansion by `1 / (2μ)` and match the cross term with the inner product.
    rw [hinner]
    simp [q1]
    have hscaled' :
        (1 / (2 * (μ : ℝ)) : ℝ) * ‖x‖ ^ (2 : ℕ) =
          (1 / (2 * (μ : ℝ)) : ℝ) * ‖x - u‖ ^ (2 : ℕ) +
            (1 / (2 * (μ : ℝ)) : ℝ) * (2 * inner ℝ (x - u) u) +
            (1 / (2 * (μ : ℝ)) : ℝ) * ‖u‖ ^ (2 : ℕ) := by
      simpa [mul_add, add_mul, add_assoc] using hscaled
    have hcross :
        (μ : ℝ)⁻¹ * inner ℝ (x - u) u =
          (1 / (2 * (μ : ℝ)) : ℝ) * (2 * inner ℝ (x - u) u) := by
      field_simp [hμ]
    rw [hcross]
    simpa [add_assoc, add_left_comm, add_comm] using hscaled'.symm
  -- Substitute the two envelope evaluations, apply Fenchel--Young, and fold the remaining
  -- finite real expression back into the owner quadratic term `ω(μ) x`.
  calc
    M[μ, f] x + M[1 / μ, f∗] ((μ : ℝ)⁻¹ • x)
        = (f u + ((q1 : ℝ) : EReal)) +
            ((f∗) ((μ : ℝ)⁻¹ • (x - u)) + ((q2 : ℝ) : EReal)) := by
              rw [hprimal, hdual]
    _ = (f u + (f∗) ((μ : ℝ)⁻¹ • (x - u))) + (((q1 : ℝ) : EReal) + ((q2 : ℝ) : EReal)) := by
          simp [add_assoc, add_left_comm, add_comm]
    _ = ((inner ℝ u ((μ : ℝ)⁻¹ • (x - u)) : ℝ) : EReal) +
          (((q1 : ℝ) : EReal) + ((q2 : ℝ) : EReal)) := by
            rw [hfenchel]
    _ = ((inner ℝ u ((μ : ℝ)⁻¹ • (x - u)) : ℝ) : EReal) +
          (((q1 + (1 / (2 * (μ : ℝ)) : ℝ) * ‖u‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
            rw [hq2, ← EReal.coe_add]
    _ = (((inner ℝ u ((μ : ℝ)⁻¹ • (x - u)) + q1 +
          (1 / (2 * (μ : ℝ)) : ℝ) * ‖u‖ ^ (2 : ℕ) : ℝ) : ℝ) : EReal) := by
            rw [← EReal.coe_add]
            congr 1
            ring
    _ = (((1 / (2 * (μ : ℝ)) : ℝ) * ‖x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
          exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hreal
    _ = ω(μ) x := by
          rw [moreau_quadratic_kernel_apply]

end
