/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped InnerProduct Pointwise

section

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/- Theorem 6.15 is `bridge/view` in the Chapter 6 proximal-mapping API. Domain sampling in the
minimal closure identifies the owner split:

- `prox[...]` from Definition 6.1 is the `core/canonical` proximal owner;
- `IsProperExtendedRealFunction` from Definition 2.5 is the project owner for the semantically
  relevant effective-domain and no-`⊥` data on extended-real objectives;
- Theorems 6.11 and 6.12 already handle the lower-level scaling and translation transports;
- `ContinuousAffineMap.contLinear` together with `ContinuousLinearMap.adjoint` is the canonical
  mathlib owner surface for the linear part of an affine map and its adjoint.

The primitive data are therefore the objective `g`, its properness witness, the continuous affine
map `φ`, the scalar `α`, the positivity hypothesis on `α`, the isotropy hypothesis on
`φ.contLinear`, and the evaluation point `x`. The translation term is derived from `φ` itself, so
the public statement should not repackage `φ` as separate raw data `(A, b)`. The review
counterexample `g ≡ ⊤` also shows that the nonempty-effective-domain half of properness is
semantically active here, so the theorem should reuse the canonical properness owner instead of a
local no-`⊥` fragment. -/

-- Proof sketch: write the proximal problem for `u ↦ g (φ u)` using the affine variable
-- `z = φ u`. The identity `φ.contLinear ∘L φ.contLinear† = α • 1` gives the affine
-- reconstruction `u = x + α⁻¹ • φ.contLinear† (z - φ x)`, and the quadratic term becomes the
-- proximal objective for `z ↦ α g z` at `φ x`. Properness supplies both the no-`⊥` condition and
-- a finite point in the effective domain, ruling out the degenerate `g ≡ ⊤` case that would make
-- the pulled-back proximal set too large. Transporting minimizers through this affine formula
-- yields the set equality.
/-- Helper for Theorem 6.15: the affine correction is a right inverse for `φ` on the codomain. -/
lemma affine_correction_apply
    (φ : V →ᴬ[ℝ] W) (α : ℝ) (hα : 0 < α)
    (hφ : φ.contLinear ∘L φ.contLinear† = α • 1) (x : V) (z : W) :
    φ (x + (α⁻¹ • φ.contLinear†) (z - φ x)) = z := by
  let c : V := (α⁻¹ • φ.contLinear†) (z - φ x)
  -- Evaluate the isotropy hypothesis on the displacement `z - φ x`.
  have happly : (φ.contLinear ∘L φ.contLinear†) (z - φ x) = α • (z - φ x) := by
    exact congrArg (fun T : W →L[ℝ] W => T (z - φ x)) hφ
  -- Rewrite `φ` on the affine section and then collapse the correction with `A A† = α I`.
  calc
    φ (x + c) = φ (c + x) := by rw [add_comm]
    _ = φ.contLinear c + φ x := by
          simpa [c] using φ.map_vadd x c
    _ = α⁻¹ • ((φ.contLinear ∘L φ.contLinear†) (z - φ x)) + φ x := by
          simp [c, ContinuousLinearMap.comp_apply]
    _ = α⁻¹ • (α • (z - φ x)) + φ x := by rw [happly]
    _ = (z - φ x) + φ x := by rw [inv_smul_smul₀ hα.ne']
    _ = z := sub_add_cancel z (φ x)

/-- Helper for Theorem 6.15: the adjoint correction rescales squared norms by `α⁻¹`. -/
lemma adjoint_correction_norm_sq
    (φ : V →ᴬ[ℝ] W) (α : ℝ) (hα : 0 < α)
    (hφ : φ.contLinear ∘L φ.contLinear† = α • 1) (y : W) :
    ‖((α⁻¹ • φ.contLinear†) y)‖ ^ (2 : ℕ) = α⁻¹ * ‖y‖ ^ (2 : ℕ) := by
  let c : V := (((α⁻¹ : ℝ) • φ.contLinear†) y)
  -- Evaluate the isotropy identity on the chosen codomain vector.
  have happly : (φ.contLinear ∘L φ.contLinear†) y = α • y := by
    exact congrArg (fun T : W →L[ℝ] W => T y) hφ
  -- Convert the squared norm into an inner product and move the adjoint across.
  calc
    ‖((α⁻¹ • φ.contLinear†) y)‖ ^ (2 : ℕ) = ‖c‖ ^ (2 : ℕ) := by simp [c]
    _ = inner ℝ c c := by rw [real_inner_self_eq_norm_sq]
    _ = inner ℝ (((α⁻¹ : ℝ) • ((φ.contLinear†) y))) (((α⁻¹ : ℝ) • ((φ.contLinear†) y))) := by
          simp [c, ContinuousLinearMap.smul_apply]
    _ = α⁻¹ * inner ℝ y y := by
          rw [real_inner_smul_left, real_inner_smul_right, ContinuousLinearMap.adjoint_inner_left]
          rw [show φ.contLinear ((φ.contLinear†) y) = α • y by
                simpa [ContinuousLinearMap.comp_apply] using happly]
          rw [real_inner_smul_right]
          field_simp [hα.ne']
    _ = α⁻¹ * ‖y‖ ^ (2 : ℕ) := by rw [real_inner_self_eq_norm_sq]

/-- Helper for Theorem 6.15: each affine fiber splits orthogonally into the canonical adjoint
correction and a kernel residual. -/
lemma affine_fiber_norm_sq_split
    (φ : V →ᴬ[ℝ] W) (α : ℝ) (hα : 0 < α)
    (hφ : φ.contLinear ∘L φ.contLinear† = α • 1) (x u : V) :
    ‖u - x‖ ^ (2 : ℕ) =
      ‖((α⁻¹ • φ.contLinear†) (φ u - φ x))‖ ^ (2 : ℕ) +
        ‖u - x - ((α⁻¹ • φ.contLinear†) (φ u - φ x))‖ ^ (2 : ℕ) := by
  let c : V := (((α⁻¹ • φ.contLinear†) (φ u - φ x)))
  let r : V := u - x - c
  have hcorrection :
      φ.contLinear c = φ u - φ x := by
    -- The correction part is the canonical section of the affine fiber.
    have happly : (φ.contLinear ∘L φ.contLinear†) (φ u - φ x) = α • (φ u - φ x) := by
      exact congrArg (fun T : W →L[ℝ] W => T (φ u - φ x)) hφ
    calc
      φ.contLinear c
          = α⁻¹ • ((φ.contLinear ∘L φ.contLinear†) (φ u - φ x)) := by
              simp [c, ContinuousLinearMap.comp_apply]
      _ = α⁻¹ • (α • (φ u - φ x)) := by rw [happly]
      _ = φ u - φ x := by rw [inv_smul_smul₀ hα.ne']
  have hr_ker : φ.contLinear r = 0 := by
    -- The residual lies in the kernel of the linear part of `φ`.
    calc
      φ.contLinear r
          = φ.contLinear (u - x) - φ.contLinear c := by
              simp [r, map_sub]
      _ = (φ u - φ x) - (φ u - φ x) := by
            rw [show φ.contLinear (u - x) = φ u - φ x by simpa using φ.linearMap_vsub u x]
            rw [hcorrection]
      _ = 0 := sub_self (φ u - φ x)
  have horth : inner ℝ c r = 0 := by
    -- Orthogonality comes from moving the adjoint onto a kernel vector.
    calc
      inner ℝ c r
          = α⁻¹ * inner ℝ ((φ.contLinear†) (φ u - φ x)) r := by
              simp [c, real_inner_smul_left]
      _ = α⁻¹ * inner ℝ (φ u - φ x) (φ.contLinear r) := by
            rw [ContinuousLinearMap.adjoint_inner_left]
      _ = 0 := by rw [hr_ker]; simp
  have hdecomp : u - x = c + r := by
    -- This is the defining decomposition of the affine fiber.
    simp [r, c, sub_eq_add_neg, add_assoc, add_left_comm]
  -- Apply the real Pythagorean identity to the orthogonal decomposition.
  calc
    ‖u - x‖ ^ (2 : ℕ) = ‖c + r‖ ^ (2 : ℕ) := by rw [hdecomp]
    _ = ‖c‖ ^ (2 : ℕ) + 2 * inner ℝ c r + ‖r‖ ^ (2 : ℕ) :=
            norm_add_sq_real _ _
    _ = ‖c‖ ^ (2 : ℕ) + ‖r‖ ^ (2 : ℕ) := by simp [horth]
    _ = ‖((α⁻¹ • φ.contLinear†) (φ u - φ x))‖ ^ (2 : ℕ) +
          ‖u - x - ((α⁻¹ • φ.contLinear†) (φ u - φ x))‖ ^ (2 : ℕ) := by
            simp [c, r]

/-- Helper for Theorem 6.15: the codomain quadratic term is `α` times the pullback quadratic term
on the canonical affine section. -/
lemma scaled_quadratic_on_affine_correction
    (φ : V →ᴬ[ℝ] W) (α : ℝ) (hα : 0 < α)
    (hφ : φ.contLinear ∘L φ.contLinear† = α • 1) (x : V) (z : W) :
    ((((1 / 2 : ℝ) * ‖z - φ x‖ ^ (2 : ℕ)) : ℝ) : EReal) =
      (α : EReal) *
        (((((1 / 2 : ℝ) * ‖(α⁻¹ • φ.contLinear†) (z - φ x)‖ ^ (2 : ℕ)) : ℝ)) : EReal) := by
  -- Convert the real quadratic identity for the adjoint correction into the `EReal` scaling form.
  have hreal :
      ((1 / 2 : ℝ) * ‖z - φ x‖ ^ (2 : ℕ)) =
        α * ((1 / 2 : ℝ) * ‖(α⁻¹ • φ.contLinear†) (z - φ x)‖ ^ (2 : ℕ)) := by
    rw [adjoint_correction_norm_sq φ α hα hφ (z - φ x)]
    field_simp [hα.ne']
  calc
    ((((1 / 2 : ℝ) * ‖z - φ x‖ ^ (2 : ℕ)) : ℝ) : EReal)
        = (((α * ((1 / 2 : ℝ) * ‖(α⁻¹ • φ.contLinear†) (z - φ x)‖ ^ (2 : ℕ)) : ℝ)) : EReal) := by
            exact_mod_cast hreal
    _ = (α : EReal) *
          (((((1 / 2 : ℝ) * ‖(α⁻¹ • φ.contLinear†) (z - φ x)‖ ^ (2 : ℕ)) : ℝ)) : EReal) := by
            rw [EReal.coe_mul]

/-- Helper for Theorem 6.15: on the canonical affine section, the codomain proximal objective is
exactly `α` times the pullback proximal objective. -/
lemma scaled_objective_on_correction
    (g : W → EReal) (φ : V →ᴬ[ℝ] W) (α : ℝ) (hα : 0 < α)
    (hφ : φ.contLinear ∘L φ.contLinear† = α • 1) (x : V) (z : W) :
    proximal_objective ((α : EReal) • g) (φ x) z =
      (α : EReal) * proximal_objective (g ∘ φ) x
        (x + (α⁻¹ • φ.contLinear†) (z - φ x)) := by
  have hs_nonneg : 0 ≤ (α : EReal) := by
    exact_mod_cast hα.le
  have hs_top : (α : EReal) ≠ ⊤ := EReal.coe_ne_top _
  -- Expand both proximal objectives, then factor out the common positive scalar `α`.
  calc
    proximal_objective ((α : EReal) • g) (φ x) z
        = (α : EReal) * g z +
            ((((1 / 2 : ℝ) * ‖z - φ x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
            simp [proximal_objective]
    _ = (α : EReal) * g z +
          (α : EReal) *
            (((((1 / 2 : ℝ) * ‖(α⁻¹ • φ.contLinear†) (z - φ x)‖ ^ (2 : ℕ)) : ℝ)) : EReal) := by
            rw [scaled_quadratic_on_affine_correction φ α hα hφ x z]
    _ = (α : EReal) *
          (g z +
            (((((1 / 2 : ℝ) * ‖(α⁻¹ • φ.contLinear†) (z - φ x)‖ ^ (2 : ℕ)) : ℝ)) : EReal)) := by
            rw [EReal.left_distrib_of_nonneg_of_ne_top hs_nonneg hs_top]
    _ = (α : EReal) * proximal_objective (g ∘ φ) x
          (x + (α⁻¹ • φ.contLinear†) (z - φ x)) := by
            have hsection :
                g z +
                  (((((1 / 2 : ℝ) * ‖(α⁻¹ • φ.contLinear†) (z - φ x)‖ ^ (2 : ℕ)) : ℝ)) : EReal) =
                  proximal_objective (g ∘ φ) x
                    (x + (α⁻¹ • φ.contLinear†) (z - φ x)) := by
              rw [proximal_objective_apply, Function.comp,
                affine_correction_apply φ α hα hφ x z]
              simp
            exact congrArg (fun t : EReal ↦ (α : EReal) * t) hsection

/-- Helper for Theorem 6.15: along any affine fiber, the scaled codomain objective is bounded above
by the pulled-back objective. -/
lemma scaled_objective_le_along_fiber
    (g : W → EReal) (φ : V →ᴬ[ℝ] W) (α : ℝ) (hα : 0 < α)
    (hφ : φ.contLinear ∘L φ.contLinear† = α • 1) (x u : V) :
    proximal_objective ((α : EReal) • g) (φ x) (φ u) ≤
      (α : EReal) * proximal_objective (g ∘ φ) x u := by
  have hs_nonneg : 0 ≤ (α : EReal) := by
    exact_mod_cast hα.le
  have hs_top : (α : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hquad_real :
      ((1 / 2 : ℝ) * ‖φ u - φ x‖ ^ (2 : ℕ)) ≤
        α * ((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) := by
    -- The fiber decomposition shows that the missing residual square is nonnegative.
    have hsplit := affine_fiber_norm_sq_split φ α hα hφ x u
    have hadj := adjoint_correction_norm_sq φ α hα hφ (φ u - φ x)
    have hres_nonneg :
        0 ≤ ‖u - x - ((α⁻¹ • φ.contLinear†) (φ u - φ x))‖ ^ (2 : ℕ) := by
      positivity
    have hbase :
        α⁻¹ * ‖φ u - φ x‖ ^ (2 : ℕ) ≤ ‖u - x‖ ^ (2 : ℕ) := by
      rw [hadj] at hsplit
      nlinarith
    have hsq_le : ‖φ u - φ x‖ ^ (2 : ℕ) ≤ α * ‖u - x‖ ^ (2 : ℕ) := by
      calc
        ‖φ u - φ x‖ ^ (2 : ℕ)
            = α * (α⁻¹ * ‖φ u - φ x‖ ^ (2 : ℕ)) := by
                field_simp [hα.ne']
        _ ≤ α * ‖u - x‖ ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hbase hα.le
    have hhalf :
        (1 / 2 : ℝ) * ‖φ u - φ x‖ ^ (2 : ℕ) ≤
          (1 / 2 : ℝ) * (α * ‖u - x‖ ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hsq_le (by positivity)
    calc
      (1 / 2 : ℝ) * ‖φ u - φ x‖ ^ (2 : ℕ)
          ≤ (1 / 2 : ℝ) * (α * ‖u - x‖ ^ (2 : ℕ)) := hhalf
      _ = α * ((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) := by ring
  have hquad :
      ((((1 / 2 : ℝ) * ‖φ u - φ x‖ ^ (2 : ℕ)) : ℝ) : EReal) ≤
        (α : EReal) * (((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ)) : EReal) := by
    have hquad' :
        ((((1 / 2 : ℝ) * ‖φ u - φ x‖ ^ (2 : ℕ)) : ℝ) : EReal) ≤
          (((α * ((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ)) : EReal) := by
      exact_mod_cast hquad_real
    simpa [EReal.coe_mul] using hquad'
  -- Compare the codomain quadratic term with the pullback quadratic term on the same fiber.
  calc
    proximal_objective ((α : EReal) • g) (φ x) (φ u)
        = (α : EReal) * g (φ u) +
            ((((1 / 2 : ℝ) * ‖φ u - φ x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
            simp [proximal_objective]
    _ ≤ (α : EReal) * g (φ u) +
          (α : EReal) * (((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ)) : EReal) := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_left hquad ((α : EReal) * g (φ u))
    _ = (α : EReal) *
          (g (φ u) + (((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ)) : EReal)) := by
            rw [EReal.left_distrib_of_nonneg_of_ne_top hs_nonneg hs_top]
    _ = (α : EReal) * proximal_objective (g ∘ φ) x u := by
            simp [proximal_objective]

/-- Helper for Theorem 6.15: a pullback proximal minimizer maps to a proximal minimizer of the
scaled codomain objective. -/
lemma pullback_minimizer_maps_to_scaled_minimizer
    (g : W → EReal) (φ : V →ᴬ[ℝ] W) (α : ℝ) (hα : 0 < α)
    (hφ : φ.contLinear ∘L φ.contLinear† = α • 1) (x u : V)
    (hu : u ∈ prox[g ∘ φ] x) :
    φ u ∈ prox[(α : EReal) • g] (φ x) := by
  let T : W → V := fun z ↦ x + (α⁻¹ • φ.contLinear†) (z - φ x)
  have hs_nonneg : 0 ≤ (α : EReal) := by
    exact_mod_cast hα.le
  rw [mem_proximal_mapping_iff] at hu ⊢
  rw [isMinOn_univ_iff] at hu ⊢
  intro z
  have huz :
      proximal_objective (g ∘ φ) x u ≤ proximal_objective (g ∘ φ) x (T z) := hu (T z)
  have hscaled :
      (α : EReal) * proximal_objective (g ∘ φ) x u ≤
        (α : EReal) * proximal_objective (g ∘ φ) x (T z) :=
    mul_le_mul_of_nonneg_left huz hs_nonneg
  -- Compare the pullback minimizer with the canonical affine section of the codomain candidate.
  calc
    proximal_objective ((α : EReal) • g) (φ x) (φ u)
        ≤ (α : EReal) * proximal_objective (g ∘ φ) x u :=
          scaled_objective_le_along_fiber g φ α hα hφ x u
    _ ≤ (α : EReal) * proximal_objective (g ∘ φ) x (T z) := hscaled
    _ = proximal_objective ((α : EReal) • g) (φ x) z := by
          simpa [T] using (scaled_objective_on_correction g φ α hα hφ x z).symm

/-- Helper for Theorem 6.15: a pullback proximal minimizer coincides with the canonical affine
section over its image `φ u`. -/
lemma pullback_minimizer_eq_affine_correction
    (g : W → EReal) (hg_proper : IsProperExtendedRealFunction g)
    (φ : V →ᴬ[ℝ] W) (α : ℝ) (hα : 0 < α)
    (hφ : φ.contLinear ∘L φ.contLinear† = α • 1) (x u : V)
    (hu : u ∈ prox[g ∘ φ] x) :
    u = x + (α⁻¹ • φ.contLinear†) (φ u - φ x) := by
  let T : W → V := fun z ↦ x + (α⁻¹ • φ.contLinear†) (z - φ x)
  rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
  rcases hg_proper.effective_domain_nonempty with ⟨z₀, hz₀_eff⟩
  have hz₀_top : g z₀ ≠ ⊤ := (mem_effective_domain.mp hz₀_eff).ne
  have hφTz₀ : φ (T z₀) = z₀ := by
    simpa [T] using affine_correction_apply φ α hα hφ x z₀
  have hobj_Tz₀_top : proximal_objective (g ∘ φ) x (T z₀) ≠ ⊤ := by
    -- Properness gives a finite competitor on the same affine section.
    intro htop
    have hfinite :
        g z₀ + ((((1 / 2 : ℝ) * ‖T z₀ - x‖ ^ (2 : ℕ)) : ℝ) : EReal) ≠ ⊤ :=
      EReal.add_ne_top hz₀_top (EReal.coe_ne_top _)
    exact hfinite (by
      simpa [proximal_objective_apply, hφTz₀] using htop)
  have hgu_top : g (φ u) ≠ ⊤ := by
    -- A minimizer cannot have value `⊤` below a finite competitor.
    intro hgu_top
    have hcompare₀ :
        proximal_objective (g ∘ φ) x u ≤ proximal_objective (g ∘ φ) x (T z₀) := hu (T z₀)
    have htop_le : (⊤ : EReal) ≤ proximal_objective (g ∘ φ) x (T z₀) := by
      have htop_eq : proximal_objective (g ∘ φ) x u = ⊤ := by
        calc
          proximal_objective (g ∘ φ) x u
              = g (φ u) + ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
                  simp [proximal_objective_apply]
          _ = ⊤ := by rw [hgu_top, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      calc
        (⊤ : EReal) = proximal_objective (g ∘ φ) x u := htop_eq.symm
        _ ≤ proximal_objective (g ∘ φ) x (T z₀) := hcompare₀
    exact hobj_Tz₀_top (top_le_iff.mp htop_le)
  let Tu : V := T (φ u)
  have hφTu : φ Tu = φ u := by
    -- The canonical affine section lands back in the same affine fiber.
    simpa [Tu, T] using affine_correction_apply φ α hα hφ x (φ u)
  have hcompare : proximal_objective (g ∘ φ) x u ≤ proximal_objective (g ∘ φ) x Tu := hu Tu
  have hcompare_real :
      (g (φ u)).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) ≤
        (g (φ u)).toReal + (1 / 2 : ℝ) * ‖Tu - x‖ ^ (2 : ℕ) := by
    -- After ruling out `⊤`, convert the shared `g (φ u)` term to reals and cancel it.
    exact EReal.coe_le_coe_iff.mp <| by
      simpa [proximal_objective_apply, hφTu, EReal.coe_add,
        EReal.coe_toReal hgu_top (hg_proper.ne_bot (φ u))] using hcompare
  have hsq_le : ‖u - x‖ ^ (2 : ℕ) ≤ ‖Tu - x‖ ^ (2 : ℕ) := by
    nlinarith
  have hsplit :
      ‖u - x‖ ^ (2 : ℕ) = ‖Tu - x‖ ^ (2 : ℕ) + ‖u - Tu‖ ^ (2 : ℕ) := by
    -- The fiber decomposition isolates the residual away from the canonical section.
    have hTu_sub : Tu - x = (α⁻¹ • φ.contLinear†) (φ u - φ x) := by
      simp [Tu, T]
    have huTu_sub :
        u - x - (Tu - x) = u - Tu := by
      abel_nf
    calc
      ‖u - x‖ ^ (2 : ℕ)
          = ‖((α⁻¹ • φ.contLinear†) (φ u - φ x))‖ ^ (2 : ℕ) +
              ‖u - x - ((α⁻¹ • φ.contLinear†) (φ u - φ x))‖ ^ (2 : ℕ) :=
            affine_fiber_norm_sq_split φ α hα hφ x u
      _ = ‖Tu - x‖ ^ (2 : ℕ) + ‖u - Tu‖ ^ (2 : ℕ) := by
            rw [← hTu_sub, huTu_sub]
  have hres_zero : ‖u - Tu‖ ^ (2 : ℕ) = 0 := by
    nlinarith [hsplit, hsq_le]
  have hnorm_zero : ‖u - Tu‖ = 0 := eq_zero_of_pow_eq_zero hres_zero
  have hu_eq_Tu : u = Tu := sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
  simpa [Tu, T] using hu_eq_Tu

/-- Theorem 6.15: composition with a continuous affine mapping. For `f = g ∘ φ`, if
`φ.contLinear ∘L φ.contLinear† = α • 1` with `α > 0`, then the proximal set of `f` at `x` is the
image of the proximal set of `(α : EReal) • g` at `φ x` under the affine correction
`z ↦ x + α⁻¹ • φ.contLinear† (z - φ x)`.
This is the chapter's set-valued formulation of the textbook proximal-point identity. For this
bare minimizer-set equality, the semantically active hypothesis on `g` is properness: `g` must
avoid `⊥` and have nonempty effective domain, excluding the degenerate `g ≡ ⊤` case. The stronger
closedness and convexity parts of the textbook assumptions are still not used at this transport
level. -/
theorem proximal_mapping_precompose_continuousAffineMap
    (g : W → EReal) (hg_proper : IsProperExtendedRealFunction g)
    (φ : V →ᴬ[ℝ] W) (α : ℝ) (hα : 0 < α)
    (hφ : φ.contLinear ∘L φ.contLinear† = α • 1) (x : V) :
    prox[g ∘ φ] x =
      (fun z ↦ x + (α⁻¹ • φ.contLinear†) (z - φ x)) ''
        prox[(α : EReal) • g] (φ x) := by
  let T : W → V := fun z ↦ x + (α⁻¹ • φ.contLinear†) (z - φ x)
  have hs_nonneg : 0 ≤ (α : EReal) := by
    exact_mod_cast hα.le
  have hs_top : (α : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hs_bot : (α : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hs_zero : (α : EReal) ≠ 0 := by
    exact_mod_cast hα.ne'
  ext u
  constructor
  · intro hu
    rw [Set.mem_image]
    refine ⟨φ u, pullback_minimizer_maps_to_scaled_minimizer g φ α hα hφ x u hu, ?_⟩
    -- A pullback minimizer is the canonical affine correction of its image.
    simpa [T] using (pullback_minimizer_eq_affine_correction g hg_proper φ α hα hφ x u hu).symm
  · rintro ⟨z, hz, rfl⟩
    rw [mem_proximal_mapping_iff] at hz ⊢
    rw [isMinOn_univ_iff] at hz ⊢
    intro v
    have hscaled :
        (α : EReal) * proximal_objective (g ∘ φ) x (T z) ≤
          (α : EReal) * proximal_objective (g ∘ φ) x v := by
      -- Route correction: prove the codomain-to-domain transport by scaling once in `EReal`
      -- and only then dividing by the positive scalar `α`.
      calc
        (α : EReal) * proximal_objective (g ∘ φ) x (T z)
            = proximal_objective ((α : EReal) • g) (φ x) z := by
                simpa [T] using (scaled_objective_on_correction g φ α hα hφ x z).symm
        _ ≤ proximal_objective ((α : EReal) • g) (φ x) (φ v) := hz (φ v)
        _ ≤ (α : EReal) * proximal_objective (g ∘ φ) x v :=
              scaled_objective_le_along_fiber g φ α hα hφ x v
    have hdiv :
        ((α : EReal) * proximal_objective (g ∘ φ) x (T z)) / (α : EReal) ≤
          ((α : EReal) * proximal_objective (g ∘ φ) x v) / (α : EReal) :=
      EReal.monotone_div_right_of_nonneg hs_nonneg hscaled
    rw [mul_comm (α : EReal) (proximal_objective (g ∘ φ) x (T z)),
      mul_comm (α : EReal) (proximal_objective (g ∘ φ) x v),
      ← EReal.mul_div_right,
      ← EReal.mul_div_right,
      EReal.div_mul_cancel hs_bot hs_top hs_zero,
      EReal.div_mul_cancel hs_bot hs_top hs_zero] at hdiv
    simpa [T] using hdiv

end
