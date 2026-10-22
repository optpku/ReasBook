/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_57
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_63

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Pointwise
open AffineMap

/- Corollary 6.64 is `source-facing`: the chapter already owns the Moreau envelope `M[μ, f]`, the
set-valued proximal mapping `prox[...]`, and Theorem 6.63's singleton formula for the proximal set
of a Moreau envelope. Domain sampling against Definition 6.7, Lemma 6.57, Theorem 6.3, and
Theorem 6.63 shows that the primitive owner data here are `f`, `μ`, `λ`, the base point `x`, and
the proper/closed/convex hypotheses ensuring that the scaled proximal point of `((μ + λ) • f)` is
attained. The singleton formula conditioned on a precomputed scaled proximal singleton is derived
bridge API; the false bare image-set identity under only `hf_ne_bot` should not remain public. -/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- Helper for Corollary 6.64: after scaling `f` by `λ`, the `(μ / λ + 1)`-scaled function is
exactly the original function scaled by `μ + λ`. -/
lemma scaled_scaled_function_eq_sum_scale (f : E → EReal) (μ lam : PosReal) :
    (((((μ : ℝ) / (lam : ℝ) + 1 : ℝ) : EReal) • ((lam : EReal) • f)) : E → EReal) =
      ((((μ + lam : ℝ) : EReal) • f) : E → EReal) := by
  ext y
  -- Expand the two pointwise scalar multiplications and compare the real coefficients.
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← EReal.coe_mul]
  congr 1
  field_simp [show (lam : ℝ) ≠ 0 by exact (PosReal.coe_pos lam).ne']

/-- Helper for Corollary 6.64: the affine weight from Theorem 6.63 simplifies to the textbook
coefficient `λ / (μ + λ)`. -/
lemma moreau_weight_div_eq (μ lam : PosReal) :
    (((μ : ℝ) / (lam : ℝ) + 1 : ℝ))⁻¹ = (lam : ℝ) / (μ + lam : ℝ) := by
  -- Reduce the weight identity to a scalar calculation in `ℝ`.
  field_simp [show (lam : ℝ) ≠ 0 by exact (PosReal.coe_pos lam).ne',
    show (μ + lam : ℝ) ≠ 0 by exact (add_pos (PosReal.coe_pos μ) (PosReal.coe_pos lam)).ne']

/-- Helper for Corollary 6.64: scaling the Moreau envelope owner by `λ` rewrites the proximal set
to the proximal set of the correspondingly rescaled Moreau envelope. -/
lemma scaled_moreau_prox_owner_rewrite (f : E → EReal) (μ lam : PosReal) (x : E) :
    prox[(lam : EReal) • M[μ, f]] x = prox[M[μ / lam, (lam : EReal) • f]] x := by
  -- Transport the owner equality from Lemma 6.57 through the proximal-set owner.
  simpa using
    congrArg (fun g : E → EReal ↦ prox[g] x)
      (smul_moreau_envelope_eq_moreau_envelope_scaled_function (E := E) f μ lam)

-- Proof sketch: rewrite `(lam : EReal) • M[μ, f]` as `M[μ / lam, (lam : EReal) • f]` using
-- Lemma 6.57. Apply Theorem 6.63 to the proper closed convex function `(lam : EReal) • f` and the
-- positive parameter `μ / lam`. The resulting scaled proximal singleton is exactly the singleton
-- proximal set of `(((μ + lam : ℝ) : EReal) • f)` at `x`, and the line-map weight simplifies to
-- `lam / (μ + lam)`.
/-- Corollary 6.64: if `f` is a proper closed convex extended-real-valued function and `μ, λ > 0`,
then at every point `x` there is a unique proximal point `u` of the scaled function `(μ + λ) f`,
and the proximal set of the scaled Moreau envelope `λ M[μ, f]` at `x` is the singleton containing
`lineMap x u (λ / (μ + λ))`. This is the chapter's set-valued rendering of the textbook formula
`prox_{λ M_f^μ}(x) = x + (λ / (μ + λ)) (prox_{(μ + λ) f}(x) - x)`. -/
theorem prox_scaled_moreau_envelope_eq_singleton_of_proper_closed_convex
    (f : E → EReal) (μ lam : PosReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) (x : E) :
    ∃ u : E,
      prox[(((μ + lam : ℝ) : EReal) • f)] x = {u} ∧
      prox[(lam : EReal) • M[μ, f]] x =
        {lineMap x u ((lam : ℝ) / (μ + lam : ℝ))} := by
  let ν : PosReal := μ / lam
  let g : E → EReal := (lam : EReal) • f
  -- First move to the scaled Moreau-envelope problem governed by Theorem 6.63.
  rcases scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam with
    ⟨hg_proper, hg_closed, hg_convex⟩
  rcases
      prox_moreau_envelope_eq_singleton_of_proper_closed_convex
        (E := E) (f := g) (μ := ν) hg_proper hg_closed hg_convex x with
    ⟨u, hscaled_prox, hscaled_moreau⟩
  have hscaled_owner :
      (((((ν + 1 : PosReal) : ℝ) : EReal) • g) : E → EReal) =
        ((((μ + lam : ℝ) : EReal) • f) : E → EReal) := by
    -- This is the scalar normalization matching Theorem 6.63's input to the corollary's input.
    simpa [ν, g] using scaled_scaled_function_eq_sum_scale (E := E) (f := f) (μ := μ) (lam := lam)
  have hprox :
      prox[(((μ + lam : ℝ) : EReal) • f)] x = {u} := by
    -- Rewrite the scaled proximal singleton produced by Theorem 6.63 to the textbook scale.
    rw [← hscaled_owner]
    exact hscaled_prox
  have howner :
      prox[(lam : EReal) • M[μ, f]] x = prox[M[ν, g]] x := by
    -- Lemma 6.57 provides the owner-level Moreau-envelope scaling identity.
    simpa [ν, g] using scaled_moreau_prox_owner_rewrite (E := E) (f := f) (μ := μ) (lam := lam) x
  refine ⟨u, hprox, ?_⟩
  -- Combine the owner rewrite with Theorem 6.63's singleton formula and simplify the weight.
  rw [howner]
  simpa [ν, g, moreau_weight_div_eq (μ := μ) (lam := lam)] using hscaled_moreau

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

-- Proof sketch: rewrite the scaled envelope `λ • M[μ, f]` as
-- `M[μ / λ, (lam : EReal) • f]` using Lemma 6.57. Then apply
-- `prox_moreau_envelope_eq_singleton_of_scaled_prox_eq_singleton` with smoothing parameter
-- `μ / lam`. The affine weight `1 / (μ / lam + 1)` simplifies to `lam / (μ + lam)` and the
-- scaled function `(μ / lam + 1) • (lam • f)` simplifies pointwise to `(μ + lam) • f`.
/-- If the proximal set of the scaled function `(μ + λ) f` at `x` is the singleton `{u}`, then
the proximal set of the scaled Moreau envelope `λ M[μ, f]` at `x` is the singleton containing
`lineMap x u (λ / (μ + λ))`, equivalently `x + (λ / (μ + λ)) • (u - x)`. This is the chapter's
singleton-valued rendering of the textbook formula from Corollary 6.64. -/
theorem prox_scaled_moreau_envelope_eq_singleton_of_scaled_prox_eq_singleton
    {f : E → EReal} {μ lam : PosReal} (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) {x u : E}
    (hprox : prox[(((μ + lam : ℝ) : EReal) • f)] x = {u}) :
    prox[(lam : EReal) • M[μ, f]] x =
      {lineMap x u ((lam : ℝ) / (μ + lam : ℝ))} := by
  -- Route correction: this bridge theorem must inherit the proper/closed/convex hypotheses needed
  -- by Theorem 6.63; the earlier `hf_ne_bot`-only route was not dependency-compatible.
  let ν : PosReal := μ / lam
  let g : E → EReal := (lam : EReal) • f
  rcases scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam with
    ⟨hg_proper, hg_closed, hg_convex⟩
  have hscaled_owner :
      (((((ν + 1 : PosReal) : ℝ) : EReal) • g) : E → EReal) =
        ((((μ + lam : ℝ) : EReal) • f) : E → EReal) := by
    -- Normalize the scaled function so the hypothesis matches Theorem 6.63 exactly.
    simpa [ν, g] using scaled_scaled_function_eq_sum_scale (E := E) (f := f) (μ := μ) (lam := lam)
  have hscaled_prox :
      prox[((((ν + 1 : PosReal) : ℝ) : EReal) • g)] x = {u} := by
    -- Rewrite the supplied singleton scaled proximal point to the scaled owner used by `g`.
    rw [hscaled_owner]
    exact hprox
  have howner :
      prox[(lam : EReal) • M[μ, f]] x = prox[M[ν, g]] x := by
    -- Lemma 6.57 again handles the owner-level rescaling of the Moreau envelope.
    simpa [ν, g] using scaled_moreau_prox_owner_rewrite (E := E) (f := f) (μ := μ) (lam := lam) x
  rw [howner]
  -- The repaired bridge theorem from Theorem 6.63 now applies verbatim to the scaled function.
  simpa [ν, g, moreau_weight_div_eq (μ := μ) (lam := lam)] using
    prox_moreau_envelope_eq_singleton_of_scaled_prox_eq_singleton
      (E := E) (f := g) (μ := ν) hg_proper hg_closed hg_convex hscaled_prox

end
