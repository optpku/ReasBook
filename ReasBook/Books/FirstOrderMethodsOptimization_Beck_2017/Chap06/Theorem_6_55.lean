/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_8
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E]

/- Theorem 6.55 spans the view, core, and source-facing layers of the Moreau-envelope API.

- Part (1) is `bridge/view` only: Definition 6.7 already owns the identity `M[μ, f] = f □ ω(μ)`,
  so this file reuses that owner directly instead of introducing a duplicate theorem wrapper.
- `moreau_envelope_is_convex_of_convex` is `core/canonical`: convexity belongs to the chapter
  owner predicate `is_convex_function`.
- `moreau_envelope_eq_real_of_proper_convex` and
  `moreau_envelope_toReal_convexOn_of_proper_convex` are `source-facing` consequences
  showing that, when `f` is proper, closed, and convex and `μ > 0`, the owner is finite
  everywhere and therefore yields a real-valued convex function on the whole space.

The convexity owner statement itself only needs convexity, while the source-facing real-valued
consequences keep the textbook proper/closed/convex hypotheses. -/

/- Theorem 6.55: Definition 6.7 already states the textbook identity
`M[μ, f] = f □ ω(μ)`, so the canonical owner is reused directly here. -/
recall moreau_envelope

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Theorem 6.55: a proper closed convex extended-real-valued function admits a global
affine minorant. -/
lemma exists_affine_minorant_of_proper_closed_convex
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    ∃ l : E →L[ℝ] ℝ, ∃ c : ℝ, ∀ y, ((l y + c : ℝ) : EReal) ≤ f y := by
  -- Separate a point strictly below the epigraph from the closed convex real epigraph.
  rcases hf_proper.effective_domain_nonempty with ⟨x0, hx0_eff⟩
  have hx0_top : f x0 ≠ ⊤ := (mem_effective_domain.mp hx0_eff).ne
  have hx0_bot : f x0 ≠ ⊥ := hf_proper.ne_bot x0
  let a : ℝ := (f x0).toReal - 1
  have hx0_val : f x0 = (((f x0).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal hx0_top hx0_bot).symm
  have hax : (a : EReal) < f x0 := by
    rw [hx0_val]
    dsimp [a]
    exact_mod_cast sub_lt_self ((f x0).toReal) zero_lt_one
  have hconv : Convex ℝ (realEpigraph f) := by
    simpa [realEpigraph, is_convex_function] using hf_convex
  have hclosed : IsClosed (realEpigraph f) :=
    (lowerSemicontinuous_iff_isClosed_real_epigraph f).1 hf_closed
  have hpoint_out : (x0, a) ∉ realEpigraph f := by
    simpa [realEpigraph, not_le] using hax
  obtain ⟨L, u, hLu, hLepi⟩ :=
    geometric_hahn_banach_point_closed hconv hclosed hpoint_out
  let l0 : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let k : ℝ := L (((0 : E), (1 : ℝ)))
  have hk_eval (y : E) (t : ℝ) : L (y, t) = l0 y + k * t := by
    have hk : (L.comp (ContinuousLinearMap.inr ℝ E ℝ)) t = k * t := by
      calc
        (L.comp (ContinuousLinearMap.inr ℝ E ℝ)) t = L (((0 : E), t)) := rfl
        _ = L (t • (((0 : E), (1 : ℝ)))) := by simp
        _ = t * L (((0 : E), (1 : ℝ))) := by
          rw [ContinuousLinearMap.map_smul]
          simp [smul_eq_mul]
        _ = k * t := by simp [k, mul_comm]
    calc
      L (y, t) = (L.comp (ContinuousLinearMap.inl ℝ E ℝ)) y +
          (L.comp (ContinuousLinearMap.inr ℝ E ℝ)) t := by
            simpa using (ContinuousLinearMap.comp_inl_add_comp_inr L (y, t)).symm
      _ = l0 y + k * t := by rw [hk]
  have hx0_mem : (x0, (f x0).toReal) ∈ realEpigraph f := by
    rw [realEpigraph]
    change f x0 ≤ (((f x0).toReal : ℝ) : EReal)
    rw [EReal.coe_toReal hx0_top hx0_bot]
  have hk_pos : 0 < k := by
    -- Evaluating the separator at the two points above `x0` forces a positive vertical coefficient.
    have hsep : L (x0, a) < L (x0, (f x0).toReal) := hLu.trans (hLepi _ hx0_mem)
    rw [hk_eval, hk_eval] at hsep
    dsimp [a] at hsep
    linarith
  let l : E →L[ℝ] ℝ := -((⟨k, hk_pos⟩ : PosReal)⁻¹ : ℝ) • l0
  let c : ℝ := (((⟨k, hk_pos⟩ : PosReal)⁻¹ : ℝ) * l0 x0 + a)
  refine ⟨l, c, ?_⟩
  intro y
  by_cases hy_top : f y = ⊤
  · simp [hy_top]
  · have hy_bot : f y ≠ ⊥ := hf_proper.ne_bot y
    have hy_mem : (y, (f y).toReal) ∈ realEpigraph f := by
      rw [realEpigraph]
      change f y ≤ (((f y).toReal : ℝ) : EReal)
      rw [EReal.coe_toReal hy_top hy_bot]
    have hsep : L (x0, a) < L (y, (f y).toReal) := hLu.trans (hLepi _ hy_mem)
    rw [hk_eval, hk_eval] at hsep
    have hreal : -(((⟨k, hk_pos⟩ : PosReal)⁻¹ : ℝ) * l0 y) +
        ((((⟨k, hk_pos⟩ : PosReal)⁻¹ : ℝ) * l0 x0) + a) ≤ (f y).toReal := by
      have hmul := mul_le_mul_of_nonneg_left hsep.le (inv_nonneg.mpr hk_pos.le)
      have hk_ne : k ≠ 0 := by linarith
      dsimp only
      field_simp [hk_ne] at hmul ⊢
      linarith
    have hcoe : (((-(((⟨k, hk_pos⟩ : PosReal)⁻¹ : ℝ) * l0 y) +
        ((((⟨k, hk_pos⟩ : PosReal)⁻¹ : ℝ) * l0 x0) + a) : ℝ)) : EReal) ≤
        (((f y).toReal : ℝ) : EReal) :=
      EReal.coe_le_coe hreal
    have hy_val : f y = (((f y).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal hy_top hy_bot).symm
    rw [hy_val]
    simpa [l, c, EReal.coe_add] using hcoe

  /-- Helper for Theorem 6.55: the Moreau penalized objective is uniformly bounded below once `f`
  has a global affine minorant. -/
lemma moreau_penalized_objective_bounded_below
    (f : E → EReal) (μ : PosReal) (x : E) (l : E →L[ℝ] ℝ) (c : ℝ)
    (hminor : ∀ y, ((l y + c : ℝ) : EReal) ≤ f y) :
    ∃ B : ℝ, ∀ y,
      (B : EReal) ≤ f y + ((((1 / (2 * μ) : ℝ) * ‖x - y‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  refine ⟨l x + c - (μ : ℝ) / 2 * ‖l‖ ^ (2 : ℕ), ?_⟩
  intro y
  set r : ℝ := ‖x - y‖
  set s : ℝ := ‖l‖
  have hlin_abs : |l (x - y)| ≤ s * r := by
    simpa [r, s, Real.norm_eq_abs] using l.le_opNorm (x - y)
  have hlin_upper : l (x - y) ≤ s * r := (abs_le.mp hlin_abs).2
  have hquad : -(μ : ℝ) / 2 * s ^ (2 : ℕ) ≤ -s * r + (1 / (2 * μ) : ℝ) * r ^ (2 : ℕ) := by
    have hsq' : 0 ≤ r ^ (2 : ℕ) - 2 * (μ : ℝ) * s * r + (μ : ℝ) ^ (2 : ℕ) * s ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (r - (μ : ℝ) * s)]
    have hμ_ne : (μ : ℝ) ≠ 0 := by
      exact_mod_cast μ.2.ne'
    field_simp [hμ_ne]
    nlinarith [hsq']
  have hy_lin : l y = l x - l (x - y) := by
    have hxy : x - (x - y) = y := by abel
    calc
      l y = l (x - (x - y)) := by rw [hxy]
      _ = l x - l (x - y) := by rw [map_sub]
  have hreal : l x + c - (μ : ℝ) / 2 * s ^ (2 : ℕ) ≤
      l y + c + (1 / (2 * μ) : ℝ) * r ^ (2 : ℕ) := by
    rw [hy_lin]
    nlinarith
  have hcoe :
      (((l x + c - (μ : ℝ) / 2 * s ^ (2 : ℕ) : ℝ)) : EReal) ≤
        (((l y + c + (1 / (2 * μ) : ℝ) * r ^ (2 : ℕ) : ℝ)) : EReal) :=
    EReal.coe_le_coe hreal
  let p : EReal := ((((1 / (2 * μ) : ℝ) * ‖x - y‖ ^ (2 : ℕ) : ℝ)) : EReal)
  have hminor_add : ((l y + c : ℝ) : EReal) + p ≤ f y + p := by
    simpa [p, add_comm] using add_le_add_right (hminor y) p
  simpa [r, s, p, EReal.coe_add, add_assoc, add_left_comm, add_comm] using hcoe.trans hminor_add

  /-- Helper for Theorem 6.55: properness gives an explicit finite upper bound on the Moreau
  envelope. -/
lemma moreau_envelope_ne_top_of_proper
    (f : E → EReal) (μ : PosReal) (hf_proper : IsProperExtendedRealFunction f) (x : E) :
    M[μ, f] x ≠ ⊤ := by
  -- Evaluate the infimum at one point where `f` is finite.
  rcases hf_proper.effective_domain_nonempty with ⟨y0, hy0_eff⟩
  have hy0_top : f y0 ≠ ⊤ := (mem_effective_domain.mp hy0_eff).ne
  have hy0_bot : f y0 ≠ ⊥ := hf_proper.ne_bot y0
  let r : ℝ := (f y0).toReal + (1 / (2 * μ) : ℝ) * ‖x - y0‖ ^ (2 : ℕ)
  have hupper : M[μ, f] x ≤ (r : EReal) := by
    have hy0_val : f y0 = (((f y0).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal hy0_top hy0_bot).symm
    rw [moreau_envelope_apply]
    calc
      (⨅ u : E, f u + ((((1 / (2 * μ) : ℝ) * ‖x - u‖ ^ (2 : ℕ) : ℝ)) : EReal)) ≤
          f y0 + ((((1 / (2 * μ) : ℝ) * ‖x - y0‖ ^ (2 : ℕ) : ℝ)) : EReal) :=
            iInf_le _ y0
      _ = (r : EReal) := by
            rw [hy0_val]
            simp [r, EReal.coe_add]
  intro htop
  rw [htop] at hupper
  exact EReal.coe_ne_top r (top_le_iff.mp hupper)

  /-- Helper for Theorem 6.55: the affine minorant and the quadratic penalty give a finite lower
  bound on the Moreau envelope. -/
lemma moreau_envelope_ne_bot_of_proper_closed_convex
    (f : E → EReal) (μ : PosReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) (x : E) :
    M[μ, f] x ≠ ⊥ := by
  -- Route correction: pointwise `f y ≠ ⊥` is not enough; we first build a global affine lower
  -- support and let the quadratic term dominate it.
  rcases exists_affine_minorant_of_proper_closed_convex f hf_proper hf_closed hf_convex with
    ⟨l, c, hminor⟩
  rcases moreau_penalized_objective_bounded_below f μ x l c hminor with ⟨B, hB⟩
  have hlower : (B : EReal) ≤ M[μ, f] x := by
    simpa [moreau_envelope_apply] using (le_iInf hB : (B : EReal) ≤ ⨅ u : E,
      f u + ((((1 / (2 * μ) : ℝ) * ‖x - u‖ ^ (2 : ℕ) : ℝ)) : EReal))
  intro hbot
  rw [hbot] at hlower
  exact EReal.coe_ne_bot B (le_bot_iff.mp hlower)

-- Proof sketch: properness gives a point where `f` is finite, so `M[μ, f] x` is never `⊤`.
-- Convexity of `f` and of the quadratic kernel makes `M[μ, f]` convex, and a proper convex
-- extended-real-valued function cannot take the value `⊥` at an interior point of its effective
-- domain; since the quadratic penalty makes the effective domain all of `E`, the envelope is a
-- genuine real number everywhere.
/-- If `f` is a proper closed convex extended-real-valued function and `μ > 0`,
then the Moreau envelope is real-valued at every point. -/
theorem moreau_envelope_eq_real_of_proper_convex
    (f : E → EReal) (μ : PosReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_convex : is_convex_function f) (x : E) :
    ∃ r : ℝ, M[μ, f] x = (r : EReal) := by
  -- The previous two lemmas show that the envelope value is a genuine finite extended real.
  have hne_top : M[μ, f] x ≠ ⊤ := moreau_envelope_ne_top_of_proper f μ hf_proper x
  have hne_bot : M[μ, f] x ≠ ⊥ :=
    moreau_envelope_ne_bot_of_proper_closed_convex f μ hf_proper hf_closed hf_convex x
  exact ⟨(M[μ, f] x).toReal, (EReal.coe_toReal hne_top hne_bot).symm⟩

-- Proof sketch: the quadratic penalty `z ↦ (1 / (2 * μ)) ‖z‖²` is convex on `Set.univ` for
-- `μ > 0` because `z ↦ ‖z‖` is convex, squaring preserves convexity on nonnegative functions, and
-- scaling by the nonnegative coefficient `(1 / (2 * μ))` preserves convexity. The owner theorem
-- `infimal_convolution_is_convex` then applies directly to `M[μ, f] = f □ ω_μ`.
/-- If `f` is convex and `μ > 0`, then the Moreau envelope is convex in the chapter owner sense.
Properness is not needed for this owner-level convexity statement. -/
theorem moreau_envelope_is_convex_of_convex
    (f : E → EReal) (μ : PosReal) (hf_convex : is_convex_function f) :
    is_convex_function (M[μ, f]) := by
  have hnorm_sq : ConvexOn ℝ Set.univ (fun x : E ↦ ‖x‖ ^ (2 : ℕ)) :=
    convexOn_univ_norm.pow (fun x _ ↦ norm_nonneg x) 2
  have hcoeff : 0 ≤ 1 / (2 * (μ : ℝ)) := by
    have hμ : 0 < (μ : ℝ) := μ.2
    positivity
  have hkernel : ConvexOn ℝ Set.univ (fun x : E ↦ (1 / (2 * (μ : ℝ))) * ‖x‖ ^ (2 : ℕ)) := by
    simpa using hnorm_sq.smul hcoeff
  convert infimal_convolution_is_convex f
      (fun x : E ↦ (1 / (2 * (μ : ℝ))) * ‖x‖ ^ (2 : ℕ)) hf_convex hkernel using 1

-- Proof sketch: unfold Definition 6.7 as `M[μ, f] = f □ ω(μ)`. The kernel `ω(μ)` is a
-- real-valued convex function on the whole space when `μ > 0`, so the owner theorem above gives
-- convexity of `M[μ, f]`. Part (2) supplies finiteness under the same proper-convex
-- hypotheses, and then the Chapter 2 bridge from `EReal`-convexity to `ConvexOn` of `.toReal`
-- upgrades this to the real-valued convexity claim.
/-- If `f` is a proper closed convex extended-real-valued function and `μ > 0`,
then the real-valued Moreau envelope `x ↦ (M_f^μ x).toReal` is convex on the whole space. -/
theorem moreau_envelope_toReal_convexOn_of_proper_convex
    (f : E → EReal) (μ : PosReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_convex : is_convex_function f) :
    ConvexOn ℝ Set.univ (fun x ↦ (M[μ, f] x).toReal) := by
  have hne_bot : ∀ x ∈ effective_domain (M[μ, f]), M[μ, f] x ≠ ⊥ := by
    intro x hx
    rcases moreau_envelope_eq_real_of_proper_convex f μ hf_proper hf_closed hf_convex x with ⟨r, hr⟩
    rw [hr]
    simp
  have hdomain : effective_domain (M[μ, f]) = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases moreau_envelope_eq_real_of_proper_convex f μ hf_proper hf_closed hf_convex x with ⟨r, hr⟩
      rw [mem_effective_domain, hr]
      simp
  simpa [hdomain] using
    convexOn_toReal_of_is_convex_function
      (moreau_envelope_is_convex_of_convex f μ hf_convex) hne_bot

end
