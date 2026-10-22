/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_22

noncomputable section

universe u

namespace LagrangianProblem

variable {E : Type u} {m : ℕ}

/- Primary domain: the auxiliary max-violation value function attached to an inequality-constrained
optimization problem.

Owner abstractions sampled before refining:
- `LagrangianProblem` in `Nesterov/Chap01/Definition_1_10_2.lean`, which owns the primitive
  objective-plus-constraints data;
- `LagrangianProblem.constrainedAuxiliaryObjective` in `Nesterov/Chap02/Lemma_2_21.lean`,
  the canonical auxiliary objective `x ↦ max {f₀(x) - t, f₁(x), …, fₘ(x)}`;
- `LagrangianProblem.constrainedAuxiliaryOptimalValue` in
  `Nesterov/Chap02/Lemma_2_21.lean`, the derived extended-real infimum value of that owner
  objective;
- `LagrangianProblem.constrainedAuxiliaryOptimalValue_eq_of_isMinOn` in
  `Nesterov/Chap02/Lemma_2_21.lean`, the owner attained-value bridge used to replace chosen
  minimizer evaluations by the canonical value function.

The primitive owner here is `LagrangianProblem E m`. For the displayed one-variable inequality, the
owner abstractions are the product-space convexity of
`problem.constrainedAuxiliaryObjective` and the attained-minimum bridge
`constrainedAuxiliaryOptimalValue_eq_of_isMinOn`: this file follows the source proof directly by
proving the convex-combination inequality for attained values and then rearranging the resulting
scalar algebra. Accordingly, the auxiliary objective and its optimal value stay derived owner
declarations, and attainment is kept as intrinsic `IsMinOn` data rather than as a chosen public
optimizer family.

Source/core/bridge triage:
- source-facing: Lemma 2.23's secant estimate for the auxiliary optimal-value function;
- core/canonical: `problem.constrainedAuxiliaryObjective t`,
  `problem.constrainedAuxiliaryOptimalValue t`, mathlib's `IsMinOn`, and product-space
  `ConvexOn`;
- bridge/view: the attained-minimum identity
  `constrainedAuxiliaryOptimalValue_eq_of_isMinOn`, which turns the extended-real owner value into
  the attained real value needed for the one-variable secant comparison; that bridge is already
  owned by `Lemma_2_22`.
-/

section SecantLowerBound

variable [AddCommMonoid E] [Module ℝ E]
variable (problem : LagrangianProblem E m)

/-- If the objective and each constraint are convex on the ambient module, then the auxiliary
objective is jointly convex in the scalar parameter and primal variable on `ℝ × E`. This is the
canonical bridge from the owner data `problem`, `problem.constraints`, and
`problem.constrainedAuxiliaryObjective` to the product-space `ConvexOn` API used downstream by
Lemma 2.23. -/
theorem constrainedAuxiliaryObjective_jointConvexOn
    (hobjective : ConvexOn ℝ Set.univ problem)
    (hconstraints : ∀ i, ConvexOn ℝ Set.univ (problem.constraints i)) :
    ConvexOn ℝ Set.univ
      (fun p : ℝ × E ↦ problem.constrainedAuxiliaryObjective p.1 p.2) := by
  have hcomponents :
      ∀ j : Fin (m + 1),
        ConvexOn ℝ Set.univ
          (fun p : ℝ × E ↦ problem.constrainedAuxiliaryComponents p.1 j p.2) := by
    intro j
    refine Fin.cases ?_ ?_ j
    · refine ⟨convex_univ, ?_⟩
      rintro ⟨s, x⟩ hs ⟨t, y⟩ ht a b ha hb hab
      simpa [constrainedAuxiliaryComponents, sub_eq_add_neg, mul_add, add_mul, add_assoc,
        add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm, smul_add] using
        hobjective.2 (by simp) (by simp) ha hb hab
    · intro i
      refine ⟨convex_univ, ?_⟩
      rintro ⟨s, x⟩ hs ⟨t, y⟩ ht a b ha hb hab
      simpa [constrainedAuxiliaryComponents] using
        (hconstraints i).2 (by simp) (by simp) ha hb hab
  simpa [constrainedAuxiliaryObjective] using
    maxTypeObjective_convexOn Set.univ
      (fun j : Fin (m + 1) ↦ fun p : ℝ × E ↦ problem.constrainedAuxiliaryComponents p.1 j p.2)
      hcomponents

omit [AddCommMonoid E] [Module ℝ E] in
/-- Helper for Lemma 2.23: any chosen attained minimizer realizes the canonical auxiliary optimal
value. -/
lemma attained_auxiliary_value_eq_optimal_value
    (xMin : ℝ → E)
    (hxMin : ∀ t : ℝ, IsMinOn (problem.constrainedAuxiliaryObjective t) Set.univ (xMin t)) :
    ∀ t : ℝ,
      problem.constrainedAuxiliaryOptimalValue t =
        ((problem.constrainedAuxiliaryObjective t (xMin t)) : EReal) := by
  intro t
  -- The owner attained-value bridge identifies the infimum with the chosen minimum value.
  simpa using problem.constrainedAuxiliaryOptimalValue_eq_of_isMinOn (hxMin t)

/-- Helper for Lemma 2.23: the attained auxiliary values satisfy the source convex-combination
inequality obtained from the joint convexity of the auxiliary objective. -/
lemma attained_auxiliary_value_convex_combination
    (hobjective : ConvexOn ℝ Set.univ problem)
    (hconstraints : ∀ i, ConvexOn ℝ Set.univ (problem.constraints i))
    (xMin : ℝ → E)
    (hxMin : ∀ t : ℝ, IsMinOn (problem.constrainedAuxiliaryObjective t) Set.univ (xMin t))
    {t0 t1 t2 α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hmid : t1 = (1 - α) * t0 + α * t2) :
    problem.constrainedAuxiliaryObjective t1 (xMin t1) ≤
      (1 - α) * problem.constrainedAuxiliaryObjective t0 (xMin t0) +
        α * problem.constrainedAuxiliaryObjective t2 (xMin t2) := by
  have haux_convex :
      ConvexOn ℝ Set.univ
        (fun p : ℝ × E ↦ problem.constrainedAuxiliaryObjective p.1 p.2) :=
    problem.constrainedAuxiliaryObjective_jointConvexOn hobjective hconstraints
  let xAlpha : E := (1 - α) • xMin t0 + α • xMin t2
  have hmin_t1 :
      problem.constrainedAuxiliaryObjective t1 (xMin t1) ≤
        problem.constrainedAuxiliaryObjective t1 xAlpha := by
    -- Minimality at `t1` is evaluated at the interpolated primal point `xAlpha`.
    exact (isMinOn_univ_iff.mp (hxMin t1)) xAlpha
  have hconv :
      problem.constrainedAuxiliaryObjective ((1 - α) * t0 + α * t2) xAlpha ≤
        (1 - α) * problem.constrainedAuxiliaryObjective t0 (xMin t0) +
          α * problem.constrainedAuxiliaryObjective t2 (xMin t2) := by
    -- Joint convexity supplies the Jensen estimate for the pair `(t, x)`.
    have hconv' :=
      haux_convex.2 (by simp : (t0, xMin t0) ∈ Set.univ) (by simp : (t2, xMin t2) ∈ Set.univ)
        (sub_nonneg.mpr hα1) hα0 (by ring)
    change problem.constrainedAuxiliaryObjective ((1 - α) * t0 + α * t2)
        ((1 - α) • xMin t0 + α • xMin t2) ≤
      (1 - α) * problem.constrainedAuxiliaryObjective t0 (xMin t0) +
        α * problem.constrainedAuxiliaryObjective t2 (xMin t2) at hconv'
    simpa [xAlpha] using hconv'
  -- The source route is: minimality at `t1`, then convexity at the interpolated point.
  calc
    problem.constrainedAuxiliaryObjective t1 (xMin t1)
        ≤ problem.constrainedAuxiliaryObjective t1 xAlpha := hmin_t1
    _ = problem.constrainedAuxiliaryObjective ((1 - α) * t0 + α * t2) xAlpha := by rw [hmid]
    _ ≤ (1 - α) * problem.constrainedAuxiliaryObjective t0 (xMin t0) +
          α * problem.constrainedAuxiliaryObjective t2 (xMin t2) := hconv

/-- Helper for Lemma 2.23: the convex-combination inequality with the source coefficient
`Δ / (t₂ - t₁ + Δ)` rearranges to the left-shifted secant lower bound. -/
lemma left_shift_secant_of_convex_combination
    {g : ℝ → ℝ} {t1 t2 Delta : ℝ}
    (ht : t1 < t2) (hDelta : 0 ≤ Delta)
    (hcombo :
      g t1 ≤
        ((t2 - t1) / (t2 - t1 + Delta)) * g (t1 - Delta) +
          (Delta / (t2 - t1 + Delta)) * g t2) :
    g (t1 - Delta) ≥ g t1 +
      (Delta / (t2 - t1)) * (g t1 - g t2) := by
  have hc : 0 < t2 - t1 := sub_pos.mpr ht
  have hd : 0 < t2 - t1 + Delta := add_pos_of_pos_of_nonneg hc hDelta
  have hmul := mul_le_mul_of_nonneg_left hcombo hd.le
  have hmul' :
      (t2 - t1 + Delta) * g t1 ≤ (t2 - t1) * g (t1 - Delta) + Delta * g t2 := by
    have htmp := hmul
    -- Clearing the positive denominator converts the convex combination into a linear inequality.
    field_simp [hd.ne'] at htmp
    ring_nf at htmp
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul] using htmp
  have hfinal :
      (t2 - t1) * (g t1 + (Delta / (t2 - t1)) * (g t1 - g t2)) ≤
        (t2 - t1) * g (t1 - Delta) := by
    have hrewrite :
        (t2 - t1) * (g t1 + (Delta / (t2 - t1)) * (g t1 - g t2)) =
          (t2 - t1 + Delta) * g t1 - Delta * g t2 := by
      field_simp [hc.ne']
      ring
    rw [hrewrite]
    linarith
  -- Dividing by the positive secant length recovers the desired one-sided slope estimate.
  exact le_of_mul_le_mul_left hfinal hc

/-- Lemma 2.23: if the objective and all constraint functions are convex and the auxiliary minimum
is attained for every parameter `t`, then the auxiliary optimal value function satisfies the
displayed left-shifted secant lower bound. This follows the source proof directly: choose attained
minimizers, prove the convex-combination inequality for the attained real values, and then rewrite
the result back into the canonical extended-real optimal-value notation. -/
theorem constrainedAuxiliaryOptimalValue_secant_lower_bound
    (hobjective : ConvexOn ℝ Set.univ problem)
    (hconstraints : ∀ i, ConvexOn ℝ Set.univ (problem.constraints i))
    (hattained :
      ∀ t : ℝ, ∃ x : E, IsMinOn (problem.constrainedAuxiliaryObjective t) Set.univ x)
    {t1 t2 Delta : ℝ} (ht : t1 < t2) (hDelta : 0 ≤ Delta) :
    problem.constrainedAuxiliaryOptimalValue (t1 - Delta) ≥
      problem.constrainedAuxiliaryOptimalValue t1 +
        (Delta / (t2 - t1)) *
          (problem.constrainedAuxiliaryOptimalValue t1 -
            problem.constrainedAuxiliaryOptimalValue t2) := by
  let xMin : ℝ → E := fun t ↦ Classical.choose (hattained t)
  have hxMin : ∀ t : ℝ, IsMinOn (problem.constrainedAuxiliaryObjective t) Set.univ (xMin t) := by
    intro t
    simpa [xMin] using Classical.choose_spec (hattained t)
  let V : ℝ → ℝ := fun t ↦ problem.constrainedAuxiliaryObjective t (xMin t)
  have hV : ∀ t : ℝ, problem.constrainedAuxiliaryOptimalValue t = (V t : EReal) := by
    intro t
    simpa [V] using problem.attained_auxiliary_value_eq_optimal_value xMin hxMin t
  let t0 : ℝ := t1 - Delta
  let α : ℝ := Delta / (t2 - t1 + Delta)
  have hgap : 0 < t2 - t1 := sub_pos.mpr ht
  have hdenom : 0 < t2 - t1 + Delta := add_pos_of_pos_of_nonneg hgap hDelta
  have hOneSubAlpha :
      1 - α = (t2 - t1) / (t2 - t1 + Delta) := by
    dsimp [α]
    field_simp [hdenom.ne']
    ring
  have hα0 : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg hDelta hdenom.le
  have hα1 : α ≤ 1 := by
    have hOneSubAlpha_nonneg : 0 ≤ 1 - α := by
      rw [hOneSubAlpha]
      exact div_nonneg hgap.le hdenom.le
    linarith
  have hmid : t1 = (1 - α) * t0 + α * t2 := by
    dsimp [t0, α]
    field_simp [hdenom.ne']
    ring
  have hcombo :
      V t1 ≤ (1 - α) * V t0 + α * V t2 := by
    -- Route correction: prove the source convex-combination estimate directly instead of calling
    -- the later secant theorem from Proposition 2.26.
    simpa [V, t0] using
      problem.attained_auxiliary_value_convex_combination
        hobjective hconstraints xMin hxMin hα0 hα1 hmid
  have hcombo' :
      V t1 ≤
        ((t2 - t1) / (t2 - t1 + Delta)) * V (t1 - Delta) +
          (Delta / (t2 - t1 + Delta)) * V t2 := by
    -- Rewriting the convex weights prepares the scalar inequality for the secant rearrangement.
    simpa [t0, α, hOneSubAlpha] using hcombo
  have hsecant :
      V (t1 - Delta) ≥ V t1 + (Delta / (t2 - t1)) * (V t1 - V t2) :=
    left_shift_secant_of_convex_combination ht hDelta hcombo'
  have hsecantEReal :
      (V (t1 - Delta) : EReal) ≥
        ((V t1 + (Delta / (t2 - t1)) * (V t1 - V t2) : ℝ) : EReal) := by
    -- The convexity computation was carried out in `ℝ`; only the final comparison is cast back.
    exact_mod_cast hsecant
  rw [hV (t1 - Delta), hV t1, hV t2]
  simpa using hsecantEReal

end SecantLowerBound

end LagrangianProblem
