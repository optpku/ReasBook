/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_47
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_24
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2

noncomputable section

open scoped Gradient StrongConvex WithTopConvexAnalysis

universe u

/- Definition 6.37 lies in the whole-space strong-convexity / subdifferential domain.

Sampled owner-style declarations:
- `S0On` with the notation `𝒮^0_σ(Q)` in `Chap03/Definition_3_47`, the chapter's source-facing
  owner for positive-parameter strong convexity;
- mathlib `StrongConvexOn`, the canonical whole-space strong-convexity owner;
- `subdifferential` with the notation `∂ f(x)` in `Chap03/Definition_3_1_5`, the chapter owner
  for subgradients of `WithTop ℝ`-valued functions;
- `strongConvexOnWith_normSeminorm_iff` and
  `StrongConvexOnWith.lower_tangent_quadratic_of_hasGradientAt` in `Chap02/Definition_2_14`, the
  ambient-norm bridge from the core owner to the textbook quadratic lower-tangent inequality.

Best owner abstraction:
- core/canonical: `f ∈ 𝒮^0_σ(Set.univ)`, equivalently `0 < σ ∧ StrongConvexOn Set.univ σ f`;
- bridge/view: the real-valued subgradient membership formula and the differentiable gradient
  specialization.

Primitive data:
- the modulus `σ : ℝ`;
- the real-valued objective `f : E → ℝ`.

Derived API:
- positivity of `σ` and the core owner `StrongConvexOn Set.univ σ f`, via `mem_S0On_iff`;
- the source-facing subgradient characterization below, phrased through the existing owner `∂`;
- the differentiable specialization with `∇ f x`.

Source/core/bridge triage:
- core/canonical main entry: `f ∈ 𝒮^0_σ(Set.univ)`;
- bridge/view: `mem_subdifferential_coe_iff`,
  `mem_S0On_univ_iff_exists_subgradient_lower_tangent_quadratic`, and
  `mem_S0On_univ_iff_gradient_inequality_of_differentiable`.

Definition 6.37 introduces no new owner beyond the earlier chapter surface `𝒮^0_σ(Set.univ)`.
This file therefore recalls that owner directly and keeps the textbook subgradient and gradient
formulas only as bridge theorems, instead of rebuilding parallel local definitions such as
`StrongConvexWithParameter`, `IsSubgradientAt`, or a second real-valued `subdifferential`.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section

variable (σ : ℝ) (f : E → ℝ)

/- Definition 6.37, owner form: positive whole-space strong convexity. -/
#check (f ∈ 𝒮^0_σ(Set.univ))

end

/-- For a real-valued function, membership in the Chapter 3 subdifferential owner is exactly the
usual affine lower-support inequality. -/
theorem mem_subdifferential_coe_iff {f : E → ℝ} {x g : E} :
    g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))(x) ↔
      ∀ y : E, f y ≥ f x + inner ℝ g (y - x) := by
  constructor
  · intro hg y
    have hy : y ∈ dom (fun z ↦ (f z : WithTop ℝ)) := by
      simp [withTopEffectiveDomain]
    have hineq :
        (((f x + inner ℝ g (y - x) : ℝ) : WithTop ℝ) ≤ (f y : WithTop ℝ)) := by
      simpa [mem_subdifferential_iff] using (mem_subdifferential_iff.mp hg).2 hy
    exact_mod_cast hineq
  · intro hg
    refine mem_subdifferential_iff.mpr ?_
    refine ⟨by simp [withTopEffectiveDomain], ?_⟩
    intro y hy
    have hineq :
        (((f x + inner ℝ g (y - x) : ℝ) : WithTop ℝ) ≤ (f y : WithTop ℝ)) := by
      exact_mod_cast hg y
    simpa using hineq

/-- Helper for Definition 6.37: for a real-valued function on the whole space, the constrained
subdifferential on `Set.univ` is the same owner surface as the unconstrained Chapter 3
subdifferential. -/
lemma mem_subdifferentialWithin_univ_iff_mem_subdifferential_coe
    {f : E → ℝ} {x g : E} :
    g ∈ ∂[Set.univ] f(x) ↔ g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))(x) := by
  constructor
  · intro hg
    rw [mem_subdifferential_coe_iff]
    rw [mem_subdifferentialWithin_iff] at hg
    intro y
    exact hg.2 (by simp)
  · intro hg
    rw [mem_subdifferentialWithin_iff]
    constructor
    · simp
    · intro y hy
      exact mem_subdifferential_coe_iff.mp hg y

/-- Helper for Definition 6.37: the quadratic lower-tangent inequality at `x` rewrites as a
support inequality for the shifted objective `z ↦ f z - (σ / 2) * ‖z‖²`. -/
lemma shiftedLowerSupport_of_quadraticLowerTangent
    {σ : ℝ} {f : E → ℝ} {x y g : E}
    (hquad :
      f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) :
    f y - (σ / 2) * ‖y‖ ^ (2 : ℕ) ≥
      f x - (σ / 2) * ‖x‖ ^ (2 : ℕ) + inner ℝ (g - σ • x) (y - x) := by
  -- Rewrite the quadratic term into the shifted affine-support form.
  have hinner : inner ℝ x (y - x) = inner ℝ x y - ‖x‖ ^ (2 : ℕ) := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
  have hnorm :
      ‖y - x‖ ^ (2 : ℕ) = ‖y‖ ^ (2 : ℕ) - 2 * inner ℝ x y + ‖x‖ ^ (2 : ℕ) := by
    rw [norm_sub_sq_real, real_inner_comm]
  have hrew :
      f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) =
        f x - (σ / 2) * ‖x‖ ^ (2 : ℕ) +
          inner ℝ (g - σ • x) (y - x) + (σ / 2) * ‖y‖ ^ (2 : ℕ) := by
    rw [inner_sub_left, real_inner_smul_left, hinner, hnorm]
    ring
  have hbound :
      f y ≥
        f x - (σ / 2) * ‖x‖ ^ (2 : ℕ) +
          inner ℝ (g - σ • x) (y - x) + (σ / 2) * ‖y‖ ^ (2 : ℕ) := by
    rwa [hrew] at hquad
  linarith

/-- Helper for Definition 6.37: a fixed quadratic lower tangent at `x` gives a whole-space
subgradient of the shifted objective. -/
lemma shiftedMemSubdifferentialWithin_of_quadraticLowerTangent
    {σ : ℝ} {f : E → ℝ} {x g : E}
    (hquad :
      ∀ y : E,
        f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) :
    g - σ • x ∈ subdifferentialWithin Set.univ
      (fun z ↦ f z - (σ / 2) * ‖z‖ ^ (2 : ℕ)) x := by
  -- Specialize the shifted support inequality to each comparison point.
  rw [mem_subdifferentialWithin_iff]
  refine ⟨by simp, ?_⟩
  intro y hy
  exact shiftedLowerSupport_of_quadraticLowerTangent (hquad y)

/-- Helper for Definition 6.37: a fixed subgradient witness at each base point yields
`f ∈ 𝒮^0_σ(Set.univ)`. -/
lemma mem_S0On_univ_of_exists_subgradient_lower_tangent_quadratic_fixed
    {σ : ℝ} {f : E → ℝ} (hσ : 0 < σ)
    (hsub :
      ∀ x : E,
        ∃ g ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(x),
          ∀ y : E,
            f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) :
    f ∈ 𝒮^0_σ(Set.univ) := by
  -- Shift the objective by `(σ / 2) * ‖·‖²` and recover convexity from nonempty whole-space
  -- subdifferentials.
  have hshifted_nonempty :
      ∀ x ∈ Set.univ,
        (subdifferentialWithin Set.univ
          (fun z ↦ f z - (σ / 2) * ‖z‖ ^ (2 : ℕ)) x).Nonempty := by
    intro x hx
    rcases hsub x with ⟨g, -, hg⟩
    exact ⟨g - σ • x, shiftedMemSubdifferentialWithin_of_quadraticLowerTangent hg⟩
  have hshifted_convex_lifted :
      ConvexOn ℝ Set.univ
        (withTopRealPart
          (fun z ↦ ((f z - (σ / 2) * ‖z‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ))) := by
    refine convexOn_of_constrainedSubdifferential_nonempty Set.univ
      (fun z ↦ ((f z - (σ / 2) * ‖z‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ))
      convex_univ ?_
    simpa [subdifferentialWithin]
      using hshifted_nonempty
  have hshifted_convex :
      ConvexOn ℝ Set.univ (fun z ↦ f z - (σ / 2) * ‖z‖ ^ (2 : ℕ)) := by
    simpa using hshifted_convex_lifted
  have hstrong : StrongConvexOn Set.univ σ f := by
    rw [strongConvexOn_iff_convex]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hshifted_convex
  exact (mem_S0On_iff).2 ⟨hσ, hstrong⟩

/-- Helper for Definition 6.37: whole-space strong convexity produces one subgradient at each
base point that supports every comparison point with the quadratic lower tangent. -/
lemma existsFixedSubgradientLowerTangentQuadratic_ofStrongConvexOnUniv
    [FiniteDimensional ℝ E] {σ : ℝ} {f : E → ℝ}
    (hσ : 0 < σ) (hstrong : StrongConvexOn Set.univ σ f) :
    ∀ x : E,
      ∃ g ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(x),
        ∀ y : E,
          f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  let lift : E → WithTop ℝ := fun z ↦ (f z : WithTop ℝ)
  have hconv : ConvexOn ℝ Set.univ f := by
    exact hstrong.convexOn (by
      intro r
      positivity)
  intro x
  have hxInt : x ∈ interior (dom lift) := by
    simp [lift, withTopEffectiveDomain]
  have hconvLift : ConvexOn ℝ (dom lift) (withTopRealPart lift) := by
    simpa [lift, withTopEffectiveDomain, withTopRealPart] using hconv
  rcases subdifferential_nonempty_of_convexOn_of_mem_interior hconvLift hxInt with ⟨g, hg⟩
  refine ⟨g, hg, ?_⟩
  intro y
  -- Convert the chosen whole-space subgradient to the constrained owner used by
  -- `StrongConvexOn.lower_bound_of_mem_subdifferentialWithin`.
  have hgWithin : g ∈ ∂[Set.univ] f(x) := by
    exact (mem_subdifferentialWithin_univ_iff_mem_subdifferential_coe).2 hg
  simpa using hstrong.lower_bound_of_mem_subdifferentialWithin hgWithin (by simp : y ∈ Set.univ)

/-- Helper for Definition 6.37: the pairwise quadratic lower-tangent hypothesis already forces
ordinary convexity on `Set.univ`, because the diagonal case gives a subgradient at every base
point. -/
lemma convexOnUniv_ofPairwiseSubgradientLowerTangentQuadratic
    {σ : ℝ} {f : E → ℝ}
    (hsub :
      ∀ x y : E,
        ∃ g ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(x),
          f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) :
    ConvexOn ℝ Set.univ f := by
  let lift : E → WithTop ℝ := fun z ↦ (f z : WithTop ℝ)
  have hsubWithin :
      ∀ x ∈ Set.univ, (∂[Set.univ] lift(x)).Nonempty := by
    intro x hx
    rcases hsub x x with ⟨g, hg, -⟩
    refine ⟨g, ?_⟩
    rw [mem_subdifferentialWithin_iff]
    refine ⟨by simp, ?_⟩
    intro y hy
    have hyDom : y ∈ dom lift := by
      simp [lift, withTopEffectiveDomain]
    have hsupport : f y ≥ f x + inner ℝ g (y - x) := mem_subdifferential_coe_iff.mp hg y
    exact_mod_cast hsupport
  have hconvLift : ConvexOn ℝ Set.univ (withTopRealPart lift) := by
    -- The diagonal witnesses provide the nonempty constrained subdifferentials needed by
    -- Lemma 3.6 on the lifted objective.
    refine convexOn_of_constrainedSubdifferential_nonempty Set.univ lift convex_univ ?_
    exact hsubWithin
  simpa [lift, withTopRealPart] using hconvLift

/-- Helper for Definition 6.37: whole-space subgradients of a convex real-valued function are
monotone along chords. -/
lemma inner_sub_nonneg_of_mem_subdifferential_coe
    {f : E → ℝ} {x y gx gy : E}
    (hgx : gx ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(x))
    (hgy : gy ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(y)) :
    0 ≤ inner ℝ (gy - gx) (y - x) := by
  -- Evaluate each subgradient at the other base point and compare the resulting chord slopes.
  have hxy : f y ≥ f x + inner ℝ gx (y - x) :=
    mem_subdifferential_coe_iff.mp hgx y
  have hyx : f x ≥ f y + inner ℝ gy (x - y) :=
    mem_subdifferential_coe_iff.mp hgy x
  have hxysym : x - y = -(y - x) := by
    abel_nf
  have hyx' : f y ≤ f x + inner ℝ gy (y - x) := by
    have hinner : inner ℝ gy (x - y) = -inner ℝ gy (y - x) := by
      rw [hxysym, inner_neg_right]
    have : f x ≥ f y - inner ℝ gy (y - x) := by
      rw [hinner] at hyx
      simpa [sub_eq_add_neg] using hyx
    linarith
  have hmono : inner ℝ gx (y - x) ≤ inner ℝ gy (y - x) := by
    linarith
  rw [inner_sub_left]
  exact sub_nonneg.mpr hmono

/-- Helper for Definition 6.37: a Chapter 3 subgradient gives a scalar support inequality on any
affine line through the base point. -/
lemma lineSupportSlope_of_mem_subdifferential_coe
    {f : E → ℝ} {z0 g d : E} {u : ℝ}
    (hg : g ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(z0)) :
    f (z0 + u • d) ≥ f z0 + u * inner ℝ g d := by
  -- Evaluate the whole-space affine support inequality at the line point `z0 + u • d`.
  have hsupport := mem_subdifferential_coe_iff.mp hg (z0 + u • d)
  simpa [inner_smul_right, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm,
    mul_left_comm, mul_assoc] using hsupport

/-- Helper for Definition 6.37: the vector pairwise quadratic lower-tangent hypothesis restricts
to the exact scalar lower-tangent statement on every affine line. -/
lemma linePairwiseQuadraticLowerTangent_ofPairwiseSubgradientLowerTangentQuadratic
    {σ : ℝ} {f : E → ℝ}
    (hsub :
      ∀ x y : E,
        ∃ g ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(x),
          f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ))
    (x d : E) (s t : ℝ) :
    ∃ m : ℝ,
      f (x + s • d) ≥
        f (x + t • d) + m * (s - t) + ((σ * ‖d‖ ^ (2 : ℕ)) / 2) * (s - t) ^ (2 : ℕ) := by
  -- Repackage the witness at the base point `x + t • d` using the scalar slope `⟪g, d⟫`.
  rcases hsub (x + t • d) (x + s • d) with ⟨g, hg, hineq⟩
  refine ⟨inner ℝ g d, ?_⟩
  have hdiff : x + s • d - (x + t • d) = (s - t) • d := by
    rw [add_sub_add_left_eq_sub, sub_smul]
  have hinner :
      inner ℝ g (x + s • d - (x + t • d)) = (s - t) * inner ℝ g d := by
    rw [hdiff, inner_smul_right]
  have hnorm :
      ‖x + s • d - (x + t • d)‖ ^ (2 : ℕ) = ‖d‖ ^ (2 : ℕ) * (s - t) ^ (2 : ℕ) := by
    rw [hdiff, norm_smul]
    calc
      (‖s - t‖ * ‖d‖) ^ (2 : ℕ) = ‖s - t‖ ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by ring
      _ = ‖d‖ ^ (2 : ℕ) * (s - t) ^ (2 : ℕ) := by
        rw [Real.norm_eq_abs, sq_abs]
        ring
  calc
    f (x + s • d) ≥
        f (x + t • d) + inner ℝ g (x + s • d - (x + t • d)) +
          (σ / 2) * ‖x + s • d - (x + t • d)‖ ^ (2 : ℕ) := hineq
    _ = f (x + t • d) + inner ℝ g d * (s - t) +
          ((σ * ‖d‖ ^ (2 : ℕ)) / 2) * (s - t) ^ (2 : ℕ) := by
        rw [hinner, hnorm]
        ring
    _ = f (x + t • d) + inner ℝ g d * (s - t) +
          ((σ * ‖d‖ ^ (2 : ℕ)) / 2) * (s - t) ^ (2 : ℕ) := rfl

/-- Helper for Definition 6.37: restricting the pairwise vector lower-tangent witness to a line
keeps both the global support inequality at the base point and the quadratic improvement at the
comparison point. -/
lemma lineSupportAndQuadraticWitness_ofPairwiseSubgradientLowerTangentQuadratic
    {σ : ℝ} {f : E → ℝ}
    (hsub :
      ∀ x y : E,
        ∃ g ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(x),
          f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ))
    (x d : E) (s t : ℝ) :
    ∃ m : ℝ,
      (∀ u : ℝ, f (x + u • d) ≥ f (x + t • d) + m * (u - t)) ∧
      f (x + s • d) ≥
        f (x + t • d) + m * (s - t) + ((σ * ‖d‖ ^ (2 : ℕ)) / 2) * (s - t) ^ (2 : ℕ) := by
  rcases hsub (x + t • d) (x + s • d) with ⟨g, hg, hineq⟩
  refine ⟨inner ℝ g d, ?_⟩
  constructor
  · intro u
    -- Recenter the scalar line parameter at the base point `t`.
    have hsupport :
        f ((x + t • d) + (u - t) • d) ≥ f (x + t • d) + (u - t) * inner ℝ g d :=
      lineSupportSlope_of_mem_subdifferential_coe hg
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul, mul_comm,
      mul_left_comm, mul_assoc] using hsupport
  · -- Reuse the same line witness to keep the quadratic improvement at the comparison point `s`.
    have hdiff : x + s • d - (x + t • d) = (s - t) • d := by
      rw [add_sub_add_left_eq_sub, sub_smul]
    have hinner :
        inner ℝ g (x + s • d - (x + t • d)) = (s - t) * inner ℝ g d := by
      rw [hdiff, inner_smul_right]
    have hnorm :
        ‖x + s • d - (x + t • d)‖ ^ (2 : ℕ) = ‖d‖ ^ (2 : ℕ) * (s - t) ^ (2 : ℕ) := by
      rw [hdiff, norm_smul]
      calc
        (‖s - t‖ * ‖d‖) ^ (2 : ℕ) = ‖s - t‖ ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by ring
        _ = ‖d‖ ^ (2 : ℕ) * (s - t) ^ (2 : ℕ) := by
          rw [Real.norm_eq_abs, sq_abs]
          ring
    calc
      f (x + s • d) ≥
          f (x + t • d) + inner ℝ g (x + s • d - (x + t • d)) +
            (σ / 2) * ‖x + s • d - (x + t • d)‖ ^ (2 : ℕ) := hineq
      _ = f (x + t • d) + inner ℝ g d * (s - t) +
            ((σ * ‖d‖ ^ (2 : ℕ)) / 2) * (s - t) ^ (2 : ℕ) := by
          rw [hinner, hnorm]
          ring
      _ = f (x + t • d) + inner ℝ g d * (s - t) +
            ((σ * ‖d‖ ^ (2 : ℕ)) / 2) * (s - t) ^ (2 : ℕ) := rfl

/-- Helper for Definition 6.37: the support-aware scalar line hypothesis gives the affine-ray
lower bound that is directly available from the comparison point `x`. -/
lemma scalarAffineRaySupportBound_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ)) :
    ∀ {x y : ℝ} {β : ℝ}, 0 ≤ β →
      φ (y + β * (y - x)) ≥
        φ y + β * (φ y - φ x) + β * (μ / 2) * (y - x) ^ (2 : ℕ) := by
  intro x y β hβ
  rcases hpair x y with ⟨m, hsupport, hquad⟩
  have hquad' :
      φ x ≥ φ y - m * (y - x) + (μ / 2) * (y - x) ^ (2 : ℕ) := by
    -- Rewrite the comparison inequality at `x` into a form where the support slope multiplies
    -- the positive displacement `y - x`.
    have hsub : x - y = -(y - x) := by
      ring
    have hsqNeg : (-(y - x)) ^ (2 : ℕ) = (y - x) ^ (2 : ℕ) := by
      ring_nf
    rw [hsub, hsqNeg] at hquad
    have hquad'' :
        φ x ≥ φ y - m * (y - x) + (μ / 2) * (y - x) ^ (2 : ℕ) := by
      linarith
    exact hquad''
  have hm :
      φ y - φ x + (μ / 2) * (y - x) ^ (2 : ℕ) ≤ m * (y - x) := by
    linarith
  have hsupportRay :
      φ (y + β * (y - x)) ≥ φ y + β * (m * (y - x)) := by
    -- Evaluate the global support inequality at the affine-ray point and normalize `u - y`.
    have hsupp := hsupport (y + β * (y - x))
    have hdiff : (y + β * (y - x)) - y = β * (y - x) := by
      ring
    calc
      φ (y + β * (y - x)) ≥ φ y + m * ((y + β * (y - x)) - y) := hsupp
      _ = φ y + β * (m * (y - x)) := by rw [hdiff]; ring
  have hmul :
      β * (φ y - φ x + (μ / 2) * (y - x) ^ (2 : ℕ)) ≤ β * (m * (y - x)) := by
    exact mul_le_mul_of_nonneg_left hm hβ
  linarith

/-- Helper for Definition 6.37: the quadratic shift along the affine ray `y + β * (y - x)`
expands in the normal form consumed by the shifted-slice affine-ray calculation. -/
lemma shiftedScalarSquare_affineRay
    {x y β : ℝ} :
    (y + β * (y - x)) ^ (2 : ℕ) =
      (1 + β) * y ^ (2 : ℕ) - β * x ^ (2 : ℕ) +
        β * (1 + β) * (y - x) ^ (2 : ℕ) := by
  -- Normalize the scalar polynomial identity once, instead of repeating the expansion inline.
  ring

/-- Helper for Definition 6.37: on an inner-product space, the squared norm along the affine ray
`y + β • (y - x)` expands in the same shifted normal form as the scalar model. -/
lemma shiftedNormSq_affineRay
    {x y : E} {β : ℝ} :
    ‖y + β • (y - x)‖ ^ (2 : ℕ) =
      (1 + β) * ‖y‖ ^ (2 : ℕ) - β * ‖x‖ ^ (2 : ℕ) +
        β * (1 + β) * ‖y - x‖ ^ (2 : ℕ) := by
  -- Rewrite the affine ray as `(1 + β) • y - β • x` and expand the squared norm once.
  have hrepr : y + β • (y - x) = (1 + β) • y + (-β) • x := by
    calc
      y + β • (y - x) = 1 • y + (β • y + β • (-x)) := by
        rw [sub_eq_add_neg, smul_add, one_smul]
      _ = (1 + β) • y + (-β) • x := by
        rw [smul_neg, add_smul]
        simp [one_smul, add_assoc, neg_smul]
  rw [hrepr, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, real_inner_comm x y, norm_sub_sq_real]
  have hsqY : (|1 + β| * ‖y‖) ^ (2 : ℕ) = (1 + β) ^ (2 : ℕ) * ‖y‖ ^ (2 : ℕ) := by
    rw [mul_pow, sq_abs]
  have hsqX : (|(-β)| * ‖x‖) ^ (2 : ℕ) = β ^ (2 : ℕ) * ‖x‖ ^ (2 : ℕ) := by
    rw [mul_pow, sq_abs, neg_sq]
  rw [hsqY, hsqX]
  rw [real_inner_comm x y]
  ring

/-- Helper for Definition 6.37: the secant slope of the shifted scalar slice
`t ↦ φ t - (μ / 2) * t²` is the original secant slope corrected by
`(μ / 2) * (x + y)`. -/
lemma shiftedScalarSlope_eq_originalSlope_sub_halfMuSum
    {φ : ℝ → ℝ} {μ x y : ℝ} (hxy : x ≠ y) :
    (((φ y - (μ / 2) * y ^ (2 : ℕ)) - (φ x - (μ / 2) * x ^ (2 : ℕ))) / (y - x)) =
      (φ y - φ x) / (y - x) - (μ / 2) * (x + y) := by
  -- Rewrite the quadratic correction through `y² - x² = (y - x) * (x + y)` before clearing the
  -- denominator, so the final step is a one-variable ring normalization.
  have hsquare : y ^ (2 : ℕ) - x ^ (2 : ℕ) = (y - x) * (x + y) := by
    ring
  have hne : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  calc
    (((φ y - (μ / 2) * y ^ (2 : ℕ)) - (φ x - (μ / 2) * x ^ (2 : ℕ))) / (y - x))
        = ((φ y - φ x) - (μ / 2) * (y ^ (2 : ℕ) - x ^ (2 : ℕ))) / (y - x) := by
            ring
    _ = ((φ y - φ x) - (μ / 2) * ((y - x) * (x + y))) / (y - x) := by
          rw [hsquare]
    _ = (φ y - φ x) / (y - x) - (μ / 2) * (x + y) := by
          rw [sub_div]
          have hdiv : ((μ / 2) * ((y - x) * (x + y))) / (y - x) = (μ / 2) * (x + y) := by
            field_simp [hne]
          rw [hdiv]

/-- Helper for Definition 6.37: a global support slope for `φ` at `t` is exactly a Chapter 3
subgradient of the lifted scalar function at `t`. -/
lemma scalarSupportSlope_mem_subdifferential_coe
    {φ : ℝ → ℝ} {t m : ℝ}
    (hsupport : ∀ u : ℝ, φ u ≥ φ t + m * (u - t)) :
    m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(t) := by
  -- Reinterpret the scalar support inequality through the owner-level subdifferential surface.
  rw [mem_subdifferential_coe_real_iff]
  intro u
  have hsupport' : φ u ≥ φ t + inner ℝ m (u - t) := by
    have hinner : inner ℝ (u - t) m = (u - t) * m := by
      calc
        inner ℝ (u - t) m = m * (starRingEnd ℝ) (u - t) := RCLike.inner_apply (u - t) m
        _ = m * (u - t) := by simp
        _ = (u - t) * m := by ring
    rw [real_inner_comm]
    rw [hinner]
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hsupport u
  exact hsupport'

/-- Helper for Definition 6.37: the quadratic lower tangent at one scalar comparison point
transports to the corresponding one-point support inequality for the shifted slice
`u ↦ φ u - (μ / 2) * u²`. -/
lemma shiftedScalarSupportAtPoint_of_supportAndQuadratic
    {φ : ℝ → ℝ} {μ s t m : ℝ}
    (hquad :
      φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ)) :
    φ s - (μ / 2) * s ^ (2 : ℕ) ≥
      φ t - (μ / 2) * t ^ (2 : ℕ) + (m - μ * t) * (s - t) := by
  -- Expand the quadratic correction once and move it into the shifted affine support form.
  have hrew :
      φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ) =
        φ t - (μ / 2) * t ^ (2 : ℕ) + (m - μ * t) * (s - t) +
          (μ / 2) * s ^ (2 : ℕ) := by
    ring
  have hquad' :
      φ s ≥
        φ t - (μ / 2) * t ^ (2 : ℕ) + (m - μ * t) * (s - t) +
          (μ / 2) * s ^ (2 : ℕ) := by
    rwa [hrew] at hquad
  linarith

/-- Helper for Definition 6.37: a lower affine support inequality at a left comparison point
turns into an upper bound on the corresponding secant slope. -/
lemma leftSecant_le_of_lowerAffineAtPoint
    {ψ : ℝ → ℝ} {x y m : ℝ}
    (hxy : x < y)
    (hleft : ψ x ≥ ψ y + m * (x - y)) :
    (ψ y - ψ x) / (y - x) ≤ m := by
  -- Move the pointwise lower support inequality into a secant form and divide by the positive gap.
  have hgap : 0 < y - x := sub_pos.mpr hxy
  have hlin : ψ y - ψ x ≤ m * (y - x) := by
    linarith
  exact (div_le_iff₀ hgap).2 (by simpa [mul_comm] using hlin)

/-- Helper for Definition 6.37: a lower affine support inequality at a right comparison point
turns into a lower bound on the corresponding secant slope. -/
lemma le_rightSecant_of_lowerAffineAtPoint
    {ψ : ℝ → ℝ} {y z m : ℝ}
    (hyz : y < z)
    (hright : ψ z ≥ ψ y + m * (z - y)) :
    m ≤ (ψ z - ψ y) / (z - y) := by
  -- Rearrange the support inequality and divide by the positive displacement to bound the secant.
  have hgap : 0 < z - y := sub_pos.mpr hyz
  have hlin : m * (z - y) ≤ ψ z - ψ y := by
    linarith
  exact (le_div_iff₀ hgap).2 (by simpa [mul_comm] using hlin)

/-- Helper for Definition 6.37: subgradients of a convex scalar function are monotone in the base
point. -/
lemma scalarSubgradient_mono_of_lt
    {φ : ℝ → ℝ} {x y g₁ g₂ : ℝ}
    (hg₁ : g₁ ∈ ∂ (fun r ↦ (φ r : WithTop ℝ))(x))
    (hg₂ : g₂ ∈ ∂ (fun r ↦ (φ r : WithTop ℝ))(y))
    (hxy : x < y) :
    g₁ ≤ g₂ := by
  -- Specialize the ambient monotonicity pairing to `ℝ`, where the inner product is ordinary
  -- multiplication by the positive gap `y - x`.
  have hmono :
      0 ≤ inner ℝ (g₂ - g₁) (y - x) :=
    inner_sub_nonneg_of_mem_subdifferential_coe hg₁ hg₂
  have hinner : inner ℝ (g₂ - g₁) (y - x) = (g₂ - g₁) * (y - x) := by
    calc
      inner ℝ (g₂ - g₁) (y - x) = (y - x) * (starRingEnd ℝ) (g₂ - g₁) := RCLike.inner_apply _ _
      _ = (y - x) * (g₂ - g₁) := by simp
      _ = (g₂ - g₁) * (y - x) := by ring
  have hprod : 0 ≤ (g₂ - g₁) * (y - x) := by
    simpa [hinner] using hmono
  have hgap : 0 < y - x := sub_pos.mpr hxy
  have hdiff_nonneg : 0 ≤ g₂ - g₁ := by
    nlinarith
  linarith

/-- Helper for Definition 6.37: the scalar pairwise support-plus-quadratic hypothesis already
forces ordinary convexity of `φ`, because the diagonal case supplies a global support slope at
every base point. -/
lemma scalarConvexOnUniv_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ)) :
    ConvexOn ℝ Set.univ φ := by
  let lift : ℝ → WithTop ℝ := fun t ↦ (φ t : WithTop ℝ)
  have hsub :
      ∀ t ∈ Set.univ, (∂[Set.univ] lift(t)).Nonempty := by
    intro t ht
    rcases hpair t t with ⟨m, hsupport, -⟩
    refine ⟨m, ?_⟩
    -- The diagonal witness is already a global support slope at `t`, so it gives a whole-space
    -- subgradient of the lifted scalar function.
    exact
      (mem_subdifferentialWithin_univ_iff_mem_subdifferential_coe).2
        (scalarSupportSlope_mem_subdifferential_coe hsupport)
  -- Recover convexity from nonempty constrained subdifferentials on `Set.univ`.
  have hconvLift : ConvexOn ℝ Set.univ (withTopRealPart lift) := by
    exact convexOn_of_constrainedSubdifferential_nonempty Set.univ lift convex_univ hsub
  simpa [lift, withTopRealPart] using hconvLift

/-- Helper for Definition 6.37: the pairwise support-plus-quadratic hypothesis already yields a
pair of subgradients whose values increase by at least `μ * (y - x)` across `x < y`. -/
lemma existsStrongMonotoneSubgradientPair_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y : ℝ} (hxy : x < y) :
    ∃ p q : ℝ,
      p ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(x) ∧
      q ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
      μ * (y - x) ≤ q - p := by
  rcases hpair y x with ⟨p, hsupportX, hyquad⟩
  rcases hpair x y with ⟨q, hsupportY, hxquad⟩
  refine ⟨p, q, scalarSupportSlope_mem_subdifferential_coe hsupportX, ?_⟩
  refine ⟨scalarSupportSlope_mem_subdifferential_coe hsupportY, ?_⟩
  -- Rewrite the `x`-comparison inequality through the positive gap `y - x`, then add it to the
  -- `y`-comparison inequality from base point `x`.
  have hxquad' :
      φ x ≥ φ y - q * (y - x) + (μ / 2) * (y - x) ^ (2 : ℕ) := by
    have hxneg : x - y = -(y - x) := by
      ring
    have hxsq : (-(y - x)) ^ (2 : ℕ) = (y - x) ^ (2 : ℕ) := by
      ring
    rw [hxneg, hxsq] at hxquad
    linarith
  have hgap : 0 < y - x := sub_pos.mpr hxy
  have hprod : 0 ≤ (q - p - μ * (y - x)) * (y - x) := by
    nlinarith [hyquad, hxquad']
  nlinarith

/-- Helper for Definition 6.37: when `x < y < z`, the scalar pairwise support-plus-quadratic
hypothesis forces the shifted left secant threshold to lie below the shifted right secant
threshold. -/
lemma quadraticSecantGap_of_shiftedConvexOn
    {φ : ℝ → ℝ} {μ : ℝ}
    (hconv : ConvexOn ℝ Set.univ (fun r ↦ φ r - (μ / 2) * r ^ (2 : ℕ)))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
      ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
  let ψ : ℝ → ℝ := fun r ↦ φ r - (μ / 2) * r ^ (2 : ℕ)
  -- Compare the adjacent secants of the shifted slice, then rewrite those secants back into the
  -- original-function thresholds.
  have hslope :
      (ψ y - ψ x) / (y - x) ≤ (ψ z - ψ y) / (z - y) := by
    simpa [ψ] using
      hconv.slope_mono_adjacent (x := x) (y := y) (z := z) (by simp) (by simp) hxy hyz
  rw [shiftedScalarSlope_eq_originalSlope_sub_halfMuSum (φ := φ) (μ := μ) (x := x) (y := y)
      hxy.ne, shiftedScalarSlope_eq_originalSlope_sub_halfMuSum (φ := φ) (μ := μ) (x := y)
      (y := z) hyz.ne] at hslope
  linarith

/-- Helper for Definition 6.37: a convex real-valued scalar slice on `Set.univ` has a greatest
middle-point subgradient. -/
lemma existsGreatestScalarSubgradient_of_convexOnUniv
    {φ : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ φ) (y : ℝ) :
    ∃ m : ℝ,
      m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
      ∀ g : ℝ, g ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) → g ≤ m := by
  let lift : ℝ → WithTop ℝ := fun u ↦ (φ u : WithTop ℝ)
  have hconvLift :
      ConvexOn ℝ (dom lift) (withTopRealPart lift) := by
    simpa [lift, withTopEffectiveDomain, withTopRealPart] using hconv
  have hyInt : y ∈ interior (dom lift) := by
    simp [lift, withTopEffectiveDomain]
  have hnonempty : (∂ lift(y)).Nonempty :=
    subdifferential_nonempty_of_convexOn_of_mem_interior hconvLift hyInt
  have hcompact : IsCompact (∂ lift(y)) :=
    (subdifferential_compact_convex_at (f := φ) hconv y).1
  obtain ⟨m, hmGreatest⟩ := hcompact.exists_isGreatest hnonempty
  refine ⟨m, hmGreatest.1, ?_⟩
  intro g hg
  exact hmGreatest.2 hg

/-- Helper for Definition 6.37: a convex real-valued scalar slice on `Set.univ` has a least
middle-point subgradient. -/
lemma existsLeastScalarSubgradient_of_convexOnUniv
    {φ : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ φ) (y : ℝ) :
    ∃ m : ℝ,
      m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
      ∀ g : ℝ, g ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) → m ≤ g := by
  let lift : ℝ → WithTop ℝ := fun u ↦ (φ u : WithTop ℝ)
  have hconvLift :
      ConvexOn ℝ (dom lift) (withTopRealPart lift) := by
    simpa [lift, withTopEffectiveDomain, withTopRealPart] using hconv
  have hyInt : y ∈ interior (dom lift) := by
    simp [lift, withTopEffectiveDomain]
  have hnonempty : (∂ lift(y)).Nonempty :=
    subdifferential_nonempty_of_convexOn_of_mem_interior hconvLift hyInt
  have hcompact : IsCompact (∂ lift(y)) :=
    (subdifferential_compact_convex_at (f := φ) hconv y).1
  let negImage : Set ℝ := (fun g : ℝ ↦ -g) '' ∂ lift(y)
  have hnegCompact : IsCompact negImage := by
    simpa [negImage] using hcompact.image continuous_neg
  have hnegNonempty : negImage.Nonempty := by
    rcases hnonempty with ⟨g, hg⟩
    exact ⟨-g, ⟨g, hg, rfl⟩⟩
  obtain ⟨n, hnGreatest⟩ := hnegCompact.exists_isGreatest hnegNonempty
  rcases hnGreatest.1 with ⟨m, hmSub, hmEq⟩
  refine ⟨m, hmSub, ?_⟩
  intro g hg
  have hnegMem : -g ∈ negImage := ⟨g, hg, rfl⟩
  have hn : n = -m := by
    simpa using hmEq.symm
  linarith [hnGreatest.2 hnegMem, hn]

/-- Helper for Definition 6.37: once the scalar subdifferential interval at `y` is known to meet
the numeric interval `[L, U]`, one can choose an actual middle-point subgradient in that overlap.
-/
lemma subgradientIntervalWitness_of_bounds
    {φ : ℝ → ℝ} {y L U mInf mSup : ℝ}
    (hmInfSub : mInf ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y))
    (hmSupSub : mSup ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y))
    (hright : mInf ≤ U)
    (hleft : L ≤ mSup)
    (hgap : L ≤ U) :
    ∃ m : ℝ,
      m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
      L ≤ m ∧
      m ≤ U := by
  have hsubConv :
      Convex ℝ (∂ (fun u ↦ (φ u : WithTop ℝ))(y)) :=
    convex_subdifferential_coe_real_at (f := φ) y
  by_cases hLmInf : L ≤ mInf
  · -- If the least subgradient already lies above `L`, it is the desired overlap witness.
    exact ⟨mInf, hmInfSub, hLmInf, hright⟩
  · -- Otherwise `L` lies between the least and greatest subgradients, so convexity places `L`
    -- itself in the scalar subdifferential interval.
    have hmInf_le_L : mInf ≤ L := (lt_of_not_ge hLmInf).le
    have hLSub : L ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) := by
      exact hsubConv.ordConnected.out hmInfSub hmSupSub ⟨hmInf_le_L, hleft⟩
    exact ⟨L, hLSub, le_rfl, hgap⟩

/-- Helper for Definition 6.37: the outer secant over `[x, z]` is the weighted average of the
adjacent secants over `[x, y]` and `[y, z]`. -/
lemma outerSecant_eq_weightedAdjacentSecants
    {φ : ℝ → ℝ} {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    (φ z - φ x) / (z - x) =
      ((z - y) / (z - x)) * ((φ z - φ y) / (z - y)) +
      ((y - x) / (z - x)) * ((φ y - φ x) / (y - x)) := by
  -- Clear the three secant denominators once so the identity is a single polynomial check.
  have hxy_ne : y - x ≠ 0 := sub_ne_zero.mpr hxy.ne.symm
  have hyz_ne : z - y ≠ 0 := sub_ne_zero.mpr hyz.ne.symm
  have hzx_ne : z - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans hxy hyz))
  field_simp [hxy_ne, hyz_ne, hzx_ne]
  ring_nf

/-- Helper for Definition 6.37: extrapolating the pair `(x, y)` along its affine ray to `z`
forces a lower bound on the outer secant over `[x, z]`. -/
lemma outerSecantLowerBound_fromLeftAffineRay
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    ((φ y - φ x) / (y - x)) + (μ / 2) * ((y - x) * (z - y) / (z - x)) ≤
      (φ z - φ x) / (z - x) := by
  let β : ℝ := (z - y) / (y - x)
  have hxy_gap : 0 < y - x := sub_pos.mpr hxy
  have hyz_gap : 0 < z - y := sub_pos.mpr hyz
  have hzx_gap : 0 < z - x := sub_pos.mpr (lt_trans hxy hyz)
  have hβ_nonneg : 0 ≤ β := by
    exact div_nonneg hyz_gap.le hxy_gap.le
  have hβray :
      y + β * (y - x) = z := by
    dsimp [β]
    field_simp [sub_ne_zero.mpr hxy.ne.symm]
    ring
  have hβdiff :
      z - y = β * (y - x) := by
    linarith [hβray]
  have hβspan :
      z - x = (1 + β) * (y - x) := by
    linarith [hβdiff]
  have hray :=
    scalarAffineRaySupportBound_of_pairwiseSupportAndQuadratic
      (φ := φ) (μ := μ) hpair (x := x) (y := y) (β := β) hβ_nonneg
  have hbound :
      φ z ≥
        φ y + β * (φ y - φ x) + β * (μ / 2) * (y - x) ^ (2 : ℕ) := by
    simpa [hβray] using hray
  -- Rewrite the affine-ray estimate into a secant inequality over `[x, z]`.
  refine (le_div_iff₀ hzx_gap).2 ?_
  rw [hβdiff, hβspan]
  field_simp [sub_ne_zero.mpr hxy.ne.symm]
  linarith

/-- Helper for Definition 6.37: extrapolating the pair `(z, y)` back to `x` forces an upper
bound on the outer secant over `[x, z]`. -/
lemma outerSecantUpperBound_fromRightAffineRay
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    (φ z - φ x) / (z - x) ≤
      ((φ z - φ y) / (z - y)) - (μ / 2) * ((y - x) * (z - y) / (z - x)) := by
  let β : ℝ := (y - x) / (z - y)
  have hxy_gap : 0 < y - x := sub_pos.mpr hxy
  have hyz_gap : 0 < z - y := sub_pos.mpr hyz
  have hzx_gap : 0 < z - x := sub_pos.mpr (lt_trans hxy hyz)
  have hβ_nonneg : 0 ≤ β := by
    exact div_nonneg hxy_gap.le hyz_gap.le
  have hβray :
      y + β * (y - z) = x := by
    dsimp [β]
    field_simp [sub_ne_zero.mpr hyz.ne.symm]
    ring
  have hβdiff :
      y - x = β * (z - y) := by
    linarith [hβray]
  have hβspan :
      z - x = (1 + β) * (z - y) := by
    linarith [hβdiff]
  have hray :=
    scalarAffineRaySupportBound_of_pairwiseSupportAndQuadratic
      (φ := φ) (μ := μ) hpair (x := z) (y := y) (β := β) hβ_nonneg
  have hbound :
      φ x ≥
        φ y + β * (φ y - φ z) + β * (μ / 2) * (z - y) ^ (2 : ℕ) := by
    have hsq : (y - z) ^ (2 : ℕ) = (z - y) ^ (2 : ℕ) := by
      ring_nf
    have hray' :
        φ (y + β * (y - z)) ≥
          φ y + β * (φ y - φ z) + β * (μ / 2) * (y - z) ^ (2 : ℕ) := hray
    rw [hβray, hsq] at hray'
    exact hray'
  -- Rewrite the reflected affine-ray estimate into the symmetric outer-secant upper bound.
  refine (div_le_iff₀ hzx_gap).2 ?_
  rw [hβdiff, hβspan]
  field_simp [sub_ne_zero.mpr hyz.ne.symm]
  linarith

/-- Helper for Definition 6.37: a quadratic lower tangent at the left endpoint forces the
corresponding shifted left secant threshold to lie below the chosen middle-point slope. -/
lemma leftSecantThreshold_le_of_subgradientLowerTangentQuadratic
    {φ : ℝ → ℝ} {μ x y m : ℝ}
    (hxy : x < y)
    (hxquad : φ x ≥ φ y + m * (x - y) + (μ / 2) * (x - y) ^ (2 : ℕ)) :
    ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤ m := by
  -- Rewrite the left inequality with the positive gap `y - x`, then divide by that gap.
  have hxy_gap : 0 < y - x := sub_pos.mpr hxy
  have hxquad' :
      φ x ≥ φ y - m * (y - x) + (μ / 2) * (y - x) ^ (2 : ℕ) := by
    have hxneg : x - y = -(y - x) := by
      ring
    have hxsq : (-(y - x)) ^ (2 : ℕ) = (y - x) ^ (2 : ℕ) := by
      ring
    rw [hxneg, hxsq] at hxquad
    linarith
  have hdiv :
      (φ y - φ x) / (y - x) ≤ m - (μ / 2) * (y - x) := by
    refine (div_le_iff₀ hxy_gap).2 ?_
    linarith
  linarith

/-- Helper for Definition 6.37: a quadratic lower tangent at the right endpoint forces the
chosen middle-point slope to lie below the corresponding shifted right secant threshold. -/
lemma subgradientLowerTangentQuadratic_le_rightSecantThreshold
    {φ : ℝ → ℝ} {μ y z m : ℝ}
    (hyz : y < z)
    (hzquad : φ z ≥ φ y + m * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ)) :
    m ≤ ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
  -- Divide the right-endpoint inequality by the positive gap `z - y` and isolate the slope.
  have hyz_gap : 0 < z - y := sub_pos.mpr hyz
  have hdiv :
      m + (μ / 2) * (z - y) ≤ (φ z - φ y) / (z - y) := by
    refine (le_div_iff₀ hyz_gap).2 ?_
    linarith
  linarith

/-- Helper for Definition 6.37: the pairwise support-plus-quadratic hypothesis at `(x, y)`
already furnishes a middle-point subgradient whose quadratic lower tangent works at the left
endpoint `x`. -/
lemma existsMiddleSubgradient_leftQuadratic_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y : ℝ} :
    ∃ m : ℝ,
      m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
      φ x ≥ φ y + m * (x - y) + (μ / 2) * (x - y) ^ (2 : ℕ) := by
  rcases hpair x y with ⟨m, hsupport, hxquad⟩
  -- Repackage the pairwise witness at base point `y` as an actual scalar subgradient.
  exact ⟨m, scalarSupportSlope_mem_subdifferential_coe hsupport, hxquad⟩

/-- Helper for Definition 6.37: the pairwise support-plus-quadratic hypothesis at `(z, y)`
already furnishes a middle-point subgradient whose quadratic lower tangent works at the right
endpoint `z`. -/
lemma existsMiddleSubgradient_rightQuadratic_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {y z : ℝ} :
    ∃ m : ℝ,
      m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
      φ z ≥ φ y + m * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ) := by
  rcases hpair z y with ⟨m, hsupport, hzquad⟩
  -- The same support witness at base point `y` immediately gives the right-endpoint tangent.
  exact ⟨m, scalarSupportSlope_mem_subdifferential_coe hsupport, hzquad⟩

/-- Helper for Definition 6.37: each scalar support-plus-quadratic witness is already a pairwise
Chapter 3 subgradient lower-tangent witness. -/
lemma scalarPairwiseSubgradientLowerTangentQuadratic_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ)) :
    ∀ s t : ℝ,
      ∃ g ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(t),
        φ s ≥ φ t + g * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ) := by
  intro s t
  rcases hpair s t with ⟨g, hsupport, hquad⟩
  refine ⟨g, scalarSupportSlope_mem_subdifferential_coe hsupport, ?_⟩
  -- This bridge only repackages the pairwise slope as a scalar subgradient at the same base.
  simpa using hquad

/-- Helper for Definition 6.37: at a fixed base point, the greatest scalar subgradient preserves
every quadratic lower tangent coming from a comparison point on the left. -/
lemma greatestScalarSubgradient_lowerTangentQuadratic_left_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {s t mSup : ℝ}
    (hs : s ≤ t)
    (_hmSupSub : mSup ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(t))
    (hmSupGreatest :
      ∀ g : ℝ, g ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(t) → g ≤ mSup) :
    φ s ≥ φ t + mSup * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ) := by
  rcases
      scalarPairwiseSubgradientLowerTangentQuadratic_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair s t with
    ⟨g, hgSub, hgquad⟩
  have hg_le : g ≤ mSup := hmSupGreatest g hgSub
  -- On the left of `t`, enlarging the slope only decreases the affine term.
  have hmul : mSup * (s - t) ≤ g * (s - t) := by
    exact mul_le_mul_of_nonpos_right hg_le (sub_nonpos.mpr hs)
  linarith

/-- Helper for Definition 6.37: at a fixed base point, the least scalar subgradient preserves
every quadratic lower tangent coming from a comparison point on the right. -/
lemma leastScalarSubgradient_lowerTangentQuadratic_right_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {t s mInf : ℝ}
    (hts : t ≤ s)
    (_hmInfSub : mInf ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(t))
    (hmInfLeast :
      ∀ g : ℝ, g ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(t) → mInf ≤ g) :
    φ s ≥ φ t + mInf * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ) := by
  rcases
      scalarPairwiseSubgradientLowerTangentQuadratic_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair s t with
    ⟨g, hgSub, hgquad⟩
  have hmInf_le : mInf ≤ g := hmInfLeast g hgSub
  -- On the right of `t`, shrinking the slope only decreases the affine term.
  have hmul : mInf * (s - t) ≤ g * (s - t) := by
    exact mul_le_mul_of_nonneg_right hmInf_le (sub_nonneg.mpr hts)
  linarith

/-- Helper for Definition 6.37: once the corrected secant gap is known, convexity of the scalar
subdifferential interval at the middle point produces one slope that works at both endpoints. -/
lemma existsSharedSubgradient_of_secantGap
    {φ : ℝ → ℝ} {μ : ℝ} {x y z mL mR : ℝ}
    (hxy : x < y) (hyz : y < z)
    (hmLSub : mL ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y))
    (hmRSub : mR ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y))
    (hxquad : φ x ≥ φ y + mL * (x - y) + (μ / 2) * (x - y) ^ (2 : ℕ))
    (hzquad : φ z ≥ φ y + mR * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ))
    (hgap :
      ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
        ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y)) :
    ∃ m : ℝ,
      m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
      φ x ≥ φ y + m * (x - y) + (μ / 2) * (x - y) ^ (2 : ℕ) ∧
      φ z ≥ φ y + m * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ) := by
  let L : ℝ := ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x)
  let U : ℝ := ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y)
  have hxy_gap : 0 < y - x := sub_pos.mpr hxy
  have hyz_gap : 0 < z - y := sub_pos.mpr hyz
  have hL : L ≤ mL := by
    -- The left quadratic tangent means every admissible shared slope must lie at or above `L`.
    simpa [L] using
      leftSecantThreshold_le_of_subgradientLowerTangentQuadratic
        (φ := φ) (μ := μ) (m := mL) hxy hxquad
  have hU : mR ≤ U := by
    -- The right quadratic tangent means every admissible shared slope must lie at or below `U`.
    simpa [U] using
      subgradientLowerTangentQuadratic_le_rightSecantThreshold
        (φ := φ) (μ := μ) (m := mR) hyz hzquad
  by_cases hmLU : mL ≤ U
  · -- If the left witness already lies below the right threshold, it works at both endpoints.
    refine ⟨mL, hmLSub, hxquad, ?_⟩
    have hmL_div :
        mL + (μ / 2) * (z - y) ≤ (φ z - φ y) / (z - y) := by
      dsimp [U] at hmLU
      linarith
    have hmL_mul :
        mL * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ) ≤ φ z - φ y := by
      have hmul := (le_div_iff₀ hyz_gap).1 hmL_div
      nlinarith
    linarith
  · -- Route correction: instead of searching for a new slope directly, use convexity of the
    -- scalar subdifferential interval to show the threshold value `U` itself is a subgradient.
    have hsubConv :
        Convex ℝ (∂ (fun u ↦ (φ u : WithTop ℝ))(y)) :=
      convex_subdifferential_coe_real_at (f := φ) y
    have hUle : U ≤ mL := (lt_of_not_ge hmLU).le
    have hUSub : U ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) := by
      exact hsubConv.ordConnected.out hmRSub hmLSub ⟨hU, hUle⟩
    refine ⟨U, hUSub, ?_, ?_⟩
    · -- The secant-gap lemma makes the threshold `U` large enough for the left endpoint.
      have hleft_div :
          (φ y - φ x) / (y - x) ≤ U - (μ / 2) * (y - x) := by
        dsimp [U]
        linarith
      have hleft_mul :
          φ y - φ x ≤ U * (y - x) - (μ / 2) * (y - x) ^ (2 : ℕ) := by
        have hmul := (div_le_iff₀ hxy_gap).1 hleft_div
        nlinarith
      linarith
    · -- The right endpoint inequality is exactly the defining equality of `U`.
      have hU_mul :
          U * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ) = φ z - φ y := by
        dsimp [U]
        have hyz_ne : z - y ≠ 0 := sub_ne_zero.mpr hyz.ne.symm
        field_simp [hyz_ne]
        ring
      linarith

/-- Helper for Definition 6.37: the corrected left secant threshold at base `t` is exactly the
adjacent secant of the shifted scalar slice, translated by the common term `μ * t`. -/
lemma correctedLeftSecantThreshold_eq_shiftedScalarSlope_add_muBase
    {φ : ℝ → ℝ} {μ s t : ℝ} (hst : s ≠ t) :
    ((φ t - φ s) / (t - s)) + (μ / 2) * (t - s) =
      (((φ t - (μ / 2) * t ^ (2 : ℕ)) - (φ s - (μ / 2) * s ^ (2 : ℕ))) / (t - s)) + μ * t := by
  -- Normalize the left corrected threshold through the shifted-slope identity, then cancel the
  -- common `μ * t` term by scalar algebra once.
  rw [shiftedScalarSlope_eq_originalSlope_sub_halfMuSum
      (φ := φ) (μ := μ) (x := s) (y := t) hst]
  ring

/-- Helper for Definition 6.37: the corrected right secant threshold at base `t` is the adjacent
secant of the same shifted scalar slice, again translated by the common term `μ * t`. -/
lemma correctedRightSecantThreshold_eq_shiftedScalarSlope_add_muBase
    {φ : ℝ → ℝ} {μ t s : ℝ} (hts : t ≠ s) :
    ((φ s - φ t) / (s - t)) - (μ / 2) * (s - t) =
      (((φ s - (μ / 2) * s ^ (2 : ℕ)) - (φ t - (μ / 2) * t ^ (2 : ℕ))) / (s - t)) + μ * t := by
  -- The right corrected threshold is the same shifted secant with the same base-dependent
  -- translation term, so the comparison reduces to ordinary shifted adjacent-slope monotonicity.
  rw [shiftedScalarSlope_eq_originalSlope_sub_halfMuSum
      (φ := φ) (μ := μ) (x := t) (y := s) hts]
  ring

/-- Helper for Definition 6.37: the strict mixed corrected-threshold overlap is equivalent to the
ordinary adjacent-slope monotonicity of the shifted scalar slice
`r ↦ φ r - (μ / 2) * r²`. -/
lemma correctedSecantThresholdOverlap_iff_shiftedSlopeMonotone
    {φ : ℝ → ℝ} {μ s₁ t s₂ : ℝ}
    (hs₁ : s₁ < t) (ht₂ : t < s₂) :
    (((φ t - φ s₁) / (t - s₁)) + (μ / 2) * (t - s₁) ≤
        ((φ s₂ - φ t) / (s₂ - t)) - (μ / 2) * (s₂ - t)) ↔
      (((φ t - (μ / 2) * t ^ (2 : ℕ)) - (φ s₁ - (μ / 2) * s₁ ^ (2 : ℕ))) / (t - s₁) ≤
        ((φ s₂ - (μ / 2) * s₂ ^ (2 : ℕ)) - (φ t - (μ / 2) * t ^ (2 : ℕ))) / (s₂ - t)) := by
  -- Both corrected thresholds differ from the corresponding shifted secants by the same additive
  -- constant `μ * t`, so the overlap comparison is exactly the shifted adjacent-slope inequality.
  rw [correctedLeftSecantThreshold_eq_shiftedScalarSlope_add_muBase
        (φ := φ) (μ := μ) (s := s₁) (t := t) hs₁.ne,
      correctedRightSecantThreshold_eq_shiftedScalarSlope_add_muBase
        (φ := φ) (μ := μ) (t := t) (s := s₂) ht₂.ne]
  constructor <;> intro h <;> linarith

/-- Helper for Definition 6.37: for three ordered scalar points, adjacent secant monotonicity of
`ψ` is equivalent to the denominator-free weighted-chord inequality at the middle point. -/
lemma shiftedSecantMonotone_iff_weightedChord
    {ψ : ℝ → ℝ} {s₁ t s₂ : ℝ}
    (hs₁ : s₁ < t) (ht₂ : t < s₂) :
    ((ψ t - ψ s₁) / (t - s₁) ≤ (ψ s₂ - ψ t) / (s₂ - t)) ↔
      (s₂ - s₁) * ψ t ≤ (s₂ - t) * ψ s₁ + (t - s₁) * ψ s₂ := by
  have hΔ1 : 0 < t - s₁ := sub_pos.mpr hs₁
  have hΔ2 : 0 < s₂ - t := sub_pos.mpr ht₂
  constructor
  · intro hsec
    -- Cross-multiply the two positive denominators once and collapse the result to the weighted
    -- chord normal form.
    have hcross :
        (ψ t - ψ s₁) * (s₂ - t) ≤ (ψ s₂ - ψ t) * (t - s₁) :=
      (div_le_div_iff₀ hΔ1 hΔ2).1 hsec
    have hweighted :
        (s₂ - s₁) * ψ t ≤ (s₂ - t) * ψ s₁ + (t - s₁) * ψ s₂ := by
      linarith
    exact hweighted
  · intro hweighted
    -- Undo the same algebra and divide back by the positive secant denominators.
    have hcross :
        (ψ t - ψ s₁) * (s₂ - t) ≤ (ψ s₂ - ψ t) * (t - s₁) := by
      linarith
    exact (div_le_div_iff₀ hΔ1 hΔ2).2 hcross

/-- Helper for Definition 6.37: the endpoint-extremal route already produces a coarse overlap
interval inside the scalar subdifferential at the middle point `t`. -/
lemma endpointExtremaCoarseOverlap_of_pairwiseSupportAndQuadraticTriple
    {φ : ℝ → ℝ} {μ : ℝ} {s₁ t s₂ mLeft mRight : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    (hs₁ : s₁ < t) (ht₂ : t < s₂)
    (hmLeftSub : mLeft ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(s₁))
    (hmLeftLeast :
      ∀ g : ℝ, g ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(s₁) → mLeft ≤ g)
    (hmRightSub : mRight ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(s₂))
    (hmRightGreatest :
      ∀ g : ℝ, g ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(s₂) → g ≤ mRight) :
    ∃ m : ℝ,
      m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(t) ∧
      mLeft + μ * (t - s₁) ≤ m ∧
      m ≤ mRight - μ * (s₂ - t) := by
  rcases
      existsMiddleSubgradient_leftQuadratic_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair (x := s₁) (y := t) with
    ⟨mL, hmLSub, hs₁quad⟩
  rcases
      existsMiddleSubgradient_rightQuadratic_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair (y := t) (z := s₂) with
    ⟨mR, hmRSub, hs₂quad⟩
  have hLeftAtMiddle :
      φ t ≥ φ s₁ + mLeft * (t - s₁) + (μ / 2) * (t - s₁) ^ (2 : ℕ) := by
    -- The least subgradient at `s₁` preserves every quadratic lower tangent to its right.
    exact
      leastScalarSubgradient_lowerTangentQuadratic_right_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair hs₁.le hmLeftSub hmLeftLeast
  have hRightAtMiddle :
      φ t ≥ φ s₂ + mRight * (t - s₂) + (μ / 2) * (t - s₂) ^ (2 : ℕ) := by
    -- The greatest subgradient at `s₂` preserves every quadratic lower tangent to its left.
    exact
      greatestScalarSubgradient_lowerTangentQuadratic_left_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair ht₂.le hmRightSub hmRightGreatest
  have hLeftAtRight :
      φ s₂ ≥ φ s₁ + mLeft * (s₂ - s₁) + (μ / 2) * (s₂ - s₁) ^ (2 : ℕ) := by
    -- Reuse the same least endpoint subgradient for the farther point `s₂`.
    exact
      leastScalarSubgradient_lowerTangentQuadratic_right_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair (le_of_lt (lt_trans hs₁ ht₂)) hmLeftSub hmLeftLeast
  have hRightAtLeft :
      φ s₁ ≥ φ s₂ + mRight * (s₁ - s₂) + (μ / 2) * (s₁ - s₂) ^ (2 : ℕ) := by
    -- Reuse the same greatest endpoint subgradient for the farther point `s₁`.
    exact
      greatestScalarSubgradient_lowerTangentQuadratic_left_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair (le_of_lt (lt_trans hs₁ ht₂)) hmRightSub hmRightGreatest
  have hleftGap :
      μ * (t - s₁) ≤ mL - mLeft := by
    -- Compare the left-endpoint quadratic tangent coming from `mL` with the canonical one coming
    -- from the least subgradient at `s₁`.
    nlinarith [hs₁quad, hLeftAtMiddle]
  have hrightGap :
      μ * (s₂ - t) ≤ mRight - mR := by
    -- Compare the right-endpoint quadratic tangent coming from `mR` with the canonical one coming
    -- from the greatest subgradient at `s₂`.
    nlinarith [hs₂quad, hRightAtMiddle]
  have hwideGap :
      μ * (s₂ - s₁) ≤ mRight - mLeft := by
    -- The endpoint extrema already control the full interval `[s₁, s₂]`.
    nlinarith [hLeftAtRight, hRightAtLeft]
  have hleftCoarse :
      mLeft + μ * (t - s₁) ≤ mL := by
    -- The left endpoint witness already lies above the coarse lower edge forced by `mLeft`.
    nlinarith [hleftGap]
  have hrightCoarse :
      mR ≤ mRight - μ * (s₂ - t) := by
    -- The right endpoint witness already lies below the coarse upper edge forced by `mRight`.
    nlinarith [hrightGap]
  have hcoarseGap :
      mLeft + μ * (t - s₁) ≤ mRight - μ * (s₂ - t) := by
    -- The endpoint-extremal comparison shows that this coarse middle-slope interval is nonempty.
    nlinarith [hwideGap]
  -- Use convexity of the scalar subdifferential interval at `t` once the coarse bounds overlap.
  exact
    subgradientIntervalWitness_of_bounds
      (φ := φ) (y := t) (L := mLeft + μ * (t - s₁)) (U := mRight - μ * (s₂ - t))
      (mInf := mR) (mSup := mL) hmRSub hmLSub hrightCoarse hleftCoarse hcoarseGap

/-- Helper for Definition 6.37: one common middle-point quadratic lower tangent already forces the
exact corrected secant-gap inequality. -/
lemma correctedSecantGap_of_sharedMiddleLowerTangentQuadratic
    {φ : ℝ → ℝ} {μ x y z m : ℝ}
    (hxy : x < y) (hyz : y < z)
    (hxquad : φ x ≥ φ y + m * (x - y) + (μ / 2) * (x - y) ^ (2 : ℕ))
    (hzquad : φ z ≥ φ y + m * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ)) :
    ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
      ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
  -- Normalize the left endpoint tangent into the corrected left threshold.
  have hleft :
      ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤ m := by
    simpa using
      leftSecantThreshold_le_of_subgradientLowerTangentQuadratic
        (φ := φ) (μ := μ) (m := m) hxy hxquad
  -- Normalize the right endpoint tangent into the corrected right threshold.
  have hright :
      m ≤ ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
    simpa using
      subgradientLowerTangentQuadratic_le_rightSecantThreshold
        (φ := φ) (μ := μ) (m := m) hyz hzquad
  exact le_trans hleft hright

/-- Helper for Definition 6.37: after the corrected-threshold normalization, the remaining scalar
frontier is the shifted adjacent-secant comparison on one strict triple `s₁ < t < s₂`. -/
lemma shiftedAdjacentSecantMonotone_of_pairwiseSupportAndQuadraticTriple
    {φ : ℝ → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {s₁ t s₂ : ℝ}
    (hs₁ : s₁ < t) (ht₂ : t < s₂) :
    (((φ t - (μ / 2) * t ^ (2 : ℕ)) - (φ s₁ - (μ / 2) * s₁ ^ (2 : ℕ))) / (t - s₁) ≤
      ((φ s₂ - (μ / 2) * s₂ ^ (2 : ℕ)) - (φ t - (μ / 2) * t ^ (2 : ℕ))) / (s₂ - t)) := by
  have _ := hμ
  have hconv : ConvexOn ℝ Set.univ φ :=
    scalarConvexOnUniv_of_pairwiseSupportAndQuadratic (φ := φ) (μ := μ) hpair
  have hφcont : ContinuousAt φ t := by
    -- Convex real-valued functions are continuous on the open whole space.
    simpa [continuousWithinAt_univ] using
      (hconv.continuousOn isOpen_univ t (by simp : t ∈ (Set.univ : Set ℝ)))
  let leftThresholdNear : ℝ → ℝ :=
    fun y ↦ ((φ y - φ s₁) / (y - s₁)) + (μ / 2) * (y - s₁)
  let rightThresholdNear : ℝ → ℝ :=
    fun y ↦ ((φ s₂ - φ y) / (s₂ - y)) - (μ / 2) * (s₂ - y)
  have hleftCont : ContinuousAt leftThresholdNear t := by
    -- The left corrected threshold has a genuine limit at `t` because its denominator stays away
    -- from zero near `t`.
    dsimp [leftThresholdNear]
    exact
      ((hφcont.sub continuousAt_const).div
          (continuousAt_id.sub continuousAt_const)
          (by simpa using sub_ne_zero.mpr hs₁.ne.symm)).add
        (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))
  have hrightCont : ContinuousAt rightThresholdNear t := by
    -- The right corrected threshold is continuous at `t` for the same reason.
    dsimp [rightThresholdNear]
    exact
      ((continuousAt_const.sub hφcont).div
          (continuousAt_const.sub continuousAt_id)
          (by simpa using sub_ne_zero.mpr ht₂.ne.symm)).sub
        (continuousAt_const.mul (continuousAt_const.sub continuousAt_id))
  have hleftEventually :
      ∀ᶠ y in nhdsWithin t (Set.Iio t), leftThresholdNear y ≤ derivWithin φ (Set.Iio t) t := by
    filter_upwards [inter_mem_nhdsWithin (Set.Iio t) (Ioi_mem_nhds hs₁)] with y hy
    have hs₁y : s₁ < y := hy.2
    have hyt : y < t := hy.1
    have hsecant :
        leftThresholdNear y ≤ (φ t - φ y) / (t - y) := by
      rcases
          existsMiddleSubgradient_leftQuadratic_of_pairwiseSupportAndQuadratic
            (φ := φ) (μ := μ) hpair (x := s₁) (y := y) with
        ⟨m, hmSub, hs₁quad⟩
      have hleft :
          leftThresholdNear y ≤ m := by
        -- Normalize the left-endpoint quadratic tangent into the corrected left threshold.
        simpa [leftThresholdNear] using
          leftSecantThreshold_le_of_subgradientLowerTangentQuadratic
            (φ := φ) (μ := μ) (m := m) hs₁y hs₁quad
      have hright :
          m ≤ (φ t - φ y) / (t - y) := by
        -- Any middle-point subgradient is an affine support slope at the right endpoint `t`.
        have hsupport :
            φ t ≥ φ y + m * (t - y) := by
          have hsupportInner := mem_subdifferential_coe_real_iff.mp hmSub t
          have hinner : inner ℝ m (t - y) = m * (t - y) := by
            calc
              inner ℝ m (t - y) = inner ℝ (t - y) m := by rw [real_inner_comm]
              _ = m * (starRingEnd ℝ) (t - y) := RCLike.inner_apply (t - y) m
              _ = m * (t - y) := by simp
          rwa [hinner] at hsupportInner
        exact
          le_rightSecant_of_lowerAffineAtPoint
            (ψ := φ) (y := y) (z := t) (m := m) hyt hsupport
      exact le_trans hleft hright
    have hslope :
        (φ t - φ y) / (t - y) ≤ derivWithin φ (Set.Iio t) t := by
      -- Any left secant into `t` is bounded above by the left derivative of a convex function.
      simpa [slope_def_field] using
        hconv.slope_le_leftDeriv_of_mem_interior
          (x := y) (y := t) (hys := by simp) (hxs := by simp) hyt
    exact le_trans hsecant hslope
  have hrightEventually :
      ∀ᶠ y in nhdsWithin t (Set.Ioi t), derivWithin φ (Set.Ioi t) t ≤ rightThresholdNear y := by
    filter_upwards [inter_mem_nhdsWithin (Set.Ioi t) (Iio_mem_nhds ht₂)] with y hy
    have hty : t < y := hy.1
    have hy₂ : y < s₂ := hy.2
    have hslope :
        derivWithin φ (Set.Ioi t) t ≤ (φ y - φ t) / (y - t) := by
      -- Any right secant out of `t` is bounded below by the right derivative of a convex function.
      simpa [slope_def_field] using
        hconv.rightDeriv_le_slope_of_mem_interior
          (x := t) (y := y) (hxs := by simp) (hys := by simp) hty
    have hsecant :
        (φ y - φ t) / (y - t) ≤ rightThresholdNear y := by
      rcases
          existsMiddleSubgradient_rightQuadratic_of_pairwiseSupportAndQuadratic
            (φ := φ) (μ := μ) hpair (y := y) (z := s₂) with
        ⟨m, hmSub, hs₂quad⟩
      have hleft :
          (φ y - φ t) / (y - t) ≤ m := by
        -- Any middle-point subgradient is an affine support slope at the left endpoint `t`.
        have hsupport :
            φ t ≥ φ y + m * (t - y) := by
          have hsupportInner := mem_subdifferential_coe_real_iff.mp hmSub t
          have hinner : inner ℝ m (t - y) = m * (t - y) := by
            calc
              inner ℝ m (t - y) = inner ℝ (t - y) m := by rw [real_inner_comm]
              _ = m * (starRingEnd ℝ) (t - y) := RCLike.inner_apply (t - y) m
              _ = m * (t - y) := by simp
          rwa [hinner] at hsupportInner
        exact
          leftSecant_le_of_lowerAffineAtPoint
            (ψ := φ) (x := t) (y := y) (m := m) hty hsupport
      have hright :
          m ≤ rightThresholdNear y := by
        -- Normalize the right-endpoint quadratic tangent into the corrected right threshold.
        simpa [rightThresholdNear] using
          subgradientLowerTangentQuadratic_le_rightSecantThreshold
            (φ := φ) (μ := μ) (m := m) hy₂ hs₂quad
      exact le_trans hleft hright
    exact le_trans hslope hsecant
  have hleftDeriv :
      leftThresholdNear t ≤ derivWithin φ (Set.Iio t) t := by
    -- Passing to the left-limit keeps the corrected threshold below the left derivative.
    exact le_of_tendsto hleftCont.continuousWithinAt.tendsto hleftEventually
  have hrightDeriv :
      derivWithin φ (Set.Ioi t) t ≤ rightThresholdNear t := by
    -- Passing to the right-limit keeps the right derivative below the corrected threshold.
    exact ge_of_tendsto hrightCont.continuousWithinAt.tendsto hrightEventually
  have hderivOrder :
      derivWithin φ (Set.Iio t) t ≤ derivWithin φ (Set.Ioi t) t := by
    -- Ordinary convexity orders the one-sided derivatives at the middle point.
    simpa using hconv.leftDeriv_le_rightDeriv_of_mem_interior (x := t) (by simp)
  -- Route correction: prove the exact corrected-threshold overlap numerically via the one-sided
  -- derivative sandwich, then translate back to the shifted adjacent-secant inequality.
  refine
    (correctedSecantThresholdOverlap_iff_shiftedSlopeMonotone
      (φ := φ) (μ := μ) hs₁ ht₂).1 ?_
  have hgap :
      leftThresholdNear t ≤ rightThresholdNear t := by
    exact le_trans hleftDeriv (le_trans hderivOrder hrightDeriv)
  simpa [leftThresholdNear, rightThresholdNear] using hgap

/-- Helper for Definition 6.37: in the strict mixed branch with `0 ≤ μ`, the remaining frontier
is the corrected secant-threshold overlap at the fixed base point. -/
lemma strictMixedSecantThresholdOverlap_nonneg_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {s₁ t s₂ : ℝ}
    (hs₁ : s₁ < t) (ht₂ : t < s₂) :
    ((φ t - φ s₁) / (t - s₁)) + (μ / 2) * (t - s₁) ≤
      ((φ s₂ - φ t) / (s₂ - t)) - (μ / 2) * (s₂ - t) := by
  -- Route correction: isolate the true frontier as one shifted-slice secant comparison, then
  -- translate that comparison back through the repaired corrected-threshold equivalence.
  have hshiftedGoal :
      (((φ t - (μ / 2) * t ^ (2 : ℕ)) - (φ s₁ - (μ / 2) * s₁ ^ (2 : ℕ))) / (t - s₁) ≤
        ((φ s₂ - (μ / 2) * s₂ ^ (2 : ℕ)) - (φ t - (μ / 2) * t ^ (2 : ℕ))) / (s₂ - t)) :=
    shiftedAdjacentSecantMonotone_of_pairwiseSupportAndQuadraticTriple
      (φ := φ) (μ := μ) hμ hpair hs₁ ht₂
  exact
    (correctedSecantThresholdOverlap_iff_shiftedSlopeMonotone
      (φ := φ) (μ := μ) hs₁ ht₂).2 hshiftedGoal

/-- Helper for Definition 6.37: after the easy one-sided branches are removed, the only unresolved
fixed-base compatibility problem is the strict mixed case `s₁ < t < s₂`. -/
lemma scalarAdmissibleSlopePair_nonempty_strictMixed_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {s₁ t s₂ : ℝ}
    (hs₁ : s₁ < t) (ht₂ : t < s₂) :
    ∃ g ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(t),
      φ s₁ ≥ φ t + g * (s₁ - t) + (μ / 2) * (s₁ - t) ^ (2 : ℕ) ∧
      φ s₂ ≥ φ t + g * (s₂ - t) + (μ / 2) * (s₂ - t) ^ (2 : ℕ) := by
  rcases
      existsMiddleSubgradient_leftQuadratic_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair (x := s₁) (y := t) with
    ⟨mL, hmLSub, hs₁quad⟩
  rcases
      existsMiddleSubgradient_rightQuadratic_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair (y := t) (z := s₂) with
    ⟨mR, hmRSub, hs₂quad⟩
  by_cases hμ : 0 ≤ μ
  · -- Route correction: once the strict mixed corrected gap is proved, the shared witness comes
    -- from the stable interval-selection argument on the scalar subdifferential interval.
    have hgap :
        ((φ t - φ s₁) / (t - s₁)) + (μ / 2) * (t - s₁) ≤
          ((φ s₂ - φ t) / (s₂ - t)) - (μ / 2) * (s₂ - t) :=
      strictMixedSecantThresholdOverlap_nonneg_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hμ hpair hs₁ ht₂
    exact
      existsSharedSubgradient_of_secantGap
        hs₁ ht₂ hmLSub hmRSub hs₁quad hs₂quad hgap
  · -- When `μ ≤ 0`, ordinary convex secant monotonicity already implies the corrected overlap.
    have hconv : ConvexOn ℝ Set.univ φ :=
      scalarConvexOnUniv_of_pairwiseSupportAndQuadratic (φ := φ) (μ := μ) hpair
    have hordinary :
        (φ t - φ s₁) / (t - s₁) ≤ (φ s₂ - φ t) / (s₂ - t) := by
      simpa using
        hconv.slope_mono_adjacent
          (x := s₁) (y := t) (z := s₂) (by simp) (by simp) hs₁ ht₂
    have hμ_nonpos : μ ≤ 0 := le_of_not_ge hμ
    have hgap :
        ((φ t - φ s₁) / (t - s₁)) + (μ / 2) * (t - s₁) ≤
          ((φ s₂ - φ t) / (s₂ - t)) - (μ / 2) * (s₂ - t) := by
      nlinarith [hordinary, hμ_nonpos, sub_nonneg.mpr hs₁.le, sub_nonneg.mpr ht₂.le]
    exact
      existsSharedSubgradient_of_secantGap
        hs₁ ht₂ hmLSub hmRSub hs₁quad hs₂quad hgap

/-- Helper for Definition 6.37: at a fixed base point, every pair of comparison points already has
one scalar subgradient whose quadratic lower tangents work at both points; only the strict mixed
case requires an additional interval-overlap argument. -/
lemma scalarAdmissibleSlopePair_nonempty_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {s₁ t s₂ : ℝ} :
    ∃ g ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(t),
      φ s₁ ≥ φ t + g * (s₁ - t) + (μ / 2) * (s₁ - t) ^ (2 : ℕ) ∧
      φ s₂ ≥ φ t + g * (s₂ - t) + (μ / 2) * (s₂ - t) ^ (2 : ℕ) := by
  have hconv : ConvexOn ℝ Set.univ φ :=
    scalarConvexOnUniv_of_pairwiseSupportAndQuadratic (φ := φ) (μ := μ) hpair
  rcases existsGreatestScalarSubgradient_of_convexOnUniv hconv t with
    ⟨mSup, hmSupSub, hmSupGreatest⟩
  rcases existsLeastScalarSubgradient_of_convexOnUniv hconv t with
    ⟨mInf, hmInfSub, hmInfLeast⟩
  by_cases hs₁_left : s₁ ≤ t
  · by_cases hs₂_left : s₂ ≤ t
    · refine ⟨mSup, hmSupSub, ?_, ?_⟩
      · -- If both points lie on the left, the greatest middle subgradient works for both.
        exact
          greatestScalarSubgradient_lowerTangentQuadratic_left_of_pairwiseSupportAndQuadratic
            (φ := φ) (μ := μ) hpair hs₁_left hmSupSub hmSupGreatest
      · -- Reuse the same maximal slope for the second left comparison point.
        exact
          greatestScalarSubgradient_lowerTangentQuadratic_left_of_pairwiseSupportAndQuadratic
            (φ := φ) (μ := μ) hpair hs₂_left hmSupSub hmSupGreatest
    · have ht₂ : t ≤ s₂ := le_of_not_ge hs₂_left
      rcases lt_or_eq_of_le hs₁_left with hs₁_lt | rfl
      · rcases lt_or_eq_of_le ht₂ with ht₂_lt | rfl
        · -- The only genuinely open branch is the strict left/right split across `t`.
          exact
            scalarAdmissibleSlopePair_nonempty_strictMixed_of_pairwiseSupportAndQuadratic
              (φ := φ) (μ := μ) hpair hs₁_lt ht₂_lt
        · refine ⟨mSup, hmSupSub, ?_, ?_⟩
          · exact
              greatestScalarSubgradient_lowerTangentQuadratic_left_of_pairwiseSupportAndQuadratic
                (φ := φ) (μ := μ) hpair hs₁_left hmSupSub hmSupGreatest
          · -- The second comparison point is the base point itself, so the tangent is tautological.
            simp
      · refine ⟨mInf, hmInfSub, ?_, ?_⟩
        · -- The first comparison point is the base point itself, so the tangent is tautological.
          simp
        · exact
            leastScalarSubgradient_lowerTangentQuadratic_right_of_pairwiseSupportAndQuadratic
              (φ := φ) (μ := μ) hpair ht₂ hmInfSub hmInfLeast
  · have ht₁ : t ≤ s₁ := le_of_not_ge hs₁_left
    by_cases hs₂_left : s₂ ≤ t
    · rcases lt_or_eq_of_le hs₂_left with hs₂_lt | rfl
      · rcases lt_or_eq_of_le ht₁ with ht₁_lt | rfl
        · rcases
              scalarAdmissibleSlopePair_nonempty_strictMixed_of_pairwiseSupportAndQuadratic
                (φ := φ) (μ := μ) hpair hs₂_lt ht₁_lt with
            ⟨g, hgSub, hg₂, hg₁⟩
          -- Swap the two comparison points after solving the strict mixed case
          -- in the canonical order.
          exact ⟨g, hgSub, hg₁, hg₂⟩
        · refine ⟨mSup, hmSupSub, ?_, ?_⟩
          · -- The first comparison point is the base point itself, so the tangent is tautological.
            simp
          · exact
              greatestScalarSubgradient_lowerTangentQuadratic_left_of_pairwiseSupportAndQuadratic
                (φ := φ) (μ := μ) hpair hs₂_left hmSupSub hmSupGreatest
      · refine ⟨mInf, hmInfSub, ?_, ?_⟩
        · exact
            leastScalarSubgradient_lowerTangentQuadratic_right_of_pairwiseSupportAndQuadratic
              (φ := φ) (μ := μ) hpair ht₁ hmInfSub hmInfLeast
        · -- The second comparison point is the base point itself, so the tangent is tautological.
          simp
    · have ht₂ : t ≤ s₂ := le_of_not_ge hs₂_left
      refine ⟨mInf, hmInfSub, ?_, ?_⟩
      · -- If both points lie on the right, the least middle subgradient works for both.
        exact
          leastScalarSubgradient_lowerTangentQuadratic_right_of_pairwiseSupportAndQuadratic
            (φ := φ) (μ := μ) hpair ht₁ hmInfSub hmInfLeast
      · -- Reuse the same minimal slope for the second right comparison point.
        exact
          leastScalarSubgradient_lowerTangentQuadratic_right_of_pairwiseSupportAndQuadratic
            (φ := φ) (μ := μ) hpair ht₂ hmInfSub hmInfLeast

/-- Helper for Definition 6.37: once the scalar pairwise witnesses are collapsed to one fixed
subgradient at each base point, the shifted slice becomes convex. -/
lemma shiftedScalarSliceConvexOn_of_fixedSubgradientLowerTangentQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hμ : 0 < μ)
    (hfixed :
      ∀ t : ℝ,
        ∃ g ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(t),
          ∀ s : ℝ,
            φ s ≥ φ t + g * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ)) :
    ConvexOn ℝ Set.univ (fun r ↦ φ r - (μ / 2) * r ^ (2 : ℕ)) := by
  have hfixedInner :
      ∀ t : ℝ,
        ∃ g ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(t),
          ∀ s : ℝ,
            φ s ≥ φ t + inner ℝ g (s - t) + (μ / 2) * ‖s - t‖ ^ (2 : ℕ) := by
    intro t
    rcases hfixed t with ⟨g, hg, hgquad⟩
    refine ⟨g, hg, ?_⟩
    intro s
    -- Normalize the scalar inner product and squared norm to the polynomial form used above.
    have hinner : inner ℝ g (s - t) = g * (s - t) := by
      calc
        inner ℝ g (s - t) = inner ℝ (s - t) g := by rw [real_inner_comm]
        _ = g * (starRingEnd ℝ) (s - t) := RCLike.inner_apply (s - t) g
        _ = g * (s - t) := by simp
    have hnorm : ‖s - t‖ ^ (2 : ℕ) = (s - t) ^ (2 : ℕ) := by
      rw [Real.norm_eq_abs, sq_abs]
    rw [hinner, hnorm]
    exact hgquad s
  have hmem :
      φ ∈ 𝒮^0_μ(Set.univ) :=
    mem_S0On_univ_of_exists_subgradient_lower_tangent_quadratic_fixed
      (σ := μ) (f := φ) hμ hfixedInner
  rcases mem_S0On_iff.mp hmem with ⟨-, hstrong⟩
  -- Switch from the owner `StrongConvexOn` back to convexity of the shifted scalar slice.
  simpa [Real.norm_eq_abs, sq_abs] using (strongConvexOn_iff_convex.mp hstrong)

/-- Helper for Definition 6.37: monotonicity of the corrected adjacent secants is already enough
to recover convexity of the shifted scalar slice on `Set.univ`. -/
lemma shiftedScalarSliceConvexOn_of_correctedAdjacentSecants
    {φ : ℝ → ℝ} {μ : ℝ}
    (hgap :
      ∀ {x y z : ℝ}, x < y → y < z →
        ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
          ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y)) :
    ConvexOn ℝ Set.univ (fun r ↦ φ r - (μ / 2) * r ^ (2 : ℕ)) := by
  let ψ : ℝ → ℝ := fun r ↦ φ r - (μ / 2) * r ^ (2 : ℕ)
  refine convexOn_of_slope_mono_adjacent convex_univ ?_
  intro x y z hx hz hxy hyz
  -- Rewrite the adjacent slopes of the shifted slice into the corrected secants of `φ`.
  have hslope :
      (ψ y - ψ x) / (y - x) ≤ (ψ z - ψ y) / (z - y) := by
    have hgap' := hgap hxy hyz
    rw [shiftedScalarSlope_eq_originalSlope_sub_halfMuSum
          (φ := φ) (μ := μ) (x := x) (y := y) hxy.ne,
        shiftedScalarSlope_eq_originalSlope_sub_halfMuSum
          (φ := φ) (μ := μ) (x := y) (y := z) hyz.ne]
    linarith
  simpa [ψ] using hslope

/-- Helper for Definition 6.37: the left endpoint quadratic tangent already forces the corrected
left secant threshold to lie below the ordinary right secant. -/
lemma leftCorrectedSecant_le_rightSecant_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
      (φ z - φ y) / (z - y) := by
  rcases
      existsMiddleSubgradient_leftQuadratic_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair (x := x) (y := y) with
    ⟨m, hmSub, hxquad⟩
  have hleft :
      ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤ m := by
    -- Normalize the left-endpoint quadratic tangent into the corrected left threshold.
    simpa using
      leftSecantThreshold_le_of_subgradientLowerTangentQuadratic
        (φ := φ) (μ := μ) (m := m) hxy hxquad
  have hright :
      m ≤ (φ z - φ y) / (z - y) := by
    -- Every middle-point subgradient is an affine support slope at the right endpoint.
    have hsupport :
        φ z ≥ φ y + m * (z - y) := by
      have hsupportInner := mem_subdifferential_coe_real_iff.mp hmSub z
      have hinner : inner ℝ m (z - y) = m * (z - y) := by
        calc
          inner ℝ m (z - y) = inner ℝ (z - y) m := by rw [real_inner_comm]
          _ = m * (starRingEnd ℝ) (z - y) := RCLike.inner_apply (z - y) m
          _ = m * (z - y) := by simp
      rwa [hinner] at hsupportInner
    exact
      le_rightSecant_of_lowerAffineAtPoint
        (ψ := φ) (y := y) (z := z) (m := m) hyz
        hsupport
  linarith

/-- Helper for Definition 6.37: the ordinary left secant already lies below the corrected right
secant threshold coming from the right endpoint quadratic tangent. -/
lemma leftSecant_le_rightCorrectedSecant_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    (φ y - φ x) / (y - x) ≤
      ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
  rcases
      existsMiddleSubgradient_rightQuadratic_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair (y := y) (z := z) with
    ⟨m, hmSub, hzquad⟩
  have hleft :
      (φ y - φ x) / (y - x) ≤ m := by
    -- Every middle-point subgradient is an affine support slope at the left endpoint.
    have hsupport :
        φ x ≥ φ y + m * (x - y) := by
      have hsupportInner := mem_subdifferential_coe_real_iff.mp hmSub x
      have hinner : inner ℝ m (x - y) = m * (x - y) := by
        calc
          inner ℝ m (x - y) = inner ℝ (x - y) m := by rw [real_inner_comm]
          _ = m * (starRingEnd ℝ) (x - y) := RCLike.inner_apply (x - y) m
          _ = m * (x - y) := by simp
      rwa [hinner] at hsupportInner
    exact
      leftSecant_le_of_lowerAffineAtPoint
        (ψ := φ) (x := x) (y := y) (m := m) hxy
        hsupport
  have hright :
      m ≤ ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
    -- Normalize the right-endpoint quadratic tangent into the corrected right threshold.
    simpa using
      subgradientLowerTangentQuadratic_le_rightSecantThreshold
        (φ := φ) (μ := μ) (m := m) hyz hzquad
  linarith

/-- Helper for Definition 6.37: the remaining scalar frontier is the pure secant-gap inequality
`L ≤ U`, isolated from the later subgradient interval-selection step. -/
lemma quadraticSecantGap_of_fixedSubgradientLowerTangentQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hfixed :
      ∀ t : ℝ,
        ∃ g ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(t),
          ∀ s : ℝ,
            φ s ≥ φ t + g * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
      ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
  by_cases hμ0 : μ = 0
  · subst μ
    have hpair0 :
        ∀ s t : ℝ,
          ∃ m : ℝ,
            (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
            φ s ≥ φ t + m * (s - t) + ((0 : ℝ) / 2) * (s - t) ^ (2 : ℕ) := by
      intro s t
      rcases hfixed t with ⟨g, hg, hgall⟩
      refine ⟨g, ?_, ?_⟩
      · -- The fixed witness at `t` already gives a global affine support slope when `μ = 0`.
        intro u
        simpa using hgall u
      · -- The comparison-point inequality is just the same fixed witness specialized to `s`.
        simpa using hgall s
    have hconv : ConvexOn ℝ Set.univ φ :=
      scalarConvexOnUniv_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := (0 : ℝ)) hpair0
    -- With zero modulus, the desired gap is exactly ordinary adjacent secant monotonicity.
    have hshifted0 : ConvexOn ℝ Set.univ (fun r ↦ φ r - ((0 : ℝ) / 2) * r ^ (2 : ℕ)) := by
      simpa using hconv
    simpa using
      quadraticSecantGap_of_shiftedConvexOn
        (φ := φ) (μ := (0 : ℝ)) hshifted0 hxy hyz
  · have hμ0' : 0 ≠ μ := by
      simpa [eq_comm] using hμ0
    have hμpos : 0 < μ := lt_of_le_of_ne hμ hμ0'
    have hshifted :
        ConvexOn ℝ Set.univ (fun r ↦ φ r - (μ / 2) * r ^ (2 : ℕ)) :=
      shiftedScalarSliceConvexOn_of_fixedSubgradientLowerTangentQuadratic
        (φ := φ) (μ := μ) hμpos hfixed
    -- Once the shifted slice is convex, its adjacent-slope monotonicity is the wanted gap.
    exact
      quadraticSecantGap_of_shiftedConvexOn
        (φ := φ) (μ := μ) hshifted hxy hyz

/-- Helper for Definition 6.37: the remaining scalar frontier is the pure secant-gap inequality
`L ≤ U`, isolated from the later subgradient interval-selection step. -/
lemma quadraticSecantGap_of_pairwiseSupportAndQuadratic_viaCanonicalExtrema
    {φ : ℝ → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
      ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
  have _ := hμ
  rcases
      scalarAdmissibleSlopePair_nonempty_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair (s₁ := x) (t := y) (s₂ := z) with
    ⟨m, -, hxquad, hzquad⟩
  -- Once one middle-point slope carries both quadratic tangents, the exact secant gap is
  -- immediate from the threshold normal forms.
  exact
    correctedSecantGap_of_sharedMiddleLowerTangentQuadratic
      (φ := φ) (μ := μ) hxy hyz hxquad hzquad

/-- Helper for Definition 6.37: under the nonnegative quadratic hypothesis, the middle
subdifferential interval at `y` already contains one slope between the corrected left and right
thresholds. -/
lemma middleThresholdOverlapNonneg_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    ∃ m : ℝ,
      m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
      ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤ m ∧
      m ≤ ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
  have hconv : ConvexOn ℝ Set.univ φ :=
    scalarConvexOnUniv_of_pairwiseSupportAndQuadratic hpair
  rcases existsGreatestScalarSubgradient_of_convexOnUniv hconv y with
    ⟨mSup, hmSupSub, hmSupGreatest⟩
  rcases existsLeastScalarSubgradient_of_convexOnUniv hconv y with
    ⟨mInf, hmInfSub, hmInfLeast⟩
  rcases hpair x y with ⟨mL, hsupportL, hxquad⟩
  have hmLSub : mL ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) :=
    scalarSupportSlope_mem_subdifferential_coe hsupportL
  have hmL_le_mSup : mL ≤ mSup := hmSupGreatest mL hmLSub
  have hxquadSup :
      φ x ≥ φ y + mSup * (x - y) + (μ / 2) * (x - y) ^ (2 : ℕ) := by
    -- The greatest middle subgradient preserves the left-endpoint inequality because `x - y < 0`.
    have hmul : mSup * (x - y) ≤ mL * (x - y) := by
      exact mul_le_mul_of_nonpos_right hmL_le_mSup (sub_nonpos.mpr hxy.le)
    linarith
  have hleft :
      ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤ mSup := by
    -- Normalize the left-endpoint quadratic tangent with the positive gap `y - x`.
    have hxy_gap : 0 < y - x := sub_pos.mpr hxy
    have hxquadSup' :
        φ x ≥ φ y - mSup * (y - x) + (μ / 2) * (y - x) ^ (2 : ℕ) := by
      have hxneg : x - y = -(y - x) := by
        ring
      have hxsq : (-(y - x)) ^ (2 : ℕ) = (y - x) ^ (2 : ℕ) := by
        ring
      rw [hxneg, hxsq] at hxquadSup
      linarith
    have hdiv :
        (φ y - φ x) / (y - x) ≤ mSup - (μ / 2) * (y - x) := by
      refine (div_le_iff₀ hxy_gap).2 ?_
      linarith
    linarith
  rcases hpair z y with ⟨mR, hsupportR, hzquad⟩
  have hmRSub : mR ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) :=
    scalarSupportSlope_mem_subdifferential_coe hsupportR
  have hmInf_le_mR : mInf ≤ mR := hmInfLeast mR hmRSub
  have hzquadInf :
      φ z ≥ φ y + mInf * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ) := by
    -- The least middle subgradient preserves the right-endpoint inequality because `z - y > 0`.
    have hmul : mInf * (z - y) ≤ mR * (z - y) := by
      exact mul_le_mul_of_nonneg_right hmInf_le_mR (sub_nonneg.mpr hyz.le)
    linarith
  have hright :
      mInf ≤ ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
    -- Normalize the right-endpoint quadratic tangent with the positive gap `z - y`.
    have hyz_gap : 0 < z - y := sub_pos.mpr hyz
    have hdiv :
        mInf + (μ / 2) * (z - y) ≤ (φ z - φ y) / (z - y) := by
      refine (le_div_iff₀ hyz_gap).2 ?_
      linarith
    linarith
  let L : ℝ := ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x)
  let U : ℝ := ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y)
  have hgap : L ≤ U := by
    -- Route correction: once the numeric bridge `L ≤ U` is isolated upstream, the overlap witness
    -- is just interval selection inside the convex scalar subdifferential at `y`.
    simpa [L, U] using
      quadraticSecantGap_of_pairwiseSupportAndQuadratic_viaCanonicalExtrema
        (φ := φ) (μ := μ) hμ hpair hxy hyz
  -- Intersect the scalar subdifferential interval with the numeric interval `[L, U]`.
  simpa [L, U] using
    subgradientIntervalWitness_of_bounds
      (φ := φ) (y := y) (L := L) (U := U) (mInf := mInf) (mSup := mSup)
      hmInfSub hmSupSub hright hleft hgap

/-- Helper for Definition 6.37: the pairwise support-plus-quadratic hypothesis already forces the
corrected adjacent secants to be monotone. The proof now factors through the middle-threshold
overlap witness instead of the old outer-secant route. -/
lemma correctedAdjacentSecants_nonneg_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
      ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
  -- Route correction: isolate the actual structural issue first by choosing one middle
  -- subgradient inside the corrected-threshold overlap, then discard the membership field.
  rcases
      middleThresholdOverlapNonneg_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hμ hpair hxy hyz with
    ⟨m, hmSub, hleft, hright⟩
  have _ := hmSub
  linarith

/-- Helper for Definition 6.37: the nonnegative pairwise support-plus-quadratic hypothesis should
already imply convexity of the shifted scalar slice. This is the canonical upstream bridge used by
the corrected secant-gap and shared-middle-subgradient arguments. -/
lemma shiftedScalarSliceConvexOn_nonneg_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ)) :
    ConvexOn ℝ Set.univ (fun r ↦ φ r - (μ / 2) * r ^ (2 : ℕ)) := by
  by_cases hμ0 : μ = 0
  · -- When the modulus vanishes, the shifted slice is just the original convex scalar function.
    subst μ
    simpa using
      scalarConvexOnUniv_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := (0 : ℝ)) hpair
  · -- Route correction: the positive branch now closes through the upstream corrected-secant
    -- bridge, avoiding the later shared-subgradient cycle entirely.
    have hgap :
        ∀ {x y z : ℝ}, x < y → y < z →
          ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
            ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
      intro x y z hxy hyz
      exact
        correctedAdjacentSecants_nonneg_of_pairwiseSupportAndQuadratic
          (φ := φ) (μ := μ) hμ hpair hxy hyz
    exact
      shiftedScalarSliceConvexOn_of_correctedAdjacentSecants
        (φ := φ) (μ := μ) hgap

/-- Helper for Definition 6.37: even without using the quadratic correction, the scalar pairwise
support hypothesis already forces the ordinary adjacent secants to be monotone. -/
lemma ordinarySecantGap_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    (φ y - φ x) / (y - x) ≤ (φ z - φ y) / (z - y) := by
  -- Forget the quadratic correction and reuse ordinary scalar convexity on `Set.univ`.
  have hconv : ConvexOn ℝ Set.univ φ :=
    scalarConvexOnUniv_of_pairwiseSupportAndQuadratic hpair
  simpa using
    hconv.slope_mono_adjacent (x := x) (y := y) (z := z) (by simp) (by simp) hxy hyz

/-- Helper for Definition 6.37: once one middle-point slope satisfies the quadratic lower-tangent
inequalities at both `x` and the affine-ray endpoint `y + β * (y - x)`, the remaining affine-ray
algebra yields the full strong coefficient `β * (1 + β)`. -/
lemma strongAffineRayBound_of_sharedMiddleSlope
    {φ : ℝ → ℝ} {μ x y β m : ℝ}
    (hβ : 0 ≤ β)
    (hx :
      φ x ≥ φ y + m * (x - y) + (μ / 2) * (x - y) ^ (2 : ℕ))
    (hz :
      φ (y + β * (y - x)) ≥
        φ y + m * (β * (y - x)) + (μ / 2) * (β * (y - x)) ^ (2 : ℕ)) :
    φ (y + β * (y - x)) ≥
      φ y + β * (φ y - φ x) + β * (1 + β) * (μ / 2) * (y - x) ^ (2 : ℕ) := by
  have hx' :
      β * (φ y - φ x) + β * (μ / 2) * (y - x) ^ (2 : ℕ) ≤ m * (β * (y - x)) := by
    -- First normalize the left-endpoint quadratic inequality so the positive scalar `β` can be
    -- multiplied through it.
    have hx'' :
        φ y - φ x + (μ / 2) * (y - x) ^ (2 : ℕ) ≤ m * (y - x) := by
      have hxneg : x - y = -(y - x) := by
        ring
      have hxsq : (-(y - x)) ^ (2 : ℕ) = (y - x) ^ (2 : ℕ) := by
        ring_nf
      rw [hxneg, hxsq] at hx
      linarith
    have :=
      mul_le_mul_of_nonneg_left hx'' hβ
    simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using this
  have htarget :
      φ (y + β * (y - x)) ≥
        φ y + (β * (φ y - φ x) + β * (μ / 2) * (y - x) ^ (2 : ℕ)) +
          (μ / 2) * (β * (y - x)) ^ (2 : ℕ) := by
    -- Combine the left-endpoint and right-endpoint quadratic bounds for the same middle slope.
    linarith
  have hsq :
      (μ / 2) * (β * (y - x)) ^ (2 : ℕ) =
        β ^ (2 : ℕ) * (μ / 2) * (y - x) ^ (2 : ℕ) := by
    ring
  calc
    φ (y + β * (y - x)) ≥
        φ y + (β * (φ y - φ x) + β * (μ / 2) * (y - x) ^ (2 : ℕ)) +
          (μ / 2) * (β * (y - x)) ^ (2 : ℕ) := htarget
    _ = φ y + β * (φ y - φ x) +
          β * (1 + β) * (μ / 2) * (y - x) ^ (2 : ℕ) := by
        rw [hsq]
        ring

/-- Helper for Definition 6.37: for nonnegative `μ`, the only remaining structural step toward
the strong affine-ray bound is to choose one middle-point subgradient at `y` whose quadratic lower
tangents work simultaneously at both endpoints of the interval `x < y < z`. -/
lemma sharedMiddleSubgradient_twoSided_nonneg_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    ∃ m : ℝ,
      m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
      φ x ≥ φ y + m * (x - y) + (μ / 2) * (x - y) ^ (2 : ℕ) ∧
      φ z ≥ φ y + m * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ) := by
  rcases
      existsMiddleSubgradient_leftQuadratic_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair (x := x) (y := y) with
    ⟨mL, hmLSub, hxquad⟩
  rcases
      existsMiddleSubgradient_rightQuadratic_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair (y := y) (z := z) with
    ⟨mR, hmRSub, hzquad⟩
  let L : ℝ := ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x)
  let U : ℝ := ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y)
  have hxy_gap : 0 < y - x := sub_pos.mpr hxy
  have hyz_gap : 0 < z - y := sub_pos.mpr hyz
  have hL : L ≤ mL := by
    -- The left endpoint quadratic tangent forces every shared witness to lie above `L`.
    simpa [L] using
      leftSecantThreshold_le_of_subgradientLowerTangentQuadratic
        (φ := φ) (μ := μ) (m := mL) hxy hxquad
  have hU : mR ≤ U := by
    -- The right endpoint quadratic tangent forces every shared witness to lie below `U`.
    simpa [U] using
      subgradientLowerTangentQuadratic_le_rightSecantThreshold
        (φ := φ) (μ := μ) (m := mR) hyz hzquad
  have sharedOfGap
      (hgap : L ≤ U) :
      ∃ m : ℝ,
        m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
        φ x ≥ φ y + m * (x - y) + (μ / 2) * (x - y) ^ (2 : ℕ) ∧
        φ z ≥ φ y + m * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ) := by
    by_cases hmLU : mL ≤ U
    · -- If the left witness is already below the right threshold, it works at both endpoints.
      refine ⟨mL, hmLSub, hxquad, ?_⟩
      have hmL_div :
          mL + (μ / 2) * (z - y) ≤ (φ z - φ y) / (z - y) := by
        dsimp [U] at hmLU
        linarith
      have hmL_mul :
          mL * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ) ≤ φ z - φ y := by
        have hmul := (le_div_iff₀ hyz_gap).1 hmL_div
        nlinarith
      linarith
    · -- Otherwise the threshold value `U` sits between two known middle subgradients at `y`.
      have hsubConv :
          Convex ℝ (∂ (fun u ↦ (φ u : WithTop ℝ))(y)) :=
        convex_subdifferential_coe_real_at (f := φ) y
      have hUle : U ≤ mL := (lt_of_not_ge hmLU).le
      have hUSub : U ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) := by
        exact hsubConv.ordConnected.out hmRSub hmLSub ⟨hU, hUle⟩
      refine ⟨U, hUSub, ?_, ?_⟩
      · -- The secant-gap bound makes `U` large enough for the left endpoint.
        have hgap_left :
            (φ y - φ x) / (y - x) + (μ / 2) * (y - x) ≤ U := by
          simpa [L] using hgap
        have hleft_div :
            (φ y - φ x) / (y - x) ≤ U - (μ / 2) * (y - x) := by
          linarith
        have hleft_mul :
            φ y - φ x ≤ U * (y - x) - (μ / 2) * (y - x) ^ (2 : ℕ) := by
          have hmul := (div_le_iff₀ hxy_gap).1 hleft_div
          nlinarith
        linarith
      · -- The right endpoint inequality is exactly the defining equality of `U`.
        have hU_mul :
            U * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ) = φ z - φ y := by
          dsimp [U]
          have hyz_ne : z - y ≠ 0 := sub_ne_zero.mpr hyz.ne.symm
          field_simp [hyz_ne]
          ring
        linarith
  have hgap : L ≤ U := by
    -- Route correction: the interval-selection argument above is stable. The only missing piece
    -- is the shifted-slice convexity bridge; once that is available, the overlap `[L, U]`
    -- follows from ordinary adjacent secant monotonicity on the shifted scalar slice.
    have hshifted :
        ConvexOn ℝ Set.univ (fun r ↦ φ r - (μ / 2) * r ^ (2 : ℕ)) :=
      shiftedScalarSliceConvexOn_nonneg_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hμ hpair
    simpa [L, U] using
      quadraticSecantGap_of_shiftedConvexOn
        (φ := φ) (μ := μ) hshifted hxy hyz
  exact sharedOfGap hgap

/-- Helper for Definition 6.37: for nonnegative `μ`, the remaining scalar frontier is the
corrected secant-gap inequality, with the zero-modulus branch already reduced to ordinary convex
secant monotonicity. -/
lemma quadraticSecantGap_nonneg_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
      ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
  -- Re-export the upstream corrected adjacent-secant bridge without re-entering later helpers.
  exact
    correctedAdjacentSecants_nonneg_of_pairwiseSupportAndQuadratic
      (φ := φ) (μ := μ) hμ hpair hxy hyz

/-- Helper for Definition 6.37: when `x < y < z`, the pairwise support-plus-quadratic hypothesis
should supply one middle-point subgradient whose quadratic lower tangents work at both endpoints.
-/
lemma sharedMiddleSubgradient_twoSided_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    ∃ m : ℝ,
      m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
      φ x ≥ φ y + m * (x - y) + (μ / 2) * (x - y) ^ (2 : ℕ) ∧
      φ z ≥ φ y + m * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ) := by
  -- Route correction: the overlap problem at `y` is downstream of a purely numeric secant-gap
  -- inequality, so first factor out the interval-selection step that only consumes that gap.
  rcases
      existsMiddleSubgradient_leftQuadratic_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair (x := x) (y := y) with
    ⟨mL, hmLSub, hxquad⟩
  rcases
      existsMiddleSubgradient_rightQuadratic_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair (y := y) (z := z) with
    ⟨mR, hmRSub, hzquad⟩
  have sharedOfGap
      (hgap :
        ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
          ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y)) :
      ∃ m : ℝ,
        m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
        φ x ≥ φ y + m * (x - y) + (μ / 2) * (x - y) ^ (2 : ℕ) ∧
        φ z ≥ φ y + m * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ) := by
    let L : ℝ := ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x)
    let U : ℝ := ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y)
    have hxy_gap : 0 < y - x := sub_pos.mpr hxy
    have hyz_gap : 0 < z - y := sub_pos.mpr hyz
    have hL : L ≤ mL := by
      -- The left-endpoint quadratic tangent places every admissible shared slope above `L`.
      simpa [L] using
        leftSecantThreshold_le_of_subgradientLowerTangentQuadratic
          (φ := φ) (μ := μ) (m := mL) hxy hxquad
    have hU : mR ≤ U := by
      -- The right-endpoint quadratic tangent places every admissible shared slope below `U`.
      simpa [U] using
        subgradientLowerTangentQuadratic_le_rightSecantThreshold
          (φ := φ) (μ := μ) (m := mR) hyz hzquad
    by_cases hmLU : mL ≤ U
    · -- If the left witness already lies below the right threshold, it works at both endpoints.
      refine ⟨mL, hmLSub, hxquad, ?_⟩
      have hmL_div :
          mL + (μ / 2) * (z - y) ≤ (φ z - φ y) / (z - y) := by
        dsimp [U] at hmLU
        linarith
      have hmL_mul :
          mL * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ) ≤ φ z - φ y := by
        have hmul := (le_div_iff₀ hyz_gap).1 hmL_div
        nlinarith
      linarith
    · -- Otherwise the threshold value `U` lies inside the scalar subdifferential interval at `y`.
      have hsubConv :
          Convex ℝ (∂ (fun u ↦ (φ u : WithTop ℝ))(y)) :=
        convex_subdifferential_coe_real_at (f := φ) y
      have hUle : U ≤ mL := (lt_of_not_ge hmLU).le
      have hUSub : U ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) := by
        exact hsubConv.ordConnected.out hmRSub hmLSub ⟨hU, hUle⟩
      refine ⟨U, hUSub, ?_, ?_⟩
      · -- The numeric secant gap makes the threshold `U` large enough for the left endpoint.
        have hleft_div :
            (φ y - φ x) / (y - x) ≤ U - (μ / 2) * (y - x) := by
          dsimp [U]
          linarith
        have hleft_mul :
            φ y - φ x ≤ U * (y - x) - (μ / 2) * (y - x) ^ (2 : ℕ) := by
          have hmul := (div_le_iff₀ hxy_gap).1 hleft_div
          nlinarith
        linarith
      · -- The right-endpoint inequality is exactly the defining equality of `U`.
        have hU_mul :
            U * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ) = φ z - φ y := by
          dsimp [U]
          have hyz_ne : z - y ≠ 0 := sub_ne_zero.mpr hyz.ne.symm
          field_simp [hyz_ne]
          ring
        linarith
  by_cases hμ : 0 ≤ μ
  · -- TODO: prove the nonnegative-`μ` corrected secant gap on the shifted slice
    -- `r ↦ φ r - (μ / 2) * r ^ (2 : ℕ)`; that numeric bridge is now isolated upstream.
    have hgap :
        ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
          ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) :=
      quadraticSecantGap_nonneg_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hμ hpair hxy hyz
    exact sharedOfGap hgap
  · -- When `μ ≤ 0`, ordinary convex secant monotonicity already implies the corrected gap.
    have hordinary :
        (φ y - φ x) / (y - x) ≤ (φ z - φ y) / (z - y) :=
      ordinarySecantGap_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair hxy hyz
    have hμ_nonpos : μ ≤ 0 := le_of_not_ge hμ
    have hgap :
        ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
          ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
      nlinarith [hordinary, hμ_nonpos, sub_nonneg.mpr hxy.le, sub_nonneg.mpr hyz.le]
    exact sharedOfGap hgap

/-- Helper for Definition 6.37: when `x < y < z`, the scalar pairwise support-plus-quadratic
hypothesis forces the shifted left secant threshold to lie below the shifted right secant
threshold. -/
lemma middleThresholdOverlap_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    ∃ m : ℝ,
      m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
      ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤ m ∧
      m ≤ ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
  -- Route correction: this later-facing alias now reuses the earlier interval-selection proof
  -- instead of maintaining a second copy of the same overlap argument.
  exact
    middleThresholdOverlapNonneg_of_pairwiseSupportAndQuadratic
      (φ := φ) (μ := μ) hμ hpair hxy hyz

/-- Helper for Definition 6.37: once one middle-point subgradient lies between the shifted left
and right thresholds, the displayed secant-gap inequality is immediate. -/
lemma quadraticSecantGap_of_middleThresholdOverlap
    {φ : ℝ → ℝ} {μ : ℝ} {x y z : ℝ}
    (hoverlap :
      ∃ m : ℝ,
        m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
        ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤ m ∧
        m ≤ ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y)) :
    ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
      ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
  -- Discard the membership field and compare the two threshold bounds through the common slope.
  rcases hoverlap with ⟨m, -, hleft, hright⟩
  linarith

/-- Helper for Definition 6.37: when `x < y < z`, the scalar pairwise support-plus-quadratic
hypothesis forces the shifted left secant threshold to lie below the shifted right secant
threshold. -/
lemma quadraticSecantGap_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
      ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) := by
  -- First isolate the genuine missing bridge: one middle-point subgradient lying between the two
  -- shifted thresholds.
  have hoverlap :
      ∃ m : ℝ,
        m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
        ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤ m ∧
        m ≤ ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) :=
    middleThresholdOverlap_of_pairwiseSupportAndQuadratic
      (φ := φ) (μ := μ) hμ hpair hxy hyz
  -- Once the overlap witness exists, the displayed numerical inequality is immediate.
  exact quadraticSecantGap_of_middleThresholdOverlap hoverlap

/-- Helper for Definition 6.37: once the shifted secant gap is known, the pairwise hypothesis
supplies endpoint witnesses and the convex scalar subdifferential interval merges them into one
shared middle-point subgradient. -/
lemma existsSharedSubgradient_of_pairwiseSupportAndQuadratic_of_secantGap
    {φ : ℝ → ℝ} {μ : ℝ}
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z)
    (hgap :
      ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
        ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y)) :
    ∃ m : ℝ,
      m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
      φ x ≥ φ y + m * (x - y) + (μ / 2) * (x - y) ^ (2 : ℕ) ∧
      φ z ≥ φ y + m * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ) := by
  rcases
      existsMiddleSubgradient_leftQuadratic_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair (x := x) (y := y) with
    ⟨mL, hmLSub, hxquad⟩
  rcases
      existsMiddleSubgradient_rightQuadratic_of_pairwiseSupportAndQuadratic
        (φ := φ) (μ := μ) hpair (y := y) (z := z) with
    ⟨mR, hmRSub, hzquad⟩
  -- The secant-gap lemma is precisely the overlap condition needed to merge the two endpoint
  -- witnesses inside the convex scalar subdifferential interval.
  exact existsSharedSubgradient_of_secantGap hxy hyz hmLSub hmRSub hxquad hzquad hgap

/-- Helper for Definition 6.37: when `x < y < z`, the scalar pairwise support-plus-quadratic
hypothesis should provide one subgradient at the middle point `y` whose quadratic lower tangents
work simultaneously at both endpoints. -/
lemma sharedShiftedSupportSlope_twoSided_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    ∃ m : ℝ,
      m ∈ ∂ (fun u ↦ (φ u : WithTop ℝ))(y) ∧
      φ x ≥ φ y + m * (x - y) + (μ / 2) * (x - y) ^ (2 : ℕ) ∧
      φ z ≥ φ y + m * (z - y) + (μ / 2) * (z - y) ^ (2 : ℕ) := by
  have hgap :
      ((φ y - φ x) / (y - x)) + (μ / 2) * (y - x) ≤
        ((φ z - φ y) / (z - y)) - (μ / 2) * (z - y) :=
    quadraticSecantGap_of_pairwiseSupportAndQuadratic hμ hpair hxy hyz
  -- First obtain the left and right endpoint witnesses from `hpair`; then `hgap` is exactly the
  -- overlap condition needed by the interval-selection lemma.
  exact
    existsSharedSubgradient_of_pairwiseSupportAndQuadratic_of_secantGap
      (φ := φ) (μ := μ) hpair hxy hyz hgap

/-- Helper for Definition 6.37: the scalar pairwise support-plus-quadratic hypothesis should
upgrade the one-point affine-ray estimate to the strong affine-ray bound with coefficient
`β * (1 + β)`. -/
lemma strongAffineRayBoundScalar_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ)) :
    ∀ {x y : ℝ} {β : ℝ}, 0 ≤ β →
      φ (y + β * (y - x)) ≥
        φ y + β * (φ y - φ x) + β * (1 + β) * (μ / 2) * (y - x) ^ (2 : ℕ) := by
  intro x y β hβ
  by_cases hβ0 : β = 0
  · -- The degenerate affine ray `y + 0 * (y - x)` is exactly the base point `y`.
    subst β
    simp
  · by_cases hxy : x = y
    · -- When the two anchor points coincide, every quadratic correction vanishes.
      subst y
      simp
    · have hβpos : 0 < β := lt_of_le_of_ne hβ (by simpa [eq_comm] using hβ0)
      by_cases hxy_lt : x < y
      · let z : ℝ := y + β * (y - x)
        have hyz : y < z := by
          dsimp [z]
          nlinarith
        rcases
            sharedShiftedSupportSlope_twoSided_of_pairwiseSupportAndQuadratic
              hμ hpair hxy_lt hyz with
          ⟨m, hmSub, hx, hz⟩
        have hz' :
            φ (y + β * (y - x)) ≥
              φ y + m * (β * (y - x)) + (μ / 2) * (β * (y - x)) ^ (2 : ℕ) := by
          simpa [z] using hz
        have hx' :
            β * (φ y - φ x) + β * (μ / 2) * (y - x) ^ (2 : ℕ) ≤ m * (β * (y - x)) := by
          have hx'' :
              φ y - φ x + (μ / 2) * (y - x) ^ (2 : ℕ) ≤ m * (y - x) := by
            linarith
          have :=
            mul_le_mul_of_nonneg_left hx'' hβ
          simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using this
        -- Combine the left-endpoint quadratic bound with the right-endpoint quadratic bound for the
        -- shared middle-point slope `m`.
        have htarget :
            φ (y + β * (y - x)) ≥
              φ y + (β * (φ y - φ x) + β * (μ / 2) * (y - x) ^ (2 : ℕ)) +
                (μ / 2) * (β * (y - x)) ^ (2 : ℕ) := by
          linarith
        have hsq :
            (μ / 2) * (β * (y - x)) ^ (2 : ℕ) =
              β ^ (2 : ℕ) * (μ / 2) * (y - x) ^ (2 : ℕ) := by
          ring
        calc
          φ (y + β * (y - x)) ≥
              φ y + (β * (φ y - φ x) + β * (μ / 2) * (y - x) ^ (2 : ℕ)) +
                (μ / 2) * (β * (y - x)) ^ (2 : ℕ) := htarget
          _ = φ y + β * (φ y - φ x) +
                β * (1 + β) * (μ / 2) * (y - x) ^ (2 : ℕ) := by
              rw [hsq]
              ring
      · have hyx : y < x := by
          refine lt_of_le_of_ne (le_of_not_gt hxy_lt) ?_
          intro hyx_eq
          exact hxy hyx_eq.symm
        let z : ℝ := y + β * (y - x)
        have hzy : z < y := by
          dsimp [z]
          nlinarith
        rcases
            sharedShiftedSupportSlope_twoSided_of_pairwiseSupportAndQuadratic hμ hpair hzy hyx with
          ⟨m, hmSub, hz, hx⟩
        have hz' :
            φ (y + β * (y - x)) ≥
              φ y + m * (β * (y - x)) + (μ / 2) * (β * (y - x)) ^ (2 : ℕ) := by
          simpa [z] using hz
        have hx' :
            β * (φ y - φ x) + β * (μ / 2) * (y - x) ^ (2 : ℕ) ≤ m * (β * (y - x)) := by
          have hx'' :
              φ y - φ x + (μ / 2) * (y - x) ^ (2 : ℕ) ≤ m * (y - x) := by
            linarith
          have :=
            mul_le_mul_of_nonneg_left hx'' hβ
          simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using this
        -- The `y < x` branch is the same cancellation argument after reversing the endpoint order.
        have htarget :
            φ (y + β * (y - x)) ≥
              φ y + (β * (φ y - φ x) + β * (μ / 2) * (y - x) ^ (2 : ℕ)) +
                (μ / 2) * (β * (y - x)) ^ (2 : ℕ) := by
          linarith
        have hsq :
            (μ / 2) * (β * (y - x)) ^ (2 : ℕ) =
              β ^ (2 : ℕ) * (μ / 2) * (y - x) ^ (2 : ℕ) := by
          ring
        calc
          φ (y + β * (y - x)) ≥
              φ y + (β * (φ y - φ x) + β * (μ / 2) * (y - x) ^ (2 : ℕ)) +
                (μ / 2) * (β * (y - x)) ^ (2 : ℕ) := htarget
          _ = φ y + β * (φ y - φ x) +
                β * (1 + β) * (μ / 2) * (y - x) ^ (2 : ℕ) := by
              rw [hsq]
              ring

/-- Helper for Definition 6.37: the scalar shifted slice is convex once the scalar affine-ray
bound carries the full `β * (1 + β)` quadratic coefficient. -/
lemma shiftedScalarSliceConvexOn_of_pairwiseSupportAndQuadratic
    {φ : ℝ → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hpair :
      ∀ s t : ℝ,
        ∃ m : ℝ,
          (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
          φ s ≥ φ t + m * (s - t) + (μ / 2) * (s - t) ^ (2 : ℕ)) :
    ConvexOn ℝ Set.univ (fun r ↦ φ r - (μ / 2) * r ^ (2 : ℕ)) := by
  -- Verify the affine-ray criterion for the shifted slice using the strong scalar affine-ray
  -- bound, then normalize the quadratic correction with the polynomial identity above.
  rw [convexOn_iff_affine_ray_inequality Set.univ (fun r ↦ φ r - (μ / 2) * r ^ (2 : ℕ))
    convex_univ]
  intro x y hx hy β hβ hmem
  have hstrong :
      φ (y + β * (y - x)) ≥
        φ y + β * (φ y - φ x) + β * (1 + β) * (μ / 2) * (y - x) ^ (2 : ℕ) :=
    strongAffineRayBoundScalar_of_pairwiseSupportAndQuadratic hμ hpair hβ
  have hsquare := shiftedScalarSquare_affineRay (x := x) (y := y) (β := β)
  have hrew :
      φ y + β * (φ y - φ x) + β * (1 + β) * (μ / 2) * (y - x) ^ (2 : ℕ) -
          (μ / 2) * (y + β * (y - x)) ^ (2 : ℕ) =
        (φ y - (μ / 2) * y ^ (2 : ℕ)) +
          β * ((φ y - (μ / 2) * y ^ (2 : ℕ)) - (φ x - (μ / 2) * x ^ (2 : ℕ))) := by
    rw [hsquare]
    ring
  have hshifted :
      φ (y + β * (y - x)) - (μ / 2) * (y + β * (y - x)) ^ (2 : ℕ) ≥
        φ y + β * (φ y - φ x) + β * (1 + β) * (μ / 2) * (y - x) ^ (2 : ℕ) -
          (μ / 2) * (y + β * (y - x)) ^ (2 : ℕ) := by
    linarith
  rw [hrew] at hshifted
  simpa using hshifted

/-- Helper for Definition 6.37: for fixed base and comparison points, the admissible subgradient
halfspace cut out by the quadratic lower-tangent inequality is closed. -/
lemma isClosed_subgradientLowerTangentQuadraticSet
    {σ : ℝ} {f : E → ℝ} {x y : E} :
    IsClosed
      {g : E |
        f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)} := by
  -- The defining inequality is the preimage of the closed ray `(-∞, f y]` under a continuous
  -- affine functional of `g`.
  have hcontInner : Continuous fun g : E ↦ inner ℝ g (y - x) := by
    exact continuous_id.inner continuous_const
  have hcont :
      Continuous fun g : E ↦
        f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
    have hconst₁ : Continuous fun _ : E ↦ f x := continuous_const
    have hconst₂ : Continuous fun _ : E ↦ (σ / 2) * ‖y - x‖ ^ (2 : ℕ) := continuous_const
    simpa [add_assoc] using hconst₁.add (hcontInner.add hconst₂)
  simpa using isClosed_le hcont continuous_const

/-- Helper for Definition 6.37: once every finite family of comparison points has a common
subgradient witness at the base point, compactness upgrades that finite-family witness to one
global witness working for all comparison points. -/
lemma existsFixedSubgradientLowerTangentQuadratic_at_ofFiniteFamily
    [FiniteDimensional ℝ E] {σ : ℝ} {f : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ f) (x : E)
    (hfinite :
      ∀ a : Finset E,
        ∃ g ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(x),
          ∀ y ∈ a,
            f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) :
    ∃ g ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(x),
      ∀ y : E,
        f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  let tangentSet : E → Set E := fun y ↦
    {g : E | f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)}
  have htangentClosed : ∀ y : E, IsClosed (tangentSet y) := by
    intro y
    -- Each comparison-point constraint is a closed affine halfspace in the subgradient variable.
    simpa [tangentSet] using
      (isClosed_subgradientLowerTangentQuadraticSet (σ := σ) (f := f) (x := x) (y := y))
  have hcompactSubdiff :
      IsCompact (∂ (fun z ↦ (f z : WithTop ℝ))(x)) := by
    exact (subdifferential_compact_convex_at hconv x).1
  have hfiniteInter :
      ∀ a : Finset E,
        ((∂ (fun z ↦ (f z : WithTop ℝ))(x)) ∩ ⋂ y ∈ a, tangentSet y).Nonempty := by
    intro a
    rcases hfinite a with ⟨g, hgSub, hgFinite⟩
    refine ⟨g, hgSub, ?_⟩
    rw [Set.mem_iInter]
    intro y
    rw [Set.mem_iInter]
    intro hy
    exact hgFinite y hy
  rcases hcompactSubdiff.inter_iInter_nonempty tangentSet htangentClosed hfiniteInter with
    ⟨g, hgSub, hgAll⟩
  refine ⟨g, hgSub, ?_⟩
  intro y
  simpa [tangentSet] using Set.mem_iInter.mp hgAll y

/-- Helper for Definition 6.37: the pairwise quadratic lower-tangent hypothesis should be
collapsed to one fixed subgradient at each base point before invoking the owner strong-convexity
criterion. -/
lemma existsFixedSubgradientLowerTangentQuadratic_ofPairwiseSubgradientLowerTangentQuadratic
    [FiniteDimensional ℝ E] {σ : ℝ} {f : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ f)
    (hsub :
      ∀ x y : E,
        ∃ g ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(x),
          f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) :
    ∀ x : E,
      ∃ g ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(x),
        ∀ y : E,
          f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  by_cases hσ : 0 < σ
  · have hμ :
        f ∈ 𝒮^0_σ(Set.univ) := by
      -- Route correction: for positive `σ`, bypass the old compactness/common-witness route and
      -- prove strong convexity from shifted affine-ray bounds on scalar line restrictions.
      have hshifted :
          ConvexOn ℝ Set.univ (fun z ↦ f z - (σ / 2) * ‖z‖ ^ (2 : ℕ)) := by
        rw [convexOn_iff_affine_ray_inequality Set.univ
          (fun z ↦ f z - (σ / 2) * ‖z‖ ^ (2 : ℕ)) convex_univ]
        intro x y hx hy β hβ hmem
        let d : E := y - x
        let φ : ℝ → ℝ := fun t ↦ f (x + t • d)
        have hline :
            ∀ s t : ℝ,
              ∃ m : ℝ,
                (∀ u : ℝ, φ u ≥ φ t + m * (u - t)) ∧
                φ s ≥ φ t + m * (s - t) +
                  ((σ * ‖d‖ ^ (2 : ℕ)) / 2) * (s - t) ^ (2 : ℕ) := by
          intro s t
          simpa [φ, d] using
            lineSupportAndQuadraticWitness_ofPairwiseSubgradientLowerTangentQuadratic
              hsub x d s t
        have hμ_nonneg : 0 ≤ σ * ‖d‖ ^ (2 : ℕ) := by
          have hsq : 0 ≤ ‖d‖ ^ (2 : ℕ) := by positivity
          exact mul_nonneg hσ.le hsq
        have hscalarRaw :
            φ (1 + β * (1 - 0)) ≥
              φ 1 + β * (φ 1 - φ 0) +
                β * (1 + β) * ((σ * ‖d‖ ^ (2 : ℕ)) / 2) * (1 - 0) ^ (2 : ℕ) :=
          strongAffineRayBoundScalar_of_pairwiseSupportAndQuadratic
            hμ_nonneg hline (x := 0) (y := 1) hβ
        have hscalar :
            φ (1 + β) ≥
              φ 1 + β * (φ 1 - φ 0) +
                β * (1 + β) * ((σ * ‖d‖ ^ (2 : ℕ)) / 2) * (1 - 0) ^ (2 : ℕ) := by
          simpa using hscalarRaw
        have hray : x + (1 + β) • d = y + β • (y - x) := by
          dsimp [d]
          rw [sub_eq_add_neg, add_smul, one_smul, smul_add, smul_neg]
          abel_nf
        have hone : x + (1 : ℝ) • d = y := by
          dsimp [d]
          simp
        have hzero : x + (0 : ℝ) • d = x := by simp
        have hvectorRaw :
            f (y + β • (y - x)) ≥
              f y + β * (f y - f x) +
                β * ((1 + β) * (σ * ‖y - x‖ ^ (2 : ℕ) / 2)) := by
          simpa [φ, d, hray, hone, hzero, mul_assoc, mul_left_comm, mul_comm] using hscalar
        have hvector :
            f (y + β • (y - x)) ≥
              f y + β * (f y - f x) +
                β * (1 + β) * (σ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
          have hmul :
              β * ((1 + β) * (σ * ‖y - x‖ ^ (2 : ℕ) / 2)) =
                β * (1 + β) * (σ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
            ring
          rwa [hmul] at hvectorRaw
        have hsquare := shiftedNormSq_affineRay (x := x) (y := y) (β := β)
        have hrew :
            f y + β * (f y - f x) + β * (1 + β) * (σ / 2) * ‖y - x‖ ^ (2 : ℕ) -
                (σ / 2) * ‖y + β • (y - x)‖ ^ (2 : ℕ) =
              (f y - (σ / 2) * ‖y‖ ^ (2 : ℕ)) +
                β * ((f y - (σ / 2) * ‖y‖ ^ (2 : ℕ)) -
                  (f x - (σ / 2) * ‖x‖ ^ (2 : ℕ))) := by
          rw [hsquare]
          ring
        have hshiftedRay :
            f (y + β • (y - x)) - (σ / 2) * ‖y + β • (y - x)‖ ^ (2 : ℕ) ≥
              f y + β * (f y - f x) + β * (1 + β) * (σ / 2) * ‖y - x‖ ^ (2 : ℕ) -
                (σ / 2) * ‖y + β • (y - x)‖ ^ (2 : ℕ) := by
          linarith
        rw [hrew] at hshiftedRay
        simpa using hshiftedRay
      have hstrong : StrongConvexOn Set.univ σ f := by
        rw [strongConvexOn_iff_convex]
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hshifted
      exact (mem_S0On_iff).2 ⟨hσ, hstrong⟩
    intro x
    rcases mem_S0On_iff.mp hμ with ⟨hσ', hstrong⟩
    exact existsFixedSubgradientLowerTangentQuadratic_ofStrongConvexOnUniv hσ' hstrong x
  · intro x
    let lift : E → WithTop ℝ := fun z ↦ (f z : WithTop ℝ)
    have hxInt : x ∈ interior (dom lift) := by
      simp [lift, withTopEffectiveDomain]
    have hconvLift : ConvexOn ℝ (dom lift) (withTopRealPart lift) := by
      simpa [lift, withTopEffectiveDomain, withTopRealPart] using hconv
    rcases subdifferential_nonempty_of_convexOn_of_mem_interior hconvLift hxInt with ⟨g, hg⟩
    refine ⟨g, hg, ?_⟩
    intro y
    have hsupport : f y ≥ f x + inner ℝ g (y - x) :=
      mem_subdifferential_coe_iff.mp hg y
    have hquad_nonpos : (σ / 2) * ‖y - x‖ ^ (2 : ℕ) ≤ 0 := by
      have hσ_nonpos : σ / 2 ≤ 0 := by
        have : σ ≤ 0 := le_of_not_gt hσ
        linarith
      have hsq_nonneg : 0 ≤ ‖y - x‖ ^ (2 : ℕ) := by positivity
      exact mul_nonpos_of_nonpos_of_nonneg hσ_nonpos hsq_nonneg
    linarith

/-- Helper for Definition 6.37: a quadratic lower tangent with the canonical gradient implies
that `∇ f x` belongs to the Chapter 3 subdifferential at `x`. -/
lemma gradientMemSubdifferential_ofQuadraticLowerTangent
    [CompleteSpace E] {σ : ℝ} {f : E → ℝ}
    {x : E} (hσ : 0 < σ)
    (hquad :
      ∀ y : E,
        f y ≥ f x + inner ℝ (∇ f x) (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) :
    ∇ f x ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(x) := by
  -- Drop the nonnegative quadratic term to recover the ordinary affine support inequality.
  rw [mem_subdifferential_coe_iff]
  intro y
  have hquad_nonneg : 0 ≤ (σ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
    have hσ_nonneg : 0 ≤ σ / 2 := by linarith
    positivity
  linarith [hquad y]

/-- Definition 6.37, source-facing bridge: on a finite-dimensional real inner-product space,
positive whole-space strong convexity is equivalent to positivity of `σ` together with the
textbook pointwise subgradient lower-tangent inequality with quadratic term
`(σ / 2) * ‖y - x‖²`. -/
theorem mem_S0On_univ_iff_exists_subgradient_lower_tangent_quadratic
    [FiniteDimensional ℝ E] {σ : ℝ} {f : E → ℝ} :
    f ∈ 𝒮^0_σ(Set.univ) ↔
      0 < σ ∧
        ∀ x y : E,
          ∃ g ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(x),
              f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  constructor
  · intro hstrong_mem
    rcases (mem_S0On_iff.mp hstrong_mem) with ⟨hσ, hstrong⟩
    refine ⟨hσ, ?_⟩
    -- A strongly convex function admits one subgradient at each base point that works for all `y`.
    intro x y
    rcases existsFixedSubgradientLowerTangentQuadratic_ofStrongConvexOnUniv hσ hstrong x with
      ⟨g, hg, hgquad⟩
    exact ⟨g, hg, hgquad y⟩
  · rintro ⟨hσ, hsub⟩
    -- Route correction: the reverse implication first upgrades the pairwise existential witness to
    -- one fixed subgradient at each base point, then reuses the established owner helper.
    have hconv : ConvexOn ℝ Set.univ f :=
      convexOnUniv_ofPairwiseSubgradientLowerTangentQuadratic hsub
    have hfixed :
        ∀ x : E,
          ∃ g ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(x),
            ∀ y : E,
              f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) :=
      existsFixedSubgradientLowerTangentQuadratic_ofPairwiseSubgradientLowerTangentQuadratic
        hconv hsub
    exact mem_S0On_univ_of_exists_subgradient_lower_tangent_quadratic_fixed hσ hfixed

/-- Auxiliary companion API: for a differentiable function, the fixed-witness strong-convexity
criterion above reduces to the gradient lower-support inequality with the same quadratic term. -/
theorem mem_S0On_univ_iff_gradient_inequality_of_differentiable
    [CompleteSpace E] {σ : ℝ} {f : E → ℝ} (hf : Differentiable ℝ f) :
    f ∈ 𝒮^0_σ(Set.univ) ↔
      0 < σ ∧
        ∀ x y : E,
          f y ≥ f x + inner ℝ (∇ f x) (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  constructor
  · intro hstrong_mem
    rcases (mem_S0On_iff.mp hstrong_mem) with ⟨hσ, hstrong⟩
    refine ⟨hσ, ?_⟩
    intro x y
    -- Apply the canonical strong-convexity lower tangent inequality with the actual gradient.
    have hgrad : HasGradientAt f (∇ f x) x := (hf x).hasGradientAt
    simpa using
      StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt hstrong (by simp) (by simp) hgrad
  · rintro ⟨hσ, hquad⟩
    -- Use the fixed gradient witness at each base point and shift by `(σ / 2) * ‖·‖²`.
    refine mem_S0On_univ_of_exists_subgradient_lower_tangent_quadratic_fixed hσ ?_
    intro x
    refine ⟨∇ f x, ?_, hquad x⟩
    exact gradientMemSubdifferential_ofQuadraticLowerTangent hσ (hquad x)

end
