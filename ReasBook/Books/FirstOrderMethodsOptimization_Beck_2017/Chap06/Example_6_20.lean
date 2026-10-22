/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_5
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_18
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E]

attribute [local instance] Classical.propDecidable

/- Example 6.20 is `source-facing`: the textbook object is the cubic norm penalty
`x ↦ λ ‖x‖^3`, stated on the chapter owner `prox[...]` from Definition 6.1. Domain sampling
against Definition 6.1, Lemma 6.5 (3), Theorem 6.18, and Example 6.19 shows the owner split
here:

- `source-facing`: the vector penalty `cubic_norm_penalty`,
- `core/canonical`: the chapter radial proximal owner `prox_norm_composition_eq_piecewise`,
- `bridge/view`: the existing scalar positive-ray owner `nonnegative_cubic_penalty`.

The primitive data are only `lam` and the norm-based penalty itself; the scalar cubic profile is
already owned canonically by `nonnegative_cubic_penalty`, so no parallel wrapper should remain in
this file. -/
-- Semantic recall: `lean_leansearch` produced no direct useful hit for this radial cubic proximal
-- formula, so the owner/API choice is verified from the local Chapter 6 precedent and
-- `prox_norm_composition_eq_piecewise`.

/-- The cubic norm penalty `x ↦ λ ‖x‖^3`. -/
def cubic_norm_penalty (lam : ℝ) : E → EReal :=
  fun x ↦ ((lam * ‖x‖ ^ (3 : ℕ) : ℝ) : EReal)

/-- Evaluating the cubic norm penalty gives the value `λ ‖x‖^3`. -/
@[simp] theorem cubic_norm_penalty_apply (lam : ℝ) (x : E) :
    cubic_norm_penalty lam x = ((lam * ‖x‖ ^ (3 : ℕ) : ℝ) : EReal) :=
  rfl

/-- The cubic norm penalty is the norm-composition of the scalar nonnegative cubic penalty. -/
theorem cubic_norm_penalty_eq_nonnegative_cubic_penalty_comp_norm (lam : ℝ) :
    cubic_norm_penalty lam = nonnegative_cubic_penalty lam ∘ fun x : E ↦ ‖x‖ := by
  funext x
  rw [cubic_norm_penalty_apply, Function.comp_apply, nonnegative_cubic_penalty_apply]
  simp

-- Proof sketch: rewrite `cubic_norm_penalty lam` as
-- `nonnegative_cubic_penalty lam ∘ norm` via
-- `cubic_norm_penalty_eq_nonnegative_cubic_penalty_comp_norm`. In the nontrivial branch, apply
-- the chapter radial proximal theorem from Theorem 6.18 to the canonical scalar owner
-- `nonnegative_cubic_penalty lam`; in the subsingleton branch, `x = 0` and the origin clause
-- already gives the correct scalar-radius description. Lemma 6.5 (3) can then be substituted
-- later to derive the closed-form singleton corollary.
section ProximalFormula

variable [InnerProductSpace ℝ E]

/-- Helper for Example 6.20: the effective domain of `nonnegative_cubic_penalty lam` is exactly
the nonnegative ray. -/
private theorem mem_effective_domain_nonnegative_cubic_penalty_iff (lam t : ℝ) :
    t ∈ effective_domain (nonnegative_cubic_penalty lam) ↔ 0 ≤ t := by
  -- Unfold the scalar penalty and separate the feasible and infeasible branches.
  rw [mem_effective_domain, nonnegative_cubic_penalty_apply]
  by_cases ht : 0 ≤ t
  · constructor
    · intro _
      exact ht
    · intro _
      simpa [ht, EReal.coe_mul, EReal.coe_pow] using
        (EReal.coe_lt_top (lam * t ^ (3 : ℕ)))
  · simp [ht]

/-- Helper for Example 6.20: the scalar cubic penalty is lower semicontinuous. -/
private theorem lowerSemicontinuous_nonnegative_cubic_penalty (lam : ℝ) :
    LowerSemicontinuous (nonnegative_cubic_penalty lam) := by
  -- The indicator of the closed ray `[0, ∞)` and the continuous cubic term are both lower
  -- semicontinuous, so their `EReal` sum is as well.
  have hind :
      LowerSemicontinuous (extendedIndicator (Set.Ici (0 : ℝ))) := by
    rw [extendedIndicator_lowerSemicontinuous_iff_isClosed]
    simpa using isClosed_Ici
  have hcont : Continuous (fun t : ℝ ↦ lam * t ^ (3 : ℕ)) :=
    continuous_const.mul (continuous_id.pow 3)
  have hcube :
      LowerSemicontinuous (Real.toEReal ∘ fun t : ℝ ↦ lam * t ^ (3 : ℕ)) :=
    (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  simpa [nonnegative_cubic_penalty] using
    hind.add' hcube
      (fun _ ↦ EReal.continuousAt_add
        (Or.inr (EReal.coe_ne_bot _))
        (Or.inr (EReal.coe_ne_top _)))

/-- Helper for Example 6.20: the scalar cubic penalty is convex once `λ ≥ 0`. -/
private theorem isConvex_nonnegative_cubic_penalty (lam : ℝ) (hlam : 0 ≤ lam) :
    is_convex_function (nonnegative_cubic_penalty lam) := by
  -- Route correction: unlike the linear penalty from Example 6.19, `t ↦ λ t^3` is not convex on
  -- all of `ℝ`, so the correct route is convexity of the finite branch on `effective_domain`.
  have hne_bot :
      ∀ t ∈ effective_domain (nonnegative_cubic_penalty lam),
        nonnegative_cubic_penalty lam t ≠ ⊥ := by
    intro t ht
    have ht_nonneg : 0 ≤ t :=
      (mem_effective_domain_nonnegative_cubic_penalty_iff lam t).mp ht
    rw [nonnegative_cubic_penalty_apply, if_pos ht_nonneg, EReal.coe_mul, EReal.coe_pow]
    exact EReal.coe_ne_bot _
  refine (is_convex_function_iff_convexOn_toReal hne_bot).2 ?_
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ ↦ lam * t ^ (3 : ℕ)) := by
    simpa using (convexOn_pow (𝕜 := ℝ) (n := 3)).smul hlam
  refine ⟨?_, ?_⟩
  · convert (convex_Ici (0 : ℝ) : Convex ℝ (Set.Ici (0 : ℝ))) using 1
    ext x
    exact mem_effective_domain_nonnegative_cubic_penalty_iff lam x
  · intro x hx y hy a b ha hb hab
    have hx_nonneg : 0 ≤ x :=
      (mem_effective_domain_nonnegative_cubic_penalty_iff lam x).mp hx
    have hy_nonneg : 0 ≤ y :=
      (mem_effective_domain_nonnegative_cubic_penalty_iff lam y).mp hy
    have hxy_nonneg : 0 ≤ a * x + b * y := by
      nlinarith
    have hconv_real :
        lam * (a * x + b * y) ^ (3 : ℕ) ≤
          a * (lam * x ^ (3 : ℕ)) + b * (lam * y ^ (3 : ℕ)) :=
      hconv.2 hx_nonneg hy_nonneg ha hb hab
    simpa [nonnegative_cubic_penalty_apply, hx_nonneg, hy_nonneg, hxy_nonneg] using hconv_real

/-- Helper for Example 6.20: the scalar cubic proximal set at `0` is the singleton `{0}`. -/
private theorem prox_nonnegative_cubic_penalty_at_zero (lam : ℝ) (hlam : 0 < lam) :
    prox[nonnegative_cubic_penalty lam] 0 = {0} := by
  -- Specialize the scalar closed-form proximal formula at the origin.
  simpa using prox_nonnegative_cubic_penalty_eq_singleton lam hlam 0

/-- Example 6.20: for the cubic norm penalty `f(x) = λ ‖x‖^3` with `0 < λ`, write
`f = nonnegative_cubic_penalty lam ∘ norm`, equivalently
`g t = if 0 ≤ t then λ t^3 else ∞`.
Then the proximal mapping of `f` is given by the radial case split from Theorem 6.18 in the
nontrivial case, with the same origin branch remaining valid in the trivial case:
at `x = 0`, it is the set of vectors whose norm lies in
`prox[nonnegative_cubic_penalty lam] 0`, and for `x ≠ 0`, it is the radial image of
`prox[nonnegative_cubic_penalty lam] ‖x‖`. -/
theorem prox_cubic_norm_penalty_eq_piecewise (lam : ℝ) (hlam : 0 < lam) (x : E) :
    prox[cubic_norm_penalty lam] x =
      if x = 0 then
        {u : E | ‖u‖ ∈ prox[nonnegative_cubic_penalty lam] 0}
      else
        (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[nonnegative_cubic_penalty lam] ‖x‖ := by
  -- Split off the zero-dimensional case first: Theorem 6.18 needs a nontrivial ambient space.
  by_cases hE : Subsingleton E
  · letI : Subsingleton E := hE
    have hx0 : x = 0 := Subsingleton.elim x 0
    -- In a subsingleton space, every proximal set is forced to be `{0}`.
    have hprox0 : prox[cubic_norm_penalty lam] (0 : E) = {(0 : E)} := by
      refine Set.eq_singleton_iff_unique_mem.2 ?_
      constructor
      · rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
        intro y
        have hy : y = 0 := Subsingleton.elim y 0
        simp [cubic_norm_penalty_apply, hy]
      · intro y hy
        simpa using (Subsingleton.elim y 0)
    have hvector0 :
        {u : E | ‖u‖ ∈ prox[nonnegative_cubic_penalty lam] 0} = {(0 : E)} := by
      -- The scalar proximal radius at the origin is `0`, so only the zero vector remains.
      ext u
      rw [prox_nonnegative_cubic_penalty_at_zero lam hlam]
      simp
    calc
      prox[cubic_norm_penalty lam] x = prox[cubic_norm_penalty lam] (0 : E) := by simp [hx0]
      _ = {(0 : E)} := hprox0
      _ = {u : E | ‖u‖ ∈ prox[nonnegative_cubic_penalty lam] 0} := hvector0.symm
      _ = if x = 0 then
            {u : E | ‖u‖ ∈ prox[nonnegative_cubic_penalty lam] 0}
          else
            (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[nonnegative_cubic_penalty lam] ‖x‖ := by
            simp [hx0]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hpiece :=
      prox_norm_composition_eq_piecewise
        (nonnegative_cubic_penalty lam)
        (isProper_nonnegative_cubic_penalty lam)
        (lowerSemicontinuous_nonnegative_cubic_penalty lam)
        (isConvex_nonnegative_cubic_penalty lam (le_of_lt hlam))
        (fun t ht ↦ by simp [nonnegative_cubic_penalty_apply, not_le_of_gt ht])
        x
    -- Rewrite the vector penalty as the radial lift of the scalar cubic penalty and apply
    -- Theorem 6.18 directly.
    calc
      prox[cubic_norm_penalty lam] x =
          prox[nonnegative_cubic_penalty lam ∘ (norm : E → ℝ)] x := by
            exact congrArg (fun f : E → EReal ↦ prox[f] x)
              (cubic_norm_penalty_eq_nonnegative_cubic_penalty_comp_norm lam)
      _ = if x = 0 then
            {u : E | ‖u‖ ∈ prox[nonnegative_cubic_penalty lam] 0}
          else
            (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[nonnegative_cubic_penalty lam] ‖x‖ := by
            simpa using hpiece

/-- At the origin, the proximal set of `cubic_norm_penalty lam` consists exactly of the vectors
whose norm belongs to the scalar proximal set of `nonnegative_cubic_penalty lam` at `0`. -/
@[simp] theorem prox_cubic_norm_penalty_at_zero (lam : ℝ) (hlam : 0 < lam) :
    prox[cubic_norm_penalty lam] (0 : E) =
      {u : E | ‖u‖ ∈ prox[nonnegative_cubic_penalty lam] 0} := by
  simpa using prox_cubic_norm_penalty_eq_piecewise lam hlam (0 : E)

/-- A vector belongs to `prox[cubic_norm_penalty lam] 0` exactly when its norm belongs to
`prox[nonnegative_cubic_penalty lam] 0`. -/
@[simp] theorem mem_prox_cubic_norm_penalty_at_zero_iff
    (lam : ℝ) (hlam : 0 < lam) {u : E} :
    u ∈ prox[cubic_norm_penalty lam] (0 : E) ↔ ‖u‖ ∈ prox[nonnegative_cubic_penalty lam] 0 := by
  rw [prox_cubic_norm_penalty_at_zero lam hlam]
  rfl

/-- Away from the origin, the proximal set of `cubic_norm_penalty lam` is the radial image of the
scalar proximal set of `nonnegative_cubic_penalty lam` at `‖x‖`. -/
theorem prox_cubic_norm_penalty_of_ne_zero
    (lam : ℝ) (hlam : 0 < lam) {x : E} (hx : x ≠ 0) :
    prox[cubic_norm_penalty lam] x =
      (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[nonnegative_cubic_penalty lam] ‖x‖ := by
  simpa [hx] using prox_cubic_norm_penalty_eq_piecewise lam hlam x

/-- Away from the origin, membership in `prox[cubic_norm_penalty lam] x` is equivalent to
belonging to the radial image of `prox[nonnegative_cubic_penalty lam] ‖x‖`. -/
theorem mem_prox_cubic_norm_penalty_of_ne_zero_iff
    (lam : ℝ) (hlam : 0 < lam) {x u : E} (hx : x ≠ 0) :
    u ∈ prox[cubic_norm_penalty lam] x ↔
      ∃ t : ℝ, t ∈ prox[nonnegative_cubic_penalty lam] ‖x‖ ∧ (t / ‖x‖) • x = u := by
  rw [prox_cubic_norm_penalty_of_ne_zero lam hlam hx, Set.mem_image]

end ProximalFormula

end
