/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "Z" => WithLp 2 (E × ℝ)

open WithLp
open scoped ConvexAnalysis
open scoped SupportFunction

/-
Remark 3.1.2.2 lies in the chapter's support-function / extended-real supremum domain.

Sampled owner-style declarations:
- `supportFunction` from `Definition_3_9`, the chapter's source-facing `EReal`-valued support
  supremum owner;
- `supportFunction_apply` from `Definition_3_9`, the defining evaluation formula for that owner;
- `supportFunction_convexHull_eq` from `Definition_3_9`, showing that the chapter owner is the
  ambient support-function abstraction rather than a coordinate-bound wrapper;
- `extendedRealEffectiveDomain` / notation `dom` from `Definition_3_1_1_2`, the chapter owner for
  finite-value domains of `EReal`-valued functions;
- the canonical `WithLp.toLp 2` transport, since mathlib's `L²` product owner lives on
  `WithLp 2 (E × ℝ)` rather than on the raw product.

Best owner abstraction:
- source-facing: the raw lifted set `quadraticSupportLift Q ⊆ E × ℝ`;
- core/canonical: the chapter owner `supportFunction`, applied to the canonical `L²` bridge
  `quadraticSupportLiftL2 Q ⊆ WithLp 2 (E × ℝ)`;
- bridge/view: `quadraticSupportLiftL2`, together with the defining evaluation formula and the
  whole-space `dom` description.

Primitive data:
- a set `Q : Set E`.

Derived API:
- `quadraticSupportLift Q`;
- its canonical `L²` bridge `quadraticSupportLiftL2 Q`;
- `supportFunction_quadraticSupportLift_apply`;
- the explicit whole-space value formula and its effective-domain corollaries.

The regularized supremum is not kept as a second root owner. Its intrinsic content is the chapter
support function of the canonical `L²` bridge of the lifted set
`{(y, -(‖y‖² / 2)) | y ∈ Q} ⊆ E × ℝ`. The raw product lift remains the source-facing object, while
the thin bridge `quadraticSupportLiftL2` is the ergonomics layer required because mathlib's
inner-product product owner lives on `WithLp 2 (E × ℝ)`. The textbook `ℝⁿ` statement is the
specialization `E = EuclideanSpace ℝ (Fin n)`.
-/

/-- The lifted set whose support function is the quadratically regularized support formula. -/
def quadraticSupportLift (Q : Set E) : Set (E × ℝ) :=
  (fun y : E ↦ (y, -(‖y‖ ^ 2) / 2)) '' Q

/-- The canonical `L²`-product view of `quadraticSupportLift Q`, where the support-function owner
acts. This is only the `WithLp.toLp 2` codomain bridge, not a second mathematical owner. -/
abbrev quadraticSupportLiftL2 (Q : Set E) : Set Z :=
  toLp 2 '' quadraticSupportLift Q

/-- Remark 3.1.2.2: the support function of the lifted set `quadraticSupportLift Q` sends
`(g, γ)` to the supremum over `y ∈ Q` of `⟪g, y⟫ - (γ / 2) ‖y‖²`, viewed in `EReal`. -/
theorem supportFunction_quadraticSupportLift_apply (Q : Set E) (g : E) (γ : ℝ) :
    ξ[quadraticSupportLiftL2 Q] (toLp 2 (g, γ)) =
      sSup
        ((fun y : E ↦ (((inner ℝ g y) - (γ / 2) * ‖y‖ ^ 2 : ℝ) : EReal)) '' Q) := by
  -- Rewrite the support function on the lifted `L²` set as the image of the raw quadratic slice.
  rw [supportFunction_apply]
  have himage :
      (fun z : Z ↦ ((inner ℝ z (toLp 2 (g, γ)) : ℝ) : EReal)) '' quadraticSupportLiftL2 Q =
        (fun y : E ↦ (((inner ℝ g y) - (γ / 2) * ‖y‖ ^ 2 : ℝ) : EReal)) '' Q := by
    ext a
    constructor
    · rintro ⟨z, ⟨w, ⟨y, hyQ, rfl⟩, rfl⟩, rfl⟩
      refine ⟨y, hyQ, ?_⟩
      simp only
      rw [WithLp.prod_inner_apply, real_inner_comm]
      congr
      norm_num [inner]
      ring
    · rintro ⟨y, hyQ, rfl⟩
      refine ⟨toLp 2 (y, -(‖y‖ ^ 2) / 2), ?_, ?_⟩
      · exact ⟨(y, -(‖y‖ ^ 2) / 2), ⟨y, hyQ, rfl⟩, rfl⟩
      · simp only
        rw [WithLp.prod_inner_apply, real_inner_comm]
        congr
        norm_num [inner]
        ring
  rw [himage]

/-- Helper for Remark 3.1.2.2: for `γ > 0`, the quadratic slice is obtained by completing the
square around the maximizer `γ⁻¹ • g`. -/
lemma quadratic_support_complete_square (g y : E) {γ : ℝ} (hγ : 0 < γ) :
    inner ℝ g y - (γ / 2) * ‖y‖ ^ 2 =
      ‖g‖ ^ 2 / (2 * γ) - (γ / 2) * ‖y - γ⁻¹ • g‖ ^ 2 := by
  -- Expand the norm square and collect the linear and quadratic terms in `y`.
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  rw [norm_sub_sq_real]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hγ)]
  rw [real_inner_smul_right, real_inner_comm y g]
  field_simp [hγ0]
  ring

/-- The positive-parameter branch of the whole-space lifted support function equals
`‖g‖² / (2γ)`. In the textbook specialization `E = EuclideanSpace ℝ (Fin n)`, this remains valid
even in the degenerate case `n = 0`. -/
-- Proof sketch: maximize the concave quadratic at `y = g / γ`.
theorem supportFunction_quadraticSupportLift_univ_eq_of_pos (g : E) {γ : ℝ} (hγ : 0 < γ) :
    ξ[quadraticSupportLiftL2 (Set.univ : Set E)] (toLp 2 (g, γ)) =
      ((((‖g‖ ^ 2) / (2 * γ) : ℝ) : EReal)) := by
  -- Rewrite the whole-space support value as one `sSup` over the scalar quadratic slices.
  rw [supportFunction_quadraticSupportLift_apply]
  let S : Set EReal :=
    (fun y : E ↦ (((inner ℝ g y) - (γ / 2) * ‖y‖ ^ 2 : ℝ) : EReal)) '' (Set.univ : Set E)
  change sSup S = ((((‖g‖ ^ 2) / (2 * γ) : ℝ) : EReal))
  refine sSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
  · rintro _ ⟨y, -, rfl⟩
    -- The completed-square form shows every slice lies below the peak value.
    simp only
    rw [quadratic_support_complete_square g y hγ]
    have hnonneg : 0 ≤ (γ / 2) * ‖y - γ⁻¹ • g‖ ^ 2 := by
      positivity
    exact_mod_cast sub_le_self _ hnonneg
  · intro w hw
    -- The candidate `y = γ⁻¹ • g` kills the square term and attains the upper bound.
    refine ⟨((‖g‖ ^ 2) / (2 * γ) : ℝ), ?_, ?_⟩
    · refine ⟨γ⁻¹ • g, Set.mem_univ _, ?_⟩
      simp only
      rw [quadratic_support_complete_square g (γ⁻¹ • g) hγ]
      simp
    · simpa using hw

/-- The whole-space lifted support function takes the value `0` at `(0, 0)`. -/
-- Proof sketch: every term in the defining supremum is `0`.
theorem supportFunction_quadraticSupportLift_univ_eq_zero :
    ξ[quadraticSupportLiftL2 (Set.univ : Set E)] (toLp 2 ((0 : E), (0 : ℝ))) =
      (0 : EReal) := by
  -- At `(0, 0)`, every slice value is exactly `0`, so the supremum is `0`.
  rw [supportFunction_quadraticSupportLift_apply]
  simp

/-- Helper for Remark 3.1.2.2: for `γ < 0`, every real threshold is exceeded by some quadratic
slice, so the whole-space supremum is unbounded above. -/
lemma quadratic_support_large_of_neg [Nontrivial E]
    (g : E) {γ : ℝ} (hγ : γ < 0) (R : ℝ) :
    ∃ y : E, R ≤ inner ℝ g y - (γ / 2) * ‖y‖ ^ 2 := by
  -- Pick any nonzero ray and make the positive quadratic growth dominate the linear term.
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  let a : ℝ := -(γ / 2) * ‖u‖ ^ 2
  have ha : 0 < a := by
    have hneg : 0 < -(γ / 2) := by
      linarith
    have hu_sq : 0 < ‖u‖ ^ 2 := by
      have hu_norm : 0 < ‖u‖ := norm_pos_iff.mpr hu
      nlinarith
    exact mul_pos hneg hu_sq
  let c : ℝ := inner ℝ g u
  let t : ℝ := max 1 ((|c| + |R| + 1) / a)
  refine ⟨t • u, ?_⟩
  have ht1 : 1 ≤ t := le_max_left _ _
  have ht : 0 ≤ t := by
    linarith
  have hbound : |c| + |R| + 1 ≤ a * t := by
    have hquot : (|c| + |R| + 1) / a ≤ t := le_max_right _ _
    simpa [mul_comm] using (div_le_iff₀ ha).mp hquot
  have hc : -|c| ≤ c := neg_abs_le c
  have hstep1 : t * (-|c|) ≤ t * c := by
    exact mul_le_mul_of_nonneg_left hc ht
  have hstep2 : |R| + 1 ≤ a * t - |c| := by
    nlinarith
  have hnonneg : 0 ≤ a * t - |c| := by
    have : 0 ≤ |R| + 1 := by
      positivity
    linarith
  have hstep3 : a * t - |c| ≤ t * (a * t - |c|) := by
    nlinarith
  have hstep4 : t * (a * t - |c|) ≤ t * c + a * t ^ 2 := by
    nlinarith
  have hR : R ≤ |R| + 1 := by
    have hRabs : R ≤ |R| := le_abs_self R
    linarith
  have hexpr : inner ℝ g (t • u) - (γ / 2) * ‖t • u‖ ^ 2 = t * c + a * t ^ 2 := by
    simp [c, a, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    ring
  linarith [hR, hstep1, hstep2, hstep3, hstep4, hexpr]

/-- On a nontrivial real inner-product space, the negative-parameter branch of the whole-space
lifted support function is unbounded above. -/
-- Proof sketch: choose any nonzero vector and scale it to infinity, so the quadratic term
-- dominates with positive sign.
theorem supportFunction_quadraticSupportLift_univ_eq_top_of_neg [Nontrivial E]
    (g : E) {γ : ℝ} (hγ : γ < 0) :
    ξ[quadraticSupportLiftL2 (Set.univ : Set E)] (toLp 2 (g, γ)) =
      ⊤ := by
  -- Rewrite to the scalar supremum and contradict any assumption of a finite upper bound.
  rw [supportFunction_quadraticSupportLift_apply]
  let S : Set EReal :=
    (fun y : E ↦ (((inner ℝ g y) - (γ / 2) * ‖y‖ ^ 2 : ℝ) : EReal)) '' (Set.univ : Set E)
  change sSup S = ⊤
  by_contra htop
  have hslt : sSup S < ⊤ := lt_top_iff_ne_top.mpr htop
  rcases quadratic_support_large_of_neg g hγ ((sSup S).toReal + 1) with ⟨y, hy⟩
  have hy' : ((((sSup S).toReal + 1 : ℝ) : EReal)) ≤
      ((inner ℝ g y - (γ / 2) * ‖y‖ ^ 2 : ℝ) : EReal) := by
    exact_mod_cast hy
  have hsbot : sSup S ≠ ⊥ := by
    -- The slice at `y = 0` already shows that the supremum is not `⊥`.
    intro hsbot
    have hzero_mem : (0 : EReal) ≤ sSup S := by
      apply le_sSup
      refine ⟨0, Set.mem_univ _, ?_⟩
      simp
    simp [hsbot] at hzero_mem
  have hlt : sSup S < ((((sSup S).toReal + 1 : ℝ) : EReal)) := by
    rw [← EReal.coe_toReal hslt.ne hsbot]
    exact_mod_cast (show (sSup S).toReal < (sSup S).toReal + 1 by linarith)
  have hmem : ((inner ℝ g y - (γ / 2) * ‖y‖ ^ 2 : ℝ) : EReal) ≤ sSup S := by
    apply le_sSup
    exact ⟨y, Set.mem_univ _, rfl⟩
  exact not_lt_of_ge (le_trans hy' hmem) hlt

/-- Helper for Remark 3.1.2.2: if `g ≠ 0`, then the linear slice `y ↦ ⟪g, y⟫` exceeds every real
threshold along the ray generated by `g`. -/
lemma quadratic_support_large_of_zero_ne_zero {g : E} (hg : g ≠ 0) (R : ℝ) :
    ∃ y : E, R ≤ inner ℝ g y := by
  -- Scale `g` so that the value becomes `R + |R| + 1`, which is strictly above `R`.
  have hg_sq : 0 < ‖g‖ ^ 2 := by
    have hg_norm : 0 < ‖g‖ := norm_pos_iff.mpr hg
    nlinarith
  let t : ℝ := (R + |R| + 1) / (‖g‖ ^ 2)
  refine ⟨t • g, ?_⟩
  have ht_eval : inner ℝ g (t • g) = R + |R| + 1 := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    dsimp [t]
    field_simp [ne_of_gt hg_sq]
  have hR : R ≤ R + |R| + 1 := by
    have hRabs : 0 ≤ |R| := abs_nonneg R
    linarith
  linarith [ht_eval, hR]

/-- For a nonzero vector `g`, the zero-parameter branch of the whole-space lifted support
function is unbounded above. -/
-- Proof sketch: with `γ = 0`, the defining supremum is the support function of the whole space,
-- which is unbounded above when `g ≠ 0`.
theorem supportFunction_quadraticSupportLift_univ_eq_top_of_zero_ne_zero {g : E} (hg : g ≠ 0) :
    ξ[quadraticSupportLiftL2 (Set.univ : Set E)] (toLp 2 (g, 0)) =
      ⊤ := by
  -- Route correction: this branch is purely linear, so use the ray generated by `g` itself.
  rw [supportFunction_quadraticSupportLift_apply]
  simp only [zero_div, zero_mul, sub_zero]
  let S : Set EReal := (fun y : E ↦ ((inner ℝ g y : ℝ) : EReal)) '' (Set.univ : Set E)
  change sSup S = ⊤
  by_contra htop
  have hslt : sSup S < ⊤ := lt_top_iff_ne_top.mpr htop
  rcases quadratic_support_large_of_zero_ne_zero hg ((sSup S).toReal + 1) with ⟨y, hy⟩
  have hy' : ((((sSup S).toReal + 1 : ℝ) : EReal)) ≤ ((inner ℝ g y : ℝ) : EReal) := by
    exact_mod_cast hy
  have hsbot : sSup S ≠ ⊥ := by
    -- The point `y = 0` contributes the finite value `0`.
    intro hsbot
    have hzero_mem : (0 : EReal) ≤ sSup S := by
      apply le_sSup
      refine ⟨0, Set.mem_univ _, ?_⟩
      simp
    simp [hsbot] at hzero_mem
  have hlt : sSup S < ((((sSup S).toReal + 1 : ℝ) : EReal)) := by
    rw [← EReal.coe_toReal hslt.ne hsbot]
    exact_mod_cast (show (sSup S).toReal < (sSup S).toReal + 1 by linarith)
  have hmem : ((inner ℝ g y : ℝ) : EReal) ≤ sSup S := by
    apply le_sSup
    exact ⟨y, Set.mem_univ _, rfl⟩
  exact not_lt_of_ge (le_trans hy' hmem) hlt

/-- On a nontrivial real inner-product space, the finite-value domain `dom` of the whole-space
lifted support function is exactly `(E × {γ > 0}) ∪ {(0, 0)}` in the raw `(g, γ)` coordinates. -/
-- Proof sketch: use the four whole-space value formulas above; under nontriviality the
-- displayed values are
-- always finite reals or `⊤`, never `⊥`, so `dom` excludes exactly the `⊤` branch.
theorem supportFunction_quadraticSupportLift_univ_dom [Nontrivial E] :
    toLp 2 ⁻¹' dom ξ[quadraticSupportLiftL2 (Set.univ : Set E)] =
      {p : E × ℝ | 0 < p.2 ∨ (p.1 = 0 ∧ p.2 = 0)} := by
  -- Split the raw coordinates by the sign of `γ` and invoke the branch formulas above.
  ext p
  rcases p with ⟨g, γ⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · intro hp
    rcases hp with ⟨hp_top, _⟩
    by_cases hγpos : 0 < γ
    · exact Or.inl hγpos
    · have hγle : γ ≤ 0 := le_of_not_gt hγpos
      by_cases hγzero : γ = 0
      · right
        constructor
        · by_contra hg
          exact hp_top (by
            simpa [hγzero] using
              supportFunction_quadraticSupportLift_univ_eq_top_of_zero_ne_zero hg)
        · exact hγzero
      · have hγneg : γ < 0 := lt_of_le_of_ne hγle hγzero
        exact False.elim (hp_top (supportFunction_quadraticSupportLift_univ_eq_top_of_neg g hγneg))
  · intro hp
    rcases hp with hγpos | ⟨hg0, hγ0⟩
    · constructor
      · rw [supportFunction_quadraticSupportLift_univ_eq_of_pos g hγpos]
        exact EReal.coe_ne_top _
      · rw [supportFunction_quadraticSupportLift_univ_eq_of_pos g hγpos]
        exact EReal.coe_ne_bot _
    · subst hg0
      subst hγ0
      constructor
      · rw [supportFunction_quadraticSupportLift_univ_eq_zero]
        norm_num
      · rw [supportFunction_quadraticSupportLift_univ_eq_zero]
        norm_num

/-- On a nontrivial real inner-product space, the whole-space lifted support function lies in
`dom` at `(g, γ)` exactly when `γ > 0` or `(g, γ) = (0, 0)`. -/
theorem supportFunction_quadraticSupportLift_univ_mem_dom_iff [Nontrivial E] (g : E) (γ : ℝ) :
    toLp 2 (g, γ) ∈ dom ξ[quadraticSupportLiftL2 (Set.univ : Set E)] ↔
      0 < γ ∨ (g = 0 ∧ γ = 0) := by
  -- This is the pointwise restatement of the raw-coordinate domain equality.
  change (g, γ) ∈ toLp 2 ⁻¹' dom ξ[quadraticSupportLiftL2 (Set.univ : Set E)] ↔
    0 < γ ∨ (g = 0 ∧ γ = 0)
  rw [supportFunction_quadraticSupportLift_univ_dom]
  rfl

end
