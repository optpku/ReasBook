/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_47
import Mathlib.Analysis.Convex.Intrinsic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped WithTopConvexAnalysis

/- Theorem 3.45 lies in the constrained strong-convexity / bounded-sublevel / minimizer-existence
domain.

Sampled owner-style declarations:
- mathlib `StrongConvexOn`
- project `𝒮^0_μ(Q)` in `Definition_3_47`
- mathlib `StrictConvexOn.eq_of_isMinOn`
- mathlib `LowerSemicontinuousOn.exists_isMinOn`
- mathlib `isCompact_of_isClosed_isBounded`
- project `constrainedSublevelSet` in `Definition_3_3`

Best owner abstraction:
- source-facing: `f ∈ 𝒮^0_μ(Q)` on `Q ⊂ ℝ^n`, together with the bounded nonempty constrained
  level-set conclusion
- core/canonical: `StrongConvexOn Q μ f`
- bridge/view: the coercion of a real-valued objective `f : E → ℝ` to its canonical
  `WithTop ℝ`-valued view `((↑) : ℝ → WithTop ℝ) ∘ f` so that sublevel sets use the chapter owner
  `constrainedSublevelSet`

Primitive data:
- a feasible set `Q`, a real-valued objective `f`, and a strong-convexity modulus `μ`
- for attainment, the genuine extra data `IsClosed Q` and `LowerSemicontinuousOn f Q`
- for the source-facing bridge theorem, continuity of `f` on the closed feasible set

Derived API:
- boundedness of the constrained sublevel sets
- under extra closedness/regularity hypotheses, existence and uniqueness of a feasible minimizer
- the continuity-on-closed-set bridge to the lower-semicontinuous owner theorem

This file keeps the source-facing theorem on the chapter owner `f ∈ 𝒮^0_μ(Q)` and uses the
canonical core predicate `StrongConvexOn Q μ f` only for companion lemmas. The only duplicate
wheel in the previous version was the raw set `Q ∩ {x | f x ≤ α}`, which is canonically the
chapter owner `constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α`. The closedness /
lower-semicontinuity hypotheses appear only in separate companion existence lemmas rather than in
the main source-facing statement. -/

namespace StrongConvexOn

section BoundedSublevel

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Theorem 3.45: reflecting a point across a center stays in the affine span of the
original set. -/
lemma lineMap_two_eq_reflectedPoint (x0 z : E) :
    AffineMap.lineMap z x0 (2 : ℝ) = (2 : ℝ) • x0 - z := by
  rw [AffineMap.lineMap_apply_module]
  have hzneg : (1 - (2 : ℝ)) • z = -z := by
    norm_num
  rw [hzneg]
  simp [sub_eq_add_neg, two_smul, add_assoc, add_comm]

/-- Helper for Theorem 3.45: reflecting a point across a center stays in the affine span of the
original set. -/
lemma reflectedPoint_mem_affineSpan {A : Set E} {x0 z : E}
    (hx0 : x0 ∈ affineSpan ℝ A) (hz : z ∈ affineSpan ℝ A) :
    (2 : ℝ) • x0 - z ∈ affineSpan ℝ A := by
  rw [← lineMap_two_eq_reflectedPoint]
  exact AffineMap.lineMap_mem (Q := affineSpan ℝ A) (2 : ℝ) hz hx0

/-- Helper for Theorem 3.45: reflecting a point across a center preserves the distance to that
center. -/
lemma dist_reflectedPoint_eq (x0 z : E) :
    dist ((2 : ℝ) • x0 - z) x0 = dist z x0 := by
  rw [dist_eq_norm, dist_eq_norm]
  have hreflect : (2 : ℝ) • x0 - z - x0 = -(z - x0) := by
    simp [sub_eq_add_neg, two_smul, add_assoc, add_left_comm, add_comm]
  rw [hreflect, norm_neg]

/-- Helper for Theorem 3.45: the midpoint of a point and its reflection across `x0` is `x0`. -/
lemma lineMap_reflectedPoint_half (x0 z : E) :
    AffineMap.lineMap z ((2 : ℝ) • x0 - z) (1 / 2 : ℝ) = x0 := by
  simp [AffineMap.lineMap_apply_module, one_div, sub_eq_add_neg, two_smul, add_assoc,
    add_comm]
  module

/-- Helper for Theorem 3.45: convexity turns an upper bound at a reflected point into a lower
bound at the original point. -/
lemma lowerBound_of_reflectedPoint
    {Q : Set E} {f : E → ℝ} {α : ℝ} {x0 z w : E}
    (hf_convex : ConvexOn ℝ Q f) (hzQ : z ∈ Q) (hwQ : w ∈ Q)
    (hmid : AffineMap.lineMap z w (1 / 2 : ℝ) = x0) (hwα : f w ≤ α) :
    2 * f x0 - α ≤ f z := by
  have hconv :
      f ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w) ≤ (1 / 2 : ℝ) * f z + (1 / 2 : ℝ) * f w := by
    exact hf_convex.2 hzQ hwQ
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hmid' : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w = x0 := by
    have hmid0 : (1 - (1 / 2 : ℝ)) • z + (1 / 2 : ℝ) • w = x0 := by
      simpa [AffineMap.lineMap_apply_module] using hmid
    norm_num at hmid0 ⊢
    exact hmid0
  have hx0_convex : f x0 ≤ (1 / 2 : ℝ) * f z + (1 / 2 : ℝ) * f w := by
    rw [hmid'] at hconv
    exact hconv
  linarith

variable [FiniteDimensional ℝ E]

/-- Helper for Theorem 3.45: a nonempty constrained sublevel set of a positive strongly convex
objective contains an intrinsic closed ball on which the objective has a finite lower bound. -/
lemma exists_localLowerBound_on_intrinsicClosedBall
    {Q : Set E} {f : E → ℝ} {μ α : ℝ}
    (hf : StrongConvexOn Q μ f) (hμ : 0 < μ)
    (hA_nonempty :
      (constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α).Nonempty) :
    ∃ x0 ∈ constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α,
      ∃ r > 0, ∃ m : ℝ,
        ∀ z : E,
          z ∈ constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α ∩
              Metric.closedBall x0 r →
            m ≤ f z := by
  let A : Set E := constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α
  have hf_convex : ConvexOn ℝ Q f := by
    simpa using (strongConvexOn_zero.mp (hf.mono hμ.le))
  have hA_eq : A = {x ∈ Q | f x ≤ α} := by
    -- Rewrite the chapter owner into the ordinary real-valued constrained sublevel set.
    ext x
    simp [A]
  have hA_convex : Convex ℝ A := by
    -- The strong-convex objective is convex, so its constrained real sublevel sets are convex.
    let B : Set E := {x ∈ Q | f x ≤ α}
    have hB_convex : Convex ℝ B := hf_convex.convex_le α
    simpa [hA_eq, B] using hB_convex
  obtain ⟨x0, hx0_intrinsic⟩ :
      (intrinsicInterior ℝ A).Nonempty :=
    hA_nonempty.intrinsicInterior hA_convex
  rcases mem_intrinsicInterior.mp hx0_intrinsic with ⟨x0', hx0'_int, rfl⟩
  let S : Set (affineSpan ℝ A) := ((↑) ⁻¹' A : Set (affineSpan ℝ A))
  have hx0A : (x0' : E) ∈ A := by
    simpa [S] using (interior_subset hx0'_int)
  have hS_nhds : S ∈ nhds x0' := mem_interior_iff_mem_nhds.mp hx0'_int
  rcases Metric.mem_nhds_iff.mp hS_nhds with ⟨ρ, hρ_pos, hρ_subset⟩
  refine ⟨(x0' : E), by simpa [A] using hx0A, ρ / 2, by positivity, 2 * f x0' - α, ?_⟩
  intro z hz
  rcases hz with ⟨hzA, hz_ball⟩
  let z0 : affineSpan ℝ A := ⟨z, subset_affineSpan ℝ A hzA⟩
  have hz0_dist : dist z0 x0' ≤ ρ / 2 := by
    simpa [Metric.mem_closedBall] using hz_ball
  have hz0_ball : z0 ∈ Metric.ball x0' ρ := by
    simpa [Metric.mem_ball] using lt_of_le_of_lt hz0_dist (half_lt_self hρ_pos)
  let w : E := (2 : ℝ) • (x0' : E) - z
  have hw_mem_affineSpan : w ∈ affineSpan ℝ A := by
    exact reflectedPoint_mem_affineSpan x0'.property z0.property
  let w0 : affineSpan ℝ A := ⟨w, hw_mem_affineSpan⟩
  have hw0_ball' : dist ((⟨w, hw_mem_affineSpan⟩ : affineSpan ℝ A) : E) (x0' : E) < ρ := by
    rw [show ((⟨w, hw_mem_affineSpan⟩ : affineSpan ℝ A) : E) = w by rfl]
    rw [dist_reflectedPoint_eq]
    exact lt_of_le_of_lt (by simpa using hz0_dist) (half_lt_self hρ_pos)
  have hw0_ball : w0 ∈ Metric.ball x0' ρ := by
    rw [Metric.mem_ball]
    change dist ↑(⟨w, hw_mem_affineSpan⟩ : affineSpan ℝ A) ↑x0' < ρ
    simpa using hw0_ball'
  have hw0A : w ∈ A := by
    exact hρ_subset hw0_ball
  have hzQ : z ∈ Q := (mem_constrainedSublevelSet_iff.mp hzA).1
  have hw0Q : w ∈ Q := (mem_constrainedSublevelSet_iff.mp hw0A).1
  have hw0α : f w ≤ α := by
    exact WithTop.coe_le_coe.mp (mem_constrainedSublevelSet_iff.mp hw0A).2
  exact lowerBound_of_reflectedPoint (Q := Q) (f := f) (α := α) (x0 := (x0' : E))
    (z := z) (w := w) hf_convex hzQ hw0Q
    (lineMap_reflectedPoint_half (x0' : E) z) hw0α

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.45: a local lower bound on one feasible closed ball turns strong
convexity into a global radius bound for the whole constrained sublevel set. -/
lemma norm_le_of_mem_constrainedSublevelSet_of_localLowerBound
    {Q : Set E} {f : E → ℝ} {μ α m r : ℝ} {x0 : E}
    (hf : StrongConvexOn Q μ f) (hμ : 0 < μ)
    (hr : 0 < r)
    (hx0A : x0 ∈ constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α)
    (hm : ∀ z : E,
      z ∈ constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α ∩ Metric.closedBall x0 r →
        m ≤ f z)
    {x : E}
    (hx : x ∈ constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α) :
    ‖x - x0‖ ≤ r + 2 * (α - m) / (μ * r) := by
  rcases mem_constrainedSublevelSet_iff.mp hx0A with ⟨hx0Q, hx0α_top⟩
  rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxQ, hxα_top⟩
  have hx0α : f x0 ≤ α := by
    exact WithTop.coe_le_coe.mp hx0α_top
  have hxα : f x ≤ α := by
    exact WithTop.coe_le_coe.mp hxα_top
  let B : ℝ := r + 2 * (α - m) / (μ * r)
  have hm_le_fx0 : m ≤ f x0 := by
    -- Apply the local lower bound to the base point itself.
    refine hm x0 ⟨hx0A, ?_⟩
    simp [Metric.mem_closedBall, hr.le]
  have hm_le_α : m ≤ α := le_trans hm_le_fx0 hx0α
  have hB_ge_r : r ≤ B := by
    -- The base-point estimate `m ≤ f x0 ≤ α` guarantees that the final enclosing radius already
    -- contains the local comparison ball.
    have hαm_nonneg : 0 ≤ α - m := sub_nonneg.mpr hm_le_α
    have hμr_nonneg : 0 ≤ μ * r := mul_nonneg hμ.le hr.le
    have hnonneg : 0 ≤ 2 * (α - m) / (μ * r) := by
      exact div_nonneg (mul_nonneg (by positivity) hαm_nonneg) hμr_nonneg
    dsimp [B]
    linarith
  by_cases hR_le : ‖x - x0‖ ≤ r
  · -- Points already inside the local comparison ball are automatically inside the final
    -- enclosing ball.
    dsimp [B]
    exact hR_le.trans hB_ge_r
  · let R : ℝ := ‖x - x0‖
    have hR_def : R = ‖x - x0‖ := rfl
    have hR_gt : r < R := by
      dsimp [R]
      linarith
    have hR_pos : 0 < R := lt_trans hr hR_gt
    let t : ℝ := r / R
    let z : E := AffineMap.lineMap x0 x t
    have ht_pos : 0 < t := by
      dsimp [t]
      exact div_pos hr hR_pos
    have ht_nonneg : 0 ≤ t := ht_pos.le
    have ht_lt_one : t < 1 := by
      dsimp [t]
      exact (div_lt_one hR_pos).2 hR_gt
    have h1t_nonneg : 0 ≤ 1 - t := by
      linarith
    have hzQ : z ∈ Q := by
      -- The contracted point lies on the feasible segment from `x0` to `x`.
      simpa [z, AffineMap.lineMap_apply_module] using
        (hf.1 hx0Q hxQ h1t_nonneg ht_nonneg (by ring))
    have hzA :
        z ∈ constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α := by
      have hf_convex : ConvexOn ℝ Q f := by
        simpa using (strongConvexOn_zero.mp (hf.mono hμ.le))
      let A : Set E := {u ∈ Q | f u ≤ α}
      have hx0A' : x0 ∈ A := by
        simpa [A, mem_constrainedSublevelSet_iff] using hx0A
      have hxA' : x ∈ A := by
        simpa [A, mem_constrainedSublevelSet_iff] using hx
      have hzA' : z ∈ A := by
        simpa [z, A, AffineMap.lineMap_apply_module] using
          (hf_convex.convex_le α) hx0A' hxA' h1t_nonneg ht_nonneg (by ring)
      simpa [A, mem_constrainedSublevelSet_iff] using hzA'
    have hz_ball : z ∈ Metric.closedBall x0 r := by
      -- The contraction parameter `t = r / ‖x - x0‖` places `z` exactly on the sphere of radius
      -- `r` around `x0`.
      have hz_norm : ‖z - x0‖ = r := by
        calc
          ‖z - x0‖ = ‖t • (x - x0)‖ := by
            simp [z, AffineMap.lineMap_apply_module', sub_eq_add_neg]
          _ = |t| * ‖x - x0‖ := norm_smul t (x - x0)
          _ = t * R := by
            rw [abs_of_pos ht_pos, hR_def]
          _ = r := by
            dsimp [t]
            field_simp [hR_pos.ne']
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz_norm.le
    have hm_le_fz : m ≤ f z := hm z ⟨hzA, hz_ball⟩
    have hstrong := hf.2 hx0Q hxQ h1t_nonneg ht_nonneg (by ring)
    have hupper : f z ≤ α - (μ / 2) * (r * (R - r)) := by
      -- Route correction: reuse the Chapter 2 radial contraction algebra here, with the explicit
      -- local lower bound `m ≤ f z` supplying the only external input.
      have hfactor : (1 - t) * t * R ^ (2 : ℕ) = r * (R - r) := by
        dsimp [t]
        field_simp [hR_pos.ne']
      have hweighted : (1 - t) * f x0 + t * f x ≤ α := by
        have hleft : (1 - t) * f x0 ≤ (1 - t) * α :=
          mul_le_mul_of_nonneg_left hx0α h1t_nonneg
        have hright : t * f x ≤ t * α :=
          mul_le_mul_of_nonneg_left hxα ht_nonneg
        have hsum : (1 - t) * α + t * α = α := by
          ring
        linarith
      calc
        f z ≤ (1 - t) * f x0 + t * f x - (1 - t) * t * ((μ / 2) * ‖x0 - x‖ ^ (2 : ℕ)) := by
          simpa [z, AffineMap.lineMap_apply_module] using hstrong
        _ ≤ α - (1 - t) * t * ((μ / 2) * ‖x0 - x‖ ^ (2 : ℕ)) := by
          exact sub_le_sub_right hweighted _
        _ = α - (μ / 2) * (r * (R - r)) := by
          have hrewrite :
              (1 - t) * t * ((μ / 2) * R ^ (2 : ℕ)) = (μ / 2) * (r * (R - r)) := by
            rw [← hfactor]
            ring
          rw [norm_sub_rev, ← hR_def, hrewrite]
    have hbound' : μ * (r * (R - r)) ≤ 2 * (α - m) := by
      -- Compare the local lower bound with the contracted-point upper bound.
      nlinarith
    have hR_sub : R - r ≤ 2 * (α - m) / (μ * r) := by
      have hμr_pos : 0 < μ * r := mul_pos hμ hr
      have hmul : (R - r) * (μ * r) ≤ 2 * (α - m) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hbound'
      exact (le_div_iff₀ hμr_pos).2 hmul
    have hR_bound : R ≤ B := by
      dsimp [B]
      linarith
    simpa [B, hR_def] using hR_bound

/-- In a finite-dimensional real normed space, every constrained level set of a positive strongly
convex real-valued objective is bounded. -/
theorem isBounded_constrainedSublevelSet
    {Q : Set E} {f : E → ℝ} {μ α : ℝ}
    (hf : StrongConvexOn Q μ f) (hμ : 0 < μ) :
    Bornology.IsBounded
      (constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α) := by
  classical
  let A : Set E := constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α
  by_cases hA_empty : A = ∅
  · -- The empty constrained sublevel set is bounded trivially.
    simp [A, hA_empty]
  · have hA_nonempty : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA_empty
    obtain ⟨x0, hx0A, r, hr, m, hm⟩ :=
      exists_localLowerBound_on_intrinsicClosedBall hf hμ
        (show A.Nonempty by simpa [A] using hA_nonempty)
    -- Route correction: once the sublevel set contains a compact intrinsic closed ball with a
    -- finite lower bound, the radial contraction estimate gives the global bound.
    refine (Metric.isBounded_iff_subset_closedBall x0).2 ?_
    refine ⟨r + 2 * (α - m) / (μ * r), ?_⟩
    intro x hx
    have hnorm :
        ‖x - x0‖ ≤ r + 2 * (α - m) / (μ * r) :=
      norm_le_of_mem_constrainedSublevelSet_of_localLowerBound hf hμ hr hx0A hm
        (show x ∈ constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α by simpa [A] using hx)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm

end BoundedSublevel

section SourceTheorem

open scoped StrongConvex

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/-- Theorem 3.45: if `Q ⊂ ℝ^n` is nonempty and `f ∈ 𝒮^0_μ(Q)`, then every nonempty constrained
level set `L_α = {x ∈ Q : f x ≤ α}` is bounded. -/
theorem boundedSublevels_of_mem_S0On
    {Q : Set Eₙ} {f : Eₙ → ℝ} {μ : ℝ}
    (hf : f ∈ 𝒮^0_μ(Q)) (hQ_nonempty : Q.Nonempty) :
    ∀ α : ℝ,
      (constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α).Nonempty →
        Bornology.IsBounded
          (constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α) := by
  intro α hα_nonempty
  have _ : Q.Nonempty := hQ_nonempty
  -- The source-facing class membership packages the positive strong-convexity owner directly.
  have hμ : 0 < μ := StrongConvexOnClass.mu_pos hf
  have hstrong : StrongConvexOn Q μ f := StrongConvexOnClass.strongConvexOn hf
  -- The boundedness owner theorem is independent of the chosen nonempty sublevel witness.
  simpa using hstrong.isBounded_constrainedSublevelSet (α := α) hμ

end SourceTheorem

section Existence

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- In a finite-dimensional real normed space, a positive strongly convex real-valued objective on
a nonempty closed feasible set has a unique feasible minimizer once the objective is lower
semicontinuous on that feasible set. -/
theorem existsUnique_isMinOn_of_isClosed_lowerSemicontinuousOn
    {Q : Set E} {f : E → ℝ} {μ : ℝ}
    (hf : StrongConvexOn Q μ f) (hμ : 0 < μ)
    (hf_lower : LowerSemicontinuousOn f Q)
    (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) :
    ∃! x : E, x ∈ Q ∧ IsMinOn f Q x := by
  rcases hQ_nonempty with ⟨x0, hx0Q⟩
  let S : Set E := constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) (f x0)
  have hx0S : x0 ∈ S := by
    -- The chosen feasible base point belongs to its own constrained sublevel slice.
    exact mem_constrainedSublevelSet_iff.2 ⟨hx0Q, le_rfl⟩
  have hS_subset : S ⊆ Q := by
    -- Membership in the constrained sublevel slice includes feasibility.
    intro x hx
    exact (mem_constrainedSublevelSet_iff.mp hx).1
  have hS_eq_preimage :
      S = Q ∩ f ⁻¹' Set.Iic (f x0) := by
    -- Normalize the chapter owner `constrainedSublevelSet` to an ordinary real sublevel slice.
    ext x
    constructor
    · intro hx
      rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxQ, hxfx⟩
      refine ⟨hxQ, ?_⟩
      simpa using hxfx
    · rintro ⟨hxQ, hxfx⟩
      refine mem_constrainedSublevelSet_iff.2 ⟨hxQ, ?_⟩
      simpa using hxfx
  have hS_closed : IsClosed S := by
    -- Lower semicontinuity on `Q` makes the base slice closed after rewriting it as
    -- `Q ∩ f ⁻¹' Set.Iic (f x0)`.
    obtain ⟨v, hv_closed, hv_eq⟩ := (lowerSemicontinuousOn_iff_preimage_Iic.mp hf_lower) (f x0)
    rw [hS_eq_preimage, hv_eq]
    exact hQ_closed.inter hv_closed
  have hS_bounded : Bornology.IsBounded S := by
    -- Route correction: reuse the owner bounded-sublevel theorem once at the base value `f x0`,
    -- then keep the compact-slice proof downstream of that owner API.
    simpa [S] using hf.isBounded_constrainedSublevelSet (α := f x0) hμ
  have hS_compact : IsCompact S :=
    Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
  have hf_lower_S : LowerSemicontinuousOn f S :=
    hf_lower.mono hS_subset
  obtain ⟨xStar, hxStarS, hxStarMinS⟩ := hf_lower_S.exists_isMinOn ⟨x0, hx0S⟩ hS_compact
  have hxStarQ : xStar ∈ Q := hS_subset hxStarS
  have hxStarMinQ : IsMinOn f Q xStar := by
    -- The compact-slice minimizer is already minimal on `S`; outside `S` every feasible point
    -- has objective value strictly above the threshold `f x0`.
    intro y hyQ
    by_cases hyS : y ∈ S
    · exact hxStarMinS hyS
    · have hy_gt : f x0 < f y := by
        refine lt_of_not_ge ?_
        intro hy_le
        have hy_mem : y ∈ S := by
          refine mem_constrainedSublevelSet_iff.2 ⟨hyQ, ?_⟩
          show (((↑) : ℝ → WithTop ℝ) ∘ f) y ≤ (f x0 : WithTop ℝ)
          simpa using hy_le
        exact hyS hy_mem
      have hxStar_le_x0 : f xStar ≤ f x0 := hxStarMinS hx0S
      exact le_trans hxStar_le_x0 hy_gt.le
  refine ⟨xStar, ⟨hxStarQ, hxStarMinQ⟩, ?_⟩
  intro y hy
  -- Positive strong convexity upgrades existence to uniqueness of the feasible minimizer.
  exact (hf.strictConvexOn hμ).eq_of_isMinOn hy.2 hxStarMinQ hy.1 hxStarQ

/-- In a finite-dimensional real normed space, a positive strongly convex real-valued objective
that is continuous on a nonempty closed feasible set has a unique feasible minimizer. -/
theorem existsUnique_isMinOn_of_isClosed
    {Q : Set E} {f : E → ℝ} {μ : ℝ}
    (hf : StrongConvexOn Q μ f) (hμ : 0 < μ)
    (hf_cont : ContinuousOn f Q)
    (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) :
    ∃! x : E, x ∈ Q ∧ IsMinOn f Q x := by
  -- Reinterpret ambient strong convexity as the Chapter 2 norm-seminorm owner theorem.
  have hnorm :
      StrongConvexOnWith (normSeminorm ℝ E) μ Q f :=
    (strongConvexOnWith_normSeminorm_iff.mpr ⟨hμ, hf⟩)
  -- The upstream continuity-based owner theorem then gives the unique feasible minimizer.
  exact hnorm.existsUnique_isMinOn_of_isClosed hf_cont hQ_nonempty hQ_closed

end Existence

section Uniqueness

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A positive strongly convex real-valued objective on a feasible set has at most one feasible
minimizer. -/
theorem eq_of_isMinOn
    {Q : Set E} {μ : ℝ} {f : E → ℝ} (hf : StrongConvexOn Q μ f) (hμ : 0 < μ)
    {xStar₁ xStar₂ : E}
    (hxStar₁ : xStar₁ ∈ Q) (hmin₁ : IsMinOn f Q xStar₁)
    (hxStar₂ : xStar₂ ∈ Q) (hmin₂ : IsMinOn f Q xStar₂) :
    xStar₁ = xStar₂ := by
  -- Positive strong convexity implies strict convexity on the feasible set.
  have hstrict : StrictConvexOn ℝ Q f := hf.strictConvexOn hμ
  -- Strict convexity identifies any two feasible minimizers.
  exact hstrict.eq_of_isMinOn hmin₁ hmin₂ hxStar₁ hxStar₂

end Uniqueness

end StrongConvexOn

end
