/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_22

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

section AffineData

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]
variable {l : ℕ}

/- Assumption 13.18 is `source-facing`: it singles out an initial point for the finite-hull
quadratic problem on a finite family of vertices `a_i`.

Domain sampling against the surrounding project and mathlib identifies the canonical owners:
- a plain objective function `f_q : E → ℝ` for the quadratic objective;
- `convexHull ℝ (Set.range a)` for the feasible polytope `Ω = conv{a₁, …, a_l}`;
- `stdSimplex ℝ (Fin l)` for the simplex weights `v⁰`;
- `positiveOrthant l` from Chapter 1 for the strict-positivity condition on those weights.

The clean public interface is therefore a `Prop`-valued class on `(f_q, a, x0, v0)`, rather than a
matrix-based wrapper for the notation `A v⁰`. -/

/-- Assumption 13.18: the starting point `x0 = x⁰` has quadratic objective value strictly below
every vertex value `f_q(a_i)`, where `Ω = conv{a₁, …, a_l}`, and `x0` is the barycentric
combination of the vertices `a_i` with strictly positive simplex weights `v0 = v⁰`. -/
class IsStrictVertexSublevelInitialPoint
    (f_q : E → ℝ) (a : Fin l → E) (x0 : E)
    (v0 : stdSimplex ℝ (Fin l)) : Prop where
  objective_lt_vertex (i : Fin l) : f_q x0 < f_q (a i)
  eq_weighted_sum : x0 = ∑ i, v0 i • a i
  weights_mem_positiveOrthant : (v0 : Fin l → ℝ) ∈ positiveOrthant l

/-- A strict-vertex-sublevel initial point has strictly positive simplex coordinates. -/
theorem IsStrictVertexSublevelInitialPoint.weight_pos
    {f_q : E → ℝ} {a : Fin l → E} {x0 : E} {v0 : stdSimplex ℝ (Fin l)}
    (h : IsStrictVertexSublevelInitialPoint f_q a x0 v0) (i : Fin l) :
    0 < v0 i := by
  have hv : ∀ j, 0 < v0 j := by
    simpa [positiveOrthant] using h.weights_mem_positiveOrthant
  exact hv i

section FeasibleSet

variable {f_q : E → ℝ} {a : Fin l → E} {x0 : E} {v0 : stdSimplex ℝ (Fin l)}

local notation "Ω" => convexHull ℝ (Set.range a)

/-- Helper for Assumption 13.18: a finite barycentric sum with nonnegative weights summing to `1`
belongs to the convex hull of the corresponding vertex family. -/
lemma weighted_sum_mem_convexHull_range
    (w : Fin l → ℝ) {x : E}
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i = 1)
    (hx : x = ∑ i, w i • a i) :
    x ∈ convexHull ℝ (Set.range a) := by
  -- View the weighted sum as the image of a point of the standard simplex under the linear map
  -- sending basis vectors to the vertices `a i`.
  let L : (Fin l → ℝ) →ₗ[ℝ] E :=
    ∑ i, (LinearMap.proj (R := ℝ) i).smulRight (a i)
  have hw_mem : (w : Fin l → ℝ) ∈ stdSimplex ℝ (Fin l) := ⟨hw_nonneg, hw_sum⟩
  have hxL : L w = x := by
    simpa [L] using hx.symm
  have hL_basis : L ∘ (fun i : Fin l ↦ Pi.single i 1) = a := by
    funext i
    simp [L]
  rw [← hxL]
  rw [← convexHull_rangle_single_eq_stdSimplex (R := ℝ) (ι := Fin l)] at hw_mem
  rw [← hL_basis, Set.range_comp, ← LinearMap.image_convexHull]
  exact ⟨w, hw_mem, rfl⟩

-- Proof sketch: rewrite `x0` using `eq_weighted_sum`, view the right-hand side as the image of the
-- simplex point `v0` under the linear map sending weights to the corresponding weighted vertex sum,
-- and apply the standard convex-hull characterization of finite barycentric combinations.
/-- A starting point satisfying the strict-vertex-sublevel assumption belongs to the feasible
polytope `Ω = conv{a₁, …, a_l}`. -/
theorem IsStrictVertexSublevelInitialPoint.mem_feasible_set
    (h : IsStrictVertexSublevelInitialPoint f_q a x0 v0) :
    x0 ∈ Ω := by
  -- The simplex coordinates of `v0` already provide the required convex-hull witness.
  refine weighted_sum_mem_convexHull_range (a := a) (w := v0) ?_ (stdSimplex.sum_eq_one v0)
    h.eq_weighted_sum
  intro i
  exact stdSimplex.zero_le _ i

end FeasibleSet

end AffineData

section InteriorFeasibleSet

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {l : ℕ}
variable {f_q : E → ℝ} {a : Fin l → E} {x0 : E} {v0 : stdSimplex ℝ (Fin l)}

local notation "Ω" => convexHull ℝ (Set.range a)

-- Proof sketch: view `Ω` through the standard finite-dimensional normed real convex-hull
-- interface; the nonempty-interior hypothesis is the full-dimensional bridge, and strictly
-- positive barycentric coordinates then place `x0` in the interior via the usual affine-basis
-- interior description of a finite convex hull.
/-- In the standard finite-dimensional normed real setting, a strictly positive barycentric
starting point lies in `interior Ω` whenever `Ω` has nonempty interior. -/
theorem IsStrictVertexSublevelInitialPoint.mem_interior_feasible_set
    (h : IsStrictVertexSublevelInitialPoint f_q a x0 v0)
    (hΩ : (interior Ω).Nonempty) :
    x0 ∈ interior Ω := by
  -- Route correction: we first extract a full-dimensional affine subbasis of the vertices, and then
  -- use that simplex as the interior source inside the larger feasible polytope.
  have hspan : affineSpan ℝ (Set.range a) = ⊤ := by
    exact (interior_convexHull_nonempty_iff_affineSpan_eq_top).mp hΩ
  obtain ⟨s, hs, b, hb⟩ := AffineBasis.exists_affine_subbasis hspan
  classical
  haveI : Finite s := b.finite
  letI : Fintype s := Fintype.ofFinite s
  letI : Nonempty s := b.nonempty
  let y : E := Finset.univ.centroid ℝ b
  have hrange : Set.range b ⊆ Set.range a := by
    intro z hz
    rcases hz with ⟨p, rfl⟩
    simpa [hb] using hs p.2
  have hyΩ : y ∈ interior Ω := by
    -- The centroid of the full-dimensional simplex spanned by `b` is interior to that simplex,
    -- hence also interior to the larger feasible polytope.
    have hyb : y ∈ interior (convexHull ℝ (Set.range b)) := by
      simpa [y] using b.centroid_mem_interior_convexHull
    exact interior_mono (convexHull_mono hrange) hyb
  let σ : s → Fin l := fun p => Classical.choose (hs p.2)
  have hσ : ∀ p : s, a (σ p) = p := by
    intro p
    exact Classical.choose_spec (hs p.2)
  have hσ_injective : Function.Injective σ := by
    intro p q hpq
    apply Subtype.ext
    calc
      (p : E) = a (σ p) := by symm; exact hσ p
      _ = a (σ q) := by rw [hpq]
      _ = (q : E) := hσ q
  let e : s ↪ Fin l := ⟨σ, hσ_injective⟩
  let t : Finset (Fin l) := Finset.univ.map e
  let m : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun p : s ↦ v0 (σ p))
  have hm_pos : 0 < m := by
    -- The representative coordinates stay strictly positive, so their finite minimum is positive.
    exact (Finset.lt_inf'_iff Finset.univ_nonempty).2 fun p _ ↦ h.weight_pos (σ p)
  have hm_le : ∀ p : s, m ≤ v0 (σ p) := by
    -- The chosen minimum is bounded above by every representative coordinate.
    intro p
    exact Finset.inf'_le _ (Finset.mem_univ p)
  have hs_card_pos_nat : 0 < Fintype.card s := Fintype.card_pos_iff.mpr b.nonempty
  have hs_card_pos : 0 < (Fintype.card s : ℝ) := by
    exact_mod_cast hs_card_pos_nat
  have hs_card_ne : (Fintype.card s : ℝ) ≠ 0 := ne_of_gt hs_card_pos
  let β : ℝ := (Fintype.card s : ℝ) * m
  have hβ_pos : 0 < β := by
    -- The peeled mass is a positive multiple of the positive minimum `m`.
    dsimp [β]
    positivity
  have hβ_le : β ≤ 1 := by
    -- The common peeled mass cannot exceed the total simplex mass.
    calc
      β = ∑ p : s, m := by
        simp [β, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
      _ ≤ ∑ p : s, v0 (σ p) := by
        exact Finset.sum_le_sum fun p _ ↦ hm_le p
      _ = Finset.sum t fun i ↦ v0 i := by
        simpa [t, e] using (Finset.univ.sum_map e fun i : Fin l ↦ v0 i).symm
      _ ≤ ∑ i, v0 i := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by intro i hi; exact Finset.mem_univ i)
          (fun i _ _ ↦ stdSimplex.zero_le _ i)
      _ = 1 := stdSimplex.sum_eq_one v0
  have hcentroid : β • y = ∑ p : s, m • a (σ p) := by
    -- The peeled uniform mass is exactly the centroid contribution from the affine subbasis.
    calc
      β • y = β • ∑ p : s, b.coord p y • b p := by
        rw [b.linear_combination_coord_eq_self y]
      _ = ∑ p : s, β • (b.coord p y • b p) := by
        simpa using
          (Finset.smul_sum (s := Finset.univ) (r := β) (f := fun p : s ↦ b.coord p y • b p))
      _ = ∑ p : s, (β * b.coord p y) • b p := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
      _ = ∑ p : s, (β * (Fintype.card s : ℝ)⁻¹) • b p := by
        apply Finset.sum_congr rfl
        intro p hp
        simpa [Finset.card_univ] using
          congrArg (fun t : ℝ ↦ (β * t) • b p)
            (by
              rw [show y = Finset.univ.centroid ℝ b by rfl]
              simpa [Finset.card_univ] using
                b.coord_apply_centroid (Finset.mem_univ p))
      _ = ∑ p : s, m • b p := by
        apply Finset.sum_congr rfl
        intro p hp
        have hβm : β * (Fintype.card s : ℝ)⁻¹ = m := by
          dsimp [β]
          calc
            ((Fintype.card s : ℝ) * m) * (Fintype.card s : ℝ)⁻¹
                = m * ((Fintype.card s : ℝ) * (Fintype.card s : ℝ)⁻¹) := by
                  ring
            _ = m := by
              rw [mul_inv_cancel₀ hs_card_ne, mul_one]
        rw [hβm]
      _ = ∑ p : s, m • a (σ p) := by
        apply Finset.sum_congr rfl
        intro p hp
        simpa [hb, hσ p]
  let ρ : Fin l → ℝ := fun i ↦ v0 i - if i ∈ t then m else 0
  have hρ_nonneg : ∀ i, 0 ≤ ρ i := by
    -- Subtracting `m` only on the representative image preserves nonnegativity.
    intro i
    by_cases hi : i ∈ t
    · have hi_range : i ∈ Set.range σ := by
        simpa [t, e] using hi
      rcases hi_range with ⟨p, rfl⟩
      simpa [ρ, hi] using (sub_nonneg.mpr (hm_le p))
    · simpa [ρ, hi] using stdSimplex.zero_le v0 i
  have hindicator_sum : (∑ i, if i ∈ t then m else 0) = β := by
    -- The indicator of the representative image counts exactly `card s` copies of `m`.
    calc
      (∑ i, if i ∈ t then m else 0) = Finset.sum t fun _ : Fin l ↦ m := by
        simpa using (Fintype.sum_ite_mem t fun _ : Fin l ↦ m)
      _ = β := by
        simp [β, t, e, Finset.card_map, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  have hρ_sum : (∑ i, ρ i) = 1 - β := by
    -- The residual weights sum to the unpeeled simplex mass.
    calc
      (∑ i, ρ i) = ∑ i, v0 i - ∑ i, if i ∈ t then m else 0 := by
        simp [ρ, Finset.sum_sub_distrib]
      _ = 1 - β := by
        rw [stdSimplex.sum_eq_one, hindicator_sum]
  have hsplit : x0 = ∑ i, ρ i • a i + β • y := by
    -- Split the original barycentric sum into the residual part and the centroid part.
    calc
      x0 = ∑ i, v0 i • a i := h.eq_weighted_sum
      _ = ∑ i, (ρ i • a i + (if i ∈ t then m else 0) • a i) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hti : i ∈ t
        · simp [ρ, hti, sub_smul]
        · simp [ρ, hti, add_smul]
      _ = ∑ i, ρ i • a i + ∑ i, (if i ∈ t then m else 0) • a i := by
        rw [Finset.sum_add_distrib]
      _ = ∑ i, ρ i • a i + Finset.sum t (fun i ↦ m • a i) := by
        congr 1
        simpa using (Fintype.sum_ite_mem t fun i : Fin l ↦ m • a i)
      _ = ∑ i, ρ i • a i + ∑ p : s, m • a (σ p) := by
        congr 1
        simpa [t, e] using (Finset.univ.sum_map e fun i : Fin l ↦ m • a i)
      _ = ∑ i, ρ i • a i + β • y := by
        rw [hcentroid]
  by_cases hβ1 : β = 1
  · have hρ_zero_sum : ∑ i, ρ i = 0 := by
      -- When `β = 1`, no residual simplex mass remains.
      simpa [hβ1] using hρ_sum
    have hρ_zero : ∀ i, ρ i = 0 := by
      -- Nonnegative weights with zero total sum must vanish coordinatewise.
      have hρ_eq_zero : ρ = 0 := (Fintype.sum_eq_zero_iff_of_nonneg hρ_nonneg).1 hρ_zero_sum
      intro i
      exact congrFun hρ_eq_zero i
    have hx0_eq_y : x0 = y := by
      -- The decomposition collapses to the centroid itself.
      calc
        x0 = ∑ i, ρ i • a i + β • y := hsplit
        _ = 0 + 1 • y := by
          simp [hβ1, hρ_zero]
        _ = y := by simp
    simpa [hx0_eq_y] using hyΩ
  · have hβ_lt_one : β < 1 := lt_of_le_of_ne hβ_le hβ1
    have hden_pos : 0 < 1 - β := sub_pos.mpr hβ_lt_one
    let w : Fin l → ℝ := fun i ↦ ρ i / (1 - β)
    let z : E := ∑ i, w i • a i
    have hw_nonneg : ∀ i, 0 ≤ w i := by
      -- Normalizing the nonnegative residual weights preserves nonnegativity.
      intro i
      exact div_nonneg (hρ_nonneg i) hden_pos.le
    have hw_sum : ∑ i, w i = 1 := by
      -- The normalized residual weights form a simplex point.
      calc
        ∑ i, w i = (∑ i, ρ i) / (1 - β) := by
          simp [w, div_eq_mul_inv, Finset.sum_mul]
        _ = (1 - β) / (1 - β) := by
          rw [hρ_sum]
        _ = 1 := by
          field_simp [hden_pos.ne']
    have hzΩ : z ∈ Ω := by
      -- The normalized residual barycentric combination stays in the feasible polytope.
      exact weighted_sum_mem_convexHull_range (a := a) (w := w) (x := z) hw_nonneg hw_sum rfl
    have hresidual : ∑ i, ρ i • a i = (1 - β) • z := by
      -- Rescaling the normalized residual point recovers the unnormalized residual sum.
      calc
        ∑ i, ρ i • a i = ∑ i, ((1 - β) * w i) • a i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hwi : (1 - β) * w i = ρ i := by
            dsimp [w]
            field_simp [hden_pos.ne']
          rw [← hwi]
        _ = (1 - β) • z := by
          rw [show z = ∑ i, w i • a i by rfl]
          simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
            (Finset.smul_sum (s := Finset.univ) (r := 1 - β) (f := fun i : Fin l ↦ w i • a i)).symm
    have hx0_combo : x0 = (1 - β) • z + β • y := by
      -- The starting point is a convex combination of the feasible residual point and the interior centroid.
      calc
        x0 = ∑ i, ρ i • a i + β • y := hsplit
        _ = (1 - β) • z + β • y := by
          rw [hresidual]
    have hcombo : (1 - β) • z + β • y ∈ interior Ω := by
      -- A positive amount of the interior centroid pushes the whole combination into the interior.
      exact (convex_convexHull ℝ (Set.range a)).combo_self_interior_mem_interior
        hzΩ hyΩ (sub_nonneg.mpr hβ_le) hβ_pos (by ring)
    exact hx0_combo ▸ hcombo

end InteriorFeasibleSet
