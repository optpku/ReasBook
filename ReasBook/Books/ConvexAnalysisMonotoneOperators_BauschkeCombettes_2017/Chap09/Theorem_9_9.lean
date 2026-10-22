/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Proposition_3_45
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_8

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace
open WithLp

universe u

namespace ERealFunction

noncomputable section

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Theorem 9.9: view `H × ℝ` with the `ℓ²` product metric used by the source proof's
projection argument. -/
local instance theorem9_9_prod_pseudoMetricSpace_l2 : PseudoMetricSpace (H × ℝ) :=
  WithLp.pseudoMetricSpaceToProd (p := 2) H ℝ

/-- Helper for Theorem 9.9: equip `H × ℝ` with the `ℓ²` product norm coming from
`WithLp 2 (H × ℝ)`. -/
local instance theorem9_9_prod_normedAddCommGroup_l2 : NormedAddCommGroup (H × ℝ) :=
  WithLp.normedAddCommGroupToProd (p := 2) H ℝ

/-- Helper for Theorem 9.9: the `ℓ²` product norm is compatible with scalar multiplication on
`H × ℝ`. -/
local instance theorem9_9_prod_normedSpace_l2 : NormedSpace ℝ (H × ℝ) := by
  letI : NormedAddCommGroup (H × ℝ) :=
    WithLp.normedAddCommGroupToProd (p := 2) H ℝ
  exact
    WithLp.normedSpaceSeminormedAddCommGroupToProd
      (p := 2) (α := H) (β := ℝ)

/-- Helper for Theorem 9.9: completeness of `H × ℝ` for the `ℓ²` product metric follows from the
uniform equivalence with `WithLp 2 (H × ℝ)`. -/
local instance theorem9_9_prod_completeSpace_l2 : CompleteSpace (H × ℝ) := by
  letI : PseudoMetricSpace (H × ℝ) :=
    WithLp.pseudoMetricSpaceToProd (p := 2) H ℝ
  exact (WithLp.uniformEquivProd (p := 2) H ℝ).completeSpace_iff.1 inferInstance

/-- Helper for Theorem 9.9: the product Hilbert structure on `H × ℝ` is the textbook one
`⟪(u, a), (v, b)⟫ = ⟪u, v⟫ + ab`. -/
local instance theorem9_9_prod_innerProductSpace_l2 : InnerProductSpace ℝ (H × ℝ) where
  inner x y := ⟪x.1, y.1⟫_ℝ + x.2 * y.2
  norm_sq_eq_re_inner x := by
    -- The `ℓ²` product norm is exactly the sum of the squared component norms.
    rw [show ‖x‖ = ‖WithLp.toLp 2 x‖ by rfl, WithLp.prod_norm_sq_eq_of_L2]
    simp [sq]
  conj_inner_symm x y := by
    -- Over `ℝ`, the componentwise formula is symmetric.
    simp [real_inner_comm, mul_comm]
  add_left x y z := by
    -- Bilinearity is inherited from the two component inner products.
    simp [inner_add_left, add_mul, add_assoc, add_left_comm, add_comm]
  smul_left x y r := by
    -- Scalar multiplication distributes through both component contributions.
    simp [inner_smul_left, mul_add, mul_left_comm, mul_comm]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 9.9: every point of the effective domain admits a real epigraph height
above it. -/
private theorem exists_mem_epigraph_of_mem_dom (f : H → EReal) {x : H} (hx : x ∈ dom f) :
    ∃ ξ : ℝ, (x, ξ) ∈ epigraph f := by
  -- Convert domain membership into strict finiteness and choose an intermediate real height.
  rw [mem_dom_iff] at hx
  rcases EReal.lt_iff_exists_real_btwn.mp hx with ⟨ξ, hfx_lt_ξ, _⟩
  refine ⟨ξ, ?_⟩
  -- That real height is, by definition, an epigraph point.
  rw [mem_epigraph_iff]
  exact le_of_lt hfx_lt_ξ

omit [CompleteSpace H] in
/-- Helper for Theorem 9.9: a point in the convex hull of `dom f` lifts to a point in the convex
hull of `epigraph f`. -/
private theorem exists_mem_convexHull_epigraph_of_mem_convexHull_dom
    (f : H → EReal) {y : H} (hy : y ∈ convexHull ℝ (dom f)) :
    ∃ η : ℝ, (y, η) ∈ convexHull ℝ (epigraph f) := by
  have hdom_image : dom f = (LinearMap.fst ℝ H ℝ) '' epigraph f := by
    ext x
    constructor
    · intro hx
      -- A finite value gives a real-height epigraph point projecting back to `x`.
      rcases exists_mem_epigraph_of_mem_dom f hx with ⟨ξ, hξ⟩
      exact ⟨(x, ξ), hξ, rfl⟩
    · intro hx
      rcases hx with ⟨p, hp, hp_proj⟩
      rcases p with ⟨z, η⟩
      -- Conversely, an epigraph point has finite first-coordinate value.
      rw [mem_dom_iff]
      have hz : (f z : EReal) ≤ (η : EReal) := by
        simpa [mem_epigraph_iff] using hp
      simpa using hp_proj ▸ lt_of_le_of_lt hz (EReal.coe_lt_top η)
  have hy' : y ∈ convexHull ℝ ((LinearMap.fst ℝ H ℝ) '' epigraph f) := by
    simpa [hdom_image] using hy
  rw [← LinearMap.image_convexHull (LinearMap.fst ℝ H ℝ) (epigraph f)] at hy'
  rcases hy' with ⟨p, hp, hp_proj⟩
  rcases p with ⟨z, η⟩
  refine ⟨η, ?_⟩
  -- Rewriting the projected first coordinate identifies the lifted convex-hull point.
  simpa using hp_proj ▸ hp

omit [CompleteSpace H] in
/-- Helper for Theorem 9.9: the product inner product splits into its base-space and height
components after translating by `(p, π)`. -/
private lemma inner_sub_prod_eq {x y p : H} {ξ η π : ℝ} :
    ⟪(y, η) - (p, π), (x, ξ) - (p, π)⟫_ℝ =
      ⟪y - p, x - p⟫_ℝ + (η - π) * (ξ - π) := rfl

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 9.9: a finite-above non-`⊥` value yields the canonical real-height
epigraph point at `toReal`. -/
private theorem mem_epigraph_toReal_of_mem_dom_of_ne_bot_local
    (f : H → EReal) {x : H} (hx : x ∈ dom f) (hbot : f x ≠ ⊥) :
    (x, (f x).toReal) ∈ epigraph f := by
  -- Excluding both infinities lets `toReal` recover the original `EReal` value.
  have htop : f x ≠ ⊤ := ne_of_lt ((mem_dom_iff f x).mp hx)
  simp [mem_epigraph_iff, EReal.coe_toReal htop hbot]

omit [CompleteSpace H] in
/-- Helper for Theorem 9.9: the closed convex hull of `epigraph f` is stable under nonnegative
vertical translation. -/
private theorem vertical_translate_mem_closure_convexHull_epigraph
    (f : H → EReal) {y : H} {η t : ℝ}
    (hyη : (y, η) ∈ closure (convexHull ℝ (epigraph f))) (ht : 0 ≤ t) :
    (y, η + t) ∈ closure (convexHull ℝ (epigraph f)) := by
  let v : H × ℝ := (0, t)
  have himage_mem :
      v + (y, η) ∈ closure ((fun p : H × ℝ ↦ v + p) '' convexHull ℝ (epigraph f)) := by
    -- Translate the closure point by continuity of addition.
    simpa [v, add_comm, add_left_comm, add_assoc] using
      mem_closure_image
        (f := fun p : H × ℝ ↦ v + p)
        ((continuous_const.add continuous_id).continuousAt) hyη
  have htranslate_epi :
      (fun p : H × ℝ ↦ v + p) '' epigraph f ⊆ epigraph f := by
    intro q hq
    rcases hq with ⟨p, hp, rfl⟩
    rcases p with ⟨x, ξ⟩
    -- Real-height epigraphs are upward closed in the second coordinate.
    rw [mem_epigraph_iff] at hp ⊢
    simpa [v, add_comm, add_left_comm, add_assoc] using
      le_trans hp
        (show (ξ : EReal) ≤ ((ξ + t : ℝ) : EReal) by
          exact_mod_cast (le_add_of_nonneg_right ht))
  have htranslate_hull :
      (fun p : H × ℝ ↦ v + p) '' convexHull ℝ (epigraph f) ⊆
        convexHull ℝ (epigraph f) := by
    -- Transport the convex hull through the affine translation map and then use monotonicity.
    rw [show
        (fun p : H × ℝ ↦ v + p) '' convexHull ℝ (epigraph f) =
          ((AffineEquiv.constVAdd ℝ (H × ℝ) v).toAffineMap) '' convexHull ℝ (epigraph f) by
            ext p
            simp [vadd_eq_add]]
    rw [AffineMap.image_convexHull ((AffineEquiv.constVAdd ℝ (H × ℝ) v).toAffineMap) (epigraph f)]
    exact convexHull_mono htranslate_epi
  -- The translated closure still lies in the original closed convex hull.
  exact
    (closure_mono htranslate_hull) <| by
      simpa [v, add_comm, add_left_comm, add_assoc] using himage_mem

omit [CompleteSpace H] in
/-- Helper for Theorem 9.9: a strict projection gap rules out the value `⊥` everywhere on `f`. -/
private theorem strict_gap_excludes_bot_values
    (f : H → EReal) {x p : H} {ξ π : ℝ}
    (hξπ : ξ < π)
    (hvari :
      ∀ {y : H} {η : ℝ}, (y, η) ∈ closure (convexHull ℝ (epigraph f)) →
        ⟪y - p, x - p⟫_ℝ + (η - π) * (ξ - π) ≤ 0) :
    ∀ y : H, f y ≠ ⊥ := by
  intro y hybot
  let A : ℝ := ⟪y - p, x - p⟫_ℝ
  let η : ℝ := π - (|A| + 1) / (π - ξ)
  have hgap_pos : 0 < π - ξ := sub_pos.mpr hξπ
  have hη_mem : (y, η) ∈ closure (convexHull ℝ (epigraph f)) := by
    have hη_epi : (y, η) ∈ epigraph f := by
      -- If `f y = ⊥`, then every real height lies in the epigraph above `y`.
      rw [mem_epigraph_iff]
      simpa [hybot]
    exact subset_closure (subset_convexHull ℝ (epigraph f) hη_epi)
  have hineq :
      A + (η - π) * (ξ - π) ≤ 0 := by
    simpa [A, η] using hvari hη_mem
  have hcalc : (η - π) * (ξ - π) = |A| + 1 := by
    -- The chosen ordinate makes the vertical contribution exactly `|A| + 1`.
    dsimp [η]
    have hgap_ne : π - ξ ≠ 0 := ne_of_gt hgap_pos
    field_simp [hgap_ne]
    ring
  have hA_nonneg : 0 ≤ A + |A| := by
    nlinarith [neg_abs_le A]
  have hA_pos : 0 < A + (|A| + 1) := by
    nlinarith
  rw [hcalc] at hineq
  linarith

omit [CompleteSpace H] in
/-- Helper for Theorem 9.9: the closed convex hull of `epigraph f` is contained in the epigraph
of the lower semicontinuous convex envelope. -/
private theorem closure_convexHull_epigraph_subset_epigraph_lowerSemicontinuousConvexEnvelope
    (f : H → EReal) :
    closure (convexHull ℝ (epigraph f)) ⊆ epigraph (lowerSemicontinuousConvexEnvelope f) := by
  -- The envelope epigraph is closed and convex, and it already contains every point of
  -- `epigraph f`.
  refine closure_minimal ?_ (isClosed_epigraph_lowerSemicontinuousConvexEnvelope f)
  refine convexHull_min ?_ (convex_epigraph_lowerSemicontinuousConvexEnvelope f)
  intro p hp
  rcases p with ⟨x, ξ⟩
  -- Pointwise minorization of `f` by its envelope gives the basic epigraph inclusion.
  rw [mem_epigraph_iff] at hp ⊢
  exact le_trans (lowerSemicontinuousConvexEnvelope_le f x) hp

-- Proof sketch: first show that `closure (convexHull ℝ (epigraph f))` lies in the epigraph of the
-- lower semicontinuous convex envelope because the latter epigraph is already closed and convex.
-- For the reverse inclusion, set up the projection of an assumed exterior point onto the closed
-- convex hull and reduce the remaining work to the source proof's vertical-translation and affine
-- minorant arguments.
/-- Theorem 9.9: the epigraph of the lower semicontinuous convex envelope of `f` is the closure of
the convex hull of the epigraph of `f`. -/
theorem epigraph_lowerSemicontinuousConvexEnvelope_eq_closure_convexHull_epigraph
    (f : H → EReal) :
    epigraph (lowerSemicontinuousConvexEnvelope f) =
      closure (convexHull ℝ (epigraph f)) := by
  apply le_antisymm
  · intro q hq
    rcases q with ⟨x, ξ⟩
    let C : Set (H × ℝ) := closure (convexHull ℝ (epigraph f))
    by_cases hqC : (x, ξ) ∈ C
    · -- If the point is already in the closed convex hull, there is nothing left to prove.
      simpa [C] using hqC
    have hx_dom : x ∈ dom (lowerSemicontinuousConvexEnvelope f) := by
      -- A real epigraph ordinate forces the envelope value at `x` to be finite.
      rw [mem_dom_iff]
      exact lt_of_le_of_lt (mem_epigraph_iff _ _ _ |>.mp hq) (EReal.coe_lt_top ξ)
    have hx_closure_dom : x ∈ closure (convexHull ℝ (dom f)) :=
      dom_lowerSemicontinuousConvexEnvelope_subset_closure_convexHull_dom f hx_dom
    have hconvexHull_dom_nonempty : (convexHull ℝ (dom f)).Nonempty := by
      by_contra h_empty
      have hx_false : False := by
        simpa [Set.not_nonempty_iff_eq_empty.mp h_empty] using hx_closure_dom
      exact hx_false.elim
    rcases hconvexHull_dom_nonempty with ⟨y, hy⟩
    rcases exists_mem_convexHull_epigraph_of_mem_convexHull_dom (f := f) (y := y) hy with
        ⟨η, hyη⟩
    have hC_nonempty : C.Nonempty := by
      refine ⟨(y, η), ?_⟩
      simpa [C] using subset_closure hyη
    have hC_closed : IsClosed C := by
      simp [C]
    have hC_convex : Convex ℝ C := by
      -- Closure preserves convexity, so the projection theorem applies to `C`.
      simpa [C] using convex_closure_of_convex (convex_convexHull ℝ (epigraph f))
    let proj :
        H × ℝ :=
      projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) (x, ξ)
    have hproj_char :
        proj ∈ C ∧ ∀ z ∈ C, ⟪z - proj, (x, ξ) - proj⟫_ℝ ≤ 0 := by
      -- Theorem 3.16 gives the variational inequality for the metric projection onto `C`.
      exact
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex).mp rfl
    have hvari :
        ∀ {y : H} {η : ℝ}, (y, η) ∈ C →
          ⟪y - proj.1, x - proj.1⟫_ℝ + (η - proj.2) * (ξ - proj.2) ≤ 0 := by
      intro y η hyη
      -- Rewriting the product inner product isolates the base-space and height contributions.
      simpa [proj, inner_sub_prod_eq] using hproj_char.2 (y, η) hyη
    have hξ_le_proj : ξ ≤ proj.2 := by
      -- Vertical translation of the projection point gives a one-step test forcing `ξ ≤ π`.
      have hproj_up : (proj.1, proj.2 + 1) ∈ C := by
        exact
          vertical_translate_mem_closure_convexHull_epigraph
            (f := f) hproj_char.1 (by norm_num)
      have hineq : (proj.2 + 1 - proj.2) * (ξ - proj.2) ≤ 0 := by
        simpa using hvari hproj_up
      linarith
    by_cases hξ_eq_proj : ξ = proj.2
    · -- Route correction: in the equal-height case, close the branch through the closed half-space
      -- containing `convexHull ℝ (dom f)` rather than searching for a stronger lift lemma.
      have hconvHull_dom_nonpos :
          convexHull ℝ (dom f) ⊆ {y : H | ⟪y - proj.1, x - proj.1⟫_ℝ ≤ 0} := by
        intro y hy
        -- Lift each convex-hull domain point to a convex-hull epigraph point and apply `hvari`.
        rcases exists_mem_convexHull_epigraph_of_mem_convexHull_dom (f := f) (y := y) hy with
            ⟨η, hη⟩
        have hηC : (y, η) ∈ C := by
          simpa [C] using subset_closure hη
        have hineq :=
          hvari hηC
        rw [hξ_eq_proj, sub_self, mul_zero, add_zero] at hineq
        exact hineq
      have hclosed_nonpos :
          IsClosed {y : H | ⟪y - proj.1, x - proj.1⟫_ℝ ≤ 0} := by
        -- The half-space is closed because the underlying inner-product functional is continuous.
        exact
          isClosed_le
            ((continuous_id.sub continuous_const).inner continuous_const)
            continuous_const
      have hx_nonpos : ⟪x - proj.1, x - proj.1⟫_ℝ ≤ 0 := by
        -- Closedness extends the half-space membership from `convexHull dom f` to its closure.
        exact
          (closure_minimal hconvHull_dom_nonpos hclosed_nonpos) hx_closure_dom
      have hinner_nonneg : 0 ≤ ⟪x - proj.1, x - proj.1⟫_ℝ := by
        simpa using (real_inner_self_nonneg : 0 ≤ ⟪x - proj.1, x - proj.1⟫_ℝ)
      have hinner_eq_zero : ⟪x - proj.1, x - proj.1⟫_ℝ = 0 := by
        nlinarith
      have hx_proj : x = proj.1 := by
        -- Vanishing self-inner-product collapses the base-space residual.
        have hsub : x - proj.1 = 0 := by
          simpa using inner_self_eq_zero.mp hinner_eq_zero
        exact sub_eq_zero.mp hsub
      have hq_mem : (x, ξ) ∈ C := by
        -- The projection point itself lies in `C`, so equality of both coordinates is impossible.
        simpa [hx_proj, hξ_eq_proj] using hproj_char.1
      exact False.elim (hqC hq_mem)
    · have hξ_lt_proj : ξ < proj.2 := lt_of_le_of_ne hξ_le_proj hξ_eq_proj
      have hno_bot :
          ∀ y : H, f y ≠ ⊥ :=
        strict_gap_excludes_bot_values
          (f := f) (x := x) (p := proj.1) (ξ := ξ) (π := proj.2) hξ_lt_proj hvari
      let u : H := (proj.2 - ξ)⁻¹ • (x - proj.1)
      let g : H → EReal := fun y ↦ ((⟪y - proj.1, u⟫_ℝ + proj.2 : ℝ) : EReal)
      have hg_le_f : g ≤ f := by
        intro y
        by_cases hy : y ∈ dom f
        · have hfy_top : f y ≠ ⊤ := ne_of_lt ((mem_dom_iff f y).mp hy)
          have hfy_bot : f y ≠ ⊥ := hno_bot y
          have hyC : (y, (f y).toReal) ∈ C := by
            -- The finite `toReal` height belongs to the original epigraph, hence to `C`.
            have hy_epi :
                (y, (f y).toReal) ∈ epigraph f :=
              mem_epigraph_toReal_of_mem_dom_of_ne_bot_local
                (f := f) hy hfy_bot
            simpa [C] using subset_closure (subset_convexHull ℝ (epigraph f) hy_epi)
          have hineq :
              ⟪y - proj.1, x - proj.1⟫_ℝ +
                  ((f y).toReal - proj.2) * (ξ - proj.2) ≤ 0 := by
            simpa using hvari hyC
          have hgap_pos : 0 < proj.2 - ξ := sub_pos.mpr hξ_lt_proj
          have hinner_le :
              ⟪y - proj.1, x - proj.1⟫_ℝ ≤
                ((f y).toReal - proj.2) * (proj.2 - ξ) := by
            -- Rewrite the variational inequality with the positive gap `π - ξ`.
            nlinarith
          have hscaled :
              ⟪y - proj.1, u⟫_ℝ ≤ (f y).toReal - proj.2 := by
            -- Divide by the positive gap to isolate the affine slope.
            have hdiv :
                ⟪y - proj.1, x - proj.1⟫_ℝ / (proj.2 - ξ) ≤
                  (f y).toReal - proj.2 := by
              refine (div_le_iff₀ hgap_pos).2 ?_
              simpa [mul_comm, mul_left_comm, mul_assoc] using hinner_le
            simpa [u, div_eq_mul_inv, real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using
              hdiv
          have hreal :
              ⟪y - proj.1, u⟫_ℝ + proj.2 ≤ (f y).toReal := by
            linarith
          have hcast :
              ((⟪y - proj.1, u⟫_ℝ + proj.2 : ℝ) : EReal) ≤
                (((f y).toReal : ℝ) : EReal) := by
            exact_mod_cast hreal
          simpa [g, EReal.coe_toReal hfy_top hfy_bot] using hcast
        · have hy_not_lt_top : ¬ f y < ⊤ := by
            simpa [mem_dom_iff] using hy
          have hfy_top : f y = ⊤ := by
            exact le_antisymm le_top (le_of_not_gt hy_not_lt_top)
          simpa [g, hfy_top] using
            (le_top : g y ≤ (⊤ : EReal))
      have hg_lsc : LowerSemicontinuous g := by
        have hg_cont : Continuous g := by
          -- The affine real formula is continuous, and coercion `ℝ → EReal` preserves continuity.
          simpa [g] using
            (continuous_coe_real_ereal.comp
              (((continuous_id.sub continuous_const).inner continuous_const).add continuous_const))
        exact hg_cont.lowerSemicontinuous
      have hg_conv : Convex ℝ (epigraph g) := by
        let A : H × ℝ →ᵃ[ℝ] ℝ :=
          AffineMap.mk'
            (fun q : H × ℝ ↦ q.2 - (⟪q.1 - proj.1, u⟫_ℝ + proj.2))
            ((LinearMap.snd ℝ H ℝ) -
              ((InnerProductSpace.toDual ℝ H u) : H →ₗ[ℝ] ℝ).comp
                (LinearMap.fst ℝ H ℝ))
            (proj.1, proj.2)
            (fun q ↦ by
              rcases q with ⟨y, η⟩
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                InnerProductSpace.toDual_apply_apply, real_inner_comm])
        have hpre : epigraph g = A ⁻¹' Set.Ici (0 : ℝ) := by
          ext q
          rcases q with ⟨y, η⟩
          constructor
          · intro hq
            rw [Set.mem_preimage, Set.mem_Ici]
            have hq' :
                ((⟪y - proj.1, u⟫_ℝ + proj.2 : ℝ) : EReal) ≤ (η : EReal) := by
              simpa [g] using hq
            have hreal : ⟪y - proj.1, u⟫_ℝ + proj.2 ≤ η := by
              exact_mod_cast hq'
            simpa [A, g] using sub_nonneg.mpr hreal
          · intro hq
            rw [Set.mem_preimage, Set.mem_Ici] at hq
            have hreal : ⟪y - proj.1, u⟫_ℝ + proj.2 ≤ η := by
              simpa [A, g] using sub_nonneg.mp hq
            have hcast :
                ((⟪y - proj.1, u⟫_ℝ + proj.2 : ℝ) : EReal) ≤ (η : EReal) := by
              exact_mod_cast hreal
            simpa [g] using hcast
        rw [hpre]
        exact (convex_Ici (0 : ℝ)).affine_preimage A
      have hg_le_env :
          g ≤ lowerSemicontinuousConvexEnvelope f :=
        le_lowerSemicontinuousConvexEnvelope_of_lowerSemicontinuous_of_convex_epigraph
          hg_lsc hg_conv hg_le_f
      have hq_env :
          lowerSemicontinuousConvexEnvelope f x ≤ ξ :=
        (mem_epigraph_iff _ _ _).mp hq
      have hπ_le_gx :
          (proj.2 : EReal) ≤ g x := by
        have hgap_nonneg : 0 ≤ (proj.2 - ξ)⁻¹ := by
          exact inv_nonneg.mpr (sub_nonneg.mpr hξ_le_proj)
        have hinner_nonneg :
            0 ≤ ⟪x - proj.1, u⟫_ℝ := by
          -- At `x`, the affine support value is at least the intercept `π`.
          simpa [u, real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using
            mul_nonneg hgap_nonneg
              (show 0 ≤ ⟪x - proj.1, x - proj.1⟫_ℝ by
                simpa using
                  (real_inner_self_nonneg : 0 ≤ ⟪x - proj.1, x - proj.1⟫_ℝ))
        have hreal : proj.2 ≤ ⟪x - proj.1, u⟫_ℝ + proj.2 := by
          linarith
        have hcast :
            ((proj.2 : ℝ) : EReal) ≤
              ((⟪x - proj.1, u⟫_ℝ + proj.2 : ℝ) : EReal) := by
          exact_mod_cast hreal
        simpa [g] using hcast
      have hπ_le_ξ : (proj.2 : EReal) ≤ (ξ : EReal) := by
        exact le_trans hπ_le_gx (le_trans (hg_le_env x) hq_env)
      have hπ_le_ξ_real : proj.2 ≤ ξ := by
        exact_mod_cast hπ_le_ξ
      exact False.elim ((not_le_of_gt hξ_lt_proj) hπ_le_ξ_real)
  · -- The easy inclusion is the closed-convex minimality argument.
    exact closure_convexHull_epigraph_subset_epigraph_lowerSemicontinuousConvexEnvelope f

end

end ERealFunction
