/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_32
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Corollary_6_53
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_25
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_29

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise InnerProductSpace

universe u

namespace ERealFunction

variable {H : Type u}

section RealVectorSpace

variable [AddCommGroup H] [Module ℝ H]

/-- The closed perspective of `φ` as an extended-real-valued function: it agrees with the
perspective away from the zero-height slice and takes the recession-function value at height
`0`. This construction only needs the effective domain of `φ` to be nonempty. -/
noncomputable def closedPerspectiveEReal
    (φ : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain φ).Nonempty) :
    ℝ × H → EReal :=
  fun p ↦
    if p.1 = 0 then
      (recessionFunction φ hdom p.2 : EReal)
    else
      perspective (fun x : H ↦ (φ x : EReal)) p

-- Proof sketch: unfold `closedPerspectiveEReal` and evaluate the zero-height branch of the
-- defining `if`.
/-- On the zero-height slice, the closed perspective equals the recession function. -/
@[simp] theorem closedPerspectiveEReal_apply_zero
    (φ : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain φ).Nonempty) (x : H) :
    closedPerspectiveEReal φ hdom (0, x) = (recessionFunction φ hdom x : EReal) := by
  -- Unfold the definition and select the zero-height branch of the conditional.
  simp [closedPerspectiveEReal]

-- Proof sketch: unfold `closedPerspectiveEReal` and evaluate the nonzero branch of the defining
-- `if`.
/-- Away from the zero-height slice, the closed perspective agrees with the ordinary perspective. -/
theorem closedPerspectiveEReal_apply_of_ne_zero
    (φ : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain φ).Nonempty)
    {ξ : ℝ} {x : H} (hξ : ξ ≠ 0) :
    closedPerspectiveEReal φ hdom (ξ, x) =
      perspective (fun y : H ↦ (φ y : EReal)) (ξ, x) := by
  -- The nonzero branch of `closedPerspectiveEReal` is exactly the original perspective.
  simp [closedPerspectiveEReal, hξ]

-- Proof sketch: split according to whether the first coordinate is `0`. On the zero slice, the
-- recession function is `]-∞,+∞]`-valued by construction; away from zero, the perspective is
-- either a positive scalar multiple of a `]-∞,+∞]`-valued value or `+∞`.
/-- The closed perspective never takes the value `-∞`. -/
theorem closedPerspectiveEReal_ne_bot
    (φ : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain φ).Nonempty)
    (p : ℝ × H) :
    ⊥ < closedPerspectiveEReal φ hdom p := by
  rcases p with ⟨ξ, x⟩
  by_cases hξ : ξ = 0
  · -- On the zero slice, the subtype-valued recession function is already `]-∞,+∞]`-valued.
    simpa [closedPerspectiveEReal, hξ] using (recessionFunction φ hdom x).2
  · rw [closedPerspectiveEReal_apply_of_ne_zero (φ := φ) (hdom := hdom) hξ]
    by_cases hpos : 0 < ξ
    · -- Positive-height values are positive scalar multiples of a `]-∞,+∞]`-valued value.
      rw [perspective_apply_of_pos _ hpos]
      apply bot_lt_iff_ne_bot.mpr
      rw [EReal.mul_ne_bot]
      constructor
      · exact Or.inl (EReal.coe_ne_bot ξ)
      constructor
      · exact Or.inr (ne_of_gt (show (⊥ : EReal) < (φ (ξ⁻¹ • x) : EReal) from
          (φ (ξ⁻¹ • x)).2))
      constructor
      · exact Or.inl (EReal.coe_ne_top ξ)
      · exact Or.inl (by exact_mod_cast hpos.le)
    · -- Nonpositive nonzero heights fall on the `+∞` branch of the perspective.
      rw [perspective_apply_of_nonpos _ (le_of_not_gt hpos)]
      simp

/-- The subtype-valued closed perspective associated with `closedPerspectiveEReal`. -/
noncomputable def closedPerspective
    (φ : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain φ).Nonempty) :
    ℝ × H → Set.Ioi (⊥ : EReal) :=
  fun p ↦ ⟨closedPerspectiveEReal φ hdom p, closedPerspectiveEReal_ne_bot φ hdom p⟩

-- Proof sketch: unfold `closedPerspective`; coercing the subtype forgets only the proof that the
-- value is strictly above `-∞`.
/-- Coercing the closed perspective to `EReal` recovers the explicit closed-perspective formula. -/
@[simp] theorem closedPerspective_coe
    (φ : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain φ).Nonempty)
    (p : ℝ × H) :
    (closedPerspective φ hdom p : EReal) = closedPerspectiveEReal φ hdom p := by
  -- Coercing the subtype simply forgets the stored proof of `⊥ < ...`.
  rfl

end RealVectorSpace

noncomputable section Hilbert

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

open WithLp

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

/-- Helper for Proposition 9.42: view `ℝ × H` with the `ℓ²` product metric so the perspective
slice lives in the intended Hilbert product space. -/
local instance scalar_prod_pseudoMetricSpace_l2 : PseudoMetricSpace (ℝ × H) :=
  WithLp.pseudoMetricSpaceToProd (p := 2) ℝ H

/-- Helper for Proposition 9.42: equip `ℝ × H` with the `ℓ²` product norm. -/
local instance scalar_prod_normedAddCommGroup_l2 : NormedAddCommGroup (ℝ × H) :=
  WithLp.normedAddCommGroupToProd (p := 2) ℝ H

/-- Helper for Proposition 9.42: the `ℓ²` product norm on `ℝ × H` is compatible with scalar
multiplication. -/
local instance scalar_prod_normedSpace_l2 : NormedSpace ℝ (ℝ × H) := by
  letI : NormedAddCommGroup (ℝ × H) := WithLp.normedAddCommGroupToProd (p := 2) ℝ H
  exact WithLp.normedSpaceSeminormedAddCommGroupToProd (p := 2) (α := ℝ) (β := H)

/-- Helper for Proposition 9.42: completeness of `ℝ × H` for the `ℓ²` product metric follows from
the uniform equivalence with `WithLp 2 (ℝ × H)`. -/
local instance scalar_prod_completeSpace_l2 : CompleteSpace (ℝ × H) := by
  letI : PseudoMetricSpace (ℝ × H) := WithLp.pseudoMetricSpaceToProd (p := 2) ℝ H
  exact (WithLp.uniformEquivProd (p := 2) ℝ H).completeSpace_iff.1 inferInstance

/-- Helper for Proposition 9.42: the product Hilbert structure on `ℝ × H` is the textbook one
`⟪(a, u), (b, v)⟫ = ab + ⟪u, v⟫`. -/
local instance scalar_prod_innerProductSpace_l2 : InnerProductSpace ℝ (ℝ × H) where
  inner x y := x.1 * y.1 + ⟪x.2, y.2⟫_ℝ
  norm_sq_eq_re_inner x := by
    rw [show ‖x‖ = ‖WithLp.toLp 2 x‖ by rfl, WithLp.prod_norm_sq_eq_of_L2]
    simp [sq]
  conj_inner_symm x y := by
    simp [real_inner_comm, mul_comm]
  add_left x y z := by
    simp [inner_add_left, add_mul, add_assoc, add_left_comm, add_comm]
  smul_left x y r := by
    simp [inner_smul_left, mul_add, mul_left_comm, mul_comm]

/-- Helper for Proposition 9.42: view `((ℝ × H) × ℝ)` with the `ℓ²` product metric so Corollary
6.53 applies in the ambient Hilbert space of the perspective epigraph. -/
local instance perspective_prod_pseudoMetricSpace_l2 : PseudoMetricSpace ((ℝ × H) × ℝ) :=
  WithLp.pseudoMetricSpaceToProd (p := 2) (ℝ × H) ℝ

/-- Helper for Proposition 9.42: equip `((ℝ × H) × ℝ)` with the `ℓ²` product norm. -/
local instance perspective_prod_normedAddCommGroup_l2 : NormedAddCommGroup ((ℝ × H) × ℝ) :=
  WithLp.normedAddCommGroupToProd (p := 2) (ℝ × H) ℝ

/-- Helper for Proposition 9.42: the `ℓ²` product norm on `((ℝ × H) × ℝ)` is compatible with
scalar multiplication. -/
local instance perspective_prod_normedSpace_l2 : NormedSpace ℝ ((ℝ × H) × ℝ) := by
  letI : NormedAddCommGroup ((ℝ × H) × ℝ) :=
    WithLp.normedAddCommGroupToProd (p := 2) (ℝ × H) ℝ
  exact WithLp.normedSpaceSeminormedAddCommGroupToProd (p := 2) (α := ℝ × H) (β := ℝ)

/-- Helper for Proposition 9.42: completeness of `((ℝ × H) × ℝ)` for the `ℓ²` product metric
again comes from its uniform equivalence with the corresponding `WithLp` product. -/
local instance perspective_prod_completeSpace_l2 : CompleteSpace ((ℝ × H) × ℝ) := by
  letI : PseudoMetricSpace ((ℝ × H) × ℝ) := WithLp.pseudoMetricSpaceToProd (p := 2) (ℝ × H) ℝ
  exact (WithLp.uniformEquivProd (p := 2) (ℝ × H) ℝ).completeSpace_iff.1 inferInstance

/-- Helper for Proposition 9.42: the ambient Hilbert structure on `((ℝ × H) × ℝ)` is the
componentwise one from the textbook product space. -/
local instance perspective_prod_innerProductSpace_l2 : InnerProductSpace ℝ ((ℝ × H) × ℝ) where
  inner x y := ⟪x.1, y.1⟫_ℝ + x.2 * y.2
  norm_sq_eq_re_inner x := by
    rw [show ‖x‖ = ‖WithLp.toLp 2 x‖ by rfl, WithLp.prod_norm_sq_eq_of_L2]
    simp [sq]
  conj_inner_symm x y := by
    simp [real_inner_comm, mul_comm]
  add_left x y z := by
    simp [inner_add_left, add_mul, add_assoc, add_left_comm, add_comm]
  smul_left x y r := by
    simp [inner_smul_left, mul_add, mul_left_comm, mul_comm]

/-- Helper for Proposition 9.42: convexity on the effective domain of a
`]-∞,+∞]`-valued function yields convexity of its real-height epigraph after coercion to `EReal`.
-/
lemma convex_epigraph_coe_of_convexOn_local
    {φ : H → Set.Ioi (⊥ : EReal)} (hconv : ConvexOn φ (effectiveDomain φ)) :
    Convex ℝ (epigraph (fun x : H ↦ (φ x : EReal))) := by
  -- Repackage the stored Jensen inequality in the `dom` form expected by the epigraph criterion.
  refine (convex_epigraph_iff_jensen_on_dom (fun y : H ↦ (φ y : EReal))).2 ?_
  intro x y hx hy α hα hα_lt_one
  have hx' : x ∈ effectiveDomain φ := by
    simpa [effectiveDomain, dom] using hx
  have hy' : y ∈ effectiveDomain φ := by
    simpa [effectiveDomain, dom] using hy
  simpa using hconv.ineq hx' hy' hα hα_lt_one

/-- Helper for Proposition 9.42: every effective-domain point gives a canonical finite-height point
of the real-height epigraph. -/
lemma mem_epigraph_toReal_of_mem_effectiveDomain
    {φ : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ effectiveDomain φ) :
    (x, (φ x : EReal).toReal) ∈ epigraph (fun y : H ↦ (φ y : EReal)) := by
  -- The finite value `(φ x).toReal` is the textbook real ordinate attached to `x`.
  rw [mem_epigraph_iff]
  exact EReal.le_coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hx))

/-- Helper for Proposition 9.42: the unit slice over a convex epigraph is convex. -/
lemma convex_perspectiveEpigraphSlice_of_convex_epigraph
    {F : H → EReal} (hF_conv : Convex ℝ (epigraph F)) :
    Convex ℝ (perspectiveEpigraphSlice F) := by
  -- The first coordinate stays fixed at `1`, while the remaining coordinates move inside the
  -- convex epigraph of `F`.
  refine (convex_iff_forall_pos).2 ?_
  intro p hp q hq a b ha hb hab
  rcases p with ⟨⟨ξ₁, x₁⟩, η₁⟩
  rcases q with ⟨⟨ξ₂, x₂⟩, η₂⟩
  rw [mem_perspectiveEpigraphSlice_iff] at hp hq ⊢
  rcases hp with ⟨hξ₁, hp⟩
  rcases hq with ⟨hξ₂, hq⟩
  constructor
  · -- The slice constraint survives convex combination because both endpoints have first
    -- coordinate `1`.
    simp [Prod.smul_mk, smul_eq_mul, hξ₁, hξ₂, hab]
  · -- Convexity of `epigraph F` controls the remaining `(x, η)` coordinates.
    have hcombo : a • (x₁, η₁) + b • (x₂, η₂) ∈ epigraph F :=
      (convex_iff_forall_pos.mp hF_conv) hp hq ha hb hab
    simpa [Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hcombo

/-- Helper for Proposition 9.42: if the real-height epigraph of `F` is closed, then the fixed
unit slice used for the perspective-cone description is also closed. -/
lemma isClosed_perspectiveEpigraphSlice_of_isClosed_epigraph
    {F : H → EReal} (hF_closed : IsClosed (epigraph F)) :
    IsClosed (perspectiveEpigraphSlice F) := by
  let e : ((ℝ × H) × ℝ) → ℝ × (H × ℝ) := fun p ↦ (p.1.1, (p.1.2, p.2))
  have he_cont : Continuous e := by
    -- The slice map is built from coordinate projections, hence continuous.
    dsimp [e]
    exact continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)
  have hprod : IsClosed (({1} : Set ℝ) ×ˢ epigraph F) :=
    isClosed_singleton.prod hF_closed
  have hpre : IsClosed (e ⁻¹' (({1} : Set ℝ) ×ˢ epigraph F)) :=
    hprod.preimage he_cont
  have heq : perspectiveEpigraphSlice F = e ⁻¹' (({1} : Set ℝ) ×ˢ epigraph F) := by
    ext p
    rcases p with ⟨⟨ξ, x⟩, η⟩
    change (ξ = 1 ∧ (x, η) ∈ epigraph F) ↔ (ξ ∈ ({1} : Set ℝ) ∧ (x, η) ∈ epigraph F)
    simp
  -- Reinterpret the slice as the pullback of a closed product set.
  rw [heq]
  exact hpre

/-- Helper for Proposition 9.42: the recession cone of the unit perspective slice consists
precisely of the zero-height directions whose remaining coordinates lie in the recession cone of
the original real-height epigraph. -/
lemma recessionCone_perspectiveEpigraphSlice_eq_zero_slice
    (F : H → EReal) (hF_nonempty : (epigraph F).Nonempty) :
    Set.recessionCone (perspectiveEpigraphSlice F) =
      {p : ((ℝ × H) × ℝ) | p.1.1 = 0 ∧ (p.1.2, p.2) ∈ Set.recessionCone (epigraph F)} := by
  ext p
  rcases p with ⟨⟨ξ, x⟩, η⟩
  rw [Set.mem_recessionCone_iff]
  constructor
  · intro hp
    rcases hF_nonempty with ⟨q, hq⟩
    have hmem : ((ξ, x), η) + ((1, q.1), q.2) ∈ perspectiveEpigraphSlice F := by
      have hq' : ((1, q.1), q.2) ∈ perspectiveEpigraphSlice F := by
        rw [mem_perspectiveEpigraphSlice_iff]
        exact ⟨rfl, hq⟩
      -- Translate a concrete point of the slice to force the first coordinate of a recession
      -- direction to vanish.
      exact hp <| Set.mem_add.2 ⟨((ξ, x), η), by simp, ((1, q.1), q.2), hq', rfl⟩
    rw [mem_perspectiveEpigraphSlice_iff] at hmem
    constructor
    · simpa using hmem.1
    · rw [Set.mem_recessionCone_iff]
      intro s hs
      rcases Set.mem_add.1 hs with ⟨u, hu, v, hv, rfl⟩
      have hu' : u = (x, η) := by
        simpa using hu
      subst u
      have hv' : ((1, v.1), v.2) ∈ perspectiveEpigraphSlice F := by
        rw [mem_perspectiveEpigraphSlice_iff]
        exact ⟨rfl, hv⟩
      have hsum : ((ξ, x), η) + ((1, v.1), v.2) ∈ perspectiveEpigraphSlice F := by
        -- Translating a general slice point pushes the `(x, η)` coordinates along the recession
        -- direction in `epigraph F`.
        exact hp <| Set.mem_add.2 ⟨((ξ, x), η), by simp, ((1, v.1), v.2), hv', rfl⟩
      rw [mem_perspectiveEpigraphSlice_iff] at hsum
      -- The translated slice point records exactly the translated epigraph point.
      have hsum' : (x + v.1, η + v.2) ∈ epigraph F := by
        simpa using hsum.2
      have hsum'' : F (x + v.1) ≤ (((η + v.2 : ℝ)) : EReal) := by
        simpa [mem_epigraph_iff] using hsum'
      rw [mem_epigraph_iff]
      simpa [add_comm, add_left_comm, add_assoc] using hsum''
  · rintro ⟨hξ, hp⟩
    intro s hs
    rcases Set.mem_add.1 hs with ⟨u, hu, v, hv, rfl⟩
    have hu' : u = ((ξ, x), η) := by
      simpa using hu
    subst u
    rw [mem_perspectiveEpigraphSlice_iff] at hv ⊢
    rcases hv with ⟨hvξ, hv⟩
    constructor
    · -- The zero-height assumption keeps the translated point on the unit slice.
      change ((ξ, x), η).1.1 + v.1.1 = 1
      simpa [hξ, hvξ]
    · have : (((ξ, x), η).1.2, ((ξ, x), η).2) + (v.1.2, v.2) ∈ epigraph F := by
        exact hp <| Set.mem_add.2 ⟨(((ξ, x), η).1.2, ((ξ, x), η).2), by simp, (v.1.2, v.2), hv, rfl⟩
      -- The remaining coordinates move by a recession direction of `epigraph F`.
      simpa [add_comm, add_left_comm, add_assoc] using this

/-- Helper for Proposition 9.42: the epigraph of the closed perspective is the union of the
ordinary perspective epigraph with the zero-height recession slice. -/
lemma epigraph_closedPerspectiveEReal_eq_perspective_union_zero_slice
    (φ : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain φ).Nonempty) :
    epigraph (closedPerspectiveEReal φ hdom) =
      epigraph (perspective (fun x : H ↦ (φ x : EReal))) ∪
        {p : ((ℝ × H) × ℝ) | p.1.1 = 0 ∧
          (p.1.2, p.2) ∈ epigraph (fun y : H ↦ (recessionFunction φ hdom y : EReal))} := by
  ext p
  rcases p with ⟨⟨ξ, x⟩, η⟩
  by_cases hξ : ξ = 0
  · constructor
    · intro hp
      right
      constructor
      · exact hξ
      · -- On the zero slice, the defining branch is exactly the recession function.
        simpa [mem_epigraph_iff, hξ, closedPerspectiveEReal_apply_zero] using hp
    · rintro (hp | hp)
      · have hpersp : perspective (fun y : H ↦ (φ y : EReal)) (ξ, x) ≤ (η : EReal) := by
          simpa [mem_epigraph_iff] using hp
        -- The ordinary perspective has no real-height epigraph points when `ξ = 0`.
        rw [perspective_apply_of_nonpos _ (by simpa [hξ] using (show ξ ≤ 0 by exact le_of_eq hξ))]
          at hpersp
        simp at hpersp
      · simpa [mem_epigraph_iff, hξ, closedPerspectiveEReal_apply_zero] using hp.2
  · constructor
    · intro hp
      left
      -- Away from zero, the closed perspective is just the ordinary perspective.
      simpa [mem_epigraph_iff,
        closedPerspectiveEReal_apply_of_ne_zero (φ := φ) (hdom := hdom) hξ] using hp
    · rintro (hp | hp)
      · simpa [mem_epigraph_iff,
          closedPerspectiveEReal_apply_of_ne_zero (φ := φ) (hdom := hdom) hξ] using hp
      · exact (hξ hp.1).elim

/-- Helper for Proposition 9.42: equality of real-height epigraphs determines an
`EReal`-valued function once one side is known never to take the value `-∞`. -/
lemma eq_of_epigraph_eq_of_forall_gt_bot {X : Type u} {f g : X → EReal}
    (hepigraph : epigraph f = epigraph g)
    (hf : ∀ x, ⊥ < f x) :
    f = g := by
  have hg : ∀ x, ⊥ < g x := by
    intro x
    by_contra hgbot
    have hgbot' : g x = ⊥ := by
      simpa [bot_lt_iff_ne_bot] using hgbot
    rcases (EReal.lt_iff_exists_real_btwn).1 (hf x) with ⟨r, _, hrf⟩
    have hxg : ((x, r) : X × ℝ) ∈ epigraph g := by
      rw [mem_epigraph_iff, hgbot']
      simp
    have hxf : ((x, r) : X × ℝ) ∈ epigraph f := by
      rw [hepigraph]
      exact hxg
    have : f x ≤ (r : EReal) := by
      simpa [mem_epigraph_iff] using hxf
    -- If `g x = ⊥`, then every real height belongs to `epi g`, hence also to `epi f`, which
    -- contradicts the strict lower bound `⊥ < f x`.
    exact not_le_of_gt hrf this
  funext x
  apply le_antisymm
  · by_cases hgtop : g x = ⊤
    · simp [hgtop]
    · have hxg : ((x, ((g x).toReal : ℝ)) : X × ℝ) ∈ epigraph g := by
        rw [mem_epigraph_iff]
        exact EReal.le_coe_toReal hgtop
      have hxf : ((x, ((g x).toReal : ℝ)) : X × ℝ) ∈ epigraph f := by
        rw [hepigraph]
        exact hxg
      have hle : f x ≤ (((g x).toReal : ℝ) : EReal) := by
        simpa [mem_epigraph_iff] using hxf
      have hgbot : g x ≠ ⊥ := ne_of_gt (hg x)
      -- Reading both epigraphs at the finite height `(g x).toReal` gives `f x ≤ g x`.
      simpa [EReal.coe_toReal hgtop hgbot] using hle
  · by_cases hftop : f x = ⊤
    · simp [hftop]
    · have hxf : ((x, ((f x).toReal : ℝ)) : X × ℝ) ∈ epigraph f := by
        rw [mem_epigraph_iff]
        exact EReal.le_coe_toReal hftop
      have hxg : ((x, ((f x).toReal : ℝ)) : X × ℝ) ∈ epigraph g := by
        rw [← hepigraph]
        exact hxf
      have hle : g x ≤ (((f x).toReal : ℝ) : EReal) := by
        simpa [mem_epigraph_iff] using hxg
      have hfbot : f x ≠ ⊥ := ne_of_gt (hf x)
      -- The symmetric finite-height evaluation gives `g x ≤ f x`.
      simpa [EReal.coe_toReal hftop hfbot] using hle

-- Proof sketch: identify the epigraph of the perspective with a cone by Proposition 8.25, take
-- the closure of that cone using the lower-semicontinuous-hull epigraph formula, and then use the
-- recession-cone description of the recession function together with the cone-closure formula from
-- Chapter 6 to recognize exactly the zero-height recession slice added in `closedPerspectiveEReal`.
/-- Proposition 9.42: for `φ ∈ Γ₀(H)`, the lower semicontinuous envelope of the perspective of
`φ` is the closed perspective obtained by inserting the recession function on the zero-height
slice. -/
theorem lowerSemicontinuousEnvelope_perspective_eq_closedPerspectiveEReal
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H)) :
    lowerSemicontinuousEnvelope (perspective (fun x : H ↦ (φ x : EReal))) =
      closedPerspectiveEReal φ hφ.2.nonempty := by
  let F : H → EReal := fun x : H ↦ (φ x : EReal)
  let C : Set ((ℝ × H) × ℝ) := perspectiveEpigraphSlice F
  have hF_conv : Convex ℝ (epigraph F) :=
    convex_epigraph_coe_of_convexOn_local hφ.2
  have hF_closed : IsClosed (epigraph F) := by
    -- Lower semicontinuity of `φ` is exactly closedness of the real-height epigraph of `F`.
    exact (lowerSemicontinuous_iff_isClosed_epigraph F).1 hφ.1
  have hF_nonempty : (epigraph F).Nonempty := by
    rcases hφ.2.nonempty with ⟨x, hx⟩
    exact ⟨(x, (φ x : EReal).toReal), mem_epigraph_toReal_of_mem_effectiveDomain hx⟩
  have hC_nonempty : C.Nonempty := by
    rcases hF_nonempty with ⟨p, hp⟩
    exact ⟨((1, p.1), p.2), by
      rw [mem_perspectiveEpigraphSlice_iff]
      exact ⟨rfl, hp⟩⟩
  have hC_closed : IsClosed C := by
    -- The unit slice is a closed pullback of the closed epigraph of `F`.
    simpa [C] using isClosed_perspectiveEpigraphSlice_of_isClosed_epigraph hF_closed
  have hC_conv : Convex ℝ C := by
    -- The same slice is convex because `epigraph F` is convex.
    simpa [C] using convex_perspectiveEpigraphSlice_of_convex_epigraph hF_conv
  have hC_zero : (0 : ((ℝ × H) × ℝ)) ∉ C := by
    intro hzero
    rw [mem_perspectiveEpigraphSlice_iff] at hzero
    norm_num at hzero
  have hepigraph :
      epigraph (closedPerspectiveEReal φ hφ.2.nonempty) =
        epigraph (lowerSemicontinuousEnvelope (perspective F)) := by
    -- Route correction: the source proof is executed epigraph-first through the cone over the unit
    -- slice `C`, rather than by pointwise case splits on the lower semicontinuous envelope.
    calc
      epigraph (closedPerspectiveEReal φ hφ.2.nonempty)
          = epigraph (perspective F) ∪
              {p : ((ℝ × H) × ℝ) | p.1.1 = 0 ∧
                (p.1.2, p.2) ∈ epigraph (fun y : H ↦
                  (recessionFunction φ hφ.2.nonempty y : EReal))} := by
              simpa [F] using
                epigraph_closedPerspectiveEReal_eq_perspective_union_zero_slice φ hφ.2.nonempty
      _ = cone C ∪
            {p : ((ℝ × H) × ℝ) | p.1.1 = 0 ∧
              (p.1.2, p.2) ∈ Set.recessionCone (epigraph F)} := by
            rw [epigraph_perspective_eq_cone F hF_conv,
              epigraph_recessionFunction_eq_recessionCone_epigraph φ hφ.2]
      _ = cone C ∪ Set.recessionCone C := by
            rw [recessionCone_perspectiveEpigraphSlice_eq_zero_slice F hF_nonempty]
      _ = closure (cone C) := by
            rw [Set.cone_union_recessionCone_eq_closure_cone_of_nonempty_isClosed_convex_zero_not_mem
              C hC_nonempty hC_closed hC_conv hC_zero]
      _ = closure (epigraph (perspective F)) := by
            rw [epigraph_perspective_eq_cone F hF_conv]
      _ = epigraph (lowerSemicontinuousEnvelope (perspective F)) := by
            symm
            exact epi_lowerSemicontinuousHull_eq_closure_epi (perspective F)
  have hEq : closedPerspectiveEReal φ hφ.2.nonempty =
      lowerSemicontinuousEnvelope (perspective F) :=
    eq_of_epigraph_eq_of_forall_gt_bot hepigraph
      (closedPerspectiveEReal_ne_bot φ hφ.2.nonempty)
  -- The epigraph identity determines the function because the closed perspective never takes `⊥`.
  simpa [F] using hEq.symm

-- Proof sketch: combine the main equality with the fact that the lower semicontinuous envelope of
-- any function is lower semicontinuous, and use the cone/perspective description together with the
-- recession-function convexity results to package the closed perspective as an element of
-- `Γ₀(ℝ × H)`.
/-- The closed perspective associated with a `Γ₀(H)` function belongs to `Γ₀(ℝ × H)`. -/
theorem closedPerspective_mem_gammaZero
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H)) :
    closedPerspective φ hφ.2.nonempty ∈ Γ₀(ℝ × H) := by
  rw [mem_gammaZero_iff]
  let F : H → EReal := fun x : H ↦ (φ x : EReal)
  have hclosed_eq :
      (fun p : ℝ × H ↦ (closedPerspective φ hφ.2.nonempty p : EReal)) =
        lowerSemicontinuousEnvelope (perspective F) := by
    funext p
    rw [closedPerspective_coe,
      lowerSemicontinuousEnvelope_perspective_eq_closedPerspectiveEReal (φ := φ) (hφ := hφ)]
  constructor
  · -- The main theorem identifies the closed perspective with a lower semicontinuous envelope.
    rw [hclosed_eq]
    exact (lowerSemicontinuousHull_isGreatest (perspective F)).1.1
  · have hF_conv : Convex ℝ (epigraph F) :=
      convex_epigraph_coe_of_convexOn_local hφ.2
    have hclosed_epi_conv :
        Convex ℝ (epigraph (fun p : ℝ × H ↦
          (closedPerspective φ hφ.2.nonempty p : EReal))) := by
      -- The closed perspective epigraph is the closure of the convex perspective epigraph.
      rw [hclosed_eq, epi_lowerSemicontinuousHull_eq_closure_epi]
      exact (convex_epigraph_perspective F hF_conv).closure
    have hJ :=
      (convex_epigraph_iff_jensen_on_dom
        (fun p : ℝ × H ↦ (closedPerspective φ hφ.2.nonempty p : EReal))).1 hclosed_epi_conv
    refine ⟨?_, subset_rfl, ?_⟩
    · rcases hφ.2.nonempty with ⟨x, hx⟩
      refine ⟨(1, x), ?_⟩
      rw [mem_effectiveDomain_iff, closedPerspective_coe,
        closedPerspectiveEReal_apply_of_ne_zero (φ := φ) (hdom := hφ.2.nonempty) (by norm_num),
        perspective_apply_of_pos (fun y : H ↦ (φ y : EReal)) (by norm_num)]
      simpa using (mem_effectiveDomain_iff.mp hx)
    · intro x hx y hy α hα hα_lt_one
      have hx' : x ∈ dom (fun p : ℝ × H ↦ (closedPerspective φ hφ.2.nonempty p : EReal)) := by
        simpa [effectiveDomain, dom] using hx
      have hy' : y ∈ dom (fun p : ℝ × H ↦ (closedPerspective φ hφ.2.nonempty p : EReal)) := by
        simpa [effectiveDomain, dom] using hy
      -- Jensen convexity on the effective domain is exactly the `Γ₀` convexity requirement.
      simpa [effectiveDomain, dom] using hJ hx' hy' hα hα_lt_one

end Hilbert

end ERealFunction
