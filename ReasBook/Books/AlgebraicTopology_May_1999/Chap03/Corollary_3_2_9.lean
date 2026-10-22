/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Example_3_2_8
import AlgebraicTopology_May_1999.Chap03.Theorem_3_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped FundamentalGroup TopCat

noncomputable section

/-- Helper for Corollary 3.2.9: after projecting a lifted loop and casting its endpoint back to the
basepoint, one recovers the original loop. -/
private theorem liftPath_projection_eq_loop
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
    (hp : IsCoveringMap p) (e : E) (γ : Path (p e) (p e)) {y : E}
    (hy : y = hp.liftPath γ e γ.source 1) (hb : p y = p e) :
    (((Path.mk (hp.liftPath γ e γ.source) (hp.liftPath_zero γ e γ.source) rfl).cast rfl hy).map
      hp.continuous).cast rfl hb.symm = γ := by
  -- The lifted path was defined so that its projection agrees pointwise with `γ`.
  ext t
  simp only [ContinuousMap.toFun_eq_coe, Path.cast_coe, Path.map_coe, Path.coe_mk',
    Function.comp_apply]
  exact congr_fun (hp.liftPath_lifts γ e γ.source) t

/-- Helper for Corollary 3.2.9: the monodromy orbit map of a universal cover is injective. -/
private theorem universal_cover_fundamentalGroupToFiber_injective
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
    (hp : IsUniversalCoveringMap p) (e : E) :
    Function.Injective (fun γ : FundamentalGroup B (p e) ↦ hp.isCoveringMap.monodromy γ.toPath
      ⟨e, rfl⟩) := by
  let _ : SimplyConnectedSpace E := hp.simplyConnectedSpace
  change Function.Injective
    (fun γ : Path.Homotopic.Quotient (p e) (p e) ↦ hp.isCoveringMap.monodromy γ ⟨e, rfl⟩)
  intro γ₀ γ₁ hγ
  revert hγ
  refine Quotient.inductionOn₂ γ₀ γ₁ ?_
  intro γ₀' γ₁' hγ'
  let y : E := hp.isCoveringMap.liftPath γ₀' e γ₀'.source 1
  have hend :
      y = hp.isCoveringMap.liftPath γ₁' e γ₁'.source 1 := by
    -- Equality in the fiber says the two lifted loops have the same endpoint.
    exact congrArg Subtype.val hγ'
  have hb : p y = p e := by
    simpa using hp.isCoveringMap.liftPath_endpoint_mem_fiber ⟨e, rfl⟩ γ₀'
  let Γ₀ : Path e y :=
    Path.mk (hp.isCoveringMap.liftPath γ₀' e γ₀'.source)
      (hp.isCoveringMap.liftPath_zero γ₀' e γ₀'.source) rfl
  let Γ₁ : Path e y :=
    (Path.mk (hp.isCoveringMap.liftPath γ₁' e γ₁'.source)
      (hp.isCoveringMap.liftPath_zero γ₁' e γ₁'.source) rfl).cast rfl hend
  have hΓ :
      Path.Homotopic.Quotient.mk Γ₀ = Path.Homotopic.Quotient.mk Γ₁ := by
    -- Simply connectedness makes any two paths with these common endpoints homotopic.
    exact Path.Homotopic.Quotient.eq.mpr (SimplyConnectedSpace.paths_homotopic Γ₀ Γ₁)
  have hmap :
      (Path.Homotopic.Quotient.mk Γ₀).map ⟨p, hp.isCoveringMap.continuous⟩ =
        (Path.Homotopic.Quotient.mk Γ₁).map ⟨p, hp.isCoveringMap.continuous⟩ := by
    exact congrArg (fun q : Path.Homotopic.Quotient e y ↦ q.map ⟨p, hp.isCoveringMap.continuous⟩) hΓ
  have hmap_cast :
      ((Path.Homotopic.Quotient.mk Γ₀).map ⟨p, hp.isCoveringMap.continuous⟩).cast rfl hb.symm =
        ((Path.Homotopic.Quotient.mk Γ₁).map ⟨p, hp.isCoveringMap.continuous⟩).cast rfl
          hb.symm := by
    -- Cast both projected paths to actual loops at `p e`.
    exact congrArg (fun q : Path.Homotopic.Quotient (p e) (p y) ↦ q.cast rfl hb.symm) hmap
  have hγ₀ :
      ((Path.Homotopic.Quotient.mk Γ₀).map ⟨p, hp.isCoveringMap.continuous⟩).cast rfl hb.symm =
        Path.Homotopic.Quotient.mk γ₀' := by
    -- The first projected lift is the original loop `γ₀'`.
    exact congrArg Path.Homotopic.Quotient.mk
      (liftPath_projection_eq_loop hp.isCoveringMap e γ₀' rfl hb)
  have hγ₁ :
      ((Path.Homotopic.Quotient.mk Γ₁).map ⟨p, hp.isCoveringMap.continuous⟩).cast rfl hb.symm =
        Path.Homotopic.Quotient.mk γ₁' := by
    -- The same projection identity holds for the second lifted loop after endpoint alignment.
    exact congrArg Path.Homotopic.Quotient.mk
      (liftPath_projection_eq_loop hp.isCoveringMap e γ₁' hend hb)
  exact hγ₀.symm.trans (hmap_cast.trans hγ₁)

/-- Helper for Corollary 3.2.9: monodromy along the projected class of a path from `e` to `z`
recovers `z`. -/
private theorem universal_cover_fundamentalGroupToFiber_from_path
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
    (hp : IsUniversalCoveringMap p) {e z : E} (γ : Path e z) (hz : p z = p e) :
    hp.isCoveringMap.monodromy
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((γ.map hp.isCoveringMap.continuous).cast rfl hz.symm))).toPath
      ⟨e, rfl⟩ =
      ⟨z, hz⟩ := by
  have hγ :
      hp.isCoveringMap.liftPath ((γ.map hp.isCoveringMap.continuous).cast rfl hz.symm) e
          ((γ.map hp.isCoveringMap.continuous).cast rfl hz.symm).source =
        γ.toContinuousMap := by
    -- The original path `γ` is already the unique lift of its projected loop starting at `e`.
    refine
      ((hp.isCoveringMap.eq_liftPath_iff'
        ((γ.map hp.isCoveringMap.continuous).cast rfl hz.symm).source).2 ?_).symm
    constructor
    · ext t
      simp [Path.cast]
    · exact γ.source
  apply Subtype.ext
  -- Evaluating the uniqueness identity at `1` recovers the endpoint `z`.
  simpa using congrArg (fun f : C(↑unitInterval, E) ↦ f 1) hγ

/-- Helper for Corollary 3.2.9: the monodromy orbit map of a universal cover is surjective onto
the fiber over the chosen basepoint. -/
private theorem universal_cover_fundamentalGroupToFiber_surjective
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
    (hp : IsUniversalCoveringMap p) (e : E) :
    Function.Surjective (fun γ : FundamentalGroup B (p e) ↦ hp.isCoveringMap.monodromy γ.toPath
      ⟨e, rfl⟩) := by
  let _ : SimplyConnectedSpace E := hp.simplyConnectedSpace
  let _ : PathConnectedSpace E := inferInstance
  rintro ⟨z, hz⟩
  have hz' : p z = p e := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hz
  let γ : Path e z := PathConnectedSpace.somePath e z
  refine ⟨FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk ((γ.map hp.isCoveringMap.continuous).cast rfl hz'.symm)), ?_⟩
  -- Projecting a path from `e` to `z` gives a loop whose lifted endpoint is exactly `z`.
  simpa [γ] using universal_cover_fundamentalGroupToFiber_from_path hp γ hz'

/-- Helper for Corollary 3.2.9: a universal cover identifies `π₁(B, p e)` with the fiber over
`p e` by the monodromy orbit map based at `e`. -/
private noncomputable def universal_cover_fundamentalGroupFiberEquiv
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
    (hp : IsUniversalCoveringMap p) (e : E) :
    FundamentalGroup B (p e) ≃ p ⁻¹' {p e} :=
  Equiv.ofBijective
    (fun γ : FundamentalGroup B (p e) ↦ hp.isCoveringMap.monodromy γ.toPath ⟨e, rfl⟩)
    ⟨universal_cover_fundamentalGroupToFiber_injective hp e,
      universal_cover_fundamentalGroupToFiber_surjective hp e⟩

/-- Helper for Corollary 3.2.9: antipodal points define the same point of projective space. -/
private theorem sphereToRealProjectiveSpace_neg_eq (n : ℕ) (y : 𝕊 n) :
    sphereToRealProjectiveSpace n (-y) = sphereToRealProjectiveSpace n y := by
  -- The quotient relation identifies each point with its antipode.
  exact (sphereToRealProjectiveSpace_eq_iff n).2 (Or.inr rfl)

/-- Helper for Corollary 3.2.9: a point in the fiber over `sphereToRealProjectiveSpace n y` is
either `y` or `-y`. -/
private theorem sphereToRealProjectiveSpace_fiber_cases
    (n : ℕ) {y z : 𝕊 n}
    (hz : sphereToRealProjectiveSpace n z = sphereToRealProjectiveSpace n y) :
    z = y ∨ z = -y := by
  -- Equality in the quotient is exactly the antipodal relation.
  exact (sphereToRealProjectiveSpace_eq_iff n).1 hz

/-- Helper for Corollary 3.2.9: unpacking a point of the fiber gives an equality of projective
classes. -/
private theorem sphereToRealProjectiveSpace_eq_of_mem_fiber
    (n : ℕ) {y : 𝕊 n}
    (z : (sphereToRealProjectiveSpace n) ⁻¹' {sphereToRealProjectiveSpace n y}) :
    sphereToRealProjectiveSpace n z.1 = sphereToRealProjectiveSpace n y := by
  -- Membership in the singleton fiber is exactly equality of quotient points.
  exact z.2

/-- Helper for Corollary 3.2.9: the class of `y` itself belongs to the fiber over its projective
image. -/
private theorem sphereToRealProjectiveSpace_self_mem_fiber
    (n : ℕ) (y : 𝕊 n) :
    y ∈ (sphereToRealProjectiveSpace n) ⁻¹' {sphereToRealProjectiveSpace n y} := by
  -- The quotient map obviously sends `y` to its own class.
  simp [Set.mem_preimage, Set.mem_singleton_iff]

/-- Helper for Corollary 3.2.9: the antipode of `y` lies in the fiber over the class of `y`. -/
private theorem sphereToRealProjectiveSpace_neg_mem_fiber
    (n : ℕ) (y : 𝕊 n) :
    -y ∈ (sphereToRealProjectiveSpace n) ⁻¹' {sphereToRealProjectiveSpace n y} := by
  -- The quotient map sends antipodal points to the same projective point.
  simp [Set.mem_preimage, Set.mem_singleton_iff, sphereToRealProjectiveSpace_neg_eq]

/-- Helper for Corollary 3.2.9: distinguish the two points in a projective-space fiber by testing
whether the representative is literally `y`. -/
private def sphereToRealProjectiveSpace_fiber_toBool
    (n : ℕ) (y : 𝕊 n) :
    ((sphereToRealProjectiveSpace n) ⁻¹' {sphereToRealProjectiveSpace n y}) → Bool :=
  let _ := Classical.decEq (𝕊 n)
  fun z ↦ if z.1 = y then false else true

/-- Helper for Corollary 3.2.9: realize the two Boolean values by the two representatives `y` and
`-y` of the projective-space fiber. -/
private def bool_to_sphereToRealProjectiveSpace_fiber
    (n : ℕ) (y : 𝕊 n) :
    Bool → ((sphereToRealProjectiveSpace n) ⁻¹' {sphereToRealProjectiveSpace n y}) :=
  fun b ↦ if b then ⟨-y, sphereToRealProjectiveSpace_neg_mem_fiber n y⟩
    else ⟨y, sphereToRealProjectiveSpace_self_mem_fiber n y⟩

/-- Helper for Corollary 3.2.9: the Boolean-to-fiber map is a left inverse to the fiber
classification map. -/
private theorem sphereToRealProjectiveSpace_fiber_leftInverse
    (n : ℕ) (y : 𝕊 n) :
    Function.LeftInverse (bool_to_sphereToRealProjectiveSpace_fiber n y)
      (sphereToRealProjectiveSpace_fiber_toBool n y) := by
  classical
  intro z
  by_cases hz : z.1 = y
  · -- The `false` branch recovers the representative `y`.
    apply Subtype.ext
    simp [bool_to_sphereToRealProjectiveSpace_fiber, sphereToRealProjectiveSpace_fiber_toBool, hz]
  · have hz' : z.1 = -y := by
      rcases sphereToRealProjectiveSpace_fiber_cases n
          (sphereToRealProjectiveSpace_eq_of_mem_fiber n z) with hzy | hzy
      · exact (hz hzy).elim
      · exact hzy
    -- If the representative is not `y`, the fiber condition forces it to be `-y`.
    have hneq : (-y : 𝕊 n) ≠ y := sphere_neg_ne_self n y
    apply Subtype.ext
    simp [bool_to_sphereToRealProjectiveSpace_fiber, sphereToRealProjectiveSpace_fiber_toBool,
      hz', hneq]

/-- Helper for Corollary 3.2.9: the Boolean-to-fiber map is a right inverse to the fiber
classification map. -/
private theorem sphereToRealProjectiveSpace_fiber_rightInverse
    (n : ℕ) (y : 𝕊 n) :
    Function.RightInverse (bool_to_sphereToRealProjectiveSpace_fiber n y)
      (sphereToRealProjectiveSpace_fiber_toBool n y) := by
  classical
  intro b
  cases b
  · -- The `false` branch is represented by the chosen point `y`.
    change sphereToRealProjectiveSpace_fiber_toBool n y
        ⟨y, sphereToRealProjectiveSpace_self_mem_fiber n y⟩ = false
    simp [sphereToRealProjectiveSpace_fiber_toBool]
  · -- The `true` branch is represented by the antipode `-y`, which is distinct from `y`.
    change sphereToRealProjectiveSpace_fiber_toBool n y
        ⟨-y, sphereToRealProjectiveSpace_neg_mem_fiber n y⟩ = true
    simp [sphereToRealProjectiveSpace_fiber_toBool, sphere_neg_ne_self]

/-- Helper for Corollary 3.2.9: the geometric fiber of `S^n → RP^n` over the class of `y`
is a two-element type. -/
private theorem sphereToRealProjectiveSpace_fiber_toBool_bijective
    (n : ℕ) (y : 𝕊 n) :
    Function.Bijective (sphereToRealProjectiveSpace_fiber_toBool n y) := by
  refine ⟨(sphereToRealProjectiveSpace_fiber_leftInverse n y).injective,
    (sphereToRealProjectiveSpace_fiber_rightInverse n y).surjective⟩

/-- Helper for Corollary 3.2.9: the fiber of `S^n → RP^n` over the class of `y` has exactly two
elements, represented by `y` and `-y`. -/
private noncomputable def sphereToRealProjectiveSpace_fiber_equiv_bool
    (n : ℕ) (y : 𝕊 n) :
    ((sphereToRealProjectiveSpace n) ⁻¹' {sphereToRealProjectiveSpace n y}) ≃ Bool :=
  Equiv.ofBijective (sphereToRealProjectiveSpace_fiber_toBool n y)
    (sphereToRealProjectiveSpace_fiber_toBool_bijective n y)

/-- Helper for Corollary 3.2.9: the based fundamental group of `RP^n` has cardinality two once
`n ≥ 2`. -/
private theorem realProjectiveSpace_fundamentalGroup_card_two
    {n : ℕ} (hn : 2 ≤ n) (y : 𝕊 n) :
    Nat.card (FundamentalGroup (RealProjectiveSpace n) (sphereToRealProjectiveSpace n y)) = 2 := by
  -- Route correction: use the canonical universal cover from Example 3.2.8 instead of the local
  -- duplicate orbit-map wrapper that originally sat in this file.
  let hEquiv :=
    universal_cover_fundamentalGroupFiberEquiv
      (sphereToRealProjectiveSpace_isUniversalCoveringMap hn) y
  calc
    Nat.card (FundamentalGroup (RealProjectiveSpace n) (sphereToRealProjectiveSpace n y)) =
        Nat.card (((sphereToRealProjectiveSpace n) ⁻¹'
          {sphereToRealProjectiveSpace n y})) := by
      exact Nat.card_congr hEquiv
    _ = Nat.card Bool := by
      exact Nat.card_congr (sphereToRealProjectiveSpace_fiber_equiv_bool n y)
    _ = 2 := by
      simp

/-- Corollary 3.2.9: for `n ≥ 2`, the fundamental group of `RP^n` at any basepoint is the cyclic
group of order two. -/
theorem realProjectiveSpace_fundamentalGroup_mulEquiv_zmod_two {n : ℕ} (hn : 2 ≤ n)
    (x : RealProjectiveSpace n) :
    Nonempty (FundamentalGroup (RealProjectiveSpace n) x ≃* Multiplicative (ZMod 2)) := by
  rcases Quotient.exists_rep x with ⟨y, rfl⟩
  -- Represent the basepoint by `y`, compute the cardinality of `π₁`, and invoke the prime-card
  -- classification of groups of order two.
  refine ⟨mulEquivOfPrimeCardEq (realProjectiveSpace_fundamentalGroup_card_two hn y) ?_⟩
  simp
