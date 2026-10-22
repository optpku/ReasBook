/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Fact_6_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

omit [FiniteDimensional ℝ H] in
/-- Helper for Corollary 8.41: convexity on the effective domain forces the effective domain
itself to be convex. -/
private theorem convex_effectiveDomain_of_convexOn
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f)) :
    Convex ℝ (effectiveDomain f) := by
  -- A convex combination of finite endpoint values is still finite, so the combination stays in
  -- the effective domain.
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  have ha_lt_one : a < 1 := by
    linarith
  have hsub_cast : (((1 - a : ℝ) : EReal)) = 1 - (a : EReal) := by
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
  have hb_eq : (1 - a : ℝ) = b := by
    linarith
  have hineq0 := hconv.ineq hx hy ha ha_lt_one
  have hineq1 :
      (f (a • x + (1 - a) • y) : EReal) ≤
        (a : EReal) * (f x : EReal) + (((1 - a : ℝ) : EReal) * (f y : EReal)) := by
    simpa [hsub_cast] using hineq0
  have hineq :
      (f (a • x + b • y) : EReal) ≤
        (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) := by
    simpa [hb_eq] using hineq1
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hsum :
      (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) =
        ((a * (f x : EReal).toReal + b * (f y : EReal).toReal : ℝ) : EReal) := by
    rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    simp
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt (hineq.trans_eq hsum) (EReal.coe_lt_top _)

omit [FiniteDimensional ℝ H] in
/-- Helper for Corollary 8.41: the finite real representative is convex on the effective domain. -/
private theorem toReal_convexOn_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f)) :
    _root_.ConvexOn ℝ (effectiveDomain f) (fun x ↦ (f x : EReal).toReal) := by
  -- Rewrite the extended-real Jensen inequality through `toReal` on finite-domain points.
  rw [convexOn_iff_forall_pos]
  constructor
  · exact convex_effectiveDomain_of_convexOn f hconv
  · intro x hx y hy a b ha hb hab
    have ha_lt_one : a < 1 := by
      linarith
    have hsub_cast : (((1 - a : ℝ) : EReal)) = 1 - (a : EReal) := by
      rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
    have hb_eq : (1 - a : ℝ) = b := by
      linarith
    have hineq0 := hconv.ineq hx hy ha ha_lt_one
    have hineq1 :
        (f (a • x + (1 - a) • y) : EReal) ≤
          (a : EReal) * (f x : EReal) + (((1 - a : ℝ) : EReal) * (f y : EReal)) := by
      simpa [hsub_cast] using hineq0
    have hineq :
        (f (a • x + b • y) : EReal) ≤
          (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) := by
      simpa [hb_eq] using hineq1
    have hxy : a • x + b • y ∈ effectiveDomain f :=
      (convex_effectiveDomain_of_convexOn f hconv) hx hy ha.le hb.le hab
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (f y : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    have hxy_bot : (f (a • x + b • y) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (a • x + b • y) : EReal) from
        (f (a • x + b • y)).2)
    have hsum :
        (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) =
          ((a * (f x : EReal).toReal + b * (f y : EReal).toReal : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot,
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      simp
    have hright_top :
        (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) ≠ ⊤ := by
      rw [hsum]
      exact ne_of_lt (EReal.coe_lt_top _)
    simpa [hsum] using EReal.toReal_le_toReal hineq hxy_bot hright_top

omit [FiniteDimensional ℝ H] in
/-- Helper for Corollary 8.41: after translating to the direction of the affine span of the
effective domain, the real representative remains convex on the chart preimage of the domain. -/
private theorem charted_toReal_convexOn_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    (x₀ : H) :
    let A : AffineSubspace ℝ H := _root_.affineSpan ℝ (effectiveDomain f)
    let V : Submodule ℝ H := A.direction
    let φ : V →ᵃ[ℝ] H :=
      { toFun := fun v ↦ (v : H) + x₀
        linear := V.subtype
        map_vadd' := by
          intro p v
          change (((v + p : V) : H) + x₀) = (v : H) + (((p : V) : H) + x₀)
          simp [add_assoc] }
    _root_.ConvexOn ℝ (φ ⁻¹' effectiveDomain f) (fun v ↦ (f (φ v) : EReal).toReal) := by
  let A : AffineSubspace ℝ H := _root_.affineSpan ℝ (effectiveDomain f)
  let V : Submodule ℝ H := A.direction
  let φ : V →ᵃ[ℝ] H :=
    { toFun := fun v ↦ (v : H) + x₀
      linear := V.subtype
      map_vadd' := by
        intro p v
        change (((v + p : V) : H) + x₀) = (v : H) + (((p : V) : H) + x₀)
        simp [add_assoc] }
  -- Precompose the ambient convex representative with the affine chart.
  simpa [φ] using (toReal_convexOn_effectiveDomain f hconv).comp_affineMap φ

omit [NormedSpace ℝ H] [FiniteDimensional ℝ H] in
/-- Helper for Corollary 8.41: compactness upgrades local Lipschitz control to a single positive
global Lipschitz constant. -/
private theorem exists_pos_lipschitzOnWith_of_isCompact_of_locallyLipschitzOn
    {s : Set H} {g : H → ℝ} (hs : IsCompact s) (hloc : LocallyLipschitzOn s g) :
    ∃ β : NNReal, 0 < β ∧ LipschitzOnWith β g s := by
  -- First obtain a compact-set Lipschitz constant, then enlarge it to a strictly positive one.
  obtain ⟨K, hK⟩ := hloc.exists_lipschitzOnWith_of_compact hs
  exact ⟨max K 1, zero_lt_one.trans_le (le_max_right K 1), hK.weaken (le_max_left _ _)⟩

omit [FiniteDimensional ℝ H] in
/-- Helper for Corollary 8.41: intrinsic interior membership is equivalent to interior membership
of the translated copy of the set inside the direction of its affine span. -/
private theorem intrinsicInterior_mem_iff_zero_mem_interior_translated_direction_preimage_normed
    {C : Set H} {x : H} (hx : x ∈ C) :
    let V : Submodule ℝ H := (_root_.affineSpan ℝ C).direction
    let T : Set V := ((↑) : V → H) ⁻¹' (C - ({x} : Set H))
    x ∈ intrinsicInterior ℝ C ↔ (0 : V) ∈ interior T := by
  haveI : Nonempty C := ⟨x, hx⟩
  let xA : _root_.affineSpan ℝ C := ⟨x, subset_affineSpan ℝ C hx⟩
  letI : Nonempty (_root_.affineSpan ℝ C) := ⟨xA⟩
  let S : Set (_root_.affineSpan ℝ C) := ((↑) ⁻¹' C)
  let T : Set ((_root_.affineSpan ℝ C).direction) := ((↑) ⁻¹' (C - ({x} : Set H)))
  let e : ((_root_.affineSpan ℝ C).direction) ≃ₜ (_root_.affineSpan ℝ C) :=
    (AffineIsometryEquiv.vaddConst ℝ xA).toHomeomorph
  have hzero : e (0 : (_root_.affineSpan ℝ C).direction) = xA := by
    -- The translated origin maps back to the chosen base point in the affine span.
    apply Subtype.ext
    change ↑((0 : (_root_.affineSpan ℝ C).direction) +ᵥ xA) = x
    simp [xA]
  have hmem : x ∈ intrinsicInterior ℝ C ↔ xA ∈ interior S := by
    constructor
    · intro hxInt
      -- Unfold the intrinsic-interior image and identify the unique affine-span point above `x`.
      rcases hxInt with ⟨y, hy, hyx⟩
      have hy_eq : y = xA := by
        apply Subtype.ext
        simpa [xA] using hyx
      simpa [S] using hy_eq ▸ hy
    · intro hxA
      -- The canonical affine-span representative of `x` witnesses intrinsic-interior membership.
      exact ⟨xA, by simpa [S] using hxA, by simp [xA]⟩
  have hcoee (v : (_root_.affineSpan ℝ C).direction) :
      (((e v) : _root_.affineSpan ℝ C) : H) =
        ((v : ((_root_.affineSpan ℝ C).direction)) : H) + x := by
    -- In ambient coordinates, `vaddConst` is just translation by `x`.
    change ↑(v +ᵥ xA) = ↑v + x
    simp [xA]
  have hpre : e ⁻¹' S = T := by
    -- Pulling `C` back along the translation homeomorphism gives the textbook translate `C - {x}`.
    ext v
    rw [show (v ∈ e ⁻¹' S) ↔ (((e v) : _root_.affineSpan ℝ C) : H) ∈ C by rfl]
    rw [hcoee]
    simp [T, sub_eq_add_neg, add_comm]
  have hhomeo : xA ∈ interior S ↔ (0 : (_root_.affineSpan ℝ C).direction) ∈ interior T := by
    constructor
    · intro hxA
      -- Transport interior membership from `xA` to the origin through the translation homeomorphism.
      have hpreimage : (0 : (_root_.affineSpan ℝ C).direction) ∈ e ⁻¹' interior S := by
        simpa [hzero] using hxA
      rw [e.preimage_interior, hpre] at hpreimage
      simpa using hpreimage
    · intro h0
      -- Transport the origin interior point back to `xA`.
      have hpreimage : (0 : (_root_.affineSpan ℝ C).direction) ∈ e ⁻¹' interior S := by
        rw [e.preimage_interior, hpre]
        simpa using h0
      simpa [hzero] using hpreimage
  exact hmem.trans hhomeo

omit [FiniteDimensional ℝ H] in
/-- Helper for Corollary 8.41: for a convex set, the source-facing cone agrees with the canonical
positive-multiple cone from mathlib. -/
private theorem cone_eq_toCone_of_convex_normed_aux {S : Set H} (hS_convex : Convex ℝ S) :
    cone S = ((hS_convex.toCone S : ConvexCone ℝ H) : Set H) := by
  -- Rewrite the source cone through the least convex cone containing `S`.
  have hHull :
      (ConvexCone.hull ℝ S : Set H) = ((hS_convex.toCone S : ConvexCone ℝ H) : Set H) := by
    simpa [ConvexCone.hull] using
      congrArg (fun C : ConvexCone ℝ H => (C : Set H)) hS_convex.toCone_eq_sInf.symm
  simpa [Set.cone_def] using hHull

omit [FiniteDimensional ℝ H] in
/-- Helper for Corollary 8.41: once a convex set has nonempty interior, the origin is interior
exactly when its source-facing cone fills the ambient space. -/
private theorem zero_mem_interior_iff_cone_eq_univ_of_convex_nonempty_interior_normed_aux
    {S : Set H} (hS_convex : Convex ℝ S) (hS_int_nonempty : (interior S).Nonempty)
    (_h0S : (0 : H) ∈ S) :
    (0 : H) ∈ interior S ↔ cone S = (univ : Set H) := by
  constructor
  · intro h0_int
    have hmem : S ∈ nhds (0 : H) := mem_interior_iff_mem_nhds.mp h0_int
    rcases Metric.mem_nhds_iff.mp hmem with ⟨ε, hε, hball⟩
    ext y
    constructor
    · intro _
      simp
    · intro _
      let t : ℝ := ε / (1 + ‖y‖)
      have ht : 0 < t := by
        dsimp [t]
        positivity
      have hty_norm : ‖t • y‖ < ε := by
        have hden : 0 < 1 + ‖y‖ := by
          positivity
        have hy_lt : ‖y‖ < 1 + ‖y‖ := by
          nlinarith [norm_nonneg y]
        have hfrac_lt : ‖y‖ / (1 + ‖y‖) < (1 : ℝ) := by
          refine (div_lt_iff₀ hden).2 ?_
          nlinarith [norm_nonneg y]
        have hlt' : ε / (1 + ‖y‖) * ‖y‖ < ε := by
          have hε_pos : 0 < ε := hε
          simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
            mul_lt_mul_of_pos_left hfrac_lt hε_pos
        have hlt : t * ‖y‖ < ε := by
          simpa [t] using hlt'
        simpa [norm_smul, Real.norm_eq_abs, abs_of_pos ht] using hlt
      have hty_mem : t • y ∈ S := hball <| by
        simpa [Metric.mem_ball, dist_eq_norm] using hty_norm
      rw [cone_eq_toCone_of_convex_normed_aux hS_convex]
      exact (Convex.mem_toCone hS_convex).2 ⟨1 / t, by positivity, t • y, hty_mem, by
        rw [one_div, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]⟩
  · intro hcone
    rcases hS_int_nonempty with ⟨z, hz⟩
    have hnegz : -z ∈ cone S := by
      rw [hcone]
      simp
    rw [cone_eq_toCone_of_convex_normed_aux hS_convex] at hnegz
    rcases (Convex.mem_toCone hS_convex).1 hnegz with ⟨c, hc, y, hy, hcy⟩
    have ha : 0 ≤ c / (c + 1) := by positivity
    have hb : 0 < 1 / (c + 1) := by positivity
    have hab : c / (c + 1) + 1 / (c + 1) = (1 : ℝ) := by
      field_simp [hc.ne']
    have hcombo :
        (c / (c + 1)) • y + (1 / (c + 1)) • z ∈ interior S :=
      hS_convex.combo_self_interior_mem_interior hy hz ha hb hab
    have hzero :
        (c / (c + 1)) • y + (1 / (c + 1)) • z = (0 : H) := by
      calc
        (c / (c + 1)) • y + (1 / (c + 1)) • z
            = (1 / (c + 1)) • (c • y) + (1 / (c + 1)) • z := by
                rw [div_eq_mul_inv, one_div, smul_smul, mul_comm c ((c + 1)⁻¹)]
        _ = (1 / (c + 1)) • (c • y + z) := by
          rw [smul_add]
        _ = (0 : H) := by
          rw [hcy, neg_add_cancel, smul_zero]
    exact hzero ▸ hcombo

/-- Helper for Corollary 8.41: in finite dimension, a convex set containing the origin has the
origin in its interior whenever its cone fills the ambient space. -/
private theorem zero_mem_interior_of_cone_eq_univ_of_convex_of_finiteDimensional
    {S : Set H} (hS_convex : Convex ℝ S) (h0S : (0 : H) ∈ S)
    (hcone : cone S = (univ : Set H)) :
    (0 : H) ∈ interior S := by
  have hsubset : cone S ⊆ (Submodule.span ℝ S : Set H) := by
    -- The span is a convex cone containing `S`, so it contains the source cone as well.
    intro y hy
    exact
      ConvexCone.hull_min
        (C := (Submodule.span ℝ S).toConvexCone)
        (fun z hz ↦ Submodule.subset_span hz) hy
  have hspan_top : Submodule.span ℝ S = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    have hy_cone : y ∈ cone S := by
      rw [hcone]
      simp
    exact hsubset hy_cone
  have hvectorTop : vectorSpan ℝ S = ⊤ := by
    -- Because `0 ∈ S`, the affine translate defining `vectorSpan` is just `S` itself.
    rw [vectorSpan_eq_span_vsub_set_right (k := ℝ) (s := S) (p := (0 : H)) h0S]
    simpa [vsub_eq_sub] using hspan_top
  have haffTop : affineSpan ℝ S = ⊤ := by
    exact
      (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ H H ⟨0, h0S⟩).2
        hvectorTop
  have hS_int_nonempty : (interior S).Nonempty :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top hS_convex).2 haffTop
  exact
    (zero_mem_interior_iff_cone_eq_univ_of_convex_nonempty_interior_normed_aux
      hS_convex hS_int_nonempty h0S).2 hcone

/-- Helper for Corollary 8.41: in finite-dimensional real normed spaces, convex relative-interior
membership upgrades to intrinsic-interior membership. -/
private theorem mem_intrinsicInterior_of_mem_relativeInterior_of_finiteDimensional_normed
    {S : Set H} (hS_convex : Convex ℝ S) {x : H} (hx_ri : x ∈ ri S) :
    x ∈ intrinsicInterior ℝ S := by
  let V : Submodule ℝ H := (_root_.affineSpan ℝ S).direction
  let T : Set V := ((↑) : V → H) ⁻¹' (S - ({x} : Set H))
  have hx : x ∈ S := (Set.mem_relativeInterior_iff.mp hx_ri).1
  have hVeq : V = Submodule.span ℝ (S - ({x} : Set H)) := by
    -- Route correction: rewrite the source span in the canonical affine-span direction model.
    calc
      V = vectorSpan ℝ S := by
        rw [show V = (_root_.affineSpan ℝ S).direction by rfl, direction_affineSpan]
      _ = Submodule.span ℝ (S - ({x} : Set H)) := by
        simpa [vsub_eq_sub, sub_eq_add_neg] using
          (vectorSpan_eq_span_vsub_set_right (k := ℝ) (s := S) (p := x) hx)
  have htranslate_convex : Convex ℝ (S - ({x} : Set H)) := by
    -- Translation keeps the convex source set convex.
    simpa [sub_eq_add_neg, add_comm] using hS_convex.translate (-x)
  have hT_convex : Convex ℝ T := by
    -- Pull the translated set back to the affine-span direction chart.
    simpa [T] using htranslate_convex.affine_preimage V.subtype.toAffineMap
  have h0T : (0 : V) ∈ T := by
    -- The origin corresponds to the trivial translate of `x`.
    change (0 : H) ∈ S - ({x} : Set H)
    exact Set.mem_sub.mpr ⟨x, hx, x, by simp, sub_self x⟩
  have hInt :
      x ∈ intrinsicInterior ℝ S ↔ (0 : V) ∈ interior T := by
    -- Chapter 6 identifies intrinsic interior with ordinary interior in the translated chart.
    simpa [V, T] using
      intrinsicInterior_mem_iff_zero_mem_interior_translated_direction_preimage_normed
        (C := S) hx
  have hcone_mem : ∀ {v : V}, v ∈ cone T ↔ ((v : H) ∈ cone (S - ({x} : Set H))) := by
    intro v
    rw [cone_eq_toCone_of_convex_normed_aux hT_convex, cone_eq_toCone_of_convex_normed_aux htranslate_convex]
    constructor
    · intro hv
      rcases (Convex.mem_toCone hT_convex).1 hv with ⟨c, hc, y, hy, rfl⟩
      exact (Convex.mem_toCone htranslate_convex).2 ⟨c, hc, (y : H), hy, rfl⟩
    · intro hv
      rcases (Convex.mem_toCone htranslate_convex).1 hv with ⟨c, hc, y, hy, hyv⟩
      have hyV : y ∈ V := by
        simpa [hVeq] using
          (Submodule.subset_span hy : y ∈ Submodule.span ℝ (S - ({x} : Set H)))
      refine (Convex.mem_toCone hT_convex).2 ?_
      refine ⟨c, hc, ⟨y, hyV⟩, hy, ?_⟩
      apply Subtype.ext
      simpa using hyv
  have hconeV : cone (S - ({x} : Set H)) = (V : Set H) := by
    -- The source relative-interior criterion becomes a cone-equals-direction statement.
    simpa [hVeq] using (Set.mem_relativeInterior_iff.mp hx_ri).2
  have hconeT : cone T = (univ : Set V) := by
    ext v
    constructor
    · intro _
      simp
    · intro _
      have hv_cone : ((v : V) : H) ∈ cone (S - ({x} : Set H)) := by
        rw [hconeV]
        exact v.property
      exact hcone_mem.2 hv_cone
  have h0int : (0 : V) ∈ interior T :=
    zero_mem_interior_of_cone_eq_univ_of_convex_of_finiteDimensional hT_convex h0T hconeT
  exact hInt.mpr h0int

/-- Helper for Corollary 8.41: every point of a subset of the relative interior of the effective
domain admits a neighborhood within that subset on which the real representative is Lipschitz. -/
private theorem exists_local_lipschitzWithinAt_on_C_of_mem_relativeInterior
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {C : Set H} (hC_subset : C ⊆ ri (effectiveDomain f))
    {x : H} (hx : x ∈ C) :
    ∃ K : NNReal, ∃ t, t ∈ nhdsWithin x C ∧
      LipschitzOnWith K (fun y ↦ (f y : EReal).toReal) t := by
  let V : Submodule ℝ H := (_root_.affineSpan ℝ (effectiveDomain f)).direction
  let T : Set V := ((↑) : V → H) ⁻¹' (effectiveDomain f - ({x} : Set H))
  let φ : V →ᵃ[ℝ] H :=
    { toFun := fun v ↦ (v : H) + x
      linear := V.subtype
      map_vadd' := by
        intro p v
        change (((v + p : V) : H) + x) = (v : H) + (((p : V) : H) + x)
        simp [add_assoc] }
  let g : V → ℝ := fun v ↦ (f (φ v) : EReal).toReal
  have hconvV : _root_.ConvexOn ℝ (φ ⁻¹' effectiveDomain f) g := by
    -- Restrict the ambient convex representative to the translated direction chart.
    simpa [V, φ, g] using charted_toReal_convexOn_effectiveDomain f hconv x
  have hx_ri : x ∈ ri (effectiveDomain f) := hC_subset hx
  have hx_dom : x ∈ effectiveDomain f := (Set.mem_relativeInterior_iff.mp hx_ri).1
  have hx_intrinsic : x ∈ intrinsicInterior ℝ (effectiveDomain f) := by
    -- Route correction: use the local finite-dimensional normed-space bridge rather than the
    -- stronger Hilbert-space theorem packaged in Chapter 6.
    exact mem_intrinsicInterior_of_mem_relativeInterior_of_finiteDimensional_normed
      (convex_effectiveDomain_of_convexOn f hconv) hx_ri
  have hzero_int_T : (0 : V) ∈ interior T := by
    -- Chapter 6 identifies intrinsic interior with ordinary interior in the translated direction chart.
    simpa [V, T] using
      (intrinsicInterior_mem_iff_zero_mem_interior_translated_direction_preimage_normed
        (C := effectiveDomain f) hx_dom).mp hx_intrinsic
  have hzero_int : (0 : V) ∈ interior (φ ⁻¹' effectiveDomain f) := by
    -- The translated set and the chart preimage of the effective domain coincide.
    simpa [T, φ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hzero_int_T
  have hlocV : LocallyLipschitzOn (interior (φ ⁻¹' effectiveDomain f)) g :=
    hconvV.locallyLipschitzOn_interior
  obtain ⟨K, t, ht, hLip_t⟩ := hlocV hzero_int
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at ht
  obtain ⟨u, hu_nhds, hu_subset⟩ := ht
  have hu_int_nhds : u ∩ interior (φ ⁻¹' effectiveDomain f) ∈ nhds (0 : V) := by
    -- Intersect the local neighborhood with the open interior chart neighborhood.
    exact Filter.inter_mem hu_nhds (isOpen_interior.mem_nhds hzero_int)
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.mem_nhds_iff.mp hu_int_nhds
  refine ⟨K, Metric.ball x r ∩ C, ?_, ?_⟩
  · -- Use the ambient ball as a neighborhood basis element within `C`.
    exact mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Metric.ball x r, Metric.ball_mem_nhds x hr_pos, by
        intro y hy
        exact hy⟩
  · -- Lift ambient points back to the affine span and apply the subtype Lipschitz estimate.
    intro y hy z hz
    have hy_ri : y ∈ ri (effectiveDomain f) := hC_subset hy.2
    have hz_ri : z ∈ ri (effectiveDomain f) := hC_subset hz.2
    have hy_dom : y ∈ effectiveDomain f := (Set.mem_relativeInterior_iff.mp hy_ri).1
    have hz_dom : z ∈ effectiveDomain f := (Set.mem_relativeInterior_iff.mp hz_ri).1
    have hyV_mem : y - x ∈ V := by
      change y - x ∈ (_root_.affineSpan ℝ (effectiveDomain f)).direction
      rw [direction_affineSpan]
      simpa [vsub_eq_sub] using vsub_mem_vectorSpan ℝ hy_dom hx_dom
    have hzV_mem : z - x ∈ V := by
      change z - x ∈ (_root_.affineSpan ℝ (effectiveDomain f)).direction
      rw [direction_affineSpan]
      simpa [vsub_eq_sub] using vsub_mem_vectorSpan ℝ hz_dom hx_dom
    let yV : V := ⟨y - x, hyV_mem⟩
    let zV : V := ⟨z - x, hzV_mem⟩
    have hyV_ball : yV ∈ Metric.ball (0 : V) r := by
      -- Translating by `x` identifies the ambient ball around `x` with the vector ball around `0`.
      change dist (y - x) 0 < r
      simpa [Metric.mem_ball, dist_eq_norm] using hy.1
    have hzV_ball : zV ∈ Metric.ball (0 : V) r := by
      -- The same translation identifies the second endpoint.
      change dist (z - x) 0 < r
      simpa [Metric.mem_ball, dist_eq_norm] using hz.1
    have hyV_t : yV ∈ t := hu_subset (hr_subset hyV_ball)
    have hzV_t : zV ∈ t := hu_subset (hr_subset hzV_ball)
    have hdist_yz : dist yV zV = dist y z := by
      change dist (y - x) (z - x) = dist y z
      exact dist_vsub_cancel_right y z x
    have hdist_yz_edist : edist yV zV = edist y z := by
      rw [edist_dist, edist_dist, hdist_yz]
    simpa [g, φ, yV, zV, hdist_yz_edist, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      hLip_t hyV_t hzV_t

-- Proof sketch: every point of `ri (effectiveDomain f)` admits, after restricting to the affine
-- hull of the effective domain, an open neighborhood on which the finite representative of `f` is
-- locally Lipschitz by the Chapter 8 continuity and local-Lipschitz results for convex functions.
-- Closed bounded sets are compact in finite dimension, so a finite subcover of `C` yields a
-- global positive Lipschitz constant on `C`.
/-- Corollary 8.41: if `C` is a closed bounded subset of the relative interior of the effective
domain of a proper convex `]-∞,+∞]`-valued function on a finite-dimensional real normed space,
then the real-valued representative of `f` is Lipschitz on `C` with some positive constant. -/
theorem exists_pos_lipschitzOnWith_on_closed_bounded_subset_relativeInterior_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {C : Set H} (hC_subset : C ⊆ ri (effectiveDomain f))
    (hC_closed : IsClosed C) (hC_bounded : Bornology.IsBounded C) :
    ∃ β : NNReal, 0 < β ∧ LipschitzOnWith β (fun x ↦ (f x : EReal).toReal) C := by
  by_cases hC_empty : C = ∅
  · -- The empty set is Lipschitz with any positive constant.
    refine ⟨1, by norm_num, ?_⟩
    simp [hC_empty, lipschitzOnWith_empty]
  · -- Closed bounded subsets are compact in finite-dimensional normed spaces.
    haveI : ProperSpace H := FiniteDimensional.proper ℝ H
    have hC_compact : IsCompact C := by
      simpa [hC_closed.closure_eq] using hC_bounded.isCompact_closure
    have hlocC :
        LocallyLipschitzOn C (fun x ↦ (f x : EReal).toReal) := by
      -- Build the local Lipschitz structure pointwise from the relative-interior hypothesis.
      intro x hx
      exact exists_local_lipschitzWithinAt_on_C_of_mem_relativeInterior f hconv hC_subset hx
    -- Compactness upgrades the local estimates to one global positive Lipschitz constant.
    exact exists_pos_lipschitzOnWith_of_isCompact_of_locallyLipschitzOn hC_compact hlocC

end ERealFunction
