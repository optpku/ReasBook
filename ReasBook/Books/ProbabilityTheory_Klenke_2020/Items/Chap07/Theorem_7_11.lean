/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Probability.Notation
import Mathlib.Analysis.Convex.Integral
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Corollary_7_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set EuclideanSpace
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin n)

/-- Helper for Theorem 7.11: an affine functional of an integrable random vector is integrable. -/
private lemma integrable_affine_comp_of_integrable {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → State} (hX : Integrable X P) (a : State →ᵃ[ℝ] ℝ) :
    Integrable (fun ω ↦ a (X ω)) P := by
  let L : State →L[ℝ] ℝ :=
    { toLinearMap := a.linear
      cont := a.linear.continuous_of_finiteDimensional }
  have hdecomp : (fun ω ↦ a (X ω)) = fun ω ↦ L (X ω) + a 0 := by
    funext ω
    have := congrArg (fun f : State → ℝ ↦ f (X ω)) a.decomp
    simpa [L] using this
  rw [hdecomp]
  exact (L.integrable_comp hX).add (integrable_const (a 0))

/-- Helper for Theorem 7.11: the expectation of an affine functional is the affine functional of
the expectation. -/
private lemma affine_expectation_eq_expectation_apply {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → State} (hX : Integrable X P) (a : State →ᵃ[ℝ] ℝ) :
    P[fun ω ↦ a (X ω)] = a (P[X]) := by
  let L : State →L[ℝ] ℝ :=
    { toLinearMap := a.linear
      cont := a.linear.continuous_of_finiteDimensional }
  have hdecomp : (fun ω ↦ a (X ω)) = fun ω ↦ L (X ω) + a 0 := by
    funext ω
    have := congrArg (fun f : State → ℝ ↦ f (X ω)) a.decomp
    simpa [L] using this
  rw [hdecomp, integral_add (L.integrable_comp hX) (integrable_const (a 0)),
    L.integral_comp_comm hX, integral_const, probReal_univ, one_smul]
  have := congrArg (fun f : State → ℝ ↦ f (P[X])) a.decomp
  simpa [L] using this.symm

/-- Helper for Theorem 7.11: an affine lower bound controls the negative part of `φ ∘ X`. -/
private lemma lintegral_neg_comp_lt_top_of_affine_lower_bound {P : Measure Ω}
    [IsProbabilityMeasure P] {G : Set State} {X : Ω → State} {φ : State → ℝ}
    {a : State →ᵃ[ℝ] ℝ} (hXG : ∀ᵐ ω ∂P, X ω ∈ G)
    (ha_lower : ∀ x ∈ G, a x ≤ φ x) (ha_int : Integrable (fun ω ↦ a (X ω)) P) :
    (∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) < ⊤ := by
  have hneg_int : Integrable (fun ω ↦ -a (X ω)) P := ha_int.neg
  have hbound : ∀ᵐ ω ∂P, ENNReal.ofReal (-φ (X ω)) ≤ ENNReal.ofReal (-a (X ω)) := by
    filter_upwards [hXG] with ω hω
    exact ENNReal.ofReal_le_ofReal (neg_le_neg (ha_lower _ hω))
  exact lt_of_le_of_lt (lintegral_mono_ae hbound) hneg_int.lintegral_lt_top

/-- Helper for Theorem 7.11: a touching affine minorant yields the extended Jensen lower bound. -/
private lemma ereal_jensen_ge_of_affine_lower_bound {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Set State} {X : Ω → State} {φ : State → ℝ} {a : State →ᵃ[ℝ] ℝ}
    (hXG : ∀ᵐ ω ∂P, X ω ∈ G) (ha_lower : ∀ x ∈ G, a x ≤ φ x)
    (ha_eq : a (P[X]) = φ (P[X])) (ha_int : Integrable (fun ω ↦ a (X ω)) P)
    (ha_expect : P[fun ω ↦ a (X ω)] = a (P[X])) :
    (((∫⁻ ω, ENNReal.ofReal (φ (X ω)) ∂P) : EReal) -
        ((∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) : EReal)) ≥
      (φ (P[X]) : EReal) := by
  have hlower : ∀ᵐ ω ∂P, a (X ω) ≤ φ (X ω) := by
    filter_upwards [hXG] with ω hω
    exact ha_lower _ hω
  have hpos : ∀ᵐ ω ∂P, ENNReal.ofReal (a (X ω)) ≤ ENNReal.ofReal (φ (X ω)) := by
    filter_upwards [hlower] with ω hω
    exact ENNReal.ofReal_le_ofReal hω
  have hneg : ∀ᵐ ω ∂P, ENNReal.ofReal (-φ (X ω)) ≤ ENNReal.ofReal (-a (X ω)) := by
    filter_upwards [hlower] with ω hω
    exact ENNReal.ofReal_le_ofReal (neg_le_neg hω)
  have hmain :
      (((∫⁻ ω, ENNReal.ofReal (a (X ω)) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-a (X ω)) ∂P) : EReal)) ≤
        (((∫⁻ ω, ENNReal.ofReal (φ (X ω)) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) : EReal)) := by
    exact EReal.sub_le_sub
      (by exact_mod_cast lintegral_mono_ae hpos)
      (by exact_mod_cast lintegral_mono_ae hneg)
  have hident :
      (((∫⁻ ω, ENNReal.ofReal (a (X ω)) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-a (X ω)) ∂P) : EReal)) =
        (∫ ω, a (X ω) ∂P : ℝ) := by
    have hpos_ne_top : (∫⁻ ω, ENNReal.ofReal (a (X ω)) ∂P) ≠ ⊤ := ha_int.lintegral_lt_top.ne
    have hneg_int : Integrable (fun ω ↦ -a (X ω)) P := ha_int.neg
    have hneg_ne_top : (∫⁻ ω, ENNReal.ofReal (-a (X ω)) ∂P) ≠ ⊤ := hneg_int.lintegral_lt_top.ne
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part ha_int]
    rw [← EReal.coe_ennreal_toReal hpos_ne_top, ← EReal.coe_ennreal_toReal hneg_ne_top]
    norm_num
  calc
    (φ (P[X]) : EReal) = (a (P[X]) : EReal) := by simp [ha_eq]
    _ = (∫ ω, a (X ω) ∂P : ℝ) := by simp [ha_expect]
    _ = (((∫⁻ ω, ENNReal.ofReal (a (X ω)) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-a (X ω)) ∂P) : EReal)) := hident.symm
    _ ≤ (((∫⁻ ω, ENNReal.ofReal (φ (X ω)) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) : EReal)) := hmain

/-- Helper for Theorem 7.11: an owner-style supporting affine map yields an ambient affine map. -/
private lemma affine_minorant_of_mem_supporting_affine_maps_on
    {G : Set State} {φ : State → ℝ} {g : G → ℝ}
    (hg : g ∈ supporting_affine_maps_on G φ) :
    ∃ a : State →ᵃ[ℝ] ℝ, (∀ x ∈ G, a x ≤ φ x) ∧ ∀ x : G, a x = g x := by
  rcases mem_supporting_affine_maps_on_iff.mp hg with ⟨hminor, l, c, rfl⟩
  let a : State →ᵃ[ℝ] ℝ := l.toAffineMap + AffineMap.const ℝ State c
  refine ⟨a, ?_, ?_⟩
  · intro x hx
    have := hminor ⟨x, hx⟩
    simpa [a, Pi.add_apply] using this
  · intro x
    simp [a, Pi.add_apply]

/-- Helper for Theorem 7.11: any ambient affine minorant restricts to the owner family
`supporting_affine_maps_on G φ`. -/
private lemma restrict_mem_supporting_affine_maps_on_of_affine_minorant
    {G : Set State} {φ : State → ℝ} {a : State →ᵃ[ℝ] ℝ}
    (ha_lower : ∀ x ∈ G, a x ≤ φ x) :
    Set.restrict G a ∈ supporting_affine_maps_on G φ := by
  -- Proof comment: package the affine map into the owner family's linear-plus-constant normal
  -- form using `AffineMap.decomp`.
  refine mem_supporting_affine_maps_on_iff.2 ?_
  refine ⟨?_, a.linear, a 0, ?_⟩
  · intro x
    exact ha_lower x x.2
  · ext x
    have hdecomp := congrArg (fun f : State → ℝ ↦ f x) a.decomp
    simpa [Pi.add_apply] using hdecomp

/-- Helper for Theorem 7.11: on the interior of a convex subset of a finite-dimensional real
normed space, strict-epigraph separation yields a touching affine minorant. -/
private lemma affine_minorant_touching_on_interior_of_finiteDimensional
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G : Set F} {φ : F → ℝ} {m : F} (hm : m ∈ interior G) (hφ : ConvexOn ℝ G φ) :
    ∃ a : F →ᵃ[ℝ] ℝ, (∀ x ∈ interior G, a x ≤ φ x) ∧ a m = φ m := by
  let S : Set (F × ℝ) := {p | p.1 ∈ interior G ∧ φ p.1 < p.2}
  have hcont : ContinuousOn φ (interior G) := hφ.continuousOn_interior
  have hS_open_aux :
      IsOpen ((interior G ×ˢ (Set.univ : Set ℝ)) ∩
        (fun p : F × ℝ ↦ φ p.1 - p.2) ⁻¹' Set.Iio 0) := by
    -- Proof comment: continuity of `(x, t) ↦ φ x - t` on the product neighborhood makes the
    -- strict epigraph open.
    have hψ : ContinuousOn (fun p : F × ℝ ↦ φ p.1 - p.2)
        (interior G ×ˢ (Set.univ : Set ℝ)) := by
      intro p hp
      have hφp : ContinuousAt φ p.1 :=
        (hcont p.1 hp.1).continuousAt (isOpen_interior.mem_nhds hp.1)
      exact ((hφp.comp continuousAt_fst).sub continuousAt_snd).continuousWithinAt
    simpa using hψ.isOpen_inter_preimage (isOpen_interior.prod isOpen_univ) isOpen_Iio
  have hS_open : IsOpen S := by
    have hEq : S = ((interior G ×ˢ (Set.univ : Set ℝ)) ∩
        (fun p : F × ℝ ↦ φ p.1 - p.2) ⁻¹' Set.Iio 0) := by
      ext p
      simp [S, sub_lt_iff_lt_add']
    rw [hEq]
    exact hS_open_aux
  have hS_conv : Convex ℝ S := by
    simpa [S] using (hφ.subset interior_subset hφ.1.interior).convex_strict_epigraph
  have hq_not_mem : (m, φ m) ∉ S := by
    simp [S, hm]
  obtain ⟨f, hf⟩ := geometric_hahn_banach_point_open hS_conv hS_open hq_not_mem
  let c : ℝ := f (0, (1 : ℝ))
  let L : F →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ f (x, 0)
      map_add' := by
        intro x y
        simpa using f.map_add (x, (0 : ℝ)) (y, 0)
      map_smul' := by
        intro t x
        simpa using f.map_smul t (x, (0 : ℝ)) }
  have hsplit : ∀ x t, f (x, t) = L x + c * t := by
    intro x t
    rw [show (x, t) = (x, (0 : ℝ)) + (0, t) by simp, map_add]
    have hzero : f (0, t) = c * t := by
      calc
        f (0, t) = f (t • (0, (1 : ℝ))) := by simp
        _ = t * f (0, (1 : ℝ)) := by
          rw [map_smul]
          simp [smul_eq_mul]
        _ = c * t := by ring
    simp [L, hzero, c]
  have hc_pos : 0 < c := by
    -- Proof comment: evaluating the separator on the vertical ray above `(m, φ m)` forces the
    -- coefficient of the `ℝ`-coordinate to be positive.
    have hmem : (m, φ m + 1) ∈ S := by
      simp [S, hm, zero_lt_one]
    have hlt := hf (m, φ m + 1) hmem
    rw [hsplit m (φ m), hsplit m (φ m + 1)] at hlt
    linarith
  let aFun : F → ℝ := fun x ↦ φ m + (L m - L x) / c
  let aLinear : F →ₗ[ℝ] ℝ := (-(1 / c : ℝ)) • L
  let a : F →ᵃ[ℝ] ℝ :=
    { toFun := aFun
      linear := aLinear
      map_vadd' := by
        intro p v
        dsimp [aFun, aLinear]
        rw [map_add]
        field_simp [hc_pos.ne']
        ring }
  have ha_apply : ∀ x, a x = aFun x := by
    intro x
    rfl
  have ha_eq : a m = φ m := by
    rw [ha_apply]
    dsimp [aFun]
    ring_nf
  have ha_lower_interior : ∀ x ∈ interior G, a x ≤ φ x := by
    intro x hx
    by_contra hxa
    have hlt : φ x < aFun x := by
      rw [← ha_apply x]
      exact lt_of_not_ge hxa
    let ε : ℝ := (aFun x - φ x) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hmem : (x, φ x + ε) ∈ S := by
      refine ⟨hx, ?_⟩
      linarith
    have hsep : L m + c * φ m < L x + c * φ x + c * ε := by
      have hraw := hf (x, φ x + ε) hmem
      rw [hsplit m (φ m), hsplit x (φ x + ε)] at hraw
      linarith
    have hlt' : L x + c * φ x < L m + c * φ m := by
      have hmult := mul_lt_mul_of_pos_right hlt hc_pos
      dsimp [aFun] at hmult
      field_simp [hc_pos.ne'] at hmult
      linarith
    have hmid : L x + c * φ x + c * ε = (L m + c * φ m + (L x + c * φ x)) / 2 := by
      dsimp [ε, aFun]
      field_simp [hc_pos.ne']
      ring
    nlinarith [hlt', hsep, hmid]
  exact ⟨a, ha_lower_interior, ha_eq⟩

/-- Helper for Theorem 7.11: on `interior G`, strict-epigraph separation yields an affine
minorant touching `φ` at `m`. -/
private lemma affine_minorant_touching_on_interior {G : Set State} {φ : State → ℝ} {m : State}
    (hm : m ∈ interior G) (hφ : ConvexOn ℝ G φ) :
    ∃ a : State →ᵃ[ℝ] ℝ, (∀ x ∈ interior G, a x ≤ φ x) ∧ a m = φ m := by
  -- Proof comment: this is the Euclidean-space specialization of the generic finite-dimensional
  -- interior supporting-minorant construction.
  simpa using affine_minorant_touching_on_interior_of_finiteDimensional hm hφ

/-- Helper for Theorem 7.11: in a finite-dimensional real normed space, an affine minorant that
touches a convex function at an interior point automatically extends from `interior G` to all of
`G` by convexity along the segment to the touching point. -/
private lemma affine_minorant_touching_of_mem_interior_of_finiteDimensional
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G : Set F} {φ : F → ℝ} {m : F} (hm : m ∈ interior G) (hφ : ConvexOn ℝ G φ) :
    ∃ a : F →ᵃ[ℝ] ℝ, (∀ x ∈ G, a x ≤ φ x) ∧ a m = φ m := by
  obtain ⟨a, ha_lower_interior, ha_eq⟩ :=
    affine_minorant_touching_on_interior_of_finiteDimensional hm hφ
  have ha_lower : ∀ x ∈ G, a x ≤ φ x := by
    intro x hx
    let y : F := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • m
    -- Proof comment: midpointing with the interior touching point moves any `x ∈ G` into
    -- `interior G`, where the local affine lower bound is already available.
    have hy : y ∈ interior G := by
      exact hφ.1.combo_self_interior_mem_interior hx hm
        (by positivity) (by positivity) (by norm_num)
    have hay : a y ≤ φ y := ha_lower_interior y hy
    have hφy : φ y ≤ (1 / 2 : ℝ) * φ x + (1 / 2 : ℝ) * φ m := by
      have hconv := hφ.2 hx (interior_subset hm)
        (by positivity) (by positivity) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
      simpa [y, smul_eq_mul, add_comm, add_left_comm, add_assoc] using hconv
    have hay_eq : a y = (1 / 2 : ℝ) * a x + (1 / 2 : ℝ) * a m := by
      have hy_line : y = AffineMap.lineMap x m (1 / 2 : ℝ) := by
        rw [AffineMap.lineMap_apply_module]
        dsimp [y]
        ring_nf
      rw [hy_line]
      calc
        a (AffineMap.lineMap x m (1 / 2 : ℝ)) = AffineMap.lineMap (a x) (a m) (1 / 2 : ℝ) := by
          exact a.apply_lineMap x m (1 / 2 : ℝ)
        _ = (1 - (1 / 2 : ℝ)) * a x + (1 / 2 : ℝ) * a m := by
          rw [AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]
        _ = (1 / 2 : ℝ) * a x + (1 / 2 : ℝ) * a m := by ring
    rw [ha_eq] at hay_eq
    linarith
  exact ⟨a, ha_lower, ha_eq⟩

/-- Helper for Theorem 7.11: if the barycenter lies in the interior of a convex domain, then the
supporting affine map on `interior G` extends canonically to a supporting affine map on `G`. -/
private lemma supporting_affine_minorant_of_mem_interior {G : Set State} {φ : State → ℝ}
    {m : State} (hm : m ∈ interior G) (hφ : ConvexOn ℝ G φ) :
    ∃ g ∈ supporting_affine_maps_on G φ, g ⟨m, interior_subset hm⟩ = φ m := by
  obtain ⟨a, ha_lower_interior, ha_eq⟩ := affine_minorant_touching_on_interior hm hφ
  have ha_lower : ∀ x ∈ G, a x ≤ φ x := by
    intro x hx
    let y : State := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • m
    have hy : y ∈ interior G := by
      exact hφ.1.combo_self_interior_mem_interior hx hm
        (by positivity) (by positivity) (by norm_num)
    have hay : a y ≤ φ y := ha_lower_interior y hy
    have hφy : φ y ≤ (1 / 2 : ℝ) * φ x + (1 / 2 : ℝ) * φ m := by
      have hconv := hφ.2 hx (interior_subset hm)
        (by positivity) (by positivity) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
      simpa [y, smul_eq_mul, add_comm, add_left_comm, add_assoc] using hconv
    have hay_eq : a y = (1 / 2 : ℝ) * a x + (1 / 2 : ℝ) * a m := by
      have hy_line : y = AffineMap.lineMap x m (1 / 2 : ℝ) := by
        rw [AffineMap.lineMap_apply_module]
        dsimp [y]
        ring_nf
      rw [hy_line]
      calc
        a (AffineMap.lineMap x m (1 / 2 : ℝ)) = AffineMap.lineMap (a x) (a m) (1 / 2 : ℝ) := by
          exact a.apply_lineMap x m (1 / 2 : ℝ)
        _ = (1 - (1 / 2 : ℝ)) * a x + (1 / 2 : ℝ) * a m := by
          rw [AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]
        _ = (1 / 2 : ℝ) * a x + (1 / 2 : ℝ) * a m := by ring
    rw [ha_eq] at hay_eq
    linarith
  refine ⟨Set.restrict G a, ?_, ?_⟩
  · exact restrict_mem_supporting_affine_maps_on_of_affine_minorant ha_lower
  · simpa using ha_eq

/-- Helper for Theorem 7.11: an affine map on a nonempty affine subspace extends to the ambient
space by projecting its linear part onto the direction along a chosen linear complement. -/
private lemma extend_affine_map_from_affineSubspace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (s : AffineSubspace ℝ F) [Nonempty s] (b : s →ᵃ[ℝ] ℝ) :
    ∃ a : F →ᵃ[ℝ] ℝ, ∀ x : s, a x = b x := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl s.direction
  let p0 : s := Classical.arbitrary s
  let L : F →ₗ[ℝ] ℝ := b.linear.comp (s.direction.linearProjOfIsCompl q hq)
  let c : ℝ := b p0 - L p0
  let a : F →ᵃ[ℝ] ℝ :=
    { toFun := fun x ↦ L x + c
      linear := L
      map_vadd' := by
        intro p v
        simp [c, map_add, add_assoc, add_left_comm, add_comm] }
  refine ⟨a, ?_⟩
  intro x
  have hproj_x : s.direction.linearProjOfIsCompl q hq (x -ᵥ p0) = x -ᵥ p0 := by
    exact Submodule.linearProjOfIsCompl_apply_left hq (x -ᵥ p0)
  have hproj_sub :
      (s.direction.linearProjOfIsCompl q hq x : F) -
          s.direction.linearProjOfIsCompl q hq p0 =
        (x : F) - p0 := by
    calc
      (s.direction.linearProjOfIsCompl q hq x : F) -
          s.direction.linearProjOfIsCompl q hq p0 =
        ↑((s.direction.linearProjOfIsCompl q hq) ((x : F) - p0)) := by
          simp [LinearMap.map_sub]
      _ = ↑(x -ᵥ p0) := congrArg Subtype.val hproj_x
      _ = (x : F) - p0 := rfl
  have hproj_vsub :
      s.direction.linearProjOfIsCompl q hq x -
          s.direction.linearProjOfIsCompl q hq p0 =
        x -ᵥ p0 := by
    exact Subtype.ext hproj_sub
  change L x + c = b x
  dsimp [c]
  have hb : b x = b.linear (x -ᵥ p0) + b p0 := by
    simpa using b.map_vadd' p0 (x -ᵥ p0)
  have hlin :
      b.linear (s.direction.linearProjOfIsCompl q hq x) -
          b.linear (s.direction.linearProjOfIsCompl q hq p0) =
        b.linear (x -ᵥ p0) := by
    rw [← b.linear.map_sub]
    simpa using congrArg b.linear hproj_vsub
  have hLx : L x = b.linear (s.direction.linearProjOfIsCompl q hq x) := by
    rfl
  have hLp0 : L p0 = b.linear (s.direction.linearProjOfIsCompl q hq p0) := by
    rfl
  rw [hLx, hLp0]
  linarith [hb, hlin]

/-- Helper for Theorem 7.11: if the contact point lies in the intrinsic interior of a convex
carrier, then one can pass to the affine-span subtype, support there, and extend the affine map
back to the ambient space. -/
private lemma supporting_affine_minorant_of_mem_intrinsicInterior {G : Set State}
    {φ : State → ℝ} {m : State} (hm : m ∈ intrinsicInterior ℝ G) (hφ : ConvexOn ℝ G φ) :
    ∃ g ∈ supporting_affine_maps_on G φ, g ⟨m, intrinsicInterior_subset hm⟩ = φ m := by
  let Carrier : Set (_root_.affineSpan ℝ G) := ((↑) ⁻¹' G : Set (_root_.affineSpan ℝ G))
  obtain ⟨mₛ, hmₛ, hm_coe⟩ :
      ∃ y : _root_.affineSpan ℝ G, y ∈ interior Carrier ∧ (y : State) = m := by
    simpa [Carrier] using hm
  letI : Nonempty (_root_.affineSpan ℝ G) := ⟨mₛ⟩
  let e := AffineIsometryEquiv.constVSub ℝ mₛ
  let γ : (_root_.affineSpan ℝ G).direction →ᵃ[ℝ] State :=
    (_root_.affineSpan ℝ G).subtype.comp e.symm.toAffineEquiv.toAffineMap
  let H : Set (_root_.affineSpan ℝ G).direction := γ ⁻¹' G
  have hH : H = e '' Carrier := by
    ext v
    constructor
    · intro hv
      refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
      simpa [H, Carrier, γ]
    · rintro ⟨x, hx, rfl⟩
      simpa [H, Carrier, γ]
  have hzero : (0 : (_root_.affineSpan ℝ G).direction) ∈ interior H := by
    rw [hH]
    have hm_img : e mₛ ∈ e '' interior Carrier := ⟨mₛ, hmₛ, rfl⟩
    have himage : e '' interior Carrier = interior (e '' Carrier) :=
      e.toHomeomorph.image_interior Carrier
    have hm_int : e mₛ ∈ interior (e '' Carrier) := by
      exact himage ▸ hm_img
    simpa [e] using hm_int
  have hψ : ConvexOn ℝ H (fun v : (_root_.affineSpan ℝ G).direction ↦ φ (γ v)) := by
    -- Proof comment: after translating the affine-span carrier to the direction space, convexity
    -- becomes an ordinary `ConvexOn` statement on the vector-space carrier `H`.
    simpa [H, γ] using hφ.comp_affineMap γ
  obtain ⟨b, hb_lower, hb_eq⟩ :=
    affine_minorant_touching_of_mem_interior_of_finiteDimensional hzero hψ
  let c : (_root_.affineSpan ℝ G) →ᵃ[ℝ] ℝ := b.comp e.toAffineEquiv.toAffineMap
  have hc_lower : ∀ x : _root_.affineSpan ℝ G, x ∈ Carrier → c x ≤ φ x := by
    intro x hx
    have hex : e x ∈ H := by
      simpa [H, Carrier, γ] using hx
    calc
      c x = b (e x) := by rfl
      _ ≤ φ (γ (e x)) := hb_lower (e x) hex
      _ = φ x := by simp [γ, e]
  have hc_eq : c mₛ = φ m := by
    -- Proof comment: the translated affine minorant touches at `0`, which pulls back to the
    -- original point `m`.
    calc
      c mₛ = b 0 := by simp [c, e]
      _ = φ (γ 0) := hb_eq
      _ = φ ↑mₛ := by simp [γ, e]
      _ = φ m := by simpa using congrArg φ hm_coe
  obtain ⟨a, ha_ext⟩ := extend_affine_map_from_affineSubspace (_root_.affineSpan ℝ G) c
  have ha_lower : ∀ x ∈ G, a x ≤ φ x := by
    intro x hx
    let xₛ : _root_.affineSpan ℝ G := ⟨x, subset_affineSpan ℝ G hx⟩
    have hxₛ : xₛ ∈ Carrier := by
      simpa [Carrier, xₛ]
    -- Proof comment: every ambient point of `G` is represented by a point of the affine span, so
    -- the affine lower bound descends through the extension map.
    calc
      a x = c xₛ := by simpa [xₛ] using ha_ext xₛ
      _ ≤ φ xₛ := hc_lower xₛ hxₛ
      _ = φ x := rfl
  have ha_eq : a m = φ m := by
    simpa [hm_coe] using (ha_ext mₛ).trans hc_eq
  refine ⟨Set.restrict G a, ?_, ?_⟩
  · exact restrict_mem_supporting_affine_maps_on_of_affine_minorant ha_lower
  · simpa using ha_eq

/-- Helper for Theorem 7.11: if the expectation already lies in the ambient interior of `G`, then
the supporting affine map on `G` can be unpacked into an ambient affine minorant. -/
private lemma affine_minorant_touching_expectation_of_mem_interior
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Set State} {X : Ω → State}
    {φ : State → ℝ} (hm : P[X] ∈ interior G) (hφ : ConvexOn ℝ G φ) :
    ∃ a : State →ᵃ[ℝ] ℝ, (∀ x ∈ G, a x ≤ φ x) ∧ a (P[X]) = φ (P[X]) := by
  obtain ⟨g, hg, htouch⟩ := supporting_affine_minorant_of_mem_interior hm hφ
  obtain ⟨a, ha_lower, ha_eq⟩ := affine_minorant_of_mem_supporting_affine_maps_on hg
  refine ⟨a, ha_lower, ?_⟩
  calc
    a (P[X]) = g ⟨P[X], interior_subset hm⟩ := ha_eq ⟨P[X], interior_subset hm⟩
    _ = φ (P[X]) := htouch

/-- Helper for Theorem 7.11: if the expectation lies in the intrinsic interior of `G`, then the
supporting affine map on `G` can still be unpacked into an ambient affine minorant. -/
private lemma affine_minorant_touching_expectation_of_mem_intrinsicInterior
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Set State} {X : Ω → State}
    {φ : State → ℝ} (hm : P[X] ∈ intrinsicInterior ℝ G) (hφ : ConvexOn ℝ G φ) :
    ∃ a : State →ᵃ[ℝ] ℝ, (∀ x ∈ G, a x ≤ φ x) ∧ a (P[X]) = φ (P[X]) := by
  obtain ⟨g, hg, htouch⟩ := supporting_affine_minorant_of_mem_intrinsicInterior hm hφ
  obtain ⟨a, ha_lower, ha_eq⟩ := affine_minorant_of_mem_supporting_affine_maps_on hg
  refine ⟨a, ha_lower, ?_⟩
  calc
    a (P[X]) = g ⟨P[X], intrinsicInterior_subset hm⟩ := ha_eq ⟨P[X], intrinsicInterior_subset hm⟩
    _ = φ (P[X]) := htouch

/-- Helper for Theorem 7.11: the expectation of an integrable random vector taking values almost
surely in a convex set lies in the closure of that convex set. -/
private lemma expectation_mem_closure_of_ae_mem_convex
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Set State} {X : Ω → State}
    (hX : Integrable X P) (hXG : ∀ᵐ ω ∂P, X ω ∈ G) (hG : Convex ℝ G) :
    P[X] ∈ closure G := by
  simpa using
    hG.closure.integral_mem isClosed_closure
      (hXG.mono fun ω hω ↦ subset_closure hω) hX

/-- Helper for Theorem 7.11: once the barycenter is known to lie in the closure of a convex set,
failing to lie in the intrinsic interior means it lies in the intrinsic frontier. -/
private lemma expectation_mem_intrinsicFrontier_of_not_mem_intrinsicInterior
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Set State} {X : Ω → State}
    (hX : Integrable X P) (hXG : ∀ᵐ ω ∂P, X ω ∈ G) (hG : Convex ℝ G)
    (hm : P[X] ∉ intrinsicInterior ℝ G) :
    P[X] ∈ intrinsicFrontier ℝ G := by
  have hclosure : P[X] ∈ closure G := expectation_mem_closure_of_ae_mem_convex hX hXG hG
  rw [← closure_diff_intrinsicInterior G]
  exact ⟨hclosure, hm⟩

/-- Helper for Theorem 7.11: a nonempty convex carrier has a genuine interior point once it is
viewed inside its affine span. -/
private lemma exists_carrierInteriorPoint_of_nonemptyConvex {G : Set State}
    (hG : Convex ℝ G) (hGne : G.Nonempty) :
    ∃ y : _root_.affineSpan ℝ G, y ∈ interior (((↑) : _root_.affineSpan ℝ G → State) ⁻¹' G) := by
  -- Proof comment: intrinsic interior is defined as ordinary interior in the affine-span carrier.
  obtain ⟨x, hx⟩ := hGne.intrinsicInterior hG
  rcases mem_intrinsicInterior.mp hx with ⟨y, hy, rfl⟩
  exact ⟨y, hy⟩

/-- Helper for Theorem 7.11: an intrinsic-frontier point admits a separating ambient affine
functional whose zero level supports `G` at that point and is nontrivial on `G`. -/
private lemma exists_affineSeparator_of_mem_intrinsicFrontier {G : Set State} {m : State}
    (hG : Convex ℝ G) (hm : m ∈ intrinsicFrontier ℝ G) :
    ∃ a : State →ᵃ[ℝ] ℝ, (∀ x ∈ G, a m ≤ a x) ∧ ∃ y ∈ G, a m < a y := by
  let Carrier : Set (_root_.affineSpan ℝ G) := ((↑) ⁻¹' G : Set (_root_.affineSpan ℝ G))
  obtain ⟨mₛ, hmₛ, hm_coe⟩ :
      ∃ y : _root_.affineSpan ℝ G, y ∈ frontier Carrier ∧ (y : State) = m := by
    simpa [Carrier] using hm
  have hGne : G.Nonempty := by
    -- Proof comment: an intrinsic-frontier point belongs to the intrinsic closure, so the carrier
    -- cannot be empty.
    have hclosure : m ∈ intrinsicClosure ℝ G :=
      intrinsicFrontier_subset_intrinsicClosure hm
    exact (show (intrinsicClosure ℝ G).Nonempty from ⟨m, hclosure⟩).ofIntrinsicClosure
  obtain ⟨uₛ, huₛ⟩ := exists_carrierInteriorPoint_of_nonemptyConvex hG hGne
  letI : Nonempty (_root_.affineSpan ℝ G) := ⟨mₛ⟩
  let e := AffineIsometryEquiv.constVSub ℝ mₛ
  let γ : (_root_.affineSpan ℝ G).direction →ᵃ[ℝ] State :=
    (_root_.affineSpan ℝ G).subtype.comp e.symm.toAffineEquiv.toAffineMap
  let H : Set (_root_.affineSpan ℝ G).direction := γ ⁻¹' G
  have hH : H = e '' Carrier := by
    ext v
    constructor
    · intro hv
      refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
      simpa [H, Carrier, γ]
    · rintro ⟨x, hx, rfl⟩
      simpa [H, Carrier, γ]
  have hH_conv : Convex ℝ H := by
    -- Proof comment: after translating the affine-span carrier so that `m` becomes `0`, the
    -- carrier becomes an ordinary convex set in the direction space.
    simpa [H, γ] using hG.affine_preimage γ
  have hzero_frontier : (0 : (_root_.affineSpan ℝ G).direction) ∈ frontier H := by
    rw [hH]
    have hm_img : e mₛ ∈ e '' frontier Carrier := ⟨mₛ, hmₛ, rfl⟩
    have hm_front : e mₛ ∈ frontier (e '' Carrier) := by
      exact (e.toHomeomorph.image_frontier Carrier) ▸ hm_img
    simpa [e] using hm_front
  have hzero_not_mem_interior : (0 : (_root_.affineSpan ℝ G).direction) ∉ interior H := by
    exact fun hzero_int ↦ hzero_frontier.2 hzero_int
  have hH_int : (interior H).Nonempty := by
    rw [hH]
    have hu_img : e uₛ ∈ e '' interior Carrier := ⟨uₛ, huₛ, rfl⟩
    have hu_int : e uₛ ∈ interior (e '' Carrier) := by
      exact (e.toHomeomorph.image_interior Carrier) ▸ hu_img
    exact ⟨e uₛ, hu_int⟩
  obtain ⟨f, hf_ne, hf_le⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hH_conv hzero_not_mem_interior hH_int
  have hCarrier_top : affineSpan ℝ Carrier = ⊤ := by
    letI : Nonempty G := hGne.to_subtype
    simpa [Carrier] using affineSpan_coe_preimage_eq_top (k := ℝ) (A := G)
  have hH_top : affineSpan ℝ H = ⊤ := by
    rw [hH]
    exact AffineMap.span_eq_top_of_surjective
      (f := e.toAffineEquiv.toAffineMap) e.toAffineEquiv.surjective hCarrier_top
  have hstrict_on_H : ∃ z ∈ H, f z < 0 := by
    by_contra hno
    have hEqZero : Set.EqOn f.toAffineMap (AffineMap.const ℝ _ (0 : ℝ)) H := by
      intro z hz
      have hz_nonneg : 0 ≤ f z := by
        exact not_lt.mp (fun hzlt ↦ hno ⟨z, hz, hzlt⟩)
      have hz_nonpos : f z ≤ 0 := by
        simpa using hf_le z hz
      have hz_zero : f z = 0 := le_antisymm hz_nonpos hz_nonneg
      simpa using hz_zero
    have hf_zero_aff : f.toAffineMap = AffineMap.const ℝ _ (0 : ℝ) :=
      AffineMap.ext_on hH_top hEqZero
    have hf_zero : f = 0 := by
      ext z
      have hz := congrArg (fun g : (_root_.affineSpan ℝ G).direction →ᵃ[ℝ] ℝ ↦ g z) hf_zero_aff
      simpa using hz
    exact hf_ne hf_zero
  obtain ⟨z, hzH, hzlt⟩ := hstrict_on_H
  let c : (_root_.affineSpan ℝ G) →ᵃ[ℝ] ℝ :=
    ((-f).toAffineMap).comp e.toAffineEquiv.toAffineMap
  obtain ⟨a, ha_ext⟩ := extend_affine_map_from_affineSubspace (_root_.affineSpan ℝ G) c
  have ha_ge : ∀ x ∈ G, a m ≤ a x := by
    intro x hx
    let xₛ : _root_.affineSpan ℝ G := ⟨x, subset_affineSpan ℝ G hx⟩
    have hxH : e xₛ ∈ H := by
      simpa [H, Carrier, γ] using hx
    have hx_nonpos : f (e xₛ) ≤ 0 := by
      simpa using hf_le (e xₛ) hxH
    -- Proof comment: the separator is normalized so that `a m = 0`, hence `a` is nonnegative on
    -- all of `G`.
    calc
      a m = c mₛ := by simpa [hm_coe] using ha_ext mₛ
      _ = 0 := by simp [c, e]
      _ ≤ c xₛ := by
        change 0 ≤ -f (e xₛ)
        linarith
      _ = a x := by simpa [xₛ] using (ha_ext xₛ).symm
  have ha_strict : ∃ y ∈ G, a m < a y := by
    rw [hH] at hzH
    rcases hzH with ⟨yₛ, hyₛ, rfl⟩
    refine ⟨(yₛ : State), ?_, ?_⟩
    · simpa [Carrier] using hyₛ
    · -- Proof comment: the nonzero separator is not constant on the carrier, giving a strict
      -- supporting witness after extending back to the ambient space.
      calc
        a m = c mₛ := by simpa [hm_coe] using ha_ext mₛ
        _ = 0 := by simp [c, e]
        _ < c yₛ := by
          change 0 < -f (e yₛ)
          linarith
        _ = a yₛ := by simpa using (ha_ext yₛ).symm
  exact ⟨a, ha_ge, ha_strict⟩

/-- Helper for Theorem 7.11: if an affine functional is nonnegative on the essential range of
`X` and has expectation equal to its value at `m`, then `X` lies almost surely in the exposed
slice where the affine gap vanishes. -/
private lemma ae_mem_exposedAffineSlice_of_affine_gap_zero
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Set State} {X : Ω → State}
    {m : State} {a : State →ᵃ[ℝ] ℝ} (hX : Integrable X P) (hXG : ∀ᵐ ω ∂P, X ω ∈ G)
    (ha_ge : ∀ x ∈ G, a m ≤ a x) (ha_expect : P[fun ω ↦ a (X ω)] = a m) :
    ∀ᵐ ω ∂P, X ω ∈ {x | x ∈ G ∧ a x = a m} := by
  let Z : Ω → ℝ := fun ω ↦ a (X ω) - a m
  have hZ_int : Integrable Z P := by
    -- Proof comment: the affine gap is the difference of an integrable affine image and a
    -- constant function.
    dsimp [Z]
    exact (integrable_affine_comp_of_integrable hX a).sub (integrable_const (a m))
  have hZ_nonneg : 0 ≤ᵐ[ P] Z := by
    -- Proof comment: the exposed-slice hypothesis makes the affine gap pointwise nonnegative on
    -- the essential range of `X`.
    filter_upwards [hXG] with ω hω
    dsimp [Z]
    linarith [ha_ge (X ω) hω]
  have hZ_integral : ∫ ω, Z ω ∂P = 0 := by
    -- Proof comment: subtract the constant `a m` from the affine expectation identity.
    dsimp [Z]
    rw [integral_sub (integrable_affine_comp_of_integrable hX a) (integrable_const (a m))]
    rw [ha_expect, integral_const, probReal_univ, one_smul, sub_self]
  have hZ_zero : Z =ᵐ[ P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hZ_nonneg hZ_int).mp hZ_integral
  filter_upwards [hXG, hZ_zero] with ω hω hω_zero
  refine ⟨hω, ?_⟩
  dsimp [Z] at hω_zero
  linarith

/-- Helper for Theorem 7.11: once the exposed slice contains at least one contact point and one
strict witness, its affine span is strictly smaller than the affine span of the ambient carrier. -/
private lemma zeroSlice_finrankDrop_of_contact_strict_separator
    {G : Set State} {m : State} {a : State →ᵃ[ℝ] ℝ}
    (hcontact : ∃ x ∈ G, a x = a m) (hstrict : ∃ y ∈ G, a m < a y) :
    let K := {x | x ∈ G ∧ a x = a m}
    Module.finrank ℝ ↥(affineSpan ℝ K).direction <
      Module.finrank ℝ ↥(affineSpan ℝ G).direction := by
  classical
  let K : Set State := {x | x ∈ G ∧ a x = a m}
  have hKsub : K ⊆ G := by
    intro x hx
    exact hx.1
  have hKle : affineSpan ℝ K ≤ affineSpan ℝ G := affineSpan_mono (k := ℝ) hKsub
  let level : AffineSubspace ℝ State := (affineSpan ℝ ({a m} : Set ℝ)).comap a
  have hKlevel : affineSpan ℝ K ≤ level := by
    rw [affineSpan_le]
    intro x hx
    change a x ∈ affineSpan ℝ ({a m} : Set ℝ)
    exact mem_affineSpan ℝ (by simpa using hx.2)
  have hlt : affineSpan ℝ K < affineSpan ℝ G := by
    refine lt_of_le_of_ne hKle ?_
    intro hEq
    rcases hstrict with ⟨y, hyG, hylt⟩
    have hy_span : y ∈ affineSpan ℝ G := subset_affineSpan ℝ G hyG
    have hy_level : y ∈ level := by
      have : y ∈ affineSpan ℝ K := by simpa [hEq] using hy_span
      exact hKlevel this
    rw [AffineSubspace.mem_comap, AffineSubspace.mem_affineSpan_singleton] at hy_level
    exact (ne_of_gt hylt) hy_level
  rcases hcontact with ⟨x, hxG, hxEq⟩
  have hKne : K.Nonempty := ⟨x, ⟨hxG, hxEq⟩⟩
  have hSpanKne : ((affineSpan ℝ K : AffineSubspace ℝ State) : Set State).Nonempty :=
    hKne.mono (subset_affineSpan ℝ K)
  have hdir_lt :=
    AffineSubspace.direction_lt_of_nonempty (k := ℝ) hlt hSpanKne
  simpa [K] using Submodule.finrank_lt_finrank_of_lt hdir_lt

/-- Helper for Theorem 7.11: the affine-span direction finrank used to induct on convex carriers. -/
private noncomputable abbrev carrierRank (G : Set State) : ℕ :=
  Module.finrank ℝ ↥(affineSpan ℝ G).direction

/-- Helper for Theorem 7.11: a rank bound lets one prove the touching-affine-minorant carrier
statement by strong induction on the affine-span direction finrank. -/
private lemma affine_minorant_touching_expectation_on_carrier_of_finrank_le
    {P : Measure Ω} [IsProbabilityMeasure P] (d : ℕ) {G : Set State} {X : Ω → State}
    {φ : State → ℝ} (hRank : carrierRank G ≤ d) (hX : Integrable X P)
    (hXG : ∀ᵐ ω ∂P, X ω ∈ G) (hφ : ConvexOn ℝ G φ) :
    ∃ K : Set State, K ⊆ G ∧ Convex ℝ K ∧
      (∀ᵐ ω ∂P, X ω ∈ K) ∧
      ∃ a : State →ᵃ[ℝ] ℝ, (∀ x ∈ K, a x ≤ φ x) ∧ a (P[X]) = φ (P[X]) := by
  let Q : ℕ → Prop := fun d =>
    ∀ (G : Set State) (X : Ω → State) (φ : State → ℝ),
      carrierRank G ≤ d →
        Integrable X P →
          (∀ᵐ ω ∂P, X ω ∈ G) →
            ConvexOn ℝ G φ →
              ∃ K : Set State, K ⊆ G ∧ Convex ℝ K ∧
                (∀ᵐ ω ∂P, X ω ∈ K) ∧
                ∃ a : State →ᵃ[ℝ] ℝ, (∀ x ∈ K, a x ≤ φ x) ∧ a (P[X]) = φ (P[X])
  have hmain : ∀ d : ℕ, Q d := by
    intro d
    refine Nat.strong_induction_on d ?_
    intro d ih G X φ hRank hX hXG hφ
    by_cases hm : P[X] ∈ intrinsicInterior ℝ G
    · -- Proof comment: once the barycenter is already in the intrinsic interior, the previously
      -- constructed supporting affine minorant works on the whole carrier.
      obtain ⟨a, ha_lower, ha_eq⟩ :=
        affine_minorant_touching_expectation_of_mem_intrinsicInterior hm hφ
      exact ⟨G, subset_rfl, hφ.1, hXG, a, ha_lower, ha_eq⟩
    · have hm_frontier : P[X] ∈ intrinsicFrontier ℝ G :=
        expectation_mem_intrinsicFrontier_of_not_mem_intrinsicInterior hX hXG hφ.1 hm
      obtain ⟨a, ha_ge, hstrict⟩ :=
        exists_affineSeparator_of_mem_intrinsicFrontier hφ.1 hm_frontier
      let K : Set State := {x | x ∈ G ∧ a x = a (P[X])}
      have ha_expect : P[fun ω ↦ a (X ω)] = a (P[X]) :=
        affine_expectation_eq_expectation_apply hX a
      have hXK : ∀ᵐ ω ∂P, X ω ∈ K := by
        -- Proof comment: the affine gap is nonnegative on `G` and has zero expectation, so the
        -- random vector collapses almost surely onto the exposed slice.
        simpa [K] using ae_mem_exposedAffineSlice_of_affine_gap_zero hX hXG ha_ge ha_expect
      have hKsub : K ⊆ G := by
        intro x hx
        exact hx.1
      have hKconv : Convex ℝ K := by
        have hlevel : Convex ℝ (a ⁻¹' ({a (P[X])} : Set ℝ)) :=
          (convex_singleton (a (P[X]))).affine_preimage a
        simpa [K, Set.preimage] using hφ.1.inter hlevel
      have hKcontact : ∃ x ∈ G, a x = a (P[X]) := by
        rcases hXK.exists with ⟨ω, hω⟩
        exact ⟨X ω, hω.1, hω.2⟩
      have hKdrop : carrierRank K < carrierRank G := by
        -- Proof comment: the exposed slice is a proper affine section because the separator is
        -- strict at some point of `G`.
        simpa [carrierRank, K] using
          zeroSlice_finrankDrop_of_contact_strict_separator
            (m := P[X]) (a := a) hKcontact hstrict
      have hφK : ConvexOn ℝ K φ := by
        -- Proof comment: the recursive call only needs convexity on the slice, which is
        -- inherited from the ambient carrier by subset restriction.
        exact hφ.subset hKsub hKconv
      have hKlt : carrierRank K < d := lt_of_lt_of_le hKdrop hRank
      -- Route correction: the frontier branch now closes by immediate recursion on the smaller
      -- exposed slice, with no further affine-transport work.
      obtain ⟨L, hLK, hLconv, hXL, b, hb_lower, hb_eq⟩ :=
        ih (carrierRank K) hKlt K X φ le_rfl hX hXK hφK
      exact ⟨L, Set.Subset.trans hLK hKsub, hLconv, hXL, b, hb_lower, hb_eq⟩
  exact hmain d G X φ hRank hX hXG hφ

/-- Helper for Theorem 7.11: after shrinking to a convex carrier containing the essential range of
`X`, a convex function admits a touching affine minorant at the barycenter. -/
private lemma affine_minorant_touching_expectation_on_carrier
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Set State} {X : Ω → State}
    {φ : State → ℝ} (hX : Integrable X P) (hXG : ∀ᵐ ω ∂P, X ω ∈ G)
    (hφ : ConvexOn ℝ G φ) :
    ∃ K : Set State, K ⊆ G ∧ Convex ℝ K ∧
      (∀ᵐ ω ∂P, X ω ∈ K) ∧
      ∃ a : State →ᵃ[ℝ] ℝ, (∀ x ∈ K, a x ≤ φ x) ∧ a (P[X]) = φ (P[X]) := by
  -- Proof comment: instantiate the rank-bounded induction lemma at the actual affine-span
  -- direction finrank of `G`.
  exact
    affine_minorant_touching_expectation_on_carrier_of_finrank_le
      (d := carrierRank G) (G := G) (X := X) (φ := φ) le_rfl hX hXG hφ

/-- Theorem 7.11: Jensen's inequality on `EuclideanSpace ℝ (Fin n)`. If an integrable random
vector `X` takes values almost surely in a convex set `G`, then the negative part of `φ ∘ X` has
finite expectation, and the extended expectation of `φ(X)`, written canonically as the difference
of the lower integrals of its positive and negative parts, is at least `φ` evaluated at the
expectation of `X`. -/
-- Proof sketch: apply the finite-dimensional Jensen argument to `X`; use a touching supporting
-- affine minorant on a convex carrier containing the essential range of `X`, then integrate the
-- affine lower bound.
theorem convexOn_erealExpectation_comp_ge_euclidean {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Set State} {X : Ω → State} {φ : State → ℝ} (hX : Integrable X P)
    (hXG : ∀ᵐ ω ∂P, X ω ∈ G) (hφ : ConvexOn ℝ G φ) :
    (∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) < ⊤ ∧
      (((∫⁻ ω, ENNReal.ofReal (φ (X ω)) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) : EReal)) ≥
        (φ (P[X]) : EReal) := by
  obtain ⟨K, _, _, hXK, a, ha_lower, ha_eq⟩ :=
    affine_minorant_touching_expectation_on_carrier hX hXG hφ
  have ha_int : Integrable (fun ω ↦ a (X ω)) P := integrable_affine_comp_of_integrable hX a
  have ha_expect : P[fun ω ↦ a (X ω)] = a (P[X]) := affine_expectation_eq_expectation_apply hX a
  refine ⟨lintegral_neg_comp_lt_top_of_affine_lower_bound hXK ha_lower ha_int, ?_⟩
  exact ereal_jensen_ge_of_affine_lower_bound hXK ha_lower ha_eq ha_int ha_expect
