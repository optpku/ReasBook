/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Function Set

section

variable {H : Type u}
variable {D : Set H} {T₁ T₂ : H → H}

/-- Helper for Proposition 4.49: the composition of two self-maps of `D` is again a self-map
of `D`. -/
private lemma mapsTo_comp (hT₁_maps : MapsTo T₁ D D) (hT₂_maps : MapsTo T₂ D D) :
    MapsTo (T₁ ∘ T₂) D D :=
  hT₁_maps.comp hT₂_maps

/-- Helper for Proposition 4.49: a common fixed point of `T₁` and `T₂` is fixed by the
composition `T₁ ∘ T₂`. -/
private lemma comp_mem_fixedPointSetOn_of_mem_inter
    {x : H} (hx : x ∈ fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂) :
    x ∈ fixedPointSetOn D (T₁ ∘ T₂) := by
  -- Unpack the two fixed-point conditions and rewrite the composition directly.
  rcases hx with ⟨hx₁, hx₂⟩
  rw [mem_fixedPointSetOn_iff] at hx₁ hx₂ ⊢
  rcases hx₁ with ⟨hxD, hxT₁⟩
  rcases hx₂ with ⟨_, hxT₂⟩
  constructor
  · exact hxD
  · simp [Function.comp, hxT₁, hxT₂]

end

section

variable {H : Type u} [NormedAddCommGroup H]
variable {D : Set H} {T₁ T₂ : H → H}

/-- Helper for Proposition 4.49: the two quasinonexpansive inequalities combine to bound the
distance to a common fixed point after applying `T₁ ∘ T₂`. -/
private lemma norm_comp_le_of_common_fixed
    (hT₂_maps : MapsTo T₂ D D)
    (hT₁_qne : QuasinonexpansiveOn D T₁) (hT₂_qne : QuasinonexpansiveOn D T₂)
    {x y : H} (hx : x ∈ D) (hy₁ : y ∈ fixedPointSetOn D T₁) (hy₂ : y ∈ fixedPointSetOn D T₂) :
    ‖(T₁ ∘ T₂) x - y‖ ≤ ‖x - y‖ := by
  -- Apply quasinonexpansiveness first to `T₁` at `T₂ x`, then to `T₂` at `x`.
  rw [quasinonexpansiveOn_iff] at hT₁_qne hT₂_qne
  calc
    ‖(T₁ ∘ T₂) x - y‖ = ‖T₁ (T₂ x) - y‖ := rfl
    _ ≤ ‖T₂ x - y‖ := hT₁_qne (T₂ x) (hT₂_maps hx) y hy₁
    _ ≤ ‖x - y‖ := hT₂_qne x hx y hy₂

/-- Helper for Proposition 4.49: a fixed point of the composition is fixed by both factors when
the maps share a common fixed point and at least one factor is strictly quasinonexpansive. -/
private lemma mem_inter_fixedPointSetOn_of_mem_comp_of_one_strict
    (hT₂_maps : MapsTo T₂ D D)
    (hT₁_qne : QuasinonexpansiveOn D T₁) (hT₂_qne : QuasinonexpansiveOn D T₂)
    (hFix : (fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂).Nonempty)
    (hstrict :
      StrictlyQuasinonexpansiveOn D T₁ ∨ StrictlyQuasinonexpansiveOn D T₂)
    {x : H} (hx : x ∈ fixedPointSetOn D (T₁ ∘ T₂)) :
    x ∈ fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂ := by
  -- Extract the composition fixed-point equation and choose a common fixed point `y`.
  rw [mem_fixedPointSetOn_iff] at hx
  rcases hx with ⟨hxD, hxcomp⟩
  rcases hFix with ⟨y, hy⟩
  rcases hy with ⟨hy₁, hy₂⟩
  rw [quasinonexpansiveOn_iff] at hT₁_qne hT₂_qne
  have hcomp_le : ‖(T₁ ∘ T₂) x - y‖ ≤ ‖T₂ x - y‖ := by
    -- The first inequality in the textbook chain comes from quasinonexpansiveness of `T₁`.
    simpa [Function.comp] using hT₁_qne (T₂ x) (hT₂_maps hxD) y hy₁
  have hT₂_le : ‖T₂ x - y‖ ≤ ‖x - y‖ := hT₂_qne x hxD y hy₂
  have hcomp_eq_norm : ‖(T₁ ∘ T₂) x - y‖ = ‖x - y‖ := by
    -- Rewrite the left endpoint of the chain using `(T₁ ∘ T₂) x = x`.
    simpa [Function.comp] using congrArg (fun z ↦ ‖z - y‖) hxcomp
  have hT₂_ge : ‖x - y‖ ≤ ‖T₂ x - y‖ := by
    -- Equality at the chain endpoints forces the middle term to have the same norm.
    calc
      ‖x - y‖ = ‖(T₁ ∘ T₂) x - y‖ := by simpa [Function.comp, hxcomp] using hcomp_eq_norm.symm
      _ ≤ ‖T₂ x - y‖ := hcomp_le
  have hT₂_eq : ‖T₂ x - y‖ = ‖x - y‖ := le_antisymm hT₂_le hT₂_ge
  have hcomp_ge : ‖T₂ x - y‖ ≤ ‖(T₁ ∘ T₂) x - y‖ := by
    -- The same endpoint equality also forces equality in the first inequality.
    calc
      ‖T₂ x - y‖ ≤ ‖x - y‖ := hT₂_le
      _ = ‖(T₁ ∘ T₂) x - y‖ := by simpa [Function.comp, hxcomp] using hcomp_eq_norm.symm
  have hcomp_eq_mid : ‖(T₁ ∘ T₂) x - y‖ = ‖T₂ x - y‖ := le_antisymm hcomp_le hcomp_ge
  rcases hstrict with hT₁_strict | hT₂_strict
  · rw [strictlyQuasinonexpansiveOn_iff] at hT₁_strict
    have hT₂x_fixed₁ : T₂ x ∈ fixedPointSetOn D T₁ := by
      -- If `T₂ x` were not fixed by `T₁`, strict quasinonexpansiveness of `T₁` would contradict
      -- equality in the first step of the chain.
      by_contra hnot
      have hlt : ‖T₁ (T₂ x) - y‖ < ‖T₂ x - y‖ := by
        exact hT₁_strict (T₂ x) ⟨hT₂_maps hxD, hnot⟩ y hy₁
      have hlt' : ‖(T₁ ∘ T₂) x - y‖ < ‖T₂ x - y‖ := by
        simpa [Function.comp] using hlt
      rw [hcomp_eq_mid] at hlt'
      exact lt_irrefl _ hlt'
    rw [mem_fixedPointSetOn_iff] at hT₂x_fixed₁
    rcases hT₂x_fixed₁ with ⟨_, hT₁T₂x⟩
    have hxT₂ : T₂ x = x := by
      -- Once `T₂ x` is fixed by `T₁`, the composition equation collapses to `T₂ x = x`.
      calc
        T₂ x = T₁ (T₂ x) := hT₁T₂x.symm
        _ = x := by simpa [Function.comp] using hxcomp
    have hx₂ : x ∈ fixedPointSetOn D T₂ := by
      rw [mem_fixedPointSetOn_iff]
      exact ⟨hxD, hxT₂⟩
    have hx₁ : x ∈ fixedPointSetOn D T₁ := by
      -- Rewrite the composition fixed-point equation using `T₂ x = x`.
      rw [mem_fixedPointSetOn_iff]
      constructor
      · exact hxD
      · simpa [Function.comp, hxT₂] using hxcomp
    exact ⟨hx₁, hx₂⟩
  · rw [strictlyQuasinonexpansiveOn_iff] at hT₂_strict
    have hx₂ : x ∈ fixedPointSetOn D T₂ := by
      -- If `x` were not fixed by `T₂`, strict quasinonexpansiveness of `T₂` would contradict
      -- equality in the second step of the chain.
      by_contra hnot
      have hlt : ‖T₂ x - y‖ < ‖x - y‖ := hT₂_strict x ⟨hxD, hnot⟩ y hy₂
      rw [hT₂_eq] at hlt
      exact lt_irrefl _ hlt
    rw [mem_fixedPointSetOn_iff] at hx₂
    rcases hx₂ with ⟨_, hxT₂⟩
    have hx₁ : x ∈ fixedPointSetOn D T₁ := by
      -- After proving `T₂ x = x`, the composition fixed-point equation reduces to `T₁ x = x`.
      rw [mem_fixedPointSetOn_iff]
      constructor
      · exact hxD
      · simpa [Function.comp, hxT₂] using hxcomp
    exact ⟨hx₁, ⟨hxD, hxT₂⟩⟩

/-- Helper for Proposition 4.49: if both factors are strictly quasinonexpansive, then every point
outside the fixed-point set of the composition moves strictly closer to each common fixed point. -/
private lemma norm_comp_lt_of_not_mem_comp_fixed
    (hT₂_maps : MapsTo T₂ D D)
    (hT₁_qne : QuasinonexpansiveOn D T₁)
    (hT₁_strict : StrictlyQuasinonexpansiveOn D T₁)
    (hT₂_strict : StrictlyQuasinonexpansiveOn D T₂)
    {x y : H} (hx : x ∈ D \ fixedPointSetOn D (T₁ ∘ T₂))
    (hy : y ∈ fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂) :
    ‖(T₁ ∘ T₂) x - y‖ < ‖x - y‖ := by
  -- Split on whether `x` is already fixed by `T₂`, matching the textbook proof.
  rw [quasinonexpansiveOn_iff] at hT₁_qne
  rw [strictlyQuasinonexpansiveOn_iff] at hT₁_strict hT₂_strict
  rcases hy with ⟨hy₁, hy₂⟩
  by_cases hx₂ : x ∈ fixedPointSetOn D T₂
  · have hx₁_not : x ∉ fixedPointSetOn D T₁ := by
      -- If `x` were fixed by both factors, it would already be fixed by the composition.
      intro hx₁
      exact hx.2 (comp_mem_fixedPointSetOn_of_mem_inter ⟨hx₁, hx₂⟩)
    have hlt : ‖T₁ x - y‖ < ‖x - y‖ := hT₁_strict x ⟨hx.1, hx₁_not⟩ y hy₁
    rw [mem_fixedPointSetOn_iff] at hx₂
    rcases hx₂ with ⟨_, hxT₂⟩
    -- Replacing `T₂ x` by `x` reduces the composition to the strict `T₁` inequality.
    simpa [Function.comp, hxT₂] using hlt
  · have hlt₂ : ‖T₂ x - y‖ < ‖x - y‖ := hT₂_strict x ⟨hx.1, hx₂⟩ y hy₂
    have hle₁ : ‖(T₁ ∘ T₂) x - y‖ ≤ ‖T₂ x - y‖ := by
      -- The first map is only used quasinonexpansively in this branch.
      simpa [Function.comp] using hT₁_qne (T₂ x) (hT₂_maps hx.1) y hy₁
    exact lt_of_le_of_lt hle₁ hlt₂

-- Proof sketch: one inclusion is immediate from the definition of fixed points. For the reverse
-- inclusion, choose a common fixed point `y`; quasinonexpansiveness gives
-- `‖(T₁ ∘ T₂) x - y‖ ≤ ‖T₂ x - y‖ ≤ ‖x - y‖`, and the equality `(T₁ ∘ T₂) x = x` forces equality
-- throughout. The strict quasinonexpansiveness of at least one factor then shows first that
-- `x ∈ fixedPointSetOn D T₂` or `T₂ x ∈ fixedPointSetOn D T₁`, and hence `x` is fixed by both
-- maps.
/-- Proposition 4.49 (1): if `T₁` and `T₂` are quasinonexpansive self-maps of `D` with a common
fixed point, and at least one of them is strictly quasinonexpansive, then the fixed points of the
composition `T₁ ∘ T₂` are exactly the common fixed points of `T₁` and `T₂` in `D`. -/
theorem fixedPointSetOn_comp_eq_inter_of_one_strictlyQuasinonexpansive
    (_hT₁_maps : MapsTo T₁ D D) (hT₂_maps : MapsTo T₂ D D)
    (hT₁_qne : QuasinonexpansiveOn D T₁) (hT₂_qne : QuasinonexpansiveOn D T₂)
    (hFix : (fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂).Nonempty)
    (hstrict :
      StrictlyQuasinonexpansiveOn D T₁ ∨ StrictlyQuasinonexpansiveOn D T₂) :
    fixedPointSetOn D (T₁ ∘ T₂) = fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂ := by
  -- Prove the two set inclusions separately, following the textbook chain-of-inequalities route.
  apply Set.Subset.antisymm
  · intro x hx
    exact mem_inter_fixedPointSetOn_of_mem_comp_of_one_strict
      hT₂_maps hT₁_qne hT₂_qne hFix hstrict hx
  · intro x hx
    exact comp_mem_fixedPointSetOn_of_mem_inter hx

-- Proof sketch: let `y ∈ fixedPointSetOn D (T₁ ∘ T₂)`. By part (1), `y` is a common fixed point
-- of `T₁` and `T₂`. Then quasinonexpansiveness of `T₁` at `T₂ x` and of `T₂` at `x` gives
-- `‖(T₁ ∘ T₂) x - y‖ ≤ ‖T₂ x - y‖ ≤ ‖x - y‖`.
/-- Proposition 4.49 (2): under the same hypotheses, the composition `T₁ ∘ T₂` is a
quasinonexpansive self-map of `D`. -/
theorem quasinonexpansiveOn_comp_of_one_strictlyQuasinonexpansive
    (hT₁_maps : MapsTo T₁ D D) (hT₂_maps : MapsTo T₂ D D)
    (hT₁_qne : QuasinonexpansiveOn D T₁) (hT₂_qne : QuasinonexpansiveOn D T₂)
    (hFix : (fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂).Nonempty)
    (hstrict :
      StrictlyQuasinonexpansiveOn D T₁ ∨ StrictlyQuasinonexpansiveOn D T₂) :
    MapsTo (T₁ ∘ T₂) D D ∧ QuasinonexpansiveOn D (T₁ ∘ T₂) := by
  -- Rewrite fixed points of the composition as common fixed points, then apply the two-step norm
  -- estimate packaged in `norm_comp_le_of_common_fixed`.
  constructor
  · exact mapsTo_comp hT₁_maps hT₂_maps
  · rw [quasinonexpansiveOn_iff]
    intro x hx y hy
    have hy' : y ∈ fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂ := by
      rw [fixedPointSetOn_comp_eq_inter_of_one_strictlyQuasinonexpansive
        hT₁_maps hT₂_maps hT₁_qne hT₂_qne hFix hstrict] at hy
      exact hy
    exact norm_comp_le_of_common_fixed hT₂_maps hT₁_qne hT₂_qne hx hy'.1 hy'.2

-- Proof sketch: let `y ∈ fixedPointSetOn D (T₁ ∘ T₂)`. By part (1), `y` is fixed by both `T₁`
-- and `T₂`. If `x ∉ fixedPointSetOn D T₂`, apply strict quasinonexpansiveness of `T₂` and then
-- quasinonexpansiveness of `T₁`. If `x ∈ fixedPointSetOn D T₂`, then `x ∉ fixedPointSetOn D T₁`
-- because otherwise `x` would already be fixed by `T₁ ∘ T₂`; now strict quasinonexpansiveness of
-- `T₁` yields the desired strict inequality.
/-- Proposition 4.49 (3): if both `T₁` and `T₂` are strictly quasinonexpansive self-maps of `D`
with a common fixed point, then their composition `T₁ ∘ T₂` is a strictly quasinonexpansive
self-map of `D`. -/
theorem strictlyQuasinonexpansiveOn_comp
    (hT₁_maps : MapsTo T₁ D D) (hT₂_maps : MapsTo T₂ D D)
    (hFix : (fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂).Nonempty)
    (hT₁_strict : StrictlyQuasinonexpansiveOn D T₁)
    (hT₂_strict : StrictlyQuasinonexpansiveOn D T₂) :
    MapsTo (T₁ ∘ T₂) D D ∧ StrictlyQuasinonexpansiveOn D (T₁ ∘ T₂) := by
  -- Identify fixed points of the composition with common fixed points and then split on whether
  -- the current point is fixed by `T₂`.
  have hT₁_qne : QuasinonexpansiveOn D T₁ :=
    StrictlyQuasinonexpansiveOn.quasinonexpansiveOn hT₁_strict
  have hT₂_qne : QuasinonexpansiveOn D T₂ :=
    StrictlyQuasinonexpansiveOn.quasinonexpansiveOn hT₂_strict
  constructor
  · exact mapsTo_comp hT₁_maps hT₂_maps
  · rw [strictlyQuasinonexpansiveOn_iff]
    intro x hx y hy
    have hy' : y ∈ fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂ := by
      rw [fixedPointSetOn_comp_eq_inter_of_one_strictlyQuasinonexpansive
        hT₁_maps hT₂_maps hT₁_qne hT₂_qne hFix (.inl hT₁_strict)] at hy
      exact hy
    exact norm_comp_lt_of_not_mem_comp_fixed hT₂_maps hT₁_qne hT₁_strict hT₂_strict hx hy'

end
