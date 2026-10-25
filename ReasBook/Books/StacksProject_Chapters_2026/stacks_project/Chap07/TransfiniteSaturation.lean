module

public import stacks_project.Chap07.Lemma_7_39_2.RequestScheduling
public import stacks_project.Chap07.Lemma_7_39_2.PackagedStages
public import stacks_project.Chap07.Lemma_7_39_2.FiniteFrontier
public import stacks_project.Chap07.Lemma_7_39_2.DiagramUnionCore
public import stacks_project.Chap07.Lemma_7_39_2.DiagramUnionLimit

@[expose] public section

/-
Self-contained per-stage saturation kernel for Lemma 7.39.2 (pipeline-safe location:
NOT under `Lemma_7_39_2/`, so the statement pipeline does not regenerate it).

Goal: prove, for one fixed packaged stage `A`, that a single compatible refinement realizes every
finite-cover request of `A.T` — by a transfinite recursion over the well-ordered request schedule.

`Chain A x` = coherent compatible diagram on the closed down-set `↓x ⊆ WithBot M` (`⊥ ↦ A`).
-/

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open GrothendieckTopology.Point.ofIsCofiltered

universe u v w

namespace CategoryTheory

namespace TransfiniteSaturation

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

variable {J : GrothendieckTopology C}
variable {ι : Type w} [Preorder ι]

section

variable {ℱ : Sheaf J (Type (max u v w))} {S' : ιᵒᵖ ⥤ C}
  {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
    (fiber.{max u v w} S').presheafFiber).obj ℱ}
variable [Limits.HasPullbacks C]
variable {M : Type w} [LinearOrder M] [WellFoundedLT M] [SuccOrder (WithBot M)]

local notation "Ω" => WithBot M

/-! ### A small `eqToHom`-style toolkit for transporting morphisms along stage equalities. -/

variable {X X' Y Y' Z : refinement_stage (J := J) S' (ℱ := ℱ) s s'}

/-- Transport a refinement-stage morphism along equalities of its source and target stages. -/
def castHom (hX : X = X') (hY : Y = Y') (f : refinement_stage_hom (J := J) X' Y') :
    refinement_stage_hom (J := J) X Y :=
  cast (by rw [hX, hY]) f

@[simp] theorem castHom_rfl (f : refinement_stage_hom (J := J) X Y) :
    castHom (J := J) (rfl : X = X) (rfl : Y = Y) f = f := by
  simp [castHom]

theorem castHom_compat (hX : X = X') (hY : Y = Y') (f : refinement_stage_hom (J := J) X' Y') :
    (castHom (J := J) hX hY f).original_compatible ↔ f.original_compatible := by
  subst hX; subst hY; rw [castHom_rfl]

theorem castHom_comp {Z' : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (f : refinement_stage_hom (J := J) X' Y') (g : refinement_stage_hom (J := J) Y' Z') :
    refinement_stage_hom.comp (J := J) (castHom (J := J) hX hY f)
        (castHom (J := J) hY hZ g) =
      castHom (J := J) hX hZ (refinement_stage_hom.comp (J := J) f g) := by
  subst hX; subst hY; subst hZ; simp

theorem castHom_self_refl (hX : X = X') :
    castHom (J := J) hX hX (refinement_stage_hom_refl (J := J) X') =
      refinement_stage_hom_refl (J := J) X := by
  subst hX; rw [castHom_rfl]

theorem castHom_congr {hX hX' : X = X'} {hY hY' : Y = Y'}
    {f g : refinement_stage_hom (J := J) X' Y'} (h : f = g) :
    castHom (J := J) hX hY f = castHom (J := J) hX' hY' g := by
  subst hX; subst hY; rw [castHom_rfl, castHom_rfl, h]

/-- A coherent compatible diagram on the closed down-set `↓x ⊆ WithBot M`, refining `A`. -/
structure Chain (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') (x : Ω) where
  obj : {y : Ω // y ≤ x} → refinement_stage (J := J) S' (ℱ := ℱ) s s'
  obj_bot : obj ⟨⊥, bot_le⟩ = A
  mono : ∀ ⦃y z : {y : Ω // y ≤ x}⦄, (y : Ω) ≤ z →
    refinement_stage_hom (J := J) (obj y) (obj z)
  mono_refl : ∀ y : {y : Ω // y ≤ x},
    mono (le_refl (y : Ω)) = refinement_stage_hom_refl (J := J) (obj y)
  mono_comp : ∀ ⦃y z t : {y : Ω // y ≤ x}⦄ (hyz : (y : Ω) ≤ z) (hzt : (z : Ω) ≤ t),
    mono (le_trans hyz hzt) = refinement_stage_hom.comp (J := J) (mono hyz) (mono hzt)
  /-- Only the morphisms out of the base node `⊥` need be compatible with the original system
  (the abstract directed-union injections from later nodes are not). -/
  mono_bot_compat : ∀ (z : {y : Ω // y ≤ x}),
    (mono (show ((⟨⊥, bot_le⟩ : {y : Ω // y ≤ x}) : Ω) ≤ z from bot_le)).original_compatible

namespace Chain

variable {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}

/-- The compatible morphism from the base stage `A` into any node of the chain. -/
noncomputable def homFromBase {x : Ω} (D : Chain (J := J) A x) (y : {y : Ω // y ≤ x}) :
    refinement_stage_hom (J := J) A (D.obj y) := by
  have h := D.mono (show ((⟨⊥, bot_le⟩ : {y : Ω // y ≤ x}) : Ω) ≤ y from bot_le)
  rw [D.obj_bot] at h
  exact h

/-- The top stage of a chain on `↓x` is its value at `x`. -/
noncomputable def top {x : Ω} (D : Chain (J := J) A x) : refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
  D.obj ⟨x, le_rfl⟩

/-- Restrict a chain on `↓x` to the smaller closed down-set `↓c`. -/
noncomputable def restrict {x : Ω} (D : Chain (J := J) A x) {c : Ω} (hc : c ≤ x) :
    Chain (J := J) A c where
  obj y := D.obj ⟨(y : Ω), le_trans y.2 hc⟩
  obj_bot := D.obj_bot
  mono := fun {y z} hyz =>
    D.mono (y := ⟨(y : Ω), le_trans y.2 hc⟩) (z := ⟨(z : Ω), le_trans z.2 hc⟩) hyz
  mono_refl y := D.mono_refl ⟨(y : Ω), le_trans y.2 hc⟩
  mono_comp := fun {y z t} hyz hzt =>
    D.mono_comp (y := ⟨(y : Ω), le_trans y.2 hc⟩) (z := ⟨(z : Ω), le_trans z.2 hc⟩)
      (t := ⟨(t : Ω), le_trans t.2 hc⟩) hyz hzt
  mono_bot_compat := fun z => D.mono_bot_compat ⟨(z : Ω), le_trans z.2 hc⟩

@[simp] theorem restrict_obj {x : Ω} (D : Chain (J := J) A x) {c : Ω} (hc : c ≤ x)
    (y : {y : Ω // y ≤ c}) :
    (D.restrict hc).obj y = D.obj ⟨(y : Ω), le_trans y.2 hc⟩ := rfl

end Chain

/-! ### Bot case. -/

/-- The trivial chain on `↓⊥`: a single node equal to `A`. -/
noncomputable def chainBot (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    Chain (J := J) A (⊥ : Ω) where
  obj _ := A
  obj_bot := rfl
  mono _ _ _ := refinement_stage_hom_refl (J := J) A
  mono_refl _ := rfl
  mono_comp := by intro y z t hyz hzt; simp [refinement_stage_hom.refl_comp]
  mono_bot_compat := fun z => refinement_stage_hom.original_compatible_refl (J := J) A

/-! ### Successor case. -/

variable {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}

/-- The top node of the successor chain: solve request `r` on the current top of `D`. -/
noncomputable def chainSuccTop {j : Ω} (D : Chain (J := J) A j)
    (r : finite_cover_lift_request J A.T) : refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
  next_stage_for_scheduled_request (J := J) A (D.obj ⟨j, le_rfl⟩) (D.homFromBase ⟨j, le_rfl⟩) r

/-- The compatible step from the current top into the successor top. -/
noncomputable def chainSuccStep {j : Ω} (D : Chain (J := J) A j)
    (r : finite_cover_lift_request J A.T) :
    refinement_stage_hom (J := J) (D.obj ⟨j, le_rfl⟩) (chainSuccTop (J := J) D r) :=
  next_stage_for_scheduled_request_hom (J := J) A (D.obj ⟨j, le_rfl⟩) (D.homFromBase ⟨j, le_rfl⟩) r

theorem chainSuccStep_compat {j : Ω} (D : Chain (J := J) A j)
    (r : finite_cover_lift_request J A.T) : (chainSuccStep (J := J) D r).original_compatible :=
  next_stage_for_scheduled_request_original_compatible (J := J) A (D.obj ⟨j, le_rfl⟩)
    (D.homFromBase ⟨j, le_rfl⟩) r

/-- The underlying object family of the successor chain. -/
noncomputable def chainSuccObj {j : Ω} (hj : ¬ IsMax j) (D : Chain (J := J) A j)
    (r : finite_cover_lift_request J A.T) :
    {y : Ω // y ≤ Order.succ j} → refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
  fun y => if h : (y : Ω) ≤ j then D.obj ⟨y, h⟩ else chainSuccTop (J := J) D r

theorem chainSuccObj_of_le {j : Ω} (hj : ¬ IsMax j) (D : Chain (J := J) A j)
    (r : finite_cover_lift_request J A.T) {y : Ω} (hy : y ≤ j) (hy' : y ≤ Order.succ j) :
    chainSuccObj (J := J) hj D r ⟨y, hy'⟩ = D.obj ⟨y, hy⟩ := by
  simp only [chainSuccObj, dif_pos hy]

theorem chainSuccObj_top {j : Ω} (hj : ¬ IsMax j) (D : Chain (J := J) A j)
    (r : finite_cover_lift_request J A.T) :
    chainSuccObj (J := J) hj D r ⟨Order.succ j, le_rfl⟩ = chainSuccTop (J := J) D r := by
  have hnle : ¬ (Order.succ j ≤ j) := not_le.mpr (Order.lt_succ_of_not_isMax hj)
  simp only [chainSuccObj, dif_neg hnle]

/-- In a `SuccOrder`, an element `≤ succ j` is either `≤ j` or equal to `succ j`. -/
theorem le_succ_cases {j : Ω} (hj : ¬ IsMax j) {y : Ω} (hy : y ≤ Order.succ j) :
    y ≤ j ∨ y = Order.succ j := by
  rcases hy.lt_or_eq with hlt | heq
  · exact Or.inl ((Order.lt_succ_iff_of_not_isMax hj).1 hlt)
  · exact Or.inr heq

/-- A node above the cut `j` is the successor top stage. -/
theorem chainSuccObj_eq_top_of_eq {j : Ω} (hj : ¬ IsMax j) (D : Chain (J := J) A j)
    (r : finite_cover_lift_request J A.T) {z : Ω} (hz' : z ≤ Order.succ j)
    (hzeq : z = Order.succ j) :
    chainSuccObj (J := J) hj D r ⟨z, hz'⟩ = chainSuccTop (J := J) D r := by
  have hnle : ¬ (z ≤ j) := by rw [hzeq]; exact not_le.mpr (Order.lt_succ_of_not_isMax hj)
  simp only [chainSuccObj, dif_neg hnle]

/-- The morphism family of the successor chain, as a transparent `castHom` term. -/
noncomputable def chainSuccMono {j : Ω} (hj : ¬ IsMax j) (D : Chain (J := J) A j)
    (r : finite_cover_lift_request J A.T) :
    ∀ ⦃y z : {y : Ω // y ≤ Order.succ j}⦄, (y : Ω) ≤ z →
      refinement_stage_hom (J := J) (chainSuccObj (J := J) hj D r y)
        (chainSuccObj (J := J) hj D r z) :=
  fun y z hyz =>
    if hz : (z : Ω) ≤ j then
      castHom (J := J) (chainSuccObj_of_le hj D r (le_trans hyz hz) y.2)
        (chainSuccObj_of_le hj D r hz z.2)
        (D.mono (y := ⟨(y : Ω), le_trans hyz hz⟩) (z := ⟨(z : Ω), hz⟩) hyz)
    else
      if hy : (y : Ω) ≤ j then
        castHom (J := J) (chainSuccObj_of_le hj D r hy y.2)
          (chainSuccObj_eq_top_of_eq hj D r z.2 ((le_succ_cases hj z.2).resolve_left hz))
          (refinement_stage_hom.comp (J := J)
            (D.mono (y := ⟨(y : Ω), hy⟩) (z := ⟨j, le_rfl⟩) hy) (chainSuccStep (J := J) D r))
      else
        castHom (J := J)
          (chainSuccObj_eq_top_of_eq hj D r y.2 ((le_succ_cases hj y.2).resolve_left hy))
          (chainSuccObj_eq_top_of_eq hj D r z.2 ((le_succ_cases hj z.2).resolve_left hz))
          (refinement_stage_hom_refl (J := J) (chainSuccTop (J := J) D r))

/-- Reduction of `chainSuccMono` when both endpoints are `≤ j`. -/
theorem chainSuccMono_ll {j : Ω} (hj : ¬ IsMax j) (D : Chain (J := J) A j)
    (r : finite_cover_lift_request J A.T) {y z : {y : Ω // y ≤ Order.succ j}}
    (hyz : (y : Ω) ≤ z) (hz : (z : Ω) ≤ j) :
    chainSuccMono (J := J) hj D r hyz =
      castHom (J := J) (chainSuccObj_of_le hj D r (le_trans hyz hz) y.2)
        (chainSuccObj_of_le hj D r hz z.2)
        (D.mono (y := ⟨(y : Ω), le_trans hyz hz⟩) (z := ⟨(z : Ω), hz⟩) hyz) := by
  simp only [chainSuccMono, dif_pos hz]

/-- Reduction of `chainSuccMono` when `y ≤ j` but `z = succ j`. -/
theorem chainSuccMono_lt {j : Ω} (hj : ¬ IsMax j) (D : Chain (J := J) A j)
    (r : finite_cover_lift_request J A.T) {y z : {y : Ω // y ≤ Order.succ j}}
    (hyz : (y : Ω) ≤ z) (hz : ¬ (z : Ω) ≤ j) (hy : (y : Ω) ≤ j) :
    chainSuccMono (J := J) hj D r hyz =
      castHom (J := J) (chainSuccObj_of_le hj D r hy y.2)
        (chainSuccObj_eq_top_of_eq hj D r z.2 ((le_succ_cases hj z.2).resolve_left hz))
        (refinement_stage_hom.comp (J := J)
          (D.mono (y := ⟨(y : Ω), hy⟩) (z := ⟨j, le_rfl⟩) hy) (chainSuccStep (J := J) D r)) := by
  simp only [chainSuccMono, dif_neg hz, dif_pos hy]

/-- Reduction of `chainSuccMono` when both endpoints equal `succ j`. -/
theorem chainSuccMono_tt {j : Ω} (hj : ¬ IsMax j) (D : Chain (J := J) A j)
    (r : finite_cover_lift_request J A.T) {y z : {y : Ω // y ≤ Order.succ j}}
    (hyz : (y : Ω) ≤ z) (hz : ¬ (z : Ω) ≤ j) (hy : ¬ (y : Ω) ≤ j) :
    chainSuccMono (J := J) hj D r hyz =
      castHom (J := J)
        (chainSuccObj_eq_top_of_eq hj D r y.2 ((le_succ_cases hj y.2).resolve_left hy))
        (chainSuccObj_eq_top_of_eq hj D r z.2 ((le_succ_cases hj z.2).resolve_left hz))
        (refinement_stage_hom_refl (J := J) (chainSuccTop (J := J) D r)) := by
  simp only [chainSuccMono, dif_neg hz, dif_neg hy]

/-- `chainSuccMono` is compatible with the original refinement data in every case. -/
theorem chainSuccMono_bot_compat {j : Ω} (hj : ¬ IsMax j) (D : Chain (J := J) A j)
    (r : finite_cover_lift_request J A.T) (z : {y : Ω // y ≤ Order.succ j}) :
    (chainSuccMono (J := J) hj D r
      (show ((⟨⊥, bot_le⟩ : {y : Ω // y ≤ Order.succ j}) : Ω) ≤ z from bot_le)).original_compatible := by
  by_cases hz : (z : Ω) ≤ j
  · rw [chainSuccMono_ll hj D r _ hz, castHom_compat]
    exact D.mono_bot_compat ⟨(z : Ω), hz⟩
  · rw [chainSuccMono_lt hj D r _ hz bot_le, castHom_compat]
    exact refinement_stage_hom.original_compatible_comp (J := J) _ _
      (D.mono_bot_compat ⟨j, le_rfl⟩) (chainSuccStep_compat (J := J) D r)

/-- `chainSuccMono` on the diagonal is the identity. -/
theorem chainSuccMono_refl {j : Ω} (hj : ¬ IsMax j) (D : Chain (J := J) A j)
    (r : finite_cover_lift_request J A.T) (y : {y : Ω // y ≤ Order.succ j}) :
    chainSuccMono (J := J) hj D r (le_refl (y : Ω)) =
      refinement_stage_hom_refl (J := J) (chainSuccObj (J := J) hj D r y) := by
  by_cases hz : (y : Ω) ≤ j
  · rw [chainSuccMono_ll hj D r (le_refl (y : Ω)) hz, D.mono_refl ⟨(y : Ω), hz⟩,
      castHom_self_refl]
  · rw [chainSuccMono_tt hj D r (le_refl (y : Ω)) hz hz, castHom_self_refl]

/-- `chainSuccMono` respects composition. -/
theorem chainSuccMono_comp {j : Ω} (hj : ¬ IsMax j) (D : Chain (J := J) A j)
    (r : finite_cover_lift_request J A.T) ⦃y z t : {y : Ω // y ≤ Order.succ j}⦄
    (hyz : (y : Ω) ≤ z) (hzt : (z : Ω) ≤ t) :
    chainSuccMono (J := J) hj D r (le_trans hyz hzt) =
      refinement_stage_hom.comp (J := J) (chainSuccMono (J := J) hj D r hyz)
        (chainSuccMono (J := J) hj D r hzt) := by
  by_cases ht : (t : Ω) ≤ j
  · -- everything is `≤ j`.
    have hz : (z : Ω) ≤ j := le_trans hzt ht
    have hy : (y : Ω) ≤ j := le_trans hyz hz
    rw [chainSuccMono_ll hj D r (le_trans hyz hzt) ht, chainSuccMono_ll hj D r hyz hz,
      chainSuccMono_ll hj D r hzt ht, castHom_comp]
    exact castHom_congr (D.mono_comp (y := ⟨(y : Ω), _⟩) (z := ⟨(z : Ω), hz⟩)
      (t := ⟨(t : Ω), ht⟩) hyz hzt)
  · by_cases hz : (z : Ω) ≤ j
    · -- `t = succ j`, `z ≤ j`, `y ≤ j`.
      have hy : (y : Ω) ≤ j := le_trans hyz hz
      rw [chainSuccMono_lt hj D r (le_trans hyz hzt) ht hy, chainSuccMono_ll hj D r hyz hz,
        chainSuccMono_lt hj D r hzt ht hz, castHom_comp]
      refine castHom_congr ?_
      rw [← refinement_stage_hom.comp_assoc,
        ← D.mono_comp (y := ⟨(y : Ω), hy⟩) (z := ⟨(z : Ω), hz⟩) (t := ⟨j, le_rfl⟩) hyz hz]
    · -- `z = t = succ j`.
      by_cases hy : (y : Ω) ≤ j
      · -- `y ≤ j`.
        rw [chainSuccMono_lt hj D r (le_trans hyz hzt) ht hy, chainSuccMono_lt hj D r hyz hz hy,
          chainSuccMono_tt hj D r hzt ht hz, castHom_comp]
        refine castHom_congr ?_
        rw [refinement_stage_hom.comp_refl]
      · -- `y = z = t = succ j`.
        rw [chainSuccMono_tt hj D r (le_trans hyz hzt) ht hy, chainSuccMono_tt hj D r hyz hz hy,
          chainSuccMono_tt hj D r hzt ht hz, castHom_comp]
        refine castHom_congr ?_
        rw [refinement_stage_hom.comp_refl]

/-- Two chains on the same down-set are equal once their object families and morphism families
agree (the remaining fields are propositions). -/
theorem Chain.ext {x : Ω} {D D' : Chain (J := J) A x} (hobj : D.obj = D'.obj)
    (hmono : HEq D.mono D'.mono) : D = D' := by
  cases D; cases D'
  cases hobj
  cases hmono
  rfl

/-! ### Limit union: directed union of the strict-below diagram of a chain. -/

/-- The strict predecessors of `c` form a directed set (linear order). -/
instance strictBelow_isDirected (c : Ω) : IsDirected {b : Ω // b < c} (· ≤ ·) where
  directed x y := ⟨⟨max (x : Ω) (y : Ω), max_lt x.2 y.2⟩, le_max_left _ _, le_max_right _ _⟩

variable {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}

/-- The strict-below diagram of a chain `D : Chain A x` at a point `y ≤ x`: the stages `D.obj c`
for `c < y`, with the comparison morphisms inherited from `D.mono`. -/
noncomputable def belowFamily {x : Ω} (D : Chain (J := J) A x) {y : Ω} (hyx : y ≤ x) :
    {b : Ω // b < y} → refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
  fun c => D.obj ⟨(c : Ω), le_of_lt (lt_of_lt_of_le c.2 hyx)⟩

noncomputable def belowHom {x : Ω} (D : Chain (J := J) A x) {y : Ω} (hyx : y ≤ x) :
    ∀ {a b : {b : Ω // b < y}}, a ≤ b →
      refinement_stage_hom (J := J) (belowFamily (J := J) D hyx a) (belowFamily (J := J) D hyx b) :=
  fun {a b} hab =>
    D.mono (y := ⟨(a : Ω), le_of_lt (lt_of_lt_of_le a.2 hyx)⟩)
      (z := ⟨(b : Ω), le_of_lt (lt_of_lt_of_le b.2 hyx)⟩) hab

theorem belowHom_refl {x : Ω} (D : Chain (J := J) A x) {y : Ω} (hyx : y ≤ x)
    (a : {b : Ω // b < y}) :
    belowHom (J := J) D hyx (show (a : Ω) ≤ a from le_rfl) =
      refinement_stage_hom_refl (J := J) (belowFamily (J := J) D hyx a) :=
  D.mono_refl _

theorem belowHom_comp {x : Ω} (D : Chain (J := J) A x) {y : Ω} (hyx : y ≤ x)
    {a b c : {b : Ω // b < y}} (hab : (a : Ω) ≤ b) (hbc : (b : Ω) ≤ c) :
    belowHom (J := J) D hyx (le_trans hab hbc) =
      refinement_stage_hom.comp (J := J) (belowHom (J := J) D hyx hab)
        (belowHom (J := J) D hyx hbc) :=
  D.mono_comp hab hbc

/-- The base index `⊥` of the strict-below diagram (present since `y` is not minimal). -/
noncomputable def belowA0 {y : Ω} (hy : ¬ IsMin y) : {b : Ω // b < y} :=
  ⟨⊥, lt_of_le_of_ne bot_le (fun h => hy (h ▸ isMin_bot))⟩

/-- `a0`-variant of `refinementStageDiagramSystemOriginal_presheafFiber_app_of_le`: only the
single morphism `hom hb` needs to be compatible (not the whole diagram). -/
theorem original_presheafFiber_app_of_le_a0
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))} {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl : ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp : ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
      hom (le_trans hab hbc) = refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    {a0 b : δ} (hb : a0 ≤ b) (hcompat_b : (hom hb).original_compatible)
    (F : Cᵒᵖ ⥤ Type (max u v w)) :
    letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
      refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    let TΔ := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp
    ((refinementFiber
        (refinementStageDiagramSystemOriginalEmbedding (J := J) A hom hom_refl hom_comp a0)
        TΔ (refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0)
      ).presheafFiber).app F =
      ((refinementFiber (A b).j (A b).T (A b).e).presheafFiber).app F ≫
        ((refinementFiber
          (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp b)
          TΔ
          (refinementStageDiagramSystemInclusionIso
            (J := J) A hom hom_refl hom_comp b)).presheafFiber).app F := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  let TΔ := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp
  let incl0 := refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a0
  let inclb := refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp b
  have hleft :
      ((refinementFiber
          (refinementStageDiagramSystemOriginalEmbedding (J := J) A hom hom_refl hom_comp a0)
          TΔ (refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0)
        ).presheafFiber).app F =
        ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app F ≫
          ((refinementFiber incl0 TΔ
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp a0)).presheafFiber).app F := by
    change
      ((refinementFiber (compose_refinement_embedding (A a0).j incl0) TΔ
        (compose_refinement_iso (A a0).j incl0 (A a0).e
          (refinementStageDiagramSystemInclusionIso
            (J := J) A hom hom_refl hom_comp a0))).presheafFiber).app F =
        ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app F ≫
          ((refinementFiber incl0 TΔ
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp a0)).presheafFiber).app F
    rw [show refinementFiber (compose_refinement_embedding (A a0).j incl0) TΔ
          (compose_refinement_iso (A a0).j incl0 (A a0).e
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp a0)) =
        refinementFiber (A a0).j (A a0).T (A a0).e ≫
          refinementFiber incl0 TΔ
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp a0) by
          exact refinementFiber_comp (A a0).j incl0 (A a0).e
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp a0)]
    exact refinementFiber_presheafFiber_app_comp
      (j := (A a0).j) (k := incl0) (e := (A a0).e)
      (e' := refinementStageDiagramSystemInclusionIso
        (J := J) A hom hom_refl hom_comp a0) F
  have hincl :
      ((refinementFiber incl0 TΔ
          (refinementStageDiagramSystemInclusionIso
            (J := J) A hom hom_refl hom_comp a0)).presheafFiber).app F =
        ((refinementFiber (hom hb).k (A b).T (hom hb).hT).presheafFiber).app F ≫
          ((refinementFiber inclb TΔ
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp b)).presheafFiber).app F := by
    rw [show refinementFiber incl0 TΔ
          (refinementStageDiagramSystemInclusionIso
            (J := J) A hom hom_refl hom_comp a0) =
        refinementFiber (hom hb).k (A b).T (hom hb).hT ≫
          refinementFiber inclb TΔ
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp b) by
          exact refinementStageDiagramSystemInclusion_refinementFiber_of_le
            (J := J) A hom hom_refl hom_comp hb]
    exact refinementFiber_presheafFiber_app_comp
      (j := (hom hb).k) (k := inclb) (e := (hom hb).hT)
      (e' := refinementStageDiagramSystemInclusionIso
        (J := J) A hom hom_refl hom_comp b) F
  have hstage :
      ((refinementFiber (A b).j (A b).T (A b).e).presheafFiber).app F =
        ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app F ≫
          ((refinementFiber (hom hb).k (A b).T (hom hb).hT).presheafFiber).app F :=
    refinement_stage_hom.original_compatible_presheafFiber_app (hom hb) hcompat_b F
  calc
    ((refinementFiber
        (refinementStageDiagramSystemOriginalEmbedding (J := J) A hom hom_refl hom_comp a0)
        TΔ (refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0)
      ).presheafFiber).app F =
        ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app F ≫
          ((refinementFiber incl0 TΔ
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp a0)).presheafFiber).app F := hleft
    _ =
        ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app F ≫
          (((refinementFiber (hom hb).k (A b).T (hom hb).hT).presheafFiber).app F ≫
            ((refinementFiber inclb TΔ
              (refinementStageDiagramSystemInclusionIso
                (J := J) A hom hom_refl hom_comp b)).presheafFiber).app F) := by rw [hincl]
    _ =
        (((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app F ≫
          ((refinementFiber (hom hb).k (A b).T (hom hb).hT).presheafFiber).app F) ≫
            ((refinementFiber inclb TΔ
              (refinementStageDiagramSystemInclusionIso
                (J := J) A hom hom_refl hom_comp b)).presheafFiber).app F := by rw [Category.assoc]
    _ =
        ((refinementFiber (A b).j (A b).T (A b).e).presheafFiber).app F ≫
          ((refinementFiber inclb TΔ
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp b)).presheafFiber).app F := by rw [← hstage]

/-- `a0`-variant of `refinementStageDiagramLimitStage_separated_of_compatible`: only the
morphisms out of `a0` need to be compatible. -/
theorem limitStage_separated_of_a0_compatible
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    {ℱ : Sheaf J (Type (max u v w))} {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl : ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp : ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
      hom (le_trans hab hbc) = refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a0 : δ) (hcompat_a0 : ∀ b (hb : a0 ≤ b), (hom hb).original_compatible) :
    letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
      refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    let TΔ := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp
    let jΔ := refinementStageDiagramSystemOriginalEmbedding (J := J) A hom hom_refl hom_comp a0
    let eΔ := refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0
    ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
      (Type (max u v w))).obj ℱ) s ≠
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s' := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  let Fobj : Cᵒᵖ ⥤ Type (max u v w) := (sheafToPresheaf J (Type (max u v w))).obj ℱ
  let TΔ := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp
  let incl0 := refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a0
  let eIncl0 := refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp a0
  let x := ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app Fobj s
  let y := ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app Fobj s'
  change ((refinementFiber
      (refinementStageDiagramSystemOriginalEmbedding (J := J) A hom hom_refl hom_comp a0)
      TΔ (refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0)
    ).presheafFiber).app Fobj s ≠
    ((refinementFiber
      (refinementStageDiagramSystemOriginalEmbedding (J := J) A hom hom_refl hom_comp a0)
      TΔ (refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0)
    ).presheafFiber).app Fobj s'
  intro hlim
  have hfactor :
      ((refinementFiber
          (refinementStageDiagramSystemOriginalEmbedding (J := J) A hom hom_refl hom_comp a0)
          TΔ (refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0)
        ).presheafFiber).app Fobj =
        ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app Fobj ≫
          ((refinementFiber incl0 TΔ eIncl0).presheafFiber).app Fobj := by
    simpa [Fobj, TΔ, incl0, eIncl0] using
      original_presheafFiber_app_of_le_a0 (J := J) A hom hom_refl hom_comp
        (a0 := a0) (b := a0) (show a0 ≤ a0 from le_rfl)
        (by simpa only [hom_refl a0] using
          refinement_stage_hom.original_compatible_refl (J := J) (A a0))
        Fobj
  have hxy :
      ((refinementFiber incl0 TΔ eIncl0).presheafFiber).app Fobj x =
        ((refinementFiber incl0 TΔ eIncl0).presheafFiber).app Fobj y := by
    calc
      ((refinementFiber incl0 TΔ eIncl0).presheafFiber).app Fobj x =
          (((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app Fobj ≫
            ((refinementFiber incl0 TΔ eIncl0).presheafFiber).app Fobj) s := rfl
      _ = ((refinementFiber
              (refinementStageDiagramSystemOriginalEmbedding (J := J) A hom hom_refl hom_comp a0)
              TΔ (refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0)
            ).presheafFiber).app Fobj s := by rw [← hfactor]
      _ = ((refinementFiber
              (refinementStageDiagramSystemOriginalEmbedding (J := J) A hom hom_refl hom_comp a0)
              TΔ (refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0)
            ).presheafFiber).app Fobj s' := hlim
      _ = (((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app Fobj ≫
            ((refinementFiber incl0 TΔ eIncl0).presheafFiber).app Fobj) s' := by rw [hfactor]
      _ = ((refinementFiber incl0 TΔ eIncl0).presheafFiber).app Fobj y := rfl
  rcases refinementStageDiagramSystemInclusion_presheafFiber_eq_of_eq
      (J := J) A hom hom_refl hom_comp a0 Fobj hxy with ⟨b, hb, hbxy⟩
  have hstage :
      ((refinementFiber (A b).j (A b).T (A b).e).presheafFiber).app Fobj =
        ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app Fobj ≫
          ((refinementFiber (hom hb).k (A b).T (hom hb).hT).presheafFiber).app Fobj :=
    refinement_stage_hom.original_compatible_presheafFiber_app
      (hom hb) (hcompat_a0 b hb) Fobj
  have hstage_eq :
      ((refinementFiber (A b).j (A b).T (A b).e).presheafFiber).app Fobj s =
        ((refinementFiber (A b).j (A b).T (A b).e).presheafFiber).app Fobj s' := by
    rw [hstage]; simpa [x, y] using hbxy
  exact (A b).separated hstage_eq

/-- Separation survives the strict-below directed union (only `⊥`-homs need be compatible). -/
noncomputable def belowHsep {x : Ω} (D : Chain (J := J) A x) {y : Ω} (hyx : y ≤ x)
    (hy : ¬ IsMin y) :=
  limitStage_separated_of_a0_compatible (J := J) (belowFamily (J := J) D hyx)
    (belowHom (J := J) D hyx) (fun a => belowHom_refl (J := J) D hyx a)
    (fun hab hbc => belowHom_comp (J := J) D hyx hab hbc) (belowA0 hy)
    (fun b _hb => D.mono_bot_compat ⟨(b : Ω), le_of_lt (lt_of_lt_of_le b.2 hyx)⟩)

/-- The directed-union stage of the strict-below diagram of `D` at a limit point `y`. -/
noncomputable def belowUnion {x : Ω} (D : Chain (J := J) A x) {y : Ω} (hyx : y ≤ x)
    (hy : ¬ IsMin y) : refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
  refinementStageDiagramLimitStage (J := J) (belowFamily (J := J) D hyx)
    (belowHom (J := J) D hyx) (fun a => belowHom_refl (J := J) D hyx a)
    (fun hab hbc => belowHom_comp (J := J) D hyx hab hbc)
    (belowA0 hy) (belowHsep (J := J) D hyx hy)

/-- The injection of a strict-below stage into the directed-union stage. -/
noncomputable def belowInj {x : Ω} (D : Chain (J := J) A x) {y : Ω} (hyx : y ≤ x)
    (hy : ¬ IsMin y) (c : {b : Ω // b < y}) :
    refinement_stage_hom (J := J) (belowFamily (J := J) D hyx c) (belowUnion (J := J) D hyx hy) :=
  refinementStageDiagramStageHomToLimit (J := J) (belowFamily (J := J) D hyx)
    (belowHom (J := J) D hyx) (fun a => belowHom_refl (J := J) D hyx a)
    (fun hab hbc => belowHom_comp (J := J) D hyx hab hbc)
    (belowA0 hy) c (belowHsep (J := J) D hyx hy)

/-- The injection from the base node `⊥` into the directed union is compatible (the union's
embedding is by definition the `⊥`-stage's embedding composed with the inclusion). -/
theorem belowInj_a0_compat {x : Ω} (D : Chain (J := J) A x) {y : Ω} (hyx : y ≤ x)
    (hy : ¬ IsMin y) : (belowInj (J := J) D hyx hy (belowA0 hy)).original_compatible :=
  ⟨rfl, HEq.rfl⟩

/-! ### The limit-chain: rebuild a chain's top as the directed union of its strict-below. -/

/-- The object family of `limitChainOf E`: below `z` it agrees with `E`, at `z` it is the union. -/
noncomputable def chainLimitObj {z : Ω} (E : Chain (J := J) A z) (hz : ¬ IsMin z) :
    {c : Ω // c ≤ z} → refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
  fun c => if h : (c : Ω) < z then E.obj ⟨(c : Ω), le_of_lt h⟩ else belowUnion (J := J) E le_rfl hz

theorem chainLimitObj_of_lt {z : Ω} (E : Chain (J := J) A z) (hz : ¬ IsMin z) {c : Ω}
    (hc : c < z) (hc' : c ≤ z) :
    chainLimitObj (J := J) E hz ⟨c, hc'⟩ = E.obj ⟨c, le_of_lt hc⟩ := by
  simp only [chainLimitObj, dif_pos hc]

theorem chainLimitObj_top {z : Ω} (E : Chain (J := J) A z) (hz : ¬ IsMin z) :
    chainLimitObj (J := J) E hz ⟨z, le_rfl⟩ = belowUnion (J := J) E le_rfl hz := by
  simp only [chainLimitObj, dif_neg (lt_irrefl z)]

theorem chainLimitObj_eq_top_of_eq {z : Ω} (E : Chain (J := J) A z) (hz : ¬ IsMin z) {c : Ω}
    (hc' : c ≤ z) (hceq : c = z) :
    chainLimitObj (J := J) E hz ⟨c, hc'⟩ = belowUnion (J := J) E le_rfl hz := by
  have hnlt : ¬ (c < z) := by rw [hceq]; exact lt_irrefl z
  simp only [chainLimitObj, dif_neg hnlt]

/-- The morphism family of `limitChainOf E`, as a transparent `castHom` term. -/
noncomputable def chainLimitMono {z : Ω} (E : Chain (J := J) A z) (hz : ¬ IsMin z) :
    ∀ ⦃c c' : {c : Ω // c ≤ z}⦄, (c : Ω) ≤ c' →
      refinement_stage_hom (J := J) (chainLimitObj (J := J) E hz c)
        (chainLimitObj (J := J) E hz c') :=
  fun c c' hcc' =>
    if hc' : (c' : Ω) < z then
      castHom (J := J) (chainLimitObj_of_lt E hz (lt_of_le_of_lt hcc' hc') c.2)
        (chainLimitObj_of_lt E hz hc' c'.2)
        (E.mono (y := ⟨(c : Ω), le_of_lt (lt_of_le_of_lt hcc' hc')⟩)
          (z := ⟨(c' : Ω), le_of_lt hc'⟩) hcc')
    else
      if hc : (c : Ω) < z then
        castHom (J := J) (chainLimitObj_of_lt E hz hc c.2)
          (chainLimitObj_eq_top_of_eq E hz c'.2 (le_antisymm c'.2 (not_lt.1 hc')))
          (belowInj (J := J) E le_rfl hz ⟨(c : Ω), hc⟩)
      else
        castHom (J := J)
          (chainLimitObj_eq_top_of_eq E hz c.2 (le_antisymm c.2 (not_lt.1 hc)))
          (chainLimitObj_eq_top_of_eq E hz c'.2 (le_antisymm c'.2 (not_lt.1 hc')))
          (refinement_stage_hom_refl (J := J) (belowUnion (J := J) E le_rfl hz))

theorem chainLimitMono_ll {z : Ω} (E : Chain (J := J) A z) (hz : ¬ IsMin z)
    {c c' : {c : Ω // c ≤ z}} (hcc' : (c : Ω) ≤ c') (hc' : (c' : Ω) < z) :
    chainLimitMono (J := J) E hz hcc' =
      castHom (J := J) (chainLimitObj_of_lt E hz (lt_of_le_of_lt hcc' hc') c.2)
        (chainLimitObj_of_lt E hz hc' c'.2)
        (E.mono (y := ⟨(c : Ω), le_of_lt (lt_of_le_of_lt hcc' hc')⟩)
          (z := ⟨(c' : Ω), le_of_lt hc'⟩) hcc') := by
  simp only [chainLimitMono, dif_pos hc']

theorem chainLimitMono_lt {z : Ω} (E : Chain (J := J) A z) (hz : ¬ IsMin z)
    {c c' : {c : Ω // c ≤ z}} (hcc' : (c : Ω) ≤ c') (hc' : ¬ (c' : Ω) < z) (hc : (c : Ω) < z) :
    chainLimitMono (J := J) E hz hcc' =
      castHom (J := J) (chainLimitObj_of_lt E hz hc c.2)
        (chainLimitObj_eq_top_of_eq E hz c'.2 (le_antisymm c'.2 (not_lt.1 hc')))
        (belowInj (J := J) E le_rfl hz ⟨(c : Ω), hc⟩) := by
  simp only [chainLimitMono, dif_neg hc', dif_pos hc]

theorem chainLimitMono_tt {z : Ω} (E : Chain (J := J) A z) (hz : ¬ IsMin z)
    {c c' : {c : Ω // c ≤ z}} (hcc' : (c : Ω) ≤ c') (hc' : ¬ (c' : Ω) < z) (hc : ¬ (c : Ω) < z) :
    chainLimitMono (J := J) E hz hcc' =
      castHom (J := J)
        (chainLimitObj_eq_top_of_eq E hz c.2 (le_antisymm c.2 (not_lt.1 hc)))
        (chainLimitObj_eq_top_of_eq E hz c'.2 (le_antisymm c'.2 (not_lt.1 hc')))
        (refinement_stage_hom_refl (J := J) (belowUnion (J := J) E le_rfl hz)) := by
  simp only [chainLimitMono, dif_neg hc', dif_neg hc]

theorem chainLimitMono_bot_compat {z : Ω} (E : Chain (J := J) A z) (hz : ¬ IsMin z)
    (c' : {c : Ω // c ≤ z}) :
    (chainLimitMono (J := J) E hz
      (show ((⟨⊥, bot_le⟩ : {c : Ω // c ≤ z}) : Ω) ≤ c' from bot_le)).original_compatible := by
  have hc : ((⟨⊥, bot_le⟩ : {c : Ω // c ≤ z}) : Ω) < z :=
    lt_of_le_of_ne bot_le (fun h => hz (h ▸ isMin_bot))
  by_cases hc' : (c' : Ω) < z
  · rw [chainLimitMono_ll E hz _ hc', castHom_compat]
    exact E.mono_bot_compat ⟨(c' : Ω), le_of_lt hc'⟩
  · rw [chainLimitMono_lt E hz _ hc' hc, castHom_compat]
    exact belowInj_a0_compat (J := J) E le_rfl hz

/-- The successor chain on `↓(succ j)`, obtained from `D : Chain A j` by solving request `r`. -/
noncomputable def chainSucc {j : Ω} (hj : ¬ IsMax j) (D : Chain (J := J) A j)
    (r : finite_cover_lift_request J A.T) : Chain (J := J) A (Order.succ j) where
  obj := chainSuccObj (J := J) hj D r
  obj_bot := (chainSuccObj_of_le hj D r bot_le bot_le).trans D.obj_bot
  mono := chainSuccMono (J := J) hj D r
  mono_refl := chainSuccMono_refl (J := J) hj D r
  mono_comp := chainSuccMono_comp (J := J) hj D r
  mono_bot_compat := chainSuccMono_bot_compat (J := J) hj D r

end

end TransfiniteSaturation

end CategoryTheory
