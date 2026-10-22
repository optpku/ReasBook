/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_2_7
import AlgebraicTopology_May_1999.Chap03.Definition_3_8_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open Path.Homotopic.Quotient
open TopologicalSpace.OpenNhdsOf
open scoped FundamentalGroup unitInterval

variable {B : Type u} [TopologicalSpace B]

/-- Helper for Theorem 3.8.2: a path-connected covering with trivial induced subgroup at one
basepoint is already universal. -/
theorem isUniversalCoveringMap_of_fundamentalGroup_range_eq_bot
    {E : Type u} [TopologicalSpace E] [PathConnectedSpace E] {p : C(E, B)}
    (hp : IsPathConnectedCoveringMap p) (e : E)
    (hbot : (FundamentalGroup.map p e).range = ⊥) :
    IsUniversalCoveringMap p := by
  refine ⟨hp, ?_⟩
  have hsub_e : Subsingleton (FundamentalGroup E e) := by
    let f : FundamentalGroup E e →* FundamentalGroup B (p e) := FundamentalGroup.map p e
    have hf : Function.Injective f := by
      simpa using hp.isCoveringMap.injective_path_homotopic_map e e
    -- Injectivity plus trivial image makes the based fundamental group at `e` trivial.
    rw [MonoidHom.range_eq_bot_iff] at hbot
    refine ⟨fun γ δ ↦ hf ?_⟩
    simpa using
      (congrArg (fun g : FundamentalGroup E e →* FundamentalGroup B (p e) ↦ g γ) hbot).trans
        (congrArg (fun g : FundamentalGroup E e →* FundamentalGroup B (p e) ↦ g δ) hbot).symm
  have hsub : ∀ x : E, Subsingleton (FundamentalGroup E x) := fun x ↦ by
    let ex : FundamentalGroup E e ≃* FundamentalGroup E x :=
      FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (X := E) (x₀ := e) (x₁ := x)
    -- Path connectedness transports triviality of the loop group from `e` to every basepoint.
    letI := hsub_e
    refine ⟨fun γ δ ↦ ?_⟩
    have hpre : ex.symm γ = ex.symm δ := Subsingleton.elim _ _
    simpa using congrArg ex hpre
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, ?_⟩
  intro x γ
  letI := hsub x
  have h : (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) : FundamentalGroup E x) = 1 :=
    Subsingleton.elim _ _
  -- Converting the trivial loop-group element back to a path class shows `γ` is null-homotopic.
  rw [show (1 : FundamentalGroup E x) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Path.refl x)) by rfl] at h
  exact Path.Homotopic.Quotient.eq.mp h

/-- Helper for Theorem 3.8.2: when the target basepoint is definitionally unchanged, the ordinary
fundamental-group map agrees with `mapOfEq`. -/
private theorem fundamental_group_map_eq_mapOfEq_rfl_local
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} (x : X) :
    FundamentalGroup.map f x = FundamentalGroup.mapOfEq f rfl := by
  -- On explicit loop representatives, both induced maps are definitionally the same.
  ext γ
  refine Quotient.inductionOn γ ?_
  intro r
  simpa using (FundamentalGroup.mapOfEq_apply (f := f) (h := rfl) (p := r)).symm

/-- Helper for Theorem 3.8.2: the induced map on fundamental groups is functorial under
composition of continuous maps. -/
private theorem fundamental_group_map_comp_local
    {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    FundamentalGroup.map (g.comp f) x =
      (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) := by
  -- Reduce composition to the path-level description of the induced map.
  ext γ
  refine Quotient.inductionOn γ ?_
  intro r
  rfl

/-- Helper for Theorem 3.8.2: every point admits a path-connected open neighborhood whose
inclusion induces the trivial map on the based fundamental group. -/
private theorem exists_suitable_universal_cover_neighborhood
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] (x : B) :
    ∃ U : TopologicalSpace.OpenNhdsOf x,
      IsPathConnected (U : Set B) ∧
        FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)) ⟨x, U.mem⟩ = 1 := by
  rcases SemilocallySimplyConnectedSpace.trivial_fundamentalGroup_map (B := B) x with ⟨U, hUtriv⟩
  let Vset : Set B := pathComponentIn (U : Set B) x
  have hVmem : x ∈ Vset := mem_pathComponentIn_self U.mem
  have hVopen : IsOpen Vset := U.isOpen.pathComponentIn x
  have hVpath : IsPathConnected Vset := isPathConnected_pathComponentIn U.mem
  let V : TopologicalSpace.OpenNhdsOf x := ⟨⟨Vset, hVopen⟩, hVmem⟩
  have hVsubsetU : (V : Set B) ⊆ U := pathComponentIn_subset
  let iVU : C(V, U) :=
    ⟨fun v ↦ ⟨v.1, hVsubsetU v.2⟩, continuous_subtype_val.subtype_mk fun v ↦ hVsubsetU v.2⟩
  have hSubtypeComp :
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)).comp iVU) =
        (⟨Subtype.val, continuous_subtype_val⟩ : C(V, B)) := by
    ext v
    rfl
  have hVtriv :
      FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(V, B)) ⟨x, V.mem⟩ =
        (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)) ⟨x, U.mem⟩).comp
          (FundamentalGroup.map iVU ⟨x, V.mem⟩) := by
    simpa [hSubtypeComp] using fundamental_group_map_comp_local iVU
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)) ⟨x, V.mem⟩
  refine ⟨V, hVpath, ?_⟩
  -- The smaller path component factors through the semilocally simply connected neighborhood.
  calc
    FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(V, B)) ⟨x, V.mem⟩
        =
        (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)) ⟨x, U.mem⟩).comp
          (FundamentalGroup.map iVU ⟨x, V.mem⟩) := hVtriv
    _ = 1 := by
      rw [hUtriv]
      simp

/-- Helper for Theorem 3.8.2: the source-faithful path-class total space over a basepoint `b0`
is the sigma type of endpoints together with endpoint-fixed homotopy classes of paths from `b0`.
-/
private abbrev universal_cover_candidate (b0 : B) : Type u :=
  Σ x : B, Path.Homotopic.Quotient b0 x

/-- Helper for Theorem 3.8.2: a suitable neighborhood for the path-class construction is a
path-connected open neighborhood whose inclusion kills the based fundamental group. -/
private def IsSuitableForUniversalCover {x : B} (U : TopologicalSpace.OpenNhdsOf x) : Prop :=
  IsPathConnected (U : Set B) ∧
    FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)) ⟨x, U.mem⟩ = 1

/-- Helper for Theorem 3.8.2: the basic neighborhood `U[q]` consists of path classes obtained by
extending `q` with a path inside the chosen neighborhood `U`. -/
private def universal_cover_candidate_basic_set {b0 : B} (q : universal_cover_candidate (B := B) b0)
    (U : TopologicalSpace.OpenNhdsOf q.1) : Set (universal_cover_candidate (B := B) b0) :=
  { r | ∃ y : U, ∃ c : Path ⟨q.1, U.mem⟩ y,
      r = ⟨y.1, q.2.trans ((mk c).map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)))⟩ }

/-- Helper for Theorem 3.8.2: any point of a basic set projects to the indexing neighborhood. -/
private theorem universal_cover_candidate_basic_set_endpoint_mem
    {b0 : B} (q : universal_cover_candidate (B := B) b0)
    (U : TopologicalSpace.OpenNhdsOf q.1)
    {r : universal_cover_candidate (B := B) b0}
    (hr : r ∈ universal_cover_candidate_basic_set q U) :
    r.1 ∈ (U : Set B) := by
  rcases hr with ⟨y, c, rfl⟩
  -- Unpacking the witnesses shows that the endpoint is exactly the chosen `y : U`.
  exact y.2

/-- Helper for Theorem 3.8.2: extending a path class by a path inside `U` produces a point of the
associated basic set. -/
private theorem universal_cover_candidate_basic_set_pathClass_mem
    {b0 : B} (q : universal_cover_candidate (B := B) b0)
    (U : TopologicalSpace.OpenNhdsOf q.1)
    (u : U) (c : Path ⟨q.1, U.mem⟩ u) :
    (⟨u.1, q.2.trans ((mk c).map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)))⟩ :
      universal_cover_candidate (B := B) b0) ∈
        universal_cover_candidate_basic_set q U := by
  -- The defining witnesses are precisely the endpoint `u` and the chosen path `c`.
  exact ⟨u, c, rfl⟩

/-- Helper for Theorem 3.8.2: every point belongs to the basic set indexed by itself. -/
private theorem universal_cover_candidate_basic_set_self_mem
    {b0 : B} (r : universal_cover_candidate (B := B) b0)
    (U : TopologicalSpace.OpenNhdsOf r.1) :
    r ∈ universal_cover_candidate_basic_set r U := by
  -- Use the constant path at `r.1`; concatenating by a constant path leaves the class unchanged.
  let i : C(U, B) := (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B))
  refine ⟨⟨r.1, U.mem⟩, Path.refl _, ?_⟩
  cases r with
  | mk x γ =>
      -- After exposing the sigma components, the constant-path extension is definitionally the
      -- same as composing with the constant path class in `B`.
      change (⟨x, γ⟩ : universal_cover_candidate (B := B) b0) =
        ⟨x, γ.trans ((mk (Path.refl ⟨x, U.mem⟩)).map i)⟩
      have hmap : ((mk (Path.refl ⟨x, U.mem⟩)).map i) = Path.Homotopic.Quotient.refl x := rfl
      rw [hmap]
      exact (congrArg (fun δ : Path.Homotopic.Quotient b0 x ↦
        (⟨x, δ⟩ : universal_cover_candidate (B := B) b0))
        (Path.Homotopic.Quotient.trans_refl γ)).symm

/-- Helper for Theorem 3.8.2: in a suitable neighborhood, extending a fixed path class by two
paths with the same endpoint gives the same point of the path-class total space. -/
private theorem path_class_eq_of_paths_in_suitable_neighborhood
    {b0 : B} (q : universal_cover_candidate (B := B) b0)
    (U : TopologicalSpace.OpenNhdsOf q.1) (hU : IsSuitableForUniversalCover U)
    (u : U) (c₁ c₂ : Path ⟨q.1, U.mem⟩ u) :
    (⟨u.1, q.2.trans ((mk c₁).map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)))⟩ :
      universal_cover_candidate (B := B) b0) =
      ⟨u.1, q.2.trans ((mk c₂).map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)))⟩ := by
  let i : C(U, B) := (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B))
  have hloop_refl :
      (((mk (c₁.trans c₂.symm)).map i) : Path.Homotopic.Quotient q.1 q.1) =
        Path.Homotopic.Quotient.refl q.1 := by
    let base : U := ⟨q.1, U.mem⟩
    have hloop_one :
        (FundamentalGroup.map i base)
            (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (c₁.trans c₂.symm))) = 1 := by
      -- Apply the trivial induced fundamental-group map to the explicit loop `c₁ * c₂⁻¹`.
      exact congrArg
        (fun g : FundamentalGroup U base →* FundamentalGroup B q.1 ↦
          g (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (c₁.trans c₂.symm))))
        (by simpa [i, base] using hU.2)
    rw [fundamental_group_map_eq_mapOfEq_rfl_local (f := i) (x := base)] at hloop_one
    rw [FundamentalGroup.mapOfEq_apply] at hloop_one
    rw [show (1 : FundamentalGroup B q.1) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Path.refl q.1)) by rfl] at hloop_one
    exact hloop_one
  have hpaths :
      ((((mk c₁).map i).trans (((mk c₂).map i).symm)) : Path.Homotopic.Quotient q.1 q.1) =
        Path.Homotopic.Quotient.refl q.1 := by
    -- Rewrite the loop built from the two endpoint paths into the explicit concatenation
    -- `c₁.trans c₂.symm`, then use trivial monodromy in `U`.
    calc
      ((((mk c₁).map i).trans (((mk c₂).map i).symm)) : Path.Homotopic.Quotient q.1 q.1) =
          (((mk (c₁.trans c₂.symm)).map i) : Path.Homotopic.Quotient q.1 q.1) := by
            rw [← mk_map, ← mk_map, ← mk_symm, ← mk_trans, ← mk_map]
            simp [Path.map_trans, Path.map_symm]
      _ = Path.Homotopic.Quotient.refl q.1 := hloop_refl
  have hpaths_eq :
      (((mk c₁).map i) : Path.Homotopic.Quotient q.1 u.1) =
        ((mk c₂).map i) := by
    -- Cancel the right-hand path class by composing the trivial loop with `c₂`.
    calc
      (((mk c₁).map i) : Path.Homotopic.Quotient q.1 u.1) =
          (((mk c₁).map i).trans (Path.Homotopic.Quotient.refl u.1)) := by
            simpa [i] using (Path.Homotopic.Quotient.trans_refl (((mk c₁).map i))).symm
      _ = (((mk c₁).map i).trans ((((mk c₂).map i).symm).trans ((mk c₂).map i))) := by
            simpa [i] using
              congrArg
                (fun γ : Path.Homotopic.Quotient u.1 u.1 ↦ ((mk c₁).map i).trans γ)
                (Path.Homotopic.Quotient.symm_trans (((mk c₂).map i))).symm
      _ =
          ((((mk c₁).map i).trans (((mk c₂).map i).symm)).trans ((mk c₂).map i)) := by
            rw [← Path.Homotopic.Quotient.trans_assoc]
      _ = (Path.Homotopic.Quotient.refl q.1).trans ((mk c₂).map i) := by
            rw [hpaths]
      _ = ((mk c₂).map i) := by
            simpa [i] using Path.Homotopic.Quotient.refl_trans (((mk c₂).map i))
  -- Once the endpoint extensions agree, the corresponding sigma points agree as well.
  exact congrArg
    (fun γ : Path.Homotopic.Quotient q.1 u.1 ↦
      (⟨u.1, q.2.trans γ⟩ : universal_cover_candidate (B := B) b0))
    hpaths_eq

/-- Helper for Theorem 3.8.2: if two basic sheets over the same suitable neighborhood meet, then
their indexing path classes coincide. -/
private theorem universal_cover_candidate_basic_sheet_eq_of_inter
    {b0 : B} {q₁ q₂ : universal_cover_candidate (B := B) b0}
    (U : TopologicalSpace.OpenNhdsOf q₁.1) (hU : IsSuitableForUniversalCover U)
    (hq₂ : q₂.1 = q₁.1)
    {r : universal_cover_candidate (B := B) b0}
    (hr₁ : r ∈ universal_cover_candidate_basic_set q₁ U)
    (hr₂ : r ∈ universal_cover_candidate_basic_set q₂ (hq₂ ▸ U)) :
    q₁ = q₂ := by
  cases q₁ with
  | mk x γ₁ =>
      cases q₂ with
      | mk x' γ₂ =>
          dsimp at hq₂
          subst hq₂
          dsimp at hr₁ hr₂ ⊢
          rcases hr₁ with ⟨y₁, c₁, rfl⟩
          rcases hr₂ with ⟨y₂, c₂, hEq⟩
          have hy : y₁ = y₂ := by
            -- The first coordinates of the common point force the two endpoints in `U` to agree.
            apply Subtype.ext
            exact Sigma.mk.inj_iff.mp hEq |>.1
          subst hy
          have hpaths :
              (γ₁.trans ((mk c₁).map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)))) =
                (γ₂.trans ((mk c₂).map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)))) := by
            -- Once the endpoints match, the common point identifies the two concatenated classes.
            exact eq_of_heq (Sigma.mk.inj_iff.mp hEq).2
          have hright_same :
              (γ₂.trans ((mk c₁).map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)))) =
                (γ₂.trans ((mk c₂).map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)))) := by
            -- Trivial monodromy in `U` lets us replace the chosen path to the common endpoint.
            have hsigma :
                (⟨y₁.1, γ₂.trans ((mk c₁).map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)))⟩ :
                  universal_cover_candidate (B := B) b0) =
                  ⟨y₁.1, γ₂.trans ((mk c₂).map (⟨Subtype.val, continuous_subtype_val⟩ :
                    C(U, B)))⟩ :=
              path_class_eq_of_paths_in_suitable_neighborhood
                (B := B) (b0 := b0) (q := ⟨x', γ₂⟩) U hU y₁ c₁ c₂
            exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
          let α : Path.Homotopic.Quotient x' y₁.1 :=
            ((mk c₁).map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)))
          have hcommon : γ₁.trans α = γ₂.trans α := by
            -- Replace the right-hand extension by the same endpoint path class on both sides.
            simpa [α] using hpaths.trans hright_same.symm
          have hγ : γ₁ = γ₂ := by
            -- Cancel the common suffix by composing with its inverse.
            calc
              γ₁ = (γ₁.trans α).trans α.symm := by
                rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
                  Path.Homotopic.Quotient.trans_refl]
              _ = (γ₂.trans α).trans α.symm := by rw [hcommon]
              _ = γ₂ := by
                rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
                  Path.Homotopic.Quotient.trans_refl]
          simpa [hγ]

/-- Helper for Theorem 3.8.2: a suitable neighborhood can be shrunk inside any prescribed open
neighborhood of the same point. -/
private theorem exists_suitable_universal_cover_neighborhood_subset
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] (x : B)
    (N : TopologicalSpace.OpenNhdsOf x) :
    ∃ U : TopologicalSpace.OpenNhdsOf x, (U : Set B) ⊆ N ∧ IsSuitableForUniversalCover U := by
  rcases exists_suitable_universal_cover_neighborhood (B := B) x with ⟨U₀, hU₀path, hU₀triv⟩
  let Iset : Set B := (U₀ : Set B) ∩ (N : Set B)
  have hImem : x ∈ Iset := ⟨U₀.mem, N.mem⟩
  have hIopen : IsOpen Iset := U₀.isOpen.inter N.isOpen
  let Vset : Set B := pathComponentIn Iset x
  have hVmem : x ∈ Vset := mem_pathComponentIn_self hImem
  have hVopen : IsOpen Vset := hIopen.pathComponentIn x
  have hVpath : IsPathConnected Vset := isPathConnected_pathComponentIn hImem
  let V : TopologicalSpace.OpenNhdsOf x := ⟨⟨Vset, hVopen⟩, hVmem⟩
  have hVsubsetI : (V : Set B) ⊆ Iset := pathComponentIn_subset
  have hVsubsetU₀ : (V : Set B) ⊆ U₀ := fun y hy ↦ (hVsubsetI hy).1
  let i : C(V, U₀) :=
    ⟨fun y ↦ ⟨y.1, hVsubsetU₀ y.2⟩,
      continuous_subtype_val.subtype_mk fun y ↦ hVsubsetU₀ y.2⟩
  have hcomp :
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U₀, B)).comp i) =
        (⟨Subtype.val, continuous_subtype_val⟩ : C(V, B)) := by
    ext y
    rfl
  have hVtriv :
      FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(V, B)) ⟨x, V.mem⟩ =
        (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U₀, B)) ⟨x, U₀.mem⟩).comp
          (FundamentalGroup.map i ⟨x, V.mem⟩) := by
    -- The smaller neighborhood still factors through the original suitable neighborhood.
    simpa [hcomp] using fundamental_group_map_comp_local i
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U₀, B)) ⟨x, V.mem⟩
  refine ⟨V, fun y hy ↦ (hVsubsetI hy).2, hVpath, ?_⟩
  -- Trivial monodromy descends along the inclusion `V ↪ U₀`.
  calc
    FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(V, B)) ⟨x, V.mem⟩
        =
        (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U₀, B)) ⟨x, U₀.mem⟩).comp
          (FundamentalGroup.map i ⟨x, V.mem⟩) := hVtriv
    _ = 1 := by
      rw [hU₀triv]
      simp

/-- Helper for Theorem 3.8.2: once `r` lies in the `U`-sheet indexed by `q`, every smaller sheet
through `r` contained in `U` stays in that same `U`-sheet. -/
private theorem universal_cover_candidate_basic_set_subset_of_mem
    {b0 : B} {q r : universal_cover_candidate (B := B) b0}
    (U : TopologicalSpace.OpenNhdsOf q.1) (hU : IsSuitableForUniversalCover U)
    (hr : r ∈ universal_cover_candidate_basic_set q U)
    {W : TopologicalSpace.OpenNhdsOf r.1} (hWU : (W : Set B) ⊆ U) :
    universal_cover_candidate_basic_set r W ⊆ universal_cover_candidate_basic_set q U := by
  rcases hr with ⟨u, c, rfl⟩
  intro t ht
  rcases ht with ⟨z, d, rfl⟩
  let i : C(W, U) :=
    ⟨fun y ↦ ⟨y.1, hWU y.2⟩, continuous_subtype_val.subtype_mk fun y ↦ hWU y.2⟩
  let iU : C(U, B) := (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B))
  let iW : C(W, B) := (⟨Subtype.val, continuous_subtype_val⟩ : C(W, B))
  let zU : U := ⟨z.1, hWU z.2⟩
  let dU : Path ⟨u.1, u.2⟩ zU := d.map i.continuous
  have hd :
      ((mk d).map iW) = ((mk dU).map iU) := by
    dsimp [dU]
    rw [← mk_map, ← mk_map]
    congr
  have htrans :
      (((mk c).map iU).trans ((mk dU).map iU)) =
        ((mk (c.trans dU)).map iU) := by
    rw [← mk_map, ← mk_map, ← mk_trans, ← mk_map]
    simp [Path.map_trans]
  refine ⟨zU, c.trans dU, ?_⟩
  apply Sigma.ext
  · rfl
  · -- Reassociate the two-stage extension and replace the `W ↪ B` path by its factorization through `U`.
    simpa [iU, iW, dU, zU] using
      (calc
        (q.2.trans ((mk c).map iU)).trans ((mk d).map iW) =
            (q.2.trans ((mk c).map iU)).trans ((mk dU).map iU) := by rw [hd]
        _ = q.2.trans ((((mk c).map iU).trans ((mk dU).map iU))) := by
            rw [Path.Homotopic.Quotient.trans_assoc]
        _ = q.2.trans ((mk (c.trans dU)).map iU) := by rw [htrans])

/-- Helper for Theorem 3.8.2: intersections of two suitable basic neighborhoods refine to a
smaller suitable basic neighborhood through the common point. -/
private theorem universal_cover_candidate_basic_set_intersection_refines
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 : B} {q r s : universal_cover_candidate (B := B) b0}
    (U : TopologicalSpace.OpenNhdsOf q.1) (V : TopologicalSpace.OpenNhdsOf s.1)
    (hU : IsSuitableForUniversalCover U) (hV : IsSuitableForUniversalCover V)
    (hrU : r ∈ universal_cover_candidate_basic_set q U)
    (hrV : r ∈ universal_cover_candidate_basic_set s V) :
    ∃ W : TopologicalSpace.OpenNhdsOf r.1, (W : Set B) ⊆ (U : Set B) ∩ (V : Set B) ∧
      IsSuitableForUniversalCover W ∧
        universal_cover_candidate_basic_set r W ⊆
          universal_cover_candidate_basic_set q U ∩ universal_cover_candidate_basic_set s V := by
  let I₀ : TopologicalSpace.OpenNhdsOf r.1 :=
    ⟨⟨(U : Set B) ∩ (V : Set B), U.isOpen.inter V.isOpen⟩,
      ⟨universal_cover_candidate_basic_set_endpoint_mem q U hrU,
        universal_cover_candidate_basic_set_endpoint_mem s V hrV⟩⟩
  rcases exists_suitable_universal_cover_neighborhood_subset (B := B) r.1 I₀ with
    ⟨W, hWsubset, hW⟩
  refine ⟨W, hWsubset, hW, ?_⟩
  intro t ht
  constructor
  · -- The refined sheet stays inside the original `U[q]` sheet.
    exact
      universal_cover_candidate_basic_set_subset_of_mem (q := q) (r := r) U hU hrU
        (fun x hx ↦ (hWsubset hx).1) ht
  · -- The same refined sheet also stays inside the original `V[s]` sheet.
    exact
      universal_cover_candidate_basic_set_subset_of_mem (q := s) (r := r) V hV hrV
        (fun x hx ↦ (hWsubset hx).2) ht

/-- Helper for Theorem 3.8.2: the generated topology on path classes is built from the standard
basic sets `U[q]`. -/
private def universal_cover_candidate_basic_sets (b0 : B) :
    Set (Set (universal_cover_candidate (B := B) b0)) :=
  { s | ∃ q : universal_cover_candidate (B := B) b0,
      ∃ U : TopologicalSpace.OpenNhdsOf q.1,
        IsSuitableForUniversalCover U ∧
          s = universal_cover_candidate_basic_set q U }

/-- Helper for Theorem 3.8.2: the path-class total space carries the topology generated by its
standard suitable basic sets. -/
private instance universal_cover_candidate_topologicalSpace (b0 : B) :
    TopologicalSpace (universal_cover_candidate (B := B) b0) :=
  TopologicalSpace.generateFrom (universal_cover_candidate_basic_sets (B := B) b0)

/-- Helper for Theorem 3.8.2: the suitable basic sets form a topological basis for the generated
path-class topology. -/
private theorem universal_cover_candidate_basic_sets_isTopologicalBasis
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] (b0 : B) :
    TopologicalSpace.IsTopologicalBasis (universal_cover_candidate_basic_sets (B := B) b0) := by
  refine TopologicalSpace.IsTopologicalBasis.mk ?_ ?_ rfl
  · intro s₁ hs₁ s₂ hs₂ r hr
    rcases hs₁ with ⟨q, U, hU, rfl⟩
    rcases hs₂ with ⟨s, V, hV, rfl⟩
    rcases universal_cover_candidate_basic_set_intersection_refines
        (q := q) (r := r) (s := s) U V hU hV hr.1 hr.2 with
      ⟨W, -, hW, hsubset⟩
    refine ⟨universal_cover_candidate_basic_set r W, ?_, ?_, hsubset⟩
    · exact ⟨r, W, hW, rfl⟩
    · exact universal_cover_candidate_basic_set_self_mem r W
  · ext r
    constructor
    · intro _
      simp
    · intro _
      rcases exists_suitable_universal_cover_neighborhood (B := B) r.1 with ⟨U, hU⟩
      have hrbasic :
          r ∈ universal_cover_candidate_basic_set r U := by
        exact universal_cover_candidate_basic_set_self_mem r U
      refine Set.mem_sUnion.mpr ⟨universal_cover_candidate_basic_set r U, ?_, hrbasic⟩
      exact ⟨r, U, hU, rfl⟩

/-- Helper for Theorem 3.8.2: the endpoint projection on the path-class space is continuous for
the topology generated by the standard basic sets. -/
private theorem universal_cover_candidate_projection_continuous
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] (b0 : B) :
    Continuous (fun q : universal_cover_candidate (B := B) b0 ↦ q.1) := by
  let hBasis := universal_cover_candidate_basic_sets_isTopologicalBasis (B := B) b0
  rw [continuous_def]
  intro N hN
  rw [hBasis.isOpen_iff]
  intro r hr
  let Nnhd : TopologicalSpace.OpenNhdsOf r.1 := ⟨⟨N, hN⟩, hr⟩
  rcases exists_suitable_universal_cover_neighborhood_subset (B := B) r.1 Nnhd with
    ⟨U, hUN, hU⟩
  refine ⟨universal_cover_candidate_basic_set r U, ?_, ?_, ?_⟩
  · -- Suitable basic sheets are among the chosen basis elements by construction.
    exact ⟨r, U, hU, rfl⟩
  · -- The point `r` lies in its own `U`-sheet by the constant-path witness.
    exact universal_cover_candidate_basic_set_self_mem r U
  · -- Every point of the `U`-sheet projects into `U ⊆ N`.
    intro s hs
    exact hUN (universal_cover_candidate_basic_set_endpoint_mem r U hs)

/-- Helper for Theorem 3.8.2: the path-class model carries the canonical endpoint projection to
the base space. -/
private def universal_cover_candidate_projectionMap
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] (b0 : B) :
    C(universal_cover_candidate (B := B) b0, B) :=
  ⟨fun q ↦ q.1, universal_cover_candidate_projection_continuous (B := B) b0⟩

/-- Helper for Theorem 3.8.2: each suitable basic sheet is open in the generated topology on the
path-class total space. -/
private theorem universal_cover_candidate_basic_set_isOpen
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 : B} (q : universal_cover_candidate (B := B) b0)
    (U : TopologicalSpace.OpenNhdsOf q.1) (hU : IsSuitableForUniversalCover U) :
    IsOpen (universal_cover_candidate_basic_set q U) := by
  -- The path-class topology was generated from these suitable basic sheets.
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨q, U, hU, rfl⟩

/-- Helper for Theorem 3.8.2: the endpoint projection maps each suitable basic sheet onto its
indexing neighborhood. -/
private theorem universal_cover_candidate_basic_set_surjOn
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 : B} (q : universal_cover_candidate (B := B) b0)
    (U : TopologicalSpace.OpenNhdsOf q.1) (hU : IsSuitableForUniversalCover U) :
    (universal_cover_candidate_basic_set q U).SurjOn
      (universal_cover_candidate_projectionMap (B := B) b0) (U : Set B) := by
  intro y hy
  let yU : U := ⟨y, hy⟩
  let c : Path ⟨q.1, U.mem⟩ yU :=
    (hU.1.joinedIn q.1 U.mem y hy).joined_subtype.somePath
  refine ⟨⟨y, q.2.trans ((mk c).map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)))⟩, ?_, rfl⟩
  -- Path connectedness of `U` supplies the required in-sheet point above `y`.
  exact universal_cover_candidate_basic_set_pathClass_mem q U yU c

/-- Helper for Theorem 3.8.2: the endpoint projection carries a suitable basic sheet exactly onto
its indexing neighborhood. -/
private theorem universal_cover_candidate_basic_set_image
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 : B} (q : universal_cover_candidate (B := B) b0)
    (U : TopologicalSpace.OpenNhdsOf q.1) (hU : IsSuitableForUniversalCover U) :
    universal_cover_candidate_projectionMap (B := B) b0 ''
        universal_cover_candidate_basic_set q U =
      (U : Set B) := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    -- Any point of the basic sheet projects into the indexing neighborhood.
    exact universal_cover_candidate_basic_set_endpoint_mem q U hr
  · intro hy
    -- Surjectivity of the basic sheet projection produces a point over any `y ∈ U`.
    have hsurjOn :=
      universal_cover_candidate_basic_set_surjOn (B := B) (q := q) U hU
    rcases hsurjOn hy with
      ⟨r, hr, hpr⟩
    exact ⟨r, hr, hpr⟩

/-- Helper for Theorem 3.8.2: the endpoint projection on the path-class model is an open map,
because every basic sheet projects homeomorphically onto its indexing neighborhood. -/
private theorem universal_cover_candidate_projectionMap_isOpenMap
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] (b0 : B) :
    IsOpenMap (universal_cover_candidate_projectionMap (B := B) b0) := by
  let hBasis := universal_cover_candidate_basic_sets_isTopologicalBasis (B := B) b0
  intro s hs
  rw [hBasis.isOpen_iff] at hs
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rcases hy with ⟨r, hrs, rfl⟩
  rcases hs r hrs with ⟨t, ht, hrt, hts⟩
  rcases ht with ⟨q, U, hU, rfl⟩
  refine mem_nhds_iff.mpr ⟨U, ?_, U.isOpen, ?_⟩
  · intro z hz
    have hsurjOn :=
      universal_cover_candidate_basic_set_surjOn (B := B) (q := q) U hU
    rcases hsurjOn hz with
      ⟨x, hxBasic, hpx⟩
    exact ⟨x, hts hxBasic, hpx⟩
  · -- The chosen basis element containing `r` projects onto an open neighborhood of `p r`.
    exact universal_cover_candidate_basic_set_endpoint_mem q U hrt

/-- Helper for Theorem 3.8.2: inside the fiber over `b`, a suitable sheet centered at `q` meets
that fiber only at the point `q`. -/
private theorem universal_cover_candidate_fiber_point_eq
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B}
    (q : universal_cover_candidate_projectionMap (B := B) b0 ⁻¹' ({b} : Set B)) :
    q.1.1 = b := by
  have hmem :
      universal_cover_candidate_projectionMap (B := B) b0 q.1 ∈ ({b} : Set B) :=
    q.2
  have hmem' : q.1.1 ∈ ({b} : Set B) := by
    simpa [universal_cover_candidate_projectionMap] using hmem
  exact Set.mem_singleton_iff.mp hmem'

/-- Helper for Theorem 3.8.2: inside the fiber over `b`, a suitable sheet centered at `q` meets
that fiber only at the point `q`. -/
private theorem universal_cover_candidate_fiber_singleton_eq_sheet_inter
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B} (q : universal_cover_candidate (B := B) b0)
    (U : TopologicalSpace.OpenNhdsOf q.1) (hU : IsSuitableForUniversalCover U) (hq : q.1 = b) :
    { x : universal_cover_candidate_projectionMap (B := B) b0 ⁻¹' ({b} : Set B) |
        x.1 ∈ universal_cover_candidate_basic_set q U } =
      {⟨q, by simpa [universal_cover_candidate_projectionMap, hq]⟩} := by
  ext x
  constructor
  · intro hx
    have hx' : x.1.1 = q.1 := by
      calc
        x.1.1 = b := universal_cover_candidate_fiber_point_eq (B := B) x
        _ = q.1 := hq.symm
    have hxself :
        x.1 ∈ universal_cover_candidate_basic_set x.1 (hx' ▸ U) := by
      -- Every point lies in the basic sheet indexed by itself.
      exact universal_cover_candidate_basic_set_self_mem x.1 (hx' ▸ U)
    have hqx : q = x.1 := by
      -- If two sheets over the same suitable neighborhood meet in a fiber point, they agree.
      exact universal_cover_candidate_basic_sheet_eq_of_inter
        (B := B) (b0 := b0) (q₁ := q) (q₂ := x.1) U hU hx' hx hxself
    exact Set.mem_singleton_iff.mpr (Subtype.ext hqx.symm)
  · rintro rfl
    -- The center point belongs to its own sheet via the constant path.
    exact universal_cover_candidate_basic_set_self_mem q U

/-- Helper for Theorem 3.8.2: the endpoint projection from the path-class model is surjective,
since any basepoint can be reached by a path from the chosen origin `b0`. -/
private theorem universal_cover_candidate_projectionMap_surjective
    [ConnectedSpace B] [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] (b0 : B) :
    Function.Surjective (universal_cover_candidate_projectionMap (B := B) b0) := by
  let _ : PathConnectedSpace B := PathConnectedSpace.of_locPathConnectedSpace
  intro x
  -- Represent `x` by the class of any path from `b0` to `x`.
  refine ⟨⟨x, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath b0 x)⟩, rfl⟩

/-- Helper for Theorem 3.8.2: the sheet centered at a fiber point is obtained by transporting the
chosen suitable neighborhood along the endpoint equality of that fiber point. -/
private def universal_cover_candidate_center_sheet
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B} (q : universal_cover_candidate_projectionMap (B := B) b0 ⁻¹' ({b} : Set B))
    (U : TopologicalSpace.OpenNhdsOf b) :
    Set (universal_cover_candidate (B := B) b0) :=
  universal_cover_candidate_basic_set q.1
    (Eq.ndrec U (universal_cover_candidate_fiber_point_eq (B := B) q).symm)

/-- Helper for Theorem 3.8.2: transporting a suitable neighborhood along an endpoint equality does
not change the suitability data. -/
private theorem isSuitableForUniversalCover_ndrec
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {x y : B} (h : x = y) (U : TopologicalSpace.OpenNhdsOf y)
    (hU : IsSuitableForUniversalCover U) :
    IsSuitableForUniversalCover (Eq.ndrec U h.symm) := by
  -- Suitability depends only on the underlying open neighborhood and the identified basepoint.
  subst h
  simpa using hU

/-- Helper for Theorem 3.8.2: successive transports of an open neighborhood along endpoint
equalities compose in the expected way. -/
private theorem openNhdsOf_ndrec_trans
    {x y z : B} (hxy : y = x) (hxz : x = z) (U : TopologicalSpace.OpenNhdsOf z) :
    Eq.ndrec (Eq.ndrec U hxz.symm) hxy.symm = Eq.ndrec U (hxy.trans hxz).symm := by
  -- Collapse the two transports after identifying all three endpoints.
  subst hxy
  subst hxz
  rfl

/-- Helper for Theorem 3.8.2: every point over a suitable neighborhood belongs to one of the
centered sheets indexed by the fiber over the neighborhood basepoint. -/
private theorem universal_cover_candidate_center_sheet_cover
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B} (U : TopologicalSpace.OpenNhdsOf b) (hU : IsSuitableForUniversalCover U)
    {r : universal_cover_candidate (B := B) b0} (hr : r.1 ∈ (U : Set B)) :
    ∃ q : universal_cover_candidate_projectionMap (B := B) b0 ⁻¹' ({b} : Set B),
      r ∈ universal_cover_candidate_center_sheet (B := B) q U := by
  let i : C(U, B) := (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B))
  let bU : U := ⟨b, U.mem⟩
  let rU : U := ⟨r.1, hr⟩
  let c : Path bU rU := (hU.1.joinedIn b U.mem r.1 hr).joined_subtype.somePath
  let q : universal_cover_candidate (B := B) b0 :=
    ⟨b, r.2.trans (((mk c).map i).symm)⟩
  let qf : universal_cover_candidate_projectionMap (B := B) b0 ⁻¹' ({b} : Set B) :=
    ⟨q, by simpa [universal_cover_candidate_projectionMap, q]⟩
  refine ⟨qf, ?_⟩
  simp [universal_cover_candidate_center_sheet, qf, q]
  refine ⟨⟨r.1, hr⟩, c, ?_⟩
  apply Sigma.ext
  · rfl
  · -- Cancelling the path inside `U` returns the original path class at `r`.
    dsimp [q]
    rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.trans_refl]

/-- Helper for Theorem 3.8.2: on a fixed suitable neighborhood, two points in the same centered
sheet are equal as soon as they have the same projection to the base. -/
private theorem universal_cover_candidate_center_sheet_injOn
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B} (U : TopologicalSpace.OpenNhdsOf b) (hU : IsSuitableForUniversalCover U)
    (q : universal_cover_candidate_projectionMap (B := B) b0 ⁻¹' ({b} : Set B)) :
    (universal_cover_candidate_center_sheet (B := B) q U).InjOn
      (universal_cover_candidate_projectionMap (B := B) b0) := by
  have hq : q.1.1 = b := universal_cover_candidate_fiber_point_eq (B := B) q
  have hUq : IsSuitableForUniversalCover (Eq.ndrec U hq.symm) := by
    -- Reindex the same suitable neighborhood so it is based at the endpoint of `q`.
    exact isSuitableForUniversalCover_ndrec (B := B) hq U hU
  intro r₁ hr₁ r₂ hr₂ hp
  have hr₁' : r₁ ∈ universal_cover_candidate_basic_set q.1 (Eq.ndrec U hq.symm) := by
    simpa [universal_cover_candidate_center_sheet] using hr₁
  have hr₂' : r₂ ∈ universal_cover_candidate_basic_set q.1 (Eq.ndrec U hq.symm) := by
    simpa [universal_cover_candidate_center_sheet] using hr₂
  rcases hr₁' with ⟨y₁, c₁, rfl⟩
  rcases hr₂' with ⟨y₂, c₂, rfl⟩
  dsimp [universal_cover_candidate_projectionMap] at hp
  have hy : y₁ = y₂ := Subtype.ext hp
  subst hy
  -- Over a suitable neighborhood, equal endpoints force equal path classes in one sheet.
  exact path_class_eq_of_paths_in_suitable_neighborhood
    (B := B) (b0 := b0) (q := q.1) (Eq.ndrec U hq.symm) hUq y₁ c₁ c₂

/-- Helper for Theorem 3.8.2: a centered sheet is open, since after transporting the indexing
neighborhood to the fiber point it is just an ordinary suitable basic sheet. -/
private theorem universal_cover_candidate_center_sheet_isOpen
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B} (U : TopologicalSpace.OpenNhdsOf b) (hU : IsSuitableForUniversalCover U)
    (q : universal_cover_candidate_projectionMap (B := B) b0 ⁻¹' ({b} : Set B)) :
    IsOpen (universal_cover_candidate_center_sheet (B := B) q U) := by
  have hq : q.1.1 = b := universal_cover_candidate_fiber_point_eq (B := B) q
  let Uq : TopologicalSpace.OpenNhdsOf q.1.1 := Eq.ndrec U hq.symm
  have hUq : IsSuitableForUniversalCover Uq := by
    -- Suitability is unchanged by transporting the same open neighborhood to the sheet center.
    exact isSuitableForUniversalCover_ndrec (B := B) hq U hU
  -- After rewriting the transported neighborhood, the centered sheet is a basic open set.
  simpa [universal_cover_candidate_center_sheet, Uq] using
    universal_cover_candidate_basic_set_isOpen (B := B) q.1 Uq hUq

/-- Helper for Theorem 3.8.2: the endpoint projection is surjective on each centered sheet over a
suitable neighborhood. -/
private theorem universal_cover_candidate_center_sheet_surjOn
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B} (U : TopologicalSpace.OpenNhdsOf b) (hU : IsSuitableForUniversalCover U)
    (q : universal_cover_candidate_projectionMap (B := B) b0 ⁻¹' ({b} : Set B)) :
    (universal_cover_candidate_center_sheet (B := B) q U).SurjOn
      (universal_cover_candidate_projectionMap (B := B) b0) (U : Set B) := by
  rcases q with ⟨q, hqmem⟩
  have hq : q.1 = b := by
    -- Unpack the fiber condition to identify the center point with the neighborhood basepoint.
    simpa [universal_cover_candidate_projectionMap] using hqmem
  subst hq
  -- After the endpoint rewrite, the centered sheet is the ordinary suitable basic sheet.
  simpa [universal_cover_candidate_center_sheet] using
    universal_cover_candidate_basic_set_surjOn (B := B) (q := q) U hU

/-- Helper for Theorem 3.8.2: centered sheets over one suitable neighborhood are pairwise
disjoint. -/
private theorem universal_cover_candidate_center_sheets_pairwise_disjoint
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B} (U : TopologicalSpace.OpenNhdsOf b) (hU : IsSuitableForUniversalCover U) :
    Pairwise
      (fun q₁ q₂ : universal_cover_candidate_projectionMap (B := B) b0 ⁻¹' ({b} : Set B) ↦
        Disjoint (universal_cover_candidate_center_sheet (B := B) q₁ U)
          (universal_cover_candidate_center_sheet (B := B) q₂ U)) := by
  intro q₁ q₂ hne
  refine Set.disjoint_left.2 ?_
  intro r hr₁ hr₂
  have hq₁ : q₁.1.1 = b := universal_cover_candidate_fiber_point_eq (B := B) q₁
  have hq₂ : q₂.1.1 = b := universal_cover_candidate_fiber_point_eq (B := B) q₂
  have hU₁ : IsSuitableForUniversalCover (Eq.ndrec U hq₁.symm) := by
    -- Reindex the fixed suitable neighborhood at the first sheet center.
    exact isSuitableForUniversalCover_ndrec (B := B) hq₁ U hU
  have hr₁' : r ∈ universal_cover_candidate_basic_set q₁.1 (Eq.ndrec U hq₁.symm) := by
    simpa [universal_cover_candidate_center_sheet] using hr₁
  have hr₂' : r ∈ universal_cover_candidate_basic_set q₂.1 (Eq.ndrec U hq₂.symm) := by
    simpa [universal_cover_candidate_center_sheet] using hr₂
  have hendpoint : q₂.1.1 = q₁.1.1 := hq₂.trans hq₁.symm
  have htransport :
      hendpoint ▸ (Eq.ndrec U hq₁.symm) = Eq.ndrec U hq₂.symm := by
    -- Both ways of transporting the original neighborhood to the second endpoint agree.
    simpa [hendpoint] using
      (openNhdsOf_ndrec_trans (B := B) hendpoint hq₁ U)
  have hr₂'' : r ∈ universal_cover_candidate_basic_set q₂.1 (hendpoint ▸ (Eq.ndrec U hq₁.symm)) := by
    -- Rewrite the second centered-sheet membership to the common neighborhood based at `q₁`.
    simpa [htransport] using hr₂'
  have hsame :
      q₁.1 = q₂.1 := by
    -- A point lying in both centered sheets forces the two indexing path classes to coincide.
    exact
      universal_cover_candidate_basic_sheet_eq_of_inter (B := B) (b0 := b0)
        (q₁ := q₁.1) (q₂ := q₂.1) (Eq.ndrec U hq₁.symm) hU₁ hendpoint hr₁' hr₂''
  exact hne (Subtype.ext hsame)

/-- Helper for Theorem 3.8.2: each fiber of the path-class projection is discrete, because a
suitable sheet cuts out a singleton around each fiber point. -/
private theorem universal_cover_candidate_fiber_discrete
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B} :
    DiscreteTopology (universal_cover_candidate_projectionMap (B := B) b0 ⁻¹' ({b} : Set B)) := by
  rcases exists_suitable_universal_cover_neighborhood (B := B) b with ⟨U, hU⟩
  refine discreteTopology_iff_isOpen_singleton.mpr ?_
  intro q
  have hq : q.1.1 = b := universal_cover_candidate_fiber_point_eq (B := B) q
  let Uq : TopologicalSpace.OpenNhdsOf q.1.1 := Eq.ndrec U hq.symm
  have hUq : IsSuitableForUniversalCover Uq := by
    -- Reuse the same suitable neighborhood at the endpoint of the chosen fiber point.
    exact isSuitableForUniversalCover_ndrec (B := B) hq U hU
  have hopen_center :
      IsOpen (universal_cover_candidate_center_sheet (B := B) q U) := by
    -- After one explicit transport, the centered sheet is an ordinary suitable basic set.
    simpa [universal_cover_candidate_center_sheet, Uq] using
      universal_cover_candidate_basic_set_isOpen (B := B) q.1 Uq hUq
  have hopen_trace :
      IsOpen {x : universal_cover_candidate_projectionMap (B := B) b0 ⁻¹' ({b} : Set B) |
        x.1 ∈ universal_cover_candidate_center_sheet (B := B) q U} := by
    -- The fiber trace of an open centered sheet is open by continuity of the subtype inclusion.
    simpa [Set.preimage] using
      hopen_center.preimage
        (continuous_subtype_val :
          Continuous fun x :
            universal_cover_candidate_projectionMap (B := B) b0 ⁻¹' ({b} : Set B) ↦ x.1)
  have hsingleton :
      {x : universal_cover_candidate_projectionMap (B := B) b0 ⁻¹' ({b} : Set B) |
          x.1 ∈ universal_cover_candidate_center_sheet (B := B) q U} = {q} := by
    -- In the fiber, the centered sheet meets the fiber only at its center.
    simpa [universal_cover_candidate_center_sheet, Uq] using
      (universal_cover_candidate_fiber_singleton_eq_sheet_inter (B := B) (b0 := b0)
        (q := q.1) Uq hUq hq)
  simpa [hsingleton] using hopen_trace

/-- Helper for Theorem 3.8.2: the initial segment `γ|[0,t]`, recast so that its source is the
distinguished basepoint `b0`. -/
private abbrev universal_cover_candidate_initial_subpath
    {b0 x : B} (γ : Path b0 x) (t : I) : Path b0 (γ t) :=
  (γ.subpath 0 t).cast γ.source.symm rfl

/-- Helper for Theorem 3.8.2: if the short suffix of `γ` from `s` to `t` stays in `U`, then the
canonical endpoint-fixed class at time `t` lies in the basic sheet centered at time `s`. -/
private theorem universal_cover_candidate_subpath_mem_basic_set_of_segment_subset
    {b0 x : B} (γ : Path b0 x) (s t : I) (U : TopologicalSpace.OpenNhdsOf (γ s))
    (hseg : ∀ u : I, γ.subpath s t u ∈ (U : Set B)) :
    (⟨γ t, Path.Homotopic.Quotient.mk
        (universal_cover_candidate_initial_subpath γ t)⟩ :
      universal_cover_candidate (B := B) b0) ∈
        universal_cover_candidate_basic_set
          (⟨γ s, Path.Homotopic.Quotient.mk
              (universal_cover_candidate_initial_subpath γ s)⟩ :
            universal_cover_candidate (B := B) b0) U := by
  let y : U := ⟨γ t, by simpa using hseg 1⟩
  have hc_cont : Continuous fun u : I ↦ (⟨γ.subpath s t u, hseg u⟩ : U) := by
    fun_prop
  have hc_source :
      (⟨γ.subpath s t 0, hseg 0⟩ : U) = ⟨γ s, U.mem⟩ := by
    apply Subtype.ext
    simp
  have hc_target :
      (⟨γ.subpath s t 1, hseg 1⟩ : U) = y := by
    apply Subtype.ext
    simp [y]
  let cMap : C(I, U) := ⟨fun u ↦ ⟨γ.subpath s t u, hseg u⟩, hc_cont⟩
  let c : Path ⟨γ s, U.mem⟩ y := ⟨cMap, hc_source, hc_target⟩
  have hc_map :
      c.map continuous_subtype_val = γ.subpath s t := by
    ext u
    rfl
  have hc_quot :
      ((Path.Homotopic.Quotient.mk c).map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B))) =
        Path.Homotopic.Quotient.mk (γ.subpath s t) := by
    simpa using congrArg Path.Homotopic.Quotient.mk hc_map
  have hquot :
      (Path.Homotopic.Quotient.mk (universal_cover_candidate_initial_subpath γ s)).trans
          ((Path.Homotopic.Quotient.mk c).map
            (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B))) =
        Path.Homotopic.Quotient.mk (universal_cover_candidate_initial_subpath γ t) := by
    -- Concatenating the initial segment with the short suffix is homotopic to the direct subpath.
    calc
      (Path.Homotopic.Quotient.mk (universal_cover_candidate_initial_subpath γ s)).trans
          ((Path.Homotopic.Quotient.mk c).map
            (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B))) =
        (Path.Homotopic.Quotient.mk (universal_cover_candidate_initial_subpath γ s)).trans
          (Path.Homotopic.Quotient.mk (γ.subpath s t)) := by
            rw [hc_quot]
      _ = Path.Homotopic.Quotient.mk
            (((γ.subpath 0 s).trans (γ.subpath s t)).cast γ.source.symm rfl) := by
            rw [← Path.Homotopic.Quotient.mk_trans]
            simp [universal_cover_candidate_initial_subpath, Path.cast_trans]
      _ = Path.Homotopic.Quotient.mk (universal_cover_candidate_initial_subpath γ t) := by
            exact Path.Homotopic.Quotient.eq.mpr
              ⟨(Path.Homotopy.subpathTransSubpath γ 0 s t).pathCast γ.source.symm rfl⟩
  refine ⟨y, c, ?_⟩
  apply Sigma.ext
  · simpa [y]
  · simpa [c] using hquot.symm

/-- Helper for Theorem 3.8.2: near any time `t₀`, one can choose an open interval in the unit
interval on which every short suffix of `γ` remains inside the chosen neighborhood of `γ t₀`. -/
private theorem universal_cover_candidate_subpath_local_sheet_control
    {b0 x : B} (γ : Path b0 x) (t₀ : I) (U : TopologicalSpace.OpenNhdsOf (γ t₀)) :
    ∃ W : Set I, IsOpen W ∧ t₀ ∈ W ∧
      ∀ ⦃t : I⦄, t ∈ W → ∀ u : I, γ.subpath t₀ t u ∈ (U : Set B) := by
  let F : I × I → B := fun z ↦ γ.subpath t₀ z.1 z.2
  have hF_cont : Continuous F := by
    have hcoord : Continuous fun z : I × I ↦ (t₀, z.1, z.2) := by
      fun_prop
    simpa [F] using γ.subpath_continuous_family.comp hcoord
  let N : Set (I × I) := F ⁻¹' (U : Set B)
  have hN_open : IsOpen N := U.isOpen.preimage hF_cont
  have hbase : ({t₀} : Set I) ×ˢ (Set.univ : Set I) ⊆ N := by
    intro z hz
    rcases z with ⟨t, u⟩
    rcases hz with ⟨ht, _⟩
    rcases ht with rfl
    change F (t, u) ∈ (U : Set B)
    simpa [F, Path.subpath_self] using U.mem
  rcases generalized_tube_lemma isCompact_singleton isCompact_univ hN_open hbase with
    ⟨W, V, hW_open, _hV_open, hW_mem, hV_mem, hWV⟩
  refine ⟨W, hW_open, hW_mem (by simp), ?_⟩
  intro t ht u
  have hu : u ∈ V := hV_mem (by simp)
  have hzu : (t, u) ∈ W ×ˢ V := ⟨ht, hu⟩
  show F (t, u) ∈ (U : Set B)
  exact hWV hzu

/-- Helper for Theorem 3.8.2: the canonical family `t ↦ [γ|[0,t]]` is continuous for the
generated path-class topology. -/
private theorem universal_cover_candidate_subpath_family_continuous
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 x : B} (γ : Path b0 x) :
    Continuous fun t ↦
      (⟨γ t, Path.Homotopic.Quotient.mk
          (universal_cover_candidate_initial_subpath γ t)⟩ :
        universal_cover_candidate (B := B) b0) := by
  let hBasis := universal_cover_candidate_basic_sets_isTopologicalBasis (B := B) b0
  rw [continuous_def]
  intro N hN
  rw [isOpen_iff_mem_nhds]
  intro t₀ ht₀
  let r₀ : universal_cover_candidate (B := B) b0 :=
    ⟨γ t₀, Path.Homotopic.Quotient.mk
      (universal_cover_candidate_initial_subpath γ t₀)⟩
  rcases (hBasis.isOpen_iff.mp hN) r₀ ht₀ with
    ⟨s, hs, hr₀s, hsN⟩
  rcases hs with ⟨q, U, hU, rfl⟩
  let U₀ : TopologicalSpace.OpenNhdsOf (γ t₀) :=
    ⟨U.1, universal_cover_candidate_basic_set_endpoint_mem q U hr₀s⟩
  rcases exists_suitable_universal_cover_neighborhood_subset (B := B) (γ t₀) U₀ with
    ⟨V, hVU, hV⟩
  have hsubset :
      universal_cover_candidate_basic_set r₀ V ⊆
        universal_cover_candidate_basic_set q U := by
    -- Recenter the basic sheet at the actual value of the canonical family.
    exact
      universal_cover_candidate_basic_set_subset_of_mem (B := B) (q := q) (r := r₀) U hU hr₀s hVU
  rcases universal_cover_candidate_subpath_local_sheet_control (B := B) γ t₀ V with
    ⟨W, hW_open, ht₀W, hWmem⟩
  refine mem_nhds_iff.mpr ⟨W, ?_, hW_open, ht₀W⟩
  intro t ht
  have hBasic :
      (⟨γ t, Path.Homotopic.Quotient.mk
          (universal_cover_candidate_initial_subpath γ t)⟩ :
        universal_cover_candidate (B := B) b0) ∈
          universal_cover_candidate_basic_set r₀ V := by
    -- Local sheet control converts geometric containment in `V` into basis membership upstairs.
    exact
      universal_cover_candidate_subpath_mem_basic_set_of_segment_subset (B := B) γ t₀ t V
        (hWmem ht)
  exact hsN (hsubset hBasic)

/-- Helper for Theorem 3.8.2: the covering lift of a path from the distinguished basepoint ends
at the corresponding endpoint-fixed homotopy class. -/
private theorem universal_cover_candidate_liftPath_endpoint_eq_pathClass
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 x : B}
    (hp : IsPathConnectedCoveringMap
      (universal_cover_candidate_projectionMap (B := B) b0))
    (γ : Path b0 x) :
    hp.isCoveringMap.liftPath γ
        (⟨b0, Path.Homotopic.Quotient.refl b0⟩ :
          universal_cover_candidate (B := B) b0)
        γ.source 1 =
      ⟨x, Path.Homotopic.Quotient.mk γ⟩ := by
  let e₀ : universal_cover_candidate (B := B) b0 :=
    ⟨b0, Path.Homotopic.Quotient.refl b0⟩
  let Γ : C(I, universal_cover_candidate (B := B) b0) :=
    ⟨fun t ↦ ⟨γ t, Path.Homotopic.Quotient.mk
        (universal_cover_candidate_initial_subpath γ t)⟩,
      universal_cover_candidate_subpath_family_continuous (B := B) γ⟩
  have hγ₀ : γ 0 = (universal_cover_candidate_projectionMap (B := B) b0) e₀ := by
    simpa [e₀, universal_cover_candidate_projectionMap] using γ.source
  have hΓ :
      Γ = hp.isCoveringMap.liftPath γ e₀ hγ₀ := by
    -- The explicit subpath family is a lift of `γ` from `e₀`, so uniqueness identifies it with
    -- the abstract covering lift.
    refine (hp.isCoveringMap.eq_liftPath_iff' hγ₀).2 ?_
    constructor
    · ext t
      rfl
    · apply Sigma.ext
      · simpa [Γ, e₀, universal_cover_candidate_projectionMap] using hγ₀
      · have hzero : HEq ((Γ 0).snd) e₀.snd := by
          simpa [Γ, e₀, universal_cover_candidate_initial_subpath, Path.subpath_self, Path.cast,
            γ.source] using
            (Path.Homotopic.hpath_hext
              (p₁ := ((Path.refl (γ 0)).cast γ.source.symm rfl))
              (p₂ := Path.refl b0) (fun t ↦ by simp [Path.cast, γ.source]))
        exact hzero
  have hΓ_one :
      Γ 1 = (⟨x, Path.Homotopic.Quotient.mk γ⟩ :
        universal_cover_candidate (B := B) b0) := by
    -- Evaluating the explicit family at `1` recovers the full path class.
    apply Sigma.ext
    · simpa [Γ] using γ.target
    · have hone : HEq ((Γ 1).snd) (⟨x, Path.Homotopic.Quotient.mk γ⟩ :
          universal_cover_candidate (B := B) b0).snd := by
          simpa [Γ, universal_cover_candidate_initial_subpath, Path.subpath_zero_one, Path.cast,
            γ.target] using
            (Path.Homotopic.hpath_hext (p₁ := γ.cast rfl γ.target) (p₂ := γ)
              (fun t ↦ by rfl))
      exact hone
  calc
    hp.isCoveringMap.liftPath γ e₀ hγ₀ 1 = Γ 1 := by
      simpa using congrArg (fun f : C(I, universal_cover_candidate (B := B) b0) ↦ f 1) hΓ.symm
    _ = ⟨x, Path.Homotopic.Quotient.mk γ⟩ := hΓ_one

/-- Helper for Theorem 3.8.2: the distinguished point in the path-class model has trivial induced
subgroup in the base fundamental group. -/
private theorem universal_cover_candidate_fundamentalGroup_range_eq_bot
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 : B}
    (hp : IsPathConnectedCoveringMap
      (universal_cover_candidate_projectionMap (B := B) b0)) :
    (FundamentalGroup.map (universal_cover_candidate_projectionMap (B := B) b0)
      (⟨b0, Path.Homotopic.Quotient.refl b0⟩ :
        universal_cover_candidate (B := B) b0)).range = ⊥ := by
  let E : Type u := universal_cover_candidate (B := B) b0
  let p : C(E, B) := universal_cover_candidate_projectionMap (B := B) b0
  let e₀ : E := ⟨b0, Path.Homotopic.Quotient.refl b0⟩
  rw [fundamental_group_map_eq_mapOfEq_rfl_local (f := p) (x := e₀)]
  rw [MonoidHom.range_eq_bot_iff]
  ext γ
  refine Quotient.inductionOn γ ?_
  intro δ
  change FundamentalGroup.mapOfEq p rfl
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ)) = 1
  rw [FundamentalGroup.mapOfEq_apply]
  change FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk ((δ.map p.continuous).cast rfl rfl)) = 1
  have hLift :
      δ.toContinuousMap =
        hp.isCoveringMap.liftPath (δ.map p.continuous) e₀ (δ.map p.continuous).source := by
    -- A loop in the total space is already the unique lift of its projection starting at `e₀`.
    refine (hp.isCoveringMap.eq_liftPath_iff' (δ.map p.continuous).source).2 ?_
    constructor
    · rfl
    · exact δ.source
  have hend :
      (⟨b0, Path.Homotopic.Quotient.mk (δ.map p.continuous)⟩ : E) = e₀ := by
    -- Closing up the lifted loop forces the projected path class to be the endpoint formula.
    calc
      (⟨b0, Path.Homotopic.Quotient.mk (δ.map p.continuous)⟩ : E) =
          hp.isCoveringMap.liftPath (δ.map p.continuous) e₀
            (δ.map p.continuous).source 1 := by
              symm
              simpa [p, e₀] using
                universal_cover_candidate_liftPath_endpoint_eq_pathClass
                  (B := B) (b0 := b0) hp (δ.map p.continuous)
      _ = δ 1 := by
            simpa using congrArg (fun f : C(I, E) ↦ f 1) hLift.symm
      _ = e₀ := δ.target
  have hclass :
      Path.Homotopic.Quotient.mk ((δ.map p.continuous).cast rfl rfl) =
        Path.Homotopic.Quotient.refl b0 := by
    -- Equality of the sigma points identifies the projected loop with the constant loop class.
    exact eq_of_heq (Sigma.mk.inj_iff.mp hend).2
  simpa [hclass]

/-- Helper for Theorem 3.8.2: the source-faithful path-class construction should produce a
path-connected covering with trivial image subgroup at a chosen point. -/
lemma exists_pathConnectedCovering_with_trivial_fundamentalGroup_range
    [ConnectedSpace B] [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] :
    ∃ (E : Type u) (_ : TopologicalSpace E) (_ : PathConnectedSpace E) (p : C(E, B)),
      IsPathConnectedCoveringMap p ∧ ∃ e : E, (FundamentalGroup.map p e).range = ⊥ := by
  -- Route correction: the remaining work is the covering assembly for the path-class space, not a
  -- fresh simply-connectedness development.
  classical
  let b0 : B := Classical.choice inferInstance
  let E : Type u := universal_cover_candidate (B := B) b0
  letI : TopologicalSpace E := universal_cover_candidate_topologicalSpace (B := B) b0
  let p : C(E, B) := universal_cover_candidate_projectionMap (B := B) b0
  have hsurj : Function.Surjective p := universal_cover_candidate_projectionMap_surjective
    (B := B) b0
  have hfiber_discrete :
      ∀ b : B, DiscreteTopology (p ⁻¹' ({b} : Set B)) := fun b ↦
        universal_cover_candidate_fiber_discrete (B := B) (b0 := b0) (b := b)
  have hcenter_cover :
      ∀ b : B, ∀ U : TopologicalSpace.OpenNhdsOf b, IsSuitableForUniversalCover U →
        ∀ {r : E}, r.1 ∈ (U : Set B) →
          ∃ q : p ⁻¹' ({b} : Set B), r ∈ universal_cover_candidate_center_sheet (B := B) q U := by
    intro b U hU r hr
    simpa [p, E] using universal_cover_candidate_center_sheet_cover
      (B := B) (b0 := b0) U hU hr
  have hcenter_disjoint :
      ∀ b : B, ∀ U : TopologicalSpace.OpenNhdsOf b, IsSuitableForUniversalCover U →
        Pairwise (fun q₁ q₂ : p ⁻¹' ({b} : Set B) ↦
          Disjoint (universal_cover_candidate_center_sheet (B := B) q₁ U)
            (universal_cover_candidate_center_sheet (B := B) q₂ U)) := by
    intro b U hU
    simpa [p, E] using universal_cover_candidate_center_sheets_pairwise_disjoint
      (B := B) (b0 := b0) U hU
  have hsheet_inj :
      ∀ b : B, ∀ U : TopologicalSpace.OpenNhdsOf b, IsSuitableForUniversalCover U →
        ∀ q : p ⁻¹' ({b} : Set B),
          (universal_cover_candidate_center_sheet (B := B) q U).InjOn p := by
    intro b U hU q
    simpa [p, E] using universal_cover_candidate_center_sheet_injOn
      (B := B) (b0 := b0) U hU q
  have hopenMap : IsOpenMap p := by
    simpa [p, E] using universal_cover_candidate_projectionMap_isOpenMap (B := B) b0
  let _ : Nonempty (B → E) := ⟨fun x ↦ Classical.choose (hsurj x)⟩
  have hp : IsPathConnectedCoveringMap p := by
    refine ⟨hsurj, fun b ↦ ?_⟩
    rcases exists_suitable_universal_cover_neighborhood (B := B) b with ⟨U, hU⟩
    let _ : Nonempty (p ⁻¹' ({b} : Set B)) := by
      rcases hsurj b with ⟨e, he⟩
      exact ⟨⟨e, by simpa using he⟩⟩
    have hopen_iff :
        ∀ q : p ⁻¹' ({b} : Set B), ∀ {W : Set B}, W ⊆ (U : Set B) →
          (IsOpen W ↔ IsOpen (p ⁻¹' W ∩ universal_cover_candidate_center_sheet (B := B) q U)) := by
      intro q W hWU
      constructor
      · intro hW
        -- Open subsets downstairs pull back to open traces on each centered sheet.
        exact (hW.preimage p.continuous).inter
          (universal_cover_candidate_center_sheet_isOpen (B := B) (b0 := b0) U hU q)
      · intro hPre
        have himage :
            p '' (p ⁻¹' W ∩ universal_cover_candidate_center_sheet (B := B) q U) = W := by
          ext y
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact hx.1
          · intro hy
            have hyU : y ∈ (U : Set B) := hWU hy
            have hsurjOn :=
              universal_cover_candidate_center_sheet_surjOn (B := B) (b0 := b0) U hU q
            rcases hsurjOn hyU with
              ⟨x, hxSheet, hpx⟩
            have hxW : x ∈ p ⁻¹' W := by
              show p x ∈ W
              exact hpx ▸ hy
            exact ⟨x, ⟨hxW, hxSheet⟩, hpx⟩
        -- Route correction: global openness of `p` converts the local image equality into the
        -- reverse `open_iff` direction needed for the sheet trivialization.
        simpa [himage] using hopenMap _ hPre
    let t : Bundle.Trivialization (p ⁻¹' ({b} : Set B)) p :=
      U.isOpen.trivializationDiscrete
        (fun q ↦ universal_cover_candidate_center_sheet (B := B) q U) (U : Set B) hopen_iff
        (hsheet_inj b U hU)
        (fun q ↦ universal_cover_candidate_center_sheet_surjOn
          (B := B) (b0 := b0) U hU q)
        (hcenter_disjoint b U hU)
        (by
          intro r hr
          rcases hcenter_cover b U hU hr with ⟨q, hq⟩
          exact Set.mem_iUnion.mpr ⟨q, hq⟩)
    refine ⟨hfiber_discrete b, (U : Set B), U.mem, U.isOpen, hU.1, ?_, ?_, ?_⟩
    · -- The preimage of the suitable neighborhood is open by continuity of the endpoint map.
      simpa using U.isOpen.preimage p.continuous
    · -- The centered sheets package into the required product chart via `trivializationDiscrete`.
      exact t.preimageHomeomorph (by simpa [t])
    · intro e
      -- The product chart records the basepoint coordinate as the projection of `e`.
      have hApply := Bundle.Trivialization.preimageHomeomorph_apply
        (e := t) (hb := by simpa [t]) e
      exact congrArg (fun z ↦ z.1.1) hApply
  let e₀ : E := ⟨b0, Path.Homotopic.Quotient.refl b0⟩
  let _ : PathConnectedSpace B := PathConnectedSpace.of_locPathConnectedSpace
  have hjoined_from_base : ∀ e : E, Joined e₀ e := by
    intro e
    rcases e with ⟨x, q⟩
    obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective q
    let Γ : Path e₀ (⟨x, Path.Homotopic.Quotient.mk γ⟩ : E) :=
      Path.mk (hp.isCoveringMap.liftPath γ e₀ γ.source)
        (hp.isCoveringMap.liftPath_zero γ e₀ γ.source)
        (universal_cover_candidate_liftPath_endpoint_eq_pathClass (B := B) (b0 := b0) hp γ)
    -- The explicit lifted path joins the distinguished basepoint to the chosen endpoint class.
    exact ⟨Γ⟩
  have hEpath : PathConnectedSpace E := by
    refine ⟨⟨e₀⟩, ?_⟩
    intro x y
    -- Join any two points by returning to `e₀` and then following the canonical lift outward.
    exact (hjoined_from_base x).symm.trans (hjoined_from_base y)
  have hbot :
      (FundamentalGroup.map p e₀).range = ⊥ := by
    -- A loop at `e₀` projects to the trivial class because its covering lift closes up at `e₀`.
    change
      (FundamentalGroup.map
        (universal_cover_candidate_projectionMap (B := B) b0)
        (⟨b0, Path.Homotopic.Quotient.refl b0⟩ : universal_cover_candidate (B := B) b0)).range =
        ⊥
    exact universal_cover_candidate_fundamentalGroup_range_eq_bot
      (B := B) (b0 := b0) hp
  exact ⟨E, inferInstance, hEpath, p, hp, e₀, hbot⟩

/-- Theorem 3.8.2: a connected, locally path connected, semilocally simply connected space admits
a universal covering map. -/
-- Proof sketch: fix a basepoint of `B` using connectedness. Construct a covering object
-- `X : Over (TopCat.of B)` from endpoint-fixed homotopy classes of paths starting at that
-- basepoint, topologized by the standard basic neighborhoods coming from semilocally simply
-- connected open sets. The projection `X.hom` is then a path-connected covering map, and the
-- path-class model makes the total space `X.left` simply connected, hence `X.hom` is universal.
theorem exists_universalCoveringMap [ConnectedSpace B] [LocPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] :
    ∃ X : Over (TopCat.of B), IsUniversalCoveringMap X.hom := by
  classical
  -- Route correction: reduce the theorem to the missing source-faithful path-class existence step.
  rcases exists_pathConnectedCovering_with_trivial_fundamentalGroup_range (B := B) with
    ⟨E, hE, hEpath, p, hp, e, hbot⟩
  let _ : TopologicalSpace E := hE
  let _ : PathConnectedSpace E := hEpath
  let X : Over (TopCat.of B) := Over.mk (TopCat.ofHom p)
  -- Once the path-class construction gives trivial based image subgroup, universality follows.
  refine ⟨X, ?_⟩
  simpa [X] using
    (isUniversalCoveringMap_of_fundamentalGroup_range_eq_bot (B := B) hp e hbot)
