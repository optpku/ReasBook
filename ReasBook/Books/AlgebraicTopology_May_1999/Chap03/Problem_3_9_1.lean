/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Lemma_1_4_2
import AlgebraicTopology_May_1999.Chap01.Problem_1_8_3
import AlgebraicTopology_May_1999.Chap01.Theorem_1_2_9
import AlgebraicTopology_May_1999.Chap02.Lemma_2_8_4
import AlgebraicTopology_May_1999.Chap03.Theorem_3_7_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped FundamentalGroup

variable {H : Type u} {G : Type v}
  [TopologicalSpace H] [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [ConnectedSpace H] [LocPathConnectedSpace H]
  {p : H → G}

section

variable (hp : IsCoveringMap p) (e : p ⁻¹' ({1} : Set G))

include hp e

/-- Helper for Problem 3.9.1: the multiplication map on `G` pulled back along the covering map
`p`. -/
def covering_base_mul : C(H × H, G) :=
  { toFun := fun z ↦ p z.1 * p z.2
    continuous_toFun := (hp.continuous.comp continuous_fst).mul (hp.continuous.comp continuous_snd) }

/-- Helper for Problem 3.9.1: the inversion map on `G` pulled back along the covering map `p`. -/
def covering_base_inv : C(H, G) :=
  { toFun := fun x ↦ (p x)⁻¹
    continuous_toFun := hp.continuous.inv }

/-- Helper for Problem 3.9.1: when the target basepoint is definitionally unchanged, the ordinary
fundamental-group map agrees with `mapOfEq`. -/
theorem fundamental_group_map_eq_mapOfEq_rfl
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} (x : X) :
    FundamentalGroup.map f x = FundamentalGroup.mapOfEq f rfl := by
  -- In the definitional-basepoint case, both maps act identically on loop representatives.
  ext γ
  refine Quotient.inductionOn γ ?_
  intro r
  simpa using (FundamentalGroup.mapOfEq_apply (f := f) (h := rfl) (p := r)).symm

/-- Helper for Problem 3.9.1: two continuous lifts through the fixed covering map agree on a
preconnected domain once their composites with `p` agree and they match at one point. -/
theorem covering_lift_ext
    {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    (f g : C(A, H)) {a₀ : A}
    (hcomp : p ∘ f = p ∘ g) (hbase : f a₀ = g a₀) :
    f = g := by
  -- Uniqueness of lifts for coverings reduces equality of continuous maps to one point check.
  ext a
  exact congrFun (hp.eq_of_comp_eq f.continuous g.continuous hcomp a₀ hbase) a

/-- Helper for Problem 3.9.1: the image of the base multiplication map on
`π₁(H × H, (e, e))` lands in the covering subgroup determined by `p`. -/
theorem mul_lift_range_le
    (he_mul : p e = covering_base_mul hp (e, e)) :
    (FundamentalGroup.map (covering_base_mul hp) (e, e)).range ≤
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he_mul).range := by
  intro x hx
  rcases MonoidHom.mem_range.mp hx with ⟨γ, rfl⟩
  refine Quotient.inductionOn γ ?_
  intro γ
  -- Route correction: normalize the covering criterion on explicit loop representatives.
  have he_one : p e = 1 := Set.mem_singleton_iff.mp e.2
  let γ₁ : Path (e : H) (e : H) := γ.map continuous_fst
  let γ₂ : Path (e : H) (e : H) := γ.map continuous_snd
  -- The normalized loop representative provides an explicit witness in the covering subgroup.
  refine MonoidHom.mem_range.mpr ?_
  refine ⟨FundamentalGroup.fromPath (.mk (γ₁.trans γ₂)), ?_⟩
  have hnorm :
      FundamentalGroup.map (covering_base_mul hp) ((e : H), (e : H))
          (FundamentalGroup.fromPath (.mk γ)) =
        FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he_mul
          (FundamentalGroup.fromPath (.mk (γ₁.trans γ₂))) := by
    rw [FundamentalGroup.mapOfEq_apply]
    change FundamentalGroup.fromPath (.mk (γ.map (covering_base_mul hp).continuous)) =
      FundamentalGroup.fromPath (.mk (((γ₁.trans γ₂).map hp.continuous).cast he_mul.symm he_mul.symm))
    apply congrArg FundamentalGroup.fromPath
    rw [Path.map_trans]
    have hmul :
        γ.map (covering_base_mul hp).continuous =
          (γ₁.map hp.continuous).mul (γ₂.map hp.continuous) := by
      ext t
      rfl
    rw [hmul]
    exact Path.Homotopic.Quotient.eq.mpr <| by
      simpa [he_one, covering_base_mul, γ₁, γ₂] using
        (loop_pointwise_mul_homotopic_trans
          ((γ₁.map hp.continuous).cast he_one.symm he_one.symm)
          ((γ₂.map hp.continuous).cast he_one.symm he_one.symm))
  simpa using hnorm.symm

/-- Problem 3.9.1 (1): for a connected locally path-connected covering space `H` over a
topological group `G`, the base multiplication has a unique continuous lift sending `(e, e)` to
`e`. The identity laws are then forced by uniqueness of lifts. -/
-- Proof sketch: apply the covering-space lifting theorem to the base multiplication
-- `fun z : H × H ↦ p z.1 * p z.2`, using the chosen point `(e, e)` over `1`. Uniqueness follows
-- from uniqueness of point-preserving lifts.
theorem existsUnique_liftedGroupMul
    : ∃! m : C(H × H, H), m (e, e) = e ∧
        ∀ z : H × H, p (m z) = p z.1 * p z.2 := by
  let _ : PathConnectedSpace H := PathConnectedSpace.of_locPathConnectedSpace
  let _ : LocPathConnectedSpace (H × H) := by
    refine LocPathConnectedSpace.of_bases
      (fun x : H × H ↦
        (LocPathConnectedSpace.path_connected_basis x.1).prod_nhds
          (LocPathConnectedSpace.path_connected_basis x.2)) ?_
    intro x i hi
    rcases i with ⟨u, v⟩
    rcases hi with ⟨hu, hv⟩
    rcases hu with ⟨-, hu_pc⟩
    rcases hv with ⟨-, hv_pc⟩
    rcases hu_pc with ⟨x₀, hx₀, hx₀_conn⟩
    rcases hv_pc with ⟨y₀, hy₀, hy₀_conn⟩
    refine ⟨(x₀, y₀), ⟨hx₀, hy₀⟩, ?_⟩
    intro z hz
    rcases hz with ⟨hz₁, hz₂⟩
    refine ⟨(hx₀_conn hz₁).somePath.prod (hy₀_conn hz₂).somePath, ?_⟩
    intro t
    exact ⟨(hx₀_conn hz₁).somePath_mem t, (hy₀_conn hz₂).somePath_mem t⟩
  let _ : PathConnectedSpace (H × H) := PathConnectedSpace.of_locPathConnectedSpace
  have he_mul : p e = covering_base_mul hp (e, e) := by
    -- The chosen point `e` lies over the identity, so the base multiplication also sends `(e,e)`
    -- to that identity.
    have he_one : p e = 1 := Set.mem_singleton_iff.mp e.2
    simpa [covering_base_mul, he_one]
  -- Apply the covering lifting criterion to the base multiplication map.
  rcases IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le
      (cov := hp) (f := covering_base_mul hp) (a₀ := (e, e)) (e₀ := e)
      (he := he_mul) (le := mul_lift_range_le (hp := hp) (e := e) he_mul) with
    ⟨m, hm, huniq⟩
  refine ⟨m, ?_, ?_⟩
  · refine ⟨hm.1, ?_⟩
    intro z
    -- Read the lift equation pointwise.
    exact congrArg (fun f : H × H → G ↦ f z) hm.2
  · intro m' hm'
    -- Any other point-preserving lift is equal by uniqueness in the lifting theorem.
    apply huniq
    refine ⟨hm'.1, ?_⟩
    ext z
    exact hm'.2 z

/-- The canonical lifted multiplication obtained from the unique existence statement. -/
noncomputable def liftedGroupMul
    : C(H × H, H) :=
  Classical.choose (ExistsUnique.exists (existsUnique_liftedGroupMul hp e))

/- The canonical lifted multiplication is the unique lift fixing `(e, e)` and covering the base
multiplication. -/
-- Proof sketch: apply `Classical.choose_spec` to the unique-existence theorem for
-- `liftedGroupMul`.
theorem liftedGroupMul_spec
    : liftedGroupMul hp e (e, e) = e ∧
        ∀ z : H × H, p (liftedGroupMul hp e z) = p z.1 * p z.2 := by
  -- Unpack the point-preserving lift chosen from the unique existence statement.
  exact Classical.choose_spec (ExistsUnique.exists (existsUnique_liftedGroupMul hp e))

/-- The canonical lifted multiplication is sent to multiplication in the base group by `p`. -/
theorem liftedGroupMul_lifts
    (z : H × H) :
    p (liftedGroupMul hp e z) = p z.1 * p z.2 :=
  (liftedGroupMul_spec hp e).2 z

/-- The canonical lifted multiplication sends `(e, e)` to `e`. -/
theorem liftedGroupMul_basepoint
    : liftedGroupMul hp e (e, e) = e :=
  (liftedGroupMul_spec hp e).1

/-- The chosen point `e` is a left identity for the canonical lifted multiplication. -/
-- Proof sketch: compare `x ↦ liftedGroupMul hp e (e, x)` with the identity map on `H`. Both
-- are lifts of `x ↦ p x` sending `e` to `e`, so uniqueness of lifts forces equality.
theorem liftedGroupMul_left_id
    (x : H) :
    liftedGroupMul hp e (e, x) = x := by
  let leftTranslate : C(H, H) :=
    { toFun := fun y ↦ liftedGroupMul hp e (e, y)
      continuous_toFun := by
        -- This map is the lifted multiplication restricted along `y ↦ (e, y)`.
        exact (liftedGroupMul hp e).continuous.comp (continuous_const.prodMk continuous_id) }
  have hcomp : p ∘ leftTranslate = p := by
    -- Both maps cover the same base map `y ↦ p y`.
    funext y
    have he_one : p e = 1 := Set.mem_singleton_iff.mp e.2
    simpa [leftTranslate, he_one] using liftedGroupMul_lifts hp e (e, y)
  have hbase : leftTranslate e = e := by
    -- The two lifts agree at the chosen point over the identity.
    simpa [leftTranslate] using liftedGroupMul_basepoint hp e
  have heq : leftTranslate = ContinuousMap.id H := by
    exact covering_lift_ext (hp := hp) (e := e) leftTranslate (ContinuousMap.id H) hcomp hbase
  simpa [leftTranslate] using congrArg (fun f : C(H, H) ↦ f x) heq

/-- The chosen point `e` is a right identity for the canonical lifted multiplication. -/
-- Proof sketch: compare `x ↦ liftedGroupMul hp e (x, e)` with the identity map on `H`. Both
-- are lifts of `x ↦ p x` sending `e` to `e`, so uniqueness of lifts forces equality.
theorem liftedGroupMul_right_id
    (x : H) :
    liftedGroupMul hp e (x, e) = x := by
  let rightTranslate : C(H, H) :=
    { toFun := fun y ↦ liftedGroupMul hp e (y, e)
      continuous_toFun := by
        -- This map is the lifted multiplication restricted along `y ↦ (y, e)`.
        exact (liftedGroupMul hp e).continuous.comp (continuous_id.prodMk continuous_const) }
  have hcomp : p ∘ rightTranslate = p := by
    -- Both maps cover the same base map `y ↦ p y`.
    funext y
    have he_one : p e = 1 := Set.mem_singleton_iff.mp e.2
    simpa [rightTranslate, he_one] using liftedGroupMul_lifts hp e (y, e)
  have hbase : rightTranslate e = e := by
    -- The two lifts agree at the chosen point over the identity.
    simpa [rightTranslate] using liftedGroupMul_basepoint hp e
  have heq : rightTranslate = ContinuousMap.id H := by
    exact covering_lift_ext (hp := hp) (e := e) rightTranslate (ContinuousMap.id H) hcomp hbase
  simpa [rightTranslate] using congrArg (fun f : C(H, H) ↦ f x) heq

/-- Problem 3.9.1 (2): the canonical lifted multiplication is associative; together with the
continuous inverse from (3), this gives a group structure on `H` with identity `e`. -/
-- Proof sketch: compare the two continuous lifts of the base map
-- `fun ((x, y), z) ↦ p x * p y * p z` obtained from the two bracketings. They agree at
-- `(e, e, e)`, so uniqueness of lifts forces them to coincide everywhere.
theorem liftedGroupMul_assoc
    (x y z : H) :
    liftedGroupMul hp e (liftedGroupMul hp e (x, y), z) =
      liftedGroupMul hp e (x, liftedGroupMul hp e (y, z)) := by
  let leftAssoc : C((H × H) × H, H) :=
    { toFun := fun t ↦ liftedGroupMul hp e (liftedGroupMul hp e (t.1.1, t.1.2), t.2)
      continuous_toFun := by
        -- Compose the lifted multiplication with itself along the left-associated pairing map.
        have hleft : Continuous fun t : (H × H) × H ↦ (t.1.1, t.1.2) := by
          exact continuous_fst.fst.prodMk continuous_fst.snd
        have hpair : Continuous fun t : (H × H) × H ↦
            (liftedGroupMul hp e (t.1.1, t.1.2), t.2) := by
          exact ((liftedGroupMul hp e).continuous.comp hleft).prodMk continuous_snd
        exact (liftedGroupMul hp e).continuous.comp hpair }
  let rightAssoc : C((H × H) × H, H) :=
    { toFun := fun t ↦ liftedGroupMul hp e (t.1.1, liftedGroupMul hp e (t.1.2, t.2))
      continuous_toFun := by
        -- Compose the lifted multiplication with itself along the right-associated pairing map.
        have hright : Continuous fun t : (H × H) × H ↦ (t.1.2, t.2) := by
          exact continuous_fst.snd.prodMk continuous_snd
        have hpair : Continuous fun t : (H × H) × H ↦
            (t.1.1, liftedGroupMul hp e (t.1.2, t.2)) := by
          exact continuous_fst.fst.prodMk ((liftedGroupMul hp e).continuous.comp hright)
        exact (liftedGroupMul hp e).continuous.comp hpair }
  have hcomp : p ∘ leftAssoc = p ∘ rightAssoc := by
    -- Both lifts cover the same ternary multiplication map in `G`.
    funext t
    rcases t with ⟨⟨x', y'⟩, z'⟩
    simp [leftAssoc, rightAssoc, liftedGroupMul_lifts, mul_assoc]
  have hbase : leftAssoc ((e, e), e) = rightAssoc ((e, e), e) := by
    -- The two lifts agree at the chosen basepoint triple.
    simp [leftAssoc, rightAssoc, liftedGroupMul_basepoint hp e]
  have heq : leftAssoc = rightAssoc := by
    exact covering_lift_ext (hp := hp) (e := e) leftAssoc rightAssoc hcomp hbase
  simpa [leftAssoc, rightAssoc] using congrArg (fun f : C((H × H) × H, H) ↦ f ((x, y), z)) heq

/-- Helper for Problem 3.9.1: the pointwise inverse loop at `1` represents the inverse class in
`π₁(G, 1)`. -/
theorem pointwise_inv_loop_class_mul_eq_one
    (δ : Path (1 : G) 1) :
    FundamentalGroup.fromPath (.mk δ) *
      FundamentalGroup.fromPath (.mk (δ.inv.cast inv_one.symm inv_one.symm)) = 1 := by
  let δinv : Path (1 : G) 1 := δ.inv.cast inv_one.symm inv_one.symm
  -- The pointwise product of a loop with its pointwise inverse is the constant loop.
  have hmul_refl :
      ((δinv.mul δ).cast (one_mul (1 : G)).symm (one_mul (1 : G)).symm) =
        Path.refl (1 : G) := by
    ext t
    simp [δinv, Path.mul, Path.inv_apply]
  -- Route correction: first identify the pointwise inverse loop as a genuine inverse class, and
  -- only afterward rewrite that inverse class as the reversed loop class.
  have hhom : (δinv.trans δ).Homotopic (Path.refl (1 : G)) := by
    have hmul := loop_pointwise_mul_homotopic_trans δinv δ
    rw [hmul_refl] at hmul
    simpa using hmul.symm
  -- Translate the homotopy statement into the group law on `π₁(G, 1)`.
  rw [show (1 : FundamentalGroup G (1 : G)) =
      FundamentalGroup.fromPath (.mk (Path.refl (1 : G))) by rfl]
  rw [← Path.Homotopic.Quotient.eq] at hhom
  simpa [δinv, loop_homotopy_mul_eq_trans, Path.Homotopic.Quotient.mk_trans] using hhom

/-- Helper for Problem 3.9.1: the casted pointwise inverse loop has the same class as path
reversal in `π₁(G, 1)`. -/
theorem pointwise_inv_loop_class_eq_symm
    (δ : Path (1 : G) 1) :
    FundamentalGroup.fromPath (.mk (δ.inv.cast inv_one.symm inv_one.symm)) =
      FundamentalGroup.fromPath (.mk δ.symm) := by
  -- First express the pointwise inverse loop class as the group inverse in `π₁(G, 1)`.
  have hinv :
      FundamentalGroup.fromPath (.mk (δ.inv.cast inv_one.symm inv_one.symm)) =
        (FundamentalGroup.fromPath (.mk δ))⁻¹ := by
    simpa using
      (inv_eq_of_mul_eq_one_right
        (pointwise_inv_loop_class_mul_eq_one (hp := hp) (e := e) (δ := δ))).symm
  -- Then rewrite inversion in the fundamental group as path reversal.
  have hsymm :
      (FundamentalGroup.fromPath (.mk δ))⁻¹ =
        FundamentalGroup.fromPath (.mk δ.symm) := by
    simpa using (loop_homotopy_inv_eq_symm (γ := FundamentalGroup.fromPath (.mk δ)))
  exact hinv.trans hsymm

/-- Helper for Problem 3.9.1: a normalized inverse-loop equality at basepoint `1` implies the
original inverse-loop equality for the covering-space basepoint. -/
theorem fromPath_inv_normalization_eq
    {γ : Path (e : H) (e : H)} {he_one : p e = 1}
    {hbase_inv : covering_base_inv hp e = 1}
    {he_inv : p e = covering_base_inv hp e}
    {he_inv_to_one : 1 = p e}
    (hmain :
      FundamentalGroup.fromPath (.mk (((γ.symm).map hp.continuous).cast
        he_inv_to_one he_inv_to_one)) =
        FundamentalGroup.fromPath (.mk ((γ.map (f := fun x ↦ (p x)⁻¹) (hp.continuous.inv)).cast
          hbase_inv.symm hbase_inv.symm))) :
    FundamentalGroup.fromPath (.mk (((γ.symm).map hp.continuous).cast
      he_inv.symm he_inv.symm)) =
      FundamentalGroup.fromPath (.mk (γ.map (f := fun x ↦ (p x)⁻¹) (hp.continuous.inv))) :=
  -- Route correction: move the equality to quotient classes, where endpoint casts compose
  -- transparently and the basepoint transport can be normalized by `cast_cast`.
  by
  have hmainQ := congrArg FundamentalGroup.toPath hmain
  have hcastQ := congrArg (fun q => q.cast hbase_inv hbase_inv) hmainQ
  -- The left-hand transport composes to the original endpoint equality `he_inv.symm`.
  have hleft_eq : hbase_inv.trans he_inv_to_one = he_inv.symm := by
    exact Subsingleton.elim _ _
  -- The right-hand transport goes from `covering_base_inv hp e` to `1` and back, so it cancels.
  have hright_eq : hbase_inv.trans hbase_inv.symm = rfl := by
    exact Subsingleton.elim _ _
  simpa [Path.Homotopic.Quotient.cast_cast, hleft_eq, hright_eq] using hcastQ

/-- Helper for Problem 3.9.1: the image of the base inversion map on `π₁(H, e)` lands in the
covering subgroup determined by `p`. -/
theorem inv_lift_range_le
    (he_inv : p e = covering_base_inv hp e) :
    (FundamentalGroup.map (covering_base_inv hp) e).range ≤
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he_inv).range := by
  intro x hx
  rcases MonoidHom.mem_range.mp hx with ⟨γ, rfl⟩
  refine Quotient.inductionOn γ ?_
  intro γ
  have he_one : p e = 1 := Set.mem_singleton_iff.mp e.2
  have hbase_inv : covering_base_inv hp e = 1 := by
    simpa [covering_base_inv, he_one]
  have he_inv_to_one : 1 = p e := by
    simpa [hbase_inv] using he_inv.symm
  let δ : Path (1 : G) 1 := (γ.map hp.continuous).cast he_one.symm he_one.symm
  -- The reversed representative `γ.symm` provides the explicit witness in the covering subgroup.
  refine MonoidHom.mem_range.mpr ?_
  refine ⟨FundamentalGroup.fromPath (.mk γ.symm), ?_⟩
  rw [FundamentalGroup.mapOfEq_apply]
  rw [FundamentalGroup.map_apply]
  -- Rewrite the ordinary fundamental-group map on `γ` to the explicit mapped loop.
  have hmap :
      Path.Homotopic.Quotient.map ⟦γ⟧ (covering_base_inv hp) =
        FundamentalGroup.fromPath (.mk (γ.map (covering_base_inv hp).continuous)) := by
    simpa using (Path.Homotopic.Quotient.mk_map (P₀ := γ) (f := covering_base_inv hp))
  rw [hmap]
  suffices hmain :
      FundamentalGroup.fromPath (.mk (((γ.symm).map hp.continuous).cast he_inv_to_one he_inv_to_one)) =
        FundamentalGroup.fromPath (.mk ((γ.map (covering_base_inv hp).continuous).cast
          hbase_inv.symm hbase_inv.symm)) by
    exact fromPath_inv_normalization_eq
      (hp := hp) (e := e) (γ := γ) (he_one := he_one)
      (hbase_inv := hbase_inv) (he_inv := he_inv)
      (he_inv_to_one := he_inv_to_one)
      (by simpa [covering_base_inv] using hmain)
  -- Normalize the mapped inverse loop to the casted pointwise inverse loop at basepoint `1`.
  have hleft :
      (γ.map (covering_base_inv hp).continuous).cast hbase_inv.symm hbase_inv.symm =
        δ.inv.cast inv_one.symm inv_one.symm := by
    ext t
    simp [δ, covering_base_inv, Path.inv_apply]
  -- Normalize the `mapOfEq` image of `γ.symm` to the reversed normalized loop `δ.symm`.
  have hright :
      ((γ.symm).map hp.continuous).cast he_inv_to_one he_inv_to_one = δ.symm := by
    ext t
    simp [δ]
  rw [hleft, pointwise_inv_loop_class_eq_symm (hp := hp) (e := e) (δ := δ)]
  rw [← hright]

/-- Problem 3.9.1 (3): the inversion map of `G` has a unique continuous lift fixing `e`; the
inverse laws for the lifted multiplication are then forced by uniqueness. -/
-- Proof sketch: lift the inversion map `fun x ↦ (p x)⁻¹` through the covering, using `e` over
-- `1`, and then compare the left- and right-inverse identities by uniqueness of lifts.
theorem existsUnique_liftedGroupInv
    : ∃! inv : C(H, H), inv e = e ∧
        ∀ x : H, p (inv x) = (p x)⁻¹ := by
  let _ : PathConnectedSpace H := PathConnectedSpace.of_locPathConnectedSpace
  have he_inv : p e = covering_base_inv hp e := by
    -- The chosen point `e` lies over the identity, so inversion also fixes the basepoint.
    have he_one : p e = 1 := Set.mem_singleton_iff.mp e.2
    simpa [covering_base_inv, he_one]
  -- Apply the covering lifting criterion to the base inversion map.
  rcases IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le
      (cov := hp) (f := covering_base_inv hp) (a₀ := e) (e₀ := e)
      (he := he_inv) (le := inv_lift_range_le (hp := hp) (e := e) he_inv) with
    ⟨inv, hinv, huniq⟩
  refine ⟨inv, ?_, ?_⟩
  · refine ⟨hinv.1, ?_⟩
    intro x
    -- Read the lift equation pointwise.
    exact congrArg (fun f : H → G ↦ f x) hinv.2
  · intro inv' hinv'
    -- Any other point-preserving lift is equal by uniqueness in the lifting theorem.
    apply huniq
    refine ⟨hinv'.1, ?_⟩
    ext x
    exact hinv'.2 x

/-- The canonical lifted inverse obtained from the unique existence statement. -/
noncomputable def liftedGroupInv
    : C(H, H) :=
  Classical.choose (ExistsUnique.exists (existsUnique_liftedGroupInv hp e))

/- The canonical lifted inverse is the unique lift fixing `e` and covering inversion in `G`. -/
-- Proof sketch: apply `Classical.choose_spec` to the unique-existence theorem for
-- `liftedGroupInv`.
theorem liftedGroupInv_spec
    : liftedGroupInv hp e e = e ∧
        ∀ x : H, p (liftedGroupInv hp e x) = (p x)⁻¹ := by
  -- Unpack the point-preserving lift chosen from the unique existence statement.
  exact Classical.choose_spec (ExistsUnique.exists (existsUnique_liftedGroupInv hp e))

/-- The canonical lifted inverse covers inversion in the base group. -/
theorem liftedGroupInv_lifts
    (x : H) :
    p (liftedGroupInv hp e x) = (p x)⁻¹ :=
  (liftedGroupInv_spec hp e).2 x

/-- The canonical lifted inverse fixes the chosen point `e`. -/
theorem liftedGroupInv_basepoint
    : liftedGroupInv hp e e = e :=
  (liftedGroupInv_spec hp e).1

/-- The canonical lifted inverse is a left inverse for the lifted multiplication. -/
-- Proof sketch: compare `x ↦ liftedGroupMul hp e (liftedGroupInv hp e x, x)` with the
-- constant map `e`. Both lift the constant map `1 : H → G` and agree at `e`.
theorem liftedGroupInv_left_inv
    (x : H) :
    liftedGroupMul hp e (liftedGroupInv hp e x, x) = e := by
  let leftInverseMap : C(H, H) :=
    { toFun := fun y ↦ liftedGroupMul hp e (liftedGroupInv hp e y, y)
      continuous_toFun := by
        -- Compose multiplication with the pair `(inv y, y)`.
        have hpair : Continuous fun y : H ↦ (liftedGroupInv hp e y, y) := by
          exact (liftedGroupInv hp e).continuous.prodMk continuous_id
        exact (liftedGroupMul hp e).continuous.comp hpair }
  let constE : C(H, H) :=
    { toFun := fun _ ↦ e
      continuous_toFun := continuous_const }
  have hcomp : p ∘ leftInverseMap = p ∘ constE := by
    -- Both lifts cover the constant map with value `1`.
    funext y
    have he_one : p e = 1 := Set.mem_singleton_iff.mp e.2
    simp [leftInverseMap, constE, liftedGroupMul_lifts, liftedGroupInv_lifts, he_one]
  have hbase : leftInverseMap e = constE e := by
    -- They also agree at the chosen lift of `1`.
    simp [leftInverseMap, constE, liftedGroupMul_basepoint hp e, liftedGroupInv_basepoint hp e]
  have heq : leftInverseMap = constE := by
    exact covering_lift_ext (hp := hp) (e := e) leftInverseMap constE hcomp hbase
  simpa [leftInverseMap, constE] using congrArg (fun f : C(H, H) ↦ f x) heq

/-- The canonical lifted inverse is a right inverse for the lifted multiplication. -/
-- Proof sketch: compare `x ↦ liftedGroupMul hp e (x, liftedGroupInv hp e x)` with the
-- constant map `e`. Both lift the constant map `1 : H → G` and agree at `e`.
theorem liftedGroupInv_right_inv
    (x : H) :
    liftedGroupMul hp e (x, liftedGroupInv hp e x) = e := by
  let rightInverseMap : C(H, H) :=
    { toFun := fun y ↦ liftedGroupMul hp e (y, liftedGroupInv hp e y)
      continuous_toFun := by
        -- Compose multiplication with the pair `(y, inv y)`.
        have hpair : Continuous fun y : H ↦ (y, liftedGroupInv hp e y) := by
          exact continuous_id.prodMk (liftedGroupInv hp e).continuous
        exact (liftedGroupMul hp e).continuous.comp hpair }
  let constE : C(H, H) :=
    { toFun := fun _ ↦ e
      continuous_toFun := continuous_const }
  have hcomp : p ∘ rightInverseMap = p ∘ constE := by
    -- Both lifts cover the constant map with value `1`.
    funext y
    have he_one : p e = 1 := Set.mem_singleton_iff.mp e.2
    simp [rightInverseMap, constE, liftedGroupMul_lifts, liftedGroupInv_lifts, he_one]
  have hbase : rightInverseMap e = constE e := by
    -- They also agree at the chosen lift of `1`.
    simp [rightInverseMap, constE, liftedGroupMul_basepoint hp e, liftedGroupInv_basepoint hp e]
  have heq : rightInverseMap = constE := by
    exact covering_lift_ext (hp := hp) (e := e) rightInverseMap constE hcomp hbase
  simpa [rightInverseMap, constE] using congrArg (fun f : C(H, H) ↦ f x) heq

/-- Problem 3.9.1, owner form: the lifted multiplication and inverse define a group structure on
`H` with identity `e`. -/
@[reducible] noncomputable def liftedGroup
    : Group H where
  mul x y := liftedGroupMul hp e (x, y)
  mul_assoc x y z := liftedGroupMul_assoc hp e x y z
  one := e
  one_mul x := liftedGroupMul_left_id hp e x
  mul_one x := liftedGroupMul_right_id hp e x
  inv := liftedGroupInv hp e
  inv_mul_cancel x := liftedGroupInv_left_inv hp e x

/-- Problem 3.9.1, owner form: the lifted group structure is topological because the chosen
multiplication and inverse were constructed as continuous maps. -/
@[reducible] noncomputable def liftedIsTopologicalGroup
    : letI : Group H := liftedGroup hp e
      IsTopologicalGroup H := by
  letI := liftedGroup hp e
  refine
    { continuous_mul := ?_
      continuous_inv := ?_ }
  · change Continuous fun z : H × H ↦ liftedGroupMul hp e z
    exact (liftedGroupMul hp e).continuous
  · change Continuous fun x : H ↦ liftedGroupInv hp e x
    exact (liftedGroupInv hp e).continuous

/-- Problem 3.9.1, canonical bridge: with the lifted group structure on `H`, the covering map is a
continuous group homomorphism. -/
noncomputable def liftedCoveringHom
    : letI : Group H := liftedGroup hp e
      letI : IsTopologicalGroup H := liftedIsTopologicalGroup hp e
      H →ₜ* G := by
  letI : Group H := liftedGroup hp e
  letI : IsTopologicalGroup H := liftedIsTopologicalGroup hp e
  exact
    { toFun := p
      map_one' := by
        change p e = 1
        exact Set.mem_singleton_iff.mp e.2
      map_mul' := fun x y ↦ by
        change p (liftedGroupMul hp e (x, y)) = p x * p y
        simpa using liftedGroupMul_lifts hp e (x, y)
      continuous_toFun := hp.continuous }

/-- The canonical lifted covering homomorphism is the original underlying map `p`. -/
@[simp] theorem liftedCoveringHom_apply
    (x : H) :
    liftedCoveringHom hp e x = p x :=
  by
    change p x = p x
    rfl

end

section

variable {H : Type u} {G : Type v}
  [TopologicalSpace H] [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G]
  [ConnectedSpace H] [LocPathConnectedSpace H]
  {p : H → G}

variable (hp : IsCoveringMap p) (e : p ⁻¹' ({1} : Set G))

include hp e

/-- Helper for Problem 3.9.1: the swapped lifted multiplication covers the same base
multiplication map when the base group is commutative. -/
theorem swapped_liftedGroupMul_lifts
    (z : H × H) :
    p (({ toFun := fun w : H × H ↦ liftedGroupMul hp e (w.2, w.1)
          continuous_toFun :=
            (liftedGroupMul hp e).continuous.comp (continuous_snd.prodMk continuous_fst) } :
        C(H × H, H)) z) =
      p z.1 * p z.2 := by
  -- Swapping the arguments only changes the order of multiplication in the abelian base group.
  simpa [mul_comm] using liftedGroupMul_lifts hp e (z.2, z.1)

/-- Problem 3.9.1 (4): if the base topological group `G` is abelian, then the canonical lifted
multiplication on `H` is commutative, so `H` is abelian as well. -/
-- Proof sketch: compare the two continuous lifts of the commutative base multiplication
-- `fun z : H × H ↦ p z.1 * p z.2`, namely `liftedGroupMul hp e` and
-- `fun z ↦ liftedGroupMul hp e (z.2, z.1)`. In the commutative base group they cover the same map
-- and both send `(e, e)` to `e`, so uniqueness forces them to agree.
theorem liftedGroupMul_comm
    (x y : H) :
    liftedGroupMul hp e (x, y) =
      liftedGroupMul hp e (y, x) := by
  let _ : PathConnectedSpace H := PathConnectedSpace.of_locPathConnectedSpace
  let _ : LocPathConnectedSpace (H × H) := by
    refine LocPathConnectedSpace.of_bases
      (fun x : H × H ↦
        (LocPathConnectedSpace.path_connected_basis x.1).prod_nhds
          (LocPathConnectedSpace.path_connected_basis x.2)) ?_
    intro x i hi
    rcases i with ⟨u, v⟩
    rcases hi with ⟨hu, hv⟩
    rcases hu with ⟨-, hu_pc⟩
    rcases hv with ⟨-, hv_pc⟩
    rcases hu_pc with ⟨x₀, hx₀, hx₀_conn⟩
    rcases hv_pc with ⟨y₀, hy₀, hy₀_conn⟩
    refine ⟨(x₀, y₀), ⟨hx₀, hy₀⟩, ?_⟩
    intro z hz
    rcases hz with ⟨hz₁, hz₂⟩
    refine ⟨(hx₀_conn hz₁).somePath.prod (hy₀_conn hz₂).somePath, ?_⟩
    intro t
    exact ⟨(hx₀_conn hz₁).somePath_mem t, (hy₀_conn hz₂).somePath_mem t⟩
  let _ : PathConnectedSpace (H × H) := PathConnectedSpace.of_locPathConnectedSpace
  let swapMul : C(H × H, H) :=
    { toFun := fun z ↦ liftedGroupMul hp e (z.2, z.1)
      continuous_toFun := (liftedGroupMul hp e).continuous.comp (continuous_snd.prodMk continuous_fst) }
  have hcomp : p ∘ swapMul = p ∘ liftedGroupMul hp e := by
    -- Both maps cover the same base multiplication map because `G` is commutative.
    funext z
    calc
      p (swapMul z) = p z.1 * p z.2 := by
        simpa [swapMul] using swapped_liftedGroupMul_lifts (hp := hp) (e := e) z
      _ = p (liftedGroupMul hp e z) := by
        symm
        exact liftedGroupMul_lifts hp e z
  have hbase : swapMul (e, e) = liftedGroupMul hp e (e, e) := by
    -- The two lifts agree at the chosen point over the identity.
    simp [swapMul, liftedGroupMul_basepoint hp e]
  have heq : swapMul = liftedGroupMul hp e := by
    -- Uniqueness of lifts on the preconnected product domain forces equality.
    exact covering_lift_ext (hp := hp) (e := e) swapMul (liftedGroupMul hp e) hcomp hbase
  simpa [swapMul] using congrArg (fun f : C(H × H, H) ↦ f (x, y)) heq.symm

/-- If the base group is commutative, the lifted group structure upgrades to a commutative group. -/
@[reducible] noncomputable def liftedCommGroup :
    CommGroup H :=
  { liftedGroup hp e with
    mul_comm := liftedGroupMul_comm hp e }

end
