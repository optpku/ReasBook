/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped SupportFunction

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

/- Lemma 7.1 lies in the finite-range support-function / pullback-seminorm domain.

Sampled owner declarations:
- `ξ[Q]` and `supportFunction_apply` from `Chap03/Definition_3_9`
- `Seminorm.comp` and `normSeminorm` for canonical pullback seminorms
- `LinearMap.pi` and `EuclideanSpace.equiv` for the canonical finite row map into
  `EuclideanSpace ℝ (Fin m)`
- `SatisfiesAsphericityCondition` from `Chap07/Definition_7_7`
- `Seminorm.IsNorm` from `Chap02/Definition_2_5`, recalled in `Chap07/Definition_7_84`

Best owner abstraction:
- source-facing: the Chapter 3 support function `ξ[Set.range a]` and the Euclidean pullback
  seminorm attached to the finite row family `a`
- core/canonical: `ξ[Set.range a]`, `Seminorm.comp`, `LinearMap.pi`, and `EuclideanSpace.equiv`
- bridge/view: the concrete `sSup` and `sqrt` evaluation formulas below

Primitive data:
- a finite family `a : Fin m → E`

Derived API kept here:
- the finite-range evaluation of the support function
- the coordinate formula for the canonical pullback seminorm
- the norm / asphericity statement of Lemma 7.1

This refinement removes the previous public convenience owners
`polyhedralMaxFunction`, `rowInnerMap`, and `rowInnerSeminorm`. The public surface is stated
directly with the established Chapter 3 support-function owner and the canonical pullback-seminorm
construction instead of parallel wrapper names.
-/

section

variable (a : Fin m → E)

/-- Evaluating the Chapter 3 support-function owner on the finite set `Set.range a` recovers the
supremum of the finitely many inner products `⟪aᵢ, x⟫`. -/
theorem supportFunction_range_toReal_eq_sSup_inner (x : E) :
    (ξ[Set.range a] x).toReal = sSup (Set.range fun i : Fin m ↦ inner ℝ (a i) x) := by
  classical
  by_cases hm : Nonempty (Fin m)
  · let M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i : Fin m ↦ inner ℝ (a i) x)
    -- Compare the `EReal` support-function value with the attained finite maximum `M`.
    have hupper : ξ[Set.range a] x ≤ (M : EReal) := by
      rw [supportFunction_apply]
      refine sSup_le ?_
      rintro _ ⟨y, ⟨i, rfl⟩, rfl⟩
      exact show (((inner ℝ (a i) x : ℝ) : EReal) ≤ (M : EReal)) by
        exact_mod_cast
          (Finset.le_sup'_of_le (fun j : Fin m ↦ inner ℝ (a j) x) (by simp : i ∈ Finset.univ)
            le_rfl)
    have hlower : (M : EReal) ≤ ξ[Set.range a] x := by
      obtain ⟨i, -, hi⟩ :=
        Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j : Fin m ↦ inner ℝ (a j) x)
      rw [supportFunction_apply]
      have hi_mem :
          (((inner ℝ (a i) x : ℝ) : EReal)) ≤
            sSup ((fun g : E ↦ ((inner ℝ g x : ℝ) : EReal)) '' Set.range a) :=
        le_sSup ⟨a i, Set.mem_range_self i, rfl⟩
      have hM : (M : EReal) = (((inner ℝ (a i) x : ℝ) : EReal)) := by
        exact_mod_cast hi
      calc
        (M : EReal) = (((inner ℝ (a i) x : ℝ) : EReal)) := hM
        _ ≤ sSup ((fun g : E ↦ ((inner ℝ g x : ℝ) : EReal)) '' Set.range a) := hi_mem
    have hξ : ξ[Set.range a] x = (M : EReal) := le_antisymm hupper hlower
    -- Rewrite the finite maximum back as the `sSup` over the finite range.
    have hM :
        M = sSup (Set.range fun i : Fin m ↦ inner ℝ (a i) x) := by
      simpa [M] using
        (Finset.sup'_eq_csSup_image Finset.univ Finset.univ_nonempty
          (fun i : Fin m ↦ inner ℝ (a i) x))
    simpa [hM] using congrArg EReal.toReal hξ
  · -- If the index type is empty, both sides are the supremum of the empty family, hence `0`.
    let hEmpty : IsEmpty (Fin m) := not_nonempty_iff.mp hm
    have hrange :
        Set.range (fun i : Fin m ↦ inner ℝ (a i) x) = (∅ : Set ℝ) := by
      ext t
      constructor
      · rintro ⟨i, rfl⟩
        exact (hEmpty.false i).elim
      · simp
    have hfamily :
        ((fun g : E ↦ ((inner ℝ g x : ℝ) : EReal)) '' Set.range a) = (∅ : Set EReal) := by
      ext t
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact (hEmpty.false i).elim
      · simp
    rw [supportFunction_apply, hfamily, hrange]
    simp

/- The single structural map used in Lemma 7.1: it records the row inner products as a vector in
`EuclideanSpace ℝ (Fin m)`. -/
private def rowInnerMap : E →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
  (((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap).comp
    (LinearMap.pi fun i ↦ (innerSL ℝ (a i)).toLinearMap))

@[simp] private theorem rowInnerMap_apply (x : E) (i : Fin m) :
    rowInnerMap a x i = inner ℝ (a i) x := by
  -- The chosen row map is definitionally the coordinate family `i ↦ ⟪aᵢ, x⟫`.
  simp [rowInnerMap]

-- Proof sketch: rewrite the pullback seminorm as the Euclidean norm of the finite row map
-- `((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap).comp
--   (LinearMap.pi fun i ↦ (innerSL ℝ (a i)).toLinearMap)` applied to `x`, then expand the
-- Euclidean norm coordinatewise.
/-- The canonical Euclidean pullback seminorm attached to `a` evaluates to the square root of the
summed squared inner products `∑ i ⟪aᵢ, x⟫²`. -/
theorem pullbackSeminorm_eq_sqrt_sum_inner_sq (x : E) :
    let p : Seminorm ℝ E :=
      Seminorm.comp
        (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
        (((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap).comp
          (LinearMap.pi fun i ↦ (innerSL ℝ (a i)).toLinearMap))
    p x =
      Real.sqrt (∑ i : Fin m, (inner ℝ (a i) x) ^ 2) := by
  -- Expand the pullback seminorm to the Euclidean norm of the row map.
  dsimp [rowInnerMap]
  -- Then read that Euclidean norm coordinatewise.
  simpa [Real.norm_eq_abs, sq_abs] using
    (EuclideanSpace.norm_eq
      ((((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap).comp
          (LinearMap.pi fun i ↦ (innerSL ℝ (a i)).toLinearMap)) x))

/-- Helper for Lemma 7.1: if the rows span the whole space, then the Euclidean pullback seminorm
is separated and therefore is a norm. -/
theorem pullback_seminorm_isNorm_of_span_eq_top
    (hfull_row_rank : Submodule.span ℝ (Set.range a) = ⊤) :
    let p : Seminorm ℝ E :=
      Seminorm.comp
        (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
        (rowInnerMap a)
    Seminorm.IsNorm p := by
  let p : Seminorm ℝ E := Seminorm.comp (normSeminorm ℝ (EuclideanSpace ℝ (Fin m))) (rowInnerMap a)
  refine ⟨?_⟩
  intro x hx
  have hx_map : rowInnerMap a x = 0 := by
    apply norm_eq_zero.mp
    simpa [p] using hx
  -- The row map vanishing says that `x` is orthogonal to every row, hence to their span.
  have hx_orthogonal : x ∈ (Submodule.span ℝ (Set.range a))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨i, rfl⟩
        have hcoord : rowInnerMap a x i = 0 := by
          exact congrArg (fun v ↦ v i) hx_map
        simpa [rowInnerMap_apply] using hcoord
    | zero =>
        simp
    | add y z hy hz hy_zero hz_zero =>
        simp [inner_add_left, hy_zero, hz_zero]
    | smul c y hy hy_zero =>
        simp [real_inner_smul_left, hy_zero]
  have hx_top : x ∈ (⊤ : Submodule ℝ E)ᗮ := by
    simpa [hfull_row_rank] using hx_orthogonal
  rw [Submodule.top_orthogonal_eq_bot] at hx_top
  simpa using hx_top

/-- Helper for Lemma 7.1: the finite support function is pointwise bounded by the Euclidean
pullback seminorm coming from the row inner-product map. -/
theorem supportFunction_range_toReal_le_pullbackSeminorm
    (hm : 0 < m) :
    let p : Seminorm ℝ E :=
      Seminorm.comp
        (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
        (rowInnerMap a)
    ∀ x : E, (ξ[Set.range a] x).toReal ≤ p x := by
  let p : Seminorm ℝ E := Seminorm.comp (normSeminorm ℝ (EuclideanSpace ℝ (Fin m))) (rowInnerMap a)
  change ∀ x : E, (ξ[Set.range a] x).toReal ≤ p x
  intro x
  have hnonempty : (Set.range fun i : Fin m ↦ inner ℝ (a i) x).Nonempty := by
    obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hm
    exact ⟨inner ℝ (a i) x, ⟨i, rfl⟩⟩
  -- Each coordinate of the Euclidean row vector is bounded by its Euclidean norm.
  have hcoord_bound (i : Fin m) : inner ℝ (a i) x ≤ p x := by
    have hbasis :
        |inner ℝ ((EuclideanSpace.basisFun (Fin m) ℝ) i) (rowInnerMap a x)| ≤
          ‖rowInnerMap a x‖ := by
      calc
        |inner ℝ ((EuclideanSpace.basisFun (Fin m) ℝ) i) (rowInnerMap a x)| ≤
            ‖(EuclideanSpace.basisFun (Fin m) ℝ) i‖ * ‖rowInnerMap a x‖ :=
          abs_real_inner_le_norm _ _
        _ = ‖rowInnerMap a x‖ := by simp
    have hcoord :
        inner ℝ (a i) x ≤ ‖rowInnerMap a x‖ := by
      have hrewrite :
          inner ℝ (a i) x =
            inner ℝ ((EuclideanSpace.basisFun (Fin m) ℝ) i) (rowInnerMap a x) := by
        calc
          inner ℝ (a i) x = rowInnerMap a x i := by simp [rowInnerMap_apply]
          _ = inner ℝ ((EuclideanSpace.basisFun (Fin m) ℝ) i) (rowInnerMap a x) := by
                symm
                simpa using
                  (EuclideanSpace.basisFun_inner
                    (ι := Fin m) (𝕜 := ℝ) (x := rowInnerMap a x) (i := i))
      calc
        inner ℝ (a i) x =
            inner ℝ ((EuclideanSpace.basisFun (Fin m) ℝ) i) (rowInnerMap a x) := hrewrite
        _ ≤ |inner ℝ ((EuclideanSpace.basisFun (Fin m) ℝ) i) (rowInnerMap a x)| :=
              le_abs_self _
        _ ≤ ‖rowInnerMap a x‖ := hbasis
    simpa [p] using hcoord
  -- The support value is the supremum of those coordinates, so the same bound passes to `sSup`.
  rw [supportFunction_range_toReal_eq_sSup_inner]
  exact csSup_le hnonempty fun b hb ↦ by
    rcases hb with ⟨i, rfl⟩
    exact hcoord_bound i

/-- Helper for Lemma 7.1: every supporting functional at the origin of the finite support function
belongs to the dual closed ball of radius `1` for the pullback seminorm. -/
theorem supporting_functional_mem_dualClosedBall_one
    (hm : 0 < m) {g : StrongDual ℝ E}
    (hg : ∀ y : E, (ξ[Set.range a] (0 : E)).toReal + g y ≤ (ξ[Set.range a] y).toReal) :
    let p : Seminorm ℝ E :=
      Seminorm.comp
        (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
        (rowInnerMap a)
    g ∈ dualClosedBall p 1 := by
  let p : Seminorm ℝ E := Seminorm.comp (normSeminorm ℝ (EuclideanSpace ℝ (Fin m))) (rowInnerMap a)
  change g ∈ dualClosedBall p 1
  -- Route correction: the intended proof applies the support inequality to `x` and `-x`,
  -- bounds the finite support function by the Euclidean row norm, and then rewrites that row norm
  -- through `pullbackSeminorm_eq_sqrt_sum_inner_sq`.
  rw [mem_dualClosedBall_iff]
  have hzero : (ξ[Set.range a] (0 : E)).toReal = 0 := by
    rw [supportFunction_range_toReal_eq_sSup_inner (a := a) (x := (0 : E))]
    have hzero_range : Set.range (fun _ : Fin m ↦ (0 : ℝ)) = {0} := by
      ext t
      constructor
      · rintro ⟨i, rfl⟩
        simp
      · intro ht
        have ht0 : t = 0 := by simpa using ht
        obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hm
        simpa [ht0] using
          (show (0 : ℝ) ∈ Set.range (fun _ : Fin m ↦ (0 : ℝ)) from ⟨i, rfl⟩)
    simp [hzero_range]
  intro x
  have hx_upper :
      g x ≤ p x := by
    have hx_support : g x ≤ (ξ[Set.range a] x).toReal := by
      linarith [hg x, hzero]
    calc
      g x ≤ (ξ[Set.range a] x).toReal := hx_support
      _ ≤ p x := supportFunction_range_toReal_le_pullbackSeminorm (a := a) hm x
  have hx_lower :
      -p x ≤ g x := by
    have hneg_upper :
        g (-x) ≤ p (-x) := by
      have hneg_support : g (-x) ≤ (ξ[Set.range a] (-x)).toReal := by
        linarith [hg (-x), hzero]
      calc
        g (-x) ≤ (ξ[Set.range a] (-x)).toReal := hneg_support
        _ ≤ p (-x) := supportFunction_range_toReal_le_pullbackSeminorm (a := a) hm (-x)
    have hneg_upper' : -g x ≤ p x := by
      simpa [p] using hneg_upper
    linarith
  simpa [p] using (abs_le.mpr ⟨hx_lower, hx_upper⟩)

/-- Helper for Lemma 7.1: a dual-ball functional vanishes on the kernel of the row map, so the
source route may pass to the row-image before applying Hahn-Banach. -/
theorem dualClosedBall_functional_eq_zero_on_row_kernel
    {γ : ℝ} {g : StrongDual ℝ E}
    (hg : g ∈ dualClosedBall
      (Seminorm.comp
        (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
        (rowInnerMap a))
      γ) :
    ∀ x : E, rowInnerMap a x = 0 → g x = 0 := by
  -- Rewrite the dual-ball hypothesis as the pointwise bound defining the source-side ball.
  rw [mem_dualClosedBall_iff] at hg
  intro x hx
  have hbound := hg x
  -- If the row map vanishes, the pullback seminorm vanishes as well.
  have hp :
      (Seminorm.comp
        (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
        (rowInnerMap a)) x = 0 := by
    simp [Seminorm.comp_apply, hx]
  have habs : |g x| ≤ 0 := by
    simpa [hp] using hbound
  exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))

/-- Helper for Lemma 7.1: once a dual-ball functional kills the row kernel, it depends only on
the row-image point. -/
theorem dualClosedBall_functional_eq_of_rowInnerMap_eq
    {γ : ℝ} {g : StrongDual ℝ E}
    (hg : g ∈ dualClosedBall
      (Seminorm.comp
        (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
        (rowInnerMap a))
      γ)
    {x y : E} (hxy : rowInnerMap a x = rowInnerMap a y) :
    g x = g y := by
  -- Compare `x` and `y` through their difference, which lies in the row-kernel.
  have hkernel : rowInnerMap a (x - y) = 0 := by
    simp [LinearMap.map_sub, hxy]
  have hzero :
      g (x - y) = 0 :=
    dualClosedBall_functional_eq_zero_on_row_kernel (a := a) hg (x - y) hkernel
  have hsub : g x - g y = 0 := by
    simpa using hzero
  linarith

/-- Helper for Lemma 7.1: the source-side dual-ball estimate descends the functional to the row
range with the same operator-norm bound. -/
theorem dualClosedBall_functional_descends_to_row_range
    {γ : ℝ} (hγ : 0 ≤ γ) {g : StrongDual ℝ E}
    (hg : g ∈ dualClosedBall
      (Seminorm.comp
        (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
        (rowInnerMap a))
      γ) :
    ∃ ψ : StrongDual ℝ (LinearMap.range (rowInnerMap a)),
      (∀ x : E, ψ ((rowInnerMap a).rangeRestrict x) = g x) ∧ ‖ψ‖ ≤ γ := by
  classical
  let pre : LinearMap.range (rowInnerMap a) → E := fun z =>
    Classical.choose ((LinearMap.surjective_rangeRestrict (f := rowInnerMap a)) z)
  have hpre : ∀ z : LinearMap.range (rowInnerMap a),
      (rowInnerMap a).rangeRestrict (pre z) = z := by
    intro z
    exact Classical.choose_spec ((LinearMap.surjective_rangeRestrict (f := rowInnerMap a)) z)
  let ψlin : LinearMap.range (rowInnerMap a) →ₗ[ℝ] ℝ :=
    { toFun := fun z ↦ g (pre z)
      map_add' := by
        intro z₁ z₂
        -- The chosen preimages of `z₁ + z₂` and of `z₁`, `z₂` represent the same row-image.
        have hrow :
            rowInnerMap a (pre (z₁ + z₂)) = rowInnerMap a (pre z₁ + pre z₂) := by
          have hrestrict :
              (rowInnerMap a).rangeRestrict (pre (z₁ + z₂)) =
                (rowInnerMap a).rangeRestrict (pre z₁ + pre z₂) := by
            rw [hpre, LinearMap.map_add, hpre, hpre]
          exact congrArg Subtype.val hrestrict
        calc
          g (pre (z₁ + z₂)) = g (pre z₁ + pre z₂) :=
            dualClosedBall_functional_eq_of_rowInnerMap_eq (a := a) hg hrow
          _ = g (pre z₁) + g (pre z₂) := by simp
      map_smul' := by
        intro c z
        -- The same row-image comparison also handles scalar multiples.
        have hrow :
            rowInnerMap a (pre (c • z)) = rowInnerMap a (c • pre z) := by
          have hrestrict :
              (rowInnerMap a).rangeRestrict (pre (c • z)) =
                (rowInnerMap a).rangeRestrict (c • pre z) := by
            rw [hpre, LinearMap.map_smul, hpre]
          exact congrArg Subtype.val hrestrict
        calc
          g (pre (c • z)) = g (c • pre z) :=
            dualClosedBall_functional_eq_of_rowInnerMap_eq (a := a) hg hrow
          _ = c * g (pre z) := by simp }
  have hg' := (mem_dualClosedBall_iff _ _ _).1 hg
  have hψlin_bound : ∀ z : LinearMap.range (rowInnerMap a), ‖ψlin z‖ ≤ γ * ‖z‖ := by
    intro z
    -- Read the original dual-ball estimate on the chosen preimage and rewrite its seminorm value
    -- as the norm of the row-image point `z`.
    have hbound := hg' (pre z)
    have hp :
        (Seminorm.comp
          (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
          (rowInnerMap a)) (pre z) = ‖z‖ := by
      change ‖rowInnerMap a (pre z)‖ = ‖z‖
      exact congrArg norm (congrArg Subtype.val (hpre z))
    simpa [ψlin, Real.norm_eq_abs, hp] using hbound
  let ψ : StrongDual ℝ (LinearMap.range (rowInnerMap a)) := ψlin.mkContinuous γ hψlin_bound
  refine ⟨ψ, ?_, ?_⟩
  · intro x
    -- The descended functional agrees with `g` because both chosen preimages have the same row
    -- image.
    have hrow :
        rowInnerMap a (pre ((rowInnerMap a).rangeRestrict x)) = rowInnerMap a x := by
      exact congrArg Subtype.val (hpre ((rowInnerMap a).rangeRestrict x))
    calc
      ψ ((rowInnerMap a).rangeRestrict x) = g (pre ((rowInnerMap a).rangeRestrict x)) := by
        rfl
      _ = g x := dualClosedBall_functional_eq_of_rowInnerMap_eq (a := a) hg hrow
  · -- Package the same bound as an operator-norm estimate for the descended continuous functional.
    simpa [ψ] using LinearMap.mkContinuous_norm_le ψlin hγ hψlin_bound

/-- Helper for Lemma 7.1: after descending to the row range, Hahn-Banach and the Riesz map produce
a coefficient vector on `Fin m` representing the functional on every row-image point. -/
theorem row_range_functional_has_euclidean_coefficients
    {γ : ℝ} {ψ : StrongDual ℝ (LinearMap.range (rowInnerMap a))}
    (hψ : ‖ψ‖ ≤ γ) :
    ∃ u : EuclideanSpace ℝ (Fin m),
      ‖u‖ ≤ γ ∧
        ∀ y : E,
          ψ ((rowInnerMap a).rangeRestrict y) =
            ∑ i : Fin m, u i * inner ℝ (a i) y := by
  obtain ⟨ψext, hψext_apply, hψext_norm⟩ :=
    Real.exists_extension_norm_eq (LinearMap.range (rowInnerMap a)) ψ
  let u : EuclideanSpace ℝ (Fin m) := (InnerProductSpace.toDual ℝ _).symm ψext
  refine ⟨u, ?_, ?_⟩
  · -- The representing vector inherits the same norm bound through Hahn-Banach and Riesz.
    calc
      ‖u‖ = ‖ψext‖ := by simp [u]
      _ = ‖ψ‖ := hψext_norm
      _ ≤ γ := hψ
  · intro y
    -- Evaluate the Hahn-Banach extension on the row-image and rewrite it by the Riesz formula.
    calc
      ψ ((rowInnerMap a).rangeRestrict y) = ψext ((rowInnerMap a).rangeRestrict y) := by
        symm
        exact hψext_apply ((rowInnerMap a).rangeRestrict y)
      _ = inner ℝ u (rowInnerMap a y) := by
        simp [u]
      _ = ∑ i : Fin m, u i * inner ℝ (a i) y := by
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl ?_
        intro i hi
        change inner ℝ (u.ofLp i) (inner ℝ (a i) y) = u.ofLp i * inner ℝ (a i) y
        simpa using
          (RCLike.inner_apply' (x := u.ofLp i) (y := inner ℝ (a i) y))

/-- Helper for Lemma 7.1: subtracting the mean from a coefficient vector produces a zero-sum
family. -/
theorem recentered_coefficients_sum_zero
    (hm : 0 < m) (u : EuclideanSpace ℝ (Fin m)) :
    let μ : ℝ := (∑ j : Fin m, u j) / m
    let v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun i : Fin m ↦ u i - μ)
    ∑ i : Fin m, v i = 0 := by
  dsimp
  have hm_ne : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hmul : (m : ℝ) * ((∑ j : Fin m, u j) / m) = ∑ j : Fin m, u j := by
    field_simp [hm_ne]
  -- Expand the centered sum and evaluate the constant term using the cardinality of `Fin m`.
  calc
    ∑ i : Fin m, (u i - (∑ j : Fin m, u j) / m)
        = (∑ i : Fin m, u i) - ∑ i : Fin m, ((∑ j : Fin m, u j) / m) := by
            rw [Finset.sum_sub_distrib]
    _ = (∑ i : Fin m, u i) - (m : ℝ) * ((∑ j : Fin m, u j) / m) := by
            simp
    _ = (∑ i : Fin m, u i) - ∑ j : Fin m, u j := by
            rw [hmul]
    _ = 0 := by
            ring

/-- Helper for Lemma 7.1: recentering the coefficient vector does not change the represented
functional because the row family sums to zero. -/
theorem recentered_coefficients_preserve_functional
    (hzero_sum : ∑ i : Fin m, a i = 0) (u : EuclideanSpace ℝ (Fin m)) :
    let μ : ℝ := (∑ j : Fin m, u j) / m
    let v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun i : Fin m ↦ u i - μ)
    ∀ y : E,
      (∑ i : Fin m, u i * inner ℝ (a i) y) =
        ∑ i : Fin m, v i * inner ℝ (a i) y := by
  dsimp
  intro y
  have hsum_inner : ∑ i : Fin m, inner ℝ (a i) y = 0 := by
    -- Apply the inner product to the zero-sum relation `∑ i, a i = 0`.
    have hinner_zero := congrArg (fun z : E ↦ inner ℝ z y) hzero_sum
    simpa [sum_inner] using hinner_zero
  let μ : ℝ := (∑ j : Fin m, u j) / m
  let v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun i : Fin m ↦ u i - μ)
  -- Rewrite the original coefficients as the centered coefficients plus the constant mean shift.
  calc
    ∑ i : Fin m, u i * inner ℝ (a i) y = ∑ i : Fin m, ((v i + μ) * inner ℝ (a i) y) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [v, μ]
    _ = ∑ i : Fin m, (v i * inner ℝ (a i) y + μ * inner ℝ (a i) y) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    _ = (∑ i : Fin m, v i * inner ℝ (a i) y) + ∑ i : Fin m, μ * inner ℝ (a i) y := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin m, v i * inner ℝ (a i) y) + μ * ∑ i : Fin m, inner ℝ (a i) y := by
      rw [Finset.mul_sum]
    _ = ∑ i : Fin m, v i * inner ℝ (a i) y := by
      rw [hsum_inner, mul_zero, add_zero]
    _ = ∑ i : Fin m, (u i - (∑ j : Fin m, u j) / m) * inner ℝ (a i) y := by
      simp [v, μ]

/-- Helper for Lemma 7.1: recentering a coefficient vector subtracts exactly the variance term
`m * μ^2` from the sum of squares. -/
theorem recentered_coefficients_sq_sum
    (hm : 0 < m) (u : EuclideanSpace ℝ (Fin m)) :
    let μ : ℝ := (∑ j : Fin m, u j) / m
    let v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun i : Fin m ↦ u i - μ)
    ∑ i : Fin m, (v i) ^ 2 = ∑ i : Fin m, (u i) ^ 2 - (m : ℝ) * μ ^ 2 := by
  dsimp
  have hm_ne : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hsum_u :
      ∑ i : Fin m, u i = (m : ℝ) * ((∑ j : Fin m, u j) / m) := by
    field_simp [hm_ne]
  -- Expand the centered square coordinatewise and collect the constant and linear terms.
  calc
    ∑ i : Fin m, (u i - (∑ j : Fin m, u j) / m) ^ 2
        = ∑ i : Fin m,
            (((u i) ^ 2 - 2 * ((∑ j : Fin m, u j) / m) * u i) +
              ((∑ j : Fin m, u j) / m) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
    _ = (∑ i : Fin m, ((u i) ^ 2 - 2 * ((∑ j : Fin m, u j) / m) * u i)) +
          ∑ i : Fin m, ((∑ j : Fin m, u j) / m) ^ 2 := by
            rw [Finset.sum_add_distrib]
    _ = ((∑ i : Fin m, (u i) ^ 2) - ∑ i : Fin m, 2 * ((∑ j : Fin m, u j) / m) * u i) +
          ∑ i : Fin m, ((∑ j : Fin m, u j) / m) ^ 2 := by
            rw [Finset.sum_sub_distrib]
    _ = ((∑ i : Fin m, (u i) ^ 2) - (2 * ((∑ j : Fin m, u j) / m)) * (∑ i : Fin m, u i)) +
          (m : ℝ) * ((∑ j : Fin m, u j) / m) ^ 2 := by
            rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ]
            rw [Fintype.card_fin, nsmul_eq_mul]
    _ = ((∑ i : Fin m, (u i) ^ 2) -
          (2 * ((∑ j : Fin m, u j) / m)) * ((m : ℝ) * ((∑ j : Fin m, u j) / m))) +
          (m : ℝ) * ((∑ j : Fin m, u j) / m) ^ 2 := by
            nth_rewrite 2 [hsum_u]
            rfl
    _ = ∑ i : Fin m, (u i) ^ 2 - (m : ℝ) * (((∑ j : Fin m, u j) / m) ^ 2) := by
            ring

/-- Helper for Lemma 7.1: a zero-sum coefficient family satisfies the sharp one-coordinate square
estimate coming from the complement-sum Cauchy-Schwarz argument. -/
theorem mul_sq_le_pred_mul_sum_sq_of_sum_eq_zero
    (hm : 2 ≤ m) {v : EuclideanSpace ℝ (Fin m)}
    (hsum : ∑ i : Fin m, v i = 0) :
    ∀ i : Fin m, (m : ℝ) * (v i) ^ 2 ≤ (m - 1 : ℝ) * (∑ j : Fin m, (v j) ^ 2) := by
  intro i
  let s : Finset (Fin m) := Finset.univ.erase i
  have hsum_erase : s.sum (fun j ↦ v j) = -v i := by
    -- Isolate the `i`-th coefficient from the zero-sum relation.
    have hsplit := hsum
    dsimp [s] at hsplit ⊢
    rw [← Finset.sum_erase_add (Finset.univ) (fun j : Fin m ↦ v j) (Finset.mem_univ i)] at hsplit
    linarith
  have hsq_erase :
      (s.sum fun j ↦ v j) ^ 2 ≤
        (s.card : ℝ) * (s.sum fun j ↦ (v j) ^ 2) := by
    -- Apply the finite Cauchy-Schwarz estimate on the complement of `{i}`.
    simpa [s] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ.erase i) (f := fun j : Fin m ↦ v j))
  have hcard :
      (s.card : ℝ) = (m - 1 : ℝ) := by
    have hm_one : 1 ≤ m := by
      linarith
    dsimp [s]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub hm_one]
    norm_num
  have hsq_i :
      (v i) ^ 2 ≤ (m - 1 : ℝ) * (s.sum fun j ↦ (v j) ^ 2) := by
    simpa [hsum_erase, hcard, sq] using hsq_erase
  have hsq_split :
      ∑ j : Fin m, (v j) ^ 2 = (v i) ^ 2 + s.sum (fun j ↦ (v j) ^ 2) := by
    -- Split the total squared mass into the chosen coordinate and its complement.
    dsimp [s]
    nth_rewrite 1 [← Finset.sum_erase_add
      (Finset.univ) (fun j : Fin m ↦ (v j) ^ 2) (Finset.mem_univ i)]
    ring
  have hm_real : (2 : ℝ) ≤ m := by
    exact_mod_cast hm
  nlinarith [hsq_i, hsq_split]

/-- Helper for Lemma 7.1: the sharp square bound on a zero-sum family implies that shifting every
coordinate by `1 / m` makes the family nonnegative. -/
theorem zero_sum_small_sq_sum_shift_nonneg
    (hm : 2 ≤ m) {v : EuclideanSpace ℝ (Fin m)}
    (hsum : ∑ i : Fin m, v i = 0)
    (hsmall : ∑ i : Fin m, (v i) ^ 2 ≤ 1 / ((m : ℝ) * (m - 1 : ℝ))) :
    ∀ i : Fin m, 0 ≤ v i + 1 / (m : ℝ) := by
  intro i
  have hm_real : (2 : ℝ) ≤ m := by
    exact_mod_cast hm
  have hm_pos : 0 < (m : ℝ) := by
    linarith
  have hm_ne : (m : ℝ) ≠ 0 := by
    linarith
  have hm_sub_nonneg : 0 ≤ (m - 1 : ℝ) := by
    nlinarith
  have hm_sub_ne : (m - 1 : ℝ) ≠ 0 := by
    nlinarith
  have hcoord :=
    mul_sq_le_pred_mul_sum_sq_of_sum_eq_zero (m := m) hm hsum i
  have hsq : (v i) ^ 2 ≤ (1 / (m : ℝ)) ^ 2 := by
    -- Feed the sharp coordinate inequality the global smallness bound on `∑ v_i^2`.
    have hcoord' : (m : ℝ) * (v i) ^ 2 ≤ 1 / (m : ℝ) := by
      calc
        (m : ℝ) * (v i) ^ 2 ≤ (m - 1 : ℝ) * (∑ j : Fin m, (v j) ^ 2) := hcoord
        _ ≤ (m - 1 : ℝ) * (1 / ((m : ℝ) * (m - 1 : ℝ))) := by
              gcongr
        _ = 1 / (m : ℝ) := by
              field_simp [hm_ne, hm_sub_ne]
    have hmul : (m : ℝ) ^ 2 * (v i) ^ 2 ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hcoord' hm_pos.le
      simpa [pow_two, hm_ne, mul_assoc, mul_left_comm, mul_comm, one_div] using this
    have hsq' : (v i) ^ 2 ≤ 1 / (m : ℝ) ^ 2 := by
      rw [le_div_iff₀ (show 0 < (m : ℝ) ^ 2 by positivity)]
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hpow : 1 / (m : ℝ) ^ 2 = (1 / (m : ℝ)) ^ 2 := by
      field_simp [hm_ne]
    rw [← hpow]
    exact hsq'
  by_contra hneg
  have hneg' : v i + 1 / (m : ℝ) < 0 := lt_of_not_ge hneg
  have hupper : 1 / (m : ℝ) < -v i := by
    linarith
  have hsq_lt : (1 / (m : ℝ)) ^ 2 < (v i) ^ 2 := by
    have hdiv_pos : 0 < 1 / (m : ℝ) := by
      positivity
    have : (1 / (m : ℝ)) ^ 2 < (-v i) ^ 2 := by
      nlinarith [hupper, hdiv_pos]
    simpa [sq] using this
  linarith

/-- Helper for Lemma 7.1: shifting a zero-sum family by the barycenter packages it as a point of
the standard simplex. -/
theorem centered_shift_to_stdSimplex
    (hm : 0 < m) {v : EuclideanSpace ℝ (Fin m)}
    (hsum : ∑ i : Fin m, v i = 0)
    (hshift : ∀ i : Fin m, 0 ≤ v i + 1 / (m : ℝ)) :
    ∃ theta : StdSimplex ℝ (Fin m), ∀ i : Fin m, theta.weights i = v i + 1 / (m : ℝ) := by
  let w : Fin m →₀ ℝ := Finsupp.equivFunOnFinite.symm (fun i : Fin m ↦ v i + 1 / (m : ℝ))
  have hw_nonneg : 0 ≤ w := by
    -- The shifted coordinates are nonnegative by hypothesis.
    intro i
    simpa [w] using hshift i
  have hm_ne : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hw_total : w.sum (fun _ r ↦ r) = 1 := by
    have hconst : ∑ i : Fin m, (1 / (m : ℝ)) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simpa [one_div] using (mul_inv_cancel₀ hm_ne)
    -- The zero-sum relation makes the shifted coefficients add up to `1`.
    calc
      w.sum (fun _ r ↦ r) = ∑ i : Fin m, (v i + 1 / (m : ℝ)) := by
        simp [w, Finsupp.sum_fintype]
      _ = (∑ i : Fin m, v i) + ∑ i : Fin m, (1 / (m : ℝ)) := by
        rw [Finset.sum_add_distrib]
      _ = 1 := by rw [hsum, zero_add, hconst]
  refine ⟨{ weights := w, nonneg := hw_nonneg, total := hw_total }, ?_⟩
  intro i
  simp [w]

/-- Helper for Lemma 7.1: every simplex-weighted average of the row inner products is bounded by
the finite support function. -/
theorem simplex_weighted_inner_le_supportFunction
    (hm : 0 < m) (theta : StdSimplex ℝ (Fin m)) (y : E) :
    ∑ i : Fin m, theta.weights i * inner ℝ (a i) y ≤ (ξ[Set.range a] y).toReal := by
  have _ : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hweights_total : ∑ i : Fin m, theta.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using theta.total
  have hcoord (i : Fin m) : inner ℝ (a i) y ≤ (ξ[Set.range a] y).toReal := by
    -- Each row inner product is one element of the finite set whose supremum defines the support.
    rw [supportFunction_range_toReal_eq_sSup_inner (a := a) (x := y)]
    exact le_csSup (Finite.bddAbove_range fun j : Fin m ↦ inner ℝ (a j) y) (Set.mem_range_self i)
  calc
    ∑ i : Fin m, theta.weights i * inner ℝ (a i) y ≤
        ∑ i : Fin m, theta.weights i * (ξ[Set.range a] y).toReal := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact mul_le_mul_of_nonneg_left (hcoord i) (theta.nonneg i)
    _ = (∑ i : Fin m, theta.weights i) * (ξ[Set.range a] y).toReal := by
          rw [Finset.sum_mul]
    _ = (ξ[Set.range a] y).toReal := by simp [hweights_total]

/-- Helper for Lemma 7.1: every sufficiently small dual-ball functional should support the finite
support function at the origin. -/
theorem small_dualClosedBall_subset_supporting_functionals
    (hm : 2 ≤ m) (hzero_sum : ∑ i : Fin m, a i = 0) :
    let p : Seminorm ℝ E :=
      Seminorm.comp
        (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
        (rowInnerMap a)
    dualClosedBall p (1 / Real.sqrt ((m : ℝ) * (m - 1 : ℝ))) ⊆
      {g : StrongDual ℝ E |
        ∀ y : E, (ξ[Set.range a] (0 : E)).toReal + g y ≤ (ξ[Set.range a] y).toReal} := by
  let p : Seminorm ℝ E :=
    Seminorm.comp (normSeminorm ℝ (EuclideanSpace ℝ (Fin m))) (rowInnerMap a)
  change dualClosedBall p (1 / Real.sqrt ((m : ℝ) * (m - 1 : ℝ))) ⊆
      {g : StrongDual ℝ E |
        ∀ y : E, (ξ[Set.range a] (0 : E)).toReal + g y ≤ (ξ[Set.range a] y).toReal}
  -- Route correction: the remaining lower inclusion must follow the source-faithful Chapter 7
  -- row-map factorization, Hahn-Banach extension, and simplex-recentering argument.
  intro g hg
  have hgamma0_nonneg : 0 ≤ 1 / Real.sqrt ((m : ℝ) * (m - 1 : ℝ)) := by
    positivity
  obtain ⟨ψ, hψ_apply, hψ_norm⟩ :=
    dualClosedBall_functional_descends_to_row_range (a := a) hgamma0_nonneg hg
  obtain ⟨u, hu_norm, hu_apply⟩ :=
    row_range_functional_has_euclidean_coefficients (a := a) hψ_norm
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  let μ : ℝ := (∑ j : Fin m, u j) / m
  let v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun i : Fin m ↦ u i - μ)
  have hv_sum_zero : ∑ i : Fin m, v i = 0 := by
    -- The source recentering step first produces a zero-sum coefficient family.
    simpa [μ, v] using recentered_coefficients_sum_zero (m := m) hm_pos u
  have hv_apply :
      ∀ y : E,
        (∑ i : Fin m, u i * inner ℝ (a i) y) =
          ∑ i : Fin m, v i * inner ℝ (a i) y := by
    -- The zero-sum relation on the row family removes the constant mean shift exactly.
    simpa [μ, v] using recentered_coefficients_preserve_functional (a := a) hzero_sum u
  have hg_apply_centered :
      ∀ y : E, g y = ∑ i : Fin m, v i * inner ℝ (a i) y := by
    intro y
    calc
      g y = ψ ((rowInnerMap a).rangeRestrict y) := by
        symm
        exact hψ_apply y
      _ = ∑ i : Fin m, u i * inner ℝ (a i) y := hu_apply y
      _ = ∑ i : Fin m, v i * inner ℝ (a i) y := hv_apply y
  have hv_sq_sum :
      ∑ i : Fin m, (v i) ^ 2 = ∑ i : Fin m, (u i) ^ 2 - (m : ℝ) * μ ^ 2 := by
    -- The scalar frontier starts with the source-side variance identity for the centered vector.
    simpa [μ, v] using recentered_coefficients_sq_sum (m := m) hm_pos u
  have hu_sq_sum_le :
      ∑ i : Fin m, (u i) ^ 2 ≤ 1 / ((m : ℝ) * (m - 1 : ℝ)) := by
    have hsum_nonneg : 0 ≤ ∑ i : Fin m, (u i) ^ 2 := by
      exact Finset.sum_nonneg fun i hi ↦ sq_nonneg (u i)
    have hnorm_sq : ‖u‖ ^ 2 = ∑ i : Fin m, (u i) ^ 2 := by
      have hnorm : ‖u‖ = Real.sqrt (∑ i : Fin m, (u i) ^ 2) := by
        simpa [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_eq u)
      calc
        ‖u‖ ^ 2 = (Real.sqrt (∑ i : Fin m, (u i) ^ 2)) ^ 2 := by rw [hnorm]
        _ = ∑ i : Fin m, (u i) ^ 2 := by rw [Real.sq_sqrt hsum_nonneg]
    have hprod_pos : 0 < (m : ℝ) * (m - 1 : ℝ) := by
      have hm_real : (2 : ℝ) ≤ m := by
        exact_mod_cast hm
      nlinarith
    have hgamma_sq :
        (1 / Real.sqrt ((m : ℝ) * (m - 1 : ℝ))) ^ 2 =
          1 / ((m : ℝ) * (m - 1 : ℝ)) := by
      have hsqrt_ne : Real.sqrt ((m : ℝ) * (m - 1 : ℝ)) ≠ 0 := by
        exact ne_of_gt (Real.sqrt_pos_of_pos hprod_pos)
      calc
        (1 / Real.sqrt ((m : ℝ) * (m - 1 : ℝ))) ^ 2
            = 1 / (Real.sqrt ((m : ℝ) * (m - 1 : ℝ))) ^ 2 := by
                field_simp [hsqrt_ne]
        _ = 1 / ((m : ℝ) * (m - 1 : ℝ)) := by
              rw [Real.sq_sqrt (le_of_lt hprod_pos)]
    have hnorm_sq_le :
        ‖u‖ ^ 2 ≤ (1 / Real.sqrt ((m : ℝ) * (m - 1 : ℝ))) ^ 2 := by
      -- Square the descended operator-norm bound to get the sum-of-squares estimate on `u`.
      have hsq := mul_self_le_mul_self (norm_nonneg u) hu_norm
      simpa [pow_two] using hsq
    rwa [hnorm_sq, hgamma_sq] at hnorm_sq_le
  have hv_sq_sum_le :
      ∑ i : Fin m, (v i) ^ 2 ≤ 1 / ((m : ℝ) * (m - 1 : ℝ)) := by
    have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
    have hmu_nonneg : 0 ≤ (m : ℝ) * μ ^ 2 := by
      exact mul_nonneg hm_nonneg (sq_nonneg μ)
    -- The centered vector loses the nonnegative variance term `m * μ^2`.
    nlinarith [hv_sq_sum, hu_sq_sum_le, hmu_nonneg]
  have hv_shift_nonneg : ∀ i : Fin m, 0 ≤ v i + 1 / (m : ℝ) := by
    -- The scalar frontier closes by combining the zero-sum relation with the sharp square bound.
    exact zero_sum_small_sq_sum_shift_nonneg (m := m) hm hv_sum_zero hv_sq_sum_le
  obtain ⟨theta, htheta_apply⟩ :=
    centered_shift_to_stdSimplex (m := m) hm_pos hv_sum_zero hv_shift_nonneg
  have hzero : (ξ[Set.range a] (0 : E)).toReal = 0 := by
    rw [supportFunction_range_toReal_eq_sSup_inner (a := a) (x := (0 : E))]
    have hzero_range :
        Set.range (fun i : Fin m ↦ inner ℝ (a i) (0 : E)) = ({0} : Set ℝ) := by
      ext t
      constructor
      · rintro ⟨i, rfl⟩
        simp
      · intro ht
        have ht0 : t = 0 := by simpa using ht
        obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hm_pos
        exact ⟨i, by simp [ht0]⟩
    rw [hzero_range]
    simp
  have hg_apply_theta :
      ∀ y : E, g y = ∑ i : Fin m, theta.weights i * inner ℝ (a i) y := by
    intro y
    have hsum_inner : ∑ i : Fin m, inner ℝ (a i) y = 0 := by
      -- The row family still sums to zero after pairing with `y`.
      have hinner_zero := congrArg (fun z : E ↦ inner ℝ z y) hzero_sum
      simpa [sum_inner] using hinner_zero
    -- Replace `v_i` by `θ_i - 1 / m` and cancel the constant shift with `∑ a_i = 0`.
    calc
      g y = ∑ i : Fin m, v i * inner ℝ (a i) y := hg_apply_centered y
      _ = ∑ i : Fin m, ((theta.weights i - 1 / (m : ℝ)) * inner ℝ (a i) y) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [htheta_apply i]
            ring
      _ = ∑ i : Fin m, theta.weights i * inner ℝ (a i) y -
            ∑ i : Fin m, (1 / (m : ℝ)) * inner ℝ (a i) y := by
            calc
              ∑ i : Fin m, (theta.weights i - 1 / (m : ℝ)) * inner ℝ (a i) y
                  = ∑ i : Fin m,
                      (theta.weights i * inner ℝ (a i) y -
                        (1 / (m : ℝ)) * inner ℝ (a i) y) := by
                          refine Finset.sum_congr rfl ?_
                          intro i hi
                          ring
              _ = ∑ i : Fin m, theta.weights i * inner ℝ (a i) y -
                    ∑ i : Fin m, (1 / (m : ℝ)) * inner ℝ (a i) y := by
                      rw [Finset.sum_sub_distrib]
      _ = ∑ i : Fin m, theta.weights i * inner ℝ (a i) y -
            (1 / (m : ℝ)) * ∑ i : Fin m, inner ℝ (a i) y := by
            rw [Finset.mul_sum]
      _ = ∑ i : Fin m, theta.weights i * inner ℝ (a i) y := by
            rw [hsum_inner, mul_zero, sub_zero]
  intro y
  -- The shifted coefficients are a simplex point, so the represented functional is bounded by the
  -- same support value.
  have hgy :
      g y ≤ (ξ[Set.range a] y).toReal := by
    calc
      g y = ∑ i : Fin m, theta.weights i * inner ℝ (a i) y := hg_apply_theta y
      _ ≤ (ξ[Set.range a] y).toReal :=
        simplex_weighted_inner_le_supportFunction (a := a) hm_pos theta y
  rw [hzero, zero_add]
  exact hgy

-- Proof sketch: prove definiteness of the pullback seminorm from the spanning hypothesis
-- `span ℝ (range a) = ⊤`, identify
-- `∂ (fun x ↦ (ξ[Set.range a] x).toReal) (0)` with
-- `convexHull ℝ (Set.range fun i ↦ (InnerProductSpace.toDual ℝ E) (a i))`, and then derive the
-- two `Definition_7_7` dual-ball inclusions using the convex-combination estimate and the
-- zero-sum estimate from the textbook proof.
/-- Lemma 7.1: if the family `a` has full row rank, encoded by
`Submodule.span ℝ (Set.range a) = ⊤`, has at least two elements, and satisfies `∑ i, a i = 0`,
then the canonical pullback seminorm
`x ↦ (∑ i ⟪aᵢ, x⟫²)^(1/2)` is a norm and the subdifferential at `0` of the Chapter 3 support
function `x ↦ (ξ[Set.range a] x).toReal` satisfies the asphericity condition with `γ₁ = 1` and
`γ₀ = 1 / √(m (m - 1))`. -/
theorem supportFunction_range_toReal_norm_and_asphericity
    (hm : 2 ≤ m) (hfull_row_rank : Submodule.span ℝ (Set.range a) = ⊤)
    (hzero_sum : ∑ i : Fin m, a i = 0) :
    let p : Seminorm ℝ E :=
      Seminorm.comp
        (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
        (((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap).comp
          (LinearMap.pi fun i ↦ (innerSL ℝ (a i)).toLinearMap))
    Seminorm.IsNorm p ∧
      SatisfiesAsphericityCondition
        (fun x ↦ (ξ[Set.range a] x).toReal)
        p
        (1 / Real.sqrt ((m : ℝ) * (m - 1 : ℝ))) 1 := by
  let p : Seminorm ℝ E := Seminorm.comp (normSeminorm ℝ (EuclideanSpace ℝ (Fin m))) (rowInnerMap a)
  have hp_norm : Seminorm.IsNorm p :=
    pullback_seminorm_isNorm_of_span_eq_top (a := a) hfull_row_rank
  refine ⟨by simpa [p, rowInnerMap] using hp_norm, ?_⟩
  change
    SatisfiesAsphericityCondition
      (fun x ↦ (ξ[Set.range a] x).toReal)
      p
      (1 / Real.sqrt ((m : ℝ) * (m - 1 : ℝ))) 1
  -- Route correction: keep the source-faithful Chapter 7 geometry. The remaining task is to prove
  -- the two asphericity inclusions by the row-map factorization and simplex-recentering argument
  -- from the textbook, rather than switching to an unrelated local recursion.
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hgamma0_pos : 0 < 1 / Real.sqrt ((m : ℝ) * (m - 1 : ℝ)) := by
    refine one_div_pos.mpr <| Real.sqrt_pos_of_pos ?_
    have hm_real : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hgamma0_le_one : 1 / Real.sqrt ((m : ℝ) * (m - 1 : ℝ)) ≤ 1 := by
    have hsqrt_ge : 1 ≤ Real.sqrt ((m : ℝ) * (m - 1 : ℝ)) := by
      rw [Real.one_le_sqrt]
      have hm_real : (2 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
    have hsqrt_pos : 0 < Real.sqrt ((m : ℝ) * (m - 1 : ℝ)) := by
      exact Real.sqrt_pos_of_pos (by
        have hm_real : (2 : ℝ) ≤ m := by exact_mod_cast hm
        nlinarith)
    exact (div_le_one hsqrt_pos).2 hsqrt_ge
  have hlower :
      dualClosedBall p (1 / Real.sqrt ((m : ℝ) * (m - 1 : ℝ))) ⊆
        {g : StrongDual ℝ E |
          ∀ y : E, (ξ[Set.range a] (0 : E)).toReal + g y ≤ (ξ[Set.range a] y).toReal} := by
    simpa [p] using
      small_dualClosedBall_subset_supporting_functionals (a := a) hm hzero_sum
  have hupper :
      {g : StrongDual ℝ E |
          ∀ y : E, (ξ[Set.range a] (0 : E)).toReal + g y ≤ (ξ[Set.range a] y).toReal} ⊆
        dualClosedBall p 1 := by
    intro g hg
    exact supporting_functional_mem_dualClosedBall_one (a := a) hm_pos hg
  exact ⟨hgamma0_pos, hgamma0_le_one, hlower, hupper⟩

end
