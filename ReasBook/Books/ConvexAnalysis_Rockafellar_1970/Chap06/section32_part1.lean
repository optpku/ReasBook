/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section10_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27_part2

open scoped Pointwise

section Chap06
section Section32

-- Proof sketch: For any `x ∈ C`, points on the segment from `z` to `x` sufficiently close to `z`
-- still lie in `C` because `z` is in the intrinsic interior. Convexity bounds `f x` by values at
-- those interior segment points, while maximality at `z` forces equality, hence `f x = f z`.
/-- Helper for Theorem 32.1: if `t > 0` and `y = z + t • (z - x)`, then `z` lies in the open
segment from `x` to `y`. -/
lemma helperForTheorem_32_1_mem_openSegment_of_point_beyond
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x z y : E} {t : ℝ}
    (ht : 0 < t) (hy : y = z + t • (z - x)) :
    z ∈ openSegment ℝ x y := by
  -- Rewrite `z` as a strict convex combination of `x` and the point beyond `z`.
  refine (mem_openSegment_iff_div (𝕜 := ℝ) (x := z) (y := x) (z := y)).2 ?_
  refine ⟨t, 1, ht, zero_lt_one, ?_⟩
  have hne : t + 1 ≠ 0 := by linarith
  have hxcoeff : t * (t + 1)⁻¹ - (1 / (t + 1)) * t = (0 : ℝ) := by
    field_simp [hne]
    ring
  have hzcoeff : 1 / (t + 1) + (1 / (t + 1)) * t = (1 : ℝ) := by
    field_simp [hne]
    ring
  calc
    (t / (t + 1)) • x + (1 / (t + 1)) • y
        = (t / (t + 1)) • x + (1 / (t + 1)) • (z + t • (z - x)) := by simp [hy]
    _ = (t / (t + 1)) • x + (1 / (t + 1)) • z + ((1 / (t + 1)) * t) • (z - x) := by
          simp [smul_add, smul_smul, add_assoc]
    _ = (t / (t + 1)) • x + (1 / (t + 1)) • z +
          (((1 / (t + 1)) * t) • z - (((1 / (t + 1)) * t) • x)) := by
          simp [smul_sub, add_assoc]
    _ = ((t / (t + 1)) • x - (((1 / (t + 1)) * t) • x)) +
          ((1 / (t + 1)) • z + (((1 / (t + 1)) * t) • z)) := by
          abel
    _ = ((t / (t + 1) - ((1 / (t + 1)) * t)) • x) +
          (((1 / (t + 1)) + ((1 / (t + 1)) * t)) • z) := by
          simp [sub_smul, add_smul]
    _ = z := by
          rw [div_eq_mul_inv, hxcoeff, hzcoeff]
          simp

/-- Helper for Theorem 32.1: an intrinsic-interior point can be extended beyond itself along the
ray from any other point of the set. -/
lemma helperForTheorem_32_1_exists_mem_openSegment_of_mem_intrinsicInterior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} {z x : E}
    (hz : z ∈ intrinsicInterior ℝ C) (hx : x ∈ C) (hxz : x ≠ z) :
    ∃ y ∈ C, z ∈ openSegment ℝ x y := by
  -- Move the intrinsic-interior condition to the affine-span subtype, where it gives a ball.
  rcases (mem_intrinsicInterior.mp hz) with ⟨zA, hzAint, rfl⟩
  let A : AffineSubspace ℝ E := affineSpan ℝ C
  let xA : A := ⟨x, subset_affineSpan ℝ C hx⟩
  have hxAzA : xA ≠ zA := by
    intro hEq
    apply hxz
    exact congrArg (fun p : A => (p : E)) hEq
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzAint) with ⟨ε, hε, hball⟩
  let v : E := (zA : E) - x
  have hv : v ≠ 0 := by
    intro hv0
    apply hxAzA
    apply Subtype.ext
    exact (sub_eq_zero.mp (by simpa [v] using hv0)).symm
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let t : ℝ := (ε / 2) / ‖v‖
  have htpos : 0 < t := by
    have hhalf : 0 < ε / 2 := by linarith
    exact div_pos hhalf hvpos
  let y : E := (zA : E) + t • v
  -- The point beyond `z` stays in the affine span, so we can test it in the subtype ball.
  have hy_aff' : (t • (((zA : E) -ᵥ x))) +ᵥ (zA : E) ∈ A := by
    refine AffineSubspace.vadd_mem_of_mem_direction ?_ zA.property
    exact Submodule.smul_mem _ _ (AffineSubspace.vsub_mem_direction zA.property xA.property)
  have hy_aff : y ∈ A := by
    simpa [A, y, v, xA, vadd_eq_add, vsub_eq_sub, add_comm, add_left_comm, add_assoc] using hy_aff'
  have hnorm : ‖t • v‖ < ε := by
    have htnonneg : 0 ≤ t := le_of_lt htpos
    calc
      ‖t • v‖ = |t| * ‖v‖ := by
        simpa [Real.norm_eq_abs] using (norm_smul t v)
      _ = t * ‖v‖ := by
        simp [abs_of_nonneg htnonneg]
      _ = ε / 2 := by
        dsimp [t]
        field_simp [ne_of_gt hvpos]
      _ < ε := by linarith
  have hy_mem_ball : (⟨y, hy_aff⟩ : A) ∈ Metric.ball zA ε := by
    change dist y (zA : E) < ε
    simpa [y, v, dist_eq_norm] using hnorm
  have hy_pre : (⟨y, hy_aff⟩ : A) ∈ ((↑) ⁻¹' C : Set A) := hball hy_mem_ball
  have hyC : y ∈ C := by simpa using hy_pre
  have hy_eq : y = (zA : E) + t • ((zA : E) - x) := by simp [y, v]
  refine ⟨y, hyC, ?_⟩
  simpa using
    helperForTheorem_32_1_mem_openSegment_of_point_beyond
      (x := x) (z := (zA : E)) (y := y) htpos hy_eq

/-- Helper for Theorem 32.1: maximality at an intrinsic-interior point forces equality with every
other point of the convex set. -/
lemma helperForTheorem_32_1_eq_value_of_mem_of_maximum_at_intrinsicInterior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} {f : E → ℝ} {z x : E}
    (hf : ConvexOn ℝ C f) (hz : z ∈ intrinsicInterior ℝ C) (hmax : IsMaxOn f C z)
    (hx : x ∈ C) : f x = f z := by
  -- Split off the trivial case `x = z`; otherwise use a point beyond `z` and convexity.
  by_cases hxz : x = z
  · simp [hxz]
  · rcases helperForTheorem_32_1_exists_mem_openSegment_of_mem_intrinsicInterior hz hx hxz with
      ⟨y, hyC, hzseg⟩
    have hxle : f x ≤ f z := (isMaxOn_iff.mp hmax) x hx
    have hyle : f y ≤ f z := (isMaxOn_iff.mp hmax) y hyC
    have hzle : f z ≤ f x := hf.le_left_of_right_le hx hyC hzseg hyle
    exact le_antisymm hxle hzle

/-- Theorem 32.1: if a convex function on `C` attains its maximum on `C` at a point of the
intrinsic interior of `C`, then it is constant on `C`. -/
theorem convexOn_eq_const_of_maximum_at_intrinsicInterior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} {f : E → ℝ} {z : E}
    (hf : ConvexOn ℝ C f) (hz : z ∈ intrinsicInterior ℝ C) (hmax : IsMaxOn f C z) :
    Set.EqOn f (fun _ ↦ f z) C := by
  -- Apply the pointwise equality helper on each point of `C`.
  intro x hx
  exact helperForTheorem_32_1_eq_value_of_mem_of_maximum_at_intrinsicInterior hf hz hmax hx

/-- The set of points of `C` where `f` attains its maximum over `C`. -/
def maximizersOn {α β : Type*} [Preorder β] (f : α → β) (C : Set α) : Set α :=
  {x : α | x ∈ C ∧ IsMaxOn f C x}

-- Proof sketch: For each maximizer `x`, choose the face of `C` whose relative interior contains
-- `x`. Applying Theorem 32.1 on that face shows `f` is constant there, so the whole face consists
-- of maximizers. Taking the union over all such faces recovers the full maximizer set.
/-- Helper for Corollary 32.1.1: if a maximizer lies in the open segment between two points of
`C`, then both endpoints have the same value as the maximizer. -/
lemma helperForCorollary_32_1_1_endpoint_values_eq_of_mem_openSegment_maximizer
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} {f : E → ℝ} {x y z : E}
    (hf : ConvexOn ℝ C f) (hx : x ∈ C) (hy : y ∈ C)
    (hzmax : z ∈ maximizersOn f C) (hzseg : z ∈ openSegment ℝ x y) :
    f x = f z ∧ f y = f z := by
  rcases hzmax with ⟨hzC, hzmaxOn⟩
  -- Maximality puts both endpoints below the value at `z`.
  have hxle : f x ≤ f z := (isMaxOn_iff.mp hzmaxOn) x hx
  have hyle : f y ≤ f z := (isMaxOn_iff.mp hzmaxOn) y hy
  -- Convexity then forces the value at `z` back below each endpoint.
  have hzlex : f z ≤ f x := hf.le_left_of_right_le hx hy hzseg hyle
  have hzley : f z ≤ f y := hf.le_right_of_left_le hx hy hzseg hxle
  exact ⟨le_antisymm hxle hzlex, le_antisymm hyle hzley⟩

/-- Helper for Corollary 32.1.1: the set of maximizers of a convex function on `C` is an extreme
subset of `C`. -/
lemma helperForCorollary_32_1_1_isExtreme_maximizersOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ C f) :
    IsExtreme ℝ C (maximizersOn f C) := by
  refine ⟨?_, ?_⟩
  · -- Every maximizer is, by definition, a point of `C`.
    intro z hzmax
    exact hzmax.1
  · intro x hx y hy z hzmax hzseg
    -- The endpoint value equals the maximizing value, so the endpoint is also a maximizer.
    rcases helperForCorollary_32_1_1_endpoint_values_eq_of_mem_openSegment_maximizer
        hf hx hy hzmax hzseg with ⟨hxz, _⟩
    rcases hzmax with ⟨_, hzmaxOn⟩
    refine ⟨hx, ?_⟩
    rw [isMaxOn_iff]
    intro w hwC
    have hwle : f w ≤ f z := (isMaxOn_iff.mp hzmaxOn) w hwC
    simpa [hxz] using hwle

/-- Helper for Corollary 32.1.1: the set of maximizers of a convex function on `C` is a face of
`C`. -/
lemma helperForCorollary_32_1_1_isFace_maximizersOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ C f) :
    IsFace (𝕜 := ℝ) C (maximizersOn f C) := by
  -- Route correction: prove the whole maximizer set is itself a face, then take a singleton family.
  exact ⟨hf.1, helperForCorollary_32_1_1_isExtreme_maximizersOn hf⟩

/-- Corollary 32.1.1: for a real-valued convex function on a convex set `C`, the set of points of
`C` where the supremum of `f` relative to `C` is attained is a union of faces of `C`. In this
formalization `f : E → ℝ` is total, so the book's `C ⊆ dom f` hypothesis is implicit. -/
theorem maximizersOn_is_sUnion_of_faces
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ C f) :
    ∃ 𝓕 : Set (Set E),
      (∀ Face ∈ 𝓕, IsFace (𝕜 := ℝ) C Face) ∧
      Set.sUnion 𝓕 = maximizersOn f C := by
  -- Take the singleton family containing the maximizer set itself.
  refine ⟨{maximizersOn f C}, ?_⟩
  constructor
  · intro Face hFace
    rw [Set.mem_singleton_iff.mp hFace]
    exact helperForCorollary_32_1_1_isFace_maximizersOn hf
  · simp

-- Proof sketch: every point of `convexHull ℝ S` lies in the convex hull of a finite subset of
-- `S`; Jensen's inequality bounds `f` at that point by the maximum over the finite subset, hence
-- by the supremum over `S`. Since `S ⊆ convexHull ℝ S`, the reverse supremum inequality is
-- immediate. If a maximizer exists on `convexHull ℝ S`, the common supremum value is realized on
-- `S`, yielding a maximizer there as well.
/-- Helper for Theorem 32.2: every point of the convex hull is dominated by some generating-point
value. -/
lemma helperForTheorem_32_2_exists_point_ge_on_generatingSet
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {S : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ (convexHull ℝ S) f)
    {x : E} (hx : x ∈ convexHull ℝ S) :
    ∃ y ∈ S, f x ≤ f y := by
  letI := Module.addCommMonoidToAddCommGroup ℝ (M := E)
  -- Apply the convex-hull maximum principle directly to the generating set `S`.
  exact hf.exists_ge_of_mem_convexHull (subset_convexHull ℝ S) hx

/-- Helper for Theorem 32.2: each value on the convex hull is bounded by the `WithTop` supremum
over the generating set. -/
lemma helperForTheorem_32_2_le_sSup_image_of_mem_convexHull
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {S : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ (convexHull ℝ S) f)
    {x : E} (hx : x ∈ convexHull ℝ S) :
    ((f x : ℝ) : WithTop ℝ) ≤
      sSup ((fun z : E => ((f z : ℝ) : WithTop ℝ)) '' S) := by
  -- First compare `f x` with a value on `S`, then bound that value by the supremum over `S`.
  obtain ⟨y, hyS, hxy⟩ := helperForTheorem_32_2_exists_point_ge_on_generatingSet hf hx
  have hxy' : ((f x : ℝ) : WithTop ℝ) ≤ ((f y : ℝ) : WithTop ℝ) := by
    exact_mod_cast hxy
  have hySup :
      ((f y : ℝ) : WithTop ℝ) ∈ ((fun z : E => ((f z : ℝ) : WithTop ℝ)) '' S) := by
    refine ⟨y, hyS, ?_⟩
    rfl
  exact le_trans hxy' (le_csSup (OrderTop.bddAbove _) hySup)

/-- Helper for Theorem 32.2: once the maximizing point is known to lie in the convex hull, the
maximum transfers to the generating set. -/
lemma helperForTheorem_32_2_exists_isMaxOn_on_generatingSet
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {S : Set E} {f : E → ℝ} {x : E}
    (hf : ConvexOn ℝ (convexHull ℝ S) f)
    (hx : x ∈ convexHull ℝ S) (hxMax : IsMaxOn f (convexHull ℝ S) x) :
    ∃ y ∈ S, IsMaxOn f S y := by
  -- Compare the maximizing value at `x` with a generator value and use maximality to get equality.
  obtain ⟨y, hyS, hxy⟩ := helperForTheorem_32_2_exists_point_ge_on_generatingSet hf hx
  have hyx : f y ≤ f x := (isMaxOn_iff.mp hxMax) y (subset_convexHull ℝ S hyS)
  have hy_eq : f y = f x := le_antisymm hyx hxy
  refine ⟨y, hyS, ?_⟩
  -- The same equality turns the convex-hull maximality bound into an `S`-maximality bound.
  rw [isMaxOn_iff]
  intro z hzS
  have hzx : f z ≤ f x := (isMaxOn_iff.mp hxMax) z (subset_convexHull ℝ S hzS)
  rw [hy_eq]
  exact hzx

/-- Helper for Theorem 32.2: maximality on a larger set restricts to maximality on any subset. -/
lemma helperForTheorem_32_2_isMaxOn_on_subset
    {α β : Type*} [Preorder β]
    {f : α → β} {A B : Set α} {x : α}
    (hAB : A ⊆ B) (hxMax : IsMaxOn f B x) :
    IsMaxOn f A x := by
  -- Reinterpret maximality as an order bound and restrict the domain to the smaller set.
  rw [isMaxOn_iff] at hxMax ⊢
  intro y hyA
  exact hxMax y (hAB hyA)

/-- Theorem 32.2: if `f` is convex on `convexHull ℝ S`, then the supremum of `f` over
`convexHull ℝ S`, viewed in `WithTop ℝ`, equals the supremum over `S`; moreover, if `f` attains
a maximum on `convexHull ℝ S`, then it attains a maximum on `S`. -/
theorem sSup_convexHull_eq_sSup_of_convexOn
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {S : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ (convexHull ℝ S) f) :
    sSup ((fun x : E => ((f x : ℝ) : WithTop ℝ)) '' convexHull ℝ S) =
      sSup ((fun x : E => ((f x : ℝ) : WithTop ℝ)) '' S) ∧
    ((∃ x, IsMaxOn f (convexHull ℝ S) x) → ∃ x, IsMaxOn f S x) := by
  constructor
  · -- Compare the real image sets first, then lift the resulting equality to `WithTop ℝ`.
    let A : Set ℝ := f '' convexHull ℝ S
    let B : Set ℝ := f '' S
    have hA_dom : ∀ a ∈ A, ∃ b ∈ B, a ≤ b := by
      -- Every value on the convex hull is bounded by some generating-set value.
      intro a ha
      rcases ha with ⟨x, hx, rfl⟩
      obtain ⟨y, hyS, hxy⟩ := helperForTheorem_32_2_exists_point_ge_on_generatingSet hf hx
      refine ⟨f y, ?_, hxy⟩
      exact ⟨y, hyS, rfl⟩
    have hB_dom : ∀ b ∈ B, ∃ a ∈ A, b ≤ a := by
      -- Since `S ⊆ convexHull ℝ S`, each generating-set value already appears on the hull side.
      intro b hb
      rcases hb with ⟨x, hxS, rfl⟩
      refine ⟨f x, ?_, le_rfl⟩
      exact ⟨x, subset_convexHull ℝ S hxS, rfl⟩
    have hB_subset_A : B ⊆ A := by
      intro b hb
      rcases hb with ⟨x, hxS, rfl⟩
      exact ⟨x, subset_convexHull ℝ S hxS, rfl⟩
    have hImageA :
        ((fun x : E => ((f x : ℝ) : WithTop ℝ)) '' convexHull ℝ S) =
          ((fun a : ℝ => (a : WithTop ℝ)) '' A) := by
      ext u
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨a, ⟨x, hx, hax⟩, hau⟩
        subst hax
        subst hau
        exact ⟨x, hx, rfl⟩
    have hImageB :
        ((fun x : E => ((f x : ℝ) : WithTop ℝ)) '' S) =
          ((fun a : ℝ => (a : WithTop ℝ)) '' B) := by
      ext u
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨a, ⟨x, hx, hax⟩, hau⟩
        subst hax
        subst hau
        exact ⟨x, hx, rfl⟩
    by_cases hBdd : BddAbove B
    · have hAdd : BddAbove A := by
        -- A bound for `B` also bounds `A`, because `A` is pointwise dominated by `B`.
        rcases hBdd with ⟨M, hM⟩
        refine ⟨M, ?_⟩
        intro a ha
        obtain ⟨b, hb, hab⟩ := hA_dom a ha
        exact le_trans hab (hM hb)
      rw [hImageA, hImageB, ← WithTop.coe_sSup' hAdd, ← WithTop.coe_sSup' hBdd]
      exact congrArg (fun r : ℝ => ((r : ℝ) : WithTop ℝ))
        (csSup_eq_csSup_of_forall_exists_le hA_dom hB_dom)
    · have hAdd : ¬ BddAbove A := by
        -- Otherwise `B`, being a subset of `A`, would also be bounded above.
        intro hAdd
        exact hBdd (BddAbove.mono hB_subset_A hAdd)
      have hTopA : (⊤ : WithTop ℝ) ∉ ((fun a : ℝ => (a : WithTop ℝ)) '' A) := by
        intro hTop
        rcases hTop with ⟨a, ha, hTopEq⟩
        simp at hTopEq
      have hTopB : (⊤ : WithTop ℝ) ∉ ((fun a : ℝ => (a : WithTop ℝ)) '' B) := by
        intro hTop
        rcases hTop with ⟨a, ha, hTopEq⟩
        simp at hTopEq
      have hPreA :
          ((fun a : ℝ => (a : WithTop ℝ)) ⁻¹' ((fun a : ℝ => (a : WithTop ℝ)) '' A) : Set ℝ) = A := by
        ext a
        constructor
        · intro ha
          rcases ha with ⟨b, hb, hba⟩
          have hb_eq : b = a := by
            simpa using hba
          simpa [hb_eq] using hb
        · intro ha
          exact ⟨a, ha, rfl⟩
      have hPreB :
          ((fun a : ℝ => (a : WithTop ℝ)) ⁻¹' ((fun a : ℝ => (a : WithTop ℝ)) '' B) : Set ℝ) = B := by
        ext a
        constructor
        · intro ha
          rcases ha with ⟨b, hb, hba⟩
          have hb_eq : b = a := by
            simpa using hba
          simpa [hb_eq] using hb
        · intro ha
          exact ⟨a, ha, rfl⟩
      rw [hImageA, hImageB]
      simp [sSup, hTopA, hTopB, hPreA, hPreB, hAdd, hBdd]
  · intro hmax
    -- Route correction: the formalized goal only asks for weak attainment, so reuse the same
    -- witness and restrict its maximality bound from the hull to the generating set.
    rcases hmax with ⟨x, hxMax⟩
    refine ⟨x, ?_⟩
    -- Every point of `S` also belongs to `convexHull ℝ S`, so maximality descends along inclusion.
    exact helperForTheorem_32_2_isMaxOn_on_subset (subset_convexHull ℝ S) hxMax

-- Proof sketch: By Theorem 18.4, every relative interior point of `C` lies in a segment whose
-- endpoints are in `euclideanRelativeBoundary n C`; hence every point of `C` belongs to the
-- convex hull of the relative boundary. Applying Theorem 32.2 with `S = euclideanRelativeBoundary
-- n C` gives equality of suprema and transfers attainment from `C` to the relative boundary.
/-- Helper for Corollary 32.2.1: every relative-interior point of `C` lies in the convex hull of
its Euclidean relative boundary. -/
lemma helperForCorollary_32_2_1_mem_convexHull_relativeBoundary_of_mem_relativeInterior
    {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C)
    (hC_not_affine :
      ¬ ∃ A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)), (A : Set (EuclideanSpace ℝ (Fin n))) = C)
    (hC_not_closedHalf_affine :
      ¬ ∃ (A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
          (g : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ) (a : ℝ),
          g ≠ 0 ∧ C = (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | g x ≤ a})
    {x : EuclideanSpace ℝ (Fin n)}
    (hxri : x ∈ euclideanRelativeInterior n C) :
    x ∈ convexHull ℝ (euclideanRelativeBoundary n C) := by
  -- Place `x` on a segment joining two relative-boundary points using Theorem 18.4.
  rcases exists_mem_segment_of_mem_euclideanRelativeInterior
      (n := n) (C := C) hCclosed hCconv hC_not_affine hC_not_closedHalf_affine hxri with
    ⟨y, z, hyBoundary, hzBoundary, hxSeg⟩
  -- Each endpoint belongs to the hull of the relative boundary by definition.
  have hyHull : y ∈ convexHull ℝ (euclideanRelativeBoundary n C) :=
    subset_convexHull ℝ (euclideanRelativeBoundary n C) hyBoundary
  have hzHull : z ∈ convexHull ℝ (euclideanRelativeBoundary n C) :=
    subset_convexHull ℝ (euclideanRelativeBoundary n C) hzBoundary
  -- Convexity of the hull then contains the whole segment between those endpoints.
  exact (convex_convexHull ℝ (euclideanRelativeBoundary n C)).segment_subset hyHull hzHull hxSeg

/-- Helper for Corollary 32.2.1: every point of `C` lies in the convex hull of its Euclidean
relative boundary. -/
lemma helperForCorollary_32_2_1_mem_convexHull_relativeBoundary_of_mem
    {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C)
    (hC_not_affine :
      ¬ ∃ A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)), (A : Set (EuclideanSpace ℝ (Fin n))) = C)
    (hC_not_closedHalf_affine :
      ¬ ∃ (A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
          (g : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ) (a : ℝ),
          g ≠ 0 ∧ C = (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | g x ≤ a})
    {x : EuclideanSpace ℝ (Fin n)}
    (hxC : x ∈ C) :
    x ∈ convexHull ℝ (euclideanRelativeBoundary n C) := by
  -- Split according to whether `x` is in the relative interior or already on the boundary.
  by_cases hxri : x ∈ euclideanRelativeInterior n C
  · exact
      helperForCorollary_32_2_1_mem_convexHull_relativeBoundary_of_mem_relativeInterior
        (n := n) (C := C) hCclosed hCconv hC_not_affine hC_not_closedHalf_affine hxri
  · have hxBoundary : x ∈ euclideanRelativeBoundary n C := by
      -- Closedness identifies the relative boundary with `C \ ri C`.
      have hxDiff : x ∈ C \ euclideanRelativeInterior n C := ⟨hxC, hxri⟩
      simpa [euclideanRelativeBoundary_eq_diff_of_isClosed (n := n) (C := C) hCclosed] using hxDiff
    -- Boundary points lie in their own convex hull.
    exact subset_convexHull ℝ (euclideanRelativeBoundary n C) hxBoundary

/-- Helper for Corollary 32.2.1: a closed convex set satisfying the non-affine and non-half-affine
hypotheses is the convex hull of its Euclidean relative boundary. -/
lemma helperForCorollary_32_2_1_convexHull_relativeBoundary_eq
    {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C)
    (hC_not_affine :
      ¬ ∃ A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)), (A : Set (EuclideanSpace ℝ (Fin n))) = C)
    (hC_not_closedHalf_affine :
      ¬ ∃ (A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
          (g : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ) (a : ℝ),
          g ≠ 0 ∧ C = (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | g x ≤ a}) :
    convexHull ℝ (euclideanRelativeBoundary n C) = C := by
  apply Set.Subset.antisymm
  · -- The relative boundary is contained in `C`, so its convex hull is contained in `C`.
    refine convexHull_min ?_ hCconv
    intro x hxBoundary
    have hxDiff : x ∈ C \ euclideanRelativeInterior n C := by
      simpa [euclideanRelativeBoundary_eq_diff_of_isClosed (n := n) (C := C) hCclosed] using hxBoundary
    exact hxDiff.1
  · -- Every point of `C` is in the convex hull of the relative boundary by the previous helper.
    intro x hxC
    exact
      helperForCorollary_32_2_1_mem_convexHull_relativeBoundary_of_mem
        (n := n) (C := C) hCclosed hCconv hC_not_affine hC_not_closedHalf_affine hxC

/-- Corollary 32.2.1: if `f` is convex on a closed convex set `C` that is neither an affine set
nor a closed half of an affine set, then the supremum of `f` over `C` equals the supremum over
the relative boundary of `C`; moreover, if the supremum on `C` is attained, then it is attained on
the relative boundary. -/
theorem sSup_relativeBoundary_eq_sSup_of_not_affine_or_half_affine
    {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C)
    (hC_not_affine :
      ¬ ∃ A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)), (A : Set (EuclideanSpace ℝ (Fin n))) = C)
    (hC_not_closedHalf_affine :
      ¬ ∃ (A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
          (g : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ) (a : ℝ),
          g ≠ 0 ∧ C = (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | g x ≤ a})
    (hf : ConvexOn ℝ C f) :
    sSup ((fun x : EuclideanSpace ℝ (Fin n) => ((f x : ℝ) : WithTop ℝ)) '' C) =
      sSup
        ((fun x : EuclideanSpace ℝ (Fin n) => ((f x : ℝ) : WithTop ℝ)) ''
          euclideanRelativeBoundary n C) ∧
    ((∃ x, IsMaxOn f C x) → ∃ x, IsMaxOn f (euclideanRelativeBoundary n C) x) := by
  let S : Set (EuclideanSpace ℝ (Fin n)) := euclideanRelativeBoundary n C
  -- Identify `C` with the convex hull of its relative boundary via the textbook segment argument.
  have hHull : convexHull ℝ S = C := by
    simpa [S] using
      helperForCorollary_32_2_1_convexHull_relativeBoundary_eq
        (n := n) (C := C) hCclosed hCconv hC_not_affine hC_not_closedHalf_affine
  -- Rewrite the convexity hypothesis onto that hull so Theorem 32.2 applies directly.
  have hfHull : ConvexOn ℝ (convexHull ℝ S) f := by
    simpa [hHull] using hf
  have hSupAndMax :
      sSup ((fun x : EuclideanSpace ℝ (Fin n) => ((f x : ℝ) : WithTop ℝ)) '' convexHull ℝ S) =
        sSup ((fun x : EuclideanSpace ℝ (Fin n) => ((f x : ℝ) : WithTop ℝ)) '' S) ∧
      ((∃ x, IsMaxOn f (convexHull ℝ S) x) → ∃ x, IsMaxOn f S x) :=
    sSup_convexHull_eq_sSup_of_convexOn (S := S) (f := f) hfHull
  constructor
  · -- The supremum identity is exactly Theorem 32.2 after rewriting the hull back to `C`.
    simpa [S, hHull] using hSupAndMax.1
  · intro hMaxC
    have hMaxHull : ∃ x, IsMaxOn f (convexHull ℝ S) x := by
      rcases hMaxC with ⟨x, hxMax⟩
      exact ⟨x, by simpa [hHull] using hxMax⟩
    rcases hSupAndMax.2 hMaxHull with ⟨x, hxMaxBoundary⟩
    -- Rewrite the maximizing set back to the actual relative boundary.
    exact ⟨x, by simpa [S] using hxMaxBoundary⟩

/-- A half-line with base point `x` and direction `d`. -/
def halfLine {E : Type*} [AddMonoid E] [SMul ℝ E] (x d : E) : Set E :=
  {y | ∃ t : ℝ, 0 ≤ t ∧ y = x + t • d}

/-- `f` is bounded above on every nontrivial half-line contained in `C`. -/
def NoUnboundedAboveOnHalfLines {E : Type*} {β : Type*}
    [Preorder β] [AddMonoid E] [SMul ℝ E]
    (f : E → β) (C : Set E) : Prop :=
  ∀ x d, d ≠ 0 → halfLine x d ⊆ C → BddAbove (f '' halfLine x d)

-- Proof sketch: split `C` along its lineality space, then apply Theorem 32.2 to the slice
-- `C ∩ Lᗮ`. The no-unbounded-half-line hypothesis removes the recession-direction contribution,
-- so the supremum is controlled by the extreme points of the orthogonal slice; any maximizer on
-- `C` therefore yields one on that extreme-point set.
/-- Helper for Theorem 32.3: the span of the lineality space has the same carrier set as the
lineality space itself. -/
lemma helperForTheorem_32_3_coe_span_linealitySpace_eq
    {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (hCconv : Convex ℝ C) :
    ((Submodule.span ℝ (Set.linealitySpace C)) : Set (EuclideanSpace ℝ (Fin n))) =
      Set.linealitySpace C := by
  -- Identify the lineality space with a genuine submodule, then rewrite its span back to itself.
  rcases linealitySpace_isSubmodule (C := C) hCconv with ⟨L, hL⟩
  have hSpan : Submodule.span ℝ (Set.linealitySpace C) = L := by
    simpa [hL] using (Submodule.span_eq (p := L))
  simpa [hSpan] using hL

/-- Helper for Theorem 32.3: orthogonal projection onto the lineality space produces a point of
the orthogonal slice `C ∩ Lᗮ`. -/
lemma helperForTheorem_32_3_exists_sliceRepresentative
    {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (hCconv : Convex ℝ C)
    {x : EuclideanSpace ℝ (Fin n)} (hxC : x ∈ C) :
    ∃ y ∈ C ∩ (((Submodule.span ℝ (Set.linealitySpace C))ᗮ : Set _)),
      y = x - (Submodule.span ℝ (Set.linealitySpace C)).starProjection x := by
  let L : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ (Set.linealitySpace C)
  -- Project `x` to `Lᗮ`; the projection vector stays in the lineality space, so subtracting it
  -- keeps us inside `C`.
  let y : EuclideanSpace ℝ (Fin n) := x - L.starProjection x
  have hproj_mem_L : L.starProjection x ∈ L :=
    Submodule.starProjection_apply_mem (U := L) (x := x)
  have hLset : (L : Set (EuclideanSpace ℝ (Fin n))) = Set.linealitySpace C := by
    simpa [L] using helperForTheorem_32_3_coe_span_linealitySpace_eq (n := n) (C := C) hCconv
  have hproj_lineality : L.starProjection x ∈ Set.linealitySpace C := by
    exact hLset ▸ hproj_mem_L
  have hyC : y ∈ C := by
    have htranslate :=
      add_sub_mem_of_mem_linealitySpace (n := n) (C := C) hCconv hproj_lineality hxC
    simpa [y] using htranslate.2
  have hyPerp : y ∈ Lᗮ := by
    simpa [y] using (Submodule.sub_starProjection_mem_orthogonal (K := L) (v := x))
  refine ⟨y, ?_, ?_⟩
  · simpa [L] using (show y ∈ C ∩ (Lᗮ : Set _) from ⟨hyC, hyPerp⟩)
  · simp [L, y]

/-- Helper for Theorem 32.3: a convex function bounded above on a recession half-line cannot
increase along that half-line. -/
lemma helperForTheorem_32_3_le_of_mem_recessionCone_bddAbove_halfLine
    {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hCconv : Convex ℝ C)
    (hf : ConvexOn ℝ C f)
    {u x : EuclideanSpace ℝ (Fin n)}
    (hu : u ∈ Set.recessionCone C)
    (hx : x ∈ C)
    (hBdd : BddAbove (f '' halfLine x u)) :
    ∀ t : ℝ, 0 ≤ t → f (x + t • u) ≤ f x := by
  intro t ht
  by_cases ht0 : t = 0
  · -- The starting point of the ray is unchanged.
    simpa [ht0] using le_rfl
  · have ht0' : 0 ≠ t := by
        intro h0
        apply ht0
        simpa using h0.symm
    have htpos : 0 < t := lt_of_le_of_ne ht ht0'
    rcases hBdd with ⟨M, hM⟩
    let y : EuclideanSpace ℝ (Fin n) := x + t • u
    have hyHalfLine : y ∈ halfLine x u := ⟨t, ht, rfl⟩
    have hyC : y ∈ C := hu hx ht
    have hy_le_M : f y ≤ M := hM ⟨y, hyHalfLine, rfl⟩
    by_contra hy_not_le
    have hxy : f x < f y := lt_of_not_ge hy_not_le
    let s : ℝ := t * (M - f y + 1) / (f y - f x)
    have hden_pos : 0 < f y - f x := sub_pos.mpr hxy
    have hden_ne : f y - f x ≠ 0 := ne_of_gt hden_pos
    have hs_nonneg : 0 ≤ s := by
      have hnum_nonneg : 0 ≤ t * (M - f y + 1) := by
        have htail : 0 ≤ M - f y + 1 := by linarith
        exact mul_nonneg ht htail
      exact div_nonneg hnum_nonneg (sub_nonneg.mpr (le_of_lt hxy))
    let z : EuclideanSpace ℝ (Fin n) := x + (t + s) • u
    have hzC : z ∈ C := hu hx (add_nonneg ht hs_nonneg)
    have hzHalfLine : z ∈ halfLine x u := ⟨t + s, add_nonneg ht hs_nonneg, rfl⟩
    have hz_le_M : f z ≤ M := hM ⟨z, hzHalfLine, rfl⟩
    let a : ℝ := s / (t + s)
    let b : ℝ := t / (t + s)
    have hts_pos : 0 < t + s := add_pos_of_pos_of_nonneg htpos hs_nonneg
    have hts_ne : t + s ≠ 0 := ne_of_gt hts_pos
    have ha_nonneg : 0 ≤ a := div_nonneg hs_nonneg (le_of_lt hts_pos)
    have hb_nonneg : 0 ≤ b := div_nonneg ht (le_of_lt hts_pos)
    have hab : a + b = 1 := by
      have hsum : s / (t + s) + t / (t + s) = (1 : ℝ) := by
        field_simp [hts_ne]
        ring
      simpa [a, b, add_comm, add_left_comm, add_assoc] using hsum
    have hy_eq : y = a • x + b • z := by
      ext i
      simp [y, z, a, b]
      field_simp [hts_ne]
      ring
    -- Compare `y` with the farther point `z` on the same recession ray.
    have hy_conv : f y ≤ a • f x + b • f z := by
      simpa [hy_eq] using hf.2 hx hzC ha_nonneg hb_nonneg hab
    have hz_scaled : a * f x + b * f z ≤ a * f x + b * M := by
      have hb_scaled : b * f z ≤ b * M := mul_le_mul_of_nonneg_left hz_le_M hb_nonneg
      nlinarith
    have hy_le_combo : f y ≤ a * f x + b * M := by
      exact le_trans (by simpa [a, b, smul_eq_mul] using hy_conv) hz_scaled
    have hmult : (t + s) * f y ≤ s * f x + t * M := by
      have hscaled := mul_le_mul_of_nonneg_left hy_le_combo (le_of_lt hts_pos)
      have hs_mul : (t + s) * a = s := by
        dsimp [a]
        field_simp [hts_ne]
      have ht_mul : (t + s) * b = t := by
        dsimp [b]
        field_simp [hts_ne]
      calc
        (t + s) * f y ≤ (t + s) * (a * f x + b * M) := hscaled
        _ = ((t + s) * a) * f x + ((t + s) * b) * M := by ring
        _ = s * f x + t * M := by simp [hs_mul, ht_mul]
    have hs_eq : s * (f y - f x) = t * (M - f y + 1) := by
      dsimp [s]
      field_simp [hden_ne]
    have hmain : t * (M - f y + 1) ≤ t * (M - f y) := by
      have hs_bound : s * (f y - f x) ≤ t * (M - f y) := by
        nlinarith
      simpa [hs_eq] using hs_bound
    linarith

/-- Helper for Theorem 32.3: translating by a lineality direction preserves the value of the
convex function. -/
lemma helperForTheorem_32_3_eq_value_of_add_mem_linealitySpace
    {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hCconv : Convex ℝ C)
    (hf : ConvexOn ℝ C f)
    (hNoHalfLines : NoUnboundedAboveOnHalfLines f C)
    {x v : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ C) (hv : v ∈ Set.linealitySpace C) :
    f (x + v) = f x := by
  have hv' : v ∈ (-Set.recessionCone C) ∩ Set.recessionCone C := by
    simpa [Set.linealitySpace] using hv
  have hvRec : v ∈ Set.recessionCone C := hv'.2
  have hnegvRec : -v ∈ Set.recessionCone C := by
    simpa [Set.mem_neg] using hv'.1
  have hxv : x + v ∈ C := (add_sub_mem_of_mem_linealitySpace (n := n) (C := C) hCconv hv hx).1
  by_cases hv0 : v = 0
  · -- The zero lineality direction gives the trivial equality.
    simp [hv0]
  · have hBddPos : BddAbove (f '' halfLine x v) := by
      apply hNoHalfLines x v hv0
      intro y hy
      rcases hy with ⟨t, ht, rfl⟩
      exact hvRec hx ht
    have hForward : f (x + v) ≤ f x := by
      simpa using
        helperForTheorem_32_3_le_of_mem_recessionCone_bddAbove_halfLine
          (n := n) (C := C) (f := f) hCconv hf hvRec hx hBddPos 1 zero_le_one
    have hBddNeg : BddAbove (f '' halfLine (x + v) (-v)) := by
      apply hNoHalfLines (x + v) (-v)
      · simpa using neg_ne_zero.mpr hv0
      · intro y hy
        rcases hy with ⟨t, ht, rfl⟩
        exact hnegvRec hxv ht
    have hBackward : f x ≤ f (x + v) := by
      have hStep :=
        helperForTheorem_32_3_le_of_mem_recessionCone_bddAbove_halfLine
          (n := n) (C := C) (f := f) hCconv hf hnegvRec hxv hBddNeg 1 zero_le_one
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hStep
    exact le_antisymm hForward hBackward

/-- Helper for Theorem 32.3: the recession cone of the orthogonal complement is the orthogonal
complement itself. -/
lemma helperForTheorem_32_3_recessionCone_orthogonal_eq
    {n : ℕ}
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Set.recessionCone ((Lᗮ : Set (EuclideanSpace ℝ (Fin n)))) =
      (Lᗮ : Set (EuclideanSpace ℝ (Fin n))) := by
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Lᗮ
  have hWconv : Convex ℝ (W : Set (EuclideanSpace ℝ (Fin n))) := W.convex
  ext y
  constructor
  · -- A recession direction of a submodule already lies in that submodule by testing at `0`.
    intro hy
    have hy' : ∀ x ∈ (W : Set (EuclideanSpace ℝ (Fin n))), x + y ∈ (W : Set _) := by
      rw [recessionCone_eq_add_mem (C := (W : Set (EuclideanSpace ℝ (Fin n)))) hWconv] at hy
      exact hy
    have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ (W : Set _) := by simp [W]
    simpa using hy' 0 hzero
  · -- Conversely, every submodule element translates the submodule into itself.
    intro hy
    have hy' : ∀ x ∈ (W : Set (EuclideanSpace ℝ (Fin n))), x + y ∈ (W : Set _) := by
      intro x hx
      exact W.add_mem hx hy
    rw [recessionCone_eq_add_mem (C := (W : Set (EuclideanSpace ℝ (Fin n)))) hWconv]
    exact hy'

/-- Helper for Theorem 32.3: the orthogonal slice `C ∩ Lᗮ` contains no lines once `L` is the
lineality space of `C`. -/
lemma helperForTheorem_32_3_no_lines_on_slice
    {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C)
    (hDne : (C ∩ (((Submodule.span ℝ (Set.linealitySpace C))ᗮ : Set _))).Nonempty) :
    ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧
      y ∈ (-Set.recessionCone (C ∩ (((Submodule.span ℝ (Set.linealitySpace C))ᗮ : Set _)))) ∩
        Set.recessionCone (C ∩ (((Submodule.span ℝ (Set.linealitySpace C))ᗮ : Set _))) := by
  let L : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ (Set.linealitySpace C)
  let D : Set (EuclideanSpace ℝ (Fin n)) := C ∩ (Lᗮ : Set _)
  have hPerpClosed : IsClosed (Lᗮ : Set (EuclideanSpace ℝ (Fin n))) :=
    Submodule.closed_of_finiteDimensional (s := Lᗮ)
  have hPerpConv : Convex ℝ (Lᗮ : Set (EuclideanSpace ℝ (Fin n))) := (Lᗮ).convex
  have hDrec :
      Set.recessionCone D =
        Set.recessionCone C ∩ Set.recessionCone (Lᗮ : Set (EuclideanSpace ℝ (Fin n))) := by
    simpa [D] using recessionCone_inter_eq hCclosed hPerpClosed hCconv hPerpConv hDne
  have hRecPerp :
      Set.recessionCone (Lᗮ : Set (EuclideanSpace ℝ (Fin n))) =
        (Lᗮ : Set (EuclideanSpace ℝ (Fin n))) := by
    simpa [L] using helperForTheorem_32_3_recessionCone_orthogonal_eq (n := n) L
  have hLset : (L : Set (EuclideanSpace ℝ (Fin n))) = Set.linealitySpace C := by
    simpa [L] using helperForTheorem_32_3_coe_span_linealitySpace_eq (n := n) (C := C) hCconv
  intro hLines
  rcases hLines with ⟨y, hyne, hy⟩
  have hyRecD : y ∈ Set.recessionCone D := hy.2
  have hnegRecD : -y ∈ Set.recessionCone D := by
    simpa [Set.mem_neg] using hy.1
  have hyRecSplit :
      y ∈ Set.recessionCone C ∩ Set.recessionCone (Lᗮ : Set (EuclideanSpace ℝ (Fin n))) := by
    simpa [hDrec] using hyRecD
  have hnegRecSplit :
      -y ∈ Set.recessionCone C ∩ Set.recessionCone (Lᗮ : Set (EuclideanSpace ℝ (Fin n))) := by
    simpa [hDrec] using hnegRecD
  have hyLineality : y ∈ Set.linealitySpace C := by
    have hyNegRec : y ∈ -Set.recessionCone C := by
      simpa [Set.mem_neg] using hnegRecSplit.1
    simpa [Set.linealitySpace] using And.intro hyNegRec hyRecSplit.1
  have hyL : y ∈ L := by
    change y ∈ (L : Set (EuclideanSpace ℝ (Fin n)))
    rw [hLset]
    exact hyLineality
  have hyPerp : y ∈ (Lᗮ : Set (EuclideanSpace ℝ (Fin n))) := by
    simpa [hRecPerp] using hyRecSplit.2
  -- Membership in both `L` and `Lᗮ` forces the vector to vanish.
  have hyInf : y ∈ (L ⊓ Lᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :=
    Submodule.mem_inf.mpr ⟨hyL, hyPerp⟩
  have hbot : (L ⊓ Lᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) = ⊥ := by
    simpa using (Submodule.inf_orthogonal_eq_bot (K := L))
  have hyZero : y ∈ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := by
    simpa [hbot] using hyInf
  have hyEqZero : y = 0 := by
    simpa using hyZero
  exact hyne hyEqZero

/-- Helper for Theorem 32.3: every value on `C` already occurs on the orthogonal slice
`C ∩ Lᗮ`. -/
lemma helperForTheorem_32_3_exists_sliceRepresentative_sameValue
    {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hCconv : Convex ℝ C)
    (hf : ConvexOn ℝ C f)
    (hNoHalfLines : NoUnboundedAboveOnHalfLines f C) :
    ∀ x ∈ C,
      ∃ y ∈ C ∩ (((Submodule.span ℝ (Set.linealitySpace C))ᗮ : Set _)), f x = f y := by
  let L : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ (Set.linealitySpace C)
  intro x hxC
  -- Move `x` to its orthogonal slice representative and use lineality-fiber constancy to keep
  -- the same function value.
  rcases helperForTheorem_32_3_exists_sliceRepresentative
      (n := n) (C := C) hCconv hxC with
    ⟨y, hyD, hyEq⟩
  have hproj_mem_L : L.starProjection x ∈ L :=
    Submodule.starProjection_apply_mem (U := L) (x := x)
  have hLset : (L : Set (EuclideanSpace ℝ (Fin n))) = Set.linealitySpace C := by
    simpa [L] using helperForTheorem_32_3_coe_span_linealitySpace_eq (n := n) (C := C) hCconv
  have hproj_lineality : L.starProjection x ∈ Set.linealitySpace C := by
    exact hLset ▸ hproj_mem_L
  have hneg_lineality : -L.starProjection x ∈ Set.linealitySpace C := by
    have hproj_lineality' :
        L.starProjection x ∈ (-Set.recessionCone C) ∩ Set.recessionCone C := by
      simpa [Set.linealitySpace] using hproj_lineality
    have hneg_mem_neg : -L.starProjection x ∈ -Set.recessionCone C := by
      simpa [Set.mem_neg] using hproj_lineality'.2
    have hneg_mem_pos : -L.starProjection x ∈ Set.recessionCone C := by
      simpa [Set.mem_neg] using hproj_lineality'.1
    simpa [Set.linealitySpace] using And.intro hneg_mem_neg hneg_mem_pos
  have hvalue :
      f (x + (-L.starProjection x)) = f x :=
    helperForTheorem_32_3_eq_value_of_add_mem_linealitySpace
      (n := n) (C := C) (f := f) hCconv hf hNoHalfLines hxC hneg_lineality
  refine ⟨y, by simpa [L] using hyD, ?_⟩
  -- Rewrite the slice representative as the translated point covered by the previous helper.
  simpa [hyEq, sub_eq_add_neg] using hvalue.symm

end Section32
end Chap06
