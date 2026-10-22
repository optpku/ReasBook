/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_8
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_21

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Topology

section

/-
Theorem 3.22 is `source-facing` at the Chapter 3 owner `subdifferential`. Domain sampling for the
max-rule API points to the following relevant declarations:

* `subdifferential` in `Definition_3_2` as the owner object.
* `directional_derivative_iSup_eq_iSup_active_indices` in `Theorem_3_9` for the canonical active
  index subtype of a finite pointwise supremum.
* `directional_derivative_eq_support_function_subdifferential_at_interior_point` in
  `Proposition_3_10` as the support-function bridge from directional derivatives to
  subdifferentials.
* `convexHull_iUnion_active_subdifferential_subset_subdifferential_iSup` in `Theorem_3_23` as the
  owner-level weak inclusion for the same active subdifferential family.

The primitive data here is only the ambient subdifferential of the supremum; the active-index
family is derived data and stays inline instead of being repackaged as a parallel public wrapper.
Those owner-level ingredients already live on the ambient finite-dimensional real normed-space
hypotheses, so no Euclidean structure belongs in the public statement here. As in the nearby
interior-point sum rules, membership `x ∈ ⋂ i, interior (effective_domain (f i))` already forces
each effective domain to be nonempty, so the public hypothesis only retains the genuinely used
no-`⊥` part.
-/
variable {E : Type u} {ι : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Finite ι] [Nonempty ι]

recall effective_domain
recall finite_domain
recall is_convex_function
recall subdifferential
recall strongDualSubdifferential
recall strongDualSubdifferential_eq_image_subdifferential
recall directional_derivative
recall support_function
recall isClosed_subdifferential
recall subdifferential_bounded_at_interior_point
recall subdifferential_nonempty_at_interior_point
recall directional_derivative_eq_support_function_subdifferential_at_interior_point
recall directional_derivative_iSup_eq_iSup_active_indices
recall eq_of_supportFunction_eq_forall_evalPoint

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.22: the pointwise supremum of a finite family of functions that never
attain `⊥` also never attains `⊥`. -/
lemma pointwiseSup_ne_bot
    (f : ι → E → EReal)
    (h_ne_bot : ∀ i : ι, ∀ y : E, f i y ≠ ⊥) :
    ∀ y : E, (⨆ i : ι, f i y) ≠ ⊥ := by
  intro y hsup
  rcases ‹Nonempty ι› with ⟨i₀⟩
  have hle : f i₀ y ≤ ⨆ i : ι, f i y :=
    Finite.le_ciSup_of_le i₀ le_rfl
  have hbot : f i₀ y = ⊥ := le_bot_iff.mp (hsup ▸ hle)
  exact h_ne_bot i₀ y hbot

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.22: an interior point of every branch effective domain is also an
interior point of the effective domain of the finite pointwise supremum. -/
lemma pointwiseSup_memInterior_effectiveDomain
    (f : ι → E → EReal) (x : E)
    (hx : x ∈ ⋂ i : ι, interior (effective_domain (f i))) :
    x ∈ interior (effective_domain fun y ↦ ⨆ i : ι, f i y) := by
  let U : Set E := ⋂ i : ι, interior (effective_domain (f i))
  have hU_open : IsOpen U := isOpen_iInter_of_finite fun _ ↦ isOpen_interior
  have hUx : x ∈ U := hx
  refine mem_interior_iff_mem_nhds.2 <| Filter.mem_of_superset (hU_open.mem_nhds hUx) ?_
  intro y hy
  obtain ⟨i₀, hi₀⟩ : ∃ i : ι, f i y = ⨆ j : ι, f j y := by
    simpa using (exists_eq_ciSup_of_finite (f := fun i : ι ↦ f i y))
  have hyi : y ∈ effective_domain (f i₀) :=
    interior_subset ((Set.mem_iInter.mp hy) i₀)
  simpa [effective_domain, hi₀] using hyi

/-- Helper for Theorem 3.22: evaluating the support function after transporting an algebraic-dual
set through `LinearMap.toContinuousLinearMap` is the same as evaluating the original support
function at the corresponding point-evaluation functional. -/
lemma supportFunction_image_toContinuousLinearMap_eval
    (S : Set (Module.Dual ℝ E)) (d : E) :
    support_function
        ((LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) '' S)
        (ContinuousLinearMap.apply ℝ ℝ d) =
      support_function S (Module.Dual.eval ℝ E d) := by
  -- Rewrite both support functions to the corresponding pairing-image suprema.
  rw [support_function_apply, support_function_apply]
  congr 1
  ext z
  constructor
  · rintro ⟨ψ, ⟨φ, hφ, rfl⟩, rfl⟩
    exact ⟨φ, hφ, by simp [Module.Dual.eval_apply]⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨LinearMap.toContinuousLinearMap φ, ⟨φ, hφ, rfl⟩, by simp [Module.Dual.eval_apply]⟩

/-- Helper for Theorem 3.22: the support function of an indexed union is the indexed supremum of
the support functions. -/
lemma supportFunction_iUnion_apply
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {κ : Type*} (A : κ → Set V) (l : Module.Dual ℝ V) :
    support_function (⋃ i : κ, A i) l = ⨆ i : κ, support_function (A i) l := by
  -- Normalize the support function to `sSup` and use the complete-lattice union formula.
  rw [support_function_apply, Set.image_iUnion, sSup_iUnion]
  simp_rw [support_function_apply]

/-- Helper for Theorem 3.22: a linear functional has the same support function on a set and on its
convex hull. -/
lemma supportFunction_convexHull_apply
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Set V) (l : Module.Dual ℝ V) :
    support_function (convexHull ℝ A) l = support_function A l := by
  -- The easy direction comes from `A ⊆ convexHull ℝ A`; the reverse direction uses that a linear
  -- functional is convex and therefore attains no larger value on the convex hull.
  rw [support_function_apply, support_function_apply]
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hzA, hzy⟩ :=
      (LinearMap.convexOn l (convex_univ : Convex ℝ (Set.univ : Set V))).exists_ge_of_mem_convexHull
        (Set.subset_univ A) hy
    exact
      (show (l y : EReal) ≤ (l z : EReal) from by exact_mod_cast hzy).trans <|
        le_sSup ⟨z, hzA, rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    exact le_sSup ⟨y, subset_convexHull ℝ A hy, rfl⟩

/-- Helper for Theorem 3.22: the strong-dual subdifferential at an interior point is compact. -/
lemma isCompact_strongDualSubdifferential_at_interior_point
    (f : E → EReal) (x : E)
    (h_ne_bot : ∀ y : E, f y ≠ ⊥)
    (hconvex : is_convex_function f)
    (hx : x ∈ interior (effective_domain f)) :
    IsCompact (∂ₛ f(x)) := by
  -- Combine the existing closedness theorem with the interior-point boundedness theorem.
  have hbounded : Bornology.IsBounded (∂ₛ f(x)) := by
    simpa using
      subdifferential_bounded_at_interior_point
        (f := f) (x := x) (h_ne_bot := fun y _ ↦ h_ne_bot y) hconvex hx
  rcases hbounded.subset_closedBall (0 : StrongDual ℝ E) with ⟨R, hR⟩
  exact (isCompact_closedBall (0 : StrongDual ℝ E) R).of_isClosed_subset
    (isClosed_subdifferential f x) hR

omit [Nonempty ι] in
/-- Helper for Theorem 3.22: the convex hull of the active strong-dual branch subdifferentials is
compact. -/
lemma isCompact_convexHull_iUnion_active_strongDualSubdifferential
    (f : ι → E → EReal) (x : E)
    (h_ne_bot : ∀ i : ι, ∀ y : E, f i y ≠ ⊥)
    (hconvex : ∀ i : ι, is_convex_function (f i))
    (hx : x ∈ ⋂ i : ι, interior (effective_domain (f i))) :
    IsCompact
      (convexHull ℝ
        (⋃ i : {i : ι // f i x = ⨆ j : ι, f j x}, ∂ₛ (f i.1)(x))) := by
  classical
  let active : Type v := {i : ι // f i x = ⨆ j : ι, f j x}
  letI : Fintype active := Fintype.ofFinite active
  let A : active → Set (StrongDual ℝ E) := fun i ↦ ∂ₛ (f i.1)(x)
  let C : Set (StrongDual ℝ E) :=
    {g | ∃ l : stdSimplex ℝ active, ∃ z : active → StrongDual ℝ E,
        (∀ i, z i ∈ A i) ∧ ∑ i, (l : active → ℝ) i • z i = g}
  -- Each active branch contributes a compact strong-dual subdifferential.
  have hbranch_compact : ∀ i : active, IsCompact (A i) := by
    intro i
    simpa [A] using
      isCompact_strongDualSubdifferential_at_interior_point
        (f := f i.1) (x := x) (h_ne_bot := h_ne_bot i.1) (hconvex := hconvex i.1)
        (hx := (Set.mem_iInter.mp hx) i.1)
  have hbranch_nonempty : ∀ i : active, (A i).Nonempty := by
    intro i
    rcases
        subdifferential_nonempty_at_interior_point (f i.1) x
          (hconvex i.1) ((Set.mem_iInter.mp hx) i.1) with
      ⟨g, hg⟩
    refine ⟨LinearMap.toContinuousLinearMap g, ?_⟩
    simpa [A, strongDualSubdifferential_eq_image_subdifferential] using
      show LinearMap.toContinuousLinearMap g ∈ ∂ₛ (f i.1)(x) from by
        rw [strongDualSubdifferential_eq_image_subdifferential]
        exact ⟨g, hg, rfl⟩
  have hbranch_convex : ∀ i : active, Convex ℝ (A i) := by
    intro i
    simpa [A] using convex_strongDualSubdifferential (f i.1) x
  choose base hbase using hbranch_nonempty
  let weightedSum : (active → ℝ) × (active → StrongDual ℝ E) → StrongDual ℝ E :=
    fun p ↦ ∑ i, p.1 i • p.2 i
  let D : Set ((active → ℝ) × (active → StrongDual ℝ E)) :=
    stdSimplex ℝ active ×ˢ Set.univ.pi A
  have hD_compact : IsCompact D := by
    -- The simplex factor and the finite product of branch compact sets are both compact.
    exact (isCompact_stdSimplex ℝ active).prod <| isCompact_univ_pi hbranch_compact
  have hweightedSum_cont : Continuous weightedSum := by
    -- The weighted sum map is continuous because it is a finite sum of coordinatewise smul maps.
    unfold weightedSum
    fun_prop
  have hC_image : C = weightedSum '' D := by
    -- Rewrite the existential description of `C` as the image of the compact simplex/product model.
    ext g
    constructor
    · rintro ⟨l, z, hz, rfl⟩
      refine ⟨(l, z), ?_, rfl⟩
      constructor
      · exact l.2
      · simpa [Set.mem_pi] using hz
    · rintro ⟨⟨l, z⟩, hzD, rfl⟩
      rcases hzD with ⟨hl, hz⟩
      refine ⟨⟨l, hl⟩, z, ?_, rfl⟩
      simpa [Set.mem_pi] using hz
  have hC_compact : IsCompact C := by
    -- Compactness is inherited from the compact model through the continuous weighted-sum map.
    rw [hC_image]
    exact hD_compact.image hweightedSum_cont
  have hC_subset :
      C ⊆ convexHull ℝ (⋃ i : active, A i) := by
    intro g hg
    rcases hg with ⟨l, z, hz, rfl⟩
    -- Any simplex-weighted active selection is a convex combination of points in the active union.
    refine mem_convexHull_of_exists_fintype (w := fun i ↦ (l : active → ℝ) i) (z := z) ?_ ?_ ?_ rfl
    · intro i
      exact stdSimplex.zero_le l i
    · exact stdSimplex.sum_eq_one l
    · intro i
      exact Set.mem_iUnion.2 ⟨i, hz i⟩
  have hunion_subset :
      (⋃ i : active, A i) ⊆ C := by
    intro g hg
    rcases Set.mem_iUnion.1 hg with ⟨i, hgi⟩
    let z : active → StrongDual ℝ E := fun j ↦ if j = i then g else base j
    -- Embed an active branch element using the simplex vertex concentrated at that branch.
    refine ⟨stdSimplex.vertex i, z, ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · simpa [z, hji] using hgi
      · simpa [z, hji] using hbase j
    · calc
        ∑ j, ((stdSimplex.vertex i : active → ℝ) j) • z j = z i := by
          simp [stdSimplex.vertex]
        _ = g := by
          simp [z]
  have hC_convex : Convex ℝ C := by
    intro g hg h hh a b ha hb hab
    rcases hg with ⟨l, z, hz, rfl⟩
    rcases hh with ⟨μ, w, hw, rfl⟩
    let ν : stdSimplex ℝ active :=
      ⟨a • (l : active → ℝ) + b • (μ : active → ℝ),
        (convex_stdSimplex ℝ active) l.2 μ.2 ha hb hab⟩
    have hu :
        ∀ i : active,
          ∃ u ∈ A i,
            ((ν : active → ℝ) i) • u =
              (a * (l : active → ℝ) i) • z i + (b * (μ : active → ℝ) i) • w i := by
      intro i
      refine
        (hbranch_convex i).exists_mem_add_smul_eq (hz i) (hw i)
          (mul_nonneg ha <| stdSimplex.zero_le l i)
          (mul_nonneg hb <| stdSimplex.zero_le μ i)
    choose u hu_mem hu_eq using hu
    refine ⟨ν, u, hu_mem, ?_⟩
    -- Combine the branchwise convexity identities into one global convexity witness for `C`.
    calc
      ∑ i, ((ν : active → ℝ) i) • u i
          = ∑ i, ((a * (l : active → ℝ) i) • z i + (b * (μ : active → ℝ) i) • w i) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              simpa [ν] using hu_eq i
      _ = (∑ i, (a * (l : active → ℝ) i) • z i) + ∑ i, (b * (μ : active → ℝ) i) • w i := by
            rw [Finset.sum_add_distrib]
      _ = a • (∑ i, (l : active → ℝ) i • z i) + b • ∑ i, (μ : active → ℝ) i • w i := by
            simp_rw [mul_smul]
            rw [← Finset.smul_sum, ← Finset.smul_sum]
      _ = a • (∑ i, (l : active → ℝ) i • z i) + b • (∑ i, (μ : active → ℝ) i • w i) := by
            rfl
  have hconvexHull_subset :
      convexHull ℝ (⋃ i : active, A i) ⊆ C :=
    convexHull_min hunion_subset hC_convex
  have hC_eq : C = convexHull ℝ (⋃ i : active, A i) := by
    exact Set.Subset.antisymm hC_subset hconvexHull_subset
  -- Route correction: use the compact simplex/product model `C`, then identify it with the target
  -- convex hull via containment and convexity instead of expanding generic convex-hull witnesses.
  rw [← hC_eq]
  exact hC_compact

-- Proof sketch: combine the max-directional-derivative formula for the indexed supremum
-- `fun y ↦ ⨆ i, f i y` with the support-function description of subdifferentials at interior
-- points. The right-hand side is the convex hull of the union of the active subdifferentials over
-- the canonical active-index subtype, and equality of support functions of the two nonempty
-- compact convex sets then identifies the sets themselves.
/-- Theorem 3.22: max rule of subdifferential calculus. For a nonempty finite family of convex
functions that never attain `-∞`, the owner subdifferential `∂ (fun y ↦ ⨆ i, f i y)(x)` at an
interior point is the convex hull of the union of the active subdifferentials `∂ (f i)(x)`. -/
theorem subdifferential_pointwise_max_eq_convexHull_iUnion_active_subdifferential
    (f : ι → E → EReal) (x : E)
    (h_ne_bot : ∀ i : ι, ∀ y : E, f i y ≠ ⊥)
    (hconvex : ∀ i : ι, is_convex_function (f i))
    (hx : x ∈ ⋂ i : ι, interior (effective_domain (f i))) :
    ∂ (fun y ↦ ⨆ i : ι, f i y)(x) =
      convexHull ℝ (⋃ i : {i : ι // f i x = ⨆ j : ι, f j x}, ∂ (f i)(x)) :=
  by
    let F : E → EReal := fun y ↦ ⨆ i : ι, f i y
    let active : Type v := {i : ι // f i x = F x}
    let e : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E := LinearMap.toContinuousLinearMap
    have hconvexF : is_convex_function F := by
      -- The ambient pointwise supremum stays convex because each branch is convex.
      simpa [F] using is_convex_function_iSup hconvex
    have hxFinite :
        x ∈ ⋂ i : ι, interior (finite_domain (f i)) := by
      -- Each branch avoids `⊥`, so its finite and effective domains agree.
      rw [Set.mem_iInter]
      intro i
      have hxi : x ∈ interior (effective_domain (f i)) := (Set.mem_iInter.mp hx) i
      simpa [finite_domain_eq_effective_domain (h_ne_bot i)] using hxi
    have hF_ne_bot : ∀ y : E, F y ≠ ⊥ := by
      -- The finite pointwise supremum inherits the no-`⊥` property from any chosen branch.
      simpa [F] using pointwiseSup_ne_bot f h_ne_bot
    have hxF_effective : x ∈ interior (effective_domain F) :=
      pointwiseSup_memInterior_effectiveDomain f x hx
    have hxF_finite : x ∈ interior (finite_domain F) := by
      simpa [finite_domain_eq_effective_domain hF_ne_bot] using hxF_effective
    have hactive_nonempty : Nonempty active := by
      obtain ⟨i₀, hi₀⟩ : ∃ i : ι, f i x = F x := by
        simpa [F] using (exists_eq_ciSup_of_finite (f := fun i : ι ↦ f i x))
      exact ⟨⟨i₀, hi₀⟩⟩
    have hA_nonempty : (∂ₛ F(x)).Nonempty := by
      rcases subdifferential_nonempty_at_interior_point F x hconvexF hxF_effective with ⟨g, hg⟩
      refine ⟨LinearMap.toContinuousLinearMap g, ?_⟩
      rw [strongDualSubdifferential_eq_image_subdifferential]
      exact ⟨g, hg, rfl⟩
    have hA_compact : IsCompact (∂ₛ F(x)) :=
      isCompact_strongDualSubdifferential_at_interior_point F x hF_ne_bot hconvexF hxF_effective
    have hA_convex : Convex ℝ (∂ₛ F(x)) :=
      convex_strongDualSubdifferential F x
    have hB_nonempty :
        (convexHull ℝ (⋃ i : active, ∂ₛ (f i.1)(x))).Nonempty := by
      rcases hactive_nonempty with ⟨i₀⟩
      rcases
          subdifferential_nonempty_at_interior_point (f i₀.1) x
            (hconvex i₀.1) ((Set.mem_iInter.mp hx) i₀.1) with
        ⟨g, hg⟩
      have hg_strong : LinearMap.toContinuousLinearMap g ∈ ∂ₛ (f i₀.1)(x) := by
        rw [strongDualSubdifferential_eq_image_subdifferential]
        exact ⟨g, hg, rfl⟩
      exact
        convexHull_nonempty_iff.2
          ⟨LinearMap.toContinuousLinearMap g, Set.mem_iUnion.2 ⟨i₀, hg_strong⟩⟩
    have hB_compact :
        IsCompact (convexHull ℝ (⋃ i : active, ∂ₛ (f i.1)(x))) :=
      isCompact_convexHull_iUnion_active_strongDualSubdifferential
        f x h_ne_bot hconvex hx
    have hB_convex : Convex ℝ (convexHull ℝ (⋃ i : active, ∂ₛ (f i.1)(x))) :=
      convex_convexHull ℝ _
    have hσ :
        ∀ d : E,
          support_function (∂ₛ F(x)) (ContinuousLinearMap.apply ℝ ℝ d) =
            support_function
              (convexHull ℝ (⋃ i : active, ∂ₛ (f i.1)(x)))
              (ContinuousLinearMap.apply ℝ ℝ d) := by
      intro d
      have hdir :
          ∀ i : ι, ∃ ℓ : ℝ, has_directional_derivative_at (f i) x d (ℓ : EReal) := by
        intro i
        exact
          exists_real_has_directional_derivative_at_of_convex_interior_point
            (f := f i) (x := x) (d := d) (hconvex i) ((Set.mem_iInter.mp hxFinite) i)
      -- Compare both support functions through the Chapter 3 directional-derivative formulas.
      calc
        support_function (∂ₛ F(x)) (ContinuousLinearMap.apply ℝ ℝ d)
            = support_function (∂ F(x)) (Module.Dual.eval ℝ E d) := by
                rw [strongDualSubdifferential_eq_image_subdifferential]
                exact supportFunction_image_toContinuousLinearMap_eval (S := ∂ F(x)) d
        _ = directional_derivative F x d := by
          symm
          simpa [F] using
            directional_derivative_eq_support_function_subdifferential_at_interior_point
              (f := F) (x := x) (d := d) hconvexF hxF_finite
        _ = ⨆ i : active, directional_derivative (f i.1) x d := by
          simpa [F, active] using
            directional_derivative_iSup_eq_iSup_active_indices
              (f := f) (x := x) (d := d) hxFinite hdir
        _ = ⨆ i : active,
              support_function (∂ₛ (f i.1)(x)) (ContinuousLinearMap.apply ℝ ℝ d) := by
          refine iSup_congr fun i ↦ ?_
          calc
            directional_derivative (f i.1) x d
                = support_function (∂ (f i.1)(x)) (Module.Dual.eval ℝ E d) := by
                    have hxi_finite : x ∈ interior (finite_domain (f i.1)) := by
                      simpa [finite_domain_eq_effective_domain (h_ne_bot i.1)] using
                        ((Set.mem_iInter.mp hx) i.1)
                    simpa using
                      directional_derivative_eq_support_function_subdifferential_at_interior_point
                        (f := f i.1) (x := x) (d := d) (hconvex i.1) hxi_finite
            _ = support_function (∂ₛ (f i.1)(x)) (ContinuousLinearMap.apply ℝ ℝ d) := by
              rw [strongDualSubdifferential_eq_image_subdifferential]
              symm
              exact supportFunction_image_toContinuousLinearMap_eval
                (S := ∂ (f i.1)(x)) d
        _ = support_function (⋃ i : active, ∂ₛ (f i.1)(x)) (ContinuousLinearMap.apply ℝ ℝ d) := by
          symm
          exact supportFunction_iUnion_apply
            (A := fun i : active ↦ ∂ₛ (f i.1)(x))
            (l := ContinuousLinearMap.apply ℝ ℝ d)
        _ =
            support_function
              (convexHull ℝ (⋃ i : active, ∂ₛ (f i.1)(x)))
              (ContinuousLinearMap.apply ℝ ℝ d) := by
          symm
          exact supportFunction_convexHull_apply _ _
    have hstrong :
        ∂ₛ F(x) = convexHull ℝ (⋃ i : active, ∂ₛ (f i.1)(x)) := by
      -- Route correction: compare the two strong-dual sets by support functions on evaluation
      -- functionals, then invoke the finite-dimensional separation theorem from Theorem 3.21.
      exact
        eq_of_supportFunction_eq_forall_evalPoint
          hA_nonempty hA_compact hA_convex hB_nonempty hB_compact hB_convex hσ
    have himage :
        e '' ∂ F(x) = e '' convexHull ℝ (⋃ i : active, ∂ (f i.1)(x)) := by
      -- Transport the strong-dual equality back through the canonical finite-dimensional
      -- equivalence `LinearMap.toContinuousLinearMap`.
      calc
        e '' ∂ F(x) = ∂ₛ F(x) := by
          simpa [e] using (strongDualSubdifferential_eq_image_subdifferential F x).symm
        _ = convexHull ℝ (⋃ i : active, ∂ₛ (f i.1)(x)) := hstrong
        _ = convexHull ℝ (⋃ i : active, e '' ∂ (f i.1)(x)) := by
          congr 1
          ext z
          simp [e, strongDualSubdifferential_eq_image_subdifferential]
        _ = convexHull ℝ (e '' (⋃ i : active, ∂ (f i.1)(x))) := by
          rw [← Set.image_iUnion]
        _ = e '' convexHull ℝ (⋃ i : active, ∂ (f i.1)(x)) := by
          simpa [e] using
            (LinearMap.image_convexHull
              (f := e.toLinearMap) (s := ⋃ i : active, ∂ (f i.1)(x))).symm
    have hpre := congrArg (Set.preimage e) himage
    simpa [F, e, Set.preimage_image_eq _ e.injective] using hpre

end
