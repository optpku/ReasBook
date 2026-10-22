/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped BigOperators

variable {ι : Type v} [Fintype ι] [Nonempty ι]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- Helper for Corollary 3.1.2.1: a continuous linear functional on a finite product `ι → ℝ` is
determined by its values on the standard coordinate vectors `Pi.single i 1`. -/
theorem strongDual_apply_fintype
    [DecidableEq ι]
    (g : StrongDual ℝ (ι → ℝ)) (z : ι → ℝ) :
    g z = ∑ i, z i * g (Pi.single i 1) := by
  -- Expand `z` in the standard basis and then use linearity termwise.
  have hdecomp :
      z = ∑ i, Pi.single i (z i) := by
    ext j
    simp
  rw [hdecomp, map_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hsingle :
      Pi.single i (z i) = z i • (Pi.single (M := fun _ ↦ ℝ) i 1) := by
    ext j
    by_cases h : i = j
    · subst h
      simp
    · simp [Pi.single_eq_of_ne (Ne.symm h)]
  rw [hsingle, map_smul]
  simp [smul_eq_mul]

/-- Helper for Corollary 3.1.2.1: if `Q` is nonempty and the constrained sublevel sets of the
finite maximum are bounded, then that maximum attains its minimum on `Q`. -/
theorem exists_isMinOn_familyMaximum_of_bounded_sublevels
    {Q : Set E} {fs : ι → E → ℝ}
    (hfs : ∀ i, ClosedConvexOn Q (fun x ↦ (fs i x : WithTop ℝ)))
    (hbounded :
      ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet Q (fun x ↦ ((maxTypeObjective fs x : ℝ) : WithTop ℝ)) α))
    (hQ_nonempty : Q.Nonempty) :
    ∃ xStar : Q, IsMinOn (fun x : Q ↦ maxTypeObjective fs x) Set.univ xStar := by
  classical
  let β₀ : ℝ := maxTypeObjective fs hQ_nonempty.some
  let S : Set E :=
    constrainedSublevelSet Q
      (fun x ↦ ((maxTypeObjective fs x : ℝ) : WithTop ℝ)) β₀
  have hsome_memS : hQ_nonempty.some ∈ S := by
    -- The reference feasible point lies in its own max-sublevel slice.
    refine mem_constrainedSublevelSet_iff.2 ?_
    exact ⟨hQ_nonempty.some_mem, le_rfl⟩
  have hS_subset : S ⊆ Q := by
    -- Membership in the constrained sublevel set already records feasibility.
    intro x hx
    exact (mem_constrainedSublevelSet_iff.mp hx).1
  have hS_closed : IsClosed S := by
    -- The max-sublevel slice is the finite intersection of the component sublevel slices.
    have hEq :
        S = ⋂ i : ι, constrainedSublevelSet Q (fun x ↦ (fs i x : WithTop ℝ)) β₀ := by
      ext x
      constructor
      · intro hx
        rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxQ, hxβ⟩
        have hxβ' : maxTypeObjective fs x ≤ β₀ := by
          exact_mod_cast hxβ
        rw [Set.mem_iInter]
        intro i
        refine mem_constrainedSublevelSet_iff.2 ⟨hxQ, ?_⟩
        exact_mod_cast (maxTypeObjective_le_iff fs x β₀).mp hxβ' i
      · intro hx
        have hxQ : x ∈ Q := by
          exact (mem_constrainedSublevelSet_iff.mp ((Set.mem_iInter.mp hx) (Classical.choice ‹Nonempty ι›))).1
        refine mem_constrainedSublevelSet_iff.2 ⟨hxQ, ?_⟩
        exact_mod_cast (maxTypeObjective_le_iff fs x β₀).mpr fun i ↦ by
          exact_mod_cast (mem_constrainedSublevelSet_iff.mp ((Set.mem_iInter.mp hx) i)).2
    rw [hEq]
    refine isClosed_iInter ?_
    intro i
    exact (hfs i).isClosed_constrainedSublevelSet β₀
  have hS_convex : Convex ℝ S := by
    -- The same finite-intersection description transfers convexity to the max-sublevel slice.
    have hEq :
        S = ⋂ i : ι, constrainedSublevelSet Q (fun x ↦ (fs i x : WithTop ℝ)) β₀ := by
      ext x
      constructor
      · intro hx
        rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxQ, hxβ⟩
        have hxβ' : maxTypeObjective fs x ≤ β₀ := by
          exact_mod_cast hxβ
        rw [Set.mem_iInter]
        intro i
        refine mem_constrainedSublevelSet_iff.2 ⟨hxQ, ?_⟩
        exact_mod_cast (maxTypeObjective_le_iff fs x β₀).mp hxβ' i
      · intro hx
        have hxQ : x ∈ Q := by
          exact (mem_constrainedSublevelSet_iff.mp ((Set.mem_iInter.mp hx) (Classical.choice ‹Nonempty ι›))).1
        refine mem_constrainedSublevelSet_iff.2 ⟨hxQ, ?_⟩
        exact_mod_cast (maxTypeObjective_le_iff fs x β₀).mpr fun i ↦ by
          exact_mod_cast (mem_constrainedSublevelSet_iff.mp ((Set.mem_iInter.mp hx) i)).2
    rw [hEq]
    refine convex_iInter ?_
    intro i
    exact (hfs i).convex_constrainedSublevelSet β₀
  have hS_bounded : Bornology.IsBounded S := by
    -- The bounded-slice hypothesis applies directly at the reference value `β₀`.
    simpa [S, β₀] using hbounded β₀
  have hS_compact : IsCompact S :=
    Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
  have hS_nonempty : S.Nonempty := ⟨hQ_nonempty.some, hsome_memS⟩
  have hfsS : ∀ i, ClosedConvexOn S (fun x ↦ (fs i x : WithTop ℝ)) := by
    -- Restrict each component to the compact slice.
    intro i
    exact (hfs i).restrict hS_closed hS_convex hS_subset
  have hmax_lower :
      LowerSemicontinuousOn (maxTypeObjective fs) S := by
    -- Finite maxima of lower-semicontinuous slice restrictions remain lower semicontinuous.
    have hiSup_lower : LowerSemicontinuousOn (fun x : E ↦ ⨆ i, fs i x) S :=
      lowerSemicontinuousOn_ciSup
        (fun x hx ↦ Finite.bddAbove_range (fun i : ι ↦ fs i x))
        fun i ↦
          (hfsS i).lowerSemicontinuousOn_real hS_closed
    have hmax_eq : maxTypeObjective fs = fun x : E ↦ ⨆ i, fs i x := by
      ext x
      rw [maxTypeObjective_apply, Finset.sup'_univ_eq_ciSup]
    simpa [hmax_eq] using hiSup_lower
  obtain ⟨xStar, hxStarS, hxStarMinS⟩ :=
    hmax_lower.exists_isMinOn hS_nonempty hS_compact
  have hxStarQ : xStar ∈ Q := hS_subset hxStarS
  have hxStar_beta : maxTypeObjective fs xStar ≤ β₀ := by
    exact_mod_cast (mem_constrainedSublevelSet_iff.mp hxStarS).2
  have hxStarMinQ : IsMinOn (maxTypeObjective fs) Q xStar := by
    -- Outside the compact slice the objective is forced above `β₀`, so `xStar` still minimizes on `Q`.
    intro y hyQ
    by_cases hyS : y ∈ S
    · exact hxStarMinS hyS
    · have hy_not_le : ¬ maxTypeObjective fs y ≤ β₀ := by
        intro hyβ
        exact hyS (mem_constrainedSublevelSet_iff.2 ⟨hyQ, by exact_mod_cast hyβ⟩)
      exact le_trans hxStar_beta (le_of_lt (lt_of_not_ge hy_not_le))
  refine ⟨⟨xStar, hxStarQ⟩, ?_⟩
  -- Repackage the ambient minimizer as a minimizer on the subtype `Q`.
  rw [isMinOn_univ_iff]
  intro x
  rw [isMinOn_iff] at hxStarMinQ
  exact hxStarMinQ x x.property

/-- Helper for Corollary 3.1.2.1: the upper image attached to a minimizer of the family maximum is
convex, has nonempty interior, contains the minimizing diagonal point, and that diagonal point lies
on its boundary. -/
theorem upperImage_boundary_of_familyMaximum_minimizer
    {Q : Set E} {fs : ι → E → ℝ} (xStar : Q)
    (hfs : ∀ i, ClosedConvexOn Q (fun x ↦ (fs i x : WithTop ℝ)))
    (hxStarMin : IsMinOn (fun x : Q ↦ maxTypeObjective fs x) Set.univ xStar) :
    let fStar := maxTypeObjective fs xStar
    let U : Set (ι → ℝ) := {p | ∃ x ∈ Q, ∀ i, fs i x ≤ p i}
    Convex ℝ U ∧
      (fun _ ↦ fStar) ∈ U ∧
      (interior U).Nonempty ∧
      (fun _ ↦ fStar) ∉ interior U := by
  classical
  let fStar : ℝ := maxTypeObjective fs xStar
  let U : Set (ι → ℝ) := {p | ∃ x ∈ Q, ∀ i, fs i x ≤ p i}
  have hconv : ∀ i, ConvexOn ℝ Q (fs i) := by
    -- Each component inherits ordinary real-valued convexity from its lifted closed-convex hypothesis.
    intro i
    exact (hfs i).convexOn_real
  have hU_convex : Convex ℝ U := by
    -- The upper image is stable under convex combinations because each coordinate is.
    intro p hp q hq a b ha hb hab
    rcases hp with ⟨x, hxQ, hx⟩
    rcases hq with ⟨y, hyQ, hy⟩
    refine ⟨a • x + b • y, (hfs (Classical.choice ‹Nonempty ι›)).convex hxQ hyQ ha hb hab, ?_⟩
    intro i
    change fs i (a • x + b • y) ≤ a * p i + b * q i
    have hcv : fs i (a • x + b • y) ≤ a * fs i x + b * fs i y := by
      simpa [smul_eq_mul] using (hconv i).2 hxQ hyQ ha hb hab
    have hxmul : a * fs i x ≤ a * p i := mul_le_mul_of_nonneg_left (hx i) ha
    have hymul : b * fs i y ≤ b * q i := mul_le_mul_of_nonneg_left (hy i) hb
    exact hcv.trans (add_le_add hxmul hymul)
  have hdStar_mem : (fun _ ↦ fStar) ∈ U := by
    -- At the minimizing point, every component lies below the family maximum.
    refine ⟨xStar, xStar.property, ?_⟩
    intro i
    exact (maxTypeObjective_le_iff fs xStar fStar).mp le_rfl i
  have hU_int_nonempty : (interior U).Nonempty := by
    -- Any feasible point provides an open orthant contained in the upper image.
    let p0 : ι → ℝ := fun i ↦ fs i xStar + 1
    let V : Set (ι → ℝ) := Set.pi Set.univ (fun i ↦ Set.Ioi (fs i xStar))
    have hp0_memV : p0 ∈ V := by
      simp [p0, V]
    have hV_open : IsOpen V := by
      refine isOpen_set_pi Set.finite_univ ?_
      intro i hi
      exact isOpen_Ioi
    have hV_subset : V ⊆ U := by
      intro p hp
      refine ⟨xStar, xStar.property, ?_⟩
      intro i
      exact (Set.mem_pi.mp hp i (by simp)).le
    refine ⟨p0, mem_interior_iff_mem_nhds.2 ?_⟩
    exact Filter.mem_of_superset (hV_open.mem_nhds hp0_memV) hV_subset
  have hdStar_not_mem_interior : (fun _ ↦ fStar) ∉ interior U := by
    -- A full neighborhood inside `U` would contain a strictly smaller constant vector, violating minimality.
    intro hdStar_int
    rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hdStar_int) with ⟨ε, hε, hεball⟩
    let pDown : ι → ℝ := fun _ ↦ fStar - ε / 2
    have hpDown_dist : dist pDown (fun _ ↦ fStar) < ε := by
      rw [dist_pi_lt_iff hε]
      intro i
      simpa [pDown, abs_of_pos hε] using (show ε / 2 < ε by linarith)
    have hpDown_memU : pDown ∈ U := interior_subset (hεball hpDown_dist)
    rcases hpDown_memU with ⟨x, hxQ, hx⟩
    have hxle : maxTypeObjective fs x ≤ fStar - ε / 2 := by
      exact (maxTypeObjective_le_iff fs x (fStar - ε / 2)).2 fun i ↦ by
        simpa [pDown] using hx i
    have hxlt : maxTypeObjective fs x < fStar := by
      linarith
    rw [isMinOn_univ_iff] at hxStarMin
    exact (not_lt_of_ge (hxStarMin ⟨x, hxQ⟩)) hxlt
  exact ⟨hU_convex, hdStar_mem, hU_int_nonempty, hdStar_not_mem_interior⟩

/- Corollary 3.1.2.1 lies in the chapter's convex-analysis/minimax-linearization domain.

Relevant owner-style declarations sampled in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`, the chapter owner for closed convexity on a
  feasible set
- `maxTypeObjective` and `maxTypeObjective_apply` from `Chap02/Lemma_2_18`, the project owner for
  the finite maximum of a nonempty real-valued family
- `constrainedSublevelSet` from `Definition_3_3`, the chapter owner for bounded feasible
  sublevel families of `WithTop ℝ`-valued objectives
- `exists_minimax_parameter_of_bounded_constrainedSublevelSets` from `Theorem_3_1_2_6`, the
  two-function owner theorem used by the recursive proof strategy
- `StdSimplex`, `ConvexSpace.convexCombination`, and the bridge theorem
  `StdSimplex.convexCombination_map_eq_sum` from `Definition_3_1_1_4`, the chapter's canonical
  simplex packaging for finite convex combinations on arbitrary finite index types

Best owner abstraction:
- source-facing: this finite-family minimax-linearization theorem
- core/canonical: `maxTypeObjective fs` for the finite maximum, the bounded feasible sublevel
  owner `constrainedSublevelSet Q (fun x ↦ ((maxTypeObjective fs x : ℝ) : WithTop ℝ)) α`, and
  `StdSimplex ℝ ι` for the coefficient data
- bridge/view: the recursive reduction to the two-function owner theorem
  `exists_minimax_parameter_of_bounded_constrainedSublevelSets`, together with the textbook
  weighted objective `∑ i, coeffs.weights i * fs i x`, recovered from the simplex owner by
  `StdSimplex.convexCombination_map_eq_sum`

Primitive data:
- a nonempty finite family `fs : ι → E → ℝ`
- closed convexity of each component on `Q`
- boundedness of the constrained sublevel sets of the canonical `WithTop` lift of the owner
  maximum `maxTypeObjective fs`

Derived API:
- the owner finite maximum `maxTypeObjective fs`
- the simplex coefficient vector `coeffs : StdSimplex ℝ ι`
- the textbook weighted objective `∑ i, coeffs.weights i * fs i x`

The theorem is genuinely source-facing and not a bridge to an earlier m-ary owner theorem, but its
ambient space and coefficient data are kept at the chapter's canonical owner level: an arbitrary
proper real normed space `E` and the simplex owner type `StdSimplex ℝ ι`, rather than the
over-concrete textbook presentation `EuclideanSpace ℝ (Fin n)` with indices `Fin m`. -/

/-- Helper for Corollary 3.1.2.1: a supporting functional on the upper image has nonnegative
coordinate coefficients, and those coefficients have positive total mass. -/
theorem supporting_functional_coordinates_nonnegative
    [DecidableEq ι]
    {Q : Set E} {fs : ι → E → ℝ} (xStar : Q)
    {g : StrongDual ℝ (ι → ℝ)} (hg_ne : g ≠ 0)
    (hg_support :
      ∀ p : ι → ℝ, (∃ x ∈ Q, ∀ i, fs i x ≤ p i) →
        g (fun _ ↦ maxTypeObjective fs xStar) ≤ g p) :
    (∀ i, 0 ≤ g (Pi.single i 1)) ∧ 0 < ∑ i, g (Pi.single i 1) := by
  classical
  have hcoord_nonneg : ∀ i, 0 ≤ g (Pi.single i 1) := by
    intro i
    let dStar : ι → ℝ := fun _ ↦ maxTypeObjective fs xStar
    let pShift : ι → ℝ := dStar + Pi.single i 1
    have hpShift_mem : ∃ x ∈ Q, ∀ j, fs j x ≤ pShift j := by
      refine ⟨xStar, xStar.property, ?_⟩
      intro j
      by_cases hij : j = i
      · have hjle :
            fs j xStar ≤ maxTypeObjective fs xStar := by
          exact (maxTypeObjective_le_iff fs xStar (maxTypeObjective fs xStar)).mp le_rfl j
        have hjle' : fs j xStar ≤ maxTypeObjective fs xStar + 1 := by
          linarith
        simpa [pShift, dStar, Pi.single_apply, hij] using hjle'
      · have hjle :
            fs j xStar ≤ maxTypeObjective fs xStar := by
          exact (maxTypeObjective_le_iff fs xStar (maxTypeObjective fs xStar)).mp le_rfl j
        simpa [pShift, dStar, Pi.single_eq_of_ne hij] using hjle
    have hineq := hg_support pShift hpShift_mem
    -- The shifted feasible point changes only the `i`-th coordinate, so support monotonicity
    -- forces the `i`-th coefficient to be nonnegative.
    rw [show pShift = dStar + Pi.single i 1 by rfl, map_add] at hineq
    linarith
  refine ⟨hcoord_nonneg, ?_⟩
  by_contra hsum_nonpos
  have hsum_eq_zero : ∑ i, g (Pi.single i 1) = 0 := by
    have hsum_nonneg : 0 ≤ ∑ i, g (Pi.single i 1) :=
      Finset.sum_nonneg fun i hi ↦ hcoord_nonneg i
    linarith
  have hcoord_zero :
      ∀ i, g (Pi.single i 1) = 0 := by
    intro i
    exact
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hcoord_nonneg j)).1 hsum_eq_zero i (by simp)
  have hg_zero : g = 0 := by
    -- Vanishing on the coordinate vectors forces vanishing on every point of the finite product.
    apply ContinuousLinearMap.ext
    intro z
    rw [strongDual_apply_fintype g z]
    simp [hcoord_zero]
  exact hg_ne hg_zero

/-- Helper for Corollary 3.1.2.1: after normalizing the supporting-functional coordinates, the
resulting coefficient family gives a global lower bound for the weighted objective. -/
theorem supporting_functional_weighted_lower_bound
    [DecidableEq ι]
    {Q : Set E} {fs : ι → E → ℝ} (xStar : Q)
    {g : StrongDual ℝ (ι → ℝ)}
    (hg_support :
      ∀ p : ι → ℝ, (∃ x ∈ Q, ∀ i, fs i x ≤ p i) →
        g (fun _ ↦ maxTypeObjective fs xStar) ≤ g p)
    (hσ_pos : 0 < ∑ i, g (Pi.single i 1)) :
    ∀ x : Q,
      maxTypeObjective fs xStar ≤
        ∑ i, ((g (Pi.single i 1)) / (∑ j, g (Pi.single j 1))) * fs i x := by
  classical
  intro x
  let dStar : ι → ℝ := fun _ ↦ maxTypeObjective fs xStar
  have hxU : ∃ y ∈ Q, ∀ i, fs i y ≤ (fun j ↦ fs j x) i := by
    refine ⟨x, x.property, ?_⟩
    intro i
    exact le_rfl
  have hineq := hg_support (fun i ↦ fs i x) hxU
  have hdStar_eval :
      g dStar =
        (∑ i, g (Pi.single i 1)) * maxTypeObjective fs xStar := by
    calc
      g dStar = ∑ i, dStar i * g (Pi.single i 1) := strongDual_apply_fintype g dStar
      _ = ∑ i, maxTypeObjective fs xStar * g (Pi.single i 1) := by simp [dStar]
      _ = (∑ i, g (Pi.single i 1)) * maxTypeObjective fs xStar := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        ring
  have hx_eval :
      g (fun i ↦ fs i x) = ∑ i, fs i x * g (Pi.single i 1) := by
    simpa using (strongDual_apply_fintype g (fun i ↦ fs i x))
  have hmul :
      (∑ i, g (Pi.single i 1)) * maxTypeObjective fs xStar ≤
        (∑ i, g (Pi.single i 1)) *
          ∑ i, (g (Pi.single i 1) / ∑ j, g (Pi.single j 1)) * fs i x := by
    -- Route correction: divide only once after rewriting both evaluations into coordinate sums.
    calc
      (∑ i, g (Pi.single i 1)) * maxTypeObjective fs xStar = g dStar := by
        rw [hdStar_eval]
      _ ≤ g (fun i ↦ fs i x) := hineq
      _ = ∑ i, fs i x * g (Pi.single i 1) := hx_eval
      _ = (∑ i, g (Pi.single i 1)) *
            ∑ i, (g (Pi.single i 1) / ∑ j, g (Pi.single j 1)) * fs i x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        field_simp [hσ_pos.ne']
  have hfinal :
      maxTypeObjective fs xStar ≤
        ∑ i, (g (Pi.single i 1) / ∑ j, g (Pi.single j 1)) * fs i x :=
    (mul_le_mul_iff_of_pos_left hσ_pos).mp hmul
  simpa using hfinal

/-- Helper for Corollary 3.1.2.1: the supporting functional at a minimizer produces simplex
coefficients whose weighted objective has the same attained value at that minimizer. -/
theorem supporting_coeffs_of_familyMaximum_minimizer
    [DecidableEq ι]
    {Q : Set E} {fs : ι → E → ℝ} (xStar : Q)
    (hfs : ∀ i, ClosedConvexOn Q (fun x ↦ (fs i x : WithTop ℝ)))
    (hxStarMin : IsMinOn (fun x : Q ↦ maxTypeObjective fs x) Set.univ xStar) :
    ∃ coeffs : StdSimplex ℝ ι,
      (∀ x : Q, maxTypeObjective fs xStar ≤ ∑ i, coeffs.weights i * fs i x) ∧
      ∑ i, coeffs.weights i * fs i xStar = maxTypeObjective fs xStar := by
  classical
  let fStar : ℝ := maxTypeObjective fs xStar
  let U : Set (ι → ℝ) := {p | ∃ x ∈ Q, ∀ i, fs i x ≤ p i}
  have hboundary :
      Convex ℝ U ∧
        (fun _ ↦ fStar) ∈ U ∧
        (interior U).Nonempty ∧
        (fun _ ↦ fStar) ∉ interior U := by
    simpa [fStar, U] using
      (upperImage_boundary_of_familyMaximum_minimizer xStar hfs hxStarMin)
  rcases hboundary with ⟨hU_convex, hdStar_memU, hU_int_nonempty, hdStar_not_mem_interior⟩
  obtain ⟨f, hf_ne, hf_support⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hU_convex hdStar_not_mem_interior
      hU_int_nonempty
  let g : StrongDual ℝ (ι → ℝ) := -f
  have hg_ne : g ≠ 0 := by
    intro hg_zero
    exact hf_ne (by simpa [g] using hg_zero)
  have hg_support :
      ∀ p : ι → ℝ, (∃ x ∈ Q, ∀ i, fs i x ≤ p i) → g (fun _ ↦ fStar) ≤ g p := by
    intro p hp
    have hpU : p ∈ U := hp
    -- Negating the separating functional turns the boundary support inequality into a lower bound.
    simpa [g, fStar] using neg_le_neg (hf_support p hpU)
  obtain ⟨hcoord_nonneg, hσ_pos⟩ :=
    supporting_functional_coordinates_nonnegative xStar hg_ne hg_support
  let coeffFn : ι → ℝ := fun i ↦ g (Pi.single i 1) / ∑ j, g (Pi.single j 1)
  have hcoeff_nonneg : ∀ i, 0 ≤ coeffFn i := by
    intro i
    exact div_nonneg (hcoord_nonneg i) hσ_pos.le
  have hcoeff_sum : ∑ i, coeffFn i = 1 := by
    -- The normalized coordinate weights sum to one by construction.
    rw [show (∑ i, coeffFn i) = (∑ i, g (Pi.single i 1)) / (∑ j, g (Pi.single j 1)) by
      simp [coeffFn, Finset.sum_div]]
    field_simp [hσ_pos.ne']
  let coeffs : StdSimplex ℝ ι :=
    ⟨Finsupp.equivFunOnFinite.symm coeffFn,
      by simpa [coeffFn] using hcoeff_nonneg,
      by
        simpa [coeffFn] using (Finsupp.equivFunOnFinite_symm_sum coeffFn).trans hcoeff_sum⟩
  have hweighted_lower :
      ∀ x : Q, fStar ≤ ∑ i, coeffs.weights i * fs i x := by
    -- The normalized support inequality gives the lower bound for every feasible point.
    intro x
    simpa [coeffs, coeffFn, fStar] using
      (supporting_functional_weighted_lower_bound xStar hg_support hσ_pos x)
  have hweights_sum : ∑ i, coeffs.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using coeffs.total
  have hweighted_xStar_le : ∑ i, coeffs.weights i * fs i xStar ≤ fStar := by
    -- Each component value at the minimizer is bounded above by the family maximum.
    calc
      ∑ i, coeffs.weights i * fs i xStar ≤ ∑ i, coeffs.weights i * fStar := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        exact mul_le_mul_of_nonneg_left
          ((maxTypeObjective_le_iff fs xStar fStar).mp le_rfl i)
          (coeffs.nonneg i)
      _ = fStar := by
        rw [← Finset.sum_mul, hweights_sum, one_mul]
  have hweighted_xStar_eq : ∑ i, coeffs.weights i * fs i xStar = fStar := by
    exact le_antisymm hweighted_xStar_le (hweighted_lower xStar)
  exact ⟨coeffs, hweighted_lower, by simpa [fStar] using hweighted_xStar_eq⟩

/-- Corollary 3.1.2.1: if `f₁, …, f_m` are closed convex real-valued functions on `Q` and every
constrained level set of their finite pointwise maximum is bounded, then there exists a
coefficient vector in the standard simplex `StdSimplex ℝ ι` whose canonical convex
combination of the family values has the same constrained minimum value as that finite maximum; in
Lean the boundedness hypothesis is expressed through the chapter owner
`constrainedSublevelSet Q (fun x ↦ ((maxTypeObjective fs x : ℝ) : WithTop ℝ)) α`, and the
conclusion is recorded as an equality of `EReal` infima over the subtype `Q` between
`maxTypeObjective fs` and the textbook simplex-weighted objective
`fun x ↦ ∑ i, coeffs.weights i * fs i x`. This weighted formula is the chapter bridge view of the
canonical simplex combination supplied by `StdSimplex.convexCombination_map_eq_sum`, and the
textbook `ℝⁿ` / `m`-indexed statement is recovered by specializing to
`E = EuclideanSpace ℝ (Fin n)` and `ι = Fin m`, using the canonical proper-space instance on that
finite-dimensional model. -/
-- Route correction: the naive tail-max recursion does not preserve the bounded-sublevel
-- hypothesis on the residual maxima. The verified route now first constructs a primal minimizer
-- for `maxTypeObjective fs`, then proves that the associated upper image in `ι → ℝ` is convex
-- with nonempty interior and has the minimizing diagonal point on its boundary. The remaining
-- blocker is to turn the supporting functional from Hahn-Banach into normalized simplex weights.
theorem exists_stdSimplex_minimax_linearization_of_bounded_familyMaximumSublevelSets
    {Q : Set E} {fs : ι → E → ℝ}
    (hfs : ∀ i, ClosedConvexOn Q (fun x ↦ (fs i x : WithTop ℝ)))
    (hbounded :
      ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet Q (fun x ↦ ((maxTypeObjective fs x : ℝ) : WithTop ℝ)) α)) :
    ∃ coeffs : StdSimplex ℝ ι,
      sInf (Set.range fun x : Q ↦ (maxTypeObjective fs x : EReal)) =
        sInf (Set.range fun x : Q ↦
          ((∑ i, coeffs.weights i * fs i x : ℝ) : EReal)) := by
  classical
  rcases Q.eq_empty_or_nonempty with rfl | hQ_nonempty
  · let coeffs : StdSimplex ℝ ι := StdSimplex.single (Classical.choice ‹Nonempty ι›)
    have hrange_max :
        Set.range (fun x : (∅ : Set E) ↦ (maxTypeObjective fs x : EReal)) = ∅ := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact x.property.elim
      · simp
    have hrange_weighted :
        Set.range (fun x : (∅ : Set E) ↦
          ((∑ i, coeffs.weights i * fs i x : ℝ) : EReal)) = ∅ := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact x.property.elim
      · simp
    refine ⟨coeffs, ?_⟩
    rw [hrange_max, hrange_weighted]
  · obtain ⟨xStar, hxStarMin⟩ :=
      exists_isMinOn_familyMaximum_of_bounded_sublevels hfs hbounded hQ_nonempty
    obtain ⟨coeffs, hweighted_lower, hweighted_xStar_eq⟩ :=
      supporting_coeffs_of_familyMaximum_minimizer xStar hfs hxStarMin
    let fStar : ℝ := maxTypeObjective fs xStar
    have hweighted_min :
        IsMinOn (fun x : Q ↦ ∑ i, coeffs.weights i * fs i x) Set.univ xStar := by
      -- The weighted objective is globally bounded below by the attained value at `xStar`.
      rw [isMinOn_univ_iff]
      intro x
      simpa [hweighted_xStar_eq] using hweighted_lower x
    have hsInf_max :
        sInf (Set.range fun x : Q ↦ (maxTypeObjective fs x : EReal)) = (fStar : EReal) := by
      -- The primal minimizer rewrites the infimum of the family maximum to its attained value.
      have hopt :
          (SetConstrainedMinimizationProblem.unconstrained
            (fun x : Q ↦ maxTypeObjective fs x)).optimalValue = (fStar : EReal) := by
        simpa [fStar] using
          (SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn
            (problem := SetConstrainedMinimizationProblem.unconstrained
              (fun x : Q ↦ maxTypeObjective fs x))
            (x := xStar) (by simp) hxStarMin)
      simpa [SetConstrainedMinimizationProblem.optimalValue] using hopt
    have hsInf_weighted :
        sInf (Set.range fun x : Q ↦ ((∑ i, coeffs.weights i * fs i x : ℝ) : EReal)) =
          (fStar : EReal) := by
      -- The same attained-value rewrite applies to the supported weighted objective.
      have hopt :
          (SetConstrainedMinimizationProblem.unconstrained
            (fun x : Q ↦ ∑ i, coeffs.weights i * fs i x)).optimalValue =
              (((∑ i, coeffs.weights i * fs i xStar : ℝ) : EReal)) := by
        simpa using
          (SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn
            (problem := SetConstrainedMinimizationProblem.unconstrained
              (fun x : Q ↦ ∑ i, coeffs.weights i * fs i x))
            (x := xStar) (by simp) hweighted_min)
      calc
        sInf (Set.range fun x : Q ↦ ((∑ i, coeffs.weights i * fs i x : ℝ) : EReal))
            = (SetConstrainedMinimizationProblem.unconstrained
                (fun x : Q ↦ ∑ i, coeffs.weights i * fs i x)).optimalValue := by
                  simp [SetConstrainedMinimizationProblem.optimalValue]
        _ = (((∑ i, coeffs.weights i * fs i xStar : ℝ) : EReal)) := hopt
        _ = (fStar : EReal) := by
          exact_mod_cast hweighted_xStar_eq
    exact ⟨coeffs, hsInf_max.trans hsInf_weighted.symm⟩

end
