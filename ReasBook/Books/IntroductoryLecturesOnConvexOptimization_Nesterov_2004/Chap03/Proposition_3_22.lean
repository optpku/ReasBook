/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.LinearEqualityFeasibleSet

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped NormalCone
open scoped TangentCone
open scoped Topology

/-
Proposition 3.22 lies in the chapter's affine linear-equality tangent/normal-cone domain.

Relevant owner declarations sampled before refinement:
* `posTangentConeAt` and the notation `𝒯[Q] xBar` in `Definition_3_23`, the chapter owner for the
  textbook tangent cone
* `normalCone` in `Definition_3_22`, the chapter owner for textbook normal cones
* `LinearMap.ker`, `LinearMap.adjoint`, and `LinearMap.range`, the canonical linear-algebra owners
* `gradient_mem_adjoint_range_of_isLocalMinOn_linearLevelSet` in `Chap01/Theorem_1_4_14`, which
  already treats linear equality constraints at the intrinsic linear-map level
* `linearEqualityFeasibleSet` and `mem_linearEqualityFeasibleSet_iff` in
  `LinearEqualityFeasibleSet`, the chapter bridge/view for the ambient-`Set.univ` specialization
* `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`, the mathlib bridge identifying `Aᵀ` with the
  adjoint linear map on Euclidean space

Best owner abstraction:
* the affine level set `{x | L x = b}` of a linear map

Primitive data:
* a linear equality map `L : E →ₗ[ℝ] F`
* a right-hand side `b`
* a feasible base point `xBar`

Derived API:
* the tangent-cone kernel formula on the intrinsic affine level set `{x | L x = b}`
* the normal-cone adjoint-range formula on the same level set
* the Chapter 3 `linearEqualityFeasibleSet (Set.univ : Set Eₙ) L b` specialization
* the matrix transpose bridge for the textbook `Aᵀ` statement

Source/core/bridge triage:
* source-facing: the textbook affine set `{x | A x = b}` and the matrix `ker A` / `range Aᵀ`
  formulas
* core/canonical: `𝒯[{x | L x = b}] xBar`, `N[{x | L x = b}] xBar`, `LinearMap.ker`, and
  `LinearMap.range`
* bridge/view: `linearEqualityFeasibleSet (Set.univ : Set Eₙ) L b` and `Matrix.toEuclideanLin`,
  which recover the chapter's ambient-`Set.univ` and matrix presentations from the intrinsic
  linear-map level-set statement

This file therefore centers both affine formulas on the intrinsic linear-map level set
`{x | L x = b}` together with the chapter owners `𝒯[Q] xBar` and `N[Q] xBar`. The
`linearEqualityFeasibleSet (Set.univ : Set Eₙ) ...` and matrix presentations remain thin
source-facing bridge theorems.
-/

section

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Proposition 3.22 (1), intrinsic owner-level form: at a feasible point of the affine level set
`{x | L x = b}` of a continuous linear constraint map, the textbook tangent cone is exactly
`ker L`. -/
-- Proof sketch: use the chapter owner `𝒯[Q] xBar = posTangentConeAt Q xBar`. If `h` is a feasible
-- direction, then points of the form `xBar + t • h` stay in the affine level set exactly when
-- `L h = 0`; conversely, every kernel vector gives such a feasible ray.
theorem posTangentConeAt_linearLevelSet
    (L : E →ₗ[ℝ] F) (hL : Continuous L) (b : F) {xBar : E} (hxBar : L xBar = b) :
    𝒯[{x | L x = b}] xBar =
      L.ker := by
  ext y
  constructor
  · intro hy
    rcases exists_fun_of_mem_tangentConeAt hy with ⟨α, l, hl, c, d, hd0, hlevel, hcd⟩
    change L y = 0
    have hLd : ∀ᶠ n in l, L (d n) = 0 := by
      filter_upwards [hlevel] with n hn
      have : L (xBar + d n) = b := hn
      simpa [LinearMap.map_add, hxBar] using this
    have hzero : ∀ᶠ n in l, L (c n • d n) = 0 := by
      filter_upwards [hLd] with n hn
      simpa using congrArg (fun z ↦ c n • z) hn
    have hLy : Filter.Tendsto (fun n ↦ L (c n • d n)) l (𝓝 (L y)) :=
      hL.tendsto _ |>.comp hcd
    have hzeroT : Filter.Tendsto (fun n ↦ L (c n • d n)) l (𝓝 (0 : F)) :=
      tendsto_const_nhds.congr' <| hzero.mono fun _ hn ↦ hn.symm
    have : L y = 0 := by
      apply tendsto_nhds_unique hLy
      exact hzeroT
    simpa using this
  · intro hy
    have hy0 : L y = 0 := by
      simpa using hy
    apply mem_posTangentConeAt_of_frequently_mem
    refine (Filter.Eventually.of_forall fun t ↦ ?_).frequently
    change L (xBar + t • y) = b
    simp [LinearMap.map_add, hy0, hxBar]

end

section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

variable [FiniteDimensional ℝ F]

/-- Proposition 3.22 (2), intrinsic linear-map form: at a feasible point of the affine level set
`{x | L x = b}`, the normal cone is exactly the adjoint range `range Lᵀ`. -/
-- Proof sketch: a normal vector annihilates every tangent direction, hence annihilates `ker L`.
-- In finite-dimensional Euclidean space this is equivalent to belonging to `L.adjoint.range`.
theorem normalCone_linearLevelSet
    (L : E →ₗ[ℝ] F) (b : F) {xBar : E} (hxBar : L xBar = b) :
    (N[{x | L x = b}] xBar : Set E) =
      L.adjoint.range := by
  ext g
  constructor
  · intro hg
    have hg_orth : g ∈ L.kerᗮ := by
      rw [Submodule.mem_orthogonal']
      intro y hy
      have hy0 : L y = 0 := by
        simpa using hy
      have hplus : xBar + y ∈ ({x | L x = b} : Set E) := by
        change L (xBar + y) = b
        simp [LinearMap.map_add, hy0, hxBar]
      have hminus : xBar - y ∈ ({x | L x = b} : Set E) := by
        change L (xBar - y) = b
        simp [LinearMap.map_sub, hy0, hxBar]
      have hplusIneq := (mem_normalCone_iff.mp hg) (xBar + y) hplus
      have hminusIneq := (mem_normalCone_iff.mp hg) (xBar - y) hminus
      have hpos : 0 ≤ inner ℝ g y := by
        simpa using hplusIneq
      have hneg : inner ℝ g y ≤ 0 := by
        simpa [sub_eq_add_neg, inner_neg_right] using hminusIneq
      exact le_antisymm hneg hpos
    rwa [LinearMap.orthogonal_ker] at hg_orth
  · intro hg
    rw [← LinearMap.orthogonal_ker] at hg
    have hg_orth : g ∈ L.kerᗮ := hg
    rw [Submodule.mem_orthogonal'] at hg_orth
    exact (mem_normalCone_iff).2 <| by
      intro x hx
      have hxker : x - xBar ∈ L.ker := by
        change L (x - xBar) = 0
        have hxEq : L x = b := hx
        simp [LinearMap.map_sub, hxEq, hxBar]
      have hinner : inner ℝ g (x - xBar) = 0 := hg_orth (x - xBar) hxker
      simp [hinner]

end

section

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/-- Proposition 3.22 (1), source-facing Chapter 3 specialization: on
`linearEqualityFeasibleSet (Set.univ : Set Eₙ) A.toEuclideanLin b`, the tangent cone is `ker A`. -/
theorem posTangentConeAt_matrix_linearEqualityFeasibleSet
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) {xBar : Eₙ}
    (hxBar : xBar ∈ linearEqualityFeasibleSet (Set.univ : Set Eₙ) A.toEuclideanLin b) :
    𝒯[linearEqualityFeasibleSet (Set.univ : Set Eₙ) A.toEuclideanLin b] xBar =
      A.toEuclideanLin.ker := by
  have hxEq : A.toEuclideanLin xBar = b := (mem_linearEqualityFeasibleSet_iff.mp hxBar).2
  have hA : Continuous A.toEuclideanLin := LinearMap.continuous_of_finiteDimensional _
  simpa [linearEqualityFeasibleSet] using
    posTangentConeAt_linearLevelSet A.toEuclideanLin hA b hxEq

/-- Proposition 3.22 (2), source-facing Chapter 3 specialization: on
`linearEqualityFeasibleSet (Set.univ : Set Eₙ) A.toEuclideanLin b`, the normal cone is the range
of the transpose map `Aᵀ`. -/
theorem normalCone_matrix_linearEqualityFeasibleSet
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) {xBar : Eₙ}
    (hxBar : xBar ∈ linearEqualityFeasibleSet (Set.univ : Set Eₙ) A.toEuclideanLin b) :
    (N[linearEqualityFeasibleSet (Set.univ : Set Eₙ) A.toEuclideanLin b] xBar : Set Eₙ) =
      (Aᵀ.toEuclideanLin).range := by
  have hxEq : A.toEuclideanLin xBar = b := (mem_linearEqualityFeasibleSet_iff.mp hxBar).2
  have hAdj : A.toEuclideanLin.adjoint = Aᵀ.toEuclideanLin := by
    simpa using (toEuclideanLin_conjTranspose_eq_adjoint A).symm
  simpa [linearEqualityFeasibleSet, hAdj] using
    normalCone_linearLevelSet A.toEuclideanLin b hxEq

end

end
