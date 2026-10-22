/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_56
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_62
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_4_5_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace MaximumVolumeInscribedEllipsoid

noncomputable section

open Matrix
open StrictPositiveSemidefiniteCone
open scoped EllipsoidNotation RealInnerProductSpace RealSymmetricMatrixSpace

variable {m n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "SymmMat" => 𝕊^n

/- Definition 5.4.5.6 lies in the inscribed-ellipsoid / convex-reformulation domain.

Sampled owner-style declarations in this domain:
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of a
  feasible set together with a real-valued objective;
* `constrainedEpigraph` and `mem_constrainedEpigraph_iff` in `Chap03/Definition_3_3`, the chapter
  owner/view for epigraph reformulations over a base feasible set;
* `innerLePolyhedron` and `mem_innerLePolyhedron_iff` in `Chap03/Definition_3_62`, the chapter
  owner/view for finite half-space presentations `⟪a i, x⟫ ≤ b i`;
* `affineEllipsoid` together with the notation `E(H, x̄)` and `mem_affineEllipsoid_iff` in
  `Chap03/Definition_3_56`, the chapter owner/view for quadratic-form ellipsoids;
* `enclosingEllipsoid` in `Chap05/Definition_5_4_5_1`, the adjacent Chapter 5 precedent for
  keeping an image-form ellipsoid owner on a strict-cone shape parameter instead of collapsing it
  into a quadratic-form surrogate;
* `logDetBarrier` in `Chap05/Definition_5_4_4_5`, the chapter owner for the `-log det`
  contribution on `𝕊^n₊₊`.

Best owner abstraction:
* source-facing: the image-form inscribed ellipsoid `W(G, v)` together with the convex
  reformulation base feasible set on `(G, v)`;
* core/canonical: `SetConstrainedMinimizationProblem`, `constrainedEpigraph`,
  `innerLePolyhedron`,
  the Chapter 3 quadratic-form ellipsoid `affineEllipsoid`, and `logDetBarrier`;
* bridge/view: the comparison `W(G, v) = E(G², v)`, the triple epigraph presentation on
  `(G, v, τ)`, and the textbook formulae obtained by expanding `logDetBarrier` back to
  `-log det G`.

Primitive data:
* the half-space presentation `a`, `b`;
* the strict-cone shape parameter `G`;
* the center `v`.

Derived API:
* the source-facing ellipsoid `W(G, v)`;
* the bridge theorem `W(G, v) = E(G², v)`;
* the containment theorem for `W(G, v) ⊆ innerLePolyhedron a b`;
* the base feasible set on `(G, v)` cut out by the geometric containment
  `W(G, v) ⊆ innerLePolyhedron a b`;
* the reformulation feasible set on triples `(G, v, τ)`, realized canonically as the epigraph of
  `logDetBarrier n` over that base feasible set;
* the owner optimization problem `optimizationProblem a b`;
* the formula companions obtained by expanding `W(G, v) ⊆ innerLePolyhedron a b` into the support
  inequalities and `logDetBarrier` into `-log det G`.

There is no upstream owner for the source-facing image-form ellipsoid parameterized by the
inscribed-ellipsoid variable `G : 𝕊^n₊₊`, so this file owns `W(G, v)` directly, keeps
`affineEllipsoid` only as the quadratic bridge `W(G, v) = E(G², v)`, and builds the optimization
reformulation from the earlier chapter owners `constrainedEpigraph`, `innerLePolyhedron`, and
`logDetBarrier` directly.
-/

def inscribedEllipsoid
    (G : 𝕊^n₊₊) (v : E) : Set E :=
  {x | ∃ u : E, ‖u‖ ≤ 1 ∧ x = v + (toMatrix G).toEuclideanLin u}

namespace InscribedEllipsoidNotation

scoped notation:max "W(" G ", " v ")" => inscribedEllipsoid G v

end InscribedEllipsoidNotation

open scoped InscribedEllipsoidNotation

/-- Membership in the image-form ellipsoid `W(G, v)` is exactly the existence of a unit-ball
parameter `u` with `x = v + G u`. -/
@[simp] theorem mem_inscribedEllipsoid_iff
    {G : 𝕊^n₊₊} {v x : E} :
    x ∈ W(G, v) ↔
      ∃ u : E, ‖u‖ ≤ 1 ∧ x = v + (toMatrix G).toEuclideanLin u :=
  Iff.rfl

/-- Helper for Definition 5.4.5.6: applying `toMatrix G` after its inverse action recovers the
original Euclidean vector. -/
private theorem toEuclideanLinInvCancel
    (G : 𝕊^n₊₊) (z : E) :
    (toMatrix G).toEuclideanLin (((toMatrix G)⁻¹).toEuclideanLin z) = z := by
  have hM : (((G : SymmMat) : Mat)).PosDef := strictPositiveSemidefiniteCone_posDef G
  have hMdet : IsUnit (((G : SymmMat) : Mat).det) := isUnit_iff_ne_zero.mpr (ne_of_gt hM.det_pos)
  have hmul : (((G : SymmMat) : Mat)) * ((((G : SymmMat) : Mat))⁻¹) = 1 :=
    Matrix.mul_nonsing_inv (A := ((G : SymmMat) : Mat)) hMdet
  -- Convert the Euclidean action to matrix multiplication and cancel the inverse on the left.
  ext i
  simp [StrictPositiveSemidefiniteCone.toMatrix_def, Matrix.ofLp_toLpLin,
    Matrix.mulVec_mulVec, hmul]

/-- Helper for Definition 5.4.5.6: applying the inverse matrix after `toMatrix G` recovers the
original Euclidean vector. -/
private theorem invToEuclideanLinCancel
    (G : 𝕊^n₊₊) (z : E) :
    ((toMatrix G)⁻¹).toEuclideanLin ((toMatrix G).toEuclideanLin z) = z := by
  have hM : (((G : SymmMat) : Mat)).PosDef := strictPositiveSemidefiniteCone_posDef G
  have hMdet : IsUnit (((G : SymmMat) : Mat).det) := isUnit_iff_ne_zero.mpr (ne_of_gt hM.det_pos)
  have hmul : ((((G : SymmMat) : Mat))⁻¹) * (((G : SymmMat) : Mat)) = 1 :=
    Matrix.nonsing_inv_mul (A := ((G : SymmMat) : Mat)) hMdet
  -- Convert the Euclidean action to matrix multiplication and cancel the inverse on the right.
  ext i
  simp [StrictPositiveSemidefiniteCone.toMatrix_def, Matrix.ofLp_toLpLin,
    Matrix.mulVec_mulVec, hmul]

/-- Helper for Definition 5.4.5.6: the quadratic form of `(toMatrix G * toMatrix G)⁻¹`
is the squared norm of the inverse action of `toMatrix G`. -/
private theorem squareInverseQuadratic_eq_normSq
    (G : 𝕊^n₊₊) (y : E) :
    inner ℝ (((toMatrix G * toMatrix G)⁻¹).toEuclideanLin y) y =
      ‖((toMatrix G)⁻¹).toEuclideanLin y‖ ^ (2 : ℕ) := by
  let M : Mat := toMatrix G
  have hMsymm : M.IsSymm := by
    simpa [M] using strictPositiveSemidefiniteCone_isSymm G
  have hmul :
      ((M⁻¹ * M⁻¹).toEuclideanLin y) = M⁻¹.toEuclideanLin (M⁻¹.toEuclideanLin y) := by
    -- This is the Euclidean-space version of `mulVec_mulVec`.
    ext i
    simp [M, Matrix.mulVec_mulVec]
  -- Rewrite the inverse square through two inverse actions and then use symmetry.
  calc
    inner ℝ (((M * M)⁻¹).toEuclideanLin y) y =
        inner ℝ ((M⁻¹ * M⁻¹).toEuclideanLin y) y := by
          rw [Matrix.mul_inv_rev]
    _ = inner ℝ (M⁻¹.toEuclideanLin (M⁻¹.toEuclideanLin y)) y := by
      rw [hmul]
    _ = inner ℝ (M⁻¹.toEuclideanLin y) ((M⁻¹)ᵀ.toEuclideanLin y) := by
      rw [← M⁻¹.toEuclideanLin.adjoint_inner_right]
      exact congrArg
        (fun z : E ↦ inner ℝ (M⁻¹.toEuclideanLin y) z)
        (congrArg
          (fun T : E →ₗ[ℝ] E ↦ T y)
          (Matrix.toEuclideanLin_conjTranspose_eq_adjoint M⁻¹).symm)
    _ = inner ℝ (M⁻¹.toEuclideanLin y) (M⁻¹.toEuclideanLin y) := by
      rw [hMsymm.inv.eq]
    _ = ‖M⁻¹.toEuclideanLin y‖ ^ (2 : ℕ) := by
      rw [real_inner_self_eq_norm_sq]

/-- Helper for Definition 5.4.5.6: the squared shape matrix `toMatrix G * toMatrix G` is
positive definite. -/
private theorem squareAction_posDef
    (G : 𝕊^n₊₊) :
    ((toMatrix G) * (toMatrix G)).PosDef := by
  have hM : (toMatrix G).PosDef := by
    simpa using strictPositiveSemidefiniteCone_posDef G
  have hMsymm : (toMatrix G).IsSymm := by
    simpa using strictPositiveSemidefiniteCone_isSymm G
  have hMinj : Function.Injective (toMatrix G).vecMul :=
    (Matrix.vecMul_injective_iff_isUnit).2 hM.isUnit
  have hsquare : ((toMatrix G) * (1 : Mat) * (toMatrix G)ᴴ).PosDef :=
    (Matrix.PosDef.one : (1 : Mat).PosDef).mul_mul_conjTranspose_same hMinj
  -- Collapse the conjugate transpose to `M` using symmetry of strict-cone matrices.
  have hsquare' : ((toMatrix G) * (toMatrix G)ᵀ).PosDef := by
    simpa [Matrix.mul_assoc] using hsquare
  simpa only [hMsymm.eq] using hsquare'

/-- Helper for Definition 5.4.5.6: the quadratic form of `toMatrix G * toMatrix G`
is the squared norm of the Euclidean action of `toMatrix G`. -/
private theorem squareAction_inner_eq_normSq
    (G : 𝕊^n₊₊) (z : E) :
    ⟪z, ((toMatrix G) * (toMatrix G)).toEuclideanLin z⟫ =
      ‖(toMatrix G).toEuclideanLin z‖ ^ (2 : ℕ) := by
  let M : Mat := toMatrix G
  have hMsymm : M.IsSymm := by
    simpa [M] using strictPositiveSemidefiniteCone_isSymm G
  have hmul :
      ((M * M).toEuclideanLin z) = M.toEuclideanLin (M.toEuclideanLin z) := by
    -- This is the Euclidean-space version of `mulVec_mulVec`.
    ext i
    simp [M, Matrix.mulVec_mulVec]
  -- Rewrite the square action through the adjoint of `M` and then use symmetry.
  calc
    ⟪z, (M * M).toEuclideanLin z⟫ = inner ℝ ((M * M).toEuclideanLin z) z := by
      rw [real_inner_comm]
    _ = inner ℝ (M.toEuclideanLin (M.toEuclideanLin z)) z := by
      rw [hmul]
    _ = inner ℝ (M.toEuclideanLin z) (Mᵀ.toEuclideanLin z) := by
      rw [← M.toEuclideanLin.adjoint_inner_right]
      exact congrArg
        (fun T : E →ₗ[ℝ] E ↦ inner ℝ (M.toEuclideanLin z) (T z))
        (Matrix.toEuclideanLin_conjTranspose_eq_adjoint M).symm
    _ = inner ℝ (M.toEuclideanLin z) (M.toEuclideanLin z) := by
      rw [hMsymm.eq]
    _ = ‖M.toEuclideanLin z‖ ^ (2 : ℕ) := by
      rw [real_inner_self_eq_norm_sq]

/-- The image-form ellipsoid `W(G, v)` is the Chapter 3 quadratic-form ellipsoid whose shape
matrix is `G²`. -/
theorem inscribedEllipsoid_eq_affineEllipsoid_sq
    (G : 𝕊^n₊₊) (v : E) :
    W(G, v) = E(toMatrix G * toMatrix G, v) := by
  ext x
  let M : Mat := toMatrix G
  have hnormSq_iff (u : E) :
      ‖u‖ ^ (2 : ℕ) ≤ 1 ↔ ‖u‖ ≤ 1 := by
    constructor
    · intro hu
      nlinarith [norm_nonneg u]
    · intro hu
      nlinarith [norm_nonneg u]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_affineEllipsoid_iff]
    have hinv :
        M⁻¹.toEuclideanLin ((v + M.toEuclideanLin u) - v) = u := by
      simpa [M] using invToEuclideanLinCancel (G := G) u
    have hquad :
        inner ℝ (((M * M)⁻¹).toEuclideanLin ((v + M.toEuclideanLin u) - v))
            ((v + M.toEuclideanLin u) - v) =
          ‖u‖ ^ (2 : ℕ) := by
      calc
        inner ℝ (((M * M)⁻¹).toEuclideanLin ((v + M.toEuclideanLin u) - v))
            ((v + M.toEuclideanLin u) - v) =
            ‖M⁻¹.toEuclideanLin ((v + M.toEuclideanLin u) - v)‖ ^ (2 : ℕ) := by
              simpa [M] using
                squareInverseQuadratic_eq_normSq (G := G) ((v + M.toEuclideanLin u) - v)
        _ = ‖u‖ ^ (2 : ℕ) := by
          rw [hinv]
    have hsq : ‖u‖ ^ (2 : ℕ) ≤ 1 := (hnormSq_iff u).2 hu
    rw [hquad]
    exact hsq
  · intro hx
    rw [mem_affineEllipsoid_iff] at hx
    let u : E := M⁻¹.toEuclideanLin (x - v)
    have hquad :
        inner ℝ (((M * M)⁻¹).toEuclideanLin (x - v)) (x - v) =
          ‖u‖ ^ (2 : ℕ) := by
      simpa [u, M] using squareInverseQuadratic_eq_normSq (G := G) (x - v)
    have hsq : ‖u‖ ^ (2 : ℕ) ≤ 1 := by
      rw [← hquad]
      exact hx
    refine ⟨u, (hnormSq_iff u).1 hsq, ?_⟩
    have hcancel : M.toEuclideanLin u = x - v := by
      simpa [u, M] using toEuclideanLinInvCancel (G := G) (x - v)
    -- Reassemble `x` from the chosen inverse-image parameter.
    calc
      x = v + (x - v) := by simp
      _ = v + M.toEuclideanLin u := by rw [hcancel]

-- Proof sketch: combine the source-facing image description of `W(G, v)` with
-- `mem_innerLePolyhedron_iff`. For the half-space `⟪a i, x⟫ ≤ b i`, the support value of
-- `x ↦ ⟪a i, x⟫` on `W(G, v)` is `⟪a i, v⟫ + ‖G a i‖`, so containment is equivalent to the
-- displayed norm inequalities.
/-- The ellipsoid `W(G, v)` is contained in the polyhedron
`Q = {x : ⟪a i, x⟫ ≤ b i}` exactly when the support-function inequalities
`‖G a_i‖ ≤ b_i - ⟪a_i, v⟫` hold for all `i`. -/
theorem inscribedEllipsoid_subset_innerLePolyhedron_iff
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) :
    W(G, v) ⊆ innerLePolyhedron a b ↔
      ∀ i : Fin m,
        ‖(toMatrix G).toEuclideanLin (a i)‖ ≤ b i - ⟪a i, v⟫ := by
  let M : Mat := toMatrix G
  have hPosDef : (M * M).PosDef := by
    simpa [M] using squareAction_posDef (G := G)
  constructor
  · intro hsubset i
    have hsubsetAffine : E(M * M, v) ⊆ innerLePolyhedron a b := by
      simpa [M, inscribedEllipsoid_eq_affineEllipsoid_sq (G := G) (v := v)] using hsubset
    have hhalfspace : ∀ x ∈ E(M * M, v), ⟪a i, x⟫ ≤ b i := by
      intro x hx
      exact (mem_innerLePolyhedron_iff a b).1 (hsubsetAffine hx) i
    have hcenter : ⟪a i, v⟫ ≤ b i := by
      exact hhalfspace v (center_mem_affineEllipsoid (M * M) v)
    have hslack : 0 ≤ b i - ⟪a i, v⟫ := sub_nonneg.mpr hcenter
    -- Reduce the support inequality to the Chapter 5 affine-ellipsoid halfspace criterion.
    have hquad :
        ⟪a i, (M * M).toEuclideanLin (a i)⟫ ≤
          (b i - ⟪a i, v⟫) ^ (2 : ℕ) :=
      (affine_le_on_affineEllipsoid_iff (a i) v (b i) (M * M) hslack hPosDef).1 hhalfspace
    have hsq :
        ‖M.toEuclideanLin (a i)‖ ^ (2 : ℕ) ≤
          (b i - ⟪a i, v⟫) ^ (2 : ℕ) := by
      rw [squareAction_inner_eq_normSq (G := G) (z := a i)] at hquad
      exact hquad
    have hnorm_nonneg : 0 ≤ ‖M.toEuclideanLin (a i)‖ := norm_nonneg _
    nlinarith
  · intro hnorm
    have hslack : ∀ i : Fin m, 0 ≤ b i - ⟪a i, v⟫ := by
      intro i
      have hnorm_nonneg : 0 ≤ ‖M.toEuclideanLin (a i)‖ := norm_nonneg _
      linarith [hnorm i]
    have hsubsetAffine : E(M * M, v) ⊆ innerLePolyhedron a b := by
      intro x hx
      rw [mem_innerLePolyhedron_iff]
      intro i
      have hsq :
          ‖M.toEuclideanLin (a i)‖ ^ (2 : ℕ) ≤
            (b i - ⟪a i, v⟫) ^ (2 : ℕ) := by
        have hnorm_nonneg : 0 ≤ ‖M.toEuclideanLin (a i)‖ := norm_nonneg _
        nlinarith [hnorm i]
      have hquad :
          ⟪a i, (M * M).toEuclideanLin (a i)⟫ ≤
            (b i - ⟪a i, v⟫) ^ (2 : ℕ) := by
        rw [squareAction_inner_eq_normSq (G := G) (z := a i)]
        exact hsq
      exact
        (affine_le_on_affineEllipsoid_iff (a i) v (b i) (M * M) (hslack i) hPosDef).2
          hquad x hx
    -- Transport the containment statement back across the ellipsoid identification.
    simpa [M, inscribedEllipsoid_eq_affineEllipsoid_sq (G := G) (v := v)] using hsubsetAffine

/-- The base feasible set of inscribed-ellipsoid parameters `(G, v)` satisfying the geometric
containment `W(G, v) ⊆ innerLePolyhedron a b`. -/
def containmentSet
    (a : Fin m → E) (b : Fin m → ℝ) : Set (𝕊^n₊₊ × E) :=
  {Gv | W(Gv.1, Gv.2) ⊆ innerLePolyhedron a b}

/-- Membership in `containmentSet a b` is exactly the geometric containment
`W(G, v) ⊆ innerLePolyhedron a b`. -/
@[simp] theorem mem_containmentSet_iff
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) :
    (G, v) ∈ containmentSet a b ↔
      W(G, v) ⊆ innerLePolyhedron a b :=
  Iff.rfl

/-- The feasible set of the convex reformulation is the epigraph of `logDetBarrier n` over the
base containment set, presented on triples `(G, v, τ)`. -/
def feasibleSet
    (a : Fin m → E) (b : Fin m → ℝ) : Set (𝕊^n₊₊ × E × ℝ) :=
  {Gvτ | ((Gvτ.1, Gvτ.2.1), Gvτ.2.2) ∈
    constrainedEpigraph (containmentSet a b)
      (fun Gv ↦ (logDetBarrier n Gv.1 : WithTop ℝ))}

/-- Membership in `feasibleSet a b` is exactly the conjunction of `logDetBarrier n G ≤ τ` and
the geometric containment `W(G, v) ⊆ innerLePolyhedron a b`. -/
@[simp] theorem mem_feasibleSet_iff
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ) :
    (G, v, τ) ∈ feasibleSet a b ↔
      logDetBarrier n G ≤ τ ∧ W(G, v) ⊆ innerLePolyhedron a b := by
  change ((G, v), τ) ∈
      constrainedEpigraph (containmentSet a b)
        (fun Gv ↦ (logDetBarrier n Gv.1 : WithTop ℝ)) ↔
    logDetBarrier n G ≤ τ ∧ W(G, v) ⊆ innerLePolyhedron a b
  rw [mem_constrainedEpigraph_iff]
  change (G, v) ∈ containmentSet a b ∧ (logDetBarrier n G : WithTop ℝ) ≤ τ ↔
    logDetBarrier n G ≤ τ ∧ W(G, v) ⊆ innerLePolyhedron a b
  rw [mem_containmentSet_iff]
  constructor
  · rintro ⟨hcontain, hτ⟩
    exact ⟨by exact_mod_cast hτ, hcontain⟩
  · rintro ⟨hτ, hcontain⟩
    exact ⟨hcontain, by exact_mod_cast hτ⟩

/-- Expanding the owner containment `W(G, v) ⊆ innerLePolyhedron a b` rewrites feasible-set
membership back to the textbook inequalities
`‖G a_i‖ ≤ b_i - ⟪a_i, v⟫`, while expanding `logDetBarrier n G` rewrites the epigraph term back
to `-log det G ≤ τ`. -/
theorem mem_feasibleSet_iff_formula
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ) :
    (G, v, τ) ∈ feasibleSet a b ↔
      -Real.log (toMatrix G).det ≤ τ ∧
        ∀ i : Fin m,
          ‖(toMatrix G).toEuclideanLin (a i)‖ ≤ b i - ⟪a i, v⟫ := by
  rw [mem_feasibleSet_iff, inscribedEllipsoid_subset_innerLePolyhedron_iff, logDetBarrier_apply]
  simp [toMatrix_def]

/-- Definition 5.4.5.6: for the polyhedron
`Q = {x ∈ ℝⁿ : ⟪a_i, x⟫ ≤ b_i, i = 1, …, m}`, the maximum-volume inscribed ellipsoid problem is
the set-constrained minimization problem on triples `(G, v, τ)` whose feasible set is the convex
reformulation and whose objective is the epigraph variable `τ`. -/
def optimizationProblem
    (a : Fin m → E) (b : Fin m → ℝ) :
    SetConstrainedMinimizationProblem (𝕊^n₊₊ × E × ℝ) where
  feasibleSet := feasibleSet a b
  objective := Prod.snd ∘ Prod.snd

/-- Evaluating the convex reformulation objective returns the auxiliary scalar variable `τ`. -/
@[simp] theorem optimizationProblem_objective_apply
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ) :
    (optimizationProblem a b).objective (G, v, τ) = τ :=
  rfl

end

end MaximumVolumeInscribedEllipsoid
