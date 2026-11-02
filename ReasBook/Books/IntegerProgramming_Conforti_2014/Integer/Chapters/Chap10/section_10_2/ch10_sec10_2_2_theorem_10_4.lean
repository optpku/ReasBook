import Mathlib.LinearAlgebra.Matrix.PosDef
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_7.ch7_sec7_7_exercise_7_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_7.ch7_sec7_7_stable_set_relaxations

open scoped BigOperators

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling note: this theorem reuses the Chapter 7 stable-set-polytope owners
-- `stableSetIndicator`, `stableSetVertices`, `stableSetPolytope`, and `clique_relaxation`,
-- together with mathlib's `SimpleGraph.IsIndepSet`, `SimpleGraph.IsClique`, `convexHull`, and
-- `Matrix.PosSemidef` APIs. There is no upstream theta-body owner in the project, so this file
-- keeps the source-facing owner `theta_body` and factors its primitive witness data into the
-- matrix property `Matrix.IsThetaBodyWitness`.

section ThetaBodyWitness

variable {V : Type}
variable (G : SimpleGraph V)

namespace Matrix

/-- A matrix `Y` is a theta-body witness for `x` when it satisfies the positive-semidefinite,
affine, and edge-zero constraints from equation `(10.4)`. -/
def IsThetaBodyWitness
    (Y : Matrix (Option V) (Option V) ℝ)
    (G : SimpleGraph V) (x : V → ℝ) : Prop :=
  Y.PosSemidef ∧
    Y none none = 1 ∧
    (∀ v : V, Y none (some v) = x v) ∧
    (∀ v : V, Y (some v) (some v) = x v) ∧
    ∀ ⦃u v : V⦄, G.Adj u v → Y (some u) (some v) = 0

/-- `Y.IsThetaBodyWitness G x` unfolds to the positive-semidefinite witness conditions from
equation `(10.4)`. -/
theorem isThetaBodyWitness_iff
    {Y : Matrix (Option V) (Option V) ℝ} {x : V → ℝ} :
    Y.IsThetaBodyWitness G x ↔
      Y.PosSemidef ∧
        Y none none = 1 ∧
        (∀ v : V, Y none (some v) = x v) ∧
        (∀ v : V, Y (some v) (some v) = x v) ∧
        ∀ ⦃u v : V⦄, G.Adj u v → Y (some u) (some v) = 0 := Iff.rfl

namespace IsThetaBodyWitness

/-- Constructor for the theta-body witness conditions from equation `(10.4)`. -/
theorem mk
    {Y : Matrix (Option V) (Option V) ℝ} {x : V → ℝ}
    (hPosSemidef : Y.PosSemidef)
    (hNoneNone : Y none none = 1)
    (hNoneSome : ∀ v : V, Y none (some v) = x v)
    (hDiag : ∀ v : V, Y (some v) (some v) = x v)
    (hEdge : ∀ ⦃u v : V⦄, G.Adj u v → Y (some u) (some v) = 0) :
    Y.IsThetaBodyWitness G x :=
  ⟨hPosSemidef, hNoneNone, hNoneSome, hDiag, hEdge⟩

/-- A theta-body witness matrix is positive semidefinite. -/
theorem posSemidef
    {Y : Matrix (Option V) (Option V) ℝ} {x : V → ℝ}
    (hY : Y.IsThetaBodyWitness G x) :
    Y.PosSemidef :=
  hY.1

/-- A theta-body witness matrix is normalized by `Y none none = 1`. -/
theorem apply_none_none
    {Y : Matrix (Option V) (Option V) ℝ} {x : V → ℝ}
    (hY : Y.IsThetaBodyWitness G x) :
    Y none none = 1 :=
  hY.2.1

/-- The `none` row of a theta-body witness matrix recovers the vector `x`. -/
theorem apply_none_some
    {Y : Matrix (Option V) (Option V) ℝ} {x : V → ℝ}
    (hY : Y.IsThetaBodyWitness G x) (v : V) :
    Y none (some v) = x v :=
  hY.2.2.1 v

/-- The `none` column of a theta-body witness matrix recovers the vector `x`. -/
theorem apply_some_none
    {Y : Matrix (Option V) (Option V) ℝ} {x : V → ℝ}
    (hY : Y.IsThetaBodyWitness G x) (v : V) :
    Y (some v) none = x v :=
  by
    let hHerm := hY.posSemidef.isHermitian
    simpa [apply_none_some G hY v] using hHerm.apply none (some v)

/-- The diagonal entries indexed by `some v` recover the vector `x`. -/
theorem apply_some_some
    {Y : Matrix (Option V) (Option V) ℝ} {x : V → ℝ}
    (hY : Y.IsThetaBodyWitness G x) (v : V) :
    Y (some v) (some v) = x v :=
  hY.2.2.2.1 v

/-- A theta-body witness matrix vanishes on entries indexed by graph edges. -/
theorem apply_some_some_eq_zero_of_adj
    {Y : Matrix (Option V) (Option V) ℝ} {x : V → ℝ}
    (hY : Y.IsThetaBodyWitness G x) {u v : V} (huv : G.Adj u v) :
    Y (some u) (some v) = 0 :=
  hY.2.2.2.2 huv

end IsThetaBodyWitness

end Matrix

/-- The Lovász theta-body relaxation `TH(G)` consists of the vectors `x : V → ℝ` admitting a
theta-body witness matrix. -/
def theta_body : Set (V → ℝ) :=
  {x | ∃ Y : Matrix (Option V) (Option V) ℝ,
      Y.IsThetaBodyWitness G x}

/-- Source notation for the Lovász theta body. -/
notation "TH(" G ")" => theta_body G

/-- Source notation for the clique relaxation of a graph. -/
notation "QSTAB(" G ")" => clique_relaxation G

/-- Membership in `TH(G)` is exactly the existence of a theta-body witness matrix. -/
theorem mem_theta_body_iff
    {x : V → ℝ} :
    x ∈ TH(G) ↔
      ∃ Y : Matrix (Option V) (Option V) ℝ,
        Y.IsThetaBodyWitness G x := Iff.rfl

/-- A theta-body witness matrix gives a point of `TH(G)`. -/
theorem Matrix.IsThetaBodyWitness.mem_theta_body
    {Y : Matrix (Option V) (Option V) ℝ} {x : V → ℝ}
    (hY : Y.IsThetaBodyWitness G x) :
    x ∈ TH(G) :=
  ⟨Y, hY⟩

end ThetaBodyWitness

section Theorem_10_4

variable {V : Type}
variable (G : SimpleGraph V)

/-- Helper for Theorem `10.4`: the raw quadratic form attached to `Matrix.vecMulVec a a`
collapses to a square of the single linear form `∑ i, z i * a i`. -/
lemma finsuppQuadratic_vecMulVec_eq_sq
    {ι : Type} (z : ι →₀ ℝ) (a : ι → ℝ) :
    z.sum (fun i zi ↦ z.sum (fun j zj ↦ zi * Matrix.vecMulVec a a i j * zj)) =
      (z.sum fun i zi ↦ zi * a i)^2 := by
  -- Expand the rank-one entries and commute the two finite-support sums.
  calc
    z.sum (fun i zi ↦ z.sum (fun j zj ↦ zi * Matrix.vecMulVec a a i j * zj))
        = z.sum (fun j zj ↦ z.sum (fun i zi ↦ (zi * a i) * (zj * a j))) := by
            rw [Finsupp.sum_comm]
            simp [Matrix.vecMulVec_apply, mul_left_comm, mul_comm]
    _ = (z.sum fun i zi ↦ zi * a i)^2 := by
          rw [sq, Finsupp.mul_sum]
          simp_rw [Finsupp.sum_mul]

/-- Helper for Theorem `10.4`: the rank-one matrix `Matrix.vecMulVec a a` is positive
semidefinite
without any ambient finiteness hypothesis on the index type. -/
lemma posSemidef_vecMulVec
    {ι : Type} (a : ι → ℝ) :
    (Matrix.vecMulVec a a).PosSemidef := by
  refine ⟨?_, ?_⟩
  · -- Over `ℝ`, the rank-one matrix is symmetric because multiplication commutes.
    ext i j
    simp [Matrix.vecMulVec_apply, mul_comm]
  · intro z
    -- Rewrite the raw quadratic form as a square and use its obvious nonnegativity.
    simpa [finsuppQuadratic_vecMulVec_eq_sq (z := z) (a := a)] using
      sq_nonneg (z.sum fun i zi ↦ zi * a i)

/-- Helper for Theorem `10.4`: the theta body `TH(G)` is convex. -/
lemma convex_thetaBody :
    Convex ℝ (TH(G)) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨Yx, hYx⟩
  rcases hy with ⟨Yy, hYy⟩
  refine ⟨a • Yx + b • Yy, ?_⟩
  -- Combine the two witness matrices with the same convex coefficients.
  refine Matrix.IsThetaBodyWitness.mk (G := G) ?_ ?_ ?_ ?_ ?_
  · exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hYx.posSemidef ha)
      (Matrix.PosSemidef.smul hYy.posSemidef hb)
  · calc
      (a • Yx + b • Yy) none none = a * Yx none none + b * Yy none none := by simp
      _ = a * 1 + b * 1 := by rw [hYx.apply_none_none, hYy.apply_none_none]
      _ = 1 := by linarith
  · intro v
    calc
      (a • Yx + b • Yy) none (some v) = a * Yx none (some v) + b * Yy none (some v) := by simp
      _ = a * x v + b * y v := by rw [hYx.apply_none_some, hYy.apply_none_some]
      _ = (a • x + b • y) v := by simp
  · intro v
    calc
      (a • Yx + b • Yy) (some v) (some v) =
          a * Yx (some v) (some v) + b * Yy (some v) (some v) := by simp
      _ = a * x v + b * y v := by rw [hYx.apply_some_some, hYy.apply_some_some]
      _ = (a • x + b • y) v := by simp
  · intro u v huv
    calc
      (a • Yx + b • Yy) (some u) (some v) =
          a * Yx (some u) (some v) + b * Yy (some u) (some v) := by simp
      _ = a * 0 + b * 0 := by
        simp
          [ Matrix.IsThetaBodyWitness.apply_some_some_eq_zero_of_adj (G := G) hYx huv
          , Matrix.IsThetaBodyWitness.apply_some_some_eq_zero_of_adj (G := G) hYy huv ]
      _ = 0 := by simp

/-- Helper for Theorem `10.4`: the indicator of a finite stable set lies in `TH(G)`. -/
lemma stableSetIndicator_mem_thetaBody
    (s : Finset V) (hs : G.IsIndepSet s) :
    stableSetIndicator s ∈ TH(G) := by
  classical
  let a : Option V → ℝ := Option.elim' 1 (stableSetIndicator s)
  let Y : Matrix (Option V) (Option V) ℝ := Matrix.vecMulVec a a
  -- Use the source's rank-one witness `Y = (1, χ)(1, χ)ᵀ`.
  refine ⟨Y, ?_⟩
  refine Matrix.IsThetaBodyWitness.mk (G := G) ?_ ?_ ?_ ?_ ?_
  · simpa [Y] using posSemidef_vecMulVec (a := a)
  · simp [Y, a, Matrix.vecMulVec]
  · intro v
    simp [Y, a, Matrix.vecMulVec]
  · intro v
    by_cases hv : v ∈ s
    · simp [Y, a, Matrix.vecMulVec, stableSetIndicator_of_mem hv]
    · simp [Y, a, Matrix.vecMulVec, stableSetIndicator_of_notMem hv]
  · intro u v huv
    -- Adjacent vertices cannot both lie in an independent set, so one factor vanishes.
    by_cases hu : u ∈ s
    · by_cases hv : v ∈ s
      · exact False.elim <| (hs hu hv huv.ne) huv
      · simp [Y, a, Matrix.vecMulVec, stableSetIndicator_of_mem hu, stableSetIndicator_of_notMem hv]
    · simp [Y, a, Matrix.vecMulVec, stableSetIndicator_of_notMem hu]

/-- Helper for Theorem `10.4`: theta-body points are coordinatewise nonnegative. -/
lemma thetaBody_nonneg
    {x : V → ℝ} (hx : x ∈ TH(G)) :
    ∀ v : V, 0 ≤ x v := by
  rcases hx with ⟨Y, hY⟩
  intro v
  -- Read the coordinate from the diagonal of a positive-semidefinite witness.
  have hdiag : 0 ≤ Y (some v) (some v) :=
    Matrix.PosSemidef.diag_nonneg hY.posSemidef (i := some v)
  simpa [Matrix.IsThetaBodyWitness.apply_some_some (G := G) hY v] using hdiag

/-- Helper for Theorem `10.4`: the `none` coordinate of the clique test vector on the
principal
submatrix equals `1 - K.sum x`. -/
lemma thetaWitnessCliqueTestVector_mulVec_none
    {Y : Matrix (Option V) (Option V) ℝ} {x : V → ℝ}
    (hY : Y.IsThetaBodyWitness G x)
    (K : Finset V) :
    let e : Option ↑K → Option V := fun
      | none => none
      | some k => some k.1
    let A : Matrix (Option ↑K) (Option ↑K) ℝ := Y.submatrix e e
    let w : Option ↑K → ℝ := fun
      | none => 1
      | some _ => -1
    (A.mulVec w) none = 1 - K.sum x := by
  classical
  intro e A w
  -- Expand the top row of the principal submatrix against the fixed test vector.
  rw [Matrix.mulVec, dotProduct, Fintype.sum_option]
  calc
    A none none * w none + ∑ k : ↑K, A none (some k) * w (some k)
        = 1 - ∑ k : ↑K, x k := by
            simp [A, e, w, Matrix.IsThetaBodyWitness.apply_none_none (G := G) hY,
              Matrix.IsThetaBodyWitness.apply_none_some (G := G) hY]
            ring
    _ = 1 - K.sum x := by
          rw [Finset.univ_eq_attach, Finset.sum_attach]

/-- Helper for Theorem `10.4`: each clique-indexed coordinate of the principal-submatrix
test
vector vanishes after diagonal cancellation and off-diagonal edge-zero rewrites. -/
lemma thetaWitnessCliqueTestVector_mulVec_some
    {Y : Matrix (Option V) (Option V) ℝ} {x : V → ℝ}
    (hY : Y.IsThetaBodyWitness G x)
    (K : Finset V) (hK : G.IsClique K)
    (k : ↑K) :
    let e : Option ↑K → Option V := fun
      | none => none
      | some l => some l.1
    let A : Matrix (Option ↑K) (Option ↑K) ℝ := Y.submatrix e e
    let w : Option ↑K → ℝ := fun
      | none => 1
      | some _ => -1
    (A.mulVec w) (some k) = 0 := by
  classical
  rw [SimpleGraph.isClique_iff] at hK
  intro e A w
  have hrow_sum :
      ∑ l : ↑K, A (some k) (some l) * w (some l) = -A (some k) (some k) := by
    -- In a clique row, every off-diagonal entry vanishes, so only the diagonal survives.
    calc
      ∑ l : ↑K, A (some k) (some l) * w (some l)
          = A (some k) (some k) * w (some k) := by
              rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
              intro l _ hkl
              have hkl_val : (k : V) ≠ l := by
                intro h
                apply hkl
                exact Subtype.ext h.symm
              have hzero : A (some k) (some l) = 0 := by
                simpa [A, e] using
                  Matrix.IsThetaBodyWitness.apply_some_some_eq_zero_of_adj (G := G) hY
                    (hK k.2 l.2 hkl_val)
              simp [hzero]
      _ = -A (some k) (some k) := by
            simp [w]
  -- The lower coordinate is the `none` entry minus the diagonal contribution, and those cancel.
  calc
    (A.mulVec w) (some k)
        = A (some k) none * w none + ∑ l : ↑K, A (some k) (some l) * w (some l) := by
            rw [Matrix.mulVec, dotProduct, Fintype.sum_option]
    _ = x k - A (some k) (some k) := by
          rw [hrow_sum]
          simp [A, e, w, sub_eq_add_neg, Matrix.IsThetaBodyWitness.apply_some_none (G := G) hY]
    _ = 0 := by
          have hdiag : A (some k) (some k) = x k := by
            simp [A, e, Matrix.IsThetaBodyWitness.apply_some_some (G := G) hY]
          rw [hdiag]
          ring

/-- Helper for Theorem `10.4`: a theta-body witness satisfies every clique inequality. -/
lemma one_sub_cliqueSum_nonneg_of_thetaWitness
    {Y : Matrix (Option V) (Option V) ℝ} {x : V → ℝ}
    (hY : Y.IsThetaBodyWitness G x)
    (K : Finset V) (hK : G.IsClique K) :
    0 ≤ 1 - K.sum x := by
  classical
  let e : Option ↑K → Option V := fun
    | none => none
    | some k => some k.1
  let A : Matrix (Option ↑K) (Option ↑K) ℝ := Y.submatrix e e
  let w : Option ↑K → ℝ := fun
    | none => 1
    | some _ => -1
  have hApsd : A.PosSemidef := by
    -- Positive semidefiniteness survives when we pass to a principal submatrix.
    simpa [A] using hY.posSemidef.submatrix e
  have hmul_none : (A.mulVec w) none = 1 - K.sum x := by
    -- The top coordinate is exactly the slack of the clique inequality.
    simpa [A, e, w] using thetaWitnessCliqueTestVector_mulVec_none (G := G) hY K
  have hmul_some : ∀ k : ↑K, (A.mulVec w) (some k) = 0 := by
    intro k
    -- Every clique-indexed coordinate cancels after the diagonal/off-diagonal split.
    simpa [A, e, w] using thetaWitnessCliqueTestVector_mulVec_some (G := G) hY K hK k
  have hnonneg : 0 ≤ dotProduct w (A.mulVec w) := by
    -- Evaluate the PSD quadratic form on the test vector `w`.
    simpa using hApsd.dotProduct_mulVec_nonneg w
  have hquad : dotProduct w (A.mulVec w) = 1 - K.sum x := by
    -- Only the `none` coordinate contributes because the clique coordinates vanish.
    rw [dotProduct, Fintype.sum_option]
    simp [w, hmul_none, hmul_some]
  rw [hquad] at hnonneg
  exact hnonneg

/-- First inclusion from Theorem `10.4`: for any graph `G`,
`STAB(G) ⊆ TH(G)`. The source states this
for finite graphs; the same inclusion is exposed here in the stronger graph-level form
`STAB(G) ⊆ TH(G)`. -/
theorem stableSetPolytope_subset_theta_body :
    STAB(G) ⊆ TH(G) := by
  -- Lift the vertexwise rank-one witnesses through the convex-hull presentation of `STAB(G)`.
  rw [stableSetPolytope_eq_convexHull]
  refine convexHull_min ?_ (convex_thetaBody (G := G))
  intro x hx
  rcases hx with ⟨s, hs, rfl⟩
  exact stableSetIndicator_mem_thetaBody (G := G) s hs

/-- Second inclusion from Theorem `10.4`: for any graph `G`,
`TH(G) ⊆ QSTAB(G)`. The source states this for finite
graphs; the same inclusion is exposed here in the stronger graph-level form
`TH(G) ⊆ QSTAB(G)`. -/
theorem theta_body_subset_clique_relaxation :
    TH(G) ⊆ QSTAB(G) := by
  intro x hx
  rw [mem_clique_relaxation_iff]
  constructor
  · -- Positive semidefiniteness already forces coordinatewise nonnegativity.
    exact thetaBody_nonneg (G := G) hx
  · intro K hK
    rcases hx with ⟨Y, hY⟩
    -- Evaluate the witness on the finite principal submatrix indexed by the clique.
    have hnonneg :
        0 ≤ 1 - K.sum x :=
      one_sub_cliqueSum_nonneg_of_thetaWitness (G := G) hY K hK
    linarith

/-- Theorem 10.4. For any graph `G`, `STAB(G) ⊆ TH(G) ∧ TH(G) ⊆ QSTAB(G)`.
Packaging the two component inclusions together gives
`STAB(G) ⊆ TH(G) ∧ TH(G) ⊆ QSTAB(G)`. -/
theorem stableSetPolytope_subset_theta_body_and_theta_body_subset_clique_relaxation :
    STAB(G) ⊆ TH(G) ∧ TH(G) ⊆ QSTAB(G) := by
  constructor
  · -- The first inclusion is the convex-hull lifting from stable-set indicators.
    exact stableSetPolytope_subset_theta_body (G := G)
  · -- The second inclusion is the clique-inequality consequence of theta witnesses.
    exact theta_body_subset_clique_relaxation (G := G)

end Theorem_10_4
