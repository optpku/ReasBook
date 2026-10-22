/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_13
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_26.Halfspace
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_8

open WithLp (toLp)

noncomputable section

section

variable {n p : ℕ}

/- The row-halfspace owner layer for Algorithm 12.9 is `source-facing`: it records the
normals `a_i`, the halfspaces `C_i = {x | ⟪a_i, x⟫ ≤ b_i}`, and the
metric-projection bridge needed by the Algorithm 12.9 step-(b) formula. This
file packages that reusable rowwise layer so later files can import it
directly without importing the full algorithm item. -/

/-- The `i`th row of `A`, viewed as the halfspace normal `a_i ∈ ℝ^n`. -/
def polyhedral_projection_halfspace_normal
    (A : Matrix (Fin p) (Fin n) ℝ) (i : Fin p) : EuclideanSpace ℝ (Fin n) :=
  toLp 2 (fun j ↦ A i j)

/-- Evaluating the row-normal vector at coordinate `j` gives the matrix entry `A i j`. -/
@[simp] theorem polyhedral_projection_halfspace_normal_apply
    (A : Matrix (Fin p) (Fin n) ℝ) (i : Fin p) (j : Fin n) :
    polyhedral_projection_halfspace_normal A i j = A i j :=
  rfl

/-- Pairing the `i`th row normal with `x` recovers the `i`th coordinate of `A x`. -/
@[simp] theorem polyhedral_projection_halfspace_normal_inner
    (A : Matrix (Fin p) (Fin n) ℝ) (i : Fin p) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (polyhedral_projection_halfspace_normal A i) x = A.toEuclideanLin x i := by
  calc
    inner ℝ (polyhedral_projection_halfspace_normal A i) x =
        x.ofLp ⬝ᵥ fun j ↦ A i j := by
          simpa [polyhedral_projection_halfspace_normal] using
            EuclideanSpace.inner_toLp_toLp (fun j ↦ A i j) x.ofLp
    _ = (fun j ↦ A i j) ⬝ᵥ x.ofLp := by
      rw [dotProduct_comm]
    _ = A.mulVec x.ofLp i := by
      simp [Matrix.mulVec]
    _ = (A.toEuclideanLin x).ofLp i := by
      rfl
    _ = A.toEuclideanLin x i := by
      rfl

/-- The `i`th row halfspace
`C_i = {x ∈ ℝ^n | ⟪a_i, x⟫ ≤ b_i}` associated to `A x ≤ b`. -/
def polyhedral_projection_halfspace
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  halfSpace (polyhedral_projection_halfspace_normal A i) (b i)

/-- Membership in the `i`th row halfspace is exactly the `i`th scalar inequality of `A x ≤ b`. -/
@[simp] theorem mem_polyhedral_projection_halfspace_iff
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) (i : Fin p)
    (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ polyhedral_projection_halfspace A b i ↔ A.toEuclideanLin x i ≤ b i := by
  simp [polyhedral_projection_halfspace, mem_halfSpace_iff]

/-- Each row halfspace of `A x ≤ b` is closed. -/
theorem polyhedral_projection_halfspace_isClosed
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    IsClosed (polyhedral_projection_halfspace A b i) :=
  (isClosed_Iic.preimage
    (innerSL ℝ (polyhedral_projection_halfspace_normal A i)).continuous :
    IsClosed
      ((innerSL ℝ (polyhedral_projection_halfspace_normal A i)) ⁻¹'
        Set.Iic (b i)))

/-- Each row halfspace of `A x ≤ b` is convex. -/
theorem polyhedral_projection_halfspace_convex
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    Convex ℝ (polyhedral_projection_halfspace A b i) := by
  simpa [polyhedral_projection_halfspace] using
    convex_halfSpace_owner (polyhedral_projection_halfspace_normal A i) (b i)

/-- A nonempty feasible set `A x ≤ b` gives nonemptiness of every row halfspace. -/
theorem polyhedral_projection_halfspace_nonempty_of_feasible_set_nonempty
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    (hS_nonempty : (polyhedral_projection_feasible_set A b).Nonempty) (i : Fin p) :
    (polyhedral_projection_halfspace A b i).Nonempty := by
  rcases hS_nonempty with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  exact (mem_polyhedral_projection_halfspace_iff A b i x).2
    ((mem_polyhedral_projection_feasible_set A b).1 hx i)

/-- A row halfspace with nonzero normal is automatically nonempty. -/
theorem polyhedral_projection_halfspace_nonempty_of_normal_ne_zero
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    (i : Fin p) (ha : polyhedral_projection_halfspace_normal A i ≠ 0) :
    (polyhedral_projection_halfspace A b i).Nonempty := by
  refine ⟨((b i) / ‖polyhedral_projection_halfspace_normal A i‖ ^ (2 : ℕ)) •
      polyhedral_projection_halfspace_normal A i, ?_⟩
  rw [polyhedral_projection_halfspace, mem_halfSpace_iff, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  have hnorm : ‖polyhedral_projection_halfspace_normal A i‖ ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  have hboundary :
      ((b i) / ‖polyhedral_projection_halfspace_normal A i‖ ^ (2 : ℕ)) *
          ‖polyhedral_projection_halfspace_normal A i‖ ^ (2 : ℕ) =
        b i := by
    field_simp [hnorm]
  exact hboundary.le

/-- Under a nonzero row normal, projecting onto the `i`th row halfspace has the standard
halfspace projection formula. -/
theorem polyhedral_projection_halfspace_projectionPoint_eq
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    (i : Fin p) (x : EuclideanSpace ℝ (Fin n))
    (ha : polyhedral_projection_halfspace_normal A i ≠ 0) :
    Pp[
        polyhedral_projection_halfspace A b i,
        polyhedral_projection_halfspace_nonempty_of_normal_ne_zero A b i ha,
        polyhedral_projection_halfspace_isClosed A b i,
        polyhedral_projection_halfspace_convex A b i] x =
      x - (((inner ℝ (polyhedral_projection_halfspace_normal A i) x - b i)⁺ /
        ‖polyhedral_projection_halfspace_normal A i‖ ^ (2 : ℕ)) •
        polyhedral_projection_halfspace_normal A i) := by
  let C := polyhedral_projection_halfspace A b i
  let hCi_nonempty : C.Nonempty :=
    polyhedral_projection_halfspace_nonempty_of_normal_ne_zero A b i ha
  let z :=
    x - (((inner ℝ (polyhedral_projection_halfspace_normal A i) x - b i)⁺ /
      ‖polyhedral_projection_halfspace_normal A i‖ ^ (2 : ℕ)) •
      polyhedral_projection_halfspace_normal A i)
  have hP :
      P[C] x = {z} := by
    simpa [C, z, polyhedral_projection_halfspace] using
      projection_mapping_halfSpace_eq_singleton_positivePartCorrection
        (polyhedral_projection_halfspace_normal A i) x (b i) ha
  have hPi :
      Pp[
          C,
          hCi_nonempty,
          polyhedral_projection_halfspace_isClosed A b i,
          polyhedral_projection_halfspace_convex A b i] x ∈ P[C] x := by
    rw [mem_projection_mapping_iff, isMinOn_iff]
    refine ⟨?_, ?_⟩
    · exact projectionPoint_mem C hCi_nonempty
        (polyhedral_projection_halfspace_isClosed A b i)
        (polyhedral_projection_halfspace_convex A b i) x
    · intro y hy
      have h_bdd : BddBelow (Set.range fun w : C ↦ ‖x - w‖) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨w, rfl⟩
        exact norm_nonneg (x - (w : EuclideanSpace ℝ (Fin n)))
      have hinf :
          (⨅ w : C, ‖x - w‖) ≤ ‖x - y‖ := by
        simpa using ciInf_le h_bdd ⟨y, hy⟩
      have hproj :
          ‖x -
              Pp[
                C,
                hCi_nonempty,
                polyhedral_projection_halfspace_isClosed A b i,
                polyhedral_projection_halfspace_convex A b i] x‖ =
            ⨅ w : C, ‖x - w‖ := by
        simpa [norm_sub_rev] using
          norm_sub_metricProjection_eq_iInf C hCi_nonempty
            (polyhedral_projection_halfspace_isClosed A b i)
            (polyhedral_projection_halfspace_convex A b i) x
      simpa [norm_sub_rev] using le_trans hproj.le hinf
  have hz :
      Pp[
          C,
          hCi_nonempty,
          polyhedral_projection_halfspace_isClosed A b i,
          polyhedral_projection_halfspace_convex A b i] x ∈
        ({z} : Set (EuclideanSpace ℝ (Fin n))) := by
    simpa [hP] using hPi
  simpa [C, hCi_nonempty, z] using Set.mem_singleton_iff.mp hz

end
