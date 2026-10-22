/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_13
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_7.ProjectionStep
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_8
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_9.Halfspace

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open WithLp (toLp)

noncomputable section

section

variable {n p : ℕ}

/- Algorithm 12.9 is `source-facing`: it specializes the finite-intersection FDPG recursion from
Algorithm 12.8 to the row halfspaces of `A x ≤ b`. The row-halfspace owner layer and its Chapter 6
projection bridge are imported from `Algorithm_12_9.Halfspace`; this file keeps the specialized
iterate families `u^k`, `y^k`, `w^k` and the textbook rowwise step-(b) update formulas. -/

/-- Algorithm 12.9: the second-version FDPG dual sequence specialized to the
row halfspaces `C_i = {x | ⟪a_i, x⟫ ≤ b_i}` of `A x ≤ b`, with explicit
rowwise nonemptiness input, admissible constant parameter `L ≥ p`, and
initialization `w⁰ = y⁰ = y0 ∈ (ℝ^n)^p`. -/
def polyhedral_projection_second_fdpg_y
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    (hC_nonempty : ∀ i, (polyhedral_projection_halfspace A b i).Nonempty)
    (d : EuclideanSpace ℝ (Fin n))
    (L : DualBasedProximalGradientDualStepsizeParameter
      (dual_block_duplication (EuclideanSpace ℝ (Fin n)) p) 1)
    (y0 : Fin p → EuclideanSpace ℝ (Fin n)) :
    ℕ → Fin p → EuclideanSpace ℝ (Fin n) :=
  finite_intersection_fdpg_y
    (polyhedral_projection_halfspace A b)
    hC_nonempty
    (polyhedral_projection_halfspace_isClosed A b)
    (polyhedral_projection_halfspace_convex A b)
    L d y0

/-- The second-FDPG extrapolated block sequence `w^k`. -/
def polyhedral_projection_second_fdpg_w
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    (hC_nonempty : ∀ i, (polyhedral_projection_halfspace A b i).Nonempty)
    (d : EuclideanSpace ℝ (Fin n))
    (L : DualBasedProximalGradientDualStepsizeParameter
      (dual_block_duplication (EuclideanSpace ℝ (Fin n)) p) 1)
    (y0 : Fin p → EuclideanSpace ℝ (Fin n)) :
    ℕ → Fin p → EuclideanSpace ℝ (Fin n) :=
  finite_intersection_fdpg_w
    (polyhedral_projection_halfspace A b)
    hC_nonempty
    (polyhedral_projection_halfspace_isClosed A b)
    (polyhedral_projection_halfspace_convex A b)
    L d y0

/-- The auxiliary primal sequence `u^k = ∑ i, w_i^k + d` derived from the second FDPG iterates. -/
def polyhedral_projection_second_fdpg_u
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    (hC_nonempty : ∀ i, (polyhedral_projection_halfspace A b i).Nonempty)
    (d : EuclideanSpace ℝ (Fin n))
    (L : DualBasedProximalGradientDualStepsizeParameter
      (dual_block_duplication (EuclideanSpace ℝ (Fin n)) p) 1)
    (y0 : Fin p → EuclideanSpace ℝ (Fin n)) :
    ℕ → EuclideanSpace ℝ (Fin n) :=
  finite_intersection_fdpg_u
    (polyhedral_projection_halfspace A b)
    hC_nonempty
    (polyhedral_projection_halfspace_isClosed A b)
    (polyhedral_projection_halfspace_convex A b)
    L d y0

section

variable (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
variable (hC_nonempty : ∀ i, (polyhedral_projection_halfspace A b i).Nonempty)
variable (d : EuclideanSpace ℝ (Fin n))
variable (L : DualBasedProximalGradientDualStepsizeParameter
  (dual_block_duplication (EuclideanSpace ℝ (Fin n)) p) 1)
variable (y0 : Fin p → EuclideanSpace ℝ (Fin n))

private theorem polyhedral_projection_second_fdpg_cancel
    (u w : EuclideanSpace ℝ (Fin n)) (hL0 : (L : ℝ) ≠ 0) :
    w - (1 / L : ℝ) • u + (1 / L : ℝ) • (u - (L : ℝ) • w) = 0 := by
  have hL : (1 / (L : ℝ)) * (L : ℝ) = 1 := by
    field_simp [hL0]
  calc
    w - (1 / L : ℝ) • u + (1 / L : ℝ) • (u - (L : ℝ) • w) =
        w - (1 / L : ℝ) • u +
          ((1 / L : ℝ) • u - (((1 / (L : ℝ)) * (L : ℝ)) • w)) := by
            rw [smul_sub, smul_smul]
    _ = w - (1 / L : ℝ) • u + ((1 / L : ℝ) • u - w) := by
      rw [hL]
      simp
    _ = 0 := by
      abel_nf

/-- The second-FDPG dual sequence starts from the prescribed initialization `y⁰ = y0`. -/
@[simp] theorem polyhedral_projection_second_fdpg_y_zero
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    (hC_nonempty : ∀ i, (polyhedral_projection_halfspace A b i).Nonempty)
    (d : EuclideanSpace ℝ (Fin n))
    (L : DualBasedProximalGradientDualStepsizeParameter
      (dual_block_duplication (EuclideanSpace ℝ (Fin n)) p) 1)
    (y0 : Fin p → EuclideanSpace ℝ (Fin n)) :
    polyhedral_projection_second_fdpg_y A b hC_nonempty d L y0 0 = y0 :=
  rfl

/-- The second-FDPG extrapolated sequence starts from `w⁰ = y⁰ = y0`. -/
@[simp] theorem polyhedral_projection_second_fdpg_w_zero
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    (hC_nonempty : ∀ i, (polyhedral_projection_halfspace A b i).Nonempty)
    (d : EuclideanSpace ℝ (Fin n))
    (L : DualBasedProximalGradientDualStepsizeParameter
      (dual_block_duplication (EuclideanSpace ℝ (Fin n)) p) 1)
    (y0 : Fin p → EuclideanSpace ℝ (Fin n)) :
    polyhedral_projection_second_fdpg_w A b hC_nonempty d L y0 0 = y0 :=
  rfl

/-- At every iteration `k`, the auxiliary point satisfies the step-(a) formula
`u^k = ∑ i, w_i^k + d`. -/
theorem polyhedral_projection_second_fdpg_u_eq
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    (hC_nonempty : ∀ i, (polyhedral_projection_halfspace A b i).Nonempty)
    (d : EuclideanSpace ℝ (Fin n))
    (L : DualBasedProximalGradientDualStepsizeParameter
      (dual_block_duplication (EuclideanSpace ℝ (Fin n)) p) 1)
    (y0 : Fin p → EuclideanSpace ℝ (Fin n))
    (k : ℕ) :
    polyhedral_projection_second_fdpg_u A b hC_nonempty d L y0 k =
      (∑ i : Fin p, polyhedral_projection_second_fdpg_w A b hC_nonempty d L y0 k i) + d :=
  rfl

/-- Each successor dual block vector is obtained by the shared finite-intersection halfspace
update owner applied to `u^k` and `w^k`. -/
theorem polyhedral_projection_second_fdpg_y_succ
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    (hC_nonempty : ∀ i, (polyhedral_projection_halfspace A b i).Nonempty)
    (d : EuclideanSpace ℝ (Fin n))
    (L : DualBasedProximalGradientDualStepsizeParameter
      (dual_block_duplication (EuclideanSpace ℝ (Fin n)) p) 1)
    (y0 : Fin p → EuclideanSpace ℝ (Fin n))
    (k : ℕ) :
    polyhedral_projection_second_fdpg_y A b hC_nonempty d L y0 (k + 1) =
      finite_intersection_projection_dual_update
        (polyhedral_projection_halfspace A b)
        hC_nonempty
        (polyhedral_projection_halfspace_isClosed A b)
        (polyhedral_projection_halfspace_convex A b)
        L
        (polyhedral_projection_second_fdpg_u A b hC_nonempty d L y0 k)
        (polyhedral_projection_second_fdpg_w A b hC_nonempty d L y0 k) :=
  rfl

/-- Step-(b) bridge theorem: for each row `i` with nonzero normal `a_i`, the successor block
`y_i^(k+1)` is given by the textbook halfspace update formula. -/
theorem polyhedral_projection_second_fdpg_y_succ_apply
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    (hC_nonempty : ∀ i, (polyhedral_projection_halfspace A b i).Nonempty)
    (d : EuclideanSpace ℝ (Fin n))
    (L : DualBasedProximalGradientDualStepsizeParameter
      (dual_block_duplication (EuclideanSpace ℝ (Fin n)) p) 1)
    (y0 : Fin p → EuclideanSpace ℝ (Fin n))
    (k : ℕ) (i : Fin p) (ha : polyhedral_projection_halfspace_normal A i ≠ 0) :
    polyhedral_projection_second_fdpg_y A b hC_nonempty d L y0 (k + 1) i =
      -((max
            (inner ℝ
              (polyhedral_projection_halfspace_normal A i)
              (polyhedral_projection_second_fdpg_u A b hC_nonempty d L y0 k -
                (L : ℝ) • polyhedral_projection_second_fdpg_w A b hC_nonempty d L y0 k i) -
              b i)
            0) /
          ((L : ℝ) * ‖polyhedral_projection_halfspace_normal A i‖ ^ (2 : ℕ))) •
        polyhedral_projection_halfspace_normal A i := by
  set u := polyhedral_projection_second_fdpg_u A b hC_nonempty d L y0 k
  set w := polyhedral_projection_second_fdpg_w A b hC_nonempty d L y0 k i
  set a := polyhedral_projection_halfspace_normal A i
  set t : ℝ := inner ℝ a (u - (L : ℝ) • w) - b i
  have ha0 : a ≠ 0 := by
    simpa [a] using ha
  have hproj :
      Pp[
          polyhedral_projection_halfspace A b i,
          hC_nonempty i,
          polyhedral_projection_halfspace_isClosed A b i,
          polyhedral_projection_halfspace_convex A b i] (u - (L : ℝ) • w) =
        (u - (L : ℝ) • w) - ((t⁺ / ‖a‖ ^ (2 : ℕ)) • a) := by
    have hCi_eq :
        polyhedral_projection_halfspace_nonempty_of_normal_ne_zero A b i ha0 =
          hC_nonempty i := by
      apply Subsingleton.elim
    cases hCi_eq
    simpa [a, t, u, w] using
      polyhedral_projection_halfspace_projectionPoint_eq
        A b i (u - (L : ℝ) • w) ha0
  have hL0 : (L : ℝ) ≠ 0 := by
    exact (PosReal.coe_pos (L : PosReal)).ne'
  have hnorm : ‖a‖ ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr ha0)
  have hcancel :
      w - (1 / L : ℝ) • u + (1 / L : ℝ) • (u - (L : ℝ) • w) =
        (0 : EuclideanSpace ℝ (Fin n)) := by
    simpa using polyhedral_projection_second_fdpg_cancel L u w hL0
  have hscalar :
      (1 / (L : ℝ)) * (t⁺ / ‖a‖ ^ (2 : ℕ)) =
        t⁺ / ((L : ℝ) * ‖a‖ ^ (2 : ℕ)) := by
    field_simp [hL0, hnorm]
  rw [polyhedral_projection_second_fdpg_y_succ, finite_intersection_projection_dual_update_apply]
  have hmain :
      w - (1 / L : ℝ) • u +
        (1 / L : ℝ) •
          Pp[
              polyhedral_projection_halfspace A b i,
              hC_nonempty i,
              polyhedral_projection_halfspace_isClosed A b i,
              polyhedral_projection_halfspace_convex A b i] (u - (L : ℝ) • w) =
        -((max t 0 / ((L : ℝ) * ‖a‖ ^ (2 : ℕ))) • a) := by
    rw [hproj]
    calc
      w - (1 / L : ℝ) • u +
          (1 / L : ℝ) • ((u - (L : ℝ) • w) - ((t⁺ / ‖a‖ ^ (2 : ℕ)) • a)) =
        (w - (1 / L : ℝ) • u + (1 / L : ℝ) • (u - (L : ℝ) • w)) -
          (1 / L : ℝ) • ((t⁺ / ‖a‖ ^ (2 : ℕ)) • a) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm]
      _ = -((1 / L : ℝ) • ((t⁺ / ‖a‖ ^ (2 : ℕ)) • a)) := by
        rw [hcancel, zero_sub]
      _ = -(((1 / (L : ℝ)) * (t⁺ / ‖a‖ ^ (2 : ℕ))) • a) := by
        simp [smul_smul]
      _ = -((t⁺ / ((L : ℝ) * ‖a‖ ^ (2 : ℕ))) • a) := by
        rw [hscalar]
      _ = -((max t 0 / ((L : ℝ) * ‖a‖ ^ (2 : ℕ))) • a) := by
        rfl
  simpa [u, w, a, t] using hmain

/-- If the `i`th row normal vanishes, then the corresponding halfspace is all of `ℝ^n`, so the
successor block collapses to `0`. -/
theorem polyhedral_projection_second_fdpg_y_succ_apply_of_zero
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    (hC_nonempty : ∀ i, (polyhedral_projection_halfspace A b i).Nonempty)
    (d : EuclideanSpace ℝ (Fin n))
    (L : DualBasedProximalGradientDualStepsizeParameter
      (dual_block_duplication (EuclideanSpace ℝ (Fin n)) p) 1)
    (y0 : Fin p → EuclideanSpace ℝ (Fin n))
    (k : ℕ) (i : Fin p) (ha : polyhedral_projection_halfspace_normal A i = 0) :
    polyhedral_projection_second_fdpg_y A b hC_nonempty d L y0 (k + 1) i = 0 := by
  set u := polyhedral_projection_second_fdpg_u A b hC_nonempty d L y0 k
  set w := polyhedral_projection_second_fdpg_w A b hC_nonempty d L y0 k i
  have hbi : 0 ≤ b i := by
    rcases hC_nonempty i with ⟨z, hz⟩
    rw [polyhedral_projection_halfspace, mem_halfSpace_iff] at hz
    simpa [ha] using hz
  have hx_mem : u - (L : ℝ) • w ∈ polyhedral_projection_halfspace A b i := by
    rw [polyhedral_projection_halfspace, mem_halfSpace_iff]
    simpa [ha] using hbi
  have hproj :
      Pp[
          polyhedral_projection_halfspace A b i,
          hC_nonempty i,
          polyhedral_projection_halfspace_isClosed A b i,
          polyhedral_projection_halfspace_convex A b i] (u - (L : ℝ) • w) =
        u - (L : ℝ) • w := by
    exact
      projectionPoint_eq_self_of_mem
        (polyhedral_projection_halfspace A b i)
        (hC_nonempty i)
        (polyhedral_projection_halfspace_isClosed A b i)
        (polyhedral_projection_halfspace_convex A b i)
        hx_mem
  have hL0 : (L : ℝ) ≠ 0 := by
    exact (PosReal.coe_pos (L : PosReal)).ne'
  have hcancel :
      w - (1 / L : ℝ) • u + (1 / L : ℝ) • (u - (L : ℝ) • w) =
        (0 : EuclideanSpace ℝ (Fin n)) := by
    simpa using polyhedral_projection_second_fdpg_cancel L u w hL0
  rw [polyhedral_projection_second_fdpg_y_succ, finite_intersection_projection_dual_update_apply]
  have hmain :
      w - (1 / L : ℝ) • u +
        (1 / L : ℝ) •
          Pp[
              polyhedral_projection_halfspace A b i,
              hC_nonempty i,
              polyhedral_projection_halfspace_isClosed A b i,
              polyhedral_projection_halfspace_convex A b i] (u - (L : ℝ) • w) =
        0 := by
    rw [hproj]
    exact hcancel
  simpa [u, w] using hmain

/-- The first extrapolated iterate satisfies `w¹ = y¹`. -/
theorem polyhedral_projection_second_fdpg_w_one
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    (hC_nonempty : ∀ i, (polyhedral_projection_halfspace A b i).Nonempty)
    (d : EuclideanSpace ℝ (Fin n))
    (L : DualBasedProximalGradientDualStepsizeParameter
      (dual_block_duplication (EuclideanSpace ℝ (Fin n)) p) 1)
    (y0 : Fin p → EuclideanSpace ℝ (Fin n)) :
    polyhedral_projection_second_fdpg_w A b hC_nonempty d L y0 1 =
      polyhedral_projection_second_fdpg_y A b hC_nonempty d L y0 1 := by
  simpa [polyhedral_projection_second_fdpg_w, polyhedral_projection_second_fdpg_y] using
    finite_intersection_fdpg_w_one
      (polyhedral_projection_halfspace A b)
      hC_nonempty
      (polyhedral_projection_halfspace_isClosed A b)
      (polyhedral_projection_halfspace_convex A b)
      L d y0

/-- For every `k`, the later extrapolated iterates satisfy the shifted textbook recursion
`w^(k+2) = y^(k+2) + (((t_(k+1) - 1) / t_(k+2)) • (y^(k+2) - y^(k+1)))`. -/
theorem polyhedral_projection_second_fdpg_w_succ_succ
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    (hC_nonempty : ∀ i, (polyhedral_projection_halfspace A b i).Nonempty)
    (d : EuclideanSpace ℝ (Fin n))
    (L : DualBasedProximalGradientDualStepsizeParameter
      (dual_block_duplication (EuclideanSpace ℝ (Fin n)) p) 1)
    (y0 : Fin p → EuclideanSpace ℝ (Fin n))
    (k : ℕ) :
    polyhedral_projection_second_fdpg_w A b hC_nonempty d L y0 (k + 2) =
      polyhedral_projection_second_fdpg_y A b hC_nonempty d L y0 (k + 2) +
        ((fista_momentum_sequence (k + 1) - 1) / fista_momentum_sequence (k + 2)) •
          (polyhedral_projection_second_fdpg_y A b hC_nonempty d L y0 (k + 2) -
            polyhedral_projection_second_fdpg_y A b hC_nonempty d L y0 (k + 1)) := by
  simpa [polyhedral_projection_second_fdpg_w, polyhedral_projection_second_fdpg_y] using
    finite_intersection_fdpg_w_succ_succ
      (polyhedral_projection_halfspace A b)
      hC_nonempty
      (polyhedral_projection_halfspace_isClosed A b)
      (polyhedral_projection_halfspace_convex A b)
      L d y0 k

end

end
