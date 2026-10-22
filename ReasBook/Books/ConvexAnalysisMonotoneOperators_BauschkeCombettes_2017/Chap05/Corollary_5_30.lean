/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Corollary_3_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Proposition_5_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Proposition_5_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Theorem_5_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open EuclideanGeometry
open scoped InnerProductSpace Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "H_univ" => (Set.univ : Set H)

/-- The ordered composition of a finite family `T 0, ..., T (m - 1)` of self-maps. -/
private def orderedComposition : {m : ℕ} → (Fin m → H → H) → H → H
  | 0, _ => id
  | _ + 1, T => T 0 ∘ orderedComposition (fun i ↦ T i.succ)

-- Proof sketch: unfold the recursive definition of `orderedComposition` at a successor index.
/-- The ordered composition of a nonempty finite family starts with the first map. -/
private theorem orderedComposition_succ {m : ℕ} (T : Fin (m + 1) → H → H) :
    orderedComposition T = T 0 ∘ orderedComposition (fun i ↦ T i.succ) := by
  rfl

/-- The metric projector onto a nonempty closed affine subspace, viewed as a self-map of the
ambient Hilbert space. -/
noncomputable def affineProjector (C : AffineSubspace ℝ H)
    (hC_nonempty : (C : Set H).Nonempty) (hC_closed : IsClosed (C : Set H)) : H → H :=
  projectionPoint (C : Set H)
    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex)

-- Proof sketch: unfold `affineProjector`; it is defined to be the canonical metric projection onto
-- the underlying closed convex set of the affine subspace.
/-- The affine projector is the canonical metric projection onto the underlying affine set. -/
theorem affineProjector_def (C : AffineSubspace ℝ H) (hC_nonempty : (C : Set H).Nonempty)
    (hC_closed : IsClosed (C : Set H)) (x : H) :
    affineProjector C hC_nonempty hC_closed x =
      projectionPoint (C : Set H)
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex) x := by
  rfl

-- Proof sketch: a point in the intersection belongs to every member of the family, so it gives a
-- witness that each affine subspace is nonempty.
/-- A nonempty affine intersection forces each affine subspace in the family to be nonempty. -/
theorem affineSubspace_nonempty_of_iInf_nonempty {m : ℕ}
    (A : Fin (m + 1) → AffineSubspace ℝ H)
    (hFix : (((⨅ i, A i : AffineSubspace ℝ H) : AffineSubspace ℝ H) : Set H).Nonempty) :
    ∀ i, (A i : Set H).Nonempty := by
  intro i
  rcases hFix with ⟨x, hx⟩
  exact ⟨x, (AffineSubspace.mem_iInf_iff _ _).mp hx i⟩

-- Proof sketch: the underlying set of the affine infimum is the finite intersection of the closed
-- sets `(A i : Set H)`, hence it is closed.
/-- The intersection of a finite family of closed affine subspaces is closed. -/
theorem isClosed_iInf_affineSubspace {m : ℕ} (A : Fin (m + 1) → AffineSubspace ℝ H)
    (hA_closed : ∀ i, IsClosed (A i : Set H)) :
    IsClosed (((⨅ i, A i : AffineSubspace ℝ H) : AffineSubspace ℝ H) : Set H) := by
  simpa using isClosed_iInter hA_closed

/-- The cyclic projection orbit attached to a finite family of closed affine subspaces with
nonempty intersection. -/
noncomputable def affinePocsOperator {m : ℕ} (A : Fin (m + 1) → AffineSubspace ℝ H)
    (hA_closed : ∀ i, IsClosed (A i : Set H))
    (hFix : (((⨅ i, A i : AffineSubspace ℝ H) : AffineSubspace ℝ H) : Set H).Nonempty)
    : H → H :=
  orderedComposition (fun i ↦
    affineProjector (A i) (affineSubspace_nonempty_of_iInf_nonempty A hFix i) (hA_closed i))

-- Proof sketch: expand `affinePocsOperator`; it is the ordered composition of the affine
-- projectors associated with the family `A`.
/-- The affine POCS operator is the ordered composition of the individual affine projectors. -/
theorem affinePocsOperator_def {m : ℕ} (A : Fin (m + 1) → AffineSubspace ℝ H)
    (hA_closed : ∀ i, IsClosed (A i : Set H))
    (hFix : (((⨅ i, A i : AffineSubspace ℝ H) : AffineSubspace ℝ H) : Set H).Nonempty) :
    affinePocsOperator A hA_closed hFix =
      orderedComposition (fun i ↦
        affineProjector (A i) (affineSubspace_nonempty_of_iInf_nonempty A hFix i)
          (hA_closed i)) := by
  rfl

/-- The cyclic projection orbit attached to a finite family of closed affine subspaces with
nonempty intersection. -/
noncomputable abbrev affinePocsOrbit {m : ℕ} (A : Fin (m + 1) → AffineSubspace ℝ H)
    (hA_closed : ∀ i, IsClosed (A i : Set H))
    (hFix : (((⨅ i, A i : AffineSubspace ℝ H) : AffineSubspace ℝ H) : Set H).Nonempty)
    (x₀ : H) : ℕ → H :=
  fun n ↦ ((affinePocsOperator A hA_closed hFix)^[n]) x₀

-- Proof sketch: unfold `affinePocsOrbit` and use the standard iterate identity for the affine
-- POCS operator.
/-- The affine POCS orbit satisfies the recursion `x_{n+1} = P₁ ∘ ··· ∘ P_m (x_n)`. -/
theorem affinePocsOrbit_succ {m : ℕ} (A : Fin (m + 1) → AffineSubspace ℝ H)
    (hA_closed : ∀ i, IsClosed (A i : Set H))
    (hFix : (((⨅ i, A i : AffineSubspace ℝ H) : AffineSubspace ℝ H) : Set H).Nonempty)
    (x₀ : H) (n : ℕ) :
    affinePocsOrbit A hA_closed hFix x₀ (n + 1) =
      affinePocsOperator A hA_closed hFix (affinePocsOrbit A hA_closed hFix x₀ n) := by
  simp [affinePocsOrbit, Function.iterate_succ_apply']

/-- Helper for Corollary 5.30: projecting onto a closed affine subspace through a point in that
subspace is translation by that point of the star projection onto the direction space. -/
private theorem affineProjector_eq_add_starProjection_direction
    (C : AffineSubspace ℝ H) (hC_nonempty : (C : Set H).Nonempty)
    (hC_closed : IsClosed (C : Set H)) [CompleteSpace C.direction] {y : H} (hy : y ∈ C) (x : H) :
    affineProjector C hC_nonempty hC_closed x = y + C.direction.starProjection (x - y) := by
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  -- Identify the metric projector with the affine orthogonal projection before translating it.
  rw [affineProjector_def]
  rw [projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
    hC_nonempty hC_closed]
  -- Evaluate the affine orthogonal projection at the chosen base point of the affine subspace.
  calc
    (orthogonalProjection C x : H) =
        ((C.direction.orthogonalProjection (x - y) : C.direction) : H) + y := by
          simpa [vsub_eq_sub, vadd_eq_add] using
            (orthogonalProjection_apply_mem C (p := x) hy)
    _ = y + C.direction.starProjection (x - y) := by
          rw [add_comm, Submodule.coe_orthogonalProjection_apply]

/-- Helper for Corollary 5.30: the ordered composition of the star projections onto a finite
family of closed linear subspaces, packaged as a continuous linear map. -/
private noncomputable def linearPocsOperator :
    {m : ℕ} → (V : Fin m → Submodule ℝ H) → (∀ i, CompleteSpace (V i)) → H →L[ℝ] H
  | 0, _, _ => ContinuousLinearMap.id ℝ H
  | _ + 1, V, hV => by
      letI : CompleteSpace (V 0) := hV 0
      exact (V 0).starProjection.comp (linearPocsOperator (fun i ↦ V i.succ) (fun i ↦ hV i.succ))

/-- Helper for Corollary 5.30: at a successor stage, the linear POCS operator starts with the
head star projection followed by the tail composition. -/
private theorem linearPocsOperator_succ {m : ℕ} (V : Fin (m + 1) → Submodule ℝ H)
    (hV : ∀ i, CompleteSpace (V i)) :
    linearPocsOperator V hV =
      (V 0).starProjection.comp (linearPocsOperator (fun i ↦ V i.succ) (fun i ↦ hV i.succ)) := by
  rfl

/-- Helper for Corollary 5.30: each finite ordered composition of orthogonal projectors is norm
non-increasing. -/
private theorem norm_linearPocsOperator_apply_le :
    ∀ {m : ℕ} (V : Fin m → Submodule ℝ H) (hV : ∀ i, CompleteSpace (V i)) (x : H),
      ‖linearPocsOperator V hV x‖ ≤ ‖x‖
  | 0, _, _, _ => by
      simp [linearPocsOperator]
  | _ + 1, V, hV, x => by
      let tail := linearPocsOperator (fun i ↦ V i.succ) (fun i ↦ hV i.succ)
      -- The head projector is norm non-increasing, and the tail composition has the same property.
      calc
        ‖linearPocsOperator V hV x‖ = ‖(V 0).starProjection (tail x)‖ := by
          rfl
        _ ≤ ‖tail x‖ := (V 0).norm_starProjection_apply_le _
        _ ≤ ‖x‖ := norm_linearPocsOperator_apply_le _ _ _

/-- Helper for Corollary 5.30: points in the common intersection of the subspaces are fixed by the
composed linear projector. -/
private theorem linearPocsOperator_apply_eq_self_of_mem :
    ∀ {m : ℕ} (V : Fin m → Submodule ℝ H) (hV : ∀ i, CompleteSpace (V i)) {x : H},
      (∀ i, x ∈ V i) → linearPocsOperator V hV x = x
  | 0, _, _, _, _ => by
      simp [linearPocsOperator]
  | _ + 1, V, hV, x, hx => by
      -- First fix the tail composition, then use that the head projector fixes points of `V 0`.
      calc
        linearPocsOperator V hV x =
            (V 0).starProjection (linearPocsOperator (fun i ↦ V i.succ) (fun i ↦ hV i.succ) x) := by
              rfl
        _ = (V 0).starProjection x := by
              rw [linearPocsOperator_apply_eq_self_of_mem (fun i ↦ V i.succ)
                (fun i ↦ hV i.succ) fun i ↦ hx i.succ]
        _ = x := (Submodule.starProjection_eq_self_iff).2 (hx 0)

/-- Helper for Corollary 5.30: a fixed point of the composed linear projector must lie in every
subspace of the family. -/
private theorem mem_of_linearPocsOperator_eq_self :
    ∀ {m : ℕ} (V : Fin m → Submodule ℝ H) (hV : ∀ i, CompleteSpace (V i)) {x : H},
      linearPocsOperator V hV x = x → ∀ i, x ∈ V i
  | 0, _, _, _, _, i => by
      exact Fin.elim0 i
  | _ + 1, V, hV, x, hx, i => by
      let tail := linearPocsOperator (fun j ↦ V j.succ) (fun j ↦ hV j.succ)
      have htail_le : ‖tail x‖ ≤ ‖x‖ := norm_linearPocsOperator_apply_le _ _ _
      have hhead_eq :
          ‖(V 0).starProjection (tail x)‖ = ‖tail x‖ := by
        have hx_le_tail : ‖x‖ ≤ ‖tail x‖ := by
          calc
            ‖x‖ = ‖(V 0).starProjection (tail x)‖ := by
              simpa [linearPocsOperator, tail] using congrArg norm hx.symm
            _ ≤ ‖tail x‖ := (V 0).norm_starProjection_apply_le _
        have htail_eq : ‖tail x‖ = ‖x‖ := by
          exact le_antisymm htail_le hx_le_tail
        calc
          ‖(V 0).starProjection (tail x)‖ = ‖x‖ := by
            simpa [linearPocsOperator, tail] using congrArg norm hx
          _ = ‖tail x‖ := htail_eq.symm
      have hmem0 : tail x ∈ V 0 :=
        (Submodule.mem_iff_norm_starProjection (V 0) (tail x)).2 hhead_eq
      have htail_fix : tail x = x := by
        calc
          tail x = (V 0).starProjection (tail x) := by
            symm
            exact (Submodule.starProjection_eq_self_iff).2 hmem0
          _ = x := by
            simpa [linearPocsOperator, tail] using hx
      cases i using Fin.cases with
      | zero =>
          simpa [htail_fix] using hmem0
      | succ j =>
          have htail_fixed :
              linearPocsOperator (fun i ↦ V i.succ) (fun i ↦ hV i.succ) x = x := by
            simpa [tail] using htail_fix
          exact mem_of_linearPocsOperator_eq_self (fun i ↦ V i.succ) (fun i ↦ hV i.succ)
            htail_fixed j

/-- Helper for Corollary 5.30: the fixed points of the composed linear projector are exactly the
intersection of the subspaces. -/
private theorem linearPocsOperator_apply_eq_self_iff_mem_iInf {m : ℕ}
    (V : Fin (m + 1) → Submodule ℝ H) (hV : ∀ i, CompleteSpace (V i)) {x : H} :
    linearPocsOperator V hV x = x ↔ x ∈ ⨅ i, V i := by
  constructor
  · intro hx
    rw [Submodule.mem_iInf]
    exact mem_of_linearPocsOperator_eq_self V hV hx
  · intro hx
    rw [Submodule.mem_iInf] at hx
    exact linearPocsOperator_apply_eq_self_of_mem V hV hx

/-- Helper for Corollary 5.30: the direction space of a closed affine subspace is complete. -/
private theorem completeSpace_direction_of_isClosed
    (C : AffineSubspace ℝ H) (hC_closed : IsClosed (C : Set H)) :
    CompleteSpace C.direction := by
  letI : IsClosed (C.direction : Set H) := (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  infer_instance

/-- Helper for Corollary 5.30: the finite intersection of complete closed subspaces is again
complete. -/
private theorem completeSpace_iInf_submodule {m : ℕ}
    (V : Fin (m + 1) → Submodule ℝ H) (hV : ∀ i, CompleteSpace (V i)) :
    CompleteSpace (⨅ i, V i : Submodule ℝ H) := by
  have hclosed_i : ∀ i, IsClosed ((V i : Submodule ℝ H) : Set H) := by
    intro i
    exact (completeSpace_coe_iff_isComplete.mp (hV i)).isClosed
  have hclosed : IsClosed (((⨅ i, V i : Submodule ℝ H) : Set H)) := by
    simpa [Submodule.coe_iInf] using isClosed_iInter hclosed_i
  letI : IsClosed (((⨅ i, V i : Submodule ℝ H) : Set H)) := hclosed
  exact IsClosed.completeSpace_coe

/-- Helper for Corollary 5.30: translating a finite ordered composition of affine projectors by a
common point in the family converts it to the corresponding composition of star projections. -/
private theorem orderedComposition_affineProjector_sub_eq_linearPocsOperator :
    ∀ {m : ℕ} (A : Fin m → AffineSubspace ℝ H)
      (hA_nonempty : ∀ i, (A i : Set H).Nonempty) (hA_closed : ∀ i, IsClosed (A i : Set H))
      {y : H}, (∀ i, y ∈ A i) → ∀ x,
        orderedComposition (fun i ↦ affineProjector (A i) (hA_nonempty i) (hA_closed i)) x - y =
          linearPocsOperator (fun i ↦ (A i).direction)
            (fun i ↦ completeSpace_direction_of_isClosed (A i) (hA_closed i)) (x - y)
  | 0, A, hA_nonempty, hA_closed, y, hy, x => by
      -- With no factors, both compositions are the identity.
      simp [orderedComposition, linearPocsOperator]
  | _ + 1, A, hA_nonempty, hA_closed, y, hy, x => by
      letI : CompleteSpace (A 0).direction :=
        completeSpace_direction_of_isClosed (A 0) (hA_closed 0)
      -- Peel off the head affine projector and then translate the recursive tail.
      calc
        orderedComposition (fun i ↦ affineProjector (A i) (hA_nonempty i) (hA_closed i)) x - y
            =
              affineProjector (A 0) (hA_nonempty 0) (hA_closed 0)
                (orderedComposition (fun i ↦
                  affineProjector (A i.succ) (hA_nonempty i.succ) (hA_closed i.succ)) x) - y := by
              simpa [Function.comp_apply] using
                congrArg (fun f : H → H ↦ f x - y)
                  (orderedComposition_succ
                    (fun i ↦ affineProjector (A i) (hA_nonempty i) (hA_closed i)))
        _ =
              (A 0).direction.starProjection
                (orderedComposition (fun i ↦
                  affineProjector (A i.succ) (hA_nonempty i.succ) (hA_closed i.succ)) x - y) := by
              rw [affineProjector_eq_add_starProjection_direction
                (C := A 0) (hC_nonempty := hA_nonempty 0) (hC_closed := hA_closed 0) (hy := hy 0)]
              abel_nf
        _ =
              (A 0).direction.starProjection
                (linearPocsOperator (fun i ↦ (A i.succ).direction)
                  (fun i ↦ completeSpace_direction_of_isClosed (A i.succ) (hA_closed i.succ))
                  (x - y)) := by
              exact congrArg ((A 0).direction.starProjection)
                (orderedComposition_affineProjector_sub_eq_linearPocsOperator
                  (A := fun i ↦ A i.succ) (hA_nonempty := fun i ↦ hA_nonempty i.succ)
                  (hA_closed := fun i ↦ hA_closed i.succ) (y := y)
                  (fun i ↦ hy i.succ) x)
        _ =
              linearPocsOperator (fun i ↦ (A i).direction)
                (fun i ↦ completeSpace_direction_of_isClosed (A i) (hA_closed i)) (x - y) := by
              rfl

/-- Helper for Corollary 5.30: translating the affine POCS operator by a point in the common
intersection yields the corresponding linear POCS operator on the directions. -/
private theorem affinePocsOperator_sub_eq_linearPocsOperator {m : ℕ}
    (A : Fin (m + 1) → AffineSubspace ℝ H) (hA_closed : ∀ i, IsClosed (A i : Set H))
    (hFix : (((⨅ i, A i : AffineSubspace ℝ H) : AffineSubspace ℝ H) : Set H).Nonempty)
    {y : H} (hy : y ∈ ⨅ i, A i) (x : H) :
    affinePocsOperator A hA_closed hFix x - y =
      linearPocsOperator (fun i ↦ (A i).direction)
        (fun i ↦ completeSpace_direction_of_isClosed (A i) (hA_closed i)) (x - y) := by
  let hA_nonempty : ∀ i, (A i : Set H).Nonempty := affineSubspace_nonempty_of_iInf_nonempty A hFix
  -- Reduce the affine POCS operator to the translated ordered-composition identity.
  rw [affinePocsOperator_def]
  exact orderedComposition_affineProjector_sub_eq_linearPocsOperator
    A hA_nonempty hA_closed (fun i ↦ (AffineSubspace.mem_iInf_iff _ _).mp hy i) x

/-- Helper for Corollary 5.30: translating the affine POCS orbit by a common point identifies it
with the Picard orbit of the linear POCS operator on the direction spaces. -/
private theorem affinePocsOrbit_sub_eq_linearPocsOperator_iterate {m : ℕ}
    (A : Fin (m + 1) → AffineSubspace ℝ H) (hA_closed : ∀ i, IsClosed (A i : Set H))
    (hFix : (((⨅ i, A i : AffineSubspace ℝ H) : AffineSubspace ℝ H) : Set H).Nonempty)
    {y : H} (hy : y ∈ ⨅ i, A i) (x₀ : H) :
    ∀ n,
      affinePocsOrbit A hA_closed hFix x₀ n - y =
        ((linearPocsOperator (fun i ↦ (A i).direction)
          (fun i ↦ completeSpace_direction_of_isClosed (A i) (hA_closed i)))^[n]) (x₀ - y)
  | 0 => by
      -- The initial translated orbit is the initial translated point.
      simp [affinePocsOrbit]
  | n + 1 => by
      -- Rewrite one affine step, then replace it by the corresponding linear step.
      calc
        affinePocsOrbit A hA_closed hFix x₀ (n + 1) - y =
            affinePocsOperator A hA_closed hFix (affinePocsOrbit A hA_closed hFix x₀ n) - y := by
              rw [affinePocsOrbit_succ]
        _ =
            linearPocsOperator (fun i ↦ (A i).direction)
              (fun i ↦ completeSpace_direction_of_isClosed (A i) (hA_closed i))
              (affinePocsOrbit A hA_closed hFix x₀ n - y) := by
              rw [affinePocsOperator_sub_eq_linearPocsOperator A hA_closed hFix hy]
        _ =
            linearPocsOperator (fun i ↦ (A i).direction)
              (fun i ↦ completeSpace_direction_of_isClosed (A i) (hA_closed i))
              (((linearPocsOperator (fun i ↦ (A i).direction)
                (fun i ↦ completeSpace_direction_of_isClosed (A i) (hA_closed i)))^[n])
                (x₀ - y)) := by
              rw [affinePocsOrbit_sub_eq_linearPocsOperator_iterate A hA_closed hFix hy x₀ n]
        _ =
            ((linearPocsOperator (fun i ↦ (A i).direction)
              (fun i ↦ completeSpace_direction_of_isClosed (A i) (hA_closed i)))^[n + 1])
              (x₀ - y) := by
              rw [Function.iterate_succ_apply']

/-- Helper for Corollary 5.30: lifting a finite family of ambient self-maps to `Set.univ`
preserves their ambient values after coercion. -/
private noncomputable def liftUnivFamily {m : ℕ} (T : Fin m → H → H) :
    Fin m → H_univ → H_univ :=
  fun i x ↦ ⟨T i (x : H), Set.mem_univ _⟩

/-- Helper for Corollary 5.30: coercing the lifted universal family recovers the original ambient
self-map. -/
@[simp] private theorem liftUnivFamily_coe {m : ℕ} (T : Fin m → H → H) (i : Fin m)
    (x : H_univ) :
    ((liftUnivFamily T i x : H_univ) : H) = T i (x : H) :=
  rfl

/-- Helper for Corollary 5.30: the finite composition of a lifted family on `Set.univ` evaluates
to the ambient finite composition after coercion. -/
@[simp] private theorem finiteComposition_liftUnivFamily_coe :
    ∀ {m : ℕ} (T : Fin m → H → H) (x : H_univ),
      ((finiteComposition (liftUnivFamily T) x : H_univ) : H) = finiteComposition T (x : H)
  | 0, T, x => rfl
  | _ + 1, T, x => by
      -- Unfold the head-tail composition and recurse on the tail family.
      rw [finiteComposition_succ, finiteComposition_succ]
      simp only [Function.comp_apply, liftUnivFamily_coe]
      exact congrArg (T 0)
        (finiteComposition_liftUnivFamily_coe (T := fun i ↦ T i.succ) (x := x))

/-- Helper for Corollary 5.30: iterating the lifted finite composition on `Set.univ` matches the
ambient iterate after coercion. -/
@[simp] private theorem iterate_finiteComposition_liftUnivFamily_coe {m : ℕ}
    (T : Fin m → H → H) (x : H_univ) :
    ∀ n, ((((finiteComposition (liftUnivFamily T))^[n]) x : H_univ) : H) =
      ((finiteComposition T)^[n]) (x : H)
  | 0 => rfl
  | n + 1 => by
      -- Push one more iterate through the coercion and then invoke the induction hypothesis.
      simp [Function.iterate_succ_apply', iterate_finiteComposition_liftUnivFamily_coe]

/-- Helper for Corollary 5.30: the reflected squared-norm gap expands to four times the firm
nonexpansiveness defect. -/
private lemma reflection_norm_gap_eq_four_mul (a b : H) :
    ‖a‖ ^ 2 - ‖(2 : ℝ) • b - a‖ ^ 2 = 4 * (inner ℝ a b - ‖b‖ ^ 2) := by
  have htwo : (2 : ℝ) • b = b + b := by
    simpa using (two_smul ℝ b)
  rw [htwo]
  have hsub : ‖a‖ ^ 2 - ‖(b + b) - a‖ ^ 2 = 2 * inner ℝ (b + b) a - ‖b + b‖ ^ 2 := by
    -- Expand the reflected square by the standard Hilbert-space norm identity.
    nlinarith [norm_sub_sq_real (b + b) a]
  have hnorm : ‖b + b‖ ^ 2 = 4 * ‖b‖ ^ 2 := by
    -- The doubled vector contributes exactly four copies of `‖b‖²`.
    rw [norm_add_sq_real, real_inner_self_eq_norm_sq]
    ring
  -- Reassemble the expansion and commute the real inner product once.
  rw [hsub, hnorm, inner_add_left, real_inner_comm b a]
  ring

/-- Helper for Corollary 5.30: each star projection is `1 / 2`-averaged on the whole-space
subtype `Set.univ`. -/
private theorem starProjection_averagedWith_half_on_univ (V : Submodule ℝ H) [CompleteSpace V] :
    AveragedWith (1 / 2 : ℝ) (fun x : H_univ ↦ (V.starProjection x : H)) := by
  let P : H_univ → H := fun x ↦ (V.starProjection x : H)
  let R : H_univ → H := fun x ↦ (2 : ℝ) • P x - (x : H)
  refine averagedWith_iff.mpr ?_
  refine ⟨by norm_num, R, ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    let a : H := (x : H) - y
    let b : H := P x - P y
    have hb : b = V.starProjection a := by
      simp [P, a, b, map_sub]
    have hfirm :
        ‖b‖ ^ 2 ≤ inner ℝ a b := by
      have hproj :
          ‖V.orthogonalProjection a‖ ^ 2 = ⟪V.starProjection a, a⟫_ℝ := by
        simpa using
          (Submodule.re_inner_starProjection_eq_normSq (K := V) (v := a)).symm
      simpa [hb, a, real_inner_comm] using hproj.le
    have hsq :
        ‖(2 : ℝ) • b - a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
      nlinarith [reflection_norm_gap_eq_four_mul a b, hfirm]
    have hreflect : R x - R y = (2 : ℝ) • b - a := by
      dsimp [R, P, a, b]
      rw [sub_eq_add_neg, sub_eq_add_neg, smul_sub]
      abel_nf
    have hdist : ‖R x - R y‖ ≤ ‖a‖ := by
      rw [hreflect]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
    simpa [Subtype.dist_eq, dist_eq_norm, one_mul, a] using hdist
  · funext x
    dsimp [R, P]
    have hhalf_eq : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
      norm_num
    calc
      V.starProjection x = (1 / 2 : ℝ) • ((2 : ℝ) • V.starProjection x) := by
              rw [smul_smul]
              norm_num
      _ = (1 / 2 : ℝ) • (x : H) +
            ((1 / 2 : ℝ) • ((2 : ℝ) • V.starProjection x) - (1 / 2 : ℝ) • (x : H)) := by
            abel_nf
      _ = (1 - (1 / 2 : ℝ)) • (x : H) + (1 / 2 : ℝ) • R x := by
            rw [hhalf_eq, smul_sub]

/-- Helper for Corollary 5.30: the linear POCS operator is the ordered finite composition of the
individual star projections. -/
@[simp] private theorem linearPocsOperator_eq_finiteComposition_starProjection :
    ∀ {m : ℕ} (V : Fin m → Submodule ℝ H) (hV : ∀ i, CompleteSpace (V i)),
      (linearPocsOperator V hV : H → H) = finiteComposition (fun i ↦ (V i).starProjection)
  | 0, V, hV => by
      funext x
      rfl
  | _ + 1, V, hV => by
      funext x
      -- Unfold the head-tail composition on both sides and recurse on the tail family.
      simp [linearPocsOperator_succ, finiteComposition_succ,
        linearPocsOperator_eq_finiteComposition_starProjection
          (V := fun i ↦ V i.succ) (hV := fun i ↦ hV i.succ), Function.comp_apply]

/-- Helper for Corollary 5.30: the linear POCS operator is nonexpansive, with Lipschitz constant
`1`. -/
private theorem linearPocsOperator_lipschitzWith_one {m : ℕ}
    (V : Fin (m + 1) → Submodule ℝ H) (hV : ∀ i, CompleteSpace (V i)) :
    LipschitzWith 1 (linearPocsOperator V hV) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  -- Apply the norm contraction estimate to the difference `x - y`.
  simpa [dist_eq_norm, one_mul, map_sub] using
    norm_linearPocsOperator_apply_le V hV (x - y)

/-- Helper for Corollary 5.30: the Picard iteration is the relaxed iteration with constant
relaxation parameter `1`. -/
private theorem relaxedOperatorIteration_one_eq_iterate (T : H → H) (x₀ : H) :
    relaxedOperatorIteration (fun _ ↦ T) (fun _ ↦ (1 : ℝ)) x₀ = fun n ↦ (T^[n]) x₀ := by
  funext n
  induction n with
  | zero =>
      simp [relaxedOperatorIteration]
  | succ n ihn =>
      -- With relaxation `1`, one relaxed step is exactly one Picard step.
      rw [relaxedOperatorIteration_succ, ihn, Function.iterate_succ_apply']
      simp

/-- Helper for Corollary 5.30: the linear POCS operator is averaged on `Set.univ`. -/
private theorem linearPocsOperator_averagedWith_on_univ {m : ℕ}
    (V : Fin (m + 1) → Submodule ℝ H) (hV : ∀ i, CompleteSpace (V i)) :
    ∃ α : ℝ, AveragedWith α (fun x : H_univ ↦ (linearPocsOperator V hV x : H)) := by
  let U : Fin (m + 1) → H_univ → H_univ := liftUnivFamily (fun i ↦ (V i).starProjection)
  have hU : ∀ i : Fin (m + 1), AveragedWith (1 / 2 : ℝ) (fun x : H_univ ↦ (U i x : H)) := by
    intro i
    simpa [U] using starProjection_averagedWith_half_on_univ (V i)
  cases m with
  | zero =>
      refine ⟨1 / 2, ?_⟩
      simpa [U, linearPocsOperator_eq_finiteComposition_starProjection, finiteComposition] using hU 0
  | succ n =>
      refine ⟨1 / (1 + (∑ i : Fin (n + 2), ((1 / 2 : ℝ) / (1 - 1 / 2)))⁻¹), ?_⟩
      have hcomp :
          AveragedWith
            (1 / (1 + (∑ i : Fin (n + 2), ((1 / 2 : ℝ) / (1 - 1 / 2)))⁻¹) : ℝ)
            (fun x : H_univ ↦ ((finiteComposition U x : H_univ) : H)) := by
        simpa using
          averagedWith_compose_fin (D := H_univ) (m := n + 2)
            (by omega) (by simpa using (Set.univ_nonempty : (Set.univ : Set H).Nonempty))
            (fun _ ↦ (1 / 2 : ℝ)) U hU
      -- Rewrite the finite composition of lifted star projections back to the ambient linear POCS
      -- operator.
      simpa [U, linearPocsOperator_eq_finiteComposition_starProjection]
        using hcomp

/-- Helper for Corollary 5.30: the Picard residuals of the linear POCS operator converge strongly
to `0`. -/
private theorem linearPocsOperator_residual_tendsto_zero {m : ℕ}
    (V : Fin (m + 1) → Submodule ℝ H) (hV : ∀ i, CompleteSpace (V i)) (x₀ : H) :
    Tendsto
      (fun n ↦ ((linearPocsOperator V hV)^[n]) x₀ - ((linearPocsOperator V hV)^[n + 1]) x₀)
      atTop (𝓝 (0 : H)) := by
  let Tlin : H → H := linearPocsOperator V hV
  rcases linearPocsOperator_averagedWith_on_univ V hV with ⟨α, hαavg⟩
  have hα : α ∈ Set.Ioo (0 : ℝ) 1 := AveragedWith.mem_Ioo hαavg
  have hlam : ∀ n : ℕ, (1 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / α) := by
    intro n
    constructor
    · norm_num
    · have hupper : (1 : ℝ) ≤ 1 / α := by
        have hinv : (1 : ℝ)⁻¹ ≤ α⁻¹ := by
          exact (inv_le_inv₀ zero_lt_one hα.1).2 (le_of_lt hα.2)
        simpa [one_div] using hinv
      simpa using hupper
  have hFix : (Function.fixedPoints Tlin).Nonempty := by
    refine ⟨0, ?_⟩
    rw [Function.mem_fixedPoints_iff]
    simpa [Tlin] using (linearPocsOperator V hV).map_zero
  have hdiv :
      Tendsto
        (fun N ↦ Finset.sum (Finset.range N) (fun n ↦ (1 : ℝ) * (1 - α * (1 : ℝ))))
        atTop atTop := by
    have hpos : 0 < 1 - α := by
      linarith [hα.2]
    convert tendsto_natCast_atTop_atTop.const_mul_atTop hpos using 1
    ext N
    simp
    ring
  have hres :
      Tendsto
        (fun n ↦
          Tlin (relaxedOperatorIteration (fun _ ↦ Tlin) (fun _ ↦ (1 : ℝ)) x₀ n) -
            relaxedOperatorIteration (fun _ ↦ Tlin) (fun _ ↦ (1 : ℝ)) x₀ n)
        atTop (𝓝 (0 : H)) := by
    exact residual_tendsto_zero_of_relaxedOperatorIteration_of_averagedWith
      (T := Tlin) (α := α) (hT := hαavg) (lam := fun _ ↦ (1 : ℝ)) (hlam := hlam) hFix hdiv x₀
  -- Rewrite the relaxed iteration with constant weight `1` as the Picard iterates of `Tlin`.
  simpa [Tlin, relaxedOperatorIteration_one_eq_iterate, Function.iterate_succ_apply',
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hres.neg

/-- Helper for Corollary 5.30: the fixed-point subspace of a continuous linear endomorphism. -/
private abbrev fixedSubspace (T : H →L[ℝ] H) : Submodule ℝ H :=
  (T - ContinuousLinearMap.id ℝ H).ker

/-- Helper for Corollary 5.30: membership in `fixedSubspace T` is exactly the fixed-point
equation `T x = x`. -/
private theorem mem_fixedSubspace_iff {T : H →L[ℝ] H} {x : H} :
    x ∈ fixedSubspace T ↔ T x = x := by
  -- Unfold the kernel description and rewrite `(T - id) x = 0`.
  constructor
  · intro hx
    have hx' : (T - ContinuousLinearMap.id ℝ H) x = 0 := hx
    exact sub_eq_zero.mp hx'
  · intro hx
    change (T - ContinuousLinearMap.id ℝ H) x = 0
    exact sub_eq_zero.mpr hx

/-- Helper for Corollary 5.30: the ambient linear map `T` lifts to a self-map of `Set.univ`. -/
private def liftUnivMap (T : H →L[ℝ] H) : H_univ → H_univ :=
  fun x ↦ ⟨T x, Set.mem_univ _⟩

/-- Helper for Corollary 5.30: coercing the lifted universal self-map recovers the ambient linear
map. -/
private theorem liftUnivMap_coe {T : H →L[ℝ] H} (x : H_univ) :
    ((liftUnivMap T x : H_univ) : H) = T (x : H) :=
  rfl

attribute [simp] liftUnivMap_coe

/-- Helper for Corollary 5.30: the lifted Picard orbit on `Set.univ` has ambient value
`(T^[n]) x₀`. -/
private theorem lift_univ_iterate_coe {T : H →L[ℝ] H} (x₀ : H) :
    ∀ n : ℕ,
      ((((liftUnivMap T)^[n]) ⟨x₀, Set.mem_univ _⟩ : H_univ) : H) = (T^[n]) x₀
  | 0 => rfl
  | n + 1 => by
      -- Push one iterate through the coercion before invoking the induction hypothesis.
      rw [Function.iterate_succ_apply', liftUnivMap_coe, lift_univ_iterate_coe,
        Function.iterate_succ_apply']

/-- Helper for Corollary 5.30: the affine subspace underlying `fixedSubspace T` is nonempty. -/
private instance fixedSubspace_toAffineSubspace_nonempty (T : H →L[ℝ] H) :
    Nonempty (fixedSubspace T).toAffineSubspace := by
  refine ⟨⟨0, ?_⟩⟩
  exact (Submodule.mem_toAffineSubspace).2 (by simp [fixedSubspace])

/-- Helper for Corollary 5.30: the affine subspace underlying `fixedSubspace T` has the canonical
orthogonal projection. -/
private instance fixedSubspace_toAffineSubspace_hasOrthogonalProjection (T : H →L[ℝ] H) :
    (fixedSubspace T).toAffineSubspace.direction.HasOrthogonalProjection := by
  rw [Submodule.toAffineSubspace_direction]
  infer_instance

/-- Helper for Corollary 5.30: the fixed-point subspace of a continuous linear endomorphism is
closed. -/
private theorem fixedSubspace_isClosed (T : H →L[ℝ] H) :
    IsClosed ((fixedSubspace T : Submodule ℝ H) : Set H) := by
  -- The fixed-point subspace is the kernel of the continuous linear map `T - id`.
  simpa [fixedSubspace] using (T - ContinuousLinearMap.id ℝ H).isClosed_ker

/-- Helper for Corollary 5.30: on the affine subspace associated with `fixedSubspace T`, the
metric projection agrees with `starProjection`. -/
private theorem projectionPoint_toAffineSubspace_eq_starProjection {T : H →L[ℝ] H}
    (h_nonempty : (((fixedSubspace T).toAffineSubspace : AffineSubspace ℝ H) : Set H).Nonempty)
    (h_closed : IsClosed ((((fixedSubspace T).toAffineSubspace : AffineSubspace ℝ H) : Set H)))
    (x : H) :
    projectionPoint
        (((fixedSubspace T).toAffineSubspace : AffineSubspace ℝ H) : Set H)
        (isChebyshev_of_nonempty_isClosed_convex h_nonempty h_closed
          ((fixedSubspace T).toAffineSubspace).convex) x =
      (fixedSubspace T).starProjection x := by
  -- Identify the metric projector with the affine orthogonal projection and then with the
  -- orthogonal projection onto the linear fixed-point subspace.
  calc
    projectionPoint
        (((fixedSubspace T).toAffineSubspace : AffineSubspace ℝ H) : Set H)
        (isChebyshev_of_nonempty_isClosed_convex h_nonempty h_closed
          ((fixedSubspace T).toAffineSubspace).convex) x =
      (orthogonalProjection ((fixedSubspace T).toAffineSubspace) x : H) := by
        rw [projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
          h_nonempty h_closed]
    _ = (fixedSubspace T).starProjection x := by
        refine (coe_orthogonalProjection_eq_iff_mem).2 ?_
        constructor
        · exact (Submodule.mem_toAffineSubspace).2
            ((fixedSubspace T).starProjection_apply_mem x)
        · rw [Submodule.toAffineSubspace_direction]
          exact (fixedSubspace T).sub_starProjection_mem_orthogonal x

/-- Helper for Corollary 5.30: the Picard orbit of a nonexpansive linear map is Fejér monotone
with respect to its fixed-point subspace. -/
private theorem picard_fejerMonotone_fixedSubspace {T : H →L[ℝ] H}
    (hT : LipschitzWith 1 T) (x₀ : H) :
    FejerMonotone ((fixedSubspace T : Submodule ℝ H) : Set H) (fun n ↦ (T^[n]) x₀) := by
  intro z hz n
  have hz_fix : T z = z := (mem_fixedSubspace_iff).mp hz
  -- Compare the next iterate to the fixed point `z` using nonexpansiveness.
  have hdist :
      dist (T ((T^[n]) x₀)) (T z) ≤ dist ((T^[n]) x₀) z := by
    simpa [one_mul] using hT.dist_le_mul ((T^[n]) x₀) z
  simpa [hz_fix, Function.iterate_succ_apply'] using hdist

/-- Helper for Corollary 5.30: Fejér monotonicity makes every projection shadow onto
`fixedSubspace T` equal to the initial one. -/
private theorem starProjection_eq_initial_of_fejerMonotone_fixedSubspace {T : H →L[ℝ] H}
    (x : ℕ → H) (hfejer : FejerMonotone ((fixedSubspace T : Submodule ℝ H) : Set H) x) (n : ℕ) :
    (fixedSubspace T).starProjection (x n) = (fixedSubspace T).starProjection (x 0) := by
  let C : AffineSubspace ℝ H := (fixedSubspace T).toAffineSubspace
  have hC_nonempty : (C : Set H).Nonempty := by
    exact ⟨0, (Submodule.mem_toAffineSubspace).2 (by simp [fixedSubspace])⟩
  have hC_closed : IsClosed (C : Set H) := by
    simpa [C, Submodule.mem_toAffineSubspace] using fixedSubspace_isClosed T
  have hfejer_aff : FejerMonotone (C : Set H) x := by
    simpa [C, Submodule.mem_toAffineSubspace] using hfejer
  -- Apply Proposition 5.9 to the affine subspace associated with the fixed-point subspace.
  calc
    (fixedSubspace T).starProjection (x n) =
        projectionPoint (C : Set H)
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex) (x n) := by
            symm
            exact projectionPoint_toAffineSubspace_eq_starProjection hC_nonempty hC_closed (x n)
    _ =
        projectionPoint (C : Set H)
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex) (x 0) :=
        projectionPoint_eq_initial_of_fejerMonotone_affineSubspace
          hC_nonempty hC_closed x hfejer_aff n
    _ = (fixedSubspace T).starProjection (x 0) :=
        projectionPoint_toAffineSubspace_eq_starProjection hC_nonempty hC_closed (x 0)

/-- Helper for Corollary 5.30: residual decay for a nonexpansive linear map upgrades to strong
convergence onto the orthogonal projection of the initial point onto its fixed-point subspace. -/
private theorem tendsto_iterates_to_starProjection_fixedSubspace_iff_tendsto_residual_zero_of_nonexpansive
    {T : H →L[ℝ] H} (hT : LipschitzWith 1 T) (x₀ : H) :
    Tendsto (fun n ↦ (T^[n]) x₀) atTop (𝓝 ((fixedSubspace T).starProjection x₀)) ↔
      Tendsto (fun n ↦ (T^[n]) x₀ - (T^[n + 1]) x₀) atTop (𝓝 (0 : H)) := by
  constructor
  · intro hlim
    have hshift :
        Tendsto (fun n ↦ (T^[n + 1]) x₀) atTop (𝓝 ((fixedSubspace T).starProjection x₀)) := by
      -- A convergent orbit keeps the same limit after shifting the index.
      simpa [Nat.add_comm] using hlim.comp (tendsto_add_atTop_nat 1)
    -- Subtract the shifted orbit from the original one and simplify the limit.
    simpa using hlim.sub hshift
  · intro hres
    -- Route correction: avoid the unavailable imported Proposition 5.28 object by rebuilding its
    -- fixed-subspace convergence bridge locally from Theorem 5.14 and Proposition 5.9.
    let x₀u : (Set.univ : Set H) := ⟨x₀, Set.mem_univ _⟩
    have hfejer :
        FejerMonotone ((fixedSubspace T : Submodule ℝ H) : Set H) (fun n ↦ (T^[n]) x₀) :=
      picard_fejerMonotone_fixedSubspace hT x₀
    have hLift : LipschitzWith 1 (liftUnivMap T) := by
      intro x y
      -- The lifted map has the same nonexpansive estimate as the ambient map.
      simpa [one_mul] using hT.edist_le_mul x y
    have hres_univ :
        Tendsto
          (fun n ↦
            ((((liftUnivMap T)^[n]) x₀u : (Set.univ : Set H)) : H) -
              (liftUnivMap T (((liftUnivMap T)^[n]) x₀u) : H))
          atTop (𝓝 (0 : H)) := by
      -- Rewrite the lifted residual sequence back to the ambient Picard residuals.
      simpa [x₀u, Function.iterate_succ_apply', lift_univ_iterate_coe] using hres
    rcases
        tendsto_iterates_to_fixedPoint_of_residual_tendsto_zero_of_nonexpansive_of_symmetric_of_odd
          (D := (Set.univ : Set H)) isClosed_univ convex_univ
          (T := liftUnivMap T) hLift x₀u hres_univ
          (by
            intro x hx
            simp)
          (by
            intro x
            change T (-(x : H)) = -(T (x : H))
            exact T.map_neg (x : H)) with
      ⟨z, hz_fix, hzlim⟩
    have hz_mem : (z : H) ∈ fixedSubspace T := by
      -- The fixed point returned by Theorem 5.14 belongs to the ambient fixed-point subspace.
      apply (mem_fixedSubspace_iff).mpr
      rw [Function.mem_fixedPoints_iff] at hz_fix
      exact congrArg Subtype.val hz_fix
    have hzlim' : Tendsto (fun n ↦ (T^[n]) x₀) atTop (𝓝 (z : H)) := by
      -- Coerce the lifted strong convergence statement back to the ambient Picard orbit.
      simpa [x₀u, lift_univ_iterate_coe] using hzlim
    have hproj_tendsto :
        Tendsto (fun n ↦ (fixedSubspace T).starProjection ((T^[n]) x₀)) atTop
          (𝓝 ((fixedSubspace T).starProjection (z : H))) := by
      -- Pass the strong convergence through the continuous orthogonal projector.
      exact ((fixedSubspace T).starProjection.continuous.tendsto (z : H)).comp hzlim'
    have hproj_eventually :
        (fun n ↦ (fixedSubspace T).starProjection ((T^[n]) x₀)) =ᶠ[atTop]
          fun _ : ℕ ↦ (fixedSubspace T).starProjection x₀ := by
      -- Fejér monotonicity forces every projection shadow to equal the initial shadow.
      exact Filter.Eventually.of_forall fun n ↦
        starProjection_eq_initial_of_fejerMonotone_fixedSubspace
          (x := fun k ↦ (T^[k]) x₀) hfejer n
    have hproj_eq :
        (fixedSubspace T).starProjection (z : H) = (fixedSubspace T).starProjection x₀ :=
      tendsto_nhds_unique_of_eventuallyEq hproj_tendsto tendsto_const_nhds hproj_eventually
    have hz_eq :
        (z : H) = (fixedSubspace T).starProjection x₀ := by
      -- Because `z` already lies in the fixed-point subspace, the projection fixes it.
      simpa [((fixedSubspace T).starProjection_eq_self_iff).2 hz_mem] using hproj_eq
    -- Replace the strong limit `z` by the identified orthogonal projection of the initial point.
    simpa [hz_eq] using hzlim'

/-- Helper for Corollary 5.30: the Picard orbit of the linear POCS operator converges strongly to
the star projection onto the common intersection of the subspaces. -/
private theorem tendsto_linearPocsOrbit_to_starProjection_iInf {m : ℕ}
    (V : Fin (m + 1) → Submodule ℝ H) (hV : ∀ i, CompleteSpace (V i))
    [CompleteSpace (⨅ i, V i : Submodule ℝ H)] (x₀ : H) :
    Tendsto (fun n ↦ ((linearPocsOperator V hV)^[n]) x₀) atTop
      (𝓝 (((⨅ i, V i : Submodule ℝ H)).starProjection x₀)) := by
  have hT : LipschitzWith 1 (linearPocsOperator V hV) :=
    linearPocsOperator_lipschitzWith_one V hV
  have hres :
      Tendsto
        (fun n ↦ ((linearPocsOperator V hV)^[n]) x₀ - ((linearPocsOperator V hV)^[n + 1]) x₀)
        atTop (𝓝 (0 : H)) :=
    linearPocsOperator_residual_tendsto_zero V hV x₀
  have hfixed :
      fixedSubspace (linearPocsOperator V hV) = (⨅ i, V i : Submodule ℝ H) := by
    ext x
    rw [mem_fixedSubspace_iff, linearPocsOperator_apply_eq_self_iff_mem_iInf]
  -- Proposition 5.28 upgrades residual decay to strong convergence onto the fixed-point subspace.
  have hconv :
      Tendsto (fun n ↦ ((linearPocsOperator V hV)^[n]) x₀) atTop
        (𝓝 ((fixedSubspace (linearPocsOperator V hV)).starProjection x₀)) := by
    exact
      (tendsto_iterates_to_starProjection_fixedSubspace_iff_tendsto_residual_zero_of_nonexpansive
        (T := linearPocsOperator V hV) hT x₀).2 hres
  simpa [hfixed] using hconv

-- Proof sketch: translate the family by a point in the common intersection to reduce to closed
-- linear subspaces, use the oddness-based asymptotic regularity from the finite averaged-operator
-- theory, and then apply the strong convergence criterion for Fejér-monotone sequences relative to
-- a closed affine subspace to identify the limit as the metric projection onto the intersection.
/-- Corollary 5.30: (von Neumann--Halperin) for a finite family of closed affine subspaces of a
real Hilbert space with nonempty intersection, the cyclic projection orbit converges strongly to
the metric projection of the initial point onto the intersection. -/
theorem tendsto_affinePocsOrbit_to_affineProjector_iInf {m : ℕ}
    (A : Fin (m + 1) → AffineSubspace ℝ H) (hA_closed : ∀ i, IsClosed (A i : Set H))
    (hFix : (((⨅ i, A i : AffineSubspace ℝ H) : AffineSubspace ℝ H) : Set H).Nonempty)
    (x₀ : H) :
    Tendsto (affinePocsOrbit A hA_closed hFix x₀) atTop
      (𝓝
        (affineProjector (⨅ i, A i) hFix (isClosed_iInf_affineSubspace A hA_closed) x₀)) := by
  have hFix_nonempty := hFix
  rcases hFix with ⟨y, hy⟩
  let V : Fin (m + 1) → Submodule ℝ H := fun i ↦ (A i).direction
  let hV : ∀ i, CompleteSpace (V i) := fun i ↦
    completeSpace_direction_of_isClosed (A i) (hA_closed i)
  letI : CompleteSpace (⨅ i, V i : Submodule ℝ H) := completeSpace_iInf_submodule V hV
  have hy_iInf : y ∈ ⨅ i, A i := hy
  have horbit_sub :
      ∀ n,
        affinePocsOrbit A hA_closed hFix_nonempty x₀ n - y =
          ((linearPocsOperator V hV)^[n]) (x₀ - y) := by
    simpa [V, hV] using
      affinePocsOrbit_sub_eq_linearPocsOperator_iterate
        (A := A) (hA_closed := hA_closed) (hFix := hFix_nonempty) (hy := hy_iInf) (x₀ := x₀)
  have hlin :
      Tendsto (fun n ↦ ((linearPocsOperator V hV)^[n]) (x₀ - y)) atTop
        (𝓝 (((⨅ i, V i : Submodule ℝ H)).starProjection (x₀ - y))) := by
    simpa [V, hV] using tendsto_linearPocsOrbit_to_starProjection_iInf V hV (x₀ - y)
  have horbit :
      affinePocsOrbit A hA_closed hFix_nonempty x₀ =
        fun n ↦ y + ((linearPocsOperator V hV)^[n]) (x₀ - y) := by
    funext n
    have hn := horbit_sub n
    rw [sub_eq_iff_eq_add] at hn
    simpa [add_comm, add_left_comm, add_assoc] using hn
  have htranslated :
      Tendsto (fun n ↦ y + ((linearPocsOperator V hV)^[n]) (x₀ - y)) atTop
        (𝓝 (y + (((⨅ i, V i : Submodule ℝ H)).starProjection (x₀ - y)))) := by
    exact ((continuous_const.add continuous_id).tendsto _).comp hlin
  have hdirection :
      (⨅ i, A i : AffineSubspace ℝ H).direction = (⨅ i, V i : Submodule ℝ H) := by
    simpa [V] using AffineSubspace.direction_iInf_of_mem_iInf A y hy_iInf
  have hlimit :
      affineProjector (⨅ i, A i) hFix_nonempty (isClosed_iInf_affineSubspace A hA_closed) x₀ =
        y + (((⨅ i, V i : Submodule ℝ H)).starProjection (x₀ - y)) := by
    letI : CompleteSpace ((⨅ i, A i : AffineSubspace ℝ H).direction) :=
      completeSpace_direction_of_isClosed (⨅ i, A i) (isClosed_iInf_affineSubspace A hA_closed)
    -- Translate the metric projector on the affine intersection back to the star projection on
    -- its direction space, then identify that direction with the intersection of the directions.
    calc
      affineProjector (⨅ i, A i) hFix_nonempty (isClosed_iInf_affineSubspace A hA_closed) x₀ =
          y + ((⨅ i, A i : AffineSubspace ℝ H).direction).starProjection (x₀ - y) := by
            exact affineProjector_eq_add_starProjection_direction
              (C := ⨅ i, A i) (hC_nonempty := hFix_nonempty)
              (hC_closed := isClosed_iInf_affineSubspace A hA_closed) (hy := hy_iInf) x₀
      _ = y + (((⨅ i, V i : Submodule ℝ H)).starProjection (x₀ - y)) := by
            simpa [hdirection]
  -- The affine orbit is exactly the translated linear orbit, so its strong limit is the affine
  -- projector onto the common intersection.
  simpa [horbit, hlimit] using htranslated

end
