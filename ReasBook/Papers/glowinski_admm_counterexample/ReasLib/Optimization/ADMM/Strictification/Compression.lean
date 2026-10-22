/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.StrictProjectionCycle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM.ProjectionCycle

universe u v
variable {N : ℕ} {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Strict support is invariant under an injective inner-product preserving map. -/
theorem strictNonselfSupports_map_iff (L : E →ₗᵢ[ℝ] F) (p n : ZMod N → E) :
    StrictNonselfSupports (fun i ↦ L (p i)) (fun i ↦ L (n i)) ↔
      StrictNonselfSupports p n := by
  simp only [StrictNonselfSupports, ← map_sub, LinearIsometry.inner_map_map]

/-- Mapping the input families maps each of the derived cycle vectors. -/
theorem cycleVectors_map (L : E →ₗ[ℝ] F) (γ : ℝ) (η ν : ZMod N → E) (i : ZMod N) :
    residual γ (fun j ↦ L (ν j)) i = L (residual γ ν i) ∧
    xVertex γ (fun j ↦ L (η j)) (fun j ↦ L (ν j)) i = L (xVertex γ η ν i) ∧
    firstNormal γ (fun j ↦ L (η j)) (fun j ↦ L (ν j)) i = L (firstNormal γ η ν i) ∧
    secondNormal γ (fun j ↦ L (ν j)) i = L (secondNormal γ ν i) := by
  simp [residual, xVertex, firstNormal, secondNormal]

/-- Strict projection cycles are invariant under linear isometries. -/
theorem strictCycle_map_iff (L : E →ₗᵢ[ℝ] F) (γ : ℝ) (η ν : ZMod N → E) :
    IsStrictProjectionCycle γ (fun i ↦ L (η i)) (fun i ↦ L (ν i)) ↔
      IsStrictProjectionCycle γ η ν := by
  simp only [IsStrictProjectionCycle, StrictNonselfSupports, firstNormal, secondNormal,
    xVertex, residual, ← map_smul, ← map_sub, ← map_add, LinearIsometry.inner_map_map]

/-- Restrict an orthogonal phase shift to the span of its two finite orbits. -/
theorem symmetry_on_span (η ν : ZMod N → E)
    (hsym : HasOrthogonalCyclicSymmetry η ν) :
    let S := Submodule.span ℝ (Set.range η ∪ Set.range ν)
    HasOrthogonalCyclicSymmetry
      (fun i ↦ (⟨η i, Submodule.subset_span (Set.mem_union_left _ ⟨i, rfl⟩)⟩ : S))
      (fun i ↦ (⟨ν i, Submodule.subset_span (Set.mem_union_right _ ⟨i, rfl⟩)⟩ : S)) := by
  classical
  dsimp only
  let S := Submodule.span ℝ (Set.range η ∪ Set.range ν)
  obtain ⟨U, hU⟩ := hsym
  have hforward : ∀ x ∈ S, U x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [(hU i).1]
        exact Submodule.subset_span (Set.mem_union_left _ ⟨i + 1, rfl⟩)
      · rw [(hU i).2]
        exact Submodule.subset_span (Set.mem_union_right _ ⟨i + 1, rfl⟩)
    | zero => simp
    | add x y hx hy ihx ihy => simpa using S.add_mem ihx ihy
    | smul a x hx ih => simpa using S.smul_mem a ih
  have hbackward : ∀ x ∈ S, U.symm x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · have hu : U (η (i - 1)) = η i := by simpa using (hU (i - 1)).1
        rw [← hu, U.symm_apply_apply]
        exact Submodule.subset_span (Set.mem_union_left _ ⟨i - 1, rfl⟩)
      · have hu : U (ν (i - 1)) = ν i := by simpa using (hU (i - 1)).2
        rw [← hu, U.symm_apply_apply]
        exact Submodule.subset_span (Set.mem_union_right _ ⟨i - 1, rfl⟩)
    | zero => simp
    | add x y hx hy ihx ihy => simpa using S.add_mem ihx ihy
    | smul a x hx ih => simpa using S.smul_mem a ih
  let US : S ≃ₗᵢ[ℝ] S :=
    { toFun := fun x ↦ ⟨U x, hforward x x.property⟩
      invFun := fun x ↦ ⟨U.symm x, hbackward x x.property⟩
      left_inv := fun x ↦ Subtype.ext (U.symm_apply_apply x)
      right_inv := fun x ↦ Subtype.ext (U.apply_symm_apply x)
      map_add' := fun x y ↦ Subtype.ext (map_add U (x : E) (y : E))
      map_smul' := fun a x ↦ Subtype.ext (map_smul U a (x : E))
      norm_map' := fun x ↦ U.norm_map x }
  refine ⟨US, fun i ↦ ⟨?_, ?_⟩⟩
  · exact Subtype.ext (hU i).1
  · exact Subtype.ext (hU i).2

/-- A strict cycle can be expressed in orthonormal coordinates on its joint
span, with at most two dimensions per phase and preserved cyclic symmetry. -/
theorem strictCycle_compress (γ : ℝ) (η ν : ZMod N → E) [NeZero N]
    (hstrict : IsStrictProjectionCycle γ η ν)
    (hnonzero : ∃ i, residual γ ν i ≠ 0) :
    ∃ d : ℕ, d ≤ 2 * N ∧
      ∃ η' ν' : ZMod N → EuclideanSpace ℝ (Fin d),
        IsStrictProjectionCycle γ η' ν' ∧ (∃ i, residual γ ν' i ≠ 0) ∧
          (HasOrthogonalCyclicSymmetry η ν → HasOrthogonalCyclicSymmetry η' ν') := by
  classical
  let S := Submodule.span ℝ (Set.range η ∪ Set.range ν)
  have hfinite : Set.Finite (Set.range η ∪ Set.range ν) :=
    (Set.finite_range η).union (Set.finite_range ν)
  letI : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ hfinite
  have hrank : Module.finrank ℝ S ≤ 2 * N := by
    calc
      Module.finrank ℝ S ≤ (Set.range η ∪ Set.range ν).ncard :=
        by simpa only [S, Set.ncard_eq_toFinset_card'] using
          (finrank_span_le_card (R := ℝ) (Set.range η ∪ Set.range ν))
      _ ≤ (Set.range η).ncard + (Set.range ν).ncard := Set.ncard_union_le _ _
      _ ≤ N + N := add_le_add
        (by simpa [Set.image_univ, Nat.card_eq_fintype_card] using
          (Set.ncard_image_le (f := η) (s := Set.univ)))
        (by simpa [Set.image_univ, Nat.card_eq_fintype_card] using
          (Set.ncard_image_le (f := ν) (s := Set.univ)))
      _ = 2 * N := by omega
  let ηS : ZMod N → S := fun i ↦
    ⟨η i, Submodule.subset_span (Set.mem_union_left _ ⟨i, rfl⟩)⟩
  let νS : ZMod N → S := fun i ↦
    ⟨ν i, Submodule.subset_span (Set.mem_union_right _ ⟨i, rfl⟩)⟩
  let e : S ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ S)) :=
    (stdOrthonormalBasis ℝ S).repr
  have hS : IsStrictProjectionCycle γ ηS νS :=
    (strictCycle_map_iff S.subtypeₗᵢ γ ηS νS).mp hstrict
  refine ⟨Module.finrank ℝ S, hrank, (fun i ↦ e (ηS i)),
    (fun i ↦ e (νS i)), (strictCycle_map_iff e.toLinearIsometry γ ηS νS).mpr hS, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hnonzero
    refine ⟨i, ?_⟩
    have hmap : residual γ (fun i ↦ e (νS i)) i = e (residual γ νS i) := by
      simp [residual]
    rw [hmap]
    intro hz
    have hzero : residual γ νS i = 0 := e.injective (by simpa using hz)
    have hval := congrArg (fun x : S ↦ (x : E)) hzero
    exact hi hval
  · intro hsym
    obtain ⟨US, hUS⟩ := symmetry_on_span η ν hsym
    refine ⟨e.symm.trans (US.trans e), fun i ↦ ⟨?_, ?_⟩⟩
    · simpa only [LinearIsometryEquiv.trans_apply, e.symm_apply_apply] using
        congrArg e (hUS i).1
    · simpa only [LinearIsometryEquiv.trans_apply, e.symm_apply_apply] using
        congrArg e (hUS i).2

end ConsensusADMM.ProjectionCycle
