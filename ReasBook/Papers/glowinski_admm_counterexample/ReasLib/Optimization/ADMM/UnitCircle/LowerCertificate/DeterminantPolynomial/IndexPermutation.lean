/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Representation
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Perm.Subperm

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

theorem mem_pairedIndices_of_bounds (n : ℕ) (j : ℤ)
    (hj : -(n : ℤ) ≤ j ∧ j ≤ n) : j ∈ pairedIndices n := by
  by_cases hzero : j = 0
  · simp [hzero, pairedIndices]
  · by_cases hpos : 0 < j
    · let k : Fin n := ⟨j.toNat - 1, by omega⟩
      have hk : (k.val + 1 : ℤ) = j := by dsimp [k]; omega
      apply List.mem_cons_of_mem 0
      apply List.mem_flatten.mpr
      refine ⟨[(k.val + 1 : ℤ), -(k.val + 1 : ℤ)],
        List.mem_ofFn.mpr ⟨k, rfl⟩, ?_⟩
      simp [hk]
    · let k : Fin n := ⟨(-j).toNat - 1, by omega⟩
      have hk : -(k.val + 1 : ℤ) = j := by dsimp [k]; omega
      apply List.mem_cons_of_mem 0
      apply List.mem_flatten.mpr
      refine ⟨[(k.val + 1 : ℤ), -(k.val + 1 : ℤ)],
        List.mem_ofFn.mpr ⟨k, rfl⟩, ?_⟩
      simp [hk]

/-- Regrouping a finite symmetric integer window is a combinatorial identity,
so no large permutation search is needed in each source certificate. -/
theorem window_indices_perm_paired (n : ℕ) :
    (windowIndices n).Perm (pairedIndices n) := by
  have hnodup : (windowIndices n).Nodup := by
    unfold windowIndices
    apply List.nodup_ofFn_ofInjective
    intro i j hij
    apply Fin.ext
    change (i.val : ℤ) - n = (j.val : ℤ) - n at hij
    omega
  have hsub : windowIndices n ⊆ pairedIndices n := by
    intro j hj
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hj
    apply mem_pairedIndices_of_bounds
    have hib := i.isLt
    constructor <;> omega
  have hlen : (pairedIndices n).length = 2 * n + 1 := by
    simp [pairedIndices, List.length_flatten, List.map_ofFn, List.sum_ofFn]
    omega
  apply (hnodup.subperm hsub).perm_of_length_le
  rw [hlen]
  simpa only [windowIndices, List.length_ofFn] using (le_refl (2 * n + 1))

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
