/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalReconstruction

@[expose] public section

/- Definition 8.1.1 (1): exact rational cases store the common coefficients,
lag tables, packed interpolation weights, endpoint parameters, and packed endpoint blocks. -/
#check ADMM.FiniteMemory.Reconstruction.RationalCase
#check ADMM.FiniteMemory.Reconstruction.RationalCase.ofNumerators

/- Definition 8.1.1 (2): the packed interpolation data reconstruct all weights,
including zero diagonals and the omitted origin column satisfying value balance. -/
#check ADMM.FiniteMemory.Reconstruction.reconstructMu
#check ADMM.FiniteMemory.Reconstruction.reconstructMu_diag
#check ADMM.FiniteMemory.Reconstruction.reconstructMu_balance

/- Definition 8.1.1 (3): exact supply matrices and endpoint principal blocks determine
the completed storage matrices through their action on constant histories. -/
#check ADMM.FiniteMemory.Reconstruction.supplyMatrix
#check ADMM.FiniteMemory.Reconstruction.supplyMatrix_quadratic
#check ADMM.FiniteMemory.Reconstruction.storageMatrix
#check ADMM.FiniteMemory.Reconstruction.storageMatrix_mul_constantModes

/- Definition 8.1.1 (4): the exact descent and lower matrices are checked by the
displayed unpivoted `LDLᵀ` recurrence and its strict rational pivot bounds. -/
#check ADMM.FiniteMemory.Reconstruction.descentMatrix
#check ADMM.FiniteMemory.Reconstruction.descentMatrix_quadratic
#check ADMM.FiniteMemory.Reconstruction.lowerMatrix
#check ADMM.FiniteMemory.Reconstruction.lowerMatrix_quadratic
#check ADMM.FiniteMemory.Reconstruction.ldl
#check ADMM.FiniteMemory.Reconstruction.PositivePivots
#check ADMM.FiniteMemory.Reconstruction.ldl_unitDiagonal
#check ADMM.FiniteMemory.Reconstruction.ldl_pivot
#check ADMM.FiniteMemory.Reconstruction.ldl_lower
#check ADMM.FiniteMemory.Reconstruction.ldl_factorization
#check ADMM.FiniteMemory.Reconstruction.posSemidef_of_positivePivots
#check ADMM.FiniteMemory.Reconstruction.posSemidef_of_kernel_and_principalPivots

/- Definition 8.1.1 (5): valid endpoint checks produce canonical finite-memory
certificates throughout the closed interval by affine interpolation of `P`. -/
#check ADMM.FiniteMemory.Reconstruction.Valid
#check ADMM.FiniteMemory.Reconstruction.cast_descentMatrix
#check ADMM.FiniteMemory.Reconstruction.cast_lowerMatrix
#check ADMM.FiniteMemory.Reconstruction.endpointDescent_posSemidef
#check ADMM.FiniteMemory.Reconstruction.endpointLower_posSemidef
#check ADMM.FiniteMemory.Reconstruction.intervalDescentMatrix_eq_affine
#check ADMM.FiniteMemory.Reconstruction.intervalLowerMatrix_eq_affine
#check ADMM.FiniteMemory.Reconstruction.intervalDescent_posSemidef
#check ADMM.FiniteMemory.Reconstruction.intervalLower_posSemidef
#check ADMM.FiniteMemory.Reconstruction.toEndpointCertificate
#check ADMM.FiniteMemory.Reconstruction.toIntervalCertificate
