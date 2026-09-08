module

public import ReasLib.Analysis.Calculus.EuclideanPlaneHessian

/- Infrastructure I.1 (Euclidean gradient, Hessian, and matrix/operator bridge) (1):
vectors, symmetric matrices, self-adjoint operators, and matrix/operator conversion. -/
#check EuclideanSpace ℝ (Fin 2)
#check Matrix (Fin 2) (Fin 2) ℝ
#check Matrix.IsHermitian
#check IsSelfAdjoint
#check Matrix.toEuclideanCLM
#check Matrix.inner_toEuclideanCLM
#check EuclideanPlane.hessianMatrix
#check EuclideanPlane.toEuclideanCLM_hessianMatrix
#check EuclideanPlane.hessianMatrix_apply

/- Infrastructure I.1 (Euclidean gradient, Hessian, and matrix/operator bridge) (2):
gradients, Hessians, Fréchet derivatives, second derivatives, and symmetry. -/
#check gradient
#check fderiv
#check iteratedFDeriv
#check EuclideanPlane.hessian
#check EuclideanPlane.hessian_def
#check EuclideanPlane.hessian_apply_inner
#check EuclideanPlane.hessian_isSelfAdjoint
#check EuclideanPlane.hessianMatrix_isHermitian

/- Infrastructure I.1 (Euclidean gradient, Hessian, and matrix/operator bridge) (3):
quadratic-form Loewner bounds and determinant comparison. -/
#check Matrix.PosSemidef
#check EuclideanPlane.lowerBound_hessianMatrix_iff
#check EuclideanPlane.upperBound_hessianMatrix_iff
#check EuclideanPlane.det_hessianMatrix

/- Infrastructure I.1 (Euclidean gradient, Hessian, and matrix/operator bridge) (4):
orthogonal changes of frame for gradients and Hessians. -/
#check LinearIsometryEquiv
#check EuclideanPlane.gradient_comp_linearIsometry
#check EuclideanPlane.hessian_comp_linearIsometry
