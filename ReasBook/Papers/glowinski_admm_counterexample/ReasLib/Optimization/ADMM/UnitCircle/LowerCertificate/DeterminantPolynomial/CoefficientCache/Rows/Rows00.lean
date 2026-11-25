/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.CoefficientTree
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Context

@[expose] public section

set_option maxRecDepth 8192
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.CoefficientCache

def row0Part00 : LookupTree ℤ := (.leaf (1))

def row0 : CoefficientRow := ⟨1, row0Part00⟩

theorem row0_represents : RowRepresents row0 Data.chebyshevRow0 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row1Part00 : LookupTree ℤ := (.node 1 (.leaf (0)) (.leaf (1)))

def row1 : CoefficientRow := ⟨2, row1Part00⟩

theorem row1_represents : RowRepresents row1 Data.chebyshevRow1 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row2Part00 : LookupTree ℤ := (.node 1 (.leaf (-1)) (.node 1 (.leaf (0)) (.leaf (2))))

def row2 : CoefficientRow := ⟨3, row2Part00⟩

theorem row2_represents : RowRepresents row2 Data.chebyshevRow2 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row3Part00 : LookupTree ℤ := (.node 2 (.node 1 (.leaf (0)) (.leaf (-3))) (.node 1 (.leaf (0)) (.leaf (4))))

def row3 : CoefficientRow := ⟨4, row3Part00⟩

theorem row3_represents : RowRepresents row3 Data.chebyshevRow3 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row4Part00 : LookupTree ℤ := (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-8)) (.node 1 (.leaf (0)) (.leaf (8)))))

def row4 : CoefficientRow := ⟨5, row4Part00⟩

theorem row4_represents : RowRepresents row4 Data.chebyshevRow4 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row5Part00 : LookupTree ℤ := (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (5)) (.leaf (0)))) (.node 1 (.leaf (-20)) (.node 1 (.leaf (0)) (.leaf (16)))))

def row5 : CoefficientRow := ⟨6, row5Part00⟩

theorem row5_represents : RowRepresents row5 Data.chebyshevRow5 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row6Part00 : LookupTree ℤ := (.node 3 (.node 1 (.leaf (-1)) (.node 1 (.leaf (0)) (.leaf (18)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-48))) (.node 1 (.leaf (0)) (.leaf (32)))))

def row6 : CoefficientRow := ⟨7, row6Part00⟩

theorem row6_represents : RowRepresents row6 Data.chebyshevRow6 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row7Part00 : LookupTree ℤ := (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-7))) (.node 1 (.leaf (0)) (.leaf (56)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-112))) (.node 1 (.leaf (0)) (.leaf (64)))))

def row7 : CoefficientRow := ⟨8, row7Part00⟩

theorem row7_represents : RowRepresents row7 Data.chebyshevRow7 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row8Part00 : LookupTree ℤ := (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-32)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (160)) (.leaf (0))) (.node 1 (.leaf (-256)) (.node 1 (.leaf (0)) (.leaf (128))))))

def row8 : CoefficientRow := ⟨9, row8Part00⟩

theorem row8_represents : RowRepresents row8 Data.chebyshevRow8 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row9Part00 : LookupTree ℤ := (.node 5 (.node 2 (.node 1 (.leaf (0)) (.leaf (9))) (.node 1 (.leaf (0)) (.node 1 (.leaf (-120)) (.leaf (0))))) (.node 2 (.node 1 (.leaf (432)) (.leaf (0))) (.node 1 (.leaf (-576)) (.node 1 (.leaf (0)) (.leaf (256))))))

def row9 : CoefficientRow := ⟨10, row9Part00⟩

theorem row9_represents : RowRepresents row9 Data.chebyshevRow9 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row10Part00 : LookupTree ℤ := (.node 5 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (50)) (.node 1 (.leaf (0)) (.leaf (-400))))) (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (1120)) (.leaf (0)))) (.node 1 (.leaf (-1280)) (.node 1 (.leaf (0)) (.leaf (512))))))

def row10 : CoefficientRow := ⟨11, row10Part00⟩

theorem row10_represents : RowRepresents row10 Data.chebyshevRow10 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row11Part00 : LookupTree ℤ := (.node 6 (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (-11)) (.leaf (0)))) (.node 1 (.leaf (220)) (.node 1 (.leaf (0)) (.leaf (-1232))))) (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (2816)) (.leaf (0)))) (.node 1 (.leaf (-2816)) (.node 1 (.leaf (0)) (.leaf (1024))))))

def row11 : CoefficientRow := ⟨12, row11Part00⟩

theorem row11_represents : RowRepresents row11 Data.chebyshevRow11 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row12Part00 : LookupTree ℤ := (.node 6 (.node 3 (.node 1 (.leaf (1)) (.node 1 (.leaf (0)) (.leaf (-72)))) (.node 1 (.leaf (0)) (.node 1 (.leaf (840)) (.leaf (0))))) (.node 3 (.node 1 (.leaf (-3584)) (.node 1 (.leaf (0)) (.leaf (6912)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-6144))) (.node 1 (.leaf (0)) (.leaf (2048))))))

def row12 : CoefficientRow := ⟨13, row12Part00⟩

theorem row12_represents : RowRepresents row12 Data.chebyshevRow12 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row13Part00 : LookupTree ℤ := (.node 7 (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (13)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-364)) (.leaf (0))) (.node 1 (.leaf (2912)) (.leaf (0))))) (.node 3 (.node 1 (.leaf (-9984)) (.node 1 (.leaf (0)) (.leaf (16640)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-13312))) (.node 1 (.leaf (0)) (.leaf (4096))))))

def row13 : CoefficientRow := ⟨14, row13Part00⟩

theorem row13_represents : RowRepresents row13 Data.chebyshevRow13 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row14Part00 : LookupTree ℤ := (.node 7 (.node 3 (.node 1 (.leaf (-1)) (.node 1 (.leaf (0)) (.leaf (98)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1568))) (.node 1 (.leaf (0)) (.leaf (9408))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-26880))) (.node 1 (.leaf (0)) (.leaf (39424)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-28672))) (.node 1 (.leaf (0)) (.leaf (8192))))))

def row14 : CoefficientRow := ⟨15, row14Part00⟩

theorem row14_represents : RowRepresents row14 Data.chebyshevRow14 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row15Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-15))) (.node 1 (.leaf (0)) (.leaf (560)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-6048))) (.node 1 (.leaf (0)) (.leaf (28800))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-70400))) (.node 1 (.leaf (0)) (.leaf (92160)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-61440))) (.node 1 (.leaf (0)) (.leaf (16384))))))

def row15 : CoefficientRow := ⟨16, row15Part00⟩

theorem row15_represents : RowRepresents row15 Data.chebyshevRow15 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.CoefficientCache
