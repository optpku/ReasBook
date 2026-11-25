/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.ChebyshevCache

@[expose] public section

set_option maxRecDepth 8192
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.Data

def chebyshevRow0 : List ℤ := [1]

def chebyshevRow1 : List ℤ := [0, 1]

def chebyshevRow2 : List ℤ := [(-1), 0, 2]

def chebyshevRow3 : List ℤ := [0, (-3), 0, 4]

def chebyshevRow4 : List ℤ := [1, 0, (-8), 0, 8]

def chebyshevRow5 : List ℤ := [0, 5, 0, (-20), 0, 16]

def chebyshevRow6 : List ℤ := [(-1), 0, 18, 0, (-48), 0, 32]

def chebyshevRow7 : List ℤ := [0, (-7), 0, 56, 0, (-112), 0, 64]

def chebyshevRow8 : List ℤ := [1, 0, (-32), 0, 160, 0, (-256), 0, 128]

def chebyshevRow9 : List ℤ := [0, 9, 0, (-120), 0, 432, 0, (-576), 0, 256]

def chebyshevRow10 : List ℤ := [(-1), 0, 50, 0, (-400), 0, 1120, 0, (-1280), 0, 512]

def chebyshevRow11 : List ℤ := [0, (-11), 0, 220, 0, (-1232), 0, 2816, 0, (-2816), 0, 1024]

def chebyshevRow12 : List ℤ := [1, 0, (-72), 0, 840, 0, (-3584), 0, 6912, 0, (-6144), 0, 2048]

def chebyshevRow13 : List ℤ := [0, 13, 0, (-364), 0, 2912, 0, (-9984), 0, 16640, 0, (-13312), 0, 4096]

def chebyshevRow14 : List ℤ := [(-1), 0, 98, 0, (-1568), 0, 9408, 0, (-26880), 0, 39424, 0, (-28672), 0, 8192]

def chebyshevRow15 : List ℤ := [0, (-15), 0, 560, 0, (-6048), 0, 28800, 0, (-70400), 0, 92160, 0, (-61440), 0, 16384]

end ADMM.UnitCircle.LowerCertificate.Data
