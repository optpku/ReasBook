/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Lower.Descent.Data
@[expose] public section
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.Descent
@[simp] theorem lookupK0_0 : candidateK (0, 0) (0, 0) = (3982533 / 100000000) := rfl
@[simp] theorem lookupK0_1 : candidateK (0, 0) (0, 1) = (3241839 / 100000000) := rfl
@[simp] theorem lookupK0_2 : candidateK (0, 0) (1, 0) = (-1942941 / 50000000) := rfl
@[simp] theorem lookupK0_3 : candidateK (0, 0) (1, 1) = (-1404877 / 50000000) := rfl
@[simp] theorem lookupK0_4 : candidateK (0, 0) (2, 0) = (-4161301 / 100000000) := rfl
@[simp] theorem lookupK0_5 : candidateK (0, 0) (2, 1) = (-386551 / 10000000) := rfl
@[simp] theorem lookupK1_0 : candidateK (0, 1) (0, 0) = (3241839 / 100000000) := rfl
@[simp] theorem lookupK1_1 : candidateK (0, 1) (0, 1) = (3810657 / 100000000) := rfl
@[simp] theorem lookupK1_2 : candidateK (0, 1) (1, 0) = (-2391359 / 100000000) := rfl
@[simp] theorem lookupK1_3 : candidateK (0, 1) (1, 1) = (-1851241 / 50000000) := rfl
@[simp] theorem lookupK1_4 : candidateK (0, 1) (2, 0) = (-491513 / 10000000) := rfl
@[simp] theorem lookupK1_5 : candidateK (0, 1) (2, 1) = (-4427 / 125000) := rfl
@[simp] theorem lookupK2_0 : candidateK (1, 0) (0, 0) = (-1942941 / 50000000) := rfl
@[simp] theorem lookupK2_1 : candidateK (1, 0) (0, 1) = (-2391359 / 100000000) := rfl
@[simp] theorem lookupK2_2 : candidateK (1, 0) (1, 0) = (5558923 / 100000000) := rfl
@[simp] theorem lookupK2_3 : candidateK (1, 0) (1, 1) = (76013 / 4000000) := rfl
@[simp] theorem lookupK2_4 : candidateK (1, 0) (2, 0) = (273729 / 50000000) := rfl
@[simp] theorem lookupK2_5 : candidateK (1, 0) (2, 1) = (874281 / 25000000) := rfl
@[simp] theorem lookupK3_0 : candidateK (1, 1) (0, 0) = (-1404877 / 50000000) := rfl
@[simp] theorem lookupK3_1 : candidateK (1, 1) (0, 1) = (-1851241 / 50000000) := rfl
@[simp] theorem lookupK3_2 : candidateK (1, 1) (1, 0) = (76013 / 4000000) := rfl
@[simp] theorem lookupK3_3 : candidateK (1, 1) (1, 1) = (21571 / 500000) := rfl
@[simp] theorem lookupK3_4 : candidateK (1, 1) (2, 0) = (4611849 / 100000000) := rfl
@[simp] theorem lookupK3_5 : candidateK (1, 1) (2, 1) = (1093091 / 50000000) := rfl
@[simp] theorem lookupK4_0 : candidateK (2, 0) (0, 0) = (-4161301 / 100000000) := rfl
@[simp] theorem lookupK4_1 : candidateK (2, 0) (0, 1) = (-491513 / 10000000) := rfl
@[simp] theorem lookupK4_2 : candidateK (2, 0) (1, 0) = (273729 / 50000000) := rfl
@[simp] theorem lookupK4_3 : candidateK (2, 0) (1, 1) = (4611849 / 100000000) := rfl
@[simp] theorem lookupK4_4 : candidateK (2, 0) (2, 0) = (11338169 / 100000000) := rfl
@[simp] theorem lookupK4_5 : candidateK (2, 0) (2, 1) = (4626251 / 100000000) := rfl
@[simp] theorem lookupK5_0 : candidateK (2, 1) (0, 0) = (-386551 / 10000000) := rfl
@[simp] theorem lookupK5_1 : candidateK (2, 1) (0, 1) = (-4427 / 125000) := rfl
@[simp] theorem lookupK5_2 : candidateK (2, 1) (1, 0) = (874281 / 25000000) := rfl
@[simp] theorem lookupK5_3 : candidateK (2, 1) (1, 1) = (1093091 / 50000000) := rfl
@[simp] theorem lookupK5_4 : candidateK (2, 1) (2, 0) = (4626251 / 100000000) := rfl
@[simp] theorem lookupK5_5 : candidateK (2, 1) (2, 1) = (6671593 / 100000000) := rfl
@[simp] theorem lookupL0_0 : candidateL (0, 0) (0, 0) = 1 := rfl
@[simp] theorem lookupL0_1 : candidateL (0, 0) (0, 1) = 0 := rfl
@[simp] theorem lookupL0_2 : candidateL (0, 0) (1, 0) = 0 := rfl
@[simp] theorem lookupL0_3 : candidateL (0, 0) (1, 1) = 0 := rfl
@[simp] theorem lookupL0_4 : candidateL (0, 0) (2, 0) = 0 := rfl
@[simp] theorem lookupL0_5 : candidateL (0, 0) (2, 1) = 0 := rfl
@[simp] theorem lookupL1_0 : candidateL (0, 1) (0, 0) = (1080613 / 1327511) := rfl
@[simp] theorem lookupL1_1 : candidateL (0, 1) (0, 1) = 1 := rfl
@[simp] theorem lookupL1_2 : candidateL (0, 1) (1, 0) = 0 := rfl
@[simp] theorem lookupL1_3 : candidateL (0, 1) (1, 1) = 0 := rfl
@[simp] theorem lookupL1_4 : candidateL (0, 1) (2, 0) = 0 := rfl
@[simp] theorem lookupL1_5 : candidateL (0, 1) (2, 1) = 0 := rfl
@[simp] theorem lookupL2_0 : candidateL (1, 0) (0, 0) = (-1295294 / 1327511) := rfl
@[simp] theorem lookupL2_1 : candidateL (1, 0) (0, 1) = (1024579228217 / 1555515717420) := rfl
@[simp] theorem lookupL2_2 : candidateL (1, 0) (1, 0) = 1 := rfl
@[simp] theorem lookupL2_3 : candidateL (1, 0) (1, 1) = 0 := rfl
@[simp] theorem lookupL2_4 : candidateL (1, 0) (2, 0) = 0 := rfl
@[simp] theorem lookupL2_5 : candidateL (1, 0) (2, 1) = 0 := rfl
@[simp] theorem lookupL3_0 : candidateL (1, 1) (0, 0) = (-2809754 / 3982533) := rfl
@[simp] theorem lookupL3_1 : candidateL (1, 1) (0, 1) = (-93941444155 / 77775785871) := rfl
@[simp] theorem lookupL3_2 : candidateL (1, 1) (1, 0) = (141527149978958480 / 1958360045461650301) := rfl
@[simp] theorem lookupL3_3 : candidateL (1, 1) (1, 1) = 1 := rfl
@[simp] theorem lookupL3_4 : candidateL (1, 1) (2, 0) = 0 := rfl
@[simp] theorem lookupL3_5 : candidateL (1, 1) (2, 1) = 0 := rfl
@[simp] theorem lookupL4_0 : candidateL (2, 0) (0, 0) = (-4161301 / 3982533) := rfl
@[simp] theorem lookupL4_1 : candidateL (2, 0) (0, 1) = (-676044394639 / 518505239140) := rfl
@[simp] theorem lookupL4_2 : candidateL (2, 0) (1, 0) = (-3898976154335161821 / 1958360045461650301) := rfl
@[simp] theorem lookupL4_3 : candidateL (2, 0) (1, 1) = (17326649157141831981575 / 904493942631276149014996) := rfl
@[simp] theorem lookupL4_4 : candidateL (2, 0) (2, 0) = 1 := rfl
@[simp] theorem lookupL4_5 : candidateL (2, 0) (2, 1) = 0 := rfl
@[simp] theorem lookupL5_0 : candidateL (2, 1) (0, 0) = (-3865510 / 3982533) := rfl
@[simp] theorem lookupL5_1 : candidateL (2, 1) (0, 1) = (-52439259997 / 155551571742) := rfl
@[simp] theorem lookupL5_2 : candidateL (2, 1) (1, 0) = (-22377053694484130 / 1958360045461650301) := rfl
@[simp] theorem lookupL5_3 : candidateL (2, 1) (1, 1) = (-1493877740660299527370171 / 904493942631276149014996) := rfl
@[simp] theorem lookupL5_4 : candidateL (2, 1) (2, 0) = (1425239014621759655886088789 / 169672809748432952560313382) := rfl
@[simp] theorem lookupL5_5 : candidateL (2, 1) (2, 1) = 1 := rfl
@[simp] theorem lookupD0 : candidateD (0, 0) = (3982533 / 100000000) := rfl
@[simp] theorem lookupD1 : candidateD (0, 1) = (77775785871 / 6637555000000) := rfl
@[simp] theorem lookupD2 : candidateD (1, 0) = (1958360045461650301 / 155551571742000000000) := rfl
@[simp] theorem lookupD3 : candidateD (1, 1) = (226123485657819037253749 / 36719250852405943143750000) := rfl
@[simp] theorem lookupD4 : candidateD (2, 0) = (84836404874216476280156691 / 1130617428289095186268745000000) := rfl
@[simp] theorem lookupD5 : candidateD (2, 1) = (9790856746765097002909144645901 / 1696728097484329525603133820000000) := rfl
@[simp] theorem finMk1_0 (h : 0 < 1) : (⟨0, h⟩ : Fin 1) = 0 := rfl
@[simp] theorem finSucc1_0 : Fin.succ (0 : Fin 1) = (1 : Fin 2) := rfl
@[simp] theorem finMk2_0 (h : 0 < 2) : (⟨0, h⟩ : Fin 2) = 0 := rfl
@[simp] theorem finSucc2_0 : Fin.succ (0 : Fin 2) = (1 : Fin 3) := rfl
@[simp] theorem finMk2_1 (h : 1 < 2) : (⟨1, h⟩ : Fin 2) = 1 := rfl
@[simp] theorem finSucc2_1 : Fin.succ (1 : Fin 2) = (2 : Fin 3) := rfl
@[simp] theorem finMk3_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem finMk3_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem finMk3_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.Descent
