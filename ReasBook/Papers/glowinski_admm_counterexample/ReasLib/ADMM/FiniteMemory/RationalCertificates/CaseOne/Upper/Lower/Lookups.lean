/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Upper.Lower.Data
@[expose] public section
set_option linter.style.longLine false
namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.Lower
@[simp] theorem lookupK0_0 : candidateK (0, 0) (0, 0) = (7340563 / 50000000) := rfl
@[simp] theorem lookupK0_1 : candidateK (0, 0) (0, 1) = (-63024021 / 1000000000) := rfl
@[simp] theorem lookupK0_2 : candidateK (0, 0) (1, 0) = (-2704523 / 20000000) := rfl
@[simp] theorem lookupK0_3 : candidateK (0, 0) (1, 1) = (-20722833 / 2000000000) := rfl
@[simp] theorem lookupK0_4 : candidateK (0, 0) (2, 0) = (-721129 / 200000000) := rfl
@[simp] theorem lookupK0_5 : candidateK (0, 0) (2, 1) = (146765503 / 2000000000) := rfl
@[simp] theorem lookupK1_0 : candidateK (0, 1) (0, 0) = (-63024021 / 1000000000) := rfl
@[simp] theorem lookupK1_1 : candidateK (0, 1) (0, 1) = (73420797 / 500000000) := rfl
@[simp] theorem lookupK1_2 : candidateK (0, 1) (1, 0) = (5576343 / 125000000) := rfl
@[simp] theorem lookupK1_3 : candidateK (0, 1) (1, 1) = (-66455241 / 1000000000) := rfl
@[simp] theorem lookupK1_4 : candidateK (0, 1) (2, 0) = (9252981 / 500000000) := rfl
@[simp] theorem lookupK1_5 : candidateK (0, 1) (2, 1) = (-138912917 / 2000000000) := rfl
@[simp] theorem lookupK2_0 : candidateK (1, 0) (0, 0) = (-2704523 / 20000000) := rfl
@[simp] theorem lookupK2_1 : candidateK (1, 0) (0, 1) = (5576343 / 125000000) := rfl
@[simp] theorem lookupK2_2 : candidateK (1, 0) (1, 0) = (10009669 / 50000000) := rfl
@[simp] theorem lookupK2_3 : candidateK (1, 0) (1, 1) = (21592063 / 500000000) := rfl
@[simp] theorem lookupK2_4 : candidateK (1, 0) (2, 0) = (-6542997 / 100000000) := rfl
@[simp] theorem lookupK2_5 : candidateK (1, 0) (2, 1) = (-17558243 / 200000000) := rfl
@[simp] theorem lookupK3_0 : candidateK (1, 1) (0, 0) = (-20722833 / 2000000000) := rfl
@[simp] theorem lookupK3_1 : candidateK (1, 1) (0, 1) = (-66455241 / 1000000000) := rfl
@[simp] theorem lookupK3_2 : candidateK (1, 1) (1, 0) = (21592063 / 500000000) := rfl
@[simp] theorem lookupK3_3 : candidateK (1, 1) (1, 1) = (69068547 / 1000000000) := rfl
@[simp] theorem lookupK3_4 : candidateK (1, 1) (2, 0) = (-6569989 / 200000000) := rfl
@[simp] theorem lookupK3_5 : candidateK (1, 1) (2, 1) = (-654593 / 250000000) := rfl
@[simp] theorem lookupK4_0 : candidateK (2, 0) (0, 0) = (-721129 / 200000000) := rfl
@[simp] theorem lookupK4_1 : candidateK (2, 0) (0, 1) = (9252981 / 500000000) := rfl
@[simp] theorem lookupK4_2 : candidateK (2, 0) (1, 0) = (-6542997 / 100000000) := rfl
@[simp] theorem lookupK4_3 : candidateK (2, 0) (1, 1) = (-6569989 / 200000000) := rfl
@[simp] theorem lookupK4_4 : candidateK (2, 0) (2, 0) = (6752789 / 100000000) := rfl
@[simp] theorem lookupK4_5 : candidateK (2, 0) (2, 1) = (14343983 / 1000000000) := rfl
@[simp] theorem lookupK5_0 : candidateK (2, 1) (0, 0) = (146765503 / 2000000000) := rfl
@[simp] theorem lookupK5_1 : candidateK (2, 1) (0, 1) = (-138912917 / 2000000000) := rfl
@[simp] theorem lookupK5_2 : candidateK (2, 1) (1, 0) = (-17558243 / 200000000) := rfl
@[simp] theorem lookupK5_3 : candidateK (2, 1) (1, 1) = (-654593 / 250000000) := rfl
@[simp] theorem lookupK5_4 : candidateK (2, 1) (2, 0) = (14343983 / 1000000000) := rfl
@[simp] theorem lookupK5_5 : candidateK (2, 1) (2, 1) = (36032651 / 500000000) := rfl
@[simp] theorem lookupL0_0 : candidateL (0, 0) (0, 0) = 1 := rfl
@[simp] theorem lookupL0_1 : candidateL (0, 0) (0, 1) = 0 := rfl
@[simp] theorem lookupL0_2 : candidateL (0, 0) (1, 0) = 0 := rfl
@[simp] theorem lookupL0_3 : candidateL (0, 0) (1, 1) = 0 := rfl
@[simp] theorem lookupL0_4 : candidateL (0, 0) (2, 0) = 0 := rfl
@[simp] theorem lookupL0_5 : candidateL (0, 0) (2, 1) = 0 := rfl
@[simp] theorem lookupL1_0 : candidateL (0, 1) (0, 0) = (-63024021 / 146811260) := rfl
@[simp] theorem lookupL1_1 : candidateL (0, 1) (0, 1) = 1 := rfl
@[simp] theorem lookupL1_2 : candidateL (0, 1) (1, 0) = 0 := rfl
@[simp] theorem lookupL1_3 : candidateL (0, 1) (1, 1) = 0 := rfl
@[simp] theorem lookupL1_4 : candidateL (0, 1) (2, 0) = 0 := rfl
@[simp] theorem lookupL1_5 : candidateL (0, 1) (2, 1) = 0 := rfl
@[simp] theorem lookupL2_0 : candidateL (1, 0) (0, 0) = (-13522615 / 14681126) := rfl
@[simp] theorem lookupL2_1 : candidateL (1, 0) (0, 1) = (-657712060390570 / 5861990737513333) := rfl
@[simp] theorem lookupL2_2 : candidateL (1, 0) (1, 0) = 1 := rfl
@[simp] theorem lookupL2_3 : candidateL (1, 0) (1, 1) = 0 := rfl
@[simp] theorem lookupL2_4 : candidateL (1, 0) (2, 0) = 0 := rfl
@[simp] theorem lookupL2_5 : candidateL (1, 0) (2, 1) = 0 := rfl
@[simp] theorem lookupL3_0 : candidateL (1, 1) (0, 0) = (-20722833 / 293622520) := rfl
@[simp] theorem lookupL3_1 : candidateL (1, 1) (0, 1) = (-6939597197266271 / 11723981475026666) := rfl
@[simp] theorem lookupL3_2 : candidateL (1, 1) (1, 0) = (15056546876711025375767 / 43455046123891756535382) := rfl
@[simp] theorem lookupL3_3 : candidateL (1, 1) (1, 1) = 1 := rfl
@[simp] theorem lookupL3_4 : candidateL (1, 1) (2, 0) = 0 := rfl
@[simp] theorem lookupL3_5 : candidateL (1, 1) (2, 1) = 0 := rfl
@[simp] theorem lookupL4_0 : candidateL (2, 0) (0, 0) = (-721129 / 29362252) := rfl
@[simp] theorem lookupL4_1 : candidateL (2, 0) (0, 1) = (829880450844525 / 5861990737513333) := rfl
@[simp] theorem lookupL4_2 : candidateL (2, 0) (1, 0) = (-39186468716470464018901 / 43455046123891756535382) := rfl
@[simp] theorem lookupL4_3 : candidateL (2, 0) (1, 1) = (376642860337307972932332994 / 69010960197465229778821425583) := rfl
@[simp] theorem lookupL4_4 : candidateL (2, 0) (2, 0) = 1 := rfl
@[simp] theorem lookupL4_5 : candidateL (2, 0) (2, 1) = 0 := rfl
@[simp] theorem lookupL5_0 : candidateL (2, 1) (0, 0) = (146765503 / 293622520) := rfl
@[simp] theorem lookupL5_1 : candidateL (2, 1) (0, 1) = (-11144228231897857 / 35171944425079998) := rfl
@[simp] theorem lookupL5_2 : candidateL (2, 1) (1, 0) = (-71685290481178236276101 / 217275230619458782676910) := rfl
@[simp] theorem lookupL5_3 : candidateL (2, 1) (1, 1) = (-993446872202931844432465906253 / 1518241124344235055134071362826) := rfl
@[simp] theorem lookupL5_4 : candidateL (2, 1) (2, 0) = (-32668837735110972423969503117953995 / 328227409756993221864265306855169617) := rfl
@[simp] theorem lookupL5_5 : candidateL (2, 1) (2, 1) = 1 := rfl
@[simp] theorem lookupD0 : candidateD (0, 0) = (7340563 / 50000000) := rfl
@[simp] theorem lookupD1 : candidateD (0, 1) = (17585972212539999 / 146811260000000000) := rfl
@[simp] theorem lookupD2 : candidateD (1, 0) = (21727523061945878267691 / 293099536875666650000000) := rfl
@[simp] theorem lookupD3 : candidateD (1, 1) = (759120562172117527567035681413 / 43455046123891756535382000000000) := rfl
@[simp] theorem lookupD4 : candidateD (2, 0) = (328227409756993221864265306855169617 / 69010960197465229778821425583000000000) := rfl
@[simp] theorem lookupD5 : candidateD (2, 1) = (3363640969855870099462453592343304140381047909 / 433260180879231052860830205048823894440000000000) := rfl
@[simp] theorem finMk1_0 (h : 0 < 1) : (⟨0, h⟩ : Fin 1) = 0 := rfl
@[simp] theorem finSucc1_0 : Fin.succ (0 : Fin 1) = (1 : Fin 2) := rfl
@[simp] theorem finMk2_0 (h : 0 < 2) : (⟨0, h⟩ : Fin 2) = 0 := rfl
@[simp] theorem finSucc2_0 : Fin.succ (0 : Fin 2) = (1 : Fin 3) := rfl
@[simp] theorem finMk2_1 (h : 1 < 2) : (⟨1, h⟩ : Fin 2) = 1 := rfl
@[simp] theorem finSucc2_1 : Fin.succ (1 : Fin 2) = (2 : Fin 3) := rfl
@[simp] theorem finMk3_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem finMk3_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem finMk3_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Upper.Lower
