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

def row16Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-128)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (2688)) (.leaf (0))) (.node 1 (.leaf (-21504)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (84480)) (.leaf (0))) (.node 1 (.leaf (-180224)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (212992)) (.leaf (0))) (.node 1 (.leaf (-131072)) (.leaf (0))))))

def row16Part01 : LookupTree ℤ := (.leaf (32768))

def row16 : CoefficientRow := ⟨17, (.node 16 row16Part00 row16Part01)⟩

theorem row16_represents : RowRepresents row16 Data.chebyshevRow16 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row17Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (17))) (.node 1 (.leaf (0)) (.leaf (-816)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (11424))) (.node 1 (.leaf (0)) (.leaf (-71808))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (239360))) (.node 1 (.leaf (0)) (.leaf (-452608)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (487424))) (.node 1 (.leaf (0)) (.leaf (-278528))))))

def row17Part01 : LookupTree ℤ := (.node 1 (.leaf (0)) (.leaf (65536)))

def row17 : CoefficientRow := ⟨18, (.node 16 row17Part00 row17Part01)⟩

theorem row17_represents : RowRepresents row17 Data.chebyshevRow17 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row18Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (162)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-4320)) (.leaf (0))) (.node 1 (.leaf (44352)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-228096)) (.leaf (0))) (.node 1 (.leaf (658944)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1118208)) (.leaf (0))) (.node 1 (.leaf (1105920)) (.leaf (0))))))

def row18Part01 : LookupTree ℤ := (.node 1 (.leaf (-589824)) (.node 1 (.leaf (0)) (.leaf (131072))))

def row18 : CoefficientRow := ⟨19, (.node 16 row18Part00 row18Part01)⟩

theorem row18_represents : RowRepresents row18 Data.chebyshevRow18 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row19Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-19))) (.node 1 (.leaf (0)) (.leaf (1140)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-20064))) (.node 1 (.leaf (0)) (.leaf (160512))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-695552))) (.node 1 (.leaf (0)) (.leaf (1770496)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2723840))) (.node 1 (.leaf (0)) (.leaf (2490368))))))

def row19Part01 : LookupTree ℤ := (.node 2 (.node 1 (.leaf (0)) (.leaf (-1245184))) (.node 1 (.leaf (0)) (.leaf (262144))))

def row19 : CoefficientRow := ⟨20, (.node 16 row19Part00 row19Part01)⟩

theorem row19_represents : RowRepresents row19 Data.chebyshevRow19 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row20Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-200)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (6600)) (.leaf (0))) (.node 1 (.leaf (-84480)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (549120)) (.leaf (0))) (.node 1 (.leaf (-2050048)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (4659200)) (.leaf (0))) (.node 1 (.leaf (-6553600)) (.leaf (0))))))

def row20Part01 : LookupTree ℤ := (.node 2 (.node 1 (.leaf (5570560)) (.leaf (0))) (.node 1 (.leaf (-2621440)) (.node 1 (.leaf (0)) (.leaf (524288)))))

def row20 : CoefficientRow := ⟨21, (.node 16 row20Part00 row20Part01)⟩

theorem row20_represents : RowRepresents row20 Data.chebyshevRow20 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row21Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (21))) (.node 1 (.leaf (0)) (.leaf (-1540)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (33264))) (.node 1 (.leaf (0)) (.leaf (-329472))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (1793792))) (.node 1 (.leaf (0)) (.leaf (-5870592)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (12042240))) (.node 1 (.leaf (0)) (.leaf (-15597568))))))

def row21Part01 : LookupTree ℤ := (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (12386304)) (.leaf (0)))) (.node 1 (.leaf (-5505024)) (.node 1 (.leaf (0)) (.leaf (1048576)))))

def row21 : CoefficientRow := ⟨22, (.node 16 row21Part00 row21Part01)⟩

theorem row21_represents : RowRepresents row21 Data.chebyshevRow21 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row22Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (242)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-9680)) (.leaf (0))) (.node 1 (.leaf (151008)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-1208064)) (.leaf (0))) (.node 1 (.leaf (5637632)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-16400384)) (.leaf (0))) (.node 1 (.leaf (30638080)) (.leaf (0))))))

def row22Part01 : LookupTree ℤ := (.node 3 (.node 1 (.leaf (-36765696)) (.node 1 (.leaf (0)) (.leaf (27394048)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-11534336))) (.node 1 (.leaf (0)) (.leaf (2097152)))))

def row22 : CoefficientRow := ⟨23, (.node 16 row22Part00 row22Part01)⟩

theorem row22_represents : RowRepresents row22 Data.chebyshevRow22 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row23Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-23))) (.node 1 (.leaf (0)) (.leaf (2024)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-52624))) (.node 1 (.leaf (0)) (.leaf (631488))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-4209920))) (.node 1 (.leaf (0)) (.leaf (17145856)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-44843008))) (.node 1 (.leaf (0)) (.leaf (76873728))))))

def row23Part01 : LookupTree ℤ := (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-85917696))) (.node 1 (.leaf (0)) (.leaf (60293120)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-24117248))) (.node 1 (.leaf (0)) (.leaf (4194304)))))

def row23 : CoefficientRow := ⟨24, (.node 16 row23Part00 row23Part01)⟩

theorem row23_represents : RowRepresents row23 Data.chebyshevRow23 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row24Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-288)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (13728)) (.leaf (0))) (.node 1 (.leaf (-256256)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (2471040)) (.leaf (0))) (.node 1 (.leaf (-14057472)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (50692096)) (.leaf (0))) (.node 1 (.leaf (-120324096)) (.leaf (0))))))

def row24Part01 : LookupTree ℤ := (.node 4 (.node 2 (.node 1 (.leaf (190513152)) (.leaf (0))) (.node 1 (.leaf (-199229440)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (132120576)) (.leaf (0))) (.node 1 (.leaf (-50331648)) (.node 1 (.leaf (0)) (.leaf (8388608))))))

def row24 : CoefficientRow := ⟨25, (.node 16 row24Part00 row24Part01)⟩

theorem row24_represents : RowRepresents row24 Data.chebyshevRow24 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row25Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (25))) (.node 1 (.leaf (0)) (.leaf (-2600)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (80080))) (.node 1 (.leaf (0)) (.leaf (-1144000))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (9152000))) (.node 1 (.leaf (0)) (.leaf (-45260800)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (146227200))) (.node 1 (.leaf (0)) (.leaf (-317521920))))))

def row25Part01 : LookupTree ℤ := (.node 5 (.node 2 (.node 1 (.leaf (0)) (.leaf (466944000))) (.node 1 (.leaf (0)) (.node 1 (.leaf (-458752000)) (.leaf (0))))) (.node 2 (.node 1 (.leaf (288358400)) (.leaf (0))) (.node 1 (.leaf (-104857600)) (.node 1 (.leaf (0)) (.leaf (16777216))))))

def row25 : CoefficientRow := ⟨26, (.node 16 row25Part00 row25Part01)⟩

theorem row25_represents : RowRepresents row25 Data.chebyshevRow25 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row26Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (338)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-18928)) (.leaf (0))) (.node 1 (.leaf (416416)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-4759040)) (.leaf (0))) (.node 1 (.leaf (32361472)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-141213696)) (.leaf (0))) (.node 1 (.leaf (412778496)) (.leaf (0))))))

def row26Part01 : LookupTree ℤ := (.node 5 (.node 2 (.node 1 (.leaf (-825556992)) (.leaf (0))) (.node 1 (.leaf (1133117440)) (.node 1 (.leaf (0)) (.leaf (-1049624576))))) (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (627048448)) (.leaf (0)))) (.node 1 (.leaf (-218103808)) (.node 1 (.leaf (0)) (.leaf (33554432))))))

def row26 : CoefficientRow := ⟨27, (.node 16 row26Part00 row26Part01)⟩

theorem row26_represents : RowRepresents row26 Data.chebyshevRow26 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row27Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-27))) (.node 1 (.leaf (0)) (.leaf (3276)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-117936))) (.node 1 (.leaf (0)) (.leaf (1976832))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-18670080))) (.node 1 (.leaf (0)) (.leaf (109983744)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-428654592))) (.node 1 (.leaf (0)) (.leaf (1143078912))))))

def row27Part01 : LookupTree ℤ := (.node 6 (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (-2118057984)) (.leaf (0)))) (.node 1 (.leaf (2724986880)) (.node 1 (.leaf (0)) (.leaf (-2387607552))))) (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (1358954496)) (.leaf (0)))) (.node 1 (.leaf (-452984832)) (.node 1 (.leaf (0)) (.leaf (67108864))))))

def row27 : CoefficientRow := ⟨28, (.node 16 row27Part00 row27Part01)⟩

theorem row27_represents : RowRepresents row27 Data.chebyshevRow27 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row28Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-392)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (25480)) (.leaf (0))) (.node 1 (.leaf (-652288)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (8712704)) (.leaf (0))) (.node 1 (.leaf (-69701632)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (361181184)) (.leaf (0))) (.node 1 (.leaf (-1270087680)) (.leaf (0))))))

def row28Part01 : LookupTree ℤ := (.node 6 (.node 3 (.node 1 (.leaf (3111714816)) (.node 1 (.leaf (0)) (.leaf (-5369233408)))) (.node 1 (.leaf (0)) (.node 1 (.leaf (6499598336)) (.leaf (0))))) (.node 3 (.node 1 (.leaf (-5402263552)) (.node 1 (.leaf (0)) (.leaf (2936012800)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-939524096))) (.node 1 (.leaf (0)) (.leaf (134217728))))))

def row28 : CoefficientRow := ⟨29, (.node 16 row28Part00 row28Part01)⟩

theorem row28_represents : RowRepresents row28 Data.chebyshevRow28 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row29Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (29))) (.node 1 (.leaf (0)) (.leaf (-4060)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (168896))) (.node 1 (.leaf (0)) (.leaf (-3281408))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (36095488))) (.node 1 (.leaf (0)) (.leaf (-249387008)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (1151016960))) (.node 1 (.leaf (0)) (.leaf (-3683254272))))))

def row29Part01 : LookupTree ℤ := (.node 7 (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (8341487616)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-13463453696)) (.leaf (0))) (.node 1 (.leaf (15386804224)) (.leaf (0))))) (.node 3 (.node 1 (.leaf (-12163481600)) (.node 1 (.leaf (0)) (.leaf (6325010432)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1946157056))) (.node 1 (.leaf (0)) (.leaf (268435456))))))

def row29 : CoefficientRow := ⟨30, (.node 16 row29Part00 row29Part01)⟩

theorem row29_represents : RowRepresents row29 Data.chebyshevRow29 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row30Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (450)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-33600)) (.leaf (0))) (.node 1 (.leaf (990080)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-15275520)) (.leaf (0))) (.node 1 (.leaf (141892608)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-859955200)) (.leaf (0))) (.node 1 (.leaf (3572121600)) (.leaf (0))))))

def row30Part01 : LookupTree ℤ := (.node 7 (.node 3 (.node 1 (.leaf (-10478223360)) (.node 1 (.leaf (0)) (.leaf (22052208640)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-33426505728))) (.node 1 (.leaf (0)) (.leaf (36175872000))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-27262976000))) (.node 1 (.leaf (0)) (.leaf (13589544960)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-4026531840))) (.node 1 (.leaf (0)) (.leaf (536870912))))))

def row30 : CoefficientRow := ⟨31, (.node 16 row30Part00 row30Part01)⟩

theorem row30_represents : RowRepresents row30 Data.chebyshevRow30 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row31Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-31))) (.node 1 (.leaf (0)) (.leaf (4960)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-236096))) (.node 1 (.leaf (0)) (.leaf (5261568))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-66646528))) (.node 1 (.leaf (0)) (.leaf (533172224)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2870927360))) (.node 1 (.leaf (0)) (.leaf (10827497472))))))

def row31Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-29297934336))) (.node 1 (.leaf (0)) (.leaf (57567870976)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-82239815680))) (.node 1 (.leaf (0)) (.leaf (84515225600))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-60850962432))) (.node 1 (.leaf (0)) (.leaf (29125246976)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-8321499136))) (.node 1 (.leaf (0)) (.leaf (1073741824))))))

def row31 : CoefficientRow := ⟨32, (.node 16 row31Part00 row31Part01)⟩

theorem row31_represents : RowRepresents row31 Data.chebyshevRow31 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.CoefficientCache
