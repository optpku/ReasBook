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

def row32Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-512)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (43520)) (.leaf (0))) (.node 1 (.leaf (-1462272)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (25798656)) (.leaf (0))) (.node 1 (.leaf (-275185664)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1926299648)) (.leaf (0))) (.node 1 (.leaf (-9313976320)) (.leaf (0))))))

def row32Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (32133218304)) (.leaf (0))) (.node 1 (.leaf (-80648077312)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (148562247680)) (.leaf (0))) (.node 1 (.leaf (-200655503360)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (196293427200)) (.leaf (0))) (.node 1 (.leaf (-135291469824)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (62277025792)) (.leaf (0))) (.node 1 (.leaf (-17179869184)) (.leaf (0))))))

def row32Part02 : LookupTree ℤ := (.leaf (2147483648))

def row32 : CoefficientRow := ⟨33, (.node 16 row32Part00 (.node 16 row32Part01 row32Part02))⟩

theorem row32_represents : RowRepresents row32 Data.chebyshevRow32 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row33Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (33))) (.node 1 (.leaf (0)) (.leaf (-5984)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (323136))) (.node 1 (.leaf (0)) (.leaf (-8186112))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (118243840))) (.node 1 (.leaf (0)) (.leaf (-1083543552)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (6723526656))) (.node 1 (.leaf (0)) (.leaf (-29455450112))))))

def row33Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (93564370944))) (.node 1 (.leaf (0)) (.leaf (-218864025600)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (379364311040))) (.node 1 (.leaf (0)) (.leaf (-485826232320))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (453437816832))) (.node 1 (.leaf (0)) (.leaf (-299708186624)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (132875550720))) (.node 1 (.leaf (0)) (.leaf (-35433480192))))))

def row33Part02 : LookupTree ℤ := (.node 1 (.leaf (0)) (.leaf (4294967296)))

def row33 : CoefficientRow := ⟨34, (.node 16 row33Part00 (.node 16 row33Part01 row33Part02))⟩

theorem row33_represents : RowRepresents row33 Data.chebyshevRow33 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row34Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (578)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-55488)) (.leaf (0))) (.node 1 (.leaf (2108544)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-42170880)) (.leaf (0))) (.node 1 (.leaf (511673344)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-4093386752)) (.leaf (0))) (.node 1 (.leaf (22761029632)) (.leaf (0))))))

def row34Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-91044118528)) (.leaf (0))) (.node 1 (.leaf (267776819200)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-586290298880)) (.leaf (0))) (.node 1 (.leaf (959384125440)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-1167945891840)) (.leaf (0))) (.node 1 (.leaf (1042167103488)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-661693399040)) (.leaf (0))) (.node 1 (.leaf (282930970624)) (.leaf (0))))))

def row34Part02 : LookupTree ℤ := (.node 1 (.leaf (-73014444032)) (.node 1 (.leaf (0)) (.leaf (8589934592))))

def row34 : CoefficientRow := ⟨35, (.node 16 row34Part00 (.node 16 row34Part01 row34Part02))⟩

theorem row34_represents : RowRepresents row34 Data.chebyshevRow34 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row35Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-35))) (.node 1 (.leaf (0)) (.leaf (7140)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-434112))) (.node 1 (.leaf (0)) (.leaf (12403200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-202585600))) (.node 1 (.leaf (0)) (.leaf (2106890240)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-14910300160))) (.node 1 (.leaf (0)) (.leaf (74977509376))))))

def row35Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-275652608000))) (.node 1 (.leaf (0)) (.leaf (754417664000)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1551944908800))) (.node 1 (.leaf (0)) (.leaf (2404594483200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-2789329600512))) (.node 1 (.leaf (0)) (.leaf (2384042393600)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1456262348800))) (.node 1 (.leaf (0)) (.leaf (601295421440))))))

def row35Part02 : LookupTree ℤ := (.node 2 (.node 1 (.leaf (0)) (.leaf (-150323855360))) (.node 1 (.leaf (0)) (.leaf (17179869184))))

def row35 : CoefficientRow := ⟨36, (.node 16 row35Part00 (.node 16 row35Part01 row35Part02))⟩

theorem row35_represents : RowRepresents row35 Data.chebyshevRow35 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row36Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-648)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (69768)) (.leaf (0))) (.node 1 (.leaf (-2976768)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (66977280)) (.leaf (0))) (.node 1 (.leaf (-916844544)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (8307167232)) (.leaf (0))) (.node 1 (.leaf (-52581629952)) (.leaf (0))))))

def row36Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (240999137280)) (.leaf (0))) (.node 1 (.leaf (-819082035200)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (2095125626880)) (.leaf (0))) (.node 1 (.leaf (-4063273943040)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (5977134858240)) (.leaf (0))) (.node 1 (.leaf (-6620826304512)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (5429778186240)) (.leaf (0))) (.node 1 (.leaf (-3195455668224)) (.leaf (0))))))

def row36Part02 : LookupTree ℤ := (.node 2 (.node 1 (.leaf (1275605286912)) (.leaf (0))) (.node 1 (.leaf (-309237645312)) (.node 1 (.leaf (0)) (.leaf (34359738368)))))

def row36 : CoefficientRow := ⟨37, (.node 16 row36Part00 (.node 16 row36Part01 row36Part02))⟩

theorem row36_represents : RowRepresents row36 Data.chebyshevRow36 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row37Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (37))) (.node 1 (.leaf (0)) (.leaf (-8436)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (573648))) (.node 1 (.leaf (0)) (.leaf (-18356736))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (336540160))) (.node 1 (.leaf (0)) (.leaf (-3940579328)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (31524634624))) (.node 1 (.leaf (0)) (.leaf (-180140769280))))))

def row37Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (757650882560))) (.node 1 (.leaf (0)) (.leaf (-2392581734400)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (5742196162560))) (.node 1 (.leaf (0)) (.leaf (-10531142369280))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (14743599316992))) (.node 1 (.leaf (0)) (.leaf (-15625695002624)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (12315818721280))) (.node 1 (.leaf (0)) (.leaf (-6992206757888))))))

def row37Part02 : LookupTree ℤ := (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (2701534429184)) (.leaf (0)))) (.node 1 (.leaf (-635655159808)) (.node 1 (.leaf (0)) (.leaf (68719476736)))))

def row37 : CoefficientRow := ⟨38, (.node 16 row37Part00 (.node 16 row37Part01 row37Part02))⟩

theorem row37_represents : RowRepresents row37 Data.chebyshevRow37 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row38Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (722)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-86640)) (.leaf (0))) (.node 1 (.leaf (4124064)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-103690752)) (.leaf (0))) (.node 1 (.leaf (1589924864)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-16188325888)) (.leaf (0))) (.node 1 (.leaf (115630899200)) (.leaf (0))))))

def row38Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-601280675840)) (.leaf (0))) (.node 1 (.leaf (2334383800320)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-6880289095680)) (.leaf (0))) (.node 1 (.leaf (15547666268160)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-27039419596800)) (.leaf (0))) (.node 1 (.leaf (36108024938496)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-36681168191488)) (.leaf (0))) (.node 1 (.leaf (27827093110784)) (.leaf (0))))))

def row38Part02 : LookupTree ℤ := (.node 3 (.node 1 (.leaf (-15260018802688)) (.node 1 (.leaf (0)) (.leaf (5712306503680)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1305670057984))) (.node 1 (.leaf (0)) (.leaf (137438953472)))))

def row38 : CoefficientRow := ⟨39, (.node 16 row38Part00 (.node 16 row38Part01 row38Part02))⟩

theorem row38_represents : RowRepresents row38 Data.chebyshevRow38 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row39Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-39))) (.node 1 (.leaf (0)) (.leaf (9880)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-746928))) (.node 1 (.leaf (0)) (.leaf (26604864))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-543921664))) (.node 1 (.leaf (0)) (.leaf (7120429056)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-63901286400))) (.node 1 (.leaf (0)) (.leaf (411402567680))))))

def row39Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-1960212234240))) (.node 1 (.leaf (0)) (.leaf (7061349335040)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-19502774353920))) (.node 1 (.leaf (0)) (.leaf (41626474905600))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-68822438510592))) (.node 1 (.leaf (0)) (.leaf (87841744879616)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-85678155104256))) (.node 1 (.leaf (0)) (.leaf (62646392979456))))))

def row39Part02 : LookupTree ℤ := (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-33221572034560))) (.node 1 (.leaf (0)) (.leaf (12060268167168)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2680059592704))) (.node 1 (.leaf (0)) (.leaf (274877906944)))))

def row39 : CoefficientRow := ⟨40, (.node 16 row39Part00 (.node 16 row39Part01 row39Part02))⟩

theorem row39_represents : RowRepresents row39 Data.chebyshevRow39 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row40Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-800)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (106400)) (.leaf (0))) (.node 1 (.leaf (-5617920)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (156900480)) (.leaf (0))) (.node 1 (.leaf (-2677768192)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (30429184000)) (.leaf (0))) (.node 1 (.leaf (-243433472000)) (.leaf (0))))))

def row40Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1424085811200)) (.leaf (0))) (.node 1 (.leaf (-6254808268800)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (21002987765760)) (.leaf (0))) (.node 1 (.leaf (-54553214976000)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (110292369408000)) (.leaf (0))) (.node 1 (.leaf (-173752901959680)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (212364657950720)) (.leaf (0))) (.node 1 (.leaf (-199183403319296)) (.leaf (0))))))

def row40Part02 : LookupTree ℤ := (.node 4 (.node 2 (.node 1 (.leaf (140552804761600)) (.leaf (0))) (.node 1 (.leaf (-72155450572800)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (25426206392320)) (.leaf (0))) (.node 1 (.leaf (-5497558138880)) (.node 1 (.leaf (0)) (.leaf (549755813888))))))

def row40 : CoefficientRow := ⟨41, (.node 16 row40Part00 (.node 16 row40Part01 row40Part02))⟩

theorem row40_represents : RowRepresents row40 Data.chebyshevRow40 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row41Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (41))) (.node 1 (.leaf (0)) (.leaf (-11480)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (959728))) (.node 1 (.leaf (0)) (.leaf (-37840704))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (857722624))) (.node 1 (.leaf (0)) (.leaf (-12475965440)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (124759654400))) (.node 1 (.leaf (0)) (.leaf (-898269511680))))))

def row41Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (4808383856640))) (.node 1 (.leaf (0)) (.leaf (-19570965872640)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (61508749885440))) (.node 1 (.leaf (0)) (.leaf (-150732904857600))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (289407177326592))) (.node 1 (.leaf (0)) (.leaf (-435347548798976)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (510407471005696))) (.node 1 (.leaf (0)) (.leaf (-461013199618048))))))

def row41Part02 : LookupTree ℤ := (.node 5 (.node 2 (.node 1 (.leaf (0)) (.leaf (314327181557760))) (.node 1 (.leaf (0)) (.node 1 (.leaf (-156371169312768)) (.leaf (0))))) (.node 2 (.node 1 (.leaf (53532472377344)) (.leaf (0))) (.node 1 (.leaf (-11269994184704)) (.node 1 (.leaf (0)) (.leaf (1099511627776))))))

def row41 : CoefficientRow := ⟨42, (.node 16 row41Part00 (.node 16 row41Part01 row41Part02))⟩

theorem row41_represents : RowRepresents row41 Data.chebyshevRow41 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row42Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (882)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-129360)) (.leaf (0))) (.node 1 (.leaf (7537376)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-232581888)) (.leaf (0))) (.node 1 (.leaf (4393213440)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-55381114880)) (.leaf (0))) (.node 1 (.leaf (492952780800)) (.leaf (0))))))

def row42Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-3220624834560)) (.leaf (0))) (.node 1 (.leaf (15871575982080)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-60144919511040)) (.leaf (0))) (.node 1 (.leaf (177570714746880)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-411758179123200)) (.leaf (0))) (.node 1 (.leaf (752567256612864)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1083059755548672)) (.leaf (0))) (.node 1 (.leaf (1219998345330688)) (.leaf (0))))))

def row42Part02 : LookupTree ℤ := (.node 5 (.node 2 (.node 1 (.leaf (-1062579203997696)) (.leaf (0))) (.node 1 (.leaf (700809813688320)) (.node 1 (.leaf (0)) (.leaf (-338168545017856))))) (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (112562502893568)) (.leaf (0)))) (.node 1 (.leaf (-23089744183296)) (.node 1 (.leaf (0)) (.leaf (2199023255552))))))

def row42 : CoefficientRow := ⟨43, (.node 16 row42Part00 (.node 16 row42Part01 row42Part02))⟩

theorem row42_represents : RowRepresents row42 Data.chebyshevRow42 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row43Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-43))) (.node 1 (.leaf (0)) (.leaf (13244)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1218448))) (.node 1 (.leaf (0)) (.leaf (52915456))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-1322886400))) (.node 1 (.leaf (0)) (.leaf (21262392320)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-235521884160))) (.node 1 (.leaf (0)) (.leaf (1884175073280))))))

def row43Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-11249633525760))) (.node 1 (.leaf (0)) (.leaf (51314117836800)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-181798588907520))) (.node 1 (.leaf (0)) (.leaf (505874334351360))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-1112923535572992))) (.node 1 (.leaf (0)) (.leaf (1940482062024704)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2676526982103040))) (.node 1 (.leaf (0)) (.leaf (2901009890279424))))))

def row43Part02 : LookupTree ℤ := (.node 6 (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (-2439485589553152)) (.leaf (0)))) (.node 1 (.leaf (1557990796689408)) (.node 1 (.leaf (0)) (.leaf (-729869562413056))))) (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (236394999971840)) (.leaf (0)))) (.node 1 (.leaf (-47278999994368)) (.node 1 (.leaf (0)) (.leaf (4398046511104))))))

def row43 : CoefficientRow := ⟨44, (.node 16 row43Part00 (.node 16 row43Part01 row43Part02))⟩

theorem row43_represents : RowRepresents row43 Data.chebyshevRow43 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row44Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-968)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (155848)) (.leaf (0))) (.node 1 (.leaf (-9974272)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (338412800)) (.leaf (0))) (.node 1 (.leaf (-7038986240)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (97905899520)) (.leaf (0))) (.node 1 (.leaf (-963996549120)) (.leaf (0))))))

def row44Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (6988974981120)) (.leaf (0))) (.node 1 (.leaf (-38370843033600)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (162773155184640)) (.leaf (0))) (.node 1 (.leaf (-541167892561920)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (1423506847825920)) (.leaf (0))) (.node 1 (.leaf (-2978414327758848)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (4964023879598080)) (.leaf (0))) (.node 1 (.leaf (-6573052309536768)) (.leaf (0))))))

def row44Part02 : LookupTree ℤ := (.node 6 (.node 3 (.node 1 (.leaf (6864598984556544)) (.node 1 (.leaf (0)) (.leaf (-5579780992794624)))) (.node 1 (.leaf (0)) (.node 1 (.leaf (3454150138396672)) (.leaf (0))))) (.node 3 (.node 1 (.leaf (-1572301627719680)) (.node 1 (.leaf (0)) (.leaf (495879744126976)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-96757023244288))) (.node 1 (.leaf (0)) (.leaf (8796093022208))))))

def row44 : CoefficientRow := ⟨45, (.node 16 row44Part00 (.node 16 row44Part01 row44Part02))⟩

theorem row44_represents : RowRepresents row44 Data.chebyshevRow44 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row45Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (45))) (.node 1 (.leaf (0)) (.leaf (-15180)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (1530144))) (.node 1 (.leaf (0)) (.leaf (-72864000))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (1999712000))) (.node 1 (.leaf (0)) (.leaf (-35340364800)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (431333683200))) (.node 1 (.leaf (0)) (.leaf (-3812168171520))))))

def row45Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (25227583488000))) (.node 1 (.leaf (0)) (.leaf (-128055803904000)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (507344899276800))) (.node 1 (.leaf (0)) (.leaf (-1588210119475200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (3959937231224832))) (.node 1 (.leaf (0)) (.leaf (-7897310717542400)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (12604574741299200))) (.node 1 (.leaf (0)) (.leaf (-16047114509352960))))))

def row45Part02 : LookupTree ℤ := (.node 7 (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (16168683558666240)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-12717552782278656)) (.leaf (0))) (.node 1 (.leaf (7638169839206400)) (.leaf (0))))) (.node 3 (.node 1 (.leaf (-3380998255411200)) (.node 1 (.leaf (0)) (.leaf (1039038488248320)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-197912092999680))) (.node 1 (.leaf (0)) (.leaf (17592186044416))))))

def row45 : CoefficientRow := ⟨46, (.node 16 row45Part00 (.node 16 row45Part01 row45Part02))⟩

theorem row45_represents : RowRepresents row45 Data.chebyshevRow45 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row46Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (1058)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-186208)) (.leaf (0))) (.node 1 (.leaf (13034560)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-484140800)) (.leaf (0))) (.node 1 (.leaf (11038410240)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-168586629120)) (.leaf (0))) (.node 1 (.leaf (1826663915520)) (.leaf (0))))))

def row46Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-14613311324160)) (.leaf (0))) (.node 1 (.leaf (88826010009600)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-418884762992640)) (.leaf (0))) (.node 1 (.leaf (1555857691115520)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-4599927086776320)) (.leaf (0))) (.node 1 (.leaf (10898288790208512)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-20758645314682880)) (.leaf (0))) (.node 1 (.leaf (31782201792135168)) (.leaf (0))))))

def row46Part02 : LookupTree ℤ := (.node 7 (.node 3 (.node 1 (.leaf (-38958828003262464)) (.node 1 (.leaf (0)) (.leaf (37917148110127104)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-28889255702953984))) (.node 1 (.leaf (0)) (.leaf (16848641306132480))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-7257876254949376))) (.node 1 (.leaf (0)) (.leaf (2174833999740928)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-404620279021568))) (.node 1 (.leaf (0)) (.leaf (35184372088832))))))

def row46 : CoefficientRow := ⟨47, (.node 16 row46Part00 (.node 16 row46Part01 row46Part02))⟩

theorem row46_represents : RowRepresents row46 Data.chebyshevRow46 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row47Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-47))) (.node 1 (.leaf (0)) (.leaf (17296)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1902560))) (.node 1 (.leaf (0)) (.leaf (98933120))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-2967993600))) (.node 1 (.leaf (0)) (.leaf (57417185280)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-768506941440))) (.node 1 (.leaf (0)) (.leaf (7465496002560))))))

def row47Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-54454206136320))) (.node 1 (.leaf (0)) (.leaf (305707823923200)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1345114425262080))) (.node 1 (.leaf (0)) (.leaf (4699925501706240))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-13159791404777472))) (.node 1 (.leaf (0)) (.leaf (29693888297959424)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-54121865370664960))) (.node 1 (.leaf (0)) (.leaf (79611518093623296))))))

def row47Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-94086339565191168))) (.node 1 (.leaf (0)) (.leaf (88551849002532864)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-65416681245114368))) (.node 1 (.leaf (0)) (.leaf (37078280867676160))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-15554790998147072))) (.node 1 (.leaf (0)) (.leaf (4547580092481536)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-826832744087552))) (.node 1 (.leaf (0)) (.leaf (70368744177664))))))

def row47 : CoefficientRow := ⟨48, (.node 16 row47Part00 (.node 16 row47Part01 row47Part02))⟩

theorem row47_represents : RowRepresents row47 Data.chebyshevRow47 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.CoefficientCache
