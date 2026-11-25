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

def row64Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-2048)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (698368)) (.leaf (0))) (.node 1 (.leaf (-94978048)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (6885908480)) (.leaf (0))) (.node 1 (.leaf (-308488699904)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (9338794278912)) (.leaf (0))) (.node 1 (.leaf (-202785247199232)) (.leaf (0))))))

def row64Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (3295260266987520)) (.leaf (0))) (.node 1 (.leaf (-41352285703372800)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (410475846508216320)) (.leaf (0))) (.node 1 (.leaf (-3283806772065730560)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (21487518225908367360)) (.leaf (0))) (.node 1 (.leaf (-116363175623380697088)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (526404842105769820160)) (.leaf (0))) (.node 1 (.leaf (-2003968778223344418816)) (.leaf (0))))))

def row64Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (6456334894356662059008)) (.leaf (0))) (.node 1 (.leaf (-17677237785618240503808)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (41246888166442561175552)) (.leaf (0))) (.node 1 (.leaf (-82141740303015057817600)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (139640958515125598289920)) (.leaf (0))) (.node 1 (.leaf (-202406406767568811458560)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (249477664155375511797760)) (.leaf (0))) (.node 1 (.leaf (-260324519118652707962880)) (.leaf (0))))))

def row64Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (228476306673285621350400)) (.leaf (0))) (.node 1 (.leaf (-167114098595317483044864)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (100570928113924096131072)) (.leaf (0))) (.node 1 (.leaf (-48915000675954696650752)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (18740162596631994171392)) (.leaf (0))) (.node 1 (.leaf (-5441789501744317726720)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1125251388496282648576)) (.leaf (0))) (.node 1 (.leaf (-147573952589676412928)) (.leaf (0))))))

def row64Part04 : LookupTree ℤ := (.leaf (9223372036854775808))

def row64 : CoefficientRow := ⟨65, (.node 32 (.node 16 row64Part00 row64Part01) (.node 16 row64Part02 (.node 16 row64Part03 row64Part04)))⟩

theorem row64_represents : RowRepresents row64 Data.chebyshevRow64 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row65Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (65))) (.node 1 (.leaf (0)) (.leaf (-45760)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (9646208))) (.node 1 (.leaf (0)) (.leaf (-964620800))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (55948006400))) (.node 1 (.leaf (0)) (.leaf (-2107713986560)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (55449091031040))) (.node 1 (.leaf (0)) (.leaf (-1070959586770944))))))

def row65Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (15749405687808000))) (.node 1 (.leaf (0)) (.leaf (-181256318091264000)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (1667558126439628800))) (.node 1 (.leaf (0)) (.leaf (-12470434684678963200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (76817877657622413312))) (.node 1 (.leaf (0)) (.leaf (-393937834141653401600)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (1696067325319236812800))) (.node 1 (.leaf (0)) (.leaf (-6171496590193868144640))))))

def row65Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (19075534915144683356160))) (.node 1 (.leaf (0)) (.leaf (-50269644952851871432704)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (113219921064981692416000))) (.node 1 (.leaf (0)) (.leaf (-218188997679883747328000))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (359745762028296129740800))) (.node 1 (.leaf (0)) (.leaf (-506751505315606508339200)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (608101806378727810007040))) (.node 1 (.leaf (0)) (.leaf (-618789997240148557824000))))))

def row65Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (530391426205841620992000))) (.node 1 (.leaf (0)) (.leaf (-379385867215472594780160)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (223556839026824199536640))) (.node 1 (.leaf (0)) (.leaf (-106584674768344466849792))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (40069426604640777011200))) (.node 1 (.leaf (0)) (.leaf (-11428334414415370649600)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (2323136831782796656640))) (.node 1 (.leaf (0)) (.leaf (-299759591197780213760))))))

def row65Part04 : LookupTree ℤ := (.node 1 (.leaf (0)) (.leaf (18446744073709551616)))

def row65 : CoefficientRow := ⟨66, (.node 32 (.node 16 row65Part00 row65Part01) (.node 16 row65Part02 (.node 16 row65Part03 row65Part04)))⟩

theorem row65_represents : RowRepresents row65 Data.chebyshevRow65 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row66Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (2178)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-789888)) (.leaf (0))) (.node 1 (.leaf (114270464)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-8815150080)) (.leaf (0))) (.node 1 (.leaf (420384712704)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-13554222252032)) (.leaf (0))) (.node 1 (.leaf (313683429261312)) (.leaf (0))))))

def row66Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-5437179440529408)) (.leaf (0))) (.node 1 (.leaf (72851097078988800)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-772988482690744320)) (.leaf (0))) (.node 1 (.leaf (6618923024944988160)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-46428387595266293760)) (.leaf (0))) (.node 1 (.leaf (269998930938625523712)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1314280510389076623360)) (.leaf (0))) (.node 1 (.leaf (5396103428861818044416)) (.leaf (0))))))

def row66Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-18799328074744398348288)) (.leaf (0))) (.node 1 (.leaf (55828307615907607216128)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-141786178072146304040960)) (.leaf (0))) (.node 1 (.leaf (308581582432978442649600)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-576018953874893092945920)) (.leaf (0))) (.node 1 (.leaf (921897930824161070940160)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1262980674786588528476160)) (.leaf (0))) (.node 1 (.leaf (1476528131876108327976960)) (.leaf (0))))))

def row66Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1466056301153582736998400)) (.leaf (0))) (.node 1 (.leaf (1227896951007000725028864)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-859342662544869285691392)) (.leaf (0))) (.node 1 (.leaf (496028678729603095724032)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-231909512133320927870976)) (.leaf (0))) (.node 1 (.leaf (85580642711025871749120)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-23981920217327023947776)) (.leaf (0))) (.node 1 (.leaf (4793847616155269726208)) (.leaf (0))))))

def row66Part04 : LookupTree ℤ := (.node 1 (.leaf (-608742554432415203328)) (.node 1 (.leaf (0)) (.leaf (36893488147419103232))))

def row66 : CoefficientRow := ⟨67, (.node 32 (.node 16 row66Part00 row66Part01) (.node 16 row66Part02 (.node 16 row66Part03 row66Part04)))⟩

theorem row66_represents : RowRepresents row66 Data.chebyshevRow66 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row67Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-67))) (.node 1 (.leaf (0)) (.leaf (50116)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-11225984))) (.node 1 (.leaf (0)) (.leaf (1193161728))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-73578306560))) (.node 1 (.leaf (0)) (.leaf (2948483411968)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-82557535535104))) (.node 1 (.leaf (0)) (.leaf (1698326445293568))))))

def row67Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-26623764568866816))) (.node 1 (.leaf (0)) (.leaf (326958512249241600)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-3213535091821117440))) (.node 1 (.leaf (0)) (.leaf (25708280734568939520))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-169674652848155000832))) (.node 1 (.leaf (0)) (.leaf (933935696018904449024)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-4324628346097390059520))) (.node 1 (.leaf (0)) (.leaf (16963703447917504233472))))))

def row67Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-56674191064633480052736))) (.node 1 (.leaf (0)) (.leaf (161926260184667085864960)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-396792277209274300497920))) (.node 1 (.leaf (0)) (.leaf (835352162545840632627200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-1511783669778082315632640))) (.node 1 (.leaf (0)) (.leaf (2350547366963928650219520)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-3134063155951904866959360))) (.node 1 (.leaf (0)) (.leaf (3571846260992365213777920))))))

def row67Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-3462504028513007094988800))) (.node 1 (.leaf (0)) (.leaf (2835179769229474044837888)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1942242164116562770919424))) (.node 1 (.leaf (0)) (.leaf (1098642032227550658297856))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-503888450871282632753152))) (.node 1 (.leaf (0)) (.leaf (182589619836467114147840)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-50286977266436844552192))) (.node 1 (.leaf (0)) (.leaf (9887454823508319666176))))))

def row67Part04 : LookupTree ℤ := (.node 2 (.node 1 (.leaf (0)) (.leaf (-1235931852938539958272))) (.node 1 (.leaf (0)) (.leaf (73786976294838206464))))

def row67 : CoefficientRow := ⟨68, (.node 32 (.node 16 row67Part00 row67Part01) (.node 16 row67Part02 (.node 16 row67Part03 row67Part04)))⟩

theorem row67_represents : RowRepresents row67 Data.chebyshevRow67 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row68Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-2312)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (890120)) (.leaf (0))) (.node 1 (.leaf (-136722432)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (11201473536)) (.leaf (0))) (.node 1 (.leaf (-567541325824)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (19451189075968)) (.leaf (0))) (.node 1 (.leaf (-478798500331520)) (.leaf (0))))))

def row68Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (8833832331116544)) (.leaf (0))) (.node 1 (.leaf (-126098626216722432)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1426905507189227520)) (.leaf (0))) (.node 1 (.leaf (-13045993208587223040)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (97844949064404172800)) (.leaf (0))) (.node 1 (.leaf (-609348236634935525376)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (3182151902426885521408)) (.leaf (0))) (.node 1 (.leaf (-14045360121056598163456)) (.leaf (0))))))

def row68Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (52726734970579406815232)) (.leaf (0))) (.node 1 (.leaf (-169176689745174567321600)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (465638698441480475770880)) (.leaf (0))) (.node 1 (.leaf (-1102166136851527043645440)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (2246723278966574358200320)) (.leaf (0))) (.node 1 (.leaf (-3945465270380325702205440)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (5964075408714445828915200)) (.leaf (0))) (.node 1 (.leaf (-7744654443779918061895680)) (.leaf (0))))))

def row68Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (8609748823138313164554240)) (.leaf (0))) (.node 1 (.leaf (-8152905008033014915006464)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (6529702201003817375367168)) (.leaf (0))) (.node 1 (.leaf (-4380513006962728637562880)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (2429193576588422244466688)) (.leaf (0))) (.node 1 (.leaf (-1093357544453591137255424)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (389161159890261252243456)) (.leaf (0))) (.node 1 (.leaf (-105367802149028958830592)) (.leaf (0))))))

def row68Part04 : LookupTree ℤ := (.node 2 (.node 1 (.leaf (20383652201449054535680)) (.leaf (0))) (.node 1 (.leaf (-2508757194024499019776)) (.node 1 (.leaf (0)) (.leaf (147573952589676412928)))))

def row68 : CoefficientRow := ⟨69, (.node 32 (.node 16 row68Part00 row68Part01) (.node 16 row68Part02 (.node 16 row68Part03 row68Part04)))⟩

theorem row68_represents : RowRepresents row68 Data.chebyshevRow68 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row69Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (69))) (.node 1 (.leaf (0)) (.leaf (-54740)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (13006224))) (.node 1 (.leaf (0)) (.leaf (-1466606592))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (95981253632))) (.node 1 (.leaf (0)) (.leaf (-4083566063616)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (121459913687040))) (.node 1 (.leaf (0)) (.leaf (-2655923445956608))))))

def row69Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (44291429231099904))) (.node 1 (.leaf (0)) (.leaf (-579155764682686464)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (6067346106199572480))) (.node 1 (.leaf (0)) (.leaf (-51800267151743385600))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (365364550976963346432))) (.node 1 (.leaf (0)) (.leaf (-2152632169288775499776)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (10688932150951161102336))) (.node 1 (.leaf (0)) (.leaf (-45054423690030700560384))))))

def row69Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (162127661005792293683200))) (.node 1 (.leaf (0)) (.leaf (-500279639675016220508160)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (1328069674092235252039680))) (.node 1 (.leaf (0)) (.leaf (-3039684436248894719918080))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (6005230227711231032033280))) (.node 1 (.leaf (0)) (.leaf (-10241477907724580054630400)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (15062213973380796524789760))) (.node 1 (.leaf (0)) (.leaf (-19061155148552201337569280))))))

def row69Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (20682001674789633424097280))) (.node 1 (.leaf (0)) (.leaf (-19140989785295503874850816)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (15001646566124197521653760))) (.node 1 (.leaf (0)) (.leaf (-9859668046153007933423616))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (5362275604048127121686528))) (.node 1 (.leaf (0)) (.leaf (-2369304708743649388658688)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (828609297046959349039104))) (.node 1 (.leaf (0)) (.leaf (-220623059121566237327360))))))

def row69Part04 : LookupTree ℤ := (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (42003236255836649029632)) (.leaf (0)))) (.node 1 (.leaf (-5091301364343836246016)) (.node 1 (.leaf (0)) (.leaf (295147905179352825856)))))

def row69 : CoefficientRow := ⟨70, (.node 32 (.node 16 row69Part00 row69Part01) (.node 16 row69Part02 (.node 16 row69Part03 row69Part04)))⟩

theorem row69_represents : RowRepresents row69 Data.chebyshevRow69 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row70Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (2450)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-999600)) (.leaf (0))) (.node 1 (.leaf (162734880)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-14134686720)) (.leaf (0))) (.node 1 (.leaf (759503833088)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-27618321203200)) (.leaf (0))) (.node 1 (.leaf (721718327705600)) (.leaf (0))))))

def row70Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-14145679223029760)) (.leaf (0))) (.node 1 (.leaf (214681484678922240)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-2585217036554600448)) (.leaf (0))) (.node 1 (.leaf (25180685420986368000)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-201445483367890944000)) (.leaf (0))) (.node 1 (.leaf (1340077338588862218240)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-7487416241004436520960)) (.leaf (0))) (.node 1 (.leaf (35423224422958920368128)) (.leaf (0))))))

def row70Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-142835582350640807936000)) (.leaf (0))) (.node 1 (.leaf (493432011756759154688000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1466197977791512916787200)) (.leaf (0))) (.node 1 (.leaf (3758305485035997547724800)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-8326092151464363798036480)) (.leaf (0))) (.node 1 (.leaf (15955925725802787766272000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-26447031224163605938176000)) (.leaf (0))) (.node 1 (.leaf (37869082390541511111475200)) (.leaf (0))))))

def row70Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-46732059120242715839692800)) (.leaf (0))) (.node 1 (.leaf (49516908357612281763201024)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-44811681771594825125068800)) (.leaf (0))) (.node 1 (.leaf (34383806139211123680870400)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-22148529668894438111313920)) (.leaf (0))) (.node 1 (.leaf (11817908752549845380628480)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-5127770577377560029560832)) (.leaf (0))) (.node 1 (.leaf (1762586396242947656908800)) (.leaf (0))))))

def row70Part04 : LookupTree ℤ := (.node 3 (.node 1 (.leaf (-461629770444581529190400)) (.node 1 (.leaf (0)) (.leaf (86515229705697797079040)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-10330176681277348904960))) (.node 1 (.leaf (0)) (.leaf (590295810358705651712)))))

def row70 : CoefficientRow := ⟨71, (.node 32 (.node 16 row70Part00 row70Part01) (.node 16 row70Part02 (.node 16 row70Part03 row70Part04)))⟩

theorem row70_represents : RowRepresents row70 Data.chebyshevRow70 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row71Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-71))) (.node 1 (.leaf (0)) (.leaf (59640)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-15005424))) (.node 1 (.leaf (0)) (.leaf (1792076352))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-124250627072))) (.node 1 (.leaf (0)) (.leaf (5602573729792)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-176696556093440))) (.node 1 (.leaf (0)) (.leaf (4099360101367808))))))

def row71Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-72582787677159424))) (.node 1 (.leaf (0)) (.leaf (1008518734040530944)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-11237780179308773376))) (.node 1 (.leaf (0)) (.leaf (102161637993716121600))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-768255517712745234432))) (.node 1 (.leaf (0)) (.leaf (4832786846466499936256)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-25663764632960034144256))) (.node 1 (.leaf (0)) (.leaf (115900872535948541296640))))))

def row71Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-447798825707073909555200))) (.node 1 (.leaf (0)) (.leaf (1487143663188534529884160)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-4260465629675261085614080))) (.node 1 (.leaf (0)) (.leaf (10556295406320889815367680))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-22657414530639958628106240))) (.node 1 (.leaf (0)) (.leaf (42153329359330155587174400)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-67956276421708008401141760))) (.node 1 (.leaf (0)) (.leaf (94799319929635223560519680))))))

def row71Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-114146119915275065103482880))) (.node 1 (.leaf (0)) (.leaf (118174806500520067401252864)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-104625010109313847771791360))) (.node 1 (.leaf (0)) (.leaf (78627280324575255295164416))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-49659334941837003344314368))) (.node 1 (.leaf (0)) (.leaf (26005122213843340149915648)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-11084150451802079408160768))) (.node 1 (.leaf (0)) (.leaf (3745795851607461551144960))))))

def row71Part04 : LookupTree ℤ := (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-965262777144999707410432))) (.node 1 (.leaf (0)) (.leaf (178121760775739430404096)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-20955501267734050635776))) (.node 1 (.leaf (0)) (.leaf (1180591620717411303424)))))

def row71 : CoefficientRow := ⟨72, (.node 32 (.node 16 row71Part00 row71Part01) (.node 16 row71Part02 (.node 16 row71Part03 row71Part04)))⟩

theorem row71_represents : RowRepresents row71 Data.chebyshevRow71 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row72Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-2592)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1118880)) (.leaf (0))) (.node 1 (.leaf (-192745728)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (17718839424)) (.leaf (0))) (.node 1 (.leaf (-1008005087232)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (38823468662784)) (.leaf (0))) (.node 1 (.leaf (-1075111439892480)) (.leaf (0))))))

def row72Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (22344399425765376)) (.leaf (0))) (.node 1 (.leaf (-359847060033241088)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (4602254504635662336)) (.leaf (0))) (.node 1 (.leaf (-47656245779603914752)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (405768759355323187200)) (.leaf (0))) (.node 1 (.leaf (-2876588374014352687104)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (17152989933937436393472)) (.leaf (0))) (.node 1 (.leaf (-86750753688878988656640)) (.leaf (0))))))

def row72Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (374637327422537890529280)) (.leaf (0))) (.node 1 (.leaf (-1389029663170906973798400)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (4440485304168581976555520)) (.leaf (0))) (.node 1 (.leaf (-12279236744386519718952960)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (29438682964106143428771840)) (.leaf (0))) (.node 1 (.leaf (-61270754787082705022484480)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (110753689942823917112524800)) (.leaf (0))) (.node 1 (.leaf (-173781635233957527913758720)) (.leaf (0))))))

def row72Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (236330698979513162960732160)) (.leaf (0))) (.node 1 (.leaf (-277809148188162411970166784)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (281161294772634959927574528)) (.leaf (0))) (.node 1 (.leaf (-243633826357838819224453120)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (179403090318044948701642752)) (.leaf (0))) (.node 1 (.leaf (-111136578636223852069257216)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (57138015005064240329392128)) (.leaf (0))) (.node 1 (.leaf (-23930887299847106473230336)) (.leaf (0))))))

def row72Part04 : LookupTree ℤ := (.node 4 (.node 2 (.node 1 (.leaf (7953221473659504631480320)) (.leaf (0))) (.node 1 (.leaf (-2017040783995697211899904)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (366573698232756209713152)) (.leaf (0))) (.node 1 (.leaf (-42501298345826806923264)) (.node 1 (.leaf (0)) (.leaf (2361183241434822606848))))))

def row72 : CoefficientRow := ⟨73, (.node 32 (.node 16 row72Part00 row72Part01) (.node 16 row72Part02 (.node 16 row72Part03 row72Part04)))⟩

theorem row72_represents : RowRepresents row72 Data.chebyshevRow72 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row73Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (73))) (.node 1 (.leaf (0)) (.leaf (-64824)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (17243184))) (.node 1 (.leaf (0)) (.leaf (-2177567808))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (159688305920))) (.node 1 (.leaf (0)) (.leaf (-7618583904256)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (254343493419008))) (.node 1 (.leaf (0)) (.leaf (-6249582981152768))))))

def row73Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (117271586528690176))) (.node 1 (.leaf (0)) (.leaf (-1728212854107013120)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (20442289188580098048))) (.node 1 (.leaf (0)) (.leaf (-197474129552923951104))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (1579793036423391608832))) (.node 1 (.leaf (0)) (.leaf (-10585963594495205310464)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (59969744500834906931200))) (.node 1 (.leaf (0)) (.leaf (-289402379913706518609920))))))

def row73Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (1197073480552149690613760))) (.node 1 (.leaf (0)) (.leaf (-4265202989530348477480960)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (13141436238012425038725120))) (.node 1 (.leaf (0)) (.leaf (-35114768895093929253273600))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (81534780458852245485649920))) (.node 1 (.leaf (0)) (.leaf (-164694838933495565632143360)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (289463656307355842626191360))) (.node 1 (.leaf (0)) (.leaf (-442362590397550279388037120))))))

def row73Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (586807517874301391024947200))) (.node 1 (.leaf (0)) (.leaf (-673793102876844891341586432)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (666947599654583767626940416))) (.node 1 (.leaf (0)) (.leaf (-565894933040252893744070656))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (408465515577926900747599872))) (.node 1 (.leaf (0)) (.leaf (-248278279486291044288430080)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (125360180461930560066945024))) (.node 1 (.leaf (0)) (.leaf (-51607570451301674497605632))))))

def row73Part04 : LookupTree ℤ := (.node 5 (.node 2 (.node 1 (.leaf (0)) (.leaf (16871705724464008970371072))) (.node 1 (.leaf (0)) (.node 1 (.leaf (-4212203328767133854203904)) (.leaf (0))))) (.node 2 (.node 1 (.leaf (754102897733246470062080)) (.leaf (0))) (.node 1 (.leaf (-86183188312371025149952)) (.node 1 (.leaf (0)) (.leaf (4722366482869645213696))))))

def row73 : CoefficientRow := ⟨74, (.node 32 (.node 16 row73Part00 row73Part01) (.node 16 row73Part02 (.node 16 row73Part03 row73Part04)))⟩

theorem row73_represents : RowRepresents row73 Data.chebyshevRow73 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row74Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (2738)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1248528)) (.leaf (0))) (.node 1 (.leaf (227232096)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-22073975040)) (.leaf (0))) (.node 1 (.leaf (1327381699072)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-54060636471296)) (.leaf (0))) (.node 1 (.leaf (1583798426730496)) (.leaf (0))))))

def row74Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-34843565388070912)) (.leaf (0))) (.node 1 (.leaf (594390233090621440)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-8058680212849688576)) (.leaf (0))) (.node 1 (.leaf (88540824156764110848)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-800717018461171089408)) (.leaf (0))) (.node 1 (.leaf (6036174446861135904768)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-38324917122927847014400)) (.leaf (0))) (.node 1 (.leaf (206690242690548802519040)) (.leaf (0))))))

def row74Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-953442087249950927749120)) (.leaf (0))) (.node 1 (.leaf (3783176624275206355025920)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-12970891283229278931517440)) (.leaf (0))) (.node 1 (.leaf (38562109220411369796403200)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-99668220754294001935319040)) (.leaf (0))) (.node 1 (.leaf (224340315704787195993784320)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-440143367809815048376811520)) (.leaf (0))) (.node 1 (.leaf (752708947848669213166141440)) (.leaf (0))))))

def row74Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1121055879774613721736806400)) (.leaf (0))) (.node 1 (.leaf (1451424183936765194020061184)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1628747500526324742610747392)) (.leaf (0))) (.node 1 (.leaf (1577529025667006354478333952)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-1311192956398550736189784064)) (.leaf (0))) (.node 1 (.leaf (928067609792077653564456960)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-553694573977646328906252288)) (.leaf (0))) (.node 1 (.leaf (274651248223708226607120384)) (.leaf (0))))))

def row74Part04 : LookupTree ℤ := (.node 5 (.node 2 (.node 1 (.leaf (-111168362376262853626691584)) (.leaf (0))) (.node 1 (.leaf (35760452232923715152642048)) (.node 1 (.leaf (0)) (.leaf (-8790980355767023918120960))))) (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (1550707093812319747047424)) (.leaf (0)))) (.node 1 (.leaf (-174727559866176872906752)) (.node 1 (.leaf (0)) (.leaf (9444732965739290427392))))))

def row74 : CoefficientRow := ⟨75, (.node 32 (.node 16 row74Part00 row74Part01) (.node 16 row74Part02 (.node 16 row74Part03 row74Part04)))⟩

theorem row74_represents : RowRepresents row74 Data.chebyshevRow74 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row75Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-75))) (.node 1 (.leaf (0)) (.leaf (70300)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-19740240))) (.node 1 (.leaf (0)) (.leaf (2632032000))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-203836256000))) (.node 1 (.leaf (0)) (.leaf (10273347302400)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-362464766361600))) (.node 1 (.leaf (0)) (.leaf (9417179834613760))))))

def row75Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-186958717304832000))) (.node 1 (.leaf (0)) (.leaf (2916993320288256000)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-36559649614279475200))) (.node 1 (.leaf (0)) (.leaf (374555777866452172800))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-3181227073345733787648))) (.node 1 (.leaf (0)) (.leaf (22658312488217477120000)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-136619578746690600960000))) (.node 1 (.leaf (0)) (.leaf (702782865294804123648000))))))

def row75Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-3103957655052051546112000))) (.node 1 (.leaf (0)) (.leaf (11831556238080761187532800)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-39083218804470982901760000))) (.node 1 (.leaf (0)) (.leaf (112238987335916668846080000))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-280871221967440249356288000))) (.node 1 (.leaf (0)) (.leaf (613375470343069957619712000)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1169750391926985939379814400))) (.node 1 (.leaf (0)) (.leaf (1947780486094888705720320000))))))

def row75Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-2828919277423528834498560000))) (.node 1 (.leaf (0)) (.leaf (3576641470750375279381708800)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-3924442600707233252848435200))) (.node 1 (.leaf (0)) (.leaf (3720952984374265602700738560))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-3030851428375028373127168000))) (.node 1 (.leaf (0)) (.leaf (2104413499070446351417344000)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1232749328417223217879449600))) (.node 1 (.leaf (0)) (.leaf (600910066898718127711846400))))))

def row75Part04 : LookupTree ℤ := (.node 6 (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (-239208430476989716223754240)) (.leaf (0)))) (.node 1 (.leaf (75733107794614564159488000)) (.node 1 (.leaf (0)) (.leaf (-18336063609267294306304000))))) (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (3187597375937010519244800)) (.leaf (0)))) (.node 1 (.leaf (-354177486215223391027200)) (.node 1 (.leaf (0)) (.leaf (18889465931478580854784))))))

def row75 : CoefficientRow := ⟨76, (.node 32 (.node 16 row75Part00 row75Part01) (.node 16 row75Part02 (.node 16 row75Part03 row75Part04)))⟩

theorem row75_represents : RowRepresents row75 Data.chebyshevRow75 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row76Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-2888)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1389128)) (.leaf (0))) (.node 1 (.leaf (-266712576)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (27338039040)) (.leaf (0))) (.node 1 (.leaf (-1735054211072)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (74607331076096)) (.leaf (0))) (.node 1 (.leaf (-2308727959453696)) (.leaf (0))))))

def row76Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (53677925057298432)) (.leaf (0))) (.node 1 (.leaf (-968307667700285440)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (13892666853426200576)) (.leaf (0))) (.node 1 (.leaf (-161660123385323061248)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (1549828574194075435008)) (.leaf (0))) (.node 1 (.leaf (-12398628593552603480064)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (83641542099362801254400)) (.leaf (0))) (.node 1 (.leaf (-479929400183930004439040)) (.leaf (0))))))

def row76Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (2359007817839559175045120)) (.leaf (0))) (.node 1 (.leaf (-9991091934379309447249920)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (36634003759390801306583040)) (.leaf (0))) (.node 1 (.leaf (-116728546829353335599923200)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (324146195426127339627479040)) (.leaf (0))) (.node 1 (.leaf (-786082759639667694706360320)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1666894308495954963616235520)) (.leaf (0))) (.node 1 (.leaf (-3092209731702641091925770240)) (.leaf (0))))))

def row76Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (5016616851964391133177446400)) (.leaf (0))) (.node 1 (.leaf (-7109262738783822863017181184)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (8782030442027075301374164992)) (.leaf (0))) (.node 1 (.leaf (-9426414227081472860175204352)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (8753098925147081941591261184)) (.leaf (0))) (.node 1 (.leaf (-6989770466542134399818792960)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (4762521572118539031740940288)) (.leaf (0))) (.node 1 (.leaf (-2740149905058154662366019584)) (.leaf (0))))))

def row76Part04 : LookupTree ℤ := (.node 6 (.node 3 (.node 1 (.leaf (1312988496173699109050384384)) (.node 1 (.leaf (0)) (.leaf (-514177313186903147600150528)))) (.node 1 (.leaf (0)) (.node 1 (.leaf (160257195944996152237096960)) (.leaf (0))))) (.node 3 (.node 1 (.leaf (-38222834312346908359655424)) (.node 1 (.leaf (0)) (.leaf (6549922311740197911396352)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-717799705396186072481792))) (.node 1 (.leaf (0)) (.leaf (37778931862957161709568))))))

def row76 : CoefficientRow := ⟨77, (.node 32 (.node 16 row76Part00 row76Part01) (.node 16 row76Part02 (.node 16 row76Part03 row76Part04)))⟩

theorem row76_represents : RowRepresents row76 Data.chebyshevRow76 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row77Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (77))) (.node 1 (.leaf (0)) (.leaf (-76076)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (22518496))) (.node 1 (.leaf (0)) (.leaf (-3165457152))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (258512334080))) (.node 1 (.leaf (0)) (.leaf (-13743455724544)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (511679428513792))) (.node 1 (.leaf (0)) (.leaf (-14034635753521152))))))

def row77Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (294314567419428864))) (.node 1 (.leaf (0)) (.leaf (-4853608655688826880)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (64344983321131876352))) (.node 1 (.leaf (0)) (.leaf (-697876024637098295296))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (6280884221733884657664))) (.node 1 (.leaf (0)) (.leaf (-47455569675322684080128)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (303902662945416203468800))) (.node 1 (.leaf (0)) (.leaf (-1662641665662664132526080))))))

def row77Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (7821973290731169896202240))) (.node 1 (.leaf (0)) (.leaf (-31813740106839380082032640)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (112351226323252585514926080))) (.node 1 (.leaf (0)) (.leaf (-345696080994623340045926400))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (929163612819694928611246080))) (.node 1 (.leaf (0)) (.leaf (-2185540989622405347032432640)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (4503539008918895866612285440))) (.node 1 (.leaf (0)) (.leaf (-8132199949500170889571860480))))))

def row77Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (12862152981352311100853452800))) (.node 1 (.leaf (0)) (.leaf (-17795166948318021005416071168)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (21488503484761383855596765184))) (.node 1 (.leaf (0)) (.leaf (-22573781438537211323051147264))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (20537049278669192256309690368))) (.node 1 (.leaf (0)) (.leaf (-16083954432154715151054929920)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (10757792472654301281361330176))) (.node 1 (.leaf (0)) (.leaf (-6081209877015027452443885568))))))

def row77Part04 : LookupTree ℤ := (.node 7 (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (2865185422824387934324523008)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1104087734168420859359789056)) (.leaf (0))) (.node 1 (.leaf (338850455499259598780497920)) (.leaf (0))))) (.node 3 (.node 1 (.leaf (-79633266000630827238555648)) (.node 1 (.leaf (0)) (.leaf (13454022109695619213819904)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1454488876723850725818368))) (.node 1 (.leaf (0)) (.leaf (75557863725914323419136))))))

def row77 : CoefficientRow := ⟨78, (.node 32 (.node 16 row77Part00 row77Part01) (.node 16 row77Part02 (.node 16 row77Part03 row77Part04)))⟩

theorem row77_represents : RowRepresents row77 Data.chebyshevRow77 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row78Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (3042)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1541280)) (.leaf (0))) (.node 1 (.leaf (311749568)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-33668953344)) (.leaf (0))) (.node 1 (.leaf (2252078879232)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-102094242525184)) (.leaf (0))) (.node 1 (.leaf (3332086816481280)) (.leaf (0))))))

def row78Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-81747196564340736)) (.leaf (0))) (.node 1 (.leaf (1556936802539143168)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-23599884164803854336)) (.leaf (0))) (.node 1 (.leaf (290350090027586813952)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-2945580623468272025600)) (.leaf (0))) (.node 1 (.leaf (24960397037020372795392)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-178552681450008169414656)) (.leaf (0))) (.node 1 (.leaf (1087734726074762411376640)) (.leaf (0))))))

def row78Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-5684291149164887440097280)) (.leaf (0))) (.node 1 (.leaf (25635038515841649239654400)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-100261483973069561470648320)) (.leaf (0))) (.node 1 (.leaf (341430999475858506629775360)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-1015538357415374019719331840)) (.leaf (0))) (.node 1 (.leaf (2644409985279057551928852480)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-6037976287740765657681100800)) (.leaf (0))) (.node 1 (.leaf (12099287749540432825150341120)) (.leaf (0))))))

def row78Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-21281016750964732912321167360)) (.leaf (0))) (.node 1 (.leaf (32833568701488445064724086784)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-44372364338663117312206307328)) (.leaf (0))) (.node 1 (.leaf (52403421196604240571368734720)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-53900661802221504587693555712)) (.leaf (0))) (.node 1 (.leaf (48063869023880518912438173696)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-36930430436427969333850800128)) (.leaf (0))) (.node 1 (.leaf (24255734850366757225088679936)) (.leaf (0))))))

def row78Part04 : LookupTree ℤ := (.node 7 (.node 3 (.node 1 (.leaf (-13475408250203754013938155520)) (.node 1 (.leaf (0)) (.leaf (6244548158835679016249196544)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2368432664281837870956675072))) (.node 1 (.leaf (0)) (.leaf (715923745310866105920651264))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-165816454313001852388507648))) (.node 1 (.leaf (0)) (.leaf (27625843924787424500121600)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2946756685310658613346304))) (.node 1 (.leaf (0)) (.leaf (151115727451828646838272))))))

def row78 : CoefficientRow := ⟨79, (.node 32 (.node 16 row78Part00 row78Part01) (.node 16 row78Part02 (.node 16 row78Part03 row78Part04)))⟩

theorem row78_represents : RowRepresents row78 Data.chebyshevRow78 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row79Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-79))) (.node 1 (.leaf (0)) (.leaf (82160)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-25601056))) (.node 1 (.leaf (0)) (.leaf (3788956288))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-325850240768))) (.node 1 (.leaf (0)) (.leaf (18247613483008)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-715867913564160))) (.node 1 (.leaf (0)) (.leaf (20698809386483712))))))

def row79Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-457808960548110336))) (.node 1 (.leaf (0)) (.leaf (7967482260767113216)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-111544751650739585024))) (.node 1 (.leaf (0)) (.leaf (1278576204692271923200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-12172045468670428708864))) (.node 1 (.leaf (0)) (.leaf (97376363749363429670912)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-661008025845432542298112))) (.node 1 (.leaf (0)) (.leaf (3838111117812188955279360))))))

def row79Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-19190555589060944776396800))) (.node 1 (.leaf (0)) (.leaf (83083817138522678561341440)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-312874194269391708456222720))) (.node 1 (.leaf (0)) (.leaf (1028558079946340353305477120))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-2960240327650442968049909760))) (.node 1 (.leaf (0)) (.leaf (7474360960180520450890137600)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-16579491584400427181974487040))) (.node 1 (.leaf (0)) (.leaf (32330775448581036539872542720))))))

def row79Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-55424186483281776925495787520))) (.node 1 (.leaf (0)) (.leaf (83462304351294911134864244736)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-110233232162087618480009379840))) (.node 1 (.leaf (0)) (.leaf (127380623831745692465788616704))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-128338372883112201431696801792))) (.node 1 (.leaf (0)) (.leaf (112211692479915752975931277312)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-84618653345510239949062930432))) (.node 1 (.leaf (0)) (.leaf (54592679577748541902621245440))))))

def row79Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-29816001923231895962200834048))) (.node 1 (.leaf (0)) (.leaf (13593184051839778891858182144)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-5075715784062935340693848064))) (.node 1 (.leaf (0)) (.leaf (1511480756622363039079858176))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-345086930735699323990835200))) (.node 1 (.leaf (0)) (.leaf (56706176726298699726061568)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-5969071234347231550111744))) (.node 1 (.leaf (0)) (.leaf (302231454903657293676544))))))

def row79 : CoefficientRow := ⟨80, (.node 32 (.node 16 row79Part00 row79Part01) (.node 16 row79Part02 (.node 16 row79Part03 row79Part04)))⟩

theorem row79_represents : RowRepresents row79 Data.chebyshevRow79 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.CoefficientCache
